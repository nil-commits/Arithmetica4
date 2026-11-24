import RHDirect.Stage9CuspFormLFunc
import RHDirect.Stage7PadicLFunction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# RHDirect.Stage11ModularSymbols

**UNCONDITIONAL CONCRETE EICHLER–SHIMURA PERIOD POLYNOMIALS, MANIN PERIOD RELATIONS,
EXACT CRITICAL `L`-VALUE RATIOS FOR RAMANUJAN'S `Δ` (INCLUDING THE `691` RELATION),
AND THE MAZUR–TATE–TEITELBAUM MODULAR-SYMBOL `p`-ADIC DISTRIBUTION LAW**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Uniform Horizontal-Strip Decay, Cauchy Derivative Decay & Cusp Decay for `S_k(SL₂(ℤ))`**:
   - `cuspForm_SL2Z_transform`: `f (γ • τ) = (c τ + d)^k * f τ` for every `γ ∈ SL₂(ℤ)`.
   - `cuspForm_exp_decay_horizontal`: for every `δ > 0`, `‖f τ‖ ≤ C * exp(-2π Im(τ))` on `Im(τ) ≥ δ`.
   - `cuspForm_exp_decay_deriv_horizontal`: Cauchy circle-integral exponential decay of `f'(z)`.
   - `cuspForm_exp_decay_atCusp`: for EVERY rational cusp `r ∈ ℚ`, super-exponential decay of
     `f(r + i t)` as `t → 0⁺` via the Bézout `SL₂(ℤ)` cusp-stabilizing matrix.

2. **Concrete Eichler–Shimura Period Polynomial `periodPoly f`, Vertical-Ray 1-Cocycle, &
   Manin Period Relations (`0` Assumptions!)**:
   - `polySlash w γ P`: exact right action of `M₂(ℤ)` on polynomials of degree `≤ w`.
   - `cuspPeriod f j = ∫_{t > 0} f(i t) (i t)^j i dt = i^{j+1} Λ(f, j + 1)`.
   - `periodPoly f = ∑_{j = 0}^{k - 2} (-1)^j C(k - 2, j) cuspPeriod f j * X^{k - 2 - j}`
     satisfying `(periodPoly f).eval X = ∫_{t > 0} f(i t) (X - i t)^{k - 2} i dt`.
   - `cuspPrimitive f z` and the Eichler–Shimura 1-cocycle `cuspCocycle f γ` satisfying
     `cuspCocycle f (γ₁ * γ₂) = polySlash (k - 2) γ₂ (cuspCocycle f γ₁) + cuspCocycle f γ₂`,
     `cuspCocycle f T = 0`, `cuspCocycle f (-1) = 0`, and `cuspCocycle f S = -periodPoly f`.
   - **`periodPoly_S_relation`**: `periodPoly f + polySlash (k - 2) matS (periodPoly f) = 0`.
   - **`periodPoly_U_relation`**:
     `periodPoly f + polySlash (k - 2) matU (periodPoly f) + polySlash (k - 2) (matU ^ 2) (periodPoly f) = 0`.
   - **`periodPoly_heckeTwo`**: exact Heilbronn-matrix action of `T_2` on `periodPoly f`.

3. **Manin's Exact Period-Ratio Theorem for Ramanujan's `Δ` (`k = 12`, `0` Assumptions!)**:
   - **`delta_even_critical_ratios`**:
     `Λ(Δ, 10) = Λ(Δ, 2)`, `Λ(Δ, 8) = Λ(Δ, 4)`,
     `48 * Λ(Δ, 4) = 25 * Λ(Δ, 2)`, `12 * Λ(Δ, 6) = 5 * Λ(Δ, 2)`, `5 * Λ(Δ, 6) = 4 * Λ(Δ, 4)`.
   - **`delta_odd_critical_ratios`**:
     `Λ(Δ, 11) = Λ(Δ, 1)`, `Λ(Δ, 9) = Λ(Δ, 3)`, `Λ(Δ, 7) = Λ(Δ, 5)`,
     `14 * Λ(Δ, 5) = 9 * Λ(Δ, 3)`, `691 * Λ(Δ, 1) = 1620 * Λ(Δ, 3)`,
     `691 * Λ(Δ, 1) = 2520 * Λ(Δ, 5)`.
   - **`manin_delta_period_ratios`**: complete exact critical-value ratio package for both
     `completedDeltaL` and `deltaL`.

4. **Concrete Modular Symbols `modularSymbol f r` & Mazur–Tate–Teitelbaum `p`-adic Distribution
   Law (`0` Assumptions!)**:
   - `modularSymbol f r = ∫_{t > 0} f(r + i t) dt` (globally integrable for every `r : ℚ`,
     `ℤ`-periodic, with `modularSymbol f 0 = completedCuspL f 1`).
   - **`modularSymbol_hecke_distribution`**: for every normalized Hecke eigenform `f` (`T_p f = a_p f`),
     `∑_{b = 0}^{p - 1} modularSymbol f ((a + b p^n) / p^{n+1}) = a_p * modularSymbol f (a / p^n) - p^{k - 2} * modularSymbol f (a / p^{n - 1})`.
   - **`mttDist` & `mttDist_compat`**: for any nonzero root `α` of `X² - a_p X + p^{k - 1} = 0`,
     `mttDist f p α n a := α^{-n} modularSymbol f (a / p^n) - (p^{k - 2} / α^{n + 1}) modularSymbol f (a / p^{n - 1})`
     satisfies the exact projective distribution law matching `Stage7PadicLFunction.PadicMeasure.compat`,
     with exact Euler-factor masses at `n = 0` and on `(ZMod p)ˣ`, unconditionally specialized to
     Ramanujan's `Δ` (`mttDistDelta`) and bridged directly to `Stage7PadicLFunction.PadicMeasure`.
-/

open Complex Real Filter MeasureTheory Polynomial Finset Matrix
open RHDirect.Stage5ModularHecke RHDirect.Stage5ThetaModular RHDirect.Stage7EisensteinSeries
open RHDirect.Stage7PadicLFunction RHDirect.Stage8ModularRing RHDirect.Stage8RamanujanDelta
open RHDirect.Stage9CuspFormLFunc
open scoped BigOperators UpperHalfPlane ModularForm Topology ENNReal Manifold

namespace RHDirect.Stage11ModularSymbols

noncomputable section

/-! ## Section 1: `SL₂(ℤ)` Transformation, Horizontal-Strip Decay, Cauchy Derivative Bound & Cusp Decay -/

section CuspFormDecayAndTransform

/-- Exact Möbius action formula for any `γ ∈ SL₂(ℤ)` on `UpperHalfPlane`:
`((γ • τ : UpperHalfPlane) : ℂ) = (γ 0 0 * τ + γ 0 1) / (γ 1 0 * τ + γ 1 1)`. -/
private lemma sl2Z_coe_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    ((γ • τ : UpperHalfPlane) : ℂ) =
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (τ : ℂ) +
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) /
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) +
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) := by
  change ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ • τ : UpperHalfPlane) : ℂ) = _
  rw [UpperHalfPlane.coe_smul]
  have hσ : UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) =
      ContinuousAlgEquiv.refl ℝ ℂ := by
    simp [UpperHalfPlane.σ]
  rw [hσ, ContinuousAlgEquiv.refl_apply]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL]

/-- Every level-1 cusp form `f ∈ S_k(SL₂(ℤ))` satisfies the exact `SL₂(ℤ)` modular transformation
`f (γ • τ) = (c * τ + d)^k * f τ`. -/
theorem cuspForm_SL2Z_transform {k : ℤ} (f : CuspForm SL2ZRange k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    f (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) +
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) ^ k * f τ := by
  have hsl := f.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) ⟨γ, rfl⟩
  have hval := congrFun hsl τ
  change SlashAction.map k (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ)
    (f : UpperHalfPlane → ℂ) τ = f τ at hval
  rw [ModularForm.slash_def] at hval
  dsimp only at hval
  have hdet_mat : ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ :
      Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := by
    change ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)).det = 1
    rw [Matrix.det_fin_two]
    have hγ := γ.prop
    rw [Matrix.det_fin_two] at hγ
    simp only [Matrix.map_apply]
    exact_mod_cast hγ
  have hdet : ((Matrix.GeneralLinearGroup.det
      (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ)) : ℝ) = 1 := hdet_mat
  have hσ : UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) =
      ContinuousAlgEquiv.refl ℝ ℂ := by
    simp [UpperHalfPlane.σ]
  have hdenom : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) (τ : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) +
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := by
    simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL]
  have hdenom_ne : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) +
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) ≠ 0 := by
    rw [← hdenom]
    exact UpperHalfPlane.denom_ne_zero _ τ
  have hsmul : (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) • τ = γ • τ := rfl
  rw [hσ, ContinuousAlgEquiv.refl_apply, hdet, abs_one, Complex.ofReal_one, _root_.one_zpow,
    mul_one, hdenom, hsmul] at hval
  calc f (γ • τ)
      = (f (γ • τ) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) +
          ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) ^ (-k)) *
          (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) +
            ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) ^ k := by
          rw [mul_assoc, ← zpow_add₀ hdenom_ne, neg_add_cancel, zpow_zero, mul_one]
    _ = f τ * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) +
          ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) ^ k := by rw [hval]
    _ = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) +
          ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) ^ k * f τ := mul_comm _ _

/-- Every level-1 cusp form of odd weight vanishes identically (from `-I ∈ SL₂(ℤ)`). -/
theorem cuspForm_eq_zero_of_odd {k : ℤ} (hk : Odd k) (f : CuspForm SL2ZRange k)
    (τ : UpperHalfPlane) : f τ = 0 := by
  have h := cuspForm_SL2Z_transform f (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) τ
  have hsmul : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ = τ := by
    apply UpperHalfPlane.ext
    rw [sl2Z_coe_smul]
    simp
  have h10 : (((-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) = 0 := by
    simp
  have h11 : (((-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = -1 := by
    simp
  rw [hsmul, h10, h11] at h
  simp only [Int.cast_zero, zero_mul, Int.cast_neg, Int.cast_one, zero_add] at h
  have hneg : (-1 : ℂ) ^ k = -1 := hk.neg_one_zpow
  rw [hneg, neg_one_mul] at h
  have h2 : (2 : ℂ) * f τ = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Integer translation invariance `f(τ + n) = f(τ)` for every `f ∈ S_k(SL₂(ℤ))` and `n : ℤ`. -/
theorem cuspForm_add_int {k : ℤ} (f : CuspForm SL2ZRange k) (τ : UpperHalfPlane) (n : ℤ) :
    f ⟨(τ : ℂ) + (n : ℂ), by simp [τ.im_pos]⟩ = f τ := by
  let Tn : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, n; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h := cuspForm_SL2Z_transform f Tn τ
  have h10 : ((Tn : Matrix (Fin 2) (Fin 2) ℤ) 1 0) = 0 := by simp [Tn]
  have h11 : ((Tn : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = 1 := by simp [Tn]
  rw [h10, h11] at h
  simp only [Int.cast_zero, zero_mul, Int.cast_one, zero_add, _root_.one_zpow, one_mul] at h
  have hpt : Tn • τ = ⟨(τ : ℂ) + (n : ℂ), by simp [τ.im_pos]⟩ := by
    apply UpperHalfPlane.ext
    rw [sl2Z_coe_smul]
    simp [Tn]
  rw [hpt] at h
  exact h

/-- Complex-domain lift `f_ℂ : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex` of a cusp form `f`. -/
def cuspToComplex {k : ℤ} (f : CuspForm SL2ZRange k) (z : ℂ) : ℂ :=
  f (UpperHalfPlane.ofComplex z)

theorem cuspToComplex_eq {k : ℤ} (f : CuspForm SL2ZRange k) (τ : UpperHalfPlane) :
    cuspToComplex f (τ : ℂ) = f τ := by
  unfold cuspToComplex
  rw [UpperHalfPlane.ofComplex_apply]

theorem differentiableOn_cuspToComplex {k : ℤ} (f : CuspForm SL2ZRange k) :
    DifferentiableOn ℂ (cuspToComplex f) {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp f.holo'

/-- **Uniform Horizontal-Strip Exponential Decay for Every Level-1 Cusp Form**:
for every `f ∈ S_k(SL₂(ℤ))` and every `δ > 0`, there exists `C > 0` such that
`‖f τ‖ ≤ C * exp(-2π Im(τ))` for ALL `τ ∈ ℍ` with `Im(τ) ≥ δ`. -/
theorem cuspForm_exp_decay_horizontal {k : ℤ} (f : CuspForm SL2ZRange k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ τ : UpperHalfPlane, δ ≤ τ.im →
      ‖f τ‖ ≤ C * Real.exp (-2 * Real.pi * τ.im) := by
  have hbigO := CuspFormClass.exp_decay_atImInfty f zero_lt_one one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨C₀, hC₀⟩ := hbigO
  rw [UpperHalfPlane.atImInfty_basis.eventually_iff] at hC₀
  obtain ⟨A, _, hA⟩ := hC₀
  let B : ℝ := max δ A
  have hBA : A ≤ B := le_max_right δ A
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc δ B
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let emb : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)
  have hemb_cont : Continuous emb :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))
  let g : ℝ × ℝ → ℝ := fun p => ‖cuspToComplex f (emb p)‖ * Real.exp (2 * Real.pi * p.2)
  have hg_cont : ContinuousOn g K := by
    refine (((differentiableOn_cuspToComplex f).continuousOn.comp hemb_cont.continuousOn ?_).norm).mul ?_
    · intro p hp
      change 0 < (emb p).im
      have hp2 : δ ≤ p.2 := hp.2.1
      simp only [emb, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add]
      linarith
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).continuousOn
  obtain ⟨C₁, hC₁⟩ := hK_compact.exists_bound_of_continuousOn hg_cont
  let C : ℝ := max (max C₀ C₁) 1
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC₀_le : C₀ ≤ C := le_trans (le_max_left C₀ C₁) (le_max_left _ _)
  have hC₁_le : C₁ ≤ C := le_trans (le_max_right C₀ C₁) (le_max_left _ _)
  refine ⟨C, hC_pos, fun τ hτ => ?_⟩
  by_cases hτB : τ.im ≤ B
  · let n : ℤ := ⌊τ.re⌋
    let τ' : UpperHalfPlane := ⟨(τ : ℂ) + ((-n : ℤ) : ℂ), by simp [τ.im_pos]⟩
    have hf_eq : f τ' = f τ := cuspForm_add_int f τ (-n)
    have hre0 : 0 ≤ τ'.re := by
      change 0 ≤ ((τ : ℂ) + ((-n : ℤ) : ℂ)).re
      simp only [Complex.add_re, Int.cast_neg, Complex.neg_re, Complex.intCast_re]
      have hfl : (n : ℝ) ≤ (τ : ℂ).re := Int.floor_le (τ : ℂ).re
      linarith
    have hre1 : τ'.re ≤ 1 := by
      change ((τ : ℂ) + ((-n : ℤ) : ℂ)).re ≤ 1
      simp only [Complex.add_re, Int.cast_neg, Complex.neg_re, Complex.intCast_re]
      have hfl : (τ : ℂ).re < (n : ℝ) + 1 := Int.lt_floor_add_one (τ : ℂ).re
      linarith
    have him' : τ'.im = τ.im := by
      change ((τ : ℂ) + ((-n : ℤ) : ℂ)).im = τ.im
      simp
    have hmem : (τ'.re, τ'.im) ∈ K := ⟨⟨hre0, hre1⟩, ⟨him'.symm ▸ hτ, him'.symm ▸ hτB⟩⟩
    have hgb : ‖g (τ'.re, τ'.im)‖ ≤ C₁ := hC₁ _ hmem
    have hg_nn : 0 ≤ g (τ'.re, τ'.im) := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hg_nn] at hgb
    have hemb_eq : emb (τ'.re, τ'.im) = (τ' : ℂ) := by
      apply Complex.ext <;> simp [emb]
    have hprod : ‖f τ‖ * Real.exp (2 * Real.pi * τ.im) ≤ C := by
      have h1 : g (τ'.re, τ'.im) = ‖f τ‖ * Real.exp (2 * Real.pi * τ.im) := by
        dsimp only [g]
        rw [hemb_eq, cuspToComplex_eq f τ', hf_eq, him']
      rw [← h1]
      exact hgb.trans hC₁_le
    have hmul : Real.exp (2 * Real.pi * τ.im) * Real.exp (-2 * Real.pi * τ.im) = 1 := by
      rw [← Real.exp_add, show 2 * Real.pi * τ.im + -2 * Real.pi * τ.im = 0 by ring, Real.exp_zero]
    calc ‖f τ‖
        = (‖f τ‖ * Real.exp (2 * Real.pi * τ.im)) * Real.exp (-2 * Real.pi * τ.im) := by
            rw [mul_assoc, hmul, mul_one]
      _ ≤ C * Real.exp (-2 * Real.pi * τ.im) :=
            mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
  · have hAτ : A ≤ τ.im := le_trans hBA (le_of_not_ge hτB)
    have hbound := hA (show τ ∈ UpperHalfPlane.im ⁻¹' Set.Ici A from hAτ)
    simp only [div_one, Real.norm_of_nonneg (Real.exp_pos _).le] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right hC₀_le (Real.exp_pos _).le)

/-- Cauchy circle-integral derivative bound: if `g` is holomorphic on `closedBall s r` (`r > 0`)
and bounded by `M` on `closedBall s r`, then `‖deriv g s‖ ≤ 2 * M / r`. -/
private lemma norm_deriv_le_of_closedBall {g : ℂ → ℂ} {s : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.closedBall s r))
    (hbound : ∀ z ∈ Metric.closedBall s r, ‖g z‖ ≤ M) :
    ‖deriv g s‖ ≤ 2 * M / r := by
  have hds_diff : DifferentiableOn ℂ (dslope g s) (Metric.closedBall s r) :=
    (Complex.differentiableOn_dslope (Metric.closedBall_mem_nhds s hr)).mpr hg
  have hds_dc : DiffContOnCl ℂ (dslope g s) (Metric.ball s r) := by
    refine ⟨hds_diff.mono Metric.ball_subset_closedBall, ?_⟩
    rw [closure_ball s hr.ne']
    exact hds_diff.continuousOn
  have hcauchy := hds_dc.circleIntegral_sub_inv_smul (Metric.mem_ball_self hr)
  rw [dslope_same] at hcauchy
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero
  have hderiv : deriv g s = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∮ z in C(s, r), (z - s)⁻¹ • dslope g s z := by
    have hinv := congrArg ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ·) hcauchy
    rw [inv_smul_smul₀ h2piI] at hinv
    exact hinv.symm
  rw [hderiv, norm_smul, norm_inv]
  have h2pi_norm : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2pi_norm]
  have hcirc : ‖∮ z in C(s, r), (z - s)⁻¹ • dslope g s z‖ ≤
      2 * Real.pi * r * (2 * M / r ^ 2) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const hr.le fun z hz => ?_
    have hdist : ‖z - s‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hne : z ≠ s := fun h => by rw [h, sub_self, norm_zero] at hdist; linarith
    have hz_cb : z ∈ Metric.closedBall s r := Metric.sphere_subset_closedBall hz
    have hs_cb : s ∈ Metric.closedBall s r := Metric.mem_closedBall_self hr.le
    rw [dslope_of_ne g hne, slope_def_field, norm_smul, norm_inv, norm_div, hdist]
    have hsub : ‖g z - g s‖ ≤ 2 * M := by
      calc ‖g z - g s‖ ≤ ‖g z‖ + ‖g s‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hbound z hz_cb) (hbound s hs_cb)
        _ = 2 * M := by ring
    calc r⁻¹ * (‖g z - g s‖ / r)
        ≤ r⁻¹ * (2 * M / r) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsub hr.le) (inv_nonneg.mpr hr.le)
      _ = 2 * M / r ^ 2 := by field_simp [hr.ne']
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  calc (2 * Real.pi)⁻¹ * ‖∮ z in C(s, r), (z - s)⁻¹ • dslope g s z‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * r * (2 * M / r ^ 2)) :=
        mul_le_mul_of_nonneg_left hcirc (inv_nonneg.mpr hpi.le)
    _ = 2 * M / r := by field_simp [Real.pi_pos.ne', hr.ne']

/-- **Uniform Horizontal-Strip Exponential Decay for the Derivative `f'(z)`** of any level-1
cusp form `f ∈ S_k(SL₂(ℤ))`, proved via Cauchy's circle-integral bound. -/
theorem cuspForm_exp_decay_deriv_horizontal {k : ℤ} (f : CuspForm SL2ZRange k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ z : ℂ, δ ≤ z.im →
      ‖deriv (cuspToComplex f) z‖ ≤ C * Real.exp (-2 * Real.pi * z.im) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := cuspForm_exp_decay_horizontal f (half_pos hδ)
  set r : ℝ := δ / 2 with hr_def
  have hr : 0 < r := half_pos hδ
  refine ⟨(2 * C₀ * Real.exp (2 * Real.pi * r)) / r, by positivity, fun z hz => ?_⟩
  have hcb_im : ∀ w ∈ Metric.closedBall z r, z.im - r ≤ w.im := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have him := (abs_le.mp ((Complex.abs_im_le_norm (w - z)).trans hw)).1
    rw [Complex.sub_im] at him
    linarith
  have hcb_sub : Metric.closedBall z r ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have := hcb_im w hw
    change 0 < w.im
    linarith [hr_def]
  have hg_diff : DifferentiableOn ℂ (cuspToComplex f) (Metric.closedBall z r) :=
    (differentiableOn_cuspToComplex f).mono hcb_sub
  let M : ℝ := C₀ * Real.exp (-2 * Real.pi * (z.im - r))
  have hbound : ∀ w ∈ Metric.closedBall z r, ‖cuspToComplex f w‖ ≤ M := by
    intro w hw
    have hw_im : r ≤ w.im := by linarith [hcb_im w hw, hr_def]
    have hw_pos : 0 < w.im := lt_of_lt_of_le hr hw_im
    let τ : UpperHalfPlane := ⟨w, hw_pos⟩
    have hval : cuspToComplex f w = f τ := cuspToComplex_eq f τ
    rw [hval]
    have h1 := hC₀ τ hw_im
    have h2 : Real.exp (-2 * Real.pi * w.im) ≤ Real.exp (-2 * Real.pi * (z.im - r)) := by
      apply Real.exp_le_exp.mpr
      have := hcb_im w hw
      nlinarith [Real.pi_pos]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC₀_pos.le)
  have hbd := norm_deriv_le_of_closedBall hr hg_diff hbound
  have hexp_eq : Real.exp (-2 * Real.pi * (z.im - r)) =
      Real.exp (2 * Real.pi * r) * Real.exp (-2 * Real.pi * z.im) := by
    rw [← Real.exp_add]
    congr 1; ring
  calc ‖deriv (cuspToComplex f) z‖
      ≤ 2 * M / r := hbd
    _ = 2 * (C₀ * (Real.exp (2 * Real.pi * r) * Real.exp (-2 * Real.pi * z.im))) / r := by
          dsimp only [M]; rw [hexp_eq]
    _ = (2 * C₀ * Real.exp (2 * Real.pi * r)) / r * Real.exp (-2 * Real.pi * z.im) := by ring

/-- Concrete Bézout matrix `γ ∈ SL₂(ℤ)` with first column `(r.num, r.den)` for any `r : ℚ`. -/
def cuspMatrix (r : ℚ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  let a : ℤ := r.num
  let c : ℤ := (r.den : ℤ)
  let x : ℤ := Int.gcdA a c
  let y : ℤ := Int.gcdB a c
  ⟨!![a, -y; c, x], by
    have hcop : Nat.Coprime r.num.natAbs r.den := r.reduced
    have hgcd : Int.gcd a c = 1 := hcop
    have hbez : (1 : ℤ) = a * x + c * y := by
      have h := Int.gcd_eq_gcd_ab a c
      rw [hgcd] at h
      exact_mod_cast h
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith⟩

/-- Exact vertical-ray inversion identity under `(cuspMatrix r)⁻¹`:
`(cuspMatrix r)⁻¹ • (r + i t) = -(d / c) + i / (c² t)` for every `r : ℚ` and `t > 0`. -/
theorem cuspMatrix_inv_smul_ray (r : ℚ) {t : ℝ} (ht : 0 < t) :
    (cuspMatrix r)⁻¹ • (⟨(r : ℂ) + Complex.I * (t : ℂ), by simp [ht]⟩ : UpperHalfPlane) =
      ⟨-(((cuspMatrix r : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) / (r.den : ℂ)) +
        Complex.I * (((((r.den : ℝ) ^ 2 * t)⁻¹ : ℝ) : ℂ)), by
          have _hc : (0 : ℝ) < (r.den : ℝ) := Nat.cast_pos.mpr r.pos
          simp only [Complex.add_im, Complex.neg_im,
            Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, one_mul, zero_add]
          have hdiv_im : (((cuspMatrix r : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) / (r.den : ℂ)).im = 0 := by
            rw [← Complex.ofReal_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
              Complex.ofReal_im]
          rw [hdiv_im, neg_zero, zero_add]
          positivity⟩ := by
  set a : ℤ := r.num
  set c : ℕ := r.den
  have hc_pos : 0 < c := r.pos
  have hc_ne : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc_pos.ne'
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hr_eq : (r : ℂ) = (a : ℂ) / (c : ℂ) := by
    have hq : r = (a : ℚ) / (c : ℚ) := (Rat.num_div_den r).symm
    conv_lhs => rw [hq]
    push_cast
    rfl
  set γ : Matrix.SpecialLinearGroup (Fin 2) ℤ := cuspMatrix r
  set d : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  have h00 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = a := rfl
  have h10 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (c : ℤ) := rfl
  have hdet : (a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ) = 1 := by
    have h := γ.prop
    rw [Matrix.det_fin_two] at h
    have h' : a * d - b * (c : ℤ) = 1 := h
    exact_mod_cast h'
  have hinv_coe : ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![d, -b; -(c : ℤ), a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h00, h10, d, b]
  apply UpperHalfPlane.ext
  rw [sl2Z_coe_smul, hinv_coe]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg,
    Int.cast_natCast]
  change ((d : ℂ) * ((r : ℂ) + Complex.I * (t : ℂ)) + -(b : ℂ)) /
      (-(c : ℂ) * ((r : ℂ) + Complex.I * (t : ℂ)) + (a : ℂ)) =
    -((d : ℂ) / (c : ℂ)) + Complex.I * (((((c : ℝ) ^ 2 * t)⁻¹ : ℝ) : ℂ))
  rw [hr_eq]
  have hden_simp : -(c : ℂ) * ((a : ℂ) / (c : ℂ) + Complex.I * (t : ℂ)) + (a : ℂ) =
      -(Complex.I * (c : ℂ) * (t : ℂ)) := by
    field_simp [hc_ne]
    ring
  have hnum_simp : (d : ℂ) * ((a : ℂ) / (c : ℂ) + Complex.I * (t : ℂ)) + -(b : ℂ) =
      1 / (c : ℂ) + Complex.I * (d : ℂ) * (t : ℂ) := by
    field_simp [hc_ne]
    linear_combination hdet
  rw [hden_simp, hnum_simp]
  push_cast
  field_simp [hc_ne, ht_ne, Complex.I_ne_zero]
  linear_combination -Complex.I_mul_I

/-- **Super-Exponential Decay at Every Rational Cusp `r ∈ ℚ`**:
for every `f ∈ S_k(SL₂(ℤ))` and every `r : ℚ`, there exists `C > 0` such that
`‖f(r + i t)‖ ≤ C * (r.den * t)^(-k) * exp(-2π / (r.den² * t))` for all `t ∈ (0, 1 / r.den²]`. -/
theorem cuspForm_exp_decay_atCusp {k : ℤ} (f : CuspForm SL2ZRange k) (r : ℚ) :
    ∃ C > 0, ∀ (t : ℝ) (ht : 0 < t), t ≤ ((r.den : ℝ) ^ 2)⁻¹ →
      ‖f ⟨(r : ℂ) + Complex.I * (t : ℂ), by simp [ht]⟩‖ ≤
        C * ((r.den : ℝ) * t) ^ (-k) * Real.exp (-2 * Real.pi / ((r.den : ℝ) ^ 2 * t)) := by
  obtain ⟨C, hC_pos, hC⟩ := cuspForm_exp_decay_horizontal f zero_lt_one
  refine ⟨C, hC_pos, fun t ht ht_le => ?_⟩
  set c : ℕ := r.den
  have hc_pos : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr r.pos
  have hc_ne : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.pos.ne'
  set τ : UpperHalfPlane := ⟨(r : ℂ) + Complex.I * (t : ℂ), by simp [ht]⟩
  have htr := cuspForm_SL2Z_transform f (cuspMatrix r)⁻¹ τ
  have hinv_mat : (((cuspMatrix r)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.adjugate (cuspMatrix r : Matrix (Fin 2) (Fin 2) ℤ) :=
    Matrix.SpecialLinearGroup.coe_inv (cuspMatrix r)
  have hinv_coe : (((cuspMatrix r)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(c : ℤ) := by
    rw [hinv_mat, Matrix.adjugate_fin_two]
    rfl
  have hinv_coe11 : (((cuspMatrix r)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) 1 1 = r.num := by
    rw [hinv_mat, Matrix.adjugate_fin_two]
    rfl
  rw [hinv_coe, hinv_coe11] at htr
  have hr_eq : (r : ℂ) = (r.num : ℂ) / (c : ℂ) := by
    have hq : r = (r.num : ℚ) / (c : ℚ) := (Rat.num_div_den r).symm
    conv_lhs => rw [hq]
    push_cast
    rfl
  have hden_eq : ((-(c : ℤ) : ℤ) : ℂ) * (τ : ℂ) + (r.num : ℂ) =
      -(Complex.I * (c : ℂ) * (t : ℂ)) := by
    push_cast
    change -(c : ℂ) * ((r : ℂ) + Complex.I * (t : ℂ)) + (r.num : ℂ) = _
    rw [hr_eq]
    field_simp [hc_ne]
    ring
  rw [hden_eq] at htr
  have hden_ne : -(Complex.I * (c : ℂ) * (t : ℂ)) ≠ 0 := by
    simp [hc_ne, Complex.ofReal_ne_zero.mpr ht.ne']
  have hf_eq : f τ = (-(Complex.I * (c : ℂ) * (t : ℂ))) ^ (-k) * f ((cuspMatrix r)⁻¹ • τ) := by
    calc f τ
        = (-(Complex.I * (c : ℂ) * (t : ℂ))) ^ (-k) *
            ((-(Complex.I * (c : ℂ) * (t : ℂ))) ^ k * f τ) := by
            rw [← mul_assoc, ← zpow_add₀ hden_ne, neg_add_cancel, zpow_zero, one_mul]
      _ = (-(Complex.I * (c : ℂ) * (t : ℂ))) ^ (-k) * f ((cuspMatrix r)⁻¹ • τ) := by rw [← htr]
  have hnorm_fac : ‖(-(Complex.I * (c : ℂ) * (t : ℂ))) ^ (-k)‖ = ((c : ℝ) * t) ^ (-k) := by
    rw [norm_zpow, norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have him_eq : ((cuspMatrix r)⁻¹ • τ).im = ((c : ℝ) ^ 2 * t)⁻¹ := by
    rw [cuspMatrix_inv_smul_ray r ht]
    change (-(((cuspMatrix r : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) / (c : ℂ)) +
      Complex.I * (((((c : ℝ) ^ 2 * t)⁻¹ : ℝ) : ℂ))).im = ((c : ℝ) ^ 2 * t)⁻¹
    have hdiv_im : (((cuspMatrix r : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) / (c : ℂ)).im = 0 := by
      rw [← Complex.ofReal_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_im]
    simp only [Complex.add_im, Complex.neg_im, hdiv_im, neg_zero, zero_add,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul]
  have him_ge : 1 ≤ ((cuspMatrix r)⁻¹ • τ).im := by
    rw [him_eq]
    have hpos : 0 < (c : ℝ) ^ 2 * t := by positivity
    rw [one_le_inv₀ hpos]
    have h1 : (c : ℝ) ^ 2 * t ≤ (c : ℝ) ^ 2 * ((c : ℝ) ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left ht_le (by positivity)
    rwa [mul_inv_cancel₀ (by positivity)] at h1
  have htop := hC ((cuspMatrix r)⁻¹ • τ) him_ge
  rw [him_eq, show -2 * Real.pi * ((c : ℝ) ^ 2 * t)⁻¹ = -2 * Real.pi / ((c : ℝ) ^ 2 * t) by
    rw [div_eq_mul_inv]] at htop
  rw [hf_eq, norm_mul, hnorm_fac]
  calc ((c : ℝ) * t) ^ (-k) * ‖f ((cuspMatrix r)⁻¹ • τ)‖
      ≤ ((c : ℝ) * t) ^ (-k) * (C * Real.exp (-2 * Real.pi / ((c : ℝ) ^ 2 * t))) :=
        mul_le_mul_of_nonneg_left htop (zpow_nonneg (by positivity) _)
    _ = C * ((c : ℝ) * t) ^ (-k) * Real.exp (-2 * Real.pi / ((c : ℝ) ^ 2 * t)) := by ring

end CuspFormDecayAndTransform

/-! ## Section 2: Right Slash Action `polySlash` on Polynomials of Degree `≤ w` -/

section PolynomialSlashAction

/-- Concrete weight-`(-w)` right slash action of a `2 × 2` integer matrix `γ = [[a, b], [c, d]]`
on polynomials `P ∈ ℂ[X]` of degree `≤ w`:
`(P |_{-w} γ)(X) = (c X + d)^w P((a X + b) / (c X + d))
                 = ∑_{m = 0}^w P.coeff m * (a X + b)^m * (c X + d)^{w - m}`. -/
def polySlash (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ m ∈ Finset.range (w + 1),
    Polynomial.C (P.coeff m) *
      (Polynomial.C (γ 0 0 : ℂ) * Polynomial.X + Polynomial.C (γ 0 1 : ℂ)) ^ m *
      (Polynomial.C (γ 1 0 : ℂ) * Polynomial.X + Polynomial.C (γ 1 1 : ℂ)) ^ (w - m)

theorem polySlash_zero (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) :
    polySlash w γ 0 = 0 := by
  simp [polySlash]

theorem polySlash_add (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) (P Q : Polynomial ℂ) :
    polySlash w γ (P + Q) = polySlash w γ P + polySlash w γ Q := by
  unfold polySlash
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.coeff_add, map_add]
  ring

theorem polySlash_sub (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) (P Q : Polynomial ℂ) :
    polySlash w γ (P - Q) = polySlash w γ P - polySlash w γ Q := by
  unfold polySlash
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.coeff_sub, map_sub]
  ring

theorem polySlash_neg (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Polynomial ℂ) :
    polySlash w γ (-P) = -polySlash w γ P := by
  unfold polySlash
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.coeff_neg, map_neg]
  ring

theorem polySlash_smul (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) (P : Polynomial ℂ) :
    polySlash w γ (c • P) = c • polySlash w γ P := by
  unfold polySlash
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.coeff_smul, smul_eq_mul, Polynomial.smul_eq_C_mul, map_mul]
  ring

theorem polySlash_sum {ι : Type*} (s : Finset ι) (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ)
    (P : ι → Polynomial ℂ) :
    polySlash w γ (∑ i ∈ s, P i) = ∑ i ∈ s, polySlash w γ (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polySlash_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, polySlash_add, ih]

/-- Degree bound for a finite sum of polynomials. -/
private lemma natDegree_finsetSum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (n : ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ n) :
    (∑ i ∈ s, f i).natDegree ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem polySlash_monomial (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) {m : ℕ} (hm : m ≤ w) (c : ℂ) :
    polySlash w γ (Polynomial.C c * Polynomial.X ^ m) =
      Polynomial.C c *
        (Polynomial.C (γ 0 0 : ℂ) * Polynomial.X + Polynomial.C (γ 0 1 : ℂ)) ^ m *
        (Polynomial.C (γ 1 0 : ℂ) * Polynomial.X + Polynomial.C (γ 1 1 : ℂ)) ^ (w - m) := by
  unfold polySlash
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)) hnot

theorem polySlash_X_pow (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) {m : ℕ} (hm : m ≤ w) :
    polySlash w γ (Polynomial.X ^ m) =
      (Polynomial.C (γ 0 0 : ℂ) * Polynomial.X + Polynomial.C (γ 0 1 : ℂ)) ^ m *
        (Polynomial.C (γ 1 0 : ℂ) * Polynomial.X + Polynomial.C (γ 1 1 : ℂ)) ^ (w - m) := by
  have h := polySlash_monomial w γ hm 1
  simpa using h

/-- Explicit evaluation of `polySlash w γ P` at any `x : ℂ`. -/
theorem polySlash_eval_eq_sum (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Polynomial ℂ) (x : ℂ) :
    (polySlash w γ P).eval x =
      ∑ m ∈ Finset.range (w + 1),
        P.coeff m * ((γ 0 0 : ℂ) * x + (γ 0 1 : ℂ)) ^ m *
          ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ (w - m) := by
  unfold polySlash
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

/-- Rational-function evaluation formula for `polySlash w γ P` whenever `P.natDegree ≤ w` and
`c x + d ≠ 0`. -/
theorem polySlash_eval {w : ℕ} {P : Polynomial ℂ} (hP : P.natDegree ≤ w)
    (γ : Matrix (Fin 2) (Fin 2) ℤ) {x : ℂ}
    (hx : (γ 1 0 : ℂ) * x + (γ 1 1 : ℂ) ≠ 0) :
    (polySlash w γ P).eval x =
      ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ w *
        P.eval (((γ 0 0 : ℂ) * x + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ))) := by
  rw [polySlash_eval_eq_sum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmw : m ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [div_pow]
  have hpow : ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ w =
      ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ (w - m) * ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmw]
  have hm_ne : ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ m ≠ 0 := pow_ne_zero m hx
  have hcancel : ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ m *
      (((γ 0 0 : ℂ) * x + (γ 0 1 : ℂ)) ^ m / ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ m) =
      ((γ 0 0 : ℂ) * x + (γ 0 1 : ℂ)) ^ m :=
    mul_div_cancel₀ _ hm_ne
  rw [hpow]
  linear_combination -P.coeff m * ((γ 1 0 : ℂ) * x + (γ 1 1 : ℂ)) ^ (w - m) * hcancel

/-- `polySlash w γ P` always has degree at most `w`. -/
theorem polySlash_natDegree_le (w : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Polynomial ℂ) :
    (polySlash w γ P).natDegree ≤ w := by
  unfold polySlash
  refine natDegree_finsetSum_le _ _ w fun m hm => ?_
  have hmw : m ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hlin1 : (Polynomial.C (γ 0 0 : ℂ) * Polynomial.X + Polynomial.C (γ 0 1 : ℂ)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hlin2 : (Polynomial.C (γ 1 0 : ℂ) * Polynomial.X + Polynomial.C (γ 1 1 : ℂ)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have h1 : (Polynomial.C (P.coeff m) *
      (Polynomial.C (γ 0 0 : ℂ) * Polynomial.X + Polynomial.C (γ 0 1 : ℂ)) ^ m *
      (Polynomial.C (γ 1 0 : ℂ) * Polynomial.X + Polynomial.C (γ 1 1 : ℂ)) ^ (w - m)).natDegree ≤
      m * 1 + (w - m) * 1 := by
    have ha : (Polynomial.C (P.coeff m) *
        (Polynomial.C (γ 0 0 : ℂ) * Polynomial.X + Polynomial.C (γ 0 1 : ℂ)) ^ m).natDegree ≤ m * 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left m hlin1))
    have hb : ((Polynomial.C (γ 1 0 : ℂ) * Polynomial.X + Polynomial.C (γ 1 1 : ℂ)) ^ (w - m)).natDegree ≤
        (w - m) * 1 :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (w - m) hlin2)
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add ha hb)
  omega

theorem polySlash_one {w : ℕ} {P : Polynomial ℂ} (hP : P.natDegree ≤ w) :
    polySlash w (1 : Matrix (Fin 2) (Fin 2) ℤ) P = P := by
  unfold polySlash
  have h1 : ∀ m ∈ Finset.range (w + 1),
      Polynomial.C (P.coeff m) *
        (Polynomial.C ((1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * Polynomial.X +
          Polynomial.C ((1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) ^ m *
        (Polynomial.C ((1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * Polynomial.X +
          Polynomial.C ((1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) ^ (w - m) =
      Polynomial.C (P.coeff m) * Polynomial.X ^ m := by
    intro m _
    simp
  rw [Finset.sum_congr rfl h1]
  have hsum := Polynomial.as_sum_range' P (w + 1) (Nat.lt_succ_of_le hP)
  simpa [Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem polySlash_neg_one {w : ℕ} {P : Polynomial ℂ} (hP : P.natDegree ≤ w) :
    polySlash w (-1 : Matrix (Fin 2) (Fin 2) ℤ) P = (-1 : ℂ) ^ w • P := by
  unfold polySlash
  have h1 : ∀ m ∈ Finset.range (w + 1),
      Polynomial.C (P.coeff m) *
        (Polynomial.C ((-1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * Polynomial.X +
          Polynomial.C ((-1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) ^ m *
        (Polynomial.C ((-1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * Polynomial.X +
          Polynomial.C ((-1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) ^ (w - m) =
      (-1 : ℂ) ^ w • (Polynomial.C (P.coeff m) * Polynomial.X ^ m) := by
    intro m hm
    have hmw : m ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hpow : (-1 : Polynomial ℂ) ^ m * (-1 : Polynomial ℂ) ^ (w - m) = (-1 : Polynomial ℂ) ^ w := by
      rw [← pow_add, Nat.add_sub_of_le hmw]
    simp only [Matrix.neg_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), neg_zero, Int.cast_neg, Int.cast_one,
      Int.cast_zero, map_neg, map_one, map_zero, zero_mul, zero_add, add_zero, neg_one_mul,
      Polynomial.smul_eq_C_mul]
    rw [neg_eq_neg_one_mul, mul_pow]
    calc Polynomial.C (P.coeff m) * ((-1 : Polynomial ℂ) ^ m * Polynomial.X ^ m) * (-1 : Polynomial ℂ) ^ (w - m)
        = ((-1 : Polynomial ℂ) ^ m * (-1 : Polynomial ℂ) ^ (w - m)) *
            (Polynomial.C (P.coeff m) * Polynomial.X ^ m) := by ring
      _ = (-1 : Polynomial ℂ) ^ w * (Polynomial.C (P.coeff m) * Polynomial.X ^ m) := by rw [hpow]
      _ = Polynomial.C ((-1 : ℂ) ^ w) * (Polynomial.C (P.coeff m) * Polynomial.X ^ m) := by simp
  rw [Finset.sum_congr rfl h1, ← Finset.smul_sum]
  congr 1
  have hsum := Polynomial.as_sum_range' P (w + 1) (Nat.lt_succ_of_le hP)
  simpa [Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

/-- Multiplicativity of `polySlash` across polynomial products:
`polySlash (w₁ + w₂) γ (Q₁ * Q₂) = polySlash w₁ γ Q₁ * polySlash w₂ γ Q₂` whenever
`Q₁.natDegree ≤ w₁` and `Q₂.natDegree ≤ w₂`. -/
theorem polySlash_mul_poly {w₁ w₂ : ℕ} (γ : Matrix (Fin 2) (Fin 2) ℤ)
    {Q₁ Q₂ : Polynomial ℂ} (hQ₁ : Q₁.natDegree ≤ w₁) (hQ₂ : Q₂.natDegree ≤ w₂) :
    polySlash (w₁ + w₂) γ (Q₁ * Q₂) = polySlash w₁ γ Q₁ * polySlash w₂ γ Q₂ := by
  have h1 : Q₁ = ∑ i ∈ Finset.range (w₁ + 1), Polynomial.C (Q₁.coeff i) * Polynomial.X ^ i := by
    simpa [Polynomial.C_mul_X_pow_eq_monomial] using
      (Polynomial.as_sum_range' Q₁ (w₁ + 1) (Nat.lt_succ_of_le hQ₁))
  have h2 : Q₂ = ∑ j ∈ Finset.range (w₂ + 1), Polynomial.C (Q₂.coeff j) * Polynomial.X ^ j := by
    simpa [Polynomial.C_mul_X_pow_eq_monomial] using
      (Polynomial.as_sum_range' Q₂ (w₂ + 1) (Nat.lt_succ_of_le hQ₂))
  conv_lhs => rw [h1, h2, Finset.sum_mul]
  rw [polySlash_sum]
  conv_rhs => rw [h1, h2, polySlash_sum, polySlash_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, polySlash_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hiw : i ≤ w₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hjw : j ≤ w₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hprod : (Polynomial.C (Q₁.coeff i) * Polynomial.X ^ i) *
      (Polynomial.C (Q₂.coeff j) * Polynomial.X ^ j) =
      Polynomial.C (Q₁.coeff i * Q₂.coeff j) * Polynomial.X ^ (i + j) := by
    rw [map_mul, pow_add]; ring
  rw [hprod, polySlash_monomial (w₁ + w₂) γ (Nat.add_le_add hiw hjw),
    polySlash_monomial w₁ γ hiw, polySlash_monomial w₂ γ hjw, map_mul, pow_add]
  have hsub : w₁ + w₂ - (i + j) = (w₁ - i) + (w₂ - j) := by omega
  rw [hsub, pow_add]
  ring

/-- `polySlash` on a power of a degree-`≤ 1` polynomial. -/
private lemma polySlash_pow_linear (m : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ)
    (L : Polynomial ℂ) (hL : L.natDegree ≤ 1) :
    polySlash m γ (L ^ m) = (polySlash 1 γ L) ^ m := by
  induction m with
  | zero =>
    simp [polySlash]
  | succ m ih =>
    have hLm : (L ^ m).natDegree ≤ m := by
      calc (L ^ m).natDegree ≤ m * L.natDegree := Polynomial.natDegree_pow_le
        _ ≤ m * 1 := Nat.mul_le_mul_left m hL
        _ = m := mul_one m
    rw [pow_succ, polySlash_mul_poly γ hLm hL, ih, pow_succ]

/-- Action of `polySlash 1 γ₂` on a linear polynomial `α X + β`. -/
private lemma polySlash_one_linear (γ : Matrix (Fin 2) (Fin 2) ℤ) (α β : ℂ) :
    polySlash 1 γ (Polynomial.C α * Polynomial.X + Polynomial.C β) =
      Polynomial.C (α * (γ 0 0 : ℂ) + β * (γ 1 0 : ℂ)) * Polynomial.X +
        Polynomial.C (α * (γ 0 1 : ℂ) + β * (γ 1 1 : ℂ)) := by
  unfold polySlash
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.sub_zero, Nat.sub_self, pow_zero, pow_one, mul_one,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
    Polynomial.coeff_X_one, Polynomial.coeff_C_zero, Polynomial.coeff_C_succ,
    mul_zero, zero_add, add_zero, map_add, map_mul]
  ring

/-- **Exact Right Group/Monoid Action Law for `polySlash`**:
for ALL `γ₁, γ₂ ∈ M₂(ℤ)` and EVERY polynomial `P` of degree `≤ w`,
`(P |_{-w} γ₁) |_{-w} γ₂ = P |_{-w} (γ₁ * γ₂)`. -/
theorem polySlash_mul {w : ℕ} (γ₁ γ₂ : Matrix (Fin 2) (Fin 2) ℤ)
    {P : Polynomial ℂ} (_hP : P.natDegree ≤ w) :
    polySlash w γ₂ (polySlash w γ₁ P) = polySlash w (γ₁ * γ₂) P := by
  conv_lhs => arg 3; unfold polySlash
  conv_rhs => unfold polySlash
  rw [polySlash_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmw : m ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  set L₁ : Polynomial ℂ := Polynomial.C (γ₁ 0 0 : ℂ) * Polynomial.X + Polynomial.C (γ₁ 0 1 : ℂ)
  set L₂ : Polynomial ℂ := Polynomial.C (γ₁ 1 0 : ℂ) * Polynomial.X + Polynomial.C (γ₁ 1 1 : ℂ)
  have hL₁ : L₁.natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  have hL₂ : L₂.natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  have hdeg1 : (L₁ ^ m).natDegree ≤ m := by
    calc (L₁ ^ m).natDegree ≤ m * L₁.natDegree := Polynomial.natDegree_pow_le
      _ ≤ m * 1 := Nat.mul_le_mul_left m hL₁
      _ = m := mul_one m
  have hdeg2 : (L₂ ^ (w - m)).natDegree ≤ w - m := by
    calc (L₂ ^ (w - m)).natDegree ≤ (w - m) * L₂.natDegree := Polynomial.natDegree_pow_le
      _ ≤ (w - m) * 1 := Nat.mul_le_mul_left (w - m) hL₂
      _ = w - m := mul_one (w - m)
  have hsmul : Polynomial.C (P.coeff m) * L₁ ^ m * L₂ ^ (w - m) =
      P.coeff m • (L₁ ^ m * L₂ ^ (w - m)) := by
    rw [Polynomial.smul_eq_C_mul]; ring
  rw [hsmul, polySlash_smul]
  have hsplit : polySlash w γ₂ (L₁ ^ m * L₂ ^ (w - m)) =
      polySlash m γ₂ (L₁ ^ m) * polySlash (w - m) γ₂ (L₂ ^ (w - m)) := by
    have h := polySlash_mul_poly γ₂ hdeg1 hdeg2
    rwa [Nat.add_sub_of_le hmw] at h
  rw [hsplit, polySlash_pow_linear m γ₂ L₁ hL₁, polySlash_pow_linear (w - m) γ₂ L₂ hL₂,
    Polynomial.smul_eq_C_mul, ← mul_assoc]
  have hL1_act : polySlash 1 γ₂ L₁ =
      Polynomial.C ((γ₁ * γ₂) 0 0 : ℂ) * Polynomial.X + Polynomial.C ((γ₁ * γ₂) 0 1 : ℂ) := by
    dsimp only [L₁]
    rw [polySlash_one_linear]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hL2_act : polySlash 1 γ₂ L₂ =
      Polynomial.C ((γ₁ * γ₂) 1 0 : ℂ) * Polynomial.X + Polynomial.C ((γ₁ * γ₂) 1 1 : ℂ) := by
    dsimp only [L₂]
    rw [polySlash_one_linear]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hL1_act, hL2_act]

end PolynomialSlashAction

/-! ## Section 3: Period Polynomial `periodPoly`, Vertical-Ray 1-Cocycle, & Eichler–Shimura–Manin Relations -/

section PeriodPolynomialAndCocycle

/-- The `j`-th period integral of a level-1 cusp form `f ∈ S_k(SL₂(ℤ))`:
`cuspPeriod f j = ∫_{t > 0} f(i t) (i t)^j i dt = i^{j+1} Λ(f, j + 1)`. -/
def cuspPeriod {k : ℤ} (f : CuspForm SL2ZRange k) (j : ℕ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), cuspImag f t * (Complex.I * (t : ℂ)) ^ j * Complex.I

/-- Exact identification of `cuspPeriod f j` with Hecke's completed `L`-value `Λ(f, j + 1)`. -/
theorem cuspPeriod_eq_completedCuspL {k : ℤ} (f : CuspForm SL2ZRange k) (j : ℕ) :
    cuspPeriod f j = Complex.I ^ (j + 1) * completedCuspL f ((j : ℂ) + 1) := by
  unfold cuspPeriod completedCuspL
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hcpow : (t : ℂ) ^ (((j : ℂ) + 1) - 1) = (t : ℂ) ^ j := by
    rw [add_sub_cancel_right, Complex.cpow_natCast]
  rw [hcpow, mul_pow, pow_succ]
  ring

/-- **Concrete Eichler–Shimura Period Polynomial `periodPoly f ∈ ℂ[X]`** of a weight-`k`
level-1 cusp form `f ∈ S_k(SL₂(ℤ))`, representing `∫_0^{i∞} f(τ) (X - τ)^{k - 2} dτ`. -/
def periodPoly {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k - 1),
    Polynomial.C ((-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * cuspPeriod f j) *
      Polynomial.X ^ (k - 2 - j)

theorem periodPoly_natDegree_le {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) :
    (periodPoly f).natDegree ≤ k - 2 := by
  unfold periodPoly
  refine natDegree_finsetSum_le _ _ (k - 2) fun j _ => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  omega

theorem periodPoly_coeff {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {m : ℕ} (hm : m ≤ k - 2) :
    (periodPoly f).coeff m =
      (-1 : ℂ) ^ (k - 2 - m) * ((k - 2).choose (k - 2 - m) : ℂ) * cuspPeriod f (k - 2 - m) := by
  unfold periodPoly
  rw [Polynomial.finsetSum_coeff]
  have hmem : k - 2 - m ∈ Finset.range (k - 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single (k - 2 - m)]
  · have hsub : k - 2 - (k - 2 - m) = m := by omega
    rw [hsub, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro j hj hne
    have hlt : j < k - 1 := Finset.mem_range.mp hj
    have hne' : k - 2 - j ≠ m := by omega
    rw [Polynomial.coeff_C_mul_X_pow, if_neg hne'.symm]
  · intro hnot; exact absurd hmem hnot

/-- Exact evaluation formula for `periodPoly f` as a single vertical-axis integral. -/
theorem periodPoly_eval {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) (X : ℂ) :
    (periodPoly f).eval X =
      ∫ t in Set.Ioi (0 : ℝ), cuspImag f t * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I := by
  unfold periodPoly
  rw [Polynomial.eval_finsetSum]
  have hterm : ∀ j ∈ Finset.range (k - 1),
      (Polynomial.C ((-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * cuspPeriod f j) *
        Polynomial.X ^ (k - 2 - j)).eval X =
      ∫ t in Set.Ioi (0 : ℝ),
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) *
          (cuspImag f t * (Complex.I * (t : ℂ)) ^ j * Complex.I) := by
    intro j _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      cuspPeriod, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [Finset.sum_congr rfl hterm]
  have hint : ∀ j ∈ Finset.range (k - 1),
      IntegrableOn (fun t : ℝ =>
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) *
          (cuspImag f t * (Complex.I * (t : ℂ)) ^ j * Complex.I)) (Set.Ioi 0) volume := by
    intro j _
    refine Integrable.const_mul ?_ _
    have hmell : IntegrableOn (fun t : ℝ => cuspImag f t * (t : ℂ) ^ (((j : ℂ) + 1) - 1))
        (Set.Ioi 0) volume := by
      refine (mellinConvergent_cuspImag f ((j : ℂ) + 1)).congr_fun (fun t _ => ?_) measurableSet_Ioi
      dsimp only; rw [smul_eq_mul, mul_comm]
    refine IntegrableOn.congr_fun (hmell.const_mul (Complex.I ^ (j + 1))) (fun t _ => ?_)
      measurableSet_Ioi
    rw [add_sub_cancel_right, Complex.cpow_natCast, mul_pow, pow_succ]
    ring
  rw [← MeasureTheory.integral_finsetSum _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hbinom : (X - Complex.I * (t : ℂ)) ^ (k - 2) =
      ∑ j ∈ Finset.range (k - 1),
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) * (Complex.I * (t : ℂ)) ^ j := by
    have hr : k - 1 = (k - 2) + 1 := by omega
    rw [hr, sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  rw [hbinom, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The modular inversion matrix `S = [[0, -1], [1, 0]]`. -/
def matS : Matrix (Fin 2) (Fin 2) ℤ :=
  (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)

/-- The order-3 modular matrix `U = S * T = [[0, -1], [1, 1]]` (`U^3 = -I`). -/
def matU : Matrix (Fin 2) (Fin 2) ℤ :=
  ((ModularGroup.S * ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ)

private lemma matS_eq : matS = !![0, -1; 1, 0] := rfl

private lemma matU_eq : matU = !![0, -1; 1, 1] := by
  unfold matU
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two]

private lemma matU_sq_eq : matU ^ 2 = !![-1, -1; 1, 0] := by
  rw [sq, matU_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **UNCONDITIONAL 2-TERM `S`-RELATION FOR EVERY LEVEL-1 CUSP FORM (Eichler–Shimura–Manin)**:
for EVERY `k ≥ 2` and EVERY `f ∈ S_k(SL₂(ℤ))`,
`periodPoly f + (periodPoly f |_{2 - k} S) = 0`. -/
theorem periodPoly_S_relation {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    periodPoly f + polySlash (k - 2) matS (periodPoly f) = 0 := by
  have hS_entries : matS 0 0 = 0 ∧ matS 0 1 = -1 ∧ matS 1 0 = 1 ∧ matS 1 1 = 0 := by
    rw [matS_eq]; decide
  -- Expand `polySlash (k - 2) matS (periodPoly f)` term by term
  have hslash : polySlash (k - 2) matS (periodPoly f) =
      ∑ m ∈ Finset.range (k - 1),
        Polynomial.C ((periodPoly f).coeff m * (-1 : ℂ) ^ m) * Polynomial.X ^ (k - 2 - m) := by
    unfold polySlash
    have hr : (k - 2) + 1 = k - 1 := by omega
    rw [hr]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hS_entries.1, hS_entries.2.1, hS_entries.2.2.1, hS_entries.2.2.2]
    simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, map_zero, map_neg, map_one,
      zero_mul, zero_add, one_mul, add_zero, map_mul, map_pow]
  rw [hslash]
  conv_lhs => arg 1; unfold periodPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjk : j ≤ k - 2 := by
    have := Finset.mem_range.mp hj; omega
  rw [periodPoly_coeff hk f hjk, ← add_mul]
  suffices hzero : (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * cuspPeriod f j +
      (-1 : ℂ) ^ (k - 2 - j) * ((k - 2).choose (k - 2 - j) : ℂ) *
        cuspPeriod f (k - 2 - j) * (-1 : ℂ) ^ j = 0 by
    rw [← map_add, hzero, map_zero, zero_mul]
  rw [Nat.choose_symm hjk, cuspPeriod_eq_completedCuspL f j,
    cuspPeriod_eq_completedCuspL f (k - 2 - j)]
  have harg : (((k - 2 - j : ℕ) : ℂ) + 1) = ((k : ℤ) : ℂ) - ((j : ℂ) + 1) := by
    have : (k - 2 - j : ℕ) + (j + 1) + 1 = k := by omega
    have hC : ((k - 2 - j : ℕ) : ℂ) + ((j : ℂ) + 1) + 1 = (k : ℂ) := by exact_mod_cast this
    push_cast
    linear_combination hC
  rw [harg, completedCuspL_functional_equation f ((j : ℂ) + 1)]
  -- Simplify the exact power of `I` and `(-1)`
  have hI_rel : Complex.I ^ (k - 2 - j + 1) * Complex.I ^ (k : ℤ) * (-1 : ℂ) ^ (k - 2 - j) =
      -Complex.I ^ (j + 1) := by
    rw [zpow_natCast]
    have hexp : k - 2 - j + 1 + k = 2 * (k - 1 - j) + (j + 1) := by omega
    have hmul : Complex.I ^ (k - 2 - j + 1) * Complex.I ^ k =
        Complex.I ^ (2 * (k - 1 - j) + (j + 1)) := by
      rw [← pow_add, hexp]
    rw [hmul, pow_add, pow_mul, Complex.I_sq]
    have hsign : (-1 : ℂ) ^ (k - 1 - j) * (-1 : ℂ) ^ (k - 2 - j) = -1 := by
      rw [← pow_add]
      have hodd : k - 1 - j + (k - 2 - j) = 2 * (k - 2 - j) + 1 := by omega
      rw [hodd, pow_add, pow_mul]
      norm_num
    calc (-1 : ℂ) ^ (k - 1 - j) * Complex.I ^ (j + 1) * (-1 : ℂ) ^ (k - 2 - j)
        = ((-1 : ℂ) ^ (k - 1 - j) * (-1 : ℂ) ^ (k - 2 - j)) * Complex.I ^ (j + 1) := by ring
      _ = (-1) * Complex.I ^ (j + 1) := by rw [hsign]
      _ = -Complex.I ^ (j + 1) := by ring
  calc (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * (Complex.I ^ (j + 1) * completedCuspL f ((j : ℂ) + 1)) +
        (-1 : ℂ) ^ (k - 2 - j) * ((k - 2).choose j : ℂ) *
          (Complex.I ^ (k - 2 - j + 1) * (Complex.I ^ (k : ℤ) * completedCuspL f ((j : ℂ) + 1))) *
          (-1 : ℂ) ^ j
      = (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * completedCuspL f ((j : ℂ) + 1) *
          (Complex.I ^ (j + 1) +
            Complex.I ^ (k - 2 - j + 1) * Complex.I ^ (k : ℤ) * (-1 : ℂ) ^ (k - 2 - j)) := by ring
    _ = (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * completedCuspL f ((j : ℂ) + 1) *
          (Complex.I ^ (j + 1) + -Complex.I ^ (j + 1)) := by rw [hI_rel]
    _ = 0 := by ring

/-! ### Vertical-Ray Eichler–Shimura Primitive & 1-Cocycle -/

private lemma integral_Ioi_add_right (g : ℝ → ℂ) (a b : ℝ) :
    ∫ t in Set.Ioi a, g (t + b) = ∫ u in Set.Ioi (a + b), g u := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  conv_rhs => rw [← MeasureTheory.integral_add_right_eq_self _ b]
  congr 1; funext t
  by_cases ht : a < t
  · have htb : a + b < t + b := by linarith
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Set.indicator_of_mem (Set.mem_Ioi.mpr htb)]
  · have htb : ¬(a + b < t + b) := by linarith
    rw [Set.indicator_of_notMem (show t ∉ Set.Ioi a from ht),
      Set.indicator_of_notMem (show t + b ∉ Set.Ioi (a + b) from htb)]

private lemma integrableOn_Ioi_add_right {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntegrableOn g (Set.Ioi (a + b)) volume) :
    IntegrableOn (fun t => g (t + b)) (Set.Ioi a) volume := by
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at hg ⊢
  have hcomp := hg.comp_add_right b
  refine hcomp.congr (Eventually.of_forall fun t => ?_)
  dsimp only
  by_cases ht : a < t
  · have htb : a + b < t + b := by linarith
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Set.indicator_of_mem (Set.mem_Ioi.mpr htb)]
  · have htb : ¬(a + b < t + b) := by linarith
    rw [Set.indicator_of_notMem (show t ∉ Set.Ioi a from ht),
      Set.indicator_of_notMem (show t + b ∉ Set.Ioi (a + b) from htb)]

private lemma integrableOn_Ioi_mul_left {g : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hg : IntegrableOn g (Set.Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t => g (c * t)) (Set.Ioi (0 : ℝ)) volume := by
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at hg ⊢
  have hcomp := hg.comp_mul_left' hc.ne'
  refine hcomp.congr (Eventually.of_forall fun t => ?_)
  dsimp only
  by_cases ht : 0 < t
  · have hct : 0 < c * t := mul_pos hc ht
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Set.indicator_of_mem (Set.mem_Ioi.mpr hct)]
  · have hct : ¬(0 < c * t) := fun h => ht (pos_of_mul_pos_right h hc.le)
    rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) from ht),
      Set.indicator_of_notMem (show c * t ∉ Set.Ioi (0 : ℝ) from hct)]

/-- Auxiliary integrability of `(t + A)^m * exp(-2π t)` on `Set.Ioi 0`. -/
private lemma integrableOn_pow_add_mul_exp_neg_two_pi (A : ℝ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => (t + A) ^ m * Real.exp (-2 * Real.pi * t)) (Set.Ioi 0) volume := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : ∀ j : ℕ, IntegrableOn (fun t : ℝ => t ^ j * Real.exp (-2 * Real.pi * t))
      (Set.Ioi 0) volume := by
    intro j
    have hbase := integrableOn_exp_neg_mul_rpow h2pi (by positivity : (0 : ℝ) < (j : ℝ) + 1)
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    dsimp only
    rw [add_sub_cancel_right, Real.rpow_natCast, mul_comm]
    congr 2; ring
  have hexp : (fun t : ℝ => (t + A) ^ m * Real.exp (-2 * Real.pi * t)) =
      fun t : ℝ => ∑ j ∈ Finset.range (m + 1),
        (A ^ (m - j) * (m.choose j : ℝ)) * (t ^ j * Real.exp (-2 * Real.pi * t)) := by
    funext t
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  exact integrable_finsetSum _ fun j _ => (h1 j).const_mul _

/-- Integrability of `t ↦ f(z + i t) * (X - (z + i t))^w * i` on `Set.Ioi 0` for `0 < z.im`. -/
private lemma integrableOn_cuspPrimitive_integrand {k : ℤ} (f : CuspForm SL2ZRange k)
    (w : ℕ) (X : ℂ) {z : ℂ} (hz : 0 < z.im) :
    IntegrableOn (fun t : ℝ => cuspToComplex f (z + Complex.I * (t : ℂ)) *
      (X - (z + Complex.I * (t : ℂ))) ^ w * Complex.I) (Set.Ioi 0) volume := by
  obtain ⟨C, hC_pos, hC⟩ := cuspForm_exp_decay_horizontal f hz
  have hmeas : AEStronglyMeasurable (fun t : ℝ => cuspToComplex f (z + Complex.I * (t : ℂ)) *
      (X - (z + Complex.I * (t : ℂ))) ^ w * Complex.I) (volume.restrict (Set.Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hline : ContinuousOn (fun t : ℝ => z + Complex.I * (t : ℂ)) (Set.Ioi 0) :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    have hf_cont : ContinuousOn (fun t : ℝ => cuspToComplex f (z + Complex.I * (t : ℂ))) (Set.Ioi 0) := by
      refine (differentiableOn_cuspToComplex f).continuousOn.comp hline ?_
      intro t ht
      change 0 < (z + Complex.I * (t : ℂ)).im
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
      linarith [Set.mem_Ioi.mp ht]
    exact (hf_cont.mul ((continuousOn_const.sub hline).pow w)).mul continuousOn_const
  have hdom : IntegrableOn (fun t : ℝ => C * ((t + ‖X - z‖) ^ w * Real.exp (-2 * Real.pi * t)))
      (Set.Ioi 0) volume :=
    (integrableOn_pow_add_mul_exp_neg_two_pi ‖X - z‖ w).const_mul C
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have him : z.im ≤ (z + Complex.I * (t : ℂ)).im := by simp [ht0.le]
  have him_pos : 0 < (z + Complex.I * (t : ℂ)).im := lt_of_lt_of_le hz him
  let τ : UpperHalfPlane := ⟨z + Complex.I * (t : ℂ), him_pos⟩
  have hf_bd : ‖cuspToComplex f (z + Complex.I * (t : ℂ))‖ ≤ C * Real.exp (-2 * Real.pi * t) := by
    rw [show cuspToComplex f (z + Complex.I * (t : ℂ)) = f τ from cuspToComplex_eq f τ]
    have h1 := hC τ him
    have him_eq : τ.im = z.im + t := by simp [τ]
    rw [him_eq] at h1
    have h2 : Real.exp (-2 * Real.pi * (z.im + t)) ≤ Real.exp (-2 * Real.pi * t) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hz])
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC_pos.le)
  have hpoly_bd : ‖(X - (z + Complex.I * (t : ℂ))) ^ w‖ ≤ (t + ‖X - z‖) ^ w := by
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ w
    have hsub : X - (z + Complex.I * (t : ℂ)) = (X - z) - Complex.I * (t : ℂ) := by ring
    rw [hsub]
    calc ‖(X - z) - Complex.I * (t : ℂ)‖
        ≤ ‖X - z‖ + ‖Complex.I * (t : ℂ)‖ := norm_sub_le _ _
      _ = ‖X - z‖ + t := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      _ = t + ‖X - z‖ := add_comm _ _
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
  calc ‖cuspToComplex f (z + Complex.I * (t : ℂ))‖ * ‖(X - (z + Complex.I * (t : ℂ))) ^ w‖
      ≤ (C * Real.exp (-2 * Real.pi * t)) * (t + ‖X - z‖) ^ w :=
        mul_le_mul hf_bd hpoly_bd (norm_nonneg _) (mul_nonneg hC_pos.le (Real.exp_pos _).le)
    _ = C * ((t + ‖X - z‖) ^ w * Real.exp (-2 * Real.pi * t)) := by ring

/-- Concrete vertical-ray primitive integral `F_X(z) = ∫_{t > 0} f(z + i t) (X - (z + i t))^w i dt`
for `z : ℂ` (used on the upper half-plane `{z | 0 < z.im}`). -/
def cuspPrimitiveEval {k : ℤ} (f : CuspForm SL2ZRange k) (w : ℕ) (X z : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    cuspToComplex f (z + Complex.I * (t : ℂ)) * (X - (z + Complex.I * (t : ℂ))) ^ w * Complex.I

/-- Concrete polynomial-valued vertical-ray primitive `F(z) ∈ ℂ[X]` for `z : UpperHalfPlane`. -/
def cuspPrimitive {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) (z : UpperHalfPlane) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k - 1),
    Polynomial.C ((-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) *
      ∫ t in Set.Ioi (0 : ℝ),
        cuspToComplex f ((z : ℂ) + Complex.I * (t : ℂ)) *
          ((z : ℂ) + Complex.I * (t : ℂ)) ^ j * Complex.I) *
      Polynomial.X ^ (k - 2 - j)

theorem cuspPrimitive_natDegree_le {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) (z : UpperHalfPlane) :
    (cuspPrimitive f z).natDegree ≤ k - 2 := by
  unfold cuspPrimitive
  refine natDegree_finsetSum_le _ _ (k - 2) fun j _ => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  omega

theorem cuspPrimitive_eval {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    (z : UpperHalfPlane) (X : ℂ) :
    (cuspPrimitive f z).eval X = cuspPrimitiveEval f (k - 2) X (z : ℂ) := by
  unfold cuspPrimitive cuspPrimitiveEval
  rw [Polynomial.eval_finsetSum]
  have hterm : ∀ j ∈ Finset.range (k - 1),
      (Polynomial.C ((-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) *
        ∫ t in Set.Ioi (0 : ℝ),
          cuspToComplex f ((z : ℂ) + Complex.I * (t : ℂ)) *
            ((z : ℂ) + Complex.I * (t : ℂ)) ^ j * Complex.I) *
        Polynomial.X ^ (k - 2 - j)).eval X =
      ∫ t in Set.Ioi (0 : ℝ),
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) *
          (cuspToComplex f ((z : ℂ) + Complex.I * (t : ℂ)) *
            ((z : ℂ) + Complex.I * (t : ℂ)) ^ j * Complex.I) := by
    intro j _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [Finset.sum_congr rfl hterm]
  have hint : ∀ j ∈ Finset.range (k - 1),
      IntegrableOn (fun t : ℝ =>
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) *
          (cuspToComplex f ((z : ℂ) + Complex.I * (t : ℂ)) *
            ((z : ℂ) + Complex.I * (t : ℂ)) ^ j * Complex.I)) (Set.Ioi 0) volume := by
    intro j _
    refine Integrable.const_mul ?_ _
    have hbase := integrableOn_cuspPrimitive_integrand f j 0 z.im_pos
    refine IntegrableOn.congr_fun (hbase.const_mul ((-1 : ℂ) ^ j)) (fun t _ => ?_) measurableSet_Ioi
    rw [zero_sub, neg_pow ((z : ℂ) + Complex.I * (t : ℂ))]
    have hsq : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
      rw [← mul_pow]; norm_num
    calc (-1 : ℂ) ^ j * (cuspToComplex f ((z : ℂ) + Complex.I * (t : ℂ)) *
            ((-1 : ℂ) ^ j * ((z : ℂ) + Complex.I * (t : ℂ)) ^ j) * Complex.I)
        = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) *
            (cuspToComplex f ((z : ℂ) + Complex.I * (t : ℂ)) *
              ((z : ℂ) + Complex.I * (t : ℂ)) ^ j * Complex.I) := by ring
      _ = cuspToComplex f ((z : ℂ) + Complex.I * (t : ℂ)) *
            ((z : ℂ) + Complex.I * (t : ℂ)) ^ j * Complex.I := by rw [hsq, one_mul]
  rw [← MeasureTheory.integral_finsetSum _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hbinom : (X - ((z : ℂ) + Complex.I * (t : ℂ))) ^ (k - 2) =
      ∑ j ∈ Finset.range (k - 1),
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) *
          ((z : ℂ) + Complex.I * (t : ℂ)) ^ j := by
    have hr : k - 1 = (k - 2) + 1 := by omega
    rw [hr, sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  rw [hbinom, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- **Exact Complex Derivative of the Vertical-Ray Primitive**:
for every `f ∈ S_k(SL₂(ℤ))`, `w : ℕ`, `X : ℂ`, and `z₀ ∈ ℂ` with `0 < z₀.im`,
`d/dz (cuspPrimitiveEval f w X z) |_{z = z₀} = -f(z₀) * (X - z₀)^w`. -/
theorem hasDerivAt_cuspPrimitiveEval {k : ℤ} (f : CuspForm SL2ZRange k)
    (w : ℕ) (X : ℂ) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    HasDerivAt (cuspPrimitiveEval f w X)
      (-(cuspToComplex f z₀ * (X - z₀) ^ w)) z₀ := by
  let g : ℂ → ℂ := fun u => cuspToComplex f u * (X - u) ^ w
  have hg_diff : DifferentiableOn ℂ g {u : ℂ | 0 < u.im} :=
    (differentiableOn_cuspToComplex f).mul ((differentiableOn_const X).sub differentiableOn_id |>.pow w)
  have hg_hasDeriv : ∀ u : ℂ, 0 < u.im →
      HasDerivAt g (deriv (cuspToComplex f) u * (X - u) ^ w +
        cuspToComplex f u * (-((w : ℂ) * (X - u) ^ (w - 1)))) u := by
    intro u hu
    have hopen : IsOpen {v : ℂ | 0 < v.im} := isOpen_lt continuous_const Complex.continuous_im
    have hf_at : HasDerivAt (cuspToComplex f) (deriv (cuspToComplex f) u) u :=
      ((differentiableOn_cuspToComplex f).differentiableAt (hopen.mem_nhds hu)).hasDerivAt
    have hsub : HasDerivAt (fun v : ℂ => X - v) (-1) u := by
      simpa [sub_eq_add_neg] using (hasDerivAt_id u).neg.const_add X
    have hpow : HasDerivAt (fun v => (X - v) ^ w) ((w : ℂ) * (X - u) ^ (w - 1) * (-1)) u :=
      hsub.pow w
    refine (hf_at.mul hpow).congr_deriv ?_
    ring
  let g' : ℂ → ℂ := fun u => deriv (cuspToComplex f) u * (X - u) ^ w +
    cuspToComplex f u * (-((w : ℂ) * (X - u) ^ (w - 1)))
  -- Step 1: Differentiate under the integral sign on `ball z₀ r` with `r = z₀.im / 2`
  set r : ℝ := z₀.im / 2 with hr_def
  have hr : 0 < r := half_pos hz₀
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := cuspForm_exp_decay_horizontal f hr
  obtain ⟨C₂, hC₂_pos, hC₂⟩ := cuspForm_exp_decay_deriv_horizontal f hr
  let A : ℝ := ‖X - z₀‖ + r
  let bound : ℝ → ℝ := fun t =>
    C₂ * ((t + A) ^ w * Real.exp (-2 * Real.pi * t)) +
      C₁ * (w : ℝ) * ((t + A) ^ (w - 1) * Real.exp (-2 * Real.pi * t))
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) :=
    ((integrableOn_pow_add_mul_exp_neg_two_pi A w).const_mul C₂).add
      ((integrableOn_pow_add_mul_exp_neg_two_pi A (w - 1)).const_mul (C₁ * (w : ℝ)))
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable
      (fun t : ℝ => g (z + Complex.I * (t : ℂ)) * Complex.I) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
    have hzim : r < z.im := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hsub := (abs_lt.mp ((Complex.abs_im_le_norm (z - z₀)).trans_lt hz)).1
      rw [Complex.sub_im] at hsub
      linarith [hr_def]
    exact (integrableOn_cuspPrimitive_integrand f w X (hr.trans hzim)).aestronglyMeasurable
  have hF_int : Integrable (fun t : ℝ => g (z₀ + Complex.I * (t : ℂ)) * Complex.I)
      (volume.restrict (Set.Ioi 0)) :=
    integrableOn_cuspPrimitive_integrand f w X hz₀
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => g' (z₀ + Complex.I * (t : ℂ)) * Complex.I) (volume.restrict (Set.Ioi 0)) := by
    have hopen : IsOpen {v : ℂ | 0 < v.im} := isOpen_lt continuous_const Complex.continuous_im
    have hf'_diff : DifferentiableOn ℂ (deriv (cuspToComplex f)) {v : ℂ | 0 < v.im} :=
      (differentiableOn_cuspToComplex f).deriv hopen
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hline : ContinuousOn (fun t : ℝ => z₀ + Complex.I * (t : ℂ)) (Set.Ioi 0) :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => z₀ + Complex.I * (t : ℂ)) (Set.Ioi 0) {v : ℂ | 0 < v.im} := by
      intro t ht; change 0 < (z₀ + Complex.I * (t : ℂ)).im; simp; linarith [Set.mem_Ioi.mp ht]
    have h1 := (hf'_diff.continuousOn.comp hline hmaps).mul (((continuousOn_const (c := X)).sub hline).pow w)
    have h2 := ((differentiableOn_cuspToComplex f).continuousOn.comp hline hmaps).mul
      (((continuousOn_const (c := (w : ℂ))).mul (((continuousOn_const (c := X)).sub hline).pow (w - 1))).neg)
    exact (h1.add h2).mul continuousOn_const
  have hdiff_int : HasDerivAt (cuspPrimitiveEval f w X)
      (∫ t in Set.Ioi (0 : ℝ), g' (z₀ + Complex.I * (t : ℂ)) * Complex.I) z₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (z : ℂ) (t : ℝ) => g (z + Complex.I * (t : ℂ)) * Complex.I)
      (F' := fun (z : ℂ) (t : ℝ) => g' (z + Complex.I * (t : ℂ)) * Complex.I)
      (Metric.ball_mem_nhds z₀ hr) hF_meas hF_int hF'_meas ?_ hbound_int ?_).2
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hz => ?_)
      have ht0 : 0 < t := ht
      have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hzim : r < z.im := by
        have hsub := (abs_lt.mp ((Complex.abs_im_le_norm (z - z₀)).trans_lt hdist)).1
        rw [Complex.sub_im] at hsub
        linarith [hr_def]
      have him_ge : r ≤ (z + Complex.I * (t : ℂ)).im := by simp; linarith
      have him_pos : 0 < (z + Complex.I * (t : ℂ)).im := lt_of_lt_of_le hr him_ge
      have hexp_le : Real.exp (-2 * Real.pi * (z + Complex.I * (t : ℂ)).im) ≤
          Real.exp (-2 * Real.pi * t) := by
        apply Real.exp_le_exp.mpr
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        nlinarith [Real.pi_pos, hr, hzim]
      have hsub_le : ‖X - (z + Complex.I * (t : ℂ))‖ ≤ t + A := by
        have heq : X - (z + Complex.I * (t : ℂ)) =
            (X - z₀) - (z - z₀) - Complex.I * (t : ℂ) := by ring
        rw [heq]
        calc ‖(X - z₀) - (z - z₀) - Complex.I * (t : ℂ)‖
            ≤ ‖(X - z₀) - (z - z₀)‖ + ‖Complex.I * (t : ℂ)‖ := norm_sub_le _ _
          _ ≤ (‖X - z₀‖ + ‖z - z₀‖) + t := by
              gcongr
              · exact norm_sub_le _ _
              · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
                  Real.norm_of_nonneg ht0.le]
          _ ≤ (‖X - z₀‖ + r) + t := by linarith
          _ = t + A := by dsimp only [A]; ring
      have hf_bd : ‖cuspToComplex f (z + Complex.I * (t : ℂ))‖ ≤ C₁ * Real.exp (-2 * Real.pi * t) := by
        let τ : UpperHalfPlane := ⟨z + Complex.I * (t : ℂ), him_pos⟩
        rw [show cuspToComplex f (z + Complex.I * (t : ℂ)) = f τ from cuspToComplex_eq f τ]
        exact (hC₁ τ him_ge).trans (mul_le_mul_of_nonneg_left hexp_le hC₁_pos.le)
      have hf'_bd : ‖deriv (cuspToComplex f) (z + Complex.I * (t : ℂ))‖ ≤
          C₂ * Real.exp (-2 * Real.pi * t) :=
        (hC₂ _ him_ge).trans (mul_le_mul_of_nonneg_left hexp_le hC₂_pos.le)
      rw [norm_mul, Complex.norm_I, mul_one]
      dsimp only [g', bound]
      calc ‖deriv (cuspToComplex f) (z + Complex.I * (t : ℂ)) * (X - (z + Complex.I * (t : ℂ))) ^ w +
              cuspToComplex f (z + Complex.I * (t : ℂ)) *
                (-((w : ℂ) * (X - (z + Complex.I * (t : ℂ))) ^ (w - 1)))‖
          ≤ ‖deriv (cuspToComplex f) (z + Complex.I * (t : ℂ)) * (X - (z + Complex.I * (t : ℂ))) ^ w‖ +
            ‖cuspToComplex f (z + Complex.I * (t : ℂ)) *
              (-((w : ℂ) * (X - (z + Complex.I * (t : ℂ))) ^ (w - 1)))‖ := norm_add_le _ _
        _ = ‖deriv (cuspToComplex f) (z + Complex.I * (t : ℂ))‖ * ‖X - (z + Complex.I * (t : ℂ))‖ ^ w +
            ‖cuspToComplex f (z + Complex.I * (t : ℂ))‖ * ((w : ℝ) * ‖X - (z + Complex.I * (t : ℂ))‖ ^ (w - 1)) := by
            rw [norm_mul, norm_pow, norm_mul, norm_neg, norm_mul, Complex.norm_natCast, norm_pow]
        _ ≤ (C₂ * Real.exp (-2 * Real.pi * t)) * (t + A) ^ w +
            (C₁ * Real.exp (-2 * Real.pi * t)) * ((w : ℝ) * (t + A) ^ (w - 1)) := by
            gcongr
        _ = C₂ * ((t + A) ^ w * Real.exp (-2 * Real.pi * t)) +
            C₁ * (w : ℝ) * ((t + A) ^ (w - 1) * Real.exp (-2 * Real.pi * t)) := by ring
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hz => ?_)
      have ht0 : 0 < t := ht
      have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hzim : r < z.im := by
        have hsub := (abs_lt.mp ((Complex.abs_im_le_norm (z - z₀)).trans_lt hdist)).1
        rw [Complex.sub_im] at hsub
        linarith [hr_def]
      have him_pos : 0 < (z + Complex.I * (t : ℂ)).im := by simp; linarith
      have hshift : HasDerivAt (fun v => v + Complex.I * (t : ℂ)) 1 z := by
        simpa using (hasDerivAt_id z).add_const (Complex.I * (t : ℂ))
      have hcomp := (hg_hasDeriv _ him_pos).comp z hshift
      rw [mul_one] at hcomp
      exact hcomp.mul_const Complex.I
  -- Step 2: Evaluate `∫_{t > 0} g'(z₀ + i t) * i dt = -g(z₀)` by 1D FTC and `T → ∞`
  have hval : (∫ t in Set.Ioi (0 : ℝ), g' (z₀ + Complex.I * (t : ℂ)) * Complex.I) = -g z₀ := by
    have hftc : ∀ T : ℝ, 0 ≤ T →
        (∫ t in (0 : ℝ)..T, g' (z₀ + Complex.I * (t : ℂ)) * Complex.I) =
          g (z₀ + Complex.I * (T : ℂ)) - g z₀ := by
      intro T hT
      have hderiv_t : ∀ t ∈ Set.uIcc (0 : ℝ) T,
          HasDerivAt (fun s : ℝ => g (z₀ + Complex.I * (s : ℂ)))
            (g' (z₀ + Complex.I * (t : ℂ)) * Complex.I) t := by
        intro t ht
        rw [Set.uIcc_of_le hT] at ht
        have him_pos : 0 < (z₀ + Complex.I * (t : ℂ)).im := by simp; linarith [ht.1]
        have hline : HasDerivAt (fun s : ℝ => z₀ + Complex.I * (s : ℂ)) Complex.I t := by
          have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
          simpa using (h1.const_mul Complex.I).const_add z₀
        have hcomp := ((hg_hasDeriv _ him_pos).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hline
        refine hcomp.congr_deriv ?_
        change Complex.I • g' (z₀ + Complex.I * (t : ℂ)) = g' (z₀ + Complex.I * (t : ℂ)) * Complex.I
        rw [smul_eq_mul, mul_comm]
      have hcont_t : ContinuousOn (fun t : ℝ => g' (z₀ + Complex.I * (t : ℂ)) * Complex.I)
          (Set.uIcc (0 : ℝ) T) := by
        rw [Set.uIcc_of_le hT]
        have hopen : IsOpen {v : ℂ | 0 < v.im} := isOpen_lt continuous_const Complex.continuous_im
        have hf'_diff : DifferentiableOn ℂ (deriv (cuspToComplex f)) {v : ℂ | 0 < v.im} :=
          (differentiableOn_cuspToComplex f).deriv hopen
        have hline : ContinuousOn (fun t : ℝ => z₀ + Complex.I * (t : ℂ)) (Set.Icc 0 T) :=
          (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
        have hmaps : Set.MapsTo (fun t : ℝ => z₀ + Complex.I * (t : ℂ)) (Set.Icc 0 T)
            {v : ℂ | 0 < v.im} := by
          intro t ht; change 0 < (z₀ + Complex.I * (t : ℂ)).im; simp; linarith [ht.1]
        have h1 := (hf'_diff.continuousOn.comp hline hmaps).mul (((continuousOn_const (c := X)).sub hline).pow w)
        have h2 := ((differentiableOn_cuspToComplex f).continuousOn.comp hline hmaps).mul
          (((continuousOn_const (c := (w : ℂ))).mul (((continuousOn_const (c := X)).sub hline).pow (w - 1))).neg)
        exact (h1.add h2).mul continuousOn_const
      have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_t hcont_t.intervalIntegrable
      simpa using h1
    have hint_g' : IntegrableOn (fun t : ℝ => g' (z₀ + Complex.I * (t : ℂ)) * Complex.I)
        (Set.Ioi 0) volume := by
      refine hbound_int.mono' hF'_meas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      have him_ge : r ≤ (z₀ + Complex.I * (t : ℂ)).im := by simp; linarith [hr_def]
      have him_pos : 0 < (z₀ + Complex.I * (t : ℂ)).im := lt_of_lt_of_le hr him_ge
      have hexp_le : Real.exp (-2 * Real.pi * (z₀ + Complex.I * (t : ℂ)).im) ≤
          Real.exp (-2 * Real.pi * t) := by
        apply Real.exp_le_exp.mpr
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        nlinarith [Real.pi_pos, hz₀]
      have hsub_le : ‖X - (z₀ + Complex.I * (t : ℂ))‖ ≤ t + A := by
        have heq : X - (z₀ + Complex.I * (t : ℂ)) = (X - z₀) - Complex.I * (t : ℂ) := by ring
        rw [heq]
        calc ‖(X - z₀) - Complex.I * (t : ℂ)‖
            ≤ ‖X - z₀‖ + ‖Complex.I * (t : ℂ)‖ := norm_sub_le _ _
          _ = ‖X - z₀‖ + t := by
              rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
          _ ≤ t + A := by dsimp only [A]; linarith
      have hf_bd : ‖cuspToComplex f (z₀ + Complex.I * (t : ℂ))‖ ≤ C₁ * Real.exp (-2 * Real.pi * t) := by
        let τ : UpperHalfPlane := ⟨z₀ + Complex.I * (t : ℂ), him_pos⟩
        rw [show cuspToComplex f (z₀ + Complex.I * (t : ℂ)) = f τ from cuspToComplex_eq f τ]
        exact (hC₁ τ him_ge).trans (mul_le_mul_of_nonneg_left hexp_le hC₁_pos.le)
      have hf'_bd : ‖deriv (cuspToComplex f) (z₀ + Complex.I * (t : ℂ))‖ ≤
          C₂ * Real.exp (-2 * Real.pi * t) :=
        (hC₂ _ him_ge).trans (mul_le_mul_of_nonneg_left hexp_le hC₂_pos.le)
      rw [norm_mul, Complex.norm_I, mul_one]
      dsimp only [g', bound]
      calc ‖deriv (cuspToComplex f) (z₀ + Complex.I * (t : ℂ)) * (X - (z₀ + Complex.I * (t : ℂ))) ^ w +
              cuspToComplex f (z₀ + Complex.I * (t : ℂ)) *
                (-((w : ℂ) * (X - (z₀ + Complex.I * (t : ℂ))) ^ (w - 1)))‖
          ≤ ‖deriv (cuspToComplex f) (z₀ + Complex.I * (t : ℂ))‖ * ‖X - (z₀ + Complex.I * (t : ℂ))‖ ^ w +
            ‖cuspToComplex f (z₀ + Complex.I * (t : ℂ))‖ * ((w : ℝ) * ‖X - (z₀ + Complex.I * (t : ℂ))‖ ^ (w - 1)) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_pow, norm_mul, norm_neg, norm_mul, Complex.norm_natCast, norm_pow]
        _ ≤ (C₂ * Real.exp (-2 * Real.pi * t)) * (t + A) ^ w +
            (C₁ * Real.exp (-2 * Real.pi * t)) * ((w : ℝ) * (t + A) ^ (w - 1)) := by gcongr
        _ = C₂ * ((t + A) ^ w * Real.exp (-2 * Real.pi * t)) +
            C₁ * (w : ℝ) * ((t + A) ^ (w - 1) * Real.exp (-2 * Real.pi * t)) := by ring
    have hlim_int : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, g' (z₀ + Complex.I * (t : ℂ)) * Complex.I)
        atTop (nhds (∫ t in Set.Ioi (0 : ℝ), g' (z₀ + Complex.I * (t : ℂ)) * Complex.I)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hint_g' tendsto_id
    have hlim_end : Tendsto (fun T : ℝ => g (z₀ + Complex.I * (T : ℂ)) - g z₀)
        atTop (nhds (-g z₀)) := by
      have hg_zero : Tendsto (fun T : ℝ => g (z₀ + Complex.I * (T : ℂ))) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hdom_zero : Tendsto (fun T : ℝ =>
            C₁ * ((T + ‖X - z₀‖) ^ w * Real.exp (-2 * Real.pi * T))) atTop (nhds 0) := by
          have hterm : ∀ j : ℕ, Tendsto (fun T : ℝ => T ^ j * Real.exp (-2 * Real.pi * T))
              atTop (nhds 0) := by
            intro j
            have hpow : Tendsto (fun u : ℝ => u ^ j * Real.exp (-u)) atTop (nhds 0) := by
              simpa [Real.exp_neg, div_eq_mul_inv] using
                Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j
            have h2pi : Tendsto (fun T : ℝ => 2 * Real.pi * T) atTop atTop :=
              Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) tendsto_id
            have hcomp := (hpow.comp h2pi).const_mul (((2 * Real.pi) ^ j)⁻¹)
            rw [mul_zero] at hcomp
            refine hcomp.congr fun T => ?_
            dsimp only [Function.comp_apply]
            have h2pi_ne : (2 * Real.pi) ^ j ≠ 0 := by positivity
            rw [show (2 * Real.pi * T) ^ j = (2 * Real.pi) ^ j * T ^ j from mul_pow (2 * Real.pi) T j,
              show -(2 * Real.pi * T) = -2 * Real.pi * T by ring]
            field_simp [h2pi_ne]
          have hsum : Tendsto (fun T : ℝ => ∑ j ∈ Finset.range (w + 1),
              (‖X - z₀‖ ^ (w - j) * (w.choose j : ℝ)) * (T ^ j * Real.exp (-2 * Real.pi * T)))
              atTop (nhds 0) := by
            have h := tendsto_finsetSum (Finset.range (w + 1)) fun j _ =>
              (hterm j).const_mul (‖X - z₀‖ ^ (w - j) * (w.choose j : ℝ))
            simpa using h
          have hcomb := hsum.const_mul C₁
          rw [mul_zero] at hcomb
          refine hcomb.congr fun T => ?_
          congr 1
          rw [add_pow, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by ring
        refine squeeze_zero_norm' ?_ hdom_zero
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        have him_ge : r ≤ (z₀ + Complex.I * (T : ℂ)).im := by simp; linarith [hr_def]
        have him_pos : 0 < (z₀ + Complex.I * (T : ℂ)).im := lt_of_lt_of_le hr him_ge
        let τ : UpperHalfPlane := ⟨z₀ + Complex.I * (T : ℂ), him_pos⟩
        have hf_bd : ‖cuspToComplex f (z₀ + Complex.I * (T : ℂ))‖ ≤ C₁ * Real.exp (-2 * Real.pi * T) := by
          rw [show cuspToComplex f (z₀ + Complex.I * (T : ℂ)) = f τ from cuspToComplex_eq f τ]
          have h1 := hC₁ τ him_ge
          have h2 : Real.exp (-2 * Real.pi * τ.im) ≤ Real.exp (-2 * Real.pi * T) := by
            apply Real.exp_le_exp.mpr
            simp only [τ, UpperHalfPlane.im, Complex.add_im, Complex.mul_im, Complex.I_re,
              Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
            nlinarith [Real.pi_pos, hz₀]
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hC₁_pos.le)
        have hpoly_bd : ‖(X - (z₀ + Complex.I * (T : ℂ))) ^ w‖ ≤ (T + ‖X - z₀‖) ^ w := by
          rw [norm_pow]
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ w
          rw [show X - (z₀ + Complex.I * (T : ℂ)) = (X - z₀) - Complex.I * (T : ℂ) by ring]
          calc ‖(X - z₀) - Complex.I * (T : ℂ)‖
              ≤ ‖X - z₀‖ + ‖Complex.I * (T : ℂ)‖ := norm_sub_le _ _
            _ = ‖X - z₀‖ + T := by
                rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hT]
            _ = T + ‖X - z₀‖ := add_comm _ _
        rw [norm_norm]
        dsimp only [g]
        rw [norm_mul]
        calc ‖cuspToComplex f (z₀ + Complex.I * (T : ℂ))‖ * ‖(X - (z₀ + Complex.I * (T : ℂ))) ^ w‖
            ≤ (C₁ * Real.exp (-2 * Real.pi * T)) * (T + ‖X - z₀‖) ^ w :=
              mul_le_mul hf_bd hpoly_bd (norm_nonneg _) (mul_nonneg hC₁_pos.le (Real.exp_pos _).le)
          _ = C₁ * ((T + ‖X - z₀‖) ^ w * Real.exp (-2 * Real.pi * T)) := by ring
      simpa using hg_zero.sub_const (g z₀)
    have hev : (fun T : ℝ => ∫ t in (0 : ℝ)..T, g' (z₀ + Complex.I * (t : ℂ)) * Complex.I) =ᶠ[atTop]
        fun T : ℝ => g (z₀ + Complex.I * (T : ℂ)) - g z₀ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact hftc T hT
    exact tendsto_nhds_unique (hlim_int.congr' hev) hlim_end
  rw [hval] at hdiff_int
  exact hdiff_int

/-- **Constancy of the Eichler–Shimura Coboundary**:
for every `f ∈ S_k(SL₂(ℤ))` (`k ≥ 2`) and every `γ ∈ SL₂(ℤ)`, the polynomial
`polySlash (k - 2) γ (cuspPrimitive f (γ • z)) - cuspPrimitive f z` is **independent of `z ∈ ℍ`**! -/
theorem cuspPrimitive_cocycle_const {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z₁ z₂ : UpperHalfPlane) :
    polySlash (k - 2) (γ : Matrix (Fin 2) (Fin 2) ℤ) (cuspPrimitive f (γ • z₁)) -
        cuspPrimitive f z₁ =
      polySlash (k - 2) (γ : Matrix (Fin 2) (Fin 2) ℤ) (cuspPrimitive f (γ • z₂)) -
        cuspPrimitive f z₂ := by
  set a : ℂ := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ)
  set b : ℂ := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)
  set c : ℂ := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ)
  set d : ℂ := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)
  have hdet : a * d - b * c = 1 := by
    have h := γ.prop
    rw [Matrix.det_fin_two] at h
    dsimp only [a, b, c, d]
    exact_mod_cast h
  -- It suffices to show both polynomials agree at infinitely many `X : ℂ` (every `X` with `c X + d ≠ 0`)
  let P₁ : Polynomial ℂ :=
    polySlash (k - 2) (γ : Matrix (Fin 2) (Fin 2) ℤ) (cuspPrimitive f (γ • z₁)) - cuspPrimitive f z₁
  let P₂ : Polynomial ℂ :=
    polySlash (k - 2) (γ : Matrix (Fin 2) (Fin 2) ℤ) (cuspPrimitive f (γ • z₂)) - cuspPrimitive f z₂
  have heval_eq : ∀ X : ℂ, c * X + d ≠ 0 → P₁.eval X = P₂.eval X := by
    intro X hX
    let Y : ℂ := (a * X + b) / (c * X + d)
    let mob : ℂ → ℂ := fun u => (a * u + b) / (c * u + d)
    let H : ℂ → ℂ := fun u =>
      (c * X + d) ^ (k - 2) * cuspPrimitiveEval f (k - 2) Y (mob u) -
        cuspPrimitiveEval f (k - 2) X u
    have hU_open : IsOpen {u : ℂ | 0 < u.im} := isOpen_lt continuous_const Complex.continuous_im
    have hU_conv : Convex ℝ {u : ℂ | 0 < u.im} := by
      intro u hu v hv s t hs ht hst
      change 0 < u.im at hu
      change 0 < v.im at hv
      change 0 < (s • u + t • v).im
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      rcases eq_or_lt_of_le hs with rfl | hs'
      · have ht1 : t = 1 := by linarith
        rw [ht1]; simp; exact hv
      · nlinarith [hu, hv]
    have hmob_eq : ∀ τ : UpperHalfPlane, ((γ • τ : UpperHalfPlane) : ℂ) = mob (τ : ℂ) := by
      intro τ
      exact sl2Z_coe_smul γ τ
    have hH_deriv : ∀ u ∈ {v : ℂ | 0 < v.im}, HasDerivAt H 0 u := by
      intro u hu
      let τ : UpperHalfPlane := ⟨u, hu⟩
      have hden_ne : c * u + d ≠ 0 := by
        have hden : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) (τ : ℂ) =
            c * u + d := by
          simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL, c, d, τ]
        rw [← hden]
        exact UpperHalfPlane.denom_ne_zero _ τ
      have hmob_im : 0 < (mob u).im := by
        rw [← hmob_eq τ]
        exact (γ • τ).im_pos
      have hmob_deriv : HasDerivAt mob ((c * u + d) ^ 2)⁻¹ u := by
        have hnum : HasDerivAt (fun v => a * v + b) a u := by
          simpa using (hasDerivAt_id u).const_mul a |>.add_const b
        have hden : HasDerivAt (fun v => c * v + d) c u := by
          simpa using (hasDerivAt_id u).const_mul c |>.add_const d
        refine (hnum.div hden hden_ne).congr_deriv ?_
        have hnum_eq : a * (c * u + d) - (a * u + b) * c = 1 := by linear_combination hdet
        rw [hnum_eq, one_div]
      have hcomp := (hasDerivAt_cuspPrimitiveEval f (k - 2) Y hmob_im).comp u hmob_deriv
      have h1 := hcomp.const_mul ((c * X + d) ^ (k - 2))
      have h2 := hasDerivAt_cuspPrimitiveEval f (k - 2) X hu
      refine (h1.sub h2).congr_deriv ?_
      have hf_mob : cuspToComplex f (mob u) = (c * u + d) ^ (k : ℤ) * cuspToComplex f u := by
        rw [← hmob_eq τ, cuspToComplex_eq f (γ • τ), cuspToComplex_eq f τ]
        exact cuspForm_SL2Z_transform f γ τ
      have hY_sub : (c * X + d) * (Y - mob u) = (X - u) / (c * u + d) := by
        dsimp only [Y, mob]
        field_simp [hX, hden_ne]
        linear_combination (X - u) * hdet
      have hpow_comb : (c * X + d) ^ (k - 2) * (Y - mob u) ^ (k - 2) =
          (X - u) ^ (k - 2) / (c * u + d) ^ (k - 2) := by
        rw [← mul_pow, hY_sub, div_pow]
      have hpow_k : (c * u + d) ^ (k : ℤ) = (c * u + d) ^ (k - 2) * (c * u + d) ^ 2 := by
        rw [zpow_natCast, ← pow_add, show (k - 2) + 2 = k by omega]
      rw [hf_mob, hpow_k]
      have hden_pow_ne : (c * u + d) ^ (k - 2) ≠ 0 := pow_ne_zero _ hden_ne
      have hden_sq_ne : (c * u + d) ^ 2 ≠ 0 := pow_ne_zero 2 hden_ne
      calc (c * X + d) ^ (k - 2) *
              (-((c * u + d) ^ (k - 2) * (c * u + d) ^ 2 * cuspToComplex f u *
                (Y - mob u) ^ (k - 2)) * ((c * u + d) ^ 2)⁻¹) -
            -(cuspToComplex f u * (X - u) ^ (k - 2))
          = -(cuspToComplex f u * ((c * u + d) ^ (k - 2) *
              ((c * X + d) ^ (k - 2) * (Y - mob u) ^ (k - 2))) *
              ((c * u + d) ^ 2 * ((c * u + d) ^ 2)⁻¹)) +
            cuspToComplex f u * (X - u) ^ (k - 2) := by ring
        _ = -(cuspToComplex f u * ((c * u + d) ^ (k - 2) *
              ((X - u) ^ (k - 2) / (c * u + d) ^ (k - 2))) * 1) +
            cuspToComplex f u * (X - u) ^ (k - 2) := by
            rw [hpow_comb, mul_inv_cancel₀ hden_sq_ne]
        _ = 0 := by field_simp [hden_pow_ne]; ring
    have hconst : H (z₁ : ℂ) = H (z₂ : ℂ) := by
      refine hU_conv.is_const_of_fderivWithin_eq_zero
        (fun u hu => ((hH_deriv u hu).hasFDerivAt.restrictScalars ℝ).differentiableAt.differentiableWithinAt)
        (fun u hu => by
          rw [fderivWithin_of_isOpen hU_open hu,
            ((hH_deriv u hu).hasFDerivAt.restrictScalars ℝ).fderiv]
          simp)
        z₁.im_pos z₂.im_pos
    have hP1 : P₁.eval X = H (z₁ : ℂ) := by
      dsimp only [P₁, H]
      rw [Polynomial.eval_sub,
        polySlash_eval (cuspPrimitive_natDegree_le f (γ • z₁)) _ hX,
        cuspPrimitive_eval hk f (γ • z₁), cuspPrimitive_eval hk f z₁, hmob_eq z₁]
    have hP2 : P₂.eval X = H (z₂ : ℂ) := by
      dsimp only [P₂, H]
      rw [Polynomial.eval_sub,
        polySlash_eval (cuspPrimitive_natDegree_le f (γ • z₂)) _ hX,
        cuspPrimitive_eval hk f (γ • z₂), cuspPrimitive_eval hk f z₂, hmob_eq z₂]
    rw [hP1, hP2, hconst]
  -- Two polynomials agreeing outside at most one root (`c * X + d = 0`) are equal
  have hdiff_zero : P₁ - P₂ = 0 := by
    by_contra hne
    have hfin : ((P₁ - P₂).roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
    have hcd_ne : ¬(c = 0 ∧ d = 0) := by
      rintro ⟨hc0, hd0⟩
      rw [hc0, hd0] at hdet
      norm_num at hdet
    have hbad_fin : {X : ℂ | c * X + d = 0}.Finite := by
      by_cases hc0 : c = 0
      · have hd0 : d ≠ 0 := fun hd => hcd_ne ⟨hc0, hd⟩
        have : {X : ℂ | c * X + d = 0} = ∅ := by ext X; simp [hc0, hd0]
        rw [this]; exact Set.finite_empty
      · have : {X : ℂ | c * X + d = 0} = {-(d / c)} := by
          ext X
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
          constructor
          · intro h; field_simp [hc0]; linear_combination h
          · intro h; rw [h]; field_simp [hc0]; ring
        rw [this]; exact Set.finite_singleton _
    have hall_fin : ({X : ℂ | c * X + d = 0} ∪ ((P₁ - P₂).roots.toFinset : Set ℂ)).Finite :=
      hbad_fin.union hfin
    obtain ⟨X, hX_not⟩ := (Set.infinite_univ.sdiff hall_fin).nonempty
    have hX_good : c * X + d ≠ 0 := fun h => hX_not.2 (Or.inl h)
    have hX_root : (P₁ - P₂).eval X = 0 := by
      rw [Polynomial.eval_sub, heval_eq X hX_good, sub_self]
    have hmem : X ∈ (P₁ - P₂).roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hX_root)
    exact hX_not.2 (Or.inr hmem)
  exact sub_eq_zero.mp hdiff_zero

/-- **The Concrete Eichler–Shimura 1-Cocycle `cuspCocycle f γ ∈ ℂ[X]`** of a level-1 cusp form
`f ∈ S_k(SL₂(ℤ))`. -/
def cuspCocycle {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Polynomial ℂ :=
  polySlash (k - 2) (γ : Matrix (Fin 2) (Fin 2) ℤ) (cuspPrimitive f (γ • UpperHalfPlane.I)) -
    cuspPrimitive f UpperHalfPlane.I

theorem cuspCocycle_eq {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    cuspCocycle f γ =
      polySlash (k - 2) (γ : Matrix (Fin 2) (Fin 2) ℤ) (cuspPrimitive f (γ • z)) -
        cuspPrimitive f z :=
  cuspPrimitive_cocycle_const hk f γ UpperHalfPlane.I z

theorem cuspCocycle_natDegree_le {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (cuspCocycle f γ).natDegree ≤ k - 2 :=
  (Polynomial.natDegree_sub_le _ _).trans
    (max_le (polySlash_natDegree_le _ _ _) (cuspPrimitive_natDegree_le f _))

/-- **Exact 1-Cocycle Multiplication Identity**:
`cuspCocycle f (γ₁ * γ₂) = (cuspCocycle f γ₁ |_{2 - k} γ₂) + cuspCocycle f γ₂`. -/
theorem cuspCocycle_mul {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    cuspCocycle f (γ₁ * γ₂) =
      polySlash (k - 2) (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) (cuspCocycle f γ₁) + cuspCocycle f γ₂ := by
  rw [cuspCocycle_eq hk f (γ₁ * γ₂) UpperHalfPlane.I,
    cuspCocycle_eq hk f γ₁ (γ₂ • UpperHalfPlane.I),
    cuspCocycle_eq hk f γ₂ UpperHalfPlane.I,
    polySlash_sub,
    polySlash_mul (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)
      (cuspPrimitive_natDegree_le f _),
    ← Matrix.SpecialLinearGroup.coe_mul, mul_smul]
  ring

/-- `cuspCocycle f T = 0` (immediate from `1`-periodicity `f(z + 1) = f(z)`). -/
theorem cuspCocycle_T {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    cuspCocycle f ModularGroup.T = 0 := by
  rw [cuspCocycle_eq hk f ModularGroup.T UpperHalfPlane.I]
  suffices h : polySlash (k - 2) (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ)
      (cuspPrimitive f (ModularGroup.T • UpperHalfPlane.I)) = cuspPrimitive f UpperHalfPlane.I by
    rw [h, sub_self]
  apply Polynomial.funext
  intro X
  have hT_entries : (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 ∧
      (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 1 ∧
      (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧
      (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ModularGroup.T]
  have hden : ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * X +
      ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) ≠ 0 := by
    rw [hT_entries.2.2.1, hT_entries.2.2.2]; simp
  rw [polySlash_eval (cuspPrimitive_natDegree_le f _) _ hden,
    cuspPrimitive_eval hk f, cuspPrimitive_eval hk f]
  rw [hT_entries.1, hT_entries.2.1, hT_entries.2.2.1, hT_entries.2.2.2]
  simp only [Int.cast_zero, Int.cast_one, zero_mul, zero_add, one_pow, one_mul, div_one]
  unfold cuspPrimitiveEval
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hT_pt : ((ModularGroup.T • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      (UpperHalfPlane.I : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]
    simp [add_comm]
  rw [hT_pt]
  have harg : (UpperHalfPlane.I : ℂ) + 1 + Complex.I * (t : ℂ) =
      ((UpperHalfPlane.I : ℂ) + Complex.I * (t : ℂ)) + ((1 : ℤ) : ℂ) := by push_cast; ring
  have hsub : X + 1 - ((UpperHalfPlane.I : ℂ) + 1 + Complex.I * (t : ℂ)) =
      X - ((UpperHalfPlane.I : ℂ) + Complex.I * (t : ℂ)) := by ring
  rw [hsub]
  congr 2
  let τ : UpperHalfPlane := ⟨(UpperHalfPlane.I : ℂ) + Complex.I * (t : ℂ), by simp; linarith⟩
  have h1 : cuspToComplex f ((UpperHalfPlane.I : ℂ) + 1 + Complex.I * (t : ℂ)) =
      f ⟨(τ : ℂ) + ((1 : ℤ) : ℂ), by simp [τ.im_pos]⟩ := by
    rw [harg]
    exact cuspToComplex_eq f ⟨(τ : ℂ) + ((1 : ℤ) : ℂ), by simp [τ.im_pos]⟩
  rw [h1, cuspForm_add_int f τ 1, ← cuspToComplex_eq f τ]

/-- `cuspCocycle f (-1) = 0` for every weight `k ≥ 2` (even `k` from `(-1)^(k-2) = 1`;
odd `k` from `f = 0`). -/
theorem cuspCocycle_neg_one {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    cuspCocycle f (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = 0 := by
  rw [cuspCocycle_eq hk f (-1) UpperHalfPlane.I]
  have hsmul : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [sl2Z_coe_smul]
    simp
  rw [hsmul, show ((-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = -1 from rfl,
    polySlash_neg_one (cuspPrimitive_natDegree_le f _)]
  rcases Nat.even_or_odd k with hev | hodd
  · have hwev : Even (k - 2) := by
      rcases hev with ⟨m, hm⟩
      exact ⟨m - 1, by omega⟩
    rw [hwev.neg_one_pow, one_smul, sub_self]
  · have hoddZ : Odd (k : ℤ) := by
      rcases hodd with ⟨m, rfl⟩; exact ⟨m, by push_cast; ring⟩
    have hf0 : cuspPrimitive f UpperHalfPlane.I = 0 := by
      apply Polynomial.funext; intro X
      rw [cuspPrimitive_eval hk f, Polynomial.eval_zero]
      unfold cuspPrimitiveEval
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      have ht0 : 0 < t := ht
      let τ : UpperHalfPlane := ⟨(UpperHalfPlane.I : ℂ) + Complex.I * (t : ℂ), by simp; linarith⟩
      rw [show cuspToComplex f ((UpperHalfPlane.I : ℂ) + Complex.I * (t : ℂ)) = f τ from
        cuspToComplex_eq f τ, cuspForm_eq_zero_of_odd hoddZ f τ,
        zero_mul, zero_mul]
    rw [hf0, smul_zero, sub_self]

/-- Tail limit of the vertical-ray integral: as `y → ∞`, `cuspPrimitiveEval f w X (x + i y) → 0`
for every fixed `x : ℝ` and `X : ℂ`. -/
private lemma tendsto_cuspPrimitiveEval_atTop {k : ℤ} (f : CuspForm SL2ZRange k)
    (w : ℕ) (X : ℂ) (x : ℝ) :
    Tendsto (fun y : ℝ => cuspPrimitiveEval f w X ((x : ℂ) + Complex.I * (y : ℂ)))
      atTop (nhds 0) := by
  have hint : IntegrableOn (fun u : ℝ => cuspToComplex f ((x : ℂ) + Complex.I * (u : ℂ)) *
      (X - ((x : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) (Set.Ioi (1 : ℝ)) volume := by
    have hbase := integrableOn_cuspPrimitive_integrand f w X (z := (x : ℂ) + Complex.I) (by simp)
    have hsub := integrableOn_Ioi_add_right (a := (1 : ℝ)) (b := (-1 : ℝ))
      (g := fun t : ℝ => cuspToComplex f ((x : ℂ) + Complex.I + Complex.I * (t : ℂ)) *
        (X - ((x : ℂ) + Complex.I + Complex.I * (t : ℂ))) ^ w * Complex.I)
      (by simpa using hbase)
    refine IntegrableOn.congr_fun hsub (fun u _ => ?_) measurableSet_Ioi
    have heq : (x : ℂ) + Complex.I + Complex.I * ((u + -1 : ℝ) : ℂ) =
        (x : ℂ) + Complex.I * (u : ℂ) := by push_cast; ring
    rw [heq]
  have hlim : Tendsto (fun y : ℝ =>
      ∫ u in Set.Ioi y, cuspToComplex f ((x : ℂ) + Complex.I * (u : ℂ)) *
        (X - ((x : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) atTop (nhds 0) := by
    have hsplit : ∀ᶠ y : ℝ in atTop,
        (∫ u in Set.Ioi y, cuspToComplex f ((x : ℂ) + Complex.I * (u : ℂ)) *
          (X - ((x : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) =
        (∫ u in Set.Ioi (1 : ℝ), cuspToComplex f ((x : ℂ) + Complex.I * (u : ℂ)) *
          (X - ((x : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) -
        (∫ u in (1 : ℝ)..y, cuspToComplex f ((x : ℂ) + Complex.I * (u : ℂ)) *
          (X - ((x : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      rw [intervalIntegral.integral_of_le hy]
      have hunion : Set.Ioc (1 : ℝ) y ∪ Set.Ioi y = Set.Ioi (1 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hy
      have hdisj : Disjoint (Set.Ioc (1 : ℝ) y) (Set.Ioi y) := Set.Ioc_disjoint_Ioi_same
      have h1 : IntegrableOn _ (Set.Ioc 1 y) volume := hint.mono_set Set.Ioc_subset_Ioi_self
      have h2 := hint.mono_set (Set.Ioi_subset_Ioi hy)
      have hadd := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi h1 h2
      rw [hunion] at hadd
      linear_combination -hadd
    have hfull := intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id
    have hsub := (tendsto_const_nhds (x := ∫ u in Set.Ioi (1 : ℝ),
      cuspToComplex f ((x : ℂ) + Complex.I * (u : ℂ)) *
        (X - ((x : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I)).sub hfull
    rw [sub_self] at hsub
    exact hsub.congr' (hsplit.mono fun y hy => hy.symm)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y _
  unfold cuspPrimitiveEval
  have htr := integral_Ioi_add_right
    (fun u : ℝ => cuspToComplex f ((x : ℂ) + Complex.I * (u : ℂ)) *
      (X - ((x : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) 0 y
  rw [zero_add] at htr
  rw [← htr]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have heq : (x : ℂ) + Complex.I * ((t + y : ℝ) : ℂ) =
      (x : ℂ) + Complex.I * (y : ℂ) + Complex.I * (t : ℂ) := by push_cast; ring
  rw [heq]

/-- Lower-endpoint limit of the vertical-ray integral at any rational cusp `r : ℚ`:
as `ε → 0⁺`, `cuspPrimitiveEval f w X (r + i ε) → ∫_{u > 0} f(r + i u) (X - (r + i u))^w i du`. -/
private lemma integrableOn_cuspRay_poly {k : ℤ} (f : CuspForm SL2ZRange k)
    (w : ℕ) (X : ℂ) (r : ℚ) :
    IntegrableOn (fun u : ℝ => cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
      (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) (Set.Ioi (0 : ℝ)) volume := by
  let δ : ℝ := ((r.den : ℝ) ^ 2)⁻¹
  have hδ : 0 < δ := by positivity
  have hunion : Set.Ioc (0 : ℝ) δ ∪ Set.Ioi δ = Set.Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hδ.le
  rw [← hunion]
  refine IntegrableOn.union ?_ ?_
  · -- Integrable on `(0, δ]` by super-exponential cusp decay
    obtain ⟨C, hC_pos, hC⟩ := cuspForm_exp_decay_atCusp f r
    have hmeas : AEStronglyMeasurable (fun u : ℝ => cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
        (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) (volume.restrict (Set.Ioc 0 δ)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      have hline : ContinuousOn (fun u : ℝ => (r : ℂ) + Complex.I * (u : ℂ)) (Set.Ioc 0 δ) :=
        (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
      have hmaps : Set.MapsTo (fun u : ℝ => (r : ℂ) + Complex.I * (u : ℂ)) (Set.Ioc 0 δ)
          {v : ℂ | 0 < v.im} := by
        intro u hu; change 0 < ((r : ℂ) + Complex.I * (u : ℂ)).im; simp [hu.1]
      exact (((differentiableOn_cuspToComplex f).continuousOn.comp hline hmaps).mul
        ((continuousOn_const.sub hline).pow w)).mul continuousOn_const
    -- On `(0, δ]`, `((c u)^(-k)) * exp(-2π / (c² u))` is bounded by a constant!
    let m : ℕ := k.toNat
    have hm_ge : k ≤ (m : ℤ) := Int.self_le_toNat k
    have hpow_lim : Tendsto (fun v : ℝ => v ^ m * Real.exp (-v)) atTop (nhds 0) := by
      simpa [Real.exp_neg, div_eq_mul_inv] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m
    have hbound_v : ∃ B > 0, ∀ v : ℝ, 0 ≤ v → v ^ m * Real.exp (-v) ≤ B := by
      obtain ⟨M, hM⟩ := (Filter.eventually_atTop.mp
        (hpow_lim.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)))
      let M' : ℝ := max M 0
      have hcont : ContinuousOn (fun v : ℝ => v ^ m * Real.exp (-v)) (Set.Icc 0 M') :=
        ((continuous_pow m).mul (Real.continuous_exp.comp continuous_neg)).continuousOn
      obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      refine ⟨max B₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun v hv => ?_⟩
      by_cases hvM : v ≤ M'
      · have h1 := hB₀ v ⟨hv, hvM⟩
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hv m) (Real.exp_pos _).le)] at h1
        exact h1.trans (le_max_left _ _)
      · have h1 := hM v (le_trans (le_max_left M 0) (le_of_not_ge hvM))
        rw [dist_zero_right,
          Real.norm_of_nonneg (mul_nonneg (pow_nonneg hv m) (Real.exp_pos _).le)] at h1
        exact h1.le.trans (le_max_right _ _)
    obtain ⟨B, hB_pos, hB⟩ := hbound_v
    set c : ℝ := (r.den : ℝ) with hc_def
    have hc_pos : 0 < c := Nat.cast_pos.mpr r.pos
    have hc_ge1 : (1 : ℝ) ≤ c := by
      rw [hc_def]
      exact_mod_cast Nat.succ_le_of_lt r.pos
    let Mconst : ℝ := C * B * (c / (2 * Real.pi)) ^ m * (δ + ‖X - (r : ℂ)‖) ^ w
    refine (integrableOn_const (C := Mconst) (hs := measure_Ioc_lt_top.ne)).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    have huδ : u ≤ δ := hu.2
    have hcu_le1 : c * u ≤ 1 := by
      have h1 : c * u ≤ c * δ := mul_le_mul_of_nonneg_left huδ hc_pos.le
      have h2 : c * δ = c⁻¹ := by dsimp only [δ]; rw [← hc_def]; field_simp [hc_pos.ne']
      have h3 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc_ge1
      linarith
    have hcu_pos : 0 < c * u := mul_pos hc_pos hu0
    have hpow_le : (c * u) ^ (-k) ≤ (c * u) ^ (-(m : ℤ)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_intCast]
      exact Real.rpow_le_rpow_of_exponent_ge hcu_pos hcu_le1 (by exact_mod_cast neg_le_neg hm_ge)
    have htau_bd : ‖cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ))‖ ≤
        C * B * (c / (2 * Real.pi)) ^ m := by
      let τ : UpperHalfPlane := ⟨(r : ℂ) + Complex.I * (u : ℂ), by simp [hu0]⟩
      rw [show cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) = f τ from cuspToComplex_eq f τ]
      have h1 := hC u hu0 huδ
      set v : ℝ := 2 * Real.pi / (c ^ 2 * u)
      have hv_pos : 0 < v := by positivity
      have hcu_eq : (c * u) ^ (-(m : ℤ)) = (c / (2 * Real.pi)) ^ m * v ^ m := by
        rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
        congr 1
        dsimp only [v]
        field_simp [hc_pos.ne', hu0.ne', Real.pi_pos.ne']
      have hexp_eq : -2 * Real.pi / (c ^ 2 * u) = -v := by dsimp only [v]; ring
      calc ‖f τ‖
          ≤ C * (c * u) ^ (-k) * Real.exp (-2 * Real.pi / (c ^ 2 * u)) := h1
        _ ≤ C * (c * u) ^ (-(m : ℤ)) * Real.exp (-v) := by
            rw [hexp_eq]
            gcongr
        _ = C * (c / (2 * Real.pi)) ^ m * (v ^ m * Real.exp (-v)) := by rw [hcu_eq]; ring
        _ ≤ C * (c / (2 * Real.pi)) ^ m * B :=
            mul_le_mul_of_nonneg_left (hB v hv_pos.le) (by positivity)
        _ = C * B * (c / (2 * Real.pi)) ^ m := by ring
    have hpoly_bd : ‖(X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w‖ ≤ (δ + ‖X - (r : ℂ)‖) ^ w := by
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ w
      rw [show X - ((r : ℂ) + Complex.I * (u : ℂ)) = (X - (r : ℂ)) - Complex.I * (u : ℂ) by ring]
      calc ‖(X - (r : ℂ)) - Complex.I * (u : ℂ)‖
          ≤ ‖X - (r : ℂ)‖ + ‖Complex.I * (u : ℂ)‖ := norm_sub_le _ _
        _ = ‖X - (r : ℂ)‖ + u := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hu0.le]
        _ ≤ δ + ‖X - (r : ℂ)‖ := by linarith
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
    exact mul_le_mul htau_bd hpoly_bd (norm_nonneg _) (by positivity)
  · -- Integrable on `(δ, ∞)` by translating from `(0, ∞)`
    have hbase := integrableOn_cuspPrimitive_integrand f w X (z := (r : ℂ) + Complex.I * (δ : ℂ))
      (by simp [hδ])
    have hsub := integrableOn_Ioi_add_right (a := δ) (b := -δ)
      (g := fun t : ℝ => cuspToComplex f ((r : ℂ) + Complex.I * (δ : ℂ) + Complex.I * (t : ℂ)) *
        (X - ((r : ℂ) + Complex.I * (δ : ℂ) + Complex.I * (t : ℂ))) ^ w * Complex.I)
      (by simpa using hbase)
    refine IntegrableOn.congr_fun hsub (fun u _ => ?_) measurableSet_Ioi
    have heq : (r : ℂ) + Complex.I * (δ : ℂ) + Complex.I * ((u + -δ : ℝ) : ℂ) =
        (r : ℂ) + Complex.I * (u : ℂ) := by push_cast; ring
    rw [heq]

private lemma tendsto_cuspPrimitiveEval_atCusp {k : ℤ} (f : CuspForm SL2ZRange k)
    (w : ℕ) (X : ℂ) (r : ℚ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : ℝ => cuspPrimitiveEval f w X ((r : ℂ) + Complex.I * (((a * y)⁻¹ : ℝ) : ℂ)))
      atTop (nhds (∫ u in Set.Ioi (0 : ℝ), cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
        (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I)) := by
  have hint := integrableOn_cuspRay_poly f w X r
  have hshift : ∀ᶠ y : ℝ in atTop,
      cuspPrimitiveEval f w X ((r : ℂ) + Complex.I * (((a * y)⁻¹ : ℝ) : ℂ)) =
        ∫ u in Set.Ioi (0 : ℝ),
          (Set.Ioi ((a * y)⁻¹)).indicator
            (fun u : ℝ => cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
              (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    unfold cuspPrimitiveEval
    have hpos : 0 < (a * y)⁻¹ := inv_pos.mpr (mul_pos ha hy)
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hpos.le)]
    have htr := integral_Ioi_add_right
      (fun u : ℝ => cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
        (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) 0 (a * y)⁻¹
    rw [zero_add] at htr
    rw [← htr]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have heq : (r : ℂ) + Complex.I * (((t + (a * y)⁻¹ : ℝ) : ℂ)) =
        (r : ℂ) + Complex.I * (((a * y)⁻¹ : ℝ) : ℂ) + Complex.I * (t : ℂ) := by push_cast; ring
    rw [heq]
  have hdom : Tendsto (fun y : ℝ =>
      ∫ u in Set.Ioi (0 : ℝ),
        (Set.Ioi ((a * y)⁻¹)).indicator
          (fun u : ℝ => cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
            (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I) u)
      atTop (nhds (∫ u in Set.Ioi (0 : ℝ), cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
        (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun u => ‖cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
        (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I‖) ?_ ?_ hint.norm ?_
    · exact Eventually.of_forall fun y => hint.aestronglyMeasurable.indicator measurableSet_Ioi
    · refine Eventually.of_forall fun y => ?_
      filter_upwards with u
      by_cases hu : u ∈ Set.Ioi (a * y)⁻¹
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, norm_zero]; exact norm_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop ((a * u)⁻¹)] with y hy
      have hy0 : 0 < y := lt_trans (inv_pos.mpr (mul_pos ha hu0)) hy
      have hlt : u ∈ Set.Ioi ((a * y)⁻¹) := by
        change (a * y)⁻¹ < u
        rw [inv_lt_comm₀ (mul_pos ha hy0) hu0]
        have h1 : a * (a * u)⁻¹ < a * y := mul_lt_mul_of_pos_left hy ha
        have h2 : a * (a * u)⁻¹ = u⁻¹ := by field_simp [ha.ne', hu0.ne']
        linarith
      exact (Set.indicator_of_mem hlt
        (fun u : ℝ => cuspToComplex f ((r : ℂ) + Complex.I * (u : ℂ)) *
          (X - ((r : ℂ) + Complex.I * (u : ℂ))) ^ w * Complex.I)).symm
  exact hdom.congr' (hshift.mono fun y hy => hy.symm)

/-- **Exact Evaluation of the `S`-Cocycle**:
`cuspCocycle f ModularGroup.S = polySlash (k - 2) matS (periodPoly f)` (and `= -periodPoly f`). -/
theorem cuspCocycle_S {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    cuspCocycle f ModularGroup.S = polySlash (k - 2) matS (periodPoly f) := by
  have hS_entries : matS 0 0 = 0 ∧ matS 0 1 = -1 ∧ matS 1 0 = 1 ∧ matS 1 1 = 0 := by
    rw [matS_eq]; decide
  let P₁ : Polynomial ℂ := cuspCocycle f ModularGroup.S
  let P₂ : Polynomial ℂ := polySlash (k - 2) matS (periodPoly f)
  have heval_eq : ∀ X : ℂ, X ≠ 0 → P₁.eval X = P₂.eval X := by
    intro X hX
    have hden : (matS 1 0 : ℂ) * X + (matS 1 1 : ℂ) ≠ 0 := by
      rw [hS_entries.2.2.1, hS_entries.2.2.2]; simpa
    have hev : ∀ᶠ y : ℝ in atTop,
        P₁.eval X = X ^ (k - 2) *
          cuspPrimitiveEval f (k - 2) (-(1 : ℂ) / X) (Complex.I * ((y⁻¹ : ℝ) : ℂ)) -
          cuspPrimitiveEval f (k - 2) X (Complex.I * (y : ℂ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hyinv : 0 < y⁻¹ := inv_pos.mpr hy
      have hS_pt : ModularGroup.S • imagPt y hy = imagPt y⁻¹ hyinv := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.modular_S_smul]
        change (-(Complex.I * (y : ℂ)))⁻¹ = Complex.I * ((y⁻¹ : ℝ) : ℂ)
        rw [inv_neg, mul_inv, Complex.inv_I, Complex.ofReal_inv]
        ring
      have hcoc := congrArg (Polynomial.eval X) (cuspCocycle_eq hk f ModularGroup.S (imagPt y hy))
      dsimp only [P₁]
      rw [hcoc, Polynomial.eval_sub, hS_pt]
      change (polySlash (k - 2) matS (cuspPrimitive f (imagPt y⁻¹ hyinv))).eval X -
          (cuspPrimitive f (imagPt y hy)).eval X = _
      rw [polySlash_eval (cuspPrimitive_natDegree_le f _) matS hden,
        cuspPrimitive_eval hk f, cuspPrimitive_eval hk f]
      rw [hS_entries.1, hS_entries.2.1, hS_entries.2.2.1, hS_entries.2.2.2]
      simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, zero_add, one_mul, add_zero,
        coe_imagPt]
    have hlim1 : Tendsto (fun y : ℝ =>
        X ^ (k - 2) * cuspPrimitiveEval f (k - 2) (-(1 : ℂ) / X) (Complex.I * ((y⁻¹ : ℝ) : ℂ)))
        atTop (nhds (P₂.eval X)) := by
      have htend := tendsto_cuspPrimitiveEval_atCusp f (k - 2) (-(1 : ℂ) / X) 0 zero_lt_one
      have hmul := htend.const_mul (X ^ (k - 2))
      have hP2_eq : P₂.eval X = X ^ (k - 2) *
          ∫ u in Set.Ioi (0 : ℝ), cuspToComplex f (((0 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
            (-(1 : ℂ) / X - (((0 : ℚ) : ℂ) + Complex.I * (u : ℂ))) ^ (k - 2) * Complex.I := by
        dsimp only [P₂]
        rw [polySlash_eval (periodPoly_natDegree_le f) _ hden, periodPoly_eval hk f]
        rw [hS_entries.1, hS_entries.2.1, hS_entries.2.2.1, hS_entries.2.2.2]
        simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, zero_add, one_mul, add_zero,
          Rat.cast_zero]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        rw [cuspImag_eq_ofComplex f hu]
        rfl
      rw [hP2_eq]
      refine hmul.congr fun y => ?_
      simp [one_mul]
    have hlim2 : Tendsto (fun y : ℝ => cuspPrimitiveEval f (k - 2) X (Complex.I * (y : ℂ)))
        atTop (nhds 0) := by
      have htend := tendsto_cuspPrimitiveEval_atTop f (k - 2) X 0
      simpa using htend
    have hsub := hlim1.sub hlim2
    rw [sub_zero] at hsub
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hsub
  -- Two polynomials agreeing for all `X ≠ 0` are equal
  have hdiff_zero : P₁ - P₂ = 0 := by
    by_contra hne
    have hfin : ({(0 : ℂ)} ∪ ((P₁ - P₂).roots.toFinset : Set ℂ)).Finite :=
      (Set.finite_singleton 0).union (Finset.finite_toSet _)
    obtain ⟨X, hX_not⟩ := (Set.infinite_univ.sdiff hfin).nonempty
    have hX0 : X ≠ 0 := fun h => hX_not.2 (Or.inl (Set.mem_singleton_iff.mpr h))
    have hroot : (P₁ - P₂).eval X = 0 := by
      rw [Polynomial.eval_sub, heval_eq X hX0, sub_self]
    exact hX_not.2 (Or.inr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hroot)))
  exact sub_eq_zero.mp hdiff_zero

theorem cuspCocycle_S_eq_neg_periodPoly {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    cuspCocycle f ModularGroup.S = -periodPoly f := by
  rw [cuspCocycle_S hk f]
  have h := periodPoly_S_relation hk f
  exact eq_neg_of_add_eq_zero_right h

/-- **UNCONDITIONAL 3-TERM `U = S T`-RELATION FOR EVERY LEVEL-1 CUSP FORM (Eichler–Shimura–Manin)**:
for EVERY `k ≥ 2` and EVERY `f ∈ S_k(SL₂(ℤ))`,
`periodPoly f + (periodPoly f |_{2 - k} U) + (periodPoly f |_{2 - k} U^2) = 0`. -/
theorem periodPoly_U_relation {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    periodPoly f + polySlash (k - 2) matU (periodPoly f) +
      polySlash (k - 2) (matU ^ 2) (periodPoly f) = 0 := by
  let U : Matrix.SpecialLinearGroup (Fin 2) ℤ := ModularGroup.S * ModularGroup.T
  have hU_coe : (U : Matrix (Fin 2) (Fin 2) ℤ) = matU := rfl
  have hU3 : U ^ 3 = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    apply Subtype.ext
    change ((U ^ 3 : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = -1
    rw [Matrix.SpecialLinearGroup.coe_pow, hU_coe, pow_succ, matU_sq_eq, matU_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hcU : cuspCocycle f U = polySlash (k - 2) matU (periodPoly f) := by
    dsimp only [U]
    rw [cuspCocycle_mul hk f ModularGroup.S ModularGroup.T, cuspCocycle_T hk f, add_zero,
      cuspCocycle_S hk f, polySlash_mul matS _ (periodPoly_natDegree_le f)]
    rfl
  have hcU3 : cuspCocycle f (U ^ 3) =
      polySlash (k - 2) (matU ^ 2) (cuspCocycle f U) +
        polySlash (k - 2) matU (cuspCocycle f U) + cuspCocycle f U := by
    rw [show U ^ 3 = (U * U) * U by rw [pow_succ, pow_two], cuspCocycle_mul hk f (U * U) U,
      cuspCocycle_mul hk f U U, polySlash_add,
      polySlash_mul (U : Matrix (Fin 2) (Fin 2) ℤ) (U : Matrix (Fin 2) (Fin 2) ℤ)
        (cuspCocycle_natDegree_le f U), hU_coe, ← sq]
  rw [hU3, cuspCocycle_neg_one hk f, hcU,
    polySlash_mul matU (matU ^ 2) (periodPoly_natDegree_le f),
    polySlash_mul matU matU (periodPoly_natDegree_le f), ← sq] at hcU3
  have hmatU3 : matU * matU ^ 2 = (-1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [matU_sq_eq, matU_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmatU3, polySlash_neg_one (periodPoly_natDegree_le f)] at hcU3
  rcases Nat.even_or_odd k with hev | hodd
  · have hwev : Even (k - 2) := by
      rcases hev with ⟨m, hm⟩
      exact ⟨m - 1, by omega⟩
    rw [hwev.neg_one_pow, one_smul] at hcU3
    linear_combination -hcU3
  · have hoddZ : Odd (k : ℤ) := by
      rcases hodd with ⟨m, rfl⟩; exact ⟨m, by push_cast; ring⟩
    have hP0 : periodPoly f = 0 := by
      apply Polynomial.funext; intro X
      rw [periodPoly_eval hk f, Polynomial.eval_zero]
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      rw [cuspImag_of_pos f ht, cuspForm_eq_zero_of_odd hoddZ f _,
        zero_mul, zero_mul]
    rw [hP0, polySlash_zero, polySlash_zero, add_zero, add_zero]

/-! ### Exact Heilbronn Action of the Hecke Operator `T_2` on `periodPoly f` -/

/-- Auxiliary period polynomial along the vertical ray from `1/2` to `i∞`:
`halfPeriodPoly f = ∫_{1/2}^{i∞} f(τ) (X - τ)^{k - 2} dτ`. -/
private def halfPeriodPoly {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k - 1),
    Polynomial.C ((-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) *
      ∫ u in Set.Ioi (0 : ℝ),
        cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
          (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) ^ j * Complex.I) *
      Polynomial.X ^ (k - 2 - j)

private lemma halfPeriodPoly_natDegree_le {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) :
    (halfPeriodPoly f).natDegree ≤ k - 2 := by
  unfold halfPeriodPoly
  refine natDegree_finsetSum_le _ _ (k - 2) fun j _ => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  omega

private lemma halfPeriodPoly_eval {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) (X : ℂ) :
    (halfPeriodPoly f).eval X =
      ∫ u in Set.Ioi (0 : ℝ),
        cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
          (X - (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ))) ^ (k - 2) * Complex.I := by
  unfold halfPeriodPoly
  rw [Polynomial.eval_finsetSum]
  have hterm : ∀ j ∈ Finset.range (k - 1),
      (Polynomial.C ((-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) *
        ∫ u in Set.Ioi (0 : ℝ),
          cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
            (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) ^ j * Complex.I) *
        Polynomial.X ^ (k - 2 - j)).eval X =
      ∫ u in Set.Ioi (0 : ℝ),
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) *
          (cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
            (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) ^ j * Complex.I) := by
    intro j _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => by ring
  rw [Finset.sum_congr rfl hterm]
  have hint : ∀ j ∈ Finset.range (k - 1),
      IntegrableOn (fun u : ℝ =>
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) *
          (cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
            (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) ^ j * Complex.I)) (Set.Ioi 0) volume := by
    intro j _
    refine Integrable.const_mul ?_ _
    have hbase := integrableOn_cuspRay_poly f j 0 (1 / 2 : ℚ)
    refine IntegrableOn.congr_fun (hbase.const_mul ((-1 : ℂ) ^ j)) (fun u _ => ?_) measurableSet_Ioi
    rw [zero_sub, neg_pow (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ))]
    have hsq : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by rw [← mul_pow]; norm_num
    calc (-1 : ℂ) ^ j * (cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
            ((-1 : ℂ) ^ j * (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) ^ j) * Complex.I)
        = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) *
            (cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
              (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) ^ j * Complex.I) := by ring
      _ = cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
            (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) ^ j * Complex.I := by rw [hsq, one_mul]
  rw [← MeasureTheory.integral_finsetSum _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have hbinom : (X - (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ))) ^ (k - 2) =
      ∑ j ∈ Finset.range (k - 1),
        (-1 : ℂ) ^ j * ((k - 2).choose j : ℂ) * X ^ (k - 2 - j) *
          (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) ^ j := by
    have hr : k - 1 = (k - 2) + 1 := by omega
    rw [hr, sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  rw [hbinom, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Exact expression of the half-cusp period polynomial `∫_{1/2}^{i∞}` in terms of `periodPoly f`:
`halfPeriodPoly f = periodPoly f - polySlash (k - 2) !![1, 0; -2, 1] (periodPoly f)`. -/
private lemma halfPeriodPoly_eq {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    halfPeriodPoly f =
      periodPoly f - polySlash (k - 2) !![1, 0; -2, 1] (periodPoly f) := by
  let γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, 0; 2, 1], by decide⟩
  have hTinv_coe : ((ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.adjugate_fin_two]
  have hγ₂_fact : γ₂ = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) *
      ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.T⁻¹) * ModularGroup.S := by
    apply Subtype.ext
    change (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) = _
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, hTinv_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γ₂, ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
  have hcTinv : cuspCocycle f ModularGroup.T⁻¹ = 0 := by
    have h1 : cuspCocycle f (ModularGroup.T * ModularGroup.T⁻¹) = 0 := by
      rw [mul_inv_cancel, cuspCocycle_eq hk f 1 UpperHalfPlane.I, one_smul]
      change polySlash (k - 2) (1 : Matrix (Fin 2) (Fin 2) ℤ) (cuspPrimitive f UpperHalfPlane.I) -
        cuspPrimitive f UpperHalfPlane.I = 0
      rw [polySlash_one (cuspPrimitive_natDegree_le f _), sub_self]
    rw [cuspCocycle_mul hk f ModularGroup.T ModularGroup.T⁻¹, cuspCocycle_T hk f,
      polySlash_zero, zero_add] at h1
    exact h1
  have hcγ₂ : cuspCocycle f γ₂ =
      -polySlash (k - 2) ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹ * ModularGroup.S :
          Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) (periodPoly f) -
        periodPoly f := by
    rw [hγ₂_fact, cuspCocycle_mul hk f _ ModularGroup.S,
      cuspCocycle_mul hk f _ (ModularGroup.T⁻¹ * ModularGroup.T⁻¹),
      cuspCocycle_mul hk f (-1) ModularGroup.S,
      cuspCocycle_mul hk f ModularGroup.T⁻¹ ModularGroup.T⁻¹,
      cuspCocycle_neg_one hk f, hcTinv, polySlash_zero, polySlash_zero, zero_add, add_zero,
      add_zero, cuspCocycle_S_eq_neg_periodPoly hk f, polySlash_neg, polySlash_neg,
      polySlash_mul _ _ (periodPoly_natDegree_le f)]
    simp only [Matrix.SpecialLinearGroup.coe_mul, sub_eq_add_neg]
  -- Evaluate `cuspCocycle f γ₂` at `z = -1/2 + i y` as `y → ∞` to get `polySlash (k - 2) γ₂ (halfPeriodPoly f)`
  have hlim_eq : cuspCocycle f γ₂ =
      polySlash (k - 2) (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) (halfPeriodPoly f) := by
    let P₁ : Polynomial ℂ := cuspCocycle f γ₂
    let P₂ : Polynomial ℂ := polySlash (k - 2) (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) (halfPeriodPoly f)
    have hγ₂_entries : (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 ∧
        (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 ∧
        (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 2 ∧
        (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
      refine ⟨rfl, rfl, rfl, rfl⟩
    have heval_eq : ∀ X : ℂ, 2 * X + 1 ≠ 0 → P₁.eval X = P₂.eval X := by
      intro X hX
      have hden : ((γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * X +
          ((γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) ≠ 0 := by
        rw [hγ₂_entries.2.2.1, hγ₂_entries.2.2.2]; simpa
      have hev : ∀ᶠ y : ℝ in atTop,
          P₁.eval X = (2 * X + 1) ^ (k - 2) *
            cuspPrimitiveEval f (k - 2) (X / (2 * X + 1))
              (((1 / 2 : ℚ) : ℂ) + Complex.I * (((4 * y)⁻¹ : ℝ) : ℂ)) -
            cuspPrimitiveEval f (k - 2) X (((-1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
        let z : UpperHalfPlane := ⟨((-1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ), by simp [hy]⟩
        let w : UpperHalfPlane :=
          ⟨(((1 / 2 : ℚ) : ℂ) + Complex.I * (((4 * y)⁻¹ : ℝ) : ℂ)), by simp [hy]⟩
        have hγz : γ₂ • z = w := by
          apply UpperHalfPlane.ext
          rw [sl2Z_coe_smul]
          rw [hγ₂_entries.1, hγ₂_entries.2.1, hγ₂_entries.2.2.1, hγ₂_entries.2.2.2]
          simp only [Int.cast_one, Int.cast_zero, Int.cast_ofNat, one_mul, add_zero, z, w]
          push_cast
          have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
          have hden_simp : 2 * (-1 / 2 + Complex.I * (y : ℂ)) + 1 = 2 * Complex.I * (y : ℂ) := by ring
          rw [hden_simp]
          field_simp [hyC, Complex.I_ne_zero]
          linear_combination -4 * Complex.I_mul_I
        have hcoc := congrArg (Polynomial.eval X) (cuspCocycle_eq hk f γ₂ z)
        dsimp only [P₁]
        rw [hcoc, Polynomial.eval_sub, hγz,
          polySlash_eval (cuspPrimitive_natDegree_le f w) _ hden,
          cuspPrimitive_eval hk f w, cuspPrimitive_eval hk f z]
        rw [hγ₂_entries.1, hγ₂_entries.2.1, hγ₂_entries.2.2.1, hγ₂_entries.2.2.2]
        simp only [Int.cast_zero, Int.cast_one, Int.cast_ofNat, one_mul, add_zero, z, w]
      have hlim1 : Tendsto (fun y : ℝ => (2 * X + 1) ^ (k - 2) *
          cuspPrimitiveEval f (k - 2) (X / (2 * X + 1))
            (((1 / 2 : ℚ) : ℂ) + Complex.I * (((4 * y)⁻¹ : ℝ) : ℂ))) atTop (nhds (P₂.eval X)) := by
        have htend := tendsto_cuspPrimitiveEval_atCusp f (k - 2) (X / (2 * X + 1)) (1 / 2 : ℚ)
          (by norm_num : (0 : ℝ) < 4)
        have hmul := htend.const_mul ((2 * X + 1) ^ (k - 2))
        have hP2_eq : P₂.eval X = (2 * X + 1) ^ (k - 2) *
            ∫ u in Set.Ioi (0 : ℝ),
              cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
                (X / (2 * X + 1) - (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ))) ^ (k - 2) *
                Complex.I := by
          dsimp only [P₂]
          rw [polySlash_eval (halfPeriodPoly_natDegree_le f) _ hden, halfPeriodPoly_eval hk f]
          rw [hγ₂_entries.1, hγ₂_entries.2.1, hγ₂_entries.2.2.1, hγ₂_entries.2.2.2]
          simp only [Int.cast_zero, Int.cast_one, Int.cast_ofNat, one_mul, add_zero]
        rw [hP2_eq]
        exact hmul
      have hlim2 : Tendsto (fun y : ℝ =>
          cuspPrimitiveEval f (k - 2) X (((-1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          atTop (nhds 0) :=
        tendsto_cuspPrimitiveEval_atTop f (k - 2) X (-1 / 2)
      have hsub := hlim1.sub hlim2
      rw [sub_zero] at hsub
      exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hsub
    have hdiff_zero : P₁ - P₂ = 0 := by
      by_contra hne
      have hfin : ({(-(1 / 2 : ℂ))} ∪ ((P₁ - P₂).roots.toFinset : Set ℂ)).Finite :=
        (Set.finite_singleton _).union (Finset.finite_toSet _)
      obtain ⟨X, hX_not⟩ := (Set.infinite_univ.sdiff hfin).nonempty
      have hX_good : 2 * X + 1 ≠ 0 := by
        intro h
        apply hX_not.2
        left
        rw [Set.mem_singleton_iff]
        linear_combination (1 / 2 : ℂ) * h
      have hroot : (P₁ - P₂).eval X = 0 := by
        rw [Polynomial.eval_sub, heval_eq X hX_good, sub_self]
      exact hX_not.2 (Or.inr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hroot)))
    exact sub_eq_zero.mp hdiff_zero
  -- Apply `polySlash (k - 2) !![1, 0; -2, 1]` (= γ₂⁻¹) to both sides
  have hprod1 : (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; -2, 1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [γ₂, Matrix.mul_apply, Fin.sum_univ_two]
  have hprod2 : ((ModularGroup.T⁻¹ * ModularGroup.T⁻¹ * ModularGroup.S :
      Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; -2, 1] = matS := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, hTinv_coe]
    rw [matS_eq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
  have happ := congrArg (polySlash (k - 2) !![1, 0; -2, 1]) hlim_eq
  rw [polySlash_mul _ _ (halfPeriodPoly_natDegree_le f), hprod1,
    polySlash_one (halfPeriodPoly_natDegree_le f), hcγ₂, polySlash_sub, polySlash_neg,
    polySlash_mul _ _ (periodPoly_natDegree_le f), hprod2] at happ
  have hS := periodPoly_S_relation hk f
  have hnegS : -polySlash (k - 2) matS (periodPoly f) = periodPoly f := by
    linear_combination -hS
  rw [hnegS] at happ
  exact happ.symm

/-- **EXACT HEILBRONN ACTION OF THE HECKE OPERATOR `T_2` ON `periodPoly f` (Manin 1973 / Zagier 1991)**:
for EVERY `k ≥ 2` and EVERY `f ∈ S_k(SL₂(ℤ))`,
`periodPoly (T_2 f) = periodPoly f |_{2 - k} ([[2, 0], [0, 1]] + [[1, 0], [0, 2]] + [[1, 1], [0, 2]] + [[2, 0], [1, 1]])`. -/
theorem periodPoly_heckeTwo {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    periodPoly (heckeCuspForm k (by omega) 2 (by norm_num) f) =
      polySlash (k - 2) !![2, 0; 0, 1] (periodPoly f) +
        polySlash (k - 2) !![1, 0; 0, 2] (periodPoly f) +
        polySlash (k - 2) !![1, 1; 0, 2] (periodPoly f) +
        polySlash (k - 2) !![2, 0; 1, 1] (periodPoly f) := by
  -- Step 1: Express `periodPoly (T_2 f)` in terms of `periodPoly f` and `halfPeriodPoly f`
  have hstep1 : periodPoly (heckeCuspForm k (by omega) 2 (by norm_num) f) =
      polySlash (k - 2) !![2, 0; 0, 1] (periodPoly f) +
        polySlash (k - 2) !![1, 0; 0, 2] (periodPoly f) +
        polySlash (k - 2) !![1, 1; 0, 2] (halfPeriodPoly f) := by
    apply Polynomial.funext
    intro X
    rw [periodPoly_eval hk, Polynomial.eval_add, Polynomial.eval_add,
      polySlash_eval (periodPoly_natDegree_le f) !![2, 0; 0, 1] (by norm_num),
      polySlash_eval (periodPoly_natDegree_le f) !![1, 0; 0, 2] (by norm_num),
      polySlash_eval (halfPeriodPoly_natDegree_le f) !![1, 1; 0, 2] (by norm_num),
      periodPoly_eval hk f, periodPoly_eval hk f, halfPeriodPoly_eval hk f]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_zero,
      Int.cast_one, Int.cast_ofNat, zero_mul, zero_add, add_zero, one_pow, one_mul, div_one]
    -- Expand `(T_2 f)(i t)` into its 3 coset terms
    have hT2_apply : ∀ t : ℝ, 0 < t →
        cuspImag (heckeCuspForm k (by omega) 2 (by norm_num) f) t =
          (1 / 2 : ℂ) * cuspImag f (t / 2) +
          (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) +
          (2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) := by
      intro t ht
      rw [cuspImag_of_pos _ ht]
      change slashHeckeOp k (1 : DirichletCharacter ℂ 1) 2 (f : UpperHalfPlane → ℂ) (imagPt t ht) = _
      unfold slashHeckeOp
      have hdiv2 : Nat.divisors 2 = {1, 2} := by decide
      rw [hdiv2, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
      simp only [trivialChar_one_apply, one_mul, show (2 : ℕ) / 1 = 2 by decide,
        show (2 : ℕ) / 2 = 1 by decide, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.zero_lt_one, zero_lt_two, and_self, ↓reduceDIte]
      rw [heckeMat_slash_apply (by omega) 1 0 2 zero_lt_one zero_lt_two,
        heckeMat_slash_apply (by omega) 1 1 2 zero_lt_one zero_lt_two,
        heckeMat_slash_apply (by omega) 2 0 1 zero_lt_two zero_lt_one]
      have hp1 : heckeMat 1 0 2 zero_lt_one zero_lt_two • imagPt t ht = imagPt (t / 2) (half_pos ht) := by
        apply UpperHalfPlane.ext
        rw [heckeMat_smul_coe]
        simp only [coe_imagPt, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, one_mul, add_zero,
          Complex.ofReal_div, Complex.ofReal_ofNat]
        ring
      have hp2 : ((heckeMat 1 1 2 zero_lt_one zero_lt_two • imagPt t ht : UpperHalfPlane) : ℂ) =
          ((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) := by
        rw [heckeMat_smul_coe]
        simp only [coe_imagPt, Nat.cast_one, Nat.cast_ofNat, one_mul, Complex.ofReal_div,
          Complex.ofReal_ofNat]
        push_cast; ring
      have hp3 : heckeMat 2 0 1 zero_lt_two zero_lt_one • imagPt t ht = imagPt (2 * t) (by positivity) := by
        apply UpperHalfPlane.ext
        rw [heckeMat_smul_coe]
        simp only [coe_imagPt, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_zero, div_one,
          Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring
      rw [hp1, hp3, ← cuspImag_of_pos f (half_pos ht), ← cuspImag_of_pos f (by positivity : 0 < 2 * t),
        ← cuspToComplex_eq f (heckeMat 1 1 2 zero_lt_one zero_lt_two • imagPt t ht), hp2]
      simp only [Nat.cast_one, one_pow, Nat.cast_ofNat, div_one]
      ring
    -- Evaluate each of the 3 integrals by linear change of variables `u = 2 t` and `u = t / 2`
    have hint1 : IntegrableOn (fun t : ℝ =>
        (2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I)
        (Set.Ioi 0) volume := by
      have hbase := integrableOn_cuspRay_poly f (k - 2) (2 * X) 0
      have hcomp := integrableOn_Ioi_mul_left (by norm_num : (0 : ℝ) < 2) hbase
      refine IntegrableOn.congr_fun (hcomp.const_mul (2 : ℂ)) (fun t ht => ?_) measurableSet_Ioi
      have ht0 : 0 < t := ht
      rw [Rat.cast_zero, zero_add, cuspToComplex, ← cuspImag_eq_ofComplex f (by positivity : 0 < 2 * t)]
      have hpow : (2 * X - Complex.I * ((2 * t : ℝ) : ℂ)) ^ (k - 2) =
          (2 : ℂ) ^ (k - 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) := by
        rw [← mul_pow]; congr 1; push_cast; ring
      have h2k : (2 : ℂ) * (2 : ℂ) ^ (k - 2) = (2 : ℂ) ^ (k - 1) := by
        rw [← pow_succ', show (k - 2) + 1 = k - 1 by omega]
      rw [hpow]
      calc (2 : ℂ) * (cuspImag f (2 * t) * ((2 : ℂ) ^ (k - 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2)) * Complex.I)
          = ((2 : ℂ) * (2 : ℂ) ^ (k - 2)) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I := by ring
        _ = (2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I := by rw [h2k]
    have hint2 : IntegrableOn (fun t : ℝ =>
        (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I)
        (Set.Ioi 0) volume := by
      have hbase := integrableOn_cuspRay_poly f (k - 2) (X / 2) 0
      have hcomp := integrableOn_Ioi_mul_left (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) hbase
      refine IntegrableOn.congr_fun (hcomp.const_mul ((2 : ℂ) ^ (k - 2) / 2)) (fun t ht => ?_)
        measurableSet_Ioi
      have ht0 : 0 < t := ht
      rw [Rat.cast_zero, zero_add, show (2 : ℝ)⁻¹ * t = t / 2 by ring,
        cuspToComplex, ← cuspImag_eq_ofComplex f (half_pos ht0)]
      have hpow : (2 : ℂ) ^ (k - 2) * (X / 2 - Complex.I * ((t / 2 : ℝ) : ℂ)) ^ (k - 2) =
          (X - Complex.I * (t : ℂ)) ^ (k - 2) := by
        rw [← mul_pow]; congr 1; push_cast; ring
      calc (2 : ℂ) ^ (k - 2) / 2 * (cuspImag f (t / 2) *
              (X / 2 - Complex.I * ((t / 2 : ℝ) : ℂ)) ^ (k - 2) * Complex.I)
          = (1 / 2 : ℂ) * cuspImag f (t / 2) *
              ((2 : ℂ) ^ (k - 2) * (X / 2 - Complex.I * ((t / 2 : ℝ) : ℂ)) ^ (k - 2)) * Complex.I := by ring
        _ = (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I := by rw [hpow]
    have hint3 : IntegrableOn (fun t : ℝ =>
        (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
          (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) (Set.Ioi 0) volume := by
      have hbase := integrableOn_cuspRay_poly f (k - 2) ((X + 1) / 2) (1 / 2 : ℚ)
      have hcomp := integrableOn_Ioi_mul_left (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) hbase
      refine IntegrableOn.congr_fun (hcomp.const_mul ((2 : ℂ) ^ (k - 2) / 2)) (fun t _ => ?_)
        measurableSet_Ioi
      rw [show (2 : ℝ)⁻¹ * t = t / 2 by ring]
      have hpow : (2 : ℂ) ^ (k - 2) *
          ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))) ^ (k - 2) =
          (X - Complex.I * (t : ℂ)) ^ (k - 2) := by
        rw [← mul_pow]; congr 1; push_cast; ring
      calc (2 : ℂ) ^ (k - 2) / 2 *
              (cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
                ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))) ^ (k - 2) *
                Complex.I)
          = (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
              ((2 : ℂ) ^ (k - 2) *
                ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))) ^ (k - 2)) *
              Complex.I := by ring
        _ = (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
              (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I := by rw [hpow]
    have hsplit : (∫ t in Set.Ioi (0 : ℝ),
        cuspImag (heckeCuspForm k (by omega) 2 (by norm_num) f) t *
          (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) =
      (∫ t in Set.Ioi (0 : ℝ),
        (2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) +
      (∫ t in Set.Ioi (0 : ℝ),
        (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) +
      (∫ t in Set.Ioi (0 : ℝ),
        (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
          (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) := by
      have h12 : (∫ t in Set.Ioi (0 : ℝ),
          (2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) +
        (∫ t in Set.Ioi (0 : ℝ),
          (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) =
        ∫ t in Set.Ioi (0 : ℝ),
          ((2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I +
            (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) :=
        (MeasureTheory.integral_add hint1 hint2).symm
      have h123 : (∫ t in Set.Ioi (0 : ℝ),
          ((2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I +
            (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I)) +
        (∫ t in Set.Ioi (0 : ℝ),
          (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
            (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) =
        ∫ t in Set.Ioi (0 : ℝ),
          (((2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I +
            (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) +
            (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
              (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) :=
        (MeasureTheory.integral_add (hint1.add hint2) hint3).symm
      rw [h12, h123]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [hT2_apply t ht]; ring
    rw [hsplit]
    -- Identify each of the three scaled integrals via `integral_comp_mul_left_Ioi`
    have heq1 : (∫ t in Set.Ioi (0 : ℝ),
        (2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) =
        ∫ t in Set.Ioi (0 : ℝ), cuspImag f t * (2 * X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I := by
      have hsub := MeasureTheory.integral_comp_mul_left_Ioi
        (fun u : ℝ => cuspImag f u * (2 * X - Complex.I * (u : ℂ)) ^ (k - 2) * Complex.I)
        (0 : ℝ) (by norm_num : (0 : ℝ) < 2)
      simp only [mul_zero, Complex.real_smul] at hsub
      have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
      have hmul : (2 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          cuspImag f (2 * t) * (2 * X - Complex.I * ((2 * t : ℝ) : ℂ)) ^ (k - 2) * Complex.I =
          ∫ u in Set.Ioi (0 : ℝ), cuspImag f u * (2 * X - Complex.I * (u : ℂ)) ^ (k - 2) * Complex.I := by
        rw [hsub, ← mul_assoc, Complex.ofReal_inv, Complex.ofReal_ofNat, mul_inv_cancel₀ h2_ne,
          one_mul]
      rw [← hmul, ← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      have hpow : (2 * X - Complex.I * ((2 * t : ℝ) : ℂ)) ^ (k - 2) =
          (2 : ℂ) ^ (k - 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) := by
        rw [← mul_pow]; congr 1; push_cast; ring
      have h2k : (2 : ℂ) * (2 : ℂ) ^ (k - 2) = (2 : ℂ) ^ (k - 1) := by
        rw [← pow_succ', show (k - 2) + 1 = k - 1 by omega]
      rw [hpow]
      calc (2 : ℂ) ^ (k - 1) * cuspImag f (2 * t) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I
          = ((2 : ℂ) * (2 : ℂ) ^ (k - 2)) * cuspImag f (2 * t) *
              (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I := by rw [h2k]
        _ = (2 : ℂ) * (cuspImag f (2 * t) *
              ((2 : ℂ) ^ (k - 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2)) * Complex.I) := by ring
    have heq2 : (∫ t in Set.Ioi (0 : ℝ),
        (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) =
        (2 : ℂ) ^ (k - 2) * ∫ u in Set.Ioi (0 : ℝ),
          cuspImag f u * (X / 2 - Complex.I * (u : ℂ)) ^ (k - 2) * Complex.I := by
      have hsub := MeasureTheory.integral_comp_mul_left_Ioi
        (fun u : ℝ => cuspImag f u * (X / 2 - Complex.I * (u : ℂ)) ^ (k - 2) * Complex.I)
        (0 : ℝ) (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
      simp only [mul_zero, inv_inv, Complex.real_smul] at hsub
      have hmul : (1 / 2 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          cuspImag f ((2 : ℝ)⁻¹ * t) * (X / 2 - Complex.I * (((2 : ℝ)⁻¹ * t : ℝ) : ℂ)) ^ (k - 2) * Complex.I =
          ∫ u in Set.Ioi (0 : ℝ), cuspImag f u * (X / 2 - Complex.I * (u : ℂ)) ^ (k - 2) * Complex.I := by
        rw [hsub]; push_cast; ring
      rw [← hmul, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [show (2 : ℝ)⁻¹ * t = t / 2 by ring]
      have hpow : (2 : ℂ) ^ (k - 2) * (X / 2 - Complex.I * ((t / 2 : ℝ) : ℂ)) ^ (k - 2) =
          (X - Complex.I * (t : ℂ)) ^ (k - 2) := by
        rw [← mul_pow]; congr 1; push_cast; ring
      calc (1 / 2 : ℂ) * cuspImag f (t / 2) * (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I
          = (1 / 2 : ℂ) * cuspImag f (t / 2) *
              ((2 : ℂ) ^ (k - 2) * (X / 2 - Complex.I * ((t / 2 : ℝ) : ℂ)) ^ (k - 2)) * Complex.I := by
              rw [hpow]
        _ = (2 : ℂ) ^ (k - 2) * ((1 / 2 : ℂ) *
              (cuspImag f (t / 2) * (X / 2 - Complex.I * ((t / 2 : ℝ) : ℂ)) ^ (k - 2) * Complex.I)) := by ring
    have heq3 : (∫ t in Set.Ioi (0 : ℝ),
        (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
          (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I) =
        (2 : ℂ) ^ (k - 2) * ∫ u in Set.Ioi (0 : ℝ),
          cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
            ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ))) ^ (k - 2) * Complex.I := by
      have hsub := MeasureTheory.integral_comp_mul_left_Ioi
        (fun u : ℝ => cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
          ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ))) ^ (k - 2) * Complex.I)
        (0 : ℝ) (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
      simp only [mul_zero, inv_inv, Complex.real_smul] at hsub
      have hmul : (1 / 2 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (((2 : ℝ)⁻¹ * t : ℝ) : ℂ)) *
            ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * (((2 : ℝ)⁻¹ * t : ℝ) : ℂ))) ^ (k - 2) *
            Complex.I =
          ∫ u in Set.Ioi (0 : ℝ),
            cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ)) *
              ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * (u : ℂ))) ^ (k - 2) * Complex.I := by
        rw [hsub]; push_cast; ring
      rw [← hmul, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [show (2 : ℝ)⁻¹ * t = t / 2 by ring]
      have hpow : (2 : ℂ) ^ (k - 2) *
          ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))) ^ (k - 2) =
          (X - Complex.I * (t : ℂ)) ^ (k - 2) := by
        rw [← mul_pow]; congr 1; push_cast; ring
      calc (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
              (X - Complex.I * (t : ℂ)) ^ (k - 2) * Complex.I
          = (1 / 2 : ℂ) * cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
              ((2 : ℂ) ^ (k - 2) *
                ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))) ^ (k - 2)) *
              Complex.I := by rw [hpow]
        _ = (2 : ℂ) ^ (k - 2) * ((1 / 2 : ℂ) *
              (cuspToComplex f (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)) *
                ((X + 1) / 2 - (((1 / 2 : ℚ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))) ^ (k - 2) *
                Complex.I)) := by ring
    rw [heq1, heq2, heq3]
  -- Step 2: Substitute `halfPeriodPoly_eq` and simplify the 4th Heilbronn matrix
  rw [hstep1, halfPeriodPoly_eq hk f, polySlash_sub,
    polySlash_mul !![1, 0; -2, 1] !![1, 1; 0, 2] (periodPoly_natDegree_le f)]
  have hmat : (!![1, 0; -2, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 1; 0, 2] =
      matS * (-1 : Matrix (Fin 2) (Fin 2) ℤ) * !![2, 0; 1, 1] := by
    rw [matS_eq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmat, ← polySlash_mul (matS * (-1 : Matrix (Fin 2) (Fin 2) ℤ)) !![2, 0; 1, 1]
    (periodPoly_natDegree_le f), ← polySlash_mul matS (-1 : Matrix (Fin 2) (Fin 2) ℤ)
    (periodPoly_natDegree_le f), polySlash_neg_one (polySlash_natDegree_le _ _ _)]
  rcases Nat.even_or_odd k with hev | hodd
  · have hwev : Even (k - 2) := by rcases hev with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
    have hnegS : -polySlash (k - 2) matS (periodPoly f) = periodPoly f := by
      linear_combination -(periodPoly_S_relation hk f)
    rw [hwev.neg_one_pow, one_smul, sub_eq_add_neg, ← polySlash_neg, hnegS]
    ring
  · have hoddZ : Odd (k : ℤ) := by
      rcases hodd with ⟨m, rfl⟩; exact ⟨m, by push_cast; ring⟩
    have hP0 : periodPoly f = 0 := by
      apply Polynomial.funext; intro X
      rw [periodPoly_eval hk f, Polynomial.eval_zero]
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      rw [cuspImag_of_pos f ht, cuspForm_eq_zero_of_odd hoddZ f _,
        zero_mul, zero_mul]
    rw [hP0]
    simp [polySlash_zero]

end PeriodPolynomialAndCocycle

/-! ## Section 4: Manin's Exact Period-Ratio Theorem for Ramanujan's `Δ` (`k = 12`, `0` Assumptions!) -/

section ManinDeltaPeriodRatios

/-- Explicit formula for `(periodPoly ramanujanDelta).eval X` in terms of the 6 independent
completed `L`-values `Λ(Δ, 1), ..., Λ(Δ, 6)`. -/
private lemma periodPoly_delta_eval (X : ℂ) :
    (periodPoly ramanujanDelta).eval X =
      (10 * completedDeltaL 2 * (X ^ 9 + X) -
        120 * completedDeltaL 4 * (X ^ 7 + X ^ 3) +
        252 * completedDeltaL 6 * X ^ 5) +
      Complex.I * (completedDeltaL 1 * (X ^ 10 - 1) -
        45 * completedDeltaL 3 * (X ^ 8 - X ^ 2) +
        210 * completedDeltaL 5 * (X ^ 6 - X ^ 4)) := by
  have hfe11 : completedDeltaL 11 = completedDeltaL 1 := by
    simpa [show (12 : ℂ) - 1 = 11 by norm_num] using completedDeltaL_functional_equation 1
  have hfe10 : completedDeltaL 10 = completedDeltaL 2 := by
    simpa [show (12 : ℂ) - 2 = 10 by norm_num] using completedDeltaL_functional_equation 2
  have hfe9 : completedDeltaL 9 = completedDeltaL 3 := by
    simpa [show (12 : ℂ) - 3 = 9 by norm_num] using completedDeltaL_functional_equation 3
  have hfe8 : completedDeltaL 8 = completedDeltaL 4 := by
    simpa [show (12 : ℂ) - 4 = 8 by norm_num] using completedDeltaL_functional_equation 4
  have hfe7 : completedDeltaL 7 = completedDeltaL 5 := by
    simpa [show (12 : ℂ) - 5 = 7 by norm_num] using completedDeltaL_functional_equation 5
  unfold periodPoly
  rw [Polynomial.eval_finsetSum]
  have hcd : ∀ s : ℂ, completedCuspL ramanujanDelta s = completedDeltaL s := fun _ => rfl
  simp only [show (12 : ℕ) - 1 = 11 by norm_num, show (12 : ℕ) - 2 = 10 by norm_num,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    cuspPeriod_eq_completedCuspL, hcd]
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  rw [hfe11, hfe10, hfe9, hfe8, hfe7]
  have hc0 : ((10 : ℕ).choose 0 : ℂ) = 1 := by exact_mod_cast (by decide : (10 : ℕ).choose 0 = 1)
  have hc1 : ((10 : ℕ).choose 1 : ℂ) = 10 := by exact_mod_cast (by decide : (10 : ℕ).choose 1 = 10)
  have hc2 : ((10 : ℕ).choose 2 : ℂ) = 45 := by exact_mod_cast (by decide : (10 : ℕ).choose 2 = 45)
  have hc3 : ((10 : ℕ).choose 3 : ℂ) = 120 := by exact_mod_cast (by decide : (10 : ℕ).choose 3 = 120)
  have hc4 : ((10 : ℕ).choose 4 : ℂ) = 210 := by exact_mod_cast (by decide : (10 : ℕ).choose 4 = 210)
  have hc5 : ((10 : ℕ).choose 5 : ℂ) = 252 := by exact_mod_cast (by decide : (10 : ℕ).choose 5 = 252)
  have hc6 : ((10 : ℕ).choose 6 : ℂ) = 210 := by exact_mod_cast (by decide : (10 : ℕ).choose 6 = 210)
  have hc7 : ((10 : ℕ).choose 7 : ℂ) = 120 := by exact_mod_cast (by decide : (10 : ℕ).choose 7 = 120)
  have hc8 : ((10 : ℕ).choose 8 : ℂ) = 45 := by exact_mod_cast (by decide : (10 : ℕ).choose 8 = 45)
  have hc9 : ((10 : ℕ).choose 9 : ℂ) = 10 := by exact_mod_cast (by decide : (10 : ℕ).choose 9 = 10)
  have hc10 : ((10 : ℕ).choose 10 : ℂ) = 1 := by exact_mod_cast (by decide : (10 : ℕ).choose 10 = 1)
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
  have hI4 : Complex.I ^ 4 = 1 := by rw [pow_succ, hI3]; linear_combination -Complex.I_sq
  have hI5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, hI4, one_mul]
  have hI6 : Complex.I ^ 6 = -1 := by rw [pow_succ, hI5, Complex.I_mul_I]
  have hI7 : Complex.I ^ 7 = -Complex.I := by rw [pow_succ, hI6]; ring
  have hI8 : Complex.I ^ 8 = 1 := by rw [pow_succ, hI7]; linear_combination -Complex.I_sq
  have hI9 : Complex.I ^ 9 = Complex.I := by rw [pow_succ, hI8, one_mul]
  have hI10 : Complex.I ^ 10 = -1 := by rw [pow_succ, hI9, Complex.I_mul_I]
  have hI11 : Complex.I ^ 11 = -Complex.I := by rw [pow_succ, hI10]; ring
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10,
    hI2, hI3, hI4, hI5, hI6, hI7, hI8, hI9, hI10, hI11]
  ring

private lemma completedDeltaL_real_eq (x : ℝ) :
    completedDeltaL (x : ℂ) = ((completedDeltaL (x : ℂ)).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact completedDeltaL_real_on_real x

private lemma completedDeltaL_eq_re_1 : completedDeltaL 1 = ((completedDeltaL 1).re : ℂ) := by
  simpa using completedDeltaL_real_eq 1
private lemma completedDeltaL_eq_re_2 : completedDeltaL 2 = ((completedDeltaL 2).re : ℂ) := by
  simpa using completedDeltaL_real_eq 2
private lemma completedDeltaL_eq_re_3 : completedDeltaL 3 = ((completedDeltaL 3).re : ℂ) := by
  simpa using completedDeltaL_real_eq 3
private lemma completedDeltaL_eq_re_4 : completedDeltaL 4 = ((completedDeltaL 4).re : ℂ) := by
  simpa using completedDeltaL_real_eq 4
private lemma completedDeltaL_eq_re_5 : completedDeltaL 5 = ((completedDeltaL 5).re : ℂ) := by
  simpa using completedDeltaL_real_eq 5
private lemma completedDeltaL_eq_re_6 : completedDeltaL 6 = ((completedDeltaL 6).re : ℂ) := by
  simpa using completedDeltaL_real_eq 6

/-- **MANIN'S EXACT EVEN CRITICAL `L`-VALUE RATIOS FOR RAMANUJAN'S `Δ` (`0` Assumptions!)**:
all 5 even critical completed `L`-values `Λ(Δ, 2), Λ(Δ, 4), Λ(Δ, 6), Λ(Δ, 8), Λ(Δ, 10)` lie in a
1-dimensional line with exact rational ratios `48 : 25 : 20 : 25 : 48`! -/
theorem delta_even_critical_ratios :
    completedDeltaL 10 = completedDeltaL 2 ∧
    completedDeltaL 8 = completedDeltaL 4 ∧
    48 * completedDeltaL 4 = 25 * completedDeltaL 2 ∧
    12 * completedDeltaL 6 = 5 * completedDeltaL 2 ∧
    5 * completedDeltaL 6 = 4 * completedDeltaL 4 := by
  have hfe10 : completedDeltaL 10 = completedDeltaL 2 := by
    simpa [show (12 : ℂ) - 2 = 10 by norm_num] using completedDeltaL_functional_equation 2
  have hfe8 : completedDeltaL 8 = completedDeltaL 4 := by
    simpa [show (12 : ℂ) - 4 = 8 by norm_num] using completedDeltaL_functional_equation 4
  have hU := periodPoly_U_relation (by norm_num : 2 ≤ 12) ramanujanDelta
  have hU_entries : matU 0 0 = 0 ∧ matU 0 1 = -1 ∧ matU 1 0 = 1 ∧ matU 1 1 = 1 := by
    rw [matU_eq]; decide
  have hU2_entries : (matU ^ 2) 0 0 = -1 ∧ (matU ^ 2) 0 1 = -1 ∧
      (matU ^ 2) 1 0 = 1 ∧ (matU ^ 2) 1 1 = 0 := by
    rw [matU_sq_eq]; decide
  set P : Polynomial ℂ := periodPoly ramanujanDelta
  have hPdeg : P.natDegree ≤ 10 := periodPoly_natDegree_le ramanujanDelta
  -- Equation 1: evaluate `P + P|_U + P|_{U^2} = 0` at `X = 0` and take real part
  have h0 := congrArg (Polynomial.eval (0 : ℂ)) hU
  rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_zero,
    polySlash_eval hPdeg matU (by rw [hU_entries.2.2.1, hU_entries.2.2.2]; norm_num),
    polySlash_eval_eq_sum] at h0
  -- Simplify `(polySlash 10 (matU ^ 2) P).eval 0`: only the `m = 10` term survives!
  have hU2_zero : (∑ m ∈ Finset.range (10 + 1),
      P.coeff m * (((matU ^ 2) 0 0 : ℂ) * 0 + ((matU ^ 2) 0 1 : ℂ)) ^ m *
        (((matU ^ 2) 1 0 : ℂ) * 0 + ((matU ^ 2) 1 1 : ℂ)) ^ (10 - m)) = P.coeff 10 := by
    rw [hU2_entries.1, hU2_entries.2.1, hU2_entries.2.2.1, hU2_entries.2.2.2]
    rw [Finset.sum_eq_single 10]
    · simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, mul_zero, zero_add, add_zero,
        Nat.sub_self, pow_zero, mul_one]
      norm_num
    · intro m hm hne
      have hlt : m < 10 := by
        have := Finset.mem_range.mp hm; omega
      have hsub : 10 - m ≠ 0 := by omega
      simp [zero_pow hsub]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by norm_num)) hnot
  have hP10 : P.coeff 10 = Complex.I * completedDeltaL 1 := by
    dsimp only [P]
    rw [periodPoly_coeff (by norm_num) ramanujanDelta (by norm_num), cuspPeriod_eq_completedCuspL]
    simp [completedDeltaL]
  rw [hU2_zero, hP10, hU_entries.1, hU_entries.2.1, hU_entries.2.2.1, hU_entries.2.2.2] at h0
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, mul_zero, zero_add, one_pow, one_mul,
    div_one] at h0
  rw [periodPoly_delta_eval 0, periodPoly_delta_eval (-1)] at h0
  have h0_re := congrArg Complex.re h0
  rw [completedDeltaL_eq_re_1, completedDeltaL_eq_re_2, completedDeltaL_eq_re_3,
    completedDeltaL_eq_re_4, completedDeltaL_eq_re_5, completedDeltaL_eq_re_6] at h0_re
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im, Complex.sub_im,
    Complex.mul_im] at h0_re
  -- Equation 2: evaluate `P + P|_U + P|_{U^2} = 0` at `X = 1` and take real part
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) hU
  rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_zero,
    polySlash_eval hPdeg matU (by rw [hU_entries.2.2.1, hU_entries.2.2.2]; norm_num),
    polySlash_eval hPdeg (matU ^ 2) (by rw [hU2_entries.2.2.1, hU2_entries.2.2.2]; norm_num)] at h1
  rw [hU_entries.1, hU_entries.2.1, hU_entries.2.2.1, hU_entries.2.2.2,
    hU2_entries.1, hU2_entries.2.1, hU2_entries.2.2.1, hU2_entries.2.2.2] at h1
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, mul_one, zero_add, add_zero, one_pow,
    one_mul, div_one] at h1
  rw [periodPoly_delta_eval 1, periodPoly_delta_eval (-1 / (1 + 1)),
    periodPoly_delta_eval (-1 + -1)] at h1
  have h1_re := congrArg Complex.re h1
  rw [completedDeltaL_eq_re_1, completedDeltaL_eq_re_2, completedDeltaL_eq_re_3,
    completedDeltaL_eq_re_4, completedDeltaL_eq_re_5, completedDeltaL_eq_re_6] at h1_re
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im, Complex.sub_im,
    Complex.mul_im] at h1_re
  have h42_re : 48 * (completedDeltaL 4).re = 25 * (completedDeltaL 2).re := by linarith
  have h62_re : 12 * (completedDeltaL 6).re = 5 * (completedDeltaL 2).re := by linarith
  have h64_re : 5 * (completedDeltaL 6).re = 4 * (completedDeltaL 4).re := by linarith
  refine ⟨hfe10, hfe8, ?_, ?_, ?_⟩
  · rw [completedDeltaL_eq_re_4, completedDeltaL_eq_re_2]
    exact_mod_cast h42_re
  · rw [completedDeltaL_eq_re_6, completedDeltaL_eq_re_2]
    exact_mod_cast h62_re
  · rw [completedDeltaL_eq_re_6, completedDeltaL_eq_re_4]
    exact_mod_cast h64_re

/-- **MANIN'S EXACT ODD CRITICAL `L`-VALUE RATIOS FOR RAMANUJAN'S `Δ` — INCLUDING THE `691`
RELATION (`0` Assumptions!)**:
all 6 odd critical completed `L`-values `Λ(Δ, 1), Λ(Δ, 3), Λ(Δ, 5), Λ(Δ, 7), Λ(Δ, 9), Λ(Δ, 11)`
have exact rational ratios `1620 : 691 : 444.21...`, specifically:
`14 * Λ(Δ, 5) = 9 * Λ(Δ, 3)`, `691 * Λ(Δ, 1) = 1620 * Λ(Δ, 3)`, and `691 * Λ(Δ, 1) = 2520 * Λ(Δ, 5)`! -/
theorem delta_odd_critical_ratios :
    completedDeltaL 11 = completedDeltaL 1 ∧
    completedDeltaL 9 = completedDeltaL 3 ∧
    completedDeltaL 7 = completedDeltaL 5 ∧
    14 * completedDeltaL 5 = 9 * completedDeltaL 3 ∧
    691 * completedDeltaL 1 = 1620 * completedDeltaL 3 ∧
    691 * completedDeltaL 1 = 2520 * completedDeltaL 5 := by
  have hfe11 : completedDeltaL 11 = completedDeltaL 1 := by
    simpa [show (12 : ℂ) - 1 = 11 by norm_num] using completedDeltaL_functional_equation 1
  have hfe9 : completedDeltaL 9 = completedDeltaL 3 := by
    simpa [show (12 : ℂ) - 3 = 9 by norm_num] using completedDeltaL_functional_equation 3
  have hfe7 : completedDeltaL 7 = completedDeltaL 5 := by
    simpa [show (12 : ℂ) - 5 = 7 by norm_num] using completedDeltaL_functional_equation 5
  -- Part A: `14 * Λ(Δ, 5) = 9 * Λ(Δ, 3)` from the `U`-relation at `X = 2` (imaginary part)
  have hU := periodPoly_U_relation (by norm_num : 2 ≤ 12) ramanujanDelta
  have hU_entries : matU 0 0 = 0 ∧ matU 0 1 = -1 ∧ matU 1 0 = 1 ∧ matU 1 1 = 1 := by
    rw [matU_eq]; decide
  have hU2_entries : (matU ^ 2) 0 0 = -1 ∧ (matU ^ 2) 0 1 = -1 ∧
      (matU ^ 2) 1 0 = 1 ∧ (matU ^ 2) 1 1 = 0 := by
    rw [matU_sq_eq]; decide
  set P : Polynomial ℂ := periodPoly ramanujanDelta
  have hPdeg : P.natDegree ≤ 10 := periodPoly_natDegree_le ramanujanDelta
  have h2 := congrArg (Polynomial.eval (2 : ℂ)) hU
  rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_zero,
    polySlash_eval hPdeg matU (by rw [hU_entries.2.2.1, hU_entries.2.2.2]; norm_num),
    polySlash_eval hPdeg (matU ^ 2) (by rw [hU2_entries.2.2.1, hU2_entries.2.2.2]; norm_num)] at h2
  rw [hU_entries.1, hU_entries.2.1, hU_entries.2.2.1, hU_entries.2.2.2,
    hU2_entries.1, hU2_entries.2.1, hU2_entries.2.2.1, hU2_entries.2.2.2] at h2
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, zero_add, one_mul, add_zero] at h2
  rw [periodPoly_delta_eval 2, periodPoly_delta_eval (-1 / (2 + 1)),
    periodPoly_delta_eval ((-1 * 2 + -1) / 2)] at h2
  have h2_im := congrArg Complex.im h2
  rw [completedDeltaL_eq_re_1, completedDeltaL_eq_re_2, completedDeltaL_eq_re_3,
    completedDeltaL_eq_re_4, completedDeltaL_eq_re_5, completedDeltaL_eq_re_6] at h2_im
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im, Complex.sub_im,
    Complex.mul_im] at h2_im
  have h53_re : 14 * (completedDeltaL 5).re = 9 * (completedDeltaL 3).re := by linarith
  -- Part B: `691 * Λ(Δ, 1) = 1620 * Λ(Δ, 3)` from `T_2 Δ = -24 Δ` + `periodPoly_heckeTwo` at `X = 0`!
  have hT2 := periodPoly_heckeTwo (by norm_num : 2 ≤ 12) ramanujanDelta
  have hMordell : heckeCuspForm 12 (by norm_num) 2 (by norm_num) ramanujanDelta =
      (-24 : ℂ) • ramanujanDelta := by
    rw [heckeCuspForm_ramanujanDelta (by norm_num), ramanujanTau_two]
    norm_num
  have hT2_lhs : periodPoly (heckeCuspForm 12 (by norm_num) 2 (by norm_num) ramanujanDelta) =
      (-24 : ℂ) • P := by
    rw [hMordell]
    apply Polynomial.funext; intro X
    rw [periodPoly_eval (by norm_num), Polynomial.eval_smul, smul_eq_mul,
      periodPoly_eval (by norm_num), ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [cuspImag_of_pos _ ht, cuspImag_of_pos _ ht]
    change ((-24 : ℂ) * ramanujanDelta (imagPt t ht)) * (X - Complex.I * (t : ℂ)) ^ 10 * Complex.I = _
    ring
  rw [hT2_lhs] at hT2
  have hT2_0 := congrArg (Polynomial.eval (0 : ℂ)) hT2
  rw [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_add, Polynomial.eval_add,
    Polynomial.eval_add,
    polySlash_eval hPdeg !![2, 0; 0, 1] (by norm_num),
    polySlash_eval hPdeg !![1, 0; 0, 2] (by norm_num),
    polySlash_eval hPdeg !![1, 1; 0, 2] (by norm_num),
    polySlash_eval hPdeg !![2, 0; 1, 1] (by norm_num)] at hT2_0
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_zero,
    Int.cast_one, Int.cast_ofNat, mul_zero, zero_add, add_zero, one_pow, one_mul,
    div_one, zero_div] at hT2_0
  rw [periodPoly_delta_eval 0, periodPoly_delta_eval (1 / 2)] at hT2_0
  have hT2_im := congrArg Complex.im hT2_0
  rw [completedDeltaL_eq_re_1, completedDeltaL_eq_re_2, completedDeltaL_eq_re_3,
    completedDeltaL_eq_re_4, completedDeltaL_eq_re_5, completedDeltaL_eq_re_6] at hT2_im
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im, Complex.sub_im,
    Complex.mul_im] at hT2_im
  have h13_re : 691 * (completedDeltaL 1).re = 1620 * (completedDeltaL 3).re := by linarith
  have h15_re : 691 * (completedDeltaL 1).re = 2520 * (completedDeltaL 5).re := by linarith
  refine ⟨hfe11, hfe9, hfe7, ?_, ?_, ?_⟩
  · rw [completedDeltaL_eq_re_5, completedDeltaL_eq_re_3]
    exact_mod_cast h53_re
  · rw [completedDeltaL_eq_re_1, completedDeltaL_eq_re_3]
    exact_mod_cast h13_re
  · rw [completedDeltaL_eq_re_1, completedDeltaL_eq_re_5]
    exact_mod_cast h15_re

/-- **MANIN'S MASTER PERIOD-RATIO THEOREM FOR RAMANUJAN'S `Δ` (Manin 1973, `0` Assumptions!)**:
combines all exact rational ratios of even and odd critical values of `Λ(Δ, s)`, plus the exact
2-parameter closed-form period polynomial `periodPoly ramanujanDelta`! -/
theorem manin_delta_period_ratios :
    (48 * completedDeltaL 4 = 25 * completedDeltaL 2 ∧
     12 * completedDeltaL 6 = 5 * completedDeltaL 2 ∧
     5 * completedDeltaL 6 = 4 * completedDeltaL 4) ∧
    (14 * completedDeltaL 5 = 9 * completedDeltaL 3 ∧
     691 * completedDeltaL 1 = 1620 * completedDeltaL 3 ∧
     691 * completedDeltaL 1 = 2520 * completedDeltaL 5) ∧
    (∀ X : ℂ,
      (periodPoly ramanujanDelta).eval X =
        (5 / 2 : ℂ) * completedDeltaL 2 *
          (4 * X ^ 9 - 25 * X ^ 7 + 42 * X ^ 5 - 25 * X ^ 3 + 4 * X) +
        Complex.I * (-45 * completedDeltaL 3) *
          (-(36 / 691 : ℂ) * (X ^ 10 - 1) + (X ^ 8 - X ^ 2) - 3 * (X ^ 6 - X ^ 4))) := by
  obtain ⟨_, _, h42, h62, h64⟩ := delta_even_critical_ratios
  obtain ⟨_, _, _, h53, h13, h15⟩ := delta_odd_critical_ratios
  refine ⟨⟨h42, h62, h64⟩, ⟨h53, h13, h15⟩, fun X => ?_⟩
  rw [periodPoly_delta_eval X]
  have h4 : completedDeltaL 4 = (25 / 48 : ℂ) * completedDeltaL 2 := by linear_combination h42 / 48
  have h6 : completedDeltaL 6 = (5 / 12 : ℂ) * completedDeltaL 2 := by linear_combination h62 / 12
  have h5 : completedDeltaL 5 = (9 / 14 : ℂ) * completedDeltaL 3 := by linear_combination h53 / 14
  have h1 : completedDeltaL 1 = (1620 / 691 : ℂ) * completedDeltaL 3 := by linear_combination h13 / 691
  rw [h4, h6, h5, h1]
  ring

end ManinDeltaPeriodRatios

/-! ## Section 5: Concrete Modular Symbols `modularSymbol f r` & Mazur–Tate–Teitelbaum `p`-adic Distribution -/

section ModularSymbolsAndMTTDistribution

/-- Vertical-ray restriction `t ↦ f(r + i t)` (for `t > 0`, and `0` for `t ≤ 0`) of a level-1
cusp form `f ∈ S_k(SL₂(ℤ))` above any rational cusp `r : ℚ`. -/
def cuspRay {k : ℤ} (f : CuspForm SL2ZRange k) (r : ℚ) (t : ℝ) : ℂ :=
  if ht : 0 < t then f ⟨(r : ℂ) + Complex.I * (t : ℂ), by simp [ht]⟩ else 0

theorem cuspRay_of_pos {k : ℤ} (f : CuspForm SL2ZRange k) (r : ℚ) {t : ℝ} (ht : 0 < t) :
    cuspRay f r t = f ⟨(r : ℂ) + Complex.I * (t : ℂ), by simp [ht]⟩ :=
  dif_pos ht

/-- Global integrability of `cuspRay f r` on `(0, ∞)` for EVERY `f ∈ S_k(SL₂(ℤ))` and EVERY `r : ℚ`
(exponential decay at both `t → ∞` and `t → 0⁺`). -/
theorem integrableOn_cuspRay {k : ℤ} (f : CuspForm SL2ZRange k) (r : ℚ) :
    IntegrableOn (cuspRay f r) (Set.Ioi (0 : ℝ)) volume := by
  have hbase := integrableOn_cuspRay_poly f 0 0 r
  refine IntegrableOn.congr_fun (hbase.const_mul (-Complex.I)) (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  rw [pow_zero, mul_one, cuspRay_of_pos f r ht0]
  let τ : UpperHalfPlane := ⟨(r : ℂ) + Complex.I * (t : ℂ), by simp [ht0]⟩
  rw [show cuspToComplex f ((r : ℂ) + Complex.I * (t : ℂ)) = f τ from cuspToComplex_eq f τ]
  linear_combination -(f τ) * Complex.I_sq

/-- **Concrete Additive Modular Symbol `modularSymbol f r`** of a level-1 cusp form
`f ∈ S_k(SL₂(ℤ))` at any rational cusp `r ∈ ℚ`:
`modularSymbol f r = ∫_{t > 0} f(r + i t) dt`. -/
def modularSymbol {k : ℤ} (f : CuspForm SL2ZRange k) (r : ℚ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), cuspRay f r t

/-- At `r = 0`, `modularSymbol f 0 = completedCuspL f 1 = Λ(f, 1)`. -/
theorem modularSymbol_zero {k : ℤ} (f : CuspForm SL2ZRange k) :
    modularSymbol f 0 = completedCuspL f 1 := by
  unfold modularSymbol completedCuspL
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [cuspRay_of_pos f 0 ht, cuspImag_of_pos f ht, sub_self, Complex.cpow_zero, mul_one]
  congr 1
  apply UpperHalfPlane.ext
  simp [imagPt]

/-- **`ℤ`-Periodicity of Modular Symbols**:
for every `f ∈ S_k(SL₂(ℤ))`, `r : ℚ`, and `m : ℤ`, `modularSymbol f (r + m) = modularSymbol f r`. -/
theorem modularSymbol_add_int {k : ℤ} (f : CuspForm SL2ZRange k) (r : ℚ) (m : ℤ) :
    modularSymbol f (r + (m : ℚ)) = modularSymbol f r := by
  unfold modularSymbol
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  rw [cuspRay_of_pos f (r + (m : ℚ)) ht0, cuspRay_of_pos f r ht0]
  let τ : UpperHalfPlane := ⟨(r : ℂ) + Complex.I * (t : ℂ), by simp [ht0]⟩
  have hpt : (⟨(((r + (m : ℚ) : ℚ) : ℂ)) + Complex.I * (t : ℂ), by simp [ht0]⟩ : UpperHalfPlane) =
      ⟨(τ : ℂ) + (m : ℂ), by simp [τ.im_pos]⟩ := by
    apply UpperHalfPlane.ext
    change ((r + (m : ℚ) : ℚ) : ℂ) + Complex.I * (t : ℂ) = (r : ℂ) + Complex.I * (t : ℂ) + (m : ℂ)
    push_cast; ring
  rw [hpt, cuspForm_add_int f τ m]

theorem modularSymbol_int {k : ℤ} (f : CuspForm SL2ZRange k) (m : ℤ) :
    modularSymbol f (m : ℚ) = modularSymbol f 0 := by
  simpa using modularSymbol_add_int f 0 m

/-- Scaling `modularSymbol` under `c • f`. -/
theorem modularSymbol_smul {k : ℤ} (c : ℂ) (f : CuspForm SL2ZRange k) (r : ℚ) :
    modularSymbol (c • f) r = c * modularSymbol f r := by
  unfold modularSymbol
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [cuspRay_of_pos _ r ht, cuspRay_of_pos f r ht]
  rfl

/-- **Exact Hecke Prime Action on Modular Symbols**:
for EVERY `k ≥ 2`, EVERY `f ∈ S_k(SL₂(ℤ))`, EVERY prime `p`, and EVERY `r : ℚ`,
`∑_{b = 0}^{p - 1} modularSymbol f ((r + b) / p) = modularSymbol (T_p f) r - p^{k - 2} * modularSymbol f (p * r)`. -/
theorem modularSymbol_hecke_prime {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {p : ℕ} (hp : p.Prime) (r : ℚ) :
    ∑ b ∈ Finset.range p, modularSymbol f ((r + (b : ℚ)) / (p : ℚ)) =
      modularSymbol (heckeCuspForm k (by omega) p hp.one_le f) r -
        (p : ℂ) ^ (k - 2) * modularSymbol f ((p : ℚ) * r) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp_neC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  -- Expand `(T_p f)(r + i t)` into its `p + 1` coset terms
  have hTp : ∀ t : ℝ, 0 < t →
      cuspRay (heckeCuspForm k (by omega) p hp.one_le f) r t =
        (∑ b ∈ Finset.range p, (p : ℂ)⁻¹ * cuspRay f ((r + (b : ℚ)) / (p : ℚ)) (t / (p : ℝ))) +
          (p : ℂ) ^ (k - 1) * cuspRay f ((p : ℚ) * r) ((p : ℝ) * t) := by
    intro t ht
    rw [cuspRay_of_pos _ r ht]
    let τ : UpperHalfPlane := ⟨(r : ℂ) + Complex.I * (t : ℂ), by simp [ht]⟩
    change slashHeckeOp k (1 : DirichletCharacter ℂ 1) p (f : UpperHalfPlane → ℂ) τ = _
    unfold slashHeckeOp
    rw [hp.divisors, Finset.sum_pair hp.ne_one.symm]
    simp only [trivialChar_one_apply, one_mul, Nat.div_one, Nat.div_self hp.pos,
      Finset.sum_range_one, Nat.zero_lt_one, hp.pos, and_self, ↓reduceDIte]
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [heckeMat_slash_apply (by omega) 1 b p zero_lt_one hp.pos,
        cuspRay_of_pos f ((r + (b : ℚ)) / (p : ℚ)) (div_pos ht hp_pos)]
      have hpt : heckeMat 1 b p zero_lt_one hp.pos • τ =
          ⟨((((r + (b : ℚ)) / (p : ℚ) : ℚ) : ℂ)) + Complex.I * ((t / (p : ℝ) : ℝ) : ℂ),
            by simp [div_pos ht hp_pos]⟩ := by
        apply UpperHalfPlane.ext
        rw [heckeMat_smul_coe]
        simp only [τ, Nat.cast_one, one_mul]
        push_cast; ring
      rw [hpt]
      simp only [Nat.cast_one, one_pow, one_div, mul_comm]
    · rw [heckeMat_slash_apply (by omega) p 0 1 hp.pos zero_lt_one,
        cuspRay_of_pos f ((p : ℚ) * r) (mul_pos hp_pos ht)]
      have hpt : heckeMat p 0 1 hp.pos zero_lt_one • τ =
          ⟨((((p : ℚ) * r : ℚ) : ℂ)) + Complex.I * (((p : ℝ) * t : ℝ) : ℂ),
            by simp [mul_pos hp_pos ht]⟩ := by
        apply UpperHalfPlane.ext
        rw [heckeMat_smul_coe]
        simp only [τ, Nat.cast_zero, Nat.cast_one, add_zero, div_one]
        push_cast; ring
      rw [hpt]
      simp only [Nat.cast_one, div_one, mul_comm]
  -- Integrability and change-of-variables evaluation of each term
  have hint_b : ∀ b ∈ Finset.range p,
      IntegrableOn (fun t : ℝ => (p : ℂ)⁻¹ * cuspRay f ((r + (b : ℚ)) / (p : ℚ)) (t / (p : ℝ)))
        (Set.Ioi 0) volume := by
    intro b _
    have hbase := integrableOn_cuspRay f ((r + (b : ℚ)) / (p : ℚ))
    have hcomp := integrableOn_Ioi_mul_left (inv_pos.mpr hp_pos) hbase
    refine IntegrableOn.congr_fun (hcomp.const_mul (p : ℂ)⁻¹) (fun t _ => ?_) measurableSet_Ioi
    congr 2; rw [div_eq_inv_mul]
  have hint_p : IntegrableOn (fun t : ℝ => (p : ℂ) ^ (k - 1) * cuspRay f ((p : ℚ) * r) ((p : ℝ) * t))
      (Set.Ioi 0) volume := by
    have hbase := integrableOn_cuspRay f ((p : ℚ) * r)
    exact (integrableOn_Ioi_mul_left hp_pos hbase).const_mul _
  have heval_b : ∀ b ∈ Finset.range p,
      (∫ t in Set.Ioi (0 : ℝ), (p : ℂ)⁻¹ * cuspRay f ((r + (b : ℚ)) / (p : ℚ)) (t / (p : ℝ))) =
        modularSymbol f ((r + (b : ℚ)) / (p : ℚ)) := by
    intro b _
    rw [MeasureTheory.integral_const_mul]
    have hsub := MeasureTheory.integral_comp_mul_left_Ioi
      (cuspRay f ((r + (b : ℚ)) / (p : ℚ))) (0 : ℝ) (inv_pos.mpr hp_pos)
    simp only [mul_zero, inv_inv, Complex.real_smul] at hsub
    have hcongr : (∫ t in Set.Ioi (0 : ℝ), cuspRay f ((r + (b : ℚ)) / (p : ℚ)) (t / (p : ℝ))) =
        ∫ t in Set.Ioi (0 : ℝ), cuspRay f ((r + (b : ℚ)) / (p : ℚ)) ((p : ℝ)⁻¹ * t) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by congr 1; rw [div_eq_inv_mul]
    rw [hcongr, hsub]
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ hp_neC, one_mul]
    rfl
  have heval_p : (∫ t in Set.Ioi (0 : ℝ), (p : ℂ) ^ (k - 1) * cuspRay f ((p : ℚ) * r) ((p : ℝ) * t)) =
      (p : ℂ) ^ (k - 2) * modularSymbol f ((p : ℚ) * r) := by
    rw [MeasureTheory.integral_const_mul]
    have hsub := MeasureTheory.integral_comp_mul_left_Ioi
      (cuspRay f ((p : ℚ) * r)) (0 : ℝ) hp_pos
    simp only [mul_zero, Complex.real_smul] at hsub
    rw [hsub]
    push_cast
    have hpk : (p : ℂ) ^ (k - 1) * (p : ℂ)⁻¹ = (p : ℂ) ^ (k - 2) := by
      rw [show k - 1 = (k - 2) + 1 by omega, pow_succ, mul_assoc, mul_inv_cancel₀ hp_neC, mul_one]
    rw [← mul_assoc, hpk]
    rfl
  have hmain : modularSymbol (heckeCuspForm k (by omega) p hp.one_le f) r =
      (∑ b ∈ Finset.range p, modularSymbol f ((r + (b : ℚ)) / (p : ℚ))) +
        (p : ℂ) ^ (k - 2) * modularSymbol f ((p : ℚ) * r) := by
    unfold modularSymbol
    have hcongr : (∫ t in Set.Ioi (0 : ℝ), cuspRay (heckeCuspForm k (by omega) p hp.one_le f) r t) =
        ∫ t in Set.Ioi (0 : ℝ),
          ((∑ b ∈ Finset.range p, (p : ℂ)⁻¹ * cuspRay f ((r + (b : ℚ)) / (p : ℚ)) (t / (p : ℝ))) +
            (p : ℂ) ^ (k - 1) * cuspRay f ((p : ℚ) * r) ((p : ℝ) * t)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => hTp t ht
    rw [hcongr, MeasureTheory.integral_add (integrable_finsetSum _ hint_b) hint_p,
      MeasureTheory.integral_finsetSum _ hint_b, heval_p]
    congr 1
    exact Finset.sum_congr rfl heval_b
  linear_combination -hmain

/-- **EXACT HECKE-EIGENFORM MODULAR-SYMBOL DISTRIBUTION RELATION (`0` Assumptions!)**:
for EVERY Hecke eigenform `f ∈ S_k(SL₂(ℤ))` (`T_p f = a_p • f`, `k ≥ 2`), EVERY prime `p`,
EVERY `a : ℤ`, and EVERY `n ≥ 1`:
`∑_{b = 0}^{p - 1} modularSymbol f ((a + b * p^n) / p^{n+1})
  = a_p * modularSymbol f (a / p^n) - p^{k - 2} * modularSymbol f (a / p^{n - 1})`. -/
theorem modularSymbol_hecke_distribution {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {p : ℕ} (hp : p.Prime) {a_p : ℂ}
    (heig : heckeCuspForm k (by omega) p hp.one_le f = a_p • f)
    (a : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ b ∈ Finset.range p,
        modularSymbol f (((a : ℚ) + (b : ℚ) * (p : ℚ) ^ n) / (p : ℚ) ^ (n + 1)) =
      a_p * modularSymbol f ((a : ℚ) / (p : ℚ) ^ n) -
        (p : ℂ) ^ (k - 2) * modularSymbol f ((a : ℚ) / (p : ℚ) ^ (n - 1)) := by
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h := modularSymbol_hecke_prime hk f hp ((a : ℚ) / (p : ℚ) ^ n)
  rw [heig, modularSymbol_smul] at h
  have h1 : ∀ b ∈ Finset.range p,
      ((a : ℚ) / (p : ℚ) ^ n + (b : ℚ)) / (p : ℚ) =
        ((a : ℚ) + (b : ℚ) * (p : ℚ) ^ n) / (p : ℚ) ^ (n + 1) := by
    intro b _
    rw [pow_succ]
    field_simp [hpQ]
  have h2 : (p : ℚ) * ((a : ℚ) / (p : ℚ) ^ n) = (a : ℚ) / (p : ℚ) ^ (n - 1) := by
    have hn_eq : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn_eq, pow_succ]
    field_simp [hpQ]
  rw [Finset.sum_congr rfl fun b hb => congrArg (modularSymbol f) (h1 b hb), h2] at h
  exact h

/-- **Concrete Mazur–Tate–Teitelbaum `p`-adic Distribution `mttDist`** attached to a cusp form
`f ∈ S_k(SL₂(ℤ))`, prime `p`, and root `α ≠ 0` of the Hecke polynomial `X² - a_p X + p^{k - 1} = 0`:
for every level `n : ℕ` and residue class `a : ZMod (p ^ n)`:
`mttDist f p α n a := α^{-n} modularSymbol f (a / p^n) - (p^{k - 2} / α^{n + 1}) modularSymbol f (a / p^{n - 1})`. -/
def mttDist {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) (p : ℕ) (α : ℂ)
    (n : ℕ) (a : ZMod (p ^ n)) : ℂ :=
  α ^ (-(n : ℤ)) * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ n) -
    ((p : ℂ) ^ (k - 2) / α ^ (n + 1)) * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ (n - 1))

/-- **EXACT MAZUR–TATE–TEITELBAUM DISTRIBUTION COMPATIBILITY (Range Form, `0` Assumptions!)**:
for every `f ∈ S_k(SL₂(ℤ))` (`k ≥ 2`), prime `p`, `T_p f = a_p • f`, and every nonzero root `α`
of `α² - a_p α + p^{k - 1} = 0`:
`∑_{b = 0}^{p - 1} mttDist f p α (n + 1) (a + b * p^n) = mttDist f p α n a` for ALL `n : ℕ`! -/
theorem mttDist_compat_range {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {p : ℕ} (hp : p.Prime) {a_p α : ℂ}
    (heig : heckeCuspForm k (by omega) p hp.one_le f = a_p • f)
    (hα_ne : α ≠ 0) (hα_root : α ^ 2 - a_p * α + (p : ℂ) ^ (k - 1) = 0)
    (n : ℕ) (a : ZMod (p ^ n)) :
    ∑ b ∈ Finset.range p,
        mttDist f p α (n + 1) ((a.val + b * p ^ n : ℕ) : ZMod (p ^ (n + 1))) =
      mttDist f p α n a := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have ha_lt : a.val < p ^ n := ZMod.val_lt a
  -- For `b < p`, `a.val + b * p ^ n < p ^ (n + 1)`, so `.val` is exact with no wrap-around!
  have hval_exact : ∀ b ∈ Finset.range p,
      (((a.val + b * p ^ n : ℕ) : ZMod (p ^ (n + 1)))).val = a.val + b * p ^ n := by
    intro b hb
    have hb_lt : b < p := Finset.mem_range.mp hb
    have hlt : a.val + b * p ^ n < p ^ (n + 1) := by
      have h1 : b * p ^ n + p ^ n = (b + 1) * p ^ n := by ring
      have h2 : (b + 1) * p ^ n ≤ p * p ^ n := Nat.mul_le_mul_right (p ^ n) hb_lt
      rw [pow_succ']
      omega
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  -- Simplify each summand
  have hterm : ∀ b ∈ Finset.range p,
      mttDist f p α (n + 1) ((a.val + b * p ^ n : ℕ) : ZMod (p ^ (n + 1))) =
        α ^ (-((n + 1 : ℕ) : ℤ)) *
          modularSymbol f (((a.val : ℚ) / (p : ℚ) ^ n + (b : ℚ)) / (p : ℚ)) -
        ((p : ℂ) ^ (k - 2) / α ^ (n + 2)) *
          modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ n) := by
    intro b hb
    unfold mttDist
    rw [hval_exact b hb, Nat.add_sub_cancel]
    have harg1 : (((a.val + b * p ^ n : ℕ) : ℚ) / (p : ℚ) ^ (n + 1)) =
        ((a.val : ℚ) / (p : ℚ) ^ n + (b : ℚ)) / (p : ℚ) := by
      push_cast; rw [pow_succ]; field_simp [hpQ]
    have harg2 : (((a.val + b * p ^ n : ℕ) : ℚ) / (p : ℚ) ^ n) =
        (a.val : ℚ) / (p : ℚ) ^ n + ((b : ℤ) : ℚ) := by
      push_cast; field_simp [hpQ]
    rw [harg1, harg2, modularSymbol_add_int f ((a.val : ℚ) / (p : ℚ) ^ n) (b : ℤ)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Apply `modularSymbol_hecke_prime` at `r = a.val / p^n`
  have hhecke := modularSymbol_hecke_prime hk f hp ((a.val : ℚ) / (p : ℚ) ^ n)
  rw [heig, modularSymbol_smul] at hhecke
  rw [hhecke]
  -- Handle `modularSymbol f (p * (a.val / p^n)) = modularSymbol f (a.val / p^(n - 1))` for all `n : ℕ`
  have hpr_eq : modularSymbol f ((p : ℚ) * ((a.val : ℚ) / (p : ℚ) ^ n)) =
      modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ (n - 1)) := by
    cases n with
    | zero =>
      simp only [pow_zero, div_one, Nat.zero_sub]
      have h1 : (p : ℚ) * (a.val : ℚ) = (((p * a.val : ℕ) : ℤ) : ℚ) := by push_cast; rfl
      have h2 : (a.val : ℚ) = ((a.val : ℤ) : ℚ) := by push_cast; rfl
      rw [h1, h2, modularSymbol_int, modularSymbol_int]
    | succ m =>
      rw [Nat.add_sub_cancel]
      congr 1
      have hpow : (p : ℚ) ^ (m + 1) = (p : ℚ) ^ m * (p : ℚ) := pow_succ (p : ℚ) m
      rw [hpow]
      field_simp [hpQ]
  rw [hpr_eq]
  unfold mttDist
  have hα_rel : a_p * α - (p : ℂ) ^ (k - 1) = α ^ 2 := by linear_combination -hα_root
  have hpk : (p : ℂ) * (p : ℂ) ^ (k - 2) = (p : ℂ) ^ (k - 1) := by
    rw [← pow_succ', show (k - 2) + 1 = k - 1 by omega]
  have hzpow1 : α ^ (-((n + 1 : ℕ) : ℤ)) = (α ^ (n + 1))⁻¹ := by
    rw [_root_.zpow_neg, zpow_natCast]
  have hzpow0 : α ^ (-(n : ℤ)) = (α ^ n)⁻¹ := by
    rw [_root_.zpow_neg, zpow_natCast]
  rw [hzpow1, hzpow0]
  have hαn : α ^ n ≠ 0 := pow_ne_zero n hα_ne
  have hαn1 : α ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) hα_ne
  have hαn2 : α ^ (n + 2) ≠ 0 := pow_ne_zero (n + 2) hα_ne
  calc (α ^ (n + 1))⁻¹ * (a_p * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ n) -
            (p : ℂ) ^ (k - 2) * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ (n - 1))) -
          (p : ℂ) * ((p : ℂ) ^ (k - 2) / α ^ (n + 2) * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ n))
      = ((a_p * α - (p : ℂ) * (p : ℂ) ^ (k - 2)) / α ^ (n + 2)) *
          modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ n) -
        ((p : ℂ) ^ (k - 2) / α ^ (n + 1)) * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ (n - 1)) := by
        rw [show α ^ (n + 2) = α ^ (n + 1) * α by rw [pow_succ]]
        field_simp [hα_ne, hαn1]
        ring
    _ = (α ^ 2 / α ^ (n + 2)) * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ n) -
        ((p : ℂ) ^ (k - 2) / α ^ (n + 1)) * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ (n - 1)) := by
        rw [hpk, hα_rel]
    _ = (α ^ n)⁻¹ * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ n) -
        ((p : ℂ) ^ (k - 2) / α ^ (n + 1)) * modularSymbol f ((a.val : ℚ) / (p : ℚ) ^ (n - 1)) := by
        congr 2
        rw [pow_add, pow_two]
        field_simp [hα_ne, hαn]

/-- **EXACT MAZUR–TATE–TEITELBAUM PROJECTIVE DISTRIBUTION COMPATIBILITY (ZMod Fiber Form,
matching `Stage7PadicLFunction.PadicMeasure.compat` verbatim!)**:
for every `f ∈ S_k(SL₂(ℤ))` (`k ≥ 2`), prime `p`, `T_p f = a_p • f`, and nonzero root `α` of
`X² - a_p X + p^{k - 1} = 0`:
`mttDist f p α n a = ∑_{b ≡ a mod p^n} mttDist f p α (n + 1) b`. -/
theorem mttDist_compat {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {p : ℕ} [Fact p.Prime] {a_p α : ℂ}
    (heig : heckeCuspForm k (by omega) p (Fact.out : p.Prime).one_le f = a_p • f)
    (hα_ne : α ≠ 0) (hα_root : α ^ 2 - a_p * α + (p : ℂ) ^ (k - 1) = 0)
    (n : ℕ) (a : ZMod (p ^ n)) :
    mttDist f p α n a =
      ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) =>
        zmodPowStep (p := p) n b = a), mttDist f p α (n + 1) b := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
  rw [← mttDist_compat_range hk f hp heig hα_ne hα_root n a]
  refine Finset.sum_nbij (fun j : ℕ => ((a.val + j * p ^ n : ℕ) : ZMod (p ^ (n + 1)))) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [zmodPowStep, zmodPowCast, map_natCast, Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val]
  · intro j₁ hj₁ j₂ hj₂ heq
    have hj₁_lt : j₁ < p := Finset.mem_range.mp hj₁
    have hj₂_lt : j₂ < p := Finset.mem_range.mp hj₂
    have ha_lt : a.val < p ^ n := ZMod.val_lt a
    have hlt1 : a.val + j₁ * p ^ n < p ^ (n + 1) := by
      have h2 : (j₁ + 1) * p ^ n ≤ p * p ^ n := Nat.mul_le_mul_right _ hj₁_lt
      rw [pow_succ']; nlinarith
    have hlt2 : a.val + j₂ * p ^ n < p ^ (n + 1) := by
      have h2 : (j₂ + 1) * p ^ n ≤ p * p ^ n := Nat.mul_le_mul_right _ hj₂_lt
      rw [pow_succ']; nlinarith
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt1, ZMod.val_natCast, Nat.mod_eq_of_lt hlt2] at hval
    have hmul : j₁ * p ^ n = j₂ * p ^ n := Nat.add_left_cancel hval
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos n) hmul
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hmod : b.val ≡ a.val [MOD p ^ n] := by
      have h := zmodPowCast_val_modEq (p := p) (Nat.le_succ n) b
      rwa [show zmodPowCast (p := p) (Nat.le_succ n) b = a from hb] at h
    have ha_lt : a.val < p ^ n := ZMod.val_lt a
    have hb_lt : b.val < p ^ (n + 1) := ZMod.val_lt b
    have hrem : b.val % p ^ n = a.val := by
      rw [Nat.ModEq] at hmod
      rw [hmod, Nat.mod_eq_of_lt ha_lt]
    let j : ℕ := b.val / p ^ n
    have hj_lt : j < p := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hp.pos n)]
      rwa [mul_comm, ← pow_succ]
    refine ⟨j, Finset.mem_coe.mpr (Finset.mem_range.mpr hj_lt), ?_⟩
    dsimp only
    have hdiv : a.val + j * p ^ n = b.val := by
      rw [← hrem, mul_comm]
      exact Nat.mod_add_div b.val (p ^ n)
    rw [hdiv, ZMod.natCast_zmod_val]
  · intro _ _; rfl

/-- **Exact Total Mass of the MTT Distribution** at `n = 0`:
`mttDist f p α 0 0 = (1 - p^{k - 2} / α) * Λ(f, 1)`. -/
theorem mttDist_total_mass {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ)) (p : ℕ) (α : ℂ) :
    mttDist f p α 0 0 = (1 - (p : ℂ) ^ (k - 2) / α) * completedCuspL f 1 := by
  unfold mttDist
  have h0 : ((0 : ZMod (p ^ 0)).val : ℚ) = 0 := by rw [ZMod.val_zero]; simp
  rw [h0, zero_div, modularSymbol_zero]
  simp only [Nat.cast_zero, neg_zero, zpow_zero, one_mul, zero_add, pow_one]
  ring

/-- **Exact Unit-Group Mass (`ℤ_pˣ`) of the MTT Distribution**:
`∑_{u ∈ (ZMod p)ˣ} mttDist f p α 1 u = (1 - α⁻¹) * (1 - p^{k - 2} / α) * Λ(f, 1)`
(recovering the exact Mazur–Tate–Teitelbaum interpolation Euler factor at `s = 1`!). -/
theorem mttDist_units_mass {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {p : ℕ} [Fact p.Prime] {a_p α : ℂ}
    (heig : heckeCuspForm k (by omega) p (Fact.out : p.Prime).one_le f = a_p • f)
    (hα_ne : α ≠ 0) (hα_root : α ^ 2 - a_p * α + (p : ℂ) ^ (k - 1) = 0) :
    ∑ u ∈ Finset.univ.filter (fun x : ZMod (p ^ 1) => x ≠ 0), mttDist f p α 1 u =
      (1 - α⁻¹) * (1 - (p : ℂ) ^ (k - 2) / α) * completedCuspL f 1 := by
  have htot := mttDist_compat hk f heig hα_ne hα_root 0 0
  have hfilt_all : Finset.univ.filter (fun b : ZMod (p ^ 1) => zmodPowStep (p := p) 0 b = 0) =
      Finset.univ := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact zmod_pow_zero_eq _ _
  rw [hfilt_all] at htot
  have hsplit : (∑ b : ZMod (p ^ 1), mttDist f p α 1 b) =
      mttDist f p α 1 0 +
        ∑ u ∈ Finset.univ.filter (fun x : ZMod (p ^ 1) => x ≠ 0), mttDist f p α 1 u := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod (p ^ 1)))]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x; simp [Finset.mem_erase]
  have h01 : mttDist f p α 1 0 = (α⁻¹ - (p : ℂ) ^ (k - 2) / α ^ 2) * completedCuspL f 1 := by
    unfold mttDist
    have h0 : ((0 : ZMod (p ^ 1)).val : ℚ) = 0 := by rw [ZMod.val_zero]; simp
    rw [h0, zero_div, zero_div, modularSymbol_zero]
    simp only [Nat.cast_one, _root_.zpow_neg_one, show (1 : ℕ) + 1 = 2 by rfl]
    ring
  rw [mttDist_total_mass, hsplit, h01] at htot
  have hcalc : (1 - (p : ℂ) ^ (k - 2) / α) * completedCuspL f 1 -
      (α⁻¹ - (p : ℂ) ^ (k - 2) / α ^ 2) * completedCuspL f 1 =
      (1 - α⁻¹) * (1 - (p : ℂ) ^ (k - 2) / α) * completedCuspL f 1 := by
    field_simp [hα_ne]
  linear_combination -htot + hcalc

/-! ### Unconditional Specialization to Ramanujan's `Δ` & Direct `PadicMeasure` Bridge -/

/-- For EVERY prime `p`, there unconditionally exists a nonzero Satake–Hecke root `α ∈ ℂ` of
`X² - τ(p) X + p¹¹ = 0` (`0` assumptions!). -/
theorem exists_delta_hecke_root {p : ℕ} (hp : p.Prime) :
    ∃ α : ℂ, α ≠ 0 ∧ α ^ 2 - (ramanujanTau p : ℂ) * α + (p : ℂ) ^ 11 = 0 := by
  obtain ⟨α, β, hpair⟩ := exists_satake_pair (ramanujanTau p : ℂ) ((p : ℂ) ^ 11)
  have hroot : α ^ 2 - (ramanujanTau p : ℂ) * α + (p : ℂ) ^ 11 = 0 := by
    rw [← hpair.1, ← hpair.2]; ring
  have hne : α ≠ 0 := by
    intro h0
    have hp11 : (p : ℂ) ^ 11 = 0 := by
      have := hpair.2
      rw [h0, zero_mul] at this
      exact this.symm
    exact pow_ne_zero 11 (Nat.cast_ne_zero.mpr hp.ne_zero) hp11
  exact ⟨α, hne, hroot⟩

/-- Concrete Mazur–Tate–Teitelbaum distribution for Ramanujan's `Δ`. -/
def mttDistDelta (p : ℕ) (α : ℂ) (n : ℕ) (a : ZMod (p ^ n)) : ℂ :=
  mttDist ramanujanDelta p α n a

/-- **UNCONDITIONAL MAZUR–TATE–TEITELBAUM DISTRIBUTION COMPATIBILITY FOR RAMANUJAN'S `Δ`**:
for EVERY prime `p` and EVERY nonzero root `α` of `X² - τ(p) X + p¹¹ = 0`, `mttDistDelta p α`
satisfies exact projective distribution compatibility! -/
theorem mttDistDelta_compat {p : ℕ} [Fact p.Prime] {α : ℂ}
    (hα_ne : α ≠ 0) (hα_root : α ^ 2 - (ramanujanTau p : ℂ) * α + (p : ℂ) ^ 11 = 0)
    (n : ℕ) (a : ZMod (p ^ n)) :
    mttDistDelta p α n a =
      ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) =>
        zmodPowStep (p := p) n b = a), mttDistDelta p α (n + 1) b :=
  mttDist_compat (by norm_num) ramanujanDelta
    (heckeCuspForm_ramanujanDelta (Fact.out : p.Prime).one_le) hα_ne hα_root n a

theorem mttDistDelta_total_mass (p : ℕ) (α : ℂ) :
    mttDistDelta p α 0 0 = (1 - (p : ℂ) ^ 10 / α) * completedDeltaL 1 :=
  mttDist_total_mass ramanujanDelta p α

theorem mttDistDelta_units_mass {p : ℕ} [Fact p.Prime] {α : ℂ}
    (hα_ne : α ≠ 0) (hα_root : α ^ 2 - (ramanujanTau p : ℂ) * α + (p : ℂ) ^ 11 = 0) :
    ∑ u ∈ Finset.univ.filter (fun x : ZMod (p ^ 1) => x ≠ 0), mttDistDelta p α 1 u =
      (1 - α⁻¹) * (1 - (p : ℂ) ^ 10 / α) * completedDeltaL 1 :=
  mttDist_units_mass (by norm_num) ramanujanDelta
    (heckeCuspForm_ramanujanDelta (Fact.out : p.Prime).one_le) hα_ne hα_root

/-- **Direct Bridge from `mttDist` to `Stage7PadicLFunction.PadicMeasure p`**:
whenever a period-normalized `ℤ_[p]`-valued family `val n a` matches `Ω⁻¹ * mttDist f p α n a`
under any injective additive map `σ : ℤ_[p] →+ ℂ`, it unconditionally defines a genuine
`Stage7PadicLFunction.PadicMeasure p`! -/
def mttDistToPadicMeasure {k : ℕ} (hk : 2 ≤ k) (f : CuspForm SL2ZRange (k : ℤ))
    {p : ℕ} [Fact p.Prime] {a_p α : ℂ}
    (heig : heckeCuspForm k (by omega) p (Fact.out : p.Prime).one_le f = a_p • f)
    (hα_ne : α ≠ 0) (hα_root : α ^ 2 - a_p * α + (p : ℂ) ^ (k - 1) = 0)
    (Ω : ℂ) (σ : ℤ_[p] →+ ℂ) (hσ : Function.Injective σ)
    (val : ∀ n : ℕ, ZMod (p ^ n) → ℤ_[p])
    (hval : ∀ n a, σ (val n a) = Ω⁻¹ * mttDist f p α n a) :
    PadicMeasure p where
  toFun := val
  compat n a := by
    apply hσ
    rw [hval n a, map_sum]
    simp_rw [hval (n + 1)]
    rw [← Finset.mul_sum, ← mttDist_compat hk f heig hα_ne hα_root n a]

end ModularSymbolsAndMTTDistribution

end

end RHDirect.Stage11ModularSymbols
