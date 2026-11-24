/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Arith4Ext.ZetaLFunctions — Dirichlet Series, Euler Products, Non-Vanishing, Complex Toolbox & Perron

Reusable, 100%-unconditional (`0` assumptions, `0` proxies, `0` `sorry`, `0` custom axioms)
Tier A analytic number theory & complex analysis library on targeted Mathlib imports
(`namespace Arith4Ext.ZetaLFunctions`):

1. **Dirichlet Series, Convolution & Euler Products (`Re s > 1`)**: Absolute convergence for
   bounded arithmetic sequences, Dirichlet convolution multiplicativity `L(f * g, s) = L(f, s) L(g, s)`,
   explicit Euler products for `ζ(s)` and `L(s, χ)`, `1 / ζ(s) = ∑ μ(n) n^{-s}`,
   `-ζ'(s) / ζ(s) = ∑ Λ(n) n^{-s}`, and `-L'(s, χ) / L(s, χ) = ∑ χ(n) Λ(n) n^{-s}`.
2. **Mertens `3 + 4 cos θ + cos 2θ ≥ 0` Non-Vanishing Core**: Elementary trigonometric positivity,
   Mertens inequality `1 ≤ ‖ζ(σ)‖^3 ‖ζ(σ + it)‖^4 ‖ζ(σ + 2it)‖` (`σ > 1`), general Dirichlet
   character Mertens inequality, non-vanishing on `Re s = 1` (`ζ(1 + it) ≠ 0`), and `L(1, χ) ≠ 0`
   for every non-principal character `χ`.
3. **Complex-Analytic Zero-Counting Toolbox**: Borel–Carathéodory Theorem (zero-at-origin and
   general forms via Schwarz Lemma / Cayley map), Hadamard Three-Circles Theorem (full closed
   annulus via rational-exponent Maximum Modulus Principle), and Jensen's Zero-Count Upper Bound
   (`∏_{ρ ∈ Z} (R / ‖ρ‖) * ‖f 0‖ ≤ M` and `|Z| ≤ log(M / ‖f 0‖) / log(R / r)` via Blaschke
   `dslope` induction + Maximum Modulus Principle).
4. **Effective Truncated Perron Formula**: Exact contour-shift bound
   `‖(1 / (2π)) ∫_{-T}^T y^{c + it} / (c + it) dt - 1_{y > 1}‖ ≤ y^c / (π T |log y|)` for `y ≠ 1`,
   exact `y = 1` evaluation `(1 / π) arctan(T / c)` with error `≤ c / (π T)`, and the full
   effective truncated Perron formula for arbitrary absolutely convergent Dirichlet series.
-/

open Real Complex Finset MeasureTheory intervalIntegral Filter Topology
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Arith4Ext.ZetaLFunctions

noncomputable section

/-! ## Section 1: Dirichlet Series, Convolution & Euler Products (`Re s > 1`) -/

/-- Absolute convergence of `LSeries f s` whenever `f` is bounded and `1 < s.re`. -/
theorem lseries_summable_of_bounded {f : ℕ → ℂ} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f s :=
  LSeriesSummable_of_bounded_of_one_lt_re (f := f) (fun n _ => hf n) hs

/-- Multiplicativity of Dirichlet series under Dirichlet convolution of arithmetic functions:
`L(f * g, s) = L(f, s) * L(g, s)` whenever both series converge absolutely at `s`. -/
theorem lseries_convolution_mul (f g : ArithmeticFunction ℂ) {s : ℂ}
    (hf : LSeriesSummable (fun n => f n) s) (hg : LSeriesSummable (fun n => g n) s) :
    LSeries (fun n => (f * g) n) s = LSeries (fun n => f n) s * LSeries (fun n => g n) s :=
  ArithmeticFunction.LSeries_mul' hf hg

/-- For `Re s > 1`, `L(1, s) = ζ(s)` where `1` is the constant-one arithmetic function. -/
theorem lseries_zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) s = riemannZeta s := by
  simpa using ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs

/-- **Euler Product for the Riemann Zeta Function (`Re s > 1`)**:
`∏'_p (1 - p^{-s})⁻¹ = ζ(s)`. -/
theorem riemannZeta_eulerProduct_tprod_eq {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-- **Euler Product for Dirichlet L-Functions (`Re s > 1`)**:
`∏'_p (1 - χ(p) p^{-s})⁻¹ = L(s, χ)`. -/
theorem dirichletLFunction_eulerProduct_tprod_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - χ p * ((p : ℕ) : ℂ) ^ (-s))⁻¹ = χ.LFunction s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_eulerProduct_tprod χ hs

/-- Absolute convergence of the Möbius Dirichlet series `∑ μ(n) n^{-s}` for `Re s > 1`. -/
theorem lseriesSummable_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
  refine lseries_summable_of_bounded (C := 1) (fun n => ?_) hs
  have h1 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  simpa [Complex.norm_intCast, Real.norm_eq_abs] using h1

/-- **Möbius–Zeta Dirichlet Series Identity (`Re s > 1`)**:
`L(μ, s) * ζ(s) = 1`. -/
theorem lseries_moebius_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s * riemannZeta s = 1 := by
  have hμ : LSeriesSummable (fun n => ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) n)) s := by
    simpa using lseriesSummable_moebius hs
  have hζ : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)) s := by
    simpa using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hmul := ArithmeticFunction.LSeries_mul' hμ hζ
  have hconv : (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) = 1 := by
    ext n
    simp [ArithmeticFunction.one_apply]
  rw [hconv] at hmul
  have h1 : LSeries (fun n => ((1 : ArithmeticFunction ℂ) n)) s = 1 := by
    unfold LSeries
    rw [tsum_eq_single 1]
    · simp [LSeries.term]
    · intro n hn
      by_cases hn0 : n = 0
      · simp [LSeries.term, hn0]
      · simp [LSeries.term_of_ne_zero hn0, ArithmeticFunction.one_apply, hn]
  rw [h1] at hmul
  have hζ_eq : LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)) s =
      riemannZeta s := by
    simpa using ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  rw [hζ_eq] at hmul
  simpa using hmul.symm

/-- **Reciprocal Riemann Zeta Dirichlet Series (`Re s > 1`)**:
`1 / ζ(s) = ∑ μ(n) n^{-s}`. -/
theorem inv_riemannZeta_eq_lseries_moebius {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hprod := lseries_moebius_mul_riemannZeta hs
  exact eq_inv_of_mul_eq_one_left hprod |>.symm

/-- Absolute convergence of the von Mangoldt Dirichlet series `∑ Λ(n) n^{-s}` for `Re s > 1`. -/
theorem lseriesSummable_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hlog : LSeriesSummable (LSeries.logMul (fun n => (ArithmeticFunction.zeta n : ℂ))) s := by
    have hζ_absc : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.zeta n : ℂ)) < s.re := by
      have hle : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.zeta n : ℂ)) ≤ 1 := by
        refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx => ?_
        have hx' : (1 : ℝ) < ((x : ℂ)).re := by simpa using hx
        simpa using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hx'
      exact lt_of_le_of_lt hle (by exact_mod_cast hs)
    exact LSeriesSummable_logMul_of_lt_re hζ_absc
  refine Summable.of_norm_bounded (hlog.norm) fun n => ?_
  by_cases hn0 : n = 0
  · simp [LSeries.term, hn0]
  · simp only [LSeries.term_of_ne_zero hn0, LSeries.logMul, ArithmeticFunction.zeta_apply, hn0,
      ↓reduceIte, Nat.cast_one, mul_one, norm_div]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    have hlog_eq : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [hlog_eq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hn0 : (1 : ℝ) ≤ n))]
    exact ArithmeticFunction.vonMangoldt_le_log

/-- **Logarithmic Derivative of the Riemann Zeta Function (`Re s > 1`)**:
`-ζ'(s) / ζ(s) = ∑ Λ(n) n^{-s}`. -/
theorem neg_deriv_riemannZeta_div_eq_lseries_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  -- Step 1: `-deriv riemannZeta s = LSeries (LSeries.logMul ζ) s`
  have hζ_absc : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.zeta n : ℂ)) < s.re := by
    have hle : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.zeta n : ℂ)) ≤ 1 := by
      refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx => ?_
      have hx' : (1 : ℝ) < ((x : ℂ)).re := by simpa using hx
      simpa using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hx'
    exact lt_of_le_of_lt hle (by exact_mod_cast hs)
  have hderiv_L : deriv (LSeries (fun n => (ArithmeticFunction.zeta n : ℂ))) s =
      -LSeries (LSeries.logMul (fun n => (ArithmeticFunction.zeta n : ℂ))) s :=
    LSeries_deriv hζ_absc
  have hderiv_eq : deriv riemannZeta s =
      deriv (LSeries (fun n => (ArithmeticFunction.zeta n : ℂ))) s := by
    refine Filter.EventuallyEq.deriv_eq ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact (lseries_zeta_eq_riemannZeta hz).symm
  -- Step 2: `Λ * ζ = log` as arithmetic functions into `ℂ`
  let lamC : ArithmeticFunction ℂ :=
    { toFun := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
      map_zero' := by simp }
  have hlam_s : LSeriesSummable (fun n => lamC n) s := lseriesSummable_vonMangoldt hs
  have hζ_s : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)) s := by
    simpa using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hmul := ArithmeticFunction.LSeries_mul' hlam_s hζ_s
  have hconv : ∀ n : ℕ, (lamC * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n =
      LSeries.logMul (fun k => (ArithmeticFunction.zeta k : ℂ)) n := by
    intro n
    by_cases hn0 : n = 0
    · simp [hn0, LSeries.logMul]
    · rw [ArithmeticFunction.mul_apply]
      have hreal : ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.vonMangoldt x.1 : ℝ) =
          Real.log (n : ℝ) := by
        rw [Nat.sum_divisorsAntidiagonal (f := fun a _ => ArithmeticFunction.vonMangoldt a)]
        exact ArithmeticFunction.vonMangoldt_sum
      have hsum : ∑ x ∈ n.divisorsAntidiagonal,
            lamC x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x.2 =
          ((∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.vonMangoldt x.1 : ℝ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hx2_ne : x.2 ≠ 0 :=
          right_ne_zero_of_mul (by rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]; exact hn0)
        simp [lamC, ArithmeticFunction.zeta_apply, hx2_ne]
      rw [hsum, hreal]
      simp [LSeries.logMul, ArithmeticFunction.zeta_apply, hn0]
  have hL_eq : LSeries (fun n => (lamC * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) s =
      LSeries (LSeries.logMul (fun k => (ArithmeticFunction.zeta k : ℂ))) s :=
    LSeries_congr (fun {n} _ => hconv n) s
  have hneg_L : LSeries (LSeries.logMul (fun k => (ArithmeticFunction.zeta k : ℂ))) s =
      -deriv (LSeries (fun n => (ArithmeticFunction.zeta n : ℂ))) s := by
    rw [hderiv_L, neg_neg]
  rw [hL_eq, hneg_L, ← hderiv_eq] at hmul
  have hζ_val : LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)) s =
      riemannZeta s := by
    simpa using ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  rw [hζ_val] at hmul
  -- `-deriv riemannZeta s = LSeries lamC s * riemannZeta s`
  rw [div_eq_iff hne]
  simpa [lamC] using hmul

/-- **Logarithmic Derivative of a Dirichlet L-Function (`Re s > 1`)**:
`-L'(s, χ) / L(s, χ) = ∑ χ(n) Λ(n) n^{-s}`. -/
theorem neg_deriv_dirichletLFunction_div_eq_lseries_vonMangoldt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    -deriv χ.LFunction s / χ.LFunction s =
      LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hne : χ.LFunction s ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  have hχ_absc : LSeries.abscissaOfAbsConv (fun n => χ n) < s.re := by
    have hle : LSeries.abscissaOfAbsConv (fun n => χ n) ≤ 1 := by
      refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx => ?_
      have hx' : (1 : ℝ) < ((x : ℂ)).re := by simpa using hx
      exact lseries_summable_of_bounded (C := 1) (fun n => DirichletCharacter.norm_le_one χ n) hx'
    exact lt_of_le_of_lt hle (by exact_mod_cast hs)
  have hderiv_L : deriv (LSeries (fun n => χ n)) s = -LSeries (LSeries.logMul (fun n => χ n)) s :=
    LSeries_deriv hχ_absc
  have hderiv_eq : deriv χ.LFunction s = deriv (LSeries (fun n => χ n)) s := by
    refine Filter.EventuallyEq.deriv_eq ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  let chiLam : ArithmeticFunction ℂ :=
    { toFun := fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
      map_zero' := by simp }
  let chiAF : ArithmeticFunction ℂ :=
    { toFun := fun n => if n = 0 then 0 else χ n
      map_zero' := rfl }
  have hchiLam_s : LSeriesSummable (fun n => chiLam n) s := by
    refine Summable.of_norm_bounded ((lseriesSummable_vonMangoldt hs).norm) fun n => ?_
    by_cases hn0 : n = 0
    · simp [LSeries.term, hn0]
    · simp only [LSeries.term_of_ne_zero hn0, chiLam, ArithmeticFunction.coe_mk, norm_div, norm_mul]
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖χ n‖ * ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖
          ≤ 1 * ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ n) (norm_nonneg _)
        _ = ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := one_mul _
  have hchiAF_s : LSeriesSummable (fun n => chiAF n) s := by
    refine lseries_summable_of_bounded (C := 1) (fun n => ?_) hs
    by_cases hn0 : n = 0
    · simp [chiAF, hn0]
    · simpa [chiAF, hn0] using DirichletCharacter.norm_le_one χ n
  have hmul := ArithmeticFunction.LSeries_mul' hchiLam_s hchiAF_s
  have hconv : ∀ n : ℕ, n ≠ 0 → (chiLam * chiAF) n = LSeries.logMul (fun k => χ k) n := by
    intro n hn0
    rw [ArithmeticFunction.mul_apply]
    have hsum : ∑ x ∈ n.divisorsAntidiagonal, chiLam x.1 * chiAF x.2 =
        χ n * ((∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.vonMangoldt x.1 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx2_ne : x.2 ≠ 0 :=
        right_ne_zero_of_mul (by rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]; exact hn0)
      have hprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
      simp only [chiLam, chiAF, ArithmeticFunction.coe_mk, hx2_ne, ↓reduceIte]
      have hχ_mul : χ x.1 * χ x.2 = χ n := by
        rw [← map_mul, ← Nat.cast_mul, hprod]
      calc χ x.1 * (ArithmeticFunction.vonMangoldt x.1 : ℂ) * χ x.2
          = (χ x.1 * χ x.2) * (ArithmeticFunction.vonMangoldt x.1 : ℂ) := by ring
        _ = χ n * (ArithmeticFunction.vonMangoldt x.1 : ℂ) := by rw [hχ_mul]
    have hreal : ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.vonMangoldt x.1 : ℝ) =
        Real.log (n : ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (f := fun a _ => ArithmeticFunction.vonMangoldt a)]
      exact ArithmeticFunction.vonMangoldt_sum
    rw [hsum, hreal]
    simp [LSeries.logMul, mul_comm]
  have hL_eq : LSeries (fun n => (chiLam * chiAF) n) s = LSeries (LSeries.logMul (fun k => χ k)) s :=
    LSeries_congr (fun {n} hn0 => hconv n hn0) s
  have hchiAF_L : LSeries (fun n => chiAF n) s = χ.LFunction s := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact LSeries_congr (fun {n} hn0 => by simp [chiAF, hn0]) s
  have hneg_L : LSeries (LSeries.logMul (fun k => χ k)) s =
      -deriv (LSeries (fun n => χ n)) s := by
    rw [hderiv_L, neg_neg]
  rw [hL_eq, hneg_L, ← hderiv_eq, hchiAF_L] at hmul
  rw [div_eq_iff hne]
  simpa [chiLam] using hmul

/-! ## Section 2: Mertens `3 + 4 cos θ + cos 2θ ≥ 0` Non-Vanishing Core -/

/-- **Mertens' Trigonometric Positivity Identity**:
`3 + 4 cos θ + cos(2θ) = 2 (1 + cos θ)^2 ≥ 0` for all `θ : ℝ`. -/
theorem mertens_trig_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have hcos : Real.cos (2 * θ) = 2 * (Real.cos θ) ^ 2 - 1 := Real.cos_two_mul θ
  rw [hcos]
  nlinarith [sq_nonneg (1 + Real.cos θ)]

/-- **Mertens' 3–4–1 Inequality for the Riemann Zeta Function (`σ > 1`)**:
`1 ≤ ‖ζ(σ)‖^3 * ‖ζ(σ + it)‖^4 * ‖ζ(σ + 2it)‖`. -/
theorem mertens_zeta_inequality {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 3 *
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 *
      ‖riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (χ := (1 : DirichletCharacter ℂ 1))
    (sub_pos.mpr hσ) t
  have hmod1 : ∀ z : ℂ, (1 : DirichletCharacter ℂ 1).LFunction z = riemannZeta z := fun z =>
    congr_fun DirichletCharacter.LFunction_modOne_eq z
  have h1sq : (1 : DirichletCharacter ℂ 1) ^ 2 = 1 := one_pow 2
  rw [h1sq] at h
  simp only [hmod1] at h
  have hs1 : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
  have hs2 : (σ : ℂ) + Complex.I * (t : ℂ) = (σ : ℂ) + (t : ℂ) * Complex.I := by ring
  have hs3 : (σ : ℂ) + 2 * Complex.I * (t : ℂ) =
      (σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hs1, hs2, hs3] at h
  simpa [norm_mul, norm_pow, mul_assoc] using h

/-- **General Mertens 3–4–1 Inequality for Dirichlet L-Functions (`σ > 1`)**:
`1 ≤ ‖L(σ, 1)‖^3 * ‖L(σ + it, χ)‖^4 * ‖L(σ + 2it, χ^2)‖`. -/
theorem mertens_dirichletLFunction_inequality {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖(1 : DirichletCharacter ℂ N).LFunction (σ : ℂ)‖ ^ 3 *
      ‖χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 *
      ‖(χ ^ 2).LFunction ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (χ := χ) (sub_pos.mpr hσ) t
  have hs1 : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
  have hs2 : (σ : ℂ) + Complex.I * (t : ℂ) = (σ : ℂ) + (t : ℂ) * Complex.I := by ring
  have hs3 : (σ : ℂ) + 2 * Complex.I * (t : ℂ) =
      (σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hs1, hs2, hs3] at h
  simpa [norm_mul, norm_pow, mul_assoc] using h

/-- **Non-Vanishing of `ζ(s)` on `Re s = 1`** (Hadamard–de la Vallée Poussin):
`ζ(1 + it) ≠ 0` for all `t : ℝ`. -/
theorem riemannZeta_ne_zero_on_re_one (t : ℝ) :
    riemannZeta (1 + (t : ℂ) * Complex.I) ≠ 0 := by
  have hre : (1 : ℝ) ≤ (1 + (t : ℂ) * Complex.I).re := by simp
  exact riemannZeta_ne_zero_of_one_le_re hre

/-- **Non-Vanishing of `L(1, χ)` for Non-Principal Dirichlet Characters**:
For every `χ ≠ 1`, `L(1, χ) ≠ 0`. -/
theorem dirichletLFunction_one_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    χ.LFunction 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

/-- **Non-Vanishing of `L(s, χ)` on `Re s ≥ 1`** (except at `s = 1` for principal `χ`):
For every `s` with `1 ≤ s.re` and `(s ≠ 1 ∨ χ ≠ 1)`, `L(s, χ) ≠ 0`. -/
theorem dirichletLFunction_ne_zero_of_one_le_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 ≤ s.re) (hne : s ≠ 1 ∨ χ ≠ 1) :
    χ.LFunction s ≠ 0 := by
  rcases hne with hs1 | hχ1
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hs

/-! ## Section 3: Complex-Analytic Zero-Counting Toolbox -/

/-! ### Borel–Carathéodory Theorem (via Schwarz Lemma / Cayley Map) -/

/-- **Borel–Carathéodory Theorem (Zero-at-Origin Form)**:
If `f` is analytic on `Metric.closedBall 0 R` (`0 < R`), `f 0 = 0`, and
`∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M` (`0 < M`), then for every `0 ≤ r < R` and `‖z‖ ≤ r`,
`‖f z‖ ≤ (2 * r / (R - r)) * M`. -/
theorem borel_caratheodory_zero {f : ℂ → ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr0 : 0 ≤ r) (hrR : r < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hf0 : f 0 = 0)
    (hre : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M) :
    ∀ z ∈ Metric.closedBall 0 r, ‖f z‖ ≤ (2 * r / (R - r)) * M := by
  intro z hz
  have hz_le : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hz_memR : z ∈ Metric.closedBall (0 : ℂ) R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz_le.trans hrR.le
  -- Cayley transform `φ(w) = f(w) / (2M - f(w))` maps `{Re ≤ M}` into the closed unit disk with `φ(0) = 0`.
  set φ : ℂ → ℂ := fun w => f w / (((2 * M : ℝ) : ℂ) - f w)
  have hden_ne : ∀ w ∈ Metric.closedBall (0 : ℂ) R, (((2 * M : ℝ) : ℂ) - f w) ≠ 0 := by
    intro w hw h0
    have hre0 := congr_arg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre0
    linarith [hre w hw]
  have hφ_le_one : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖φ w‖ ≤ 1 := by
    intro w hw
    dsimp [φ]
    rw [norm_div]
    refine (div_le_one (norm_pos_iff.mpr (hden_ne w hw))).mpr ?_
    have hsq : ‖f w‖ ^ 2 ≤ ‖(((2 * M : ℝ) : ℂ) - f w)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_sub,
        mul_neg, neg_mul, neg_neg]
      nlinarith [hre w hw]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hφ_an : AnalyticOnNhd ℂ φ (Metric.closedBall 0 R) :=
    fun w hw => (hf w hw).div (analyticAt_const.sub (hf w hw)) (hden_ne w hw)
  have hφ0 : φ 0 = 0 := by simp [φ, hf0]
  -- Schwarz quotient `ψ(w) = dslope φ 0 w` is analytic on `closedBall 0 R` with `‖ψ w‖ ≤ 1 / R` on `sphere 0 R`.
  set ψ : ℂ → ℂ := dslope φ 0
  have hψ_an : AnalyticOnNhd ℂ ψ (Metric.closedBall 0 R) := by
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      have hev := Complex.analyticAt_iff_eventually_differentiableAt.mp
        (hφ_an 0 (Metric.mem_closedBall_self hR.le))
      refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
      rcases eventually_nhds_iff.mp hev with ⟨U, hU_diff, hU_open, h0U⟩
      have hd : DifferentiableOn ℂ (dslope φ 0) U :=
        (Complex.differentiableOn_dslope (hU_open.mem_nhds h0U)).mpr
          (fun u hu => (hU_diff u hu).differentiableWithinAt)
      exact eventually_nhds_iff.mpr ⟨U, fun u hu => hd.differentiableAt (hU_open.mem_nhds hu),
        hU_open, h0U⟩
    · have hopen : IsOpen ({(0 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
      have heq : ψ =ᶠ[𝓝 w] fun u => (φ u - φ 0) / (u - 0) := by
        filter_upwards [hopen.mem_nhds hw0] with u hu
        rw [show ψ u = dslope φ 0 u from rfl, dslope_of_ne φ hu, slope_def_field]
      have hq : AnalyticAt ℂ (fun u => (φ u - φ 0) / (u - 0)) w :=
        ((hφ_an w hw).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr hw0)
      exact hq.congr heq.symm
  have hψ_diff : DiffContOnCl ℂ ψ (Metric.ball 0 R) :=
    ⟨fun w hw => (hψ_an w (Metric.ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt,
      by rw [closure_ball (0 : ℂ) hR.ne']
         exact fun w hw => (hψ_an w hw).continuousAt.continuousWithinAt⟩
  have hψ_bound : ‖ψ z‖ ≤ 1 / R := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := Metric.ball (0 : ℂ) R) (hU := Metric.isBounded_ball) (hd := hψ_diff)
      (hC := fun w hw => ?_)
      (hz := by rw [closure_ball (0 : ℂ) hR.ne']; exact hz_memR)
    rw [frontier_ball (0 : ℂ) hR.ne'] at hw
    have hw_norm : ‖w‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hw
    have hw_ne0 : w ≠ 0 := norm_pos_iff.mp (hw_norm.symm ▸ hR)
    have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R := Metric.sphere_subset_closedBall hw
    have hψw : ψ w = φ w / w := by
      dsimp [ψ]
      rw [dslope_of_ne φ hw_ne0, slope_def_field, hφ0, sub_zero, sub_zero]
    rw [hψw, norm_div, hw_norm]
    exact div_le_div_of_nonneg_right (hφ_le_one w hw_mem) hR.le
  have hφz_le : ‖φ z‖ ≤ r / R := by
    by_cases hz0 : z = 0
    · subst hz0
      rw [hφ0, norm_zero]
      exact div_nonneg hr0 hR.le
    · have hφz_eq : φ z = z * ψ z := by
        dsimp [ψ]
        rw [dslope_of_ne φ hz0, slope_def_field, hφ0, sub_zero, sub_zero, mul_div_cancel₀ _ hz0]
      rw [hφz_eq, norm_mul]
      calc ‖z‖ * ‖ψ z‖ ≤ r * (1 / R) :=
            mul_le_mul hz_le hψ_bound (norm_nonneg _) hr0
        _ = r / R := by ring
  -- Unwind `f z = φ z * (2M - f z)` to obtain `‖f z‖ ≤ (2r / (R - r)) * M`.
  have hf_eq : f z = φ z * (((2 * M : ℝ) : ℂ) - f z) := by
    dsimp [φ]
    exact (div_mul_cancel₀ (f z) (hden_ne z hz_memR)).symm
  have hnorm_sub : ‖(((2 * M : ℝ) : ℂ) - f z)‖ ≤ 2 * M + ‖f z‖ := by
    calc ‖(((2 * M : ℝ) : ℂ) - f z)‖
        ≤ ‖((2 * M : ℝ) : ℂ)‖ + ‖f z‖ := norm_sub_le _ _
      _ = 2 * M + ‖f z‖ := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hstep : ‖f z‖ ≤ (r / R) * (2 * M + ‖f z‖) := by
    calc ‖f z‖ = ‖φ z * (((2 * M : ℝ) : ℂ) - f z)‖ := congr_arg norm hf_eq
      _ = ‖φ z‖ * ‖(((2 * M : ℝ) : ℂ) - f z)‖ := norm_mul _ _
      _ ≤ (r / R) * (2 * M + ‖f z‖) :=
          mul_le_mul hφz_le hnorm_sub (norm_nonneg _) (div_nonneg hr0 hR.le)
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hstep2 : R * ‖f z‖ ≤ r * (2 * M + ‖f z‖) := by
    have hmul := mul_le_mul_of_nonneg_left hstep hR.le
    have hcancel : R * (r / R * (2 * M + ‖f z‖)) = r * (2 * M + ‖f z‖) := by
      field_simp [hR.ne']
    linarith
  have hstep3 : (R - r) * ‖f z‖ ≤ 2 * r * M := by nlinarith
  rw [show (2 * r / (R - r)) * M = (2 * r * M) / (R - r) by ring]
  exact (le_div_iff₀ hRr).mpr (by linarith)

/-- **Borel–Carathéodory Theorem (General Form)**:
If `f` is analytic on `Metric.closedBall 0 R` (`0 < R`) and
`∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M` (`0 ≤ M`), then for every `0 ≤ r < R` and `‖z‖ ≤ r`,
`‖f z‖ ≤ (2 * r / (R - r)) * M + ((R + r) / (R - r)) * ‖f 0‖`. -/
theorem borel_caratheodory {f : ℂ → ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr0 : 0 ≤ r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hre : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M) :
    ∀ z ∈ Metric.closedBall 0 r,
      ‖f z‖ ≤ (2 * r / (R - r)) * max M 0 + ((R + r) / (R - r)) * ‖f 0‖ := by
  intro z hz
  set M' : ℝ := max M 0
  have hM'_ge : M ≤ M' := le_max_left M 0
  have hM'_nn : 0 ≤ M' := le_max_right M 0
  have hre' : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M' := fun w hw => (hre w hw).trans hM'_ge
  -- Shift `g(w) = f(w) - f(0)` so `g 0 = 0` and `(g w).re ≤ M' - (f 0).re`
  set A : ℝ := M' - (f 0).re
  have hA_nn : 0 ≤ A := by
    have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := Metric.mem_closedBall_self hR.le
    linarith [hre' 0 h0mem]
  have hbound_eps : ∀ ε : ℝ, 0 < ε →
      ‖f z - f 0‖ ≤ (2 * r / (R - r)) * (A + ε) := by
    intro ε hε
    have hg_an : AnalyticOnNhd ℂ (fun w => f w - f 0) (Metric.closedBall 0 R) :=
      hf.sub analyticOnNhd_const
    have hg_re : ∀ w ∈ Metric.closedBall 0 R, (f w - f 0).re ≤ A + ε := fun w hw => by
      simp only [Complex.sub_re]
      linarith [hre' w hw]
    exact borel_caratheodory_zero hR hr0 hrR (by linarith) hg_an (sub_self _) hg_re z hz
  have hdiff : ‖f z - f 0‖ ≤ (2 * r / (R - r)) * A := by
    by_contra hgt
    push Not at hgt
    set δ : ℝ := ‖f z - f 0‖ - (2 * r / (R - r)) * A
    have hδ : 0 < δ := by linarith
    by_cases hr0' : r = 0
    · subst hr0'
      have hz0 : z = 0 := by simpa using hz
      subst hz0
      simp at hgt
    · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr0')
      have hc_pos : 0 < 2 * r / (R - r) := div_pos (by linarith) (by linarith)
      set ε : ℝ := δ / (2 * (2 * r / (R - r)))
      have hε : 0 < ε := div_pos hδ (by linarith)
      have hb := hbound_eps ε hε
      have hcalc : (2 * r / (R - r)) * (A + ε) = (2 * r / (R - r)) * A + δ / 2 := by
        have hRr : R - r ≠ 0 := by linarith
        dsimp [ε]
        field_simp [hRr, hr_pos.ne']
      linarith
  have hneg_re : -(f 0).re ≤ ‖f 0‖ := by
    have := Complex.abs_re_le_norm (f 0)
    linarith [neg_le_abs (f 0).re]
  have htri : ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := by
    calc ‖f z‖ = ‖(f z - f 0) + f 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_add_le _ _
  have hcoeff : 2 * r / (R - r) + 1 = (R + r) / (R - r) := by
    have hne : R - r ≠ 0 := by linarith
    field_simp [hne]
    ring
  have hnonneg_c : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) (by linarith)
  have hA_le : A ≤ M' + ‖f 0‖ := by dsimp [A]; linarith
  calc ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := htri
    _ ≤ (2 * r / (R - r)) * A + ‖f 0‖ := by linarith
    _ ≤ (2 * r / (R - r)) * (M' + ‖f 0‖) + ‖f 0‖ := by nlinarith
    _ = (2 * r / (R - r)) * M' + (2 * r / (R - r) + 1) * ‖f 0‖ := by ring
    _ = (2 * r / (R - r)) * M' + ((R + r) / (R - r)) * ‖f 0‖ := by rw [hcoeff]

/-! ### Hadamard Three-Circles Theorem (Full Closed Annulus) -/

/-- **Hadamard Three-Circles Theorem**:
Let `0 < r₁ < r < r₂`, let `f : ℂ → ℂ` be continuous on the closed annulus
`A = {z | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂}` and differentiable on the open annulus
`{z | r₁ < ‖z‖ ∧ ‖z‖ < r₂}`, with boundary bounds `‖f z‖ ≤ M₁` on `‖z‖ = r₁`
and `‖f z‖ ≤ M₂` on `‖z‖ = r₂` (`0 < M₁`, `0 < M₂`). Then for every `z` with `‖z‖ = r`:
`‖f z‖ ^ log(r₂ / r₁) ≤ M₁ ^ log(r₂ / r) * M₂ ^ log(r / r₁)`. -/
theorem hadamard_three_circles {f : ℂ → ℂ} {r₁ r r₂ M₁ M₂ : ℝ}
    (hr1 : 0 < r₁) (h1r : r₁ < r) (hr2 : r < r₂) (hM1 : 0 < M₁) (hM2 : 0 < M₂)
    (hcont : ContinuousOn f {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂})
    (hdiff : DifferentiableOn ℂ f {z : ℂ | r₁ < ‖z‖ ∧ ‖z‖ < r₂})
    (hb1 : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ M₁)
    (hb2 : ∀ z : ℂ, ‖z‖ = r₂ → ‖f z‖ ≤ M₂) :
    ∀ z : ℂ, ‖z‖ = r →
      ‖f z‖ ^ Real.log (r₂ / r₁) ≤ M₁ ^ Real.log (r₂ / r) * M₂ ^ Real.log (r / r₁) := by
  intro z hz
  have hr_pos : 0 < r := hr1.trans h1r
  have hr2_pos : 0 < r₂ := hr_pos.trans hr2
  have hlog_pos : 0 < Real.log (r₂ / r₁) := Real.log_pos ((one_lt_div hr1).mpr (h1r.trans hr2))
  by_cases hfz0 : ‖f z‖ = 0
  · rw [hfz0, Real.zero_rpow hlog_pos.ne']
    positivity
  have hfz_pos : 0 < ‖f z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfz0)
  -- Closed annulus `K` and open annulus `U`
  set K : Set ℂ := {w : ℂ | r₁ ≤ ‖w‖ ∧ ‖w‖ ≤ r₂}
  set U : Set ℂ := {w : ℂ | r₁ < ‖w‖ ∧ ‖w‖ < r₂}
  have hK_closed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hK_bdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r₂)).subset fun w hw => ?_
    simpa [Metric.mem_closedBall, dist_zero_right] using hw.2
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hU_sub_K : U ⊆ K := fun w hw => ⟨hw.1.le, hw.2.le⟩
  have hU_sub_int : U ⊆ interior K := interior_maximal hU_sub_K hU_open
  have hfront : frontier K ⊆ {w : ℂ | ‖w‖ = r₁ ∨ ‖w‖ = r₂} := by
    intro w hw
    have hwK : w ∈ K := hK_closed.closure_eq ▸ hw.1
    have hnotU : w ∉ U := fun h => hw.2 (hU_sub_int h)
    simp only [U, Set.mem_ofPred_eq, not_and_or, not_lt] at hnotU
    rcases hnotU with hle1 | hge2
    · exact Or.inl (le_antisymm hle1 hwK.1)
    · exact Or.inr (le_antisymm hwK.2 hge2)
  have hdiff_int : ∀ {g : ℂ → ℂ},
      ContinuousOn g K → DifferentiableOn ℂ g U →
      DiffContOnCl ℂ g U := by
    intro g hg_cont hg_diff
    have hcl_sub : closure U ⊆ K := hK_closed.closure_subset_iff.mpr hU_sub_K
    exact ⟨hg_diff, hg_cont.mono hcl_sub⟩
  -- Key rational-exponent bound via Maximum Modulus Principle on `w ↦ w^p * (f w)^q`
  have hrat : ∀ (p : ℤ) (q : ℕ), 1 ≤ q →
      (p : ℝ) * Real.log r + (q : ℝ) * Real.log ‖f z‖ ≤
        max ((p : ℝ) * Real.log r₁ + (q : ℝ) * Real.log M₁)
            ((p : ℝ) * Real.log r₂ + (q : ℝ) * Real.log M₂) := by
    intro p q hq
    set g : ℂ → ℂ := fun w => w ^ p * (f w) ^ q
    have hg_cont : ContinuousOn g K := by
      refine ContinuousOn.mul ?_ (hcont.pow q)
      refine continuousOn_id.zpow₀ p fun w hw => Or.inl ?_
      have : 0 < ‖w‖ := lt_of_lt_of_le hr1 hw.1
      exact norm_pos_iff.mp this
    have hg_diff : DifferentiableOn ℂ g U := by
      refine DifferentiableOn.mul ?_ (hdiff.pow q)
      intro w hw
      have hw0 : w ≠ 0 := norm_pos_iff.mp (hr1.trans hw.1)
      exact ((differentiableAt_zpow (m := p) (x := w)).mpr (Or.inl hw0)).differentiableWithinAt
    set B : ℝ := max (r₁ ^ p * M₁ ^ q) (r₂ ^ p * M₂ ^ q)
    have hmax : ‖g z‖ ≤ B := Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := U) (C := B) (hU := hK_bdd.subset hU_sub_K) (hd := hdiff_int hg_cont hg_diff)
      (hC := fun w hw => by
        have hfrontU : frontier U ⊆ frontier K := by
          intro x hx
          have hxK : x ∈ K := (hK_closed.closure_subset_iff.mpr hU_sub_K) hx.1
          have hxnotU : x ∉ U := by
            have h2 := hx.2
            rwa [hU_open.interior_eq] at h2
          have hnot_int : x ∉ interior K := by
            intro hint
            have hxU : x ∈ U := by
              -- Any interior point of `K` has `r₁ < ‖x‖ < r₂`!
              rcases Metric.isOpen_iff.mp isOpen_interior x hint with ⟨ε, hε, hball⟩
              have hx_ne : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr1 hxK.1)
              have h1 : r₁ < ‖x‖ := by
                by_contra hle
                have heq : ‖x‖ = r₁ := le_antisymm (not_lt.mp hle) hxK.1
                set t : ℝ := max (1 / 2) (1 - ε / (2 * r₁))
                have ht_lt1 : t < 1 := max_lt (by norm_num) (by
                  have : 0 < ε / (2 * r₁) := by positivity
                  linarith)
                have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
                set y : ℂ := (t : ℂ) * x
                have hdist : dist y x < ε := by
                  rw [dist_eq_norm]
                  have hsub : y - x = ((t - 1 : ℝ) : ℂ) * x := by dsimp [y]; push_cast; ring
                  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), heq]
                  have ht_ge : 1 - ε / (2 * r₁) ≤ t := le_max_right _ _
                  have : (1 - t) * r₁ ≤ ε / 2 := by
                    have h1' : 1 - t ≤ ε / (2 * r₁) := by linarith
                    have h2' := mul_le_mul_of_nonneg_right h1' hr1.le
                    have h3' : ε / (2 * r₁) * r₁ = ε / 2 := by field_simp [hr1.ne']
                    linarith
                  linarith
                have hyK : y ∈ K := interior_subset (hball hdist)
                have hynorm : ‖y‖ = t * r₁ := by
                  dsimp [y]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos, heq]
                have := hyK.1
                nlinarith
              have h2 : ‖x‖ < r₂ := by
                by_contra hge
                have heq : ‖x‖ = r₂ := le_antisymm hxK.2 (not_lt.mp hge)
                set t : ℝ := 1 + ε / (2 * r₂)
                have ht_gt1 : 1 < t := by
                  dsimp [t]
                  have : 0 < ε / (2 * r₂) := by positivity
                  linarith
                set y : ℂ := (t : ℂ) * x
                have hdist : dist y x < ε := by
                  rw [dist_eq_norm]
                  have hsub : y - x = ((t - 1 : ℝ) : ℂ) * x := by dsimp [y]; push_cast; ring
                  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), heq]
                  have hcalc : (t - 1) * r₂ = ε / 2 := by dsimp [t]; field_simp [hr2_pos.ne']; ring
                  linarith
                have hyK : y ∈ K := interior_subset (hball hdist)
                have hynorm : ‖y‖ = t * r₂ := by
                  dsimp [y]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), heq]
                have := hyK.2
                nlinarith
              exact ⟨h1, h2⟩
            exact hxnotU hxU
          exact ⟨subset_closure hxK, hnot_int⟩
        rcases hfront (hfrontU hw) with hw1 | hw2
        · refine le_trans ?_ (le_max_left _ _)
          dsimp [g]
          rw [norm_mul, norm_zpow, norm_pow, hw1]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb1 w hw1) q)
            (zpow_nonneg hr1.le p)
        · refine le_trans ?_ (le_max_right _ _)
          dsimp [g]
          rw [norm_mul, norm_zpow, norm_pow, hw2]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb2 w hw2) q)
            (zpow_nonneg hr2_pos.le p))
      (hz := subset_closure (show z ∈ U from ⟨hz ▸ h1r, hz ▸ hr2⟩))
    have hgz : ‖g z‖ = r ^ p * ‖f z‖ ^ q := by
      dsimp [g]; rw [norm_mul, norm_zpow, norm_pow, hz]
    rw [hgz] at hmax
    have hpos_lhs : 0 < r ^ p * ‖f z‖ ^ q := mul_pos (zpow_pos hr_pos p) (pow_pos hfz_pos q)
    have hlog := Real.log_le_log hpos_lhs hmax
    have hlhs_log : Real.log (r ^ p * ‖f z‖ ^ q) = (p : ℝ) * Real.log r + (q : ℝ) * Real.log ‖f z‖ := by
      rw [Real.log_mul (zpow_pos hr_pos p).ne' (pow_pos hfz_pos q).ne', Real.log_zpow, Real.log_pow]
    rw [hlhs_log] at hlog
    refine hlog.trans ?_
    have hmax_log : Real.log (max (r₁ ^ p * M₁ ^ q) (r₂ ^ p * M₂ ^ q)) =
        max (Real.log (r₁ ^ p * M₁ ^ q)) (Real.log (r₂ ^ p * M₂ ^ q)) := by
      by_cases hle : r₁ ^ p * M₁ ^ q ≤ r₂ ^ p * M₂ ^ q
      · rw [max_eq_right hle, max_eq_right (Real.log_le_log (mul_pos (zpow_pos hr1 p) (pow_pos hM1 q)) hle)]
      · have hlt := lt_of_not_ge hle
        rw [max_eq_left hlt.le, max_eq_left (Real.log_le_log (mul_pos (zpow_pos hr2_pos p) (pow_pos hM2 q)) hlt.le)]
    rw [hmax_log,
      Real.log_mul (zpow_pos hr1 p).ne' (pow_pos hM1 q).ne', Real.log_zpow, Real.log_pow,
      Real.log_mul (zpow_pos hr2_pos p).ne' (pow_pos hM2 q).ne', Real.log_zpow, Real.log_pow]
  -- Extend from `α ∈ ℚ` to all `α : ℝ` by continuity & density of `ℚ` in `ℝ`
  have hreal_alpha : ∀ α : ℝ,
      α * Real.log r + Real.log ‖f z‖ ≤
        max (α * Real.log r₁ + Real.log M₁) (α * Real.log r₂ + Real.log M₂) := by
    intro α
    have hrat_q : ∀ q : ℚ,
        (q : ℝ) * Real.log r + Real.log ‖f z‖ ≤
          max ((q : ℝ) * Real.log r₁ + Real.log M₁) ((q : ℝ) * Real.log r₂ + Real.log M₂) := by
      intro q
      have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
      have h0 := hrat q.num q.den q.pos
      have hdiv := div_le_div_of_nonneg_right h0 hden_pos.le
      have hq_eq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := q.cast_def
      rw [hq_eq]
      have hL : ((q.num : ℝ) * Real.log r + (q.den : ℝ) * Real.log ‖f z‖) / (q.den : ℝ) =
          (q.num : ℝ) / (q.den : ℝ) * Real.log r + Real.log ‖f z‖ := by
        field_simp [hden_pos.ne']
      have hR : max ((q.num : ℝ) * Real.log r₁ + (q.den : ℝ) * Real.log M₁)
            ((q.num : ℝ) * Real.log r₂ + (q.den : ℝ) * Real.log M₂) / (q.den : ℝ) =
          max ((q.num : ℝ) / (q.den : ℝ) * Real.log r₁ + Real.log M₁)
            ((q.num : ℝ) / (q.den : ℝ) * Real.log r₂ + Real.log M₂) := by
        have hmd : ∀ u v : ℝ, max u v / (q.den : ℝ) = max (u / (q.den : ℝ)) (v / (q.den : ℝ)) := by
          intro u v
          by_cases huv : u ≤ v
          · rw [max_eq_right huv, max_eq_right (div_le_div_of_nonneg_right huv hden_pos.le)]
          · have hlt := lt_of_not_ge huv
            rw [max_eq_left hlt.le, max_eq_left (div_le_div_of_nonneg_right hlt.le hden_pos.le)]
        rw [hmd]
        congr 1 <;> field_simp [hden_pos.ne']
      rwa [hL, hR] at hdiv
    -- Use density of `ℚ` in `ℝ` (`Rat.denseRange_cast`):
    have hcontL : Continuous (fun x : ℝ => x * Real.log r + Real.log ‖f z‖) := by fun_prop
    have hcontR : Continuous (fun x : ℝ =>
        max (x * Real.log r₁ + Real.log M₁) (x * Real.log r₂ + Real.log M₂)) :=
      (by fun_prop : Continuous fun x : ℝ => x * Real.log r₁ + Real.log M₁).max
        (by fun_prop : Continuous fun x : ℝ => x * Real.log r₂ + Real.log M₂)
    have hclosed : IsClosed {x : ℝ | x * Real.log r + Real.log ‖f z‖ ≤
        max (x * Real.log r₁ + Real.log M₁) (x * Real.log r₂ + Real.log M₂)} :=
      isClosed_le hcontL hcontR
    have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | x * Real.log r + Real.log ‖f z‖ ≤
        max (x * Real.log r₁ + Real.log M₁) (x * Real.log r₂ + Real.log M₂)} := by
      rintro _ ⟨q, rfl⟩; exact hrat_q q
    have huniv : {x : ℝ | x * Real.log r + Real.log ‖f z‖ ≤
        max (x * Real.log r₁ + Real.log M₁) (x * Real.log r₂ + Real.log M₂)} = Set.univ := by
      rw [← Set.univ_subset_iff, ← Rat.denseRange_cast.closure_eq]
      exact hclosed.closure_subset_iff.mpr hsub
    have hmem : α ∈ Set.univ := Set.mem_univ α
    rw [← huniv] at hmem
    exact hmem
  -- Plug in `α := -(log M₂ - log M₁) / log (r₂ / r₁)` where both branches of `max` agree!
  set α : ℝ := -(Real.log M₂ - Real.log M₁) / Real.log (r₂ / r₁)
  have hα := hreal_alpha α
  have hlog_div : Real.log (r₂ / r₁) = Real.log r₂ - Real.log r₁ := Real.log_div hr2_pos.ne' hr1.ne'
  have hbranch_eq : α * Real.log r₁ + Real.log M₁ = α * Real.log r₂ + Real.log M₂ := by
    dsimp [α]; rw [hlog_div]
    have hne : Real.log r₂ - Real.log r₁ ≠ 0 := by linarith [hlog_pos, hlog_div]
    field_simp [hne]; ring
  rw [hbranch_eq, max_self] at hα
  -- Multiply by `log (r₂ / r₁) > 0` and exponentiate!
  have hlog_ineq : Real.log ‖f z‖ * Real.log (r₂ / r₁) ≤
      Real.log M₁ * Real.log (r₂ / r) + Real.log M₂ * Real.log (r / r₁) := by
    have h1 := mul_le_mul_of_nonneg_right hα hlog_pos.le
    have hα_mul : α * Real.log (r₂ / r₁) = -(Real.log M₂ - Real.log M₁) := by
      dsimp [α]; exact div_mul_cancel₀ _ hlog_pos.ne'
    have hdiv1 : Real.log (r₂ / r) = Real.log r₂ - Real.log r := Real.log_div hr2_pos.ne' hr_pos.ne'
    have hdiv2 : Real.log (r / r₁) = Real.log r - Real.log r₁ := Real.log_div hr_pos.ne' hr1.ne'
    have hL : (α * Real.log r + Real.log ‖f z‖) * Real.log (r₂ / r₁) =
        -(Real.log M₂ - Real.log M₁) * Real.log r + Real.log ‖f z‖ * Real.log (r₂ / r₁) := by
      calc (α * Real.log r + Real.log ‖f z‖) * Real.log (r₂ / r₁)
          = (α * Real.log (r₂ / r₁)) * Real.log r + Real.log ‖f z‖ * Real.log (r₂ / r₁) := by ring
        _ = -(Real.log M₂ - Real.log M₁) * Real.log r + Real.log ‖f z‖ * Real.log (r₂ / r₁) := by
            rw [hα_mul]
    have hR : (α * Real.log r₂ + Real.log M₂) * Real.log (r₂ / r₁) =
        -(Real.log M₂ - Real.log M₁) * Real.log r₂ + Real.log M₂ * (Real.log r₂ - Real.log r₁) := by
      calc (α * Real.log r₂ + Real.log M₂) * Real.log (r₂ / r₁)
          = (α * Real.log (r₂ / r₁)) * Real.log r₂ + Real.log M₂ * Real.log (r₂ / r₁) := by ring
        _ = -(Real.log M₂ - Real.log M₁) * Real.log r₂ + Real.log M₂ * (Real.log r₂ - Real.log r₁) := by
            rw [hα_mul, hlog_div]
    rw [hL, hR] at h1
    rw [hdiv1, hdiv2]
    linarith
  have hexp := Real.exp_le_exp.mpr hlog_ineq
  rw [Real.exp_add] at hexp
  have h1 : Real.exp (Real.log ‖f z‖ * Real.log (r₂ / r₁)) = ‖f z‖ ^ Real.log (r₂ / r₁) :=
    (Real.rpow_def_of_pos hfz_pos _).symm
  have h2 : Real.exp (Real.log M₁ * Real.log (r₂ / r)) = M₁ ^ Real.log (r₂ / r) :=
    (Real.rpow_def_of_pos hM1 _).symm
  have h3 : Real.exp (Real.log M₂ * Real.log (r / r₁)) = M₂ ^ Real.log (r / r₁) :=
    (Real.rpow_def_of_pos hM2 _).symm
  rwa [h1, h2, h3] at hexp

/-! ### Jensen's Zero-Count Upper Bound (via Blaschke `dslope` Induction & Maximum Modulus) -/

/-- **Blaschke-Jensen Product Bound for Zeros in a Disk**:
If `f` is analytic on `Metric.closedBall 0 R` (`0 < R`), `f 0 ≠ 0`, `∀ z ∈ closedBall 0 R, ‖f z‖ ≤ M`,
and `Z : Finset ℂ` is a finite set of distinct zeros of `f` strictly inside `Metric.ball 0 R`, then
`(∏ ρ ∈ Z, R / ‖ρ‖) * ‖f 0‖ ≤ M`. -/
theorem jensen_blaschke_product_bound {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hf0 : f 0 ≠ 0)
    (hM : ∀ z ∈ Metric.closedBall 0 R, ‖f z‖ ≤ M)
    (Z : Finset ℂ) (hZ_ball : ∀ ρ ∈ Z, ‖ρ‖ < R) (hZ_zero : ∀ ρ ∈ Z, f ρ = 0) :
    (∏ ρ ∈ Z, R / ‖ρ‖) * ‖f 0‖ ≤ M := by
  -- Induct on `Z`, dividing out each Blaschke factor `R * (z - ρ) / (R^2 - star ρ * z)` via `dslope`!
  have hind : ∀ S : Finset ℂ, ∀ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.closedBall 0 R) →
      g 0 ≠ 0 →
      (∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g z‖ ≤ M) →
      (∀ ρ ∈ S, ‖ρ‖ < R) →
      (∀ ρ ∈ S, g ρ = 0) →
      (∏ ρ ∈ S, R / ‖ρ‖) * ‖g 0‖ ≤ M := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty =>
      intro g hg _ hgs _ _
      simp only [Finset.prod_empty, one_mul]
      have hdiff : DiffContOnCl ℂ g (Metric.ball 0 R) :=
        ⟨fun z hz => (hg z (Metric.ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt,
          by rw [closure_ball (0 : ℂ) hR.ne']
             exact fun z hz => (hg z hz).continuousAt.continuousWithinAt⟩
      have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
        (U := Metric.ball (0 : ℂ) R) (hU := Metric.isBounded_ball) (hd := hdiff)
        (hC := fun z hz => hgs z (by rwa [frontier_ball (0 : ℂ) hR.ne'] at hz))
        (hz := by rw [closure_ball (0 : ℂ) hR.ne']; exact Metric.mem_closedBall_self hR.le)
      exact hmax
    | @insert ρ s hρ_not ih =>
      intro g hg hg0 hgs hS_ball hS_zero
      have hρ_lt : ‖ρ‖ < R := hS_ball ρ (Finset.mem_insert_self ρ s)
      have hρ_zero : g ρ = 0 := hS_zero ρ (Finset.mem_insert_self ρ s)
      have hρ_ne0 : ρ ≠ 0 := fun h => hg0 (h ▸ hρ_zero)
      have hρ_norm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne0
      -- Define Blaschke-divided function `g₁(z) = ((R^2 - star ρ * z) / R) * dslope g ρ z`
      set g₁ : ℂ → ℂ := fun z => (((R : ℂ) ^ 2 - star ρ * z) / (R : ℂ)) * dslope g ρ z
      have hg₁_an : AnalyticOnNhd ℂ g₁ (Metric.closedBall 0 R) := by
        intro z hz
        have hpoly : AnalyticAt ℂ (fun w : ℂ => ((R : ℂ) ^ 2 - star ρ * w) / (R : ℂ)) z :=
          (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div analyticAt_const
            (Complex.ofReal_ne_zero.mpr hR.ne')
        have hdslope : AnalyticAt ℂ (dslope g ρ) z := by
          have hρ_mem : ρ ∈ Metric.closedBall (0 : ℂ) R := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hρ_lt.le
          by_cases hzρ : z = ρ
          · subst hzρ
            exact (Complex.analyticAt_iff_eventually_differentiableAt.mp (hg z hρ_mem)) |> fun hev =>
              Complex.analyticAt_iff_eventually_differentiableAt.mpr
                (by
                  rcases eventually_nhds_iff.mp hev with ⟨U, hU_diff, hU_open, hzU⟩
                  have hd : DifferentiableOn ℂ (dslope g z) U :=
                    (Complex.differentiableOn_dslope (hU_open.mem_nhds hzU)).mpr
                      (fun w hw => (hU_diff w hw).differentiableWithinAt)
                  exact eventually_nhds_iff.mpr ⟨U, fun w hw => hd.differentiableAt (hU_open.mem_nhds hw),
                    hU_open, hzU⟩)
          · have hopen : IsOpen ({ρ}ᶜ : Set ℂ) := isOpen_compl_singleton
            have heq : dslope g ρ =ᶠ[𝓝 z] fun w => (g w - g ρ) / (w - ρ) := by
              filter_upwards [hopen.mem_nhds hzρ] with w hw
              rw [dslope_of_ne g hw, slope_def_field]
            have hq : AnalyticAt ℂ (fun w => (g w - g ρ) / (w - ρ)) z :=
              ((hg z hz).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
                (sub_ne_zero.mpr hzρ)
            exact hq.congr heq.symm
        exact hpoly.mul hdslope
      have hg₁_val_ne : ∀ z : ℂ, z ≠ ρ →
          g₁ z = (((R : ℂ) ^ 2 - star ρ * z) / ((R : ℂ) * (z - ρ))) * g z := by
        intro z hzρ
        dsimp [g₁]
        rw [dslope_of_ne g hzρ, slope_def_field, hρ_zero, sub_zero]
        have hR_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
        have hz_ne : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
        field_simp [hR_ne, hz_ne]
      have hg₁_0 : ‖g₁ 0‖ = (R / ‖ρ‖) * ‖g 0‖ := by
        rw [hg₁_val_ne 0 hρ_ne0.symm, norm_mul, mul_zero, sub_zero, zero_sub, norm_div,
          norm_pow, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
        have hR_ne : R ≠ 0 := hR.ne'
        field_simp [hR_ne, hρ_norm_pos.ne']
      have hg₁_0_ne : g₁ 0 ≠ 0 := by
        rw [← norm_pos_iff, hg₁_0]
        exact mul_pos (div_pos hR hρ_norm_pos) (norm_pos_iff.mpr hg0)
      have hg₁_sphere : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g₁ z‖ ≤ M := by
        intro z hz
        have hz_norm : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
        have hzρ : z ≠ ρ := fun h => by rw [h] at hz_norm; linarith
        rw [hg₁_val_ne z hzρ, norm_mul, norm_div]
        -- On `‖z‖ = R`: `‖R^2 - star ρ * z‖ = ‖z * star z - star ρ * z‖ = R * ‖z - ρ‖`!
        have hbl : ‖(R : ℂ) ^ 2 - star ρ * z‖ = ‖(R : ℂ) * (z - ρ)‖ := by
          have hR2 : ((R : ℂ) ^ 2) = z * star z := by
            have := Complex.mul_conj' z
            rw [hz_norm] at this
            simpa [Complex.ofReal_pow] using this.symm
          have hfac : (R : ℂ) ^ 2 - star ρ * z = z * star (z - ρ) := by
            rw [hR2, star_sub]; ring
          rw [hfac, norm_mul, norm_star, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hR, hz_norm]
        have hden_ne : ‖(R : ℂ) * (z - ρ)‖ ≠ 0 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
          exact mul_ne_zero hR.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzρ))
        rw [hbl, div_self hden_ne, one_mul]
        exact hgs z hz
      have hg₁_zeros : ∀ w ∈ s, g₁ w = 0 := by
        intro w hw
        have hwρ : w ≠ ρ := fun h => hρ_not (h ▸ hw)
        rw [hg₁_val_ne w hwρ, hS_zero w (Finset.mem_insert_of_mem hw), mul_zero]
      have hrec := ih g₁ hg₁_an hg₁_0_ne hg₁_sphere
        (fun w hw => hS_ball w (Finset.mem_insert_of_mem hw)) hg₁_zeros
      rw [hg₁_0] at hrec
      rw [Finset.prod_insert hρ_not]
      linarith [show (∏ x ∈ s, R / ‖x‖) * (R / ‖ρ‖ * ‖g 0‖) =
        (R / ‖ρ‖ * ∏ x ∈ s, R / ‖x‖) * ‖g 0‖ by ring]
  exact hind Z f hf hf0
    (fun z hz => hM z (Metric.sphere_subset_closedBall hz)) hZ_ball hZ_zero

/-- **Jensen's Zero-Count Upper Bound on Disks**:
If `f` is analytic on `Metric.closedBall 0 R` (`0 < r < R`), `f 0 ≠ 0`,
`∀ z ∈ Metric.closedBall 0 R, ‖f z‖ ≤ M` (`0 < M`), and `Z : Finset ℂ` is any finite set of
distinct zeros of `f` in `Metric.closedBall 0 r`, then:
`(Z.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log (R / r)`. -/
theorem jensen_zero_count_bound {f : ℂ → ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hf0 : f 0 ≠ 0)
    (hM : ∀ z ∈ Metric.closedBall 0 R, ‖f z‖ ≤ M)
    (Z : Finset ℂ) (hZ_ball : ∀ ρ ∈ Z, ‖ρ‖ ≤ r) (hZ_zero : ∀ ρ ∈ Z, f ρ = 0) :
    (Z.card : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hf0_pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hM_ge : ‖f 0‖ ≤ M := hM 0 (Metric.mem_closedBall_self hR.le)
  have hM_pos : 0 < M := lt_of_lt_of_le hf0_pos hM_ge
  have hprod := jensen_blaschke_product_bound hR hf hf0 hM Z
    (fun ρ hρ => (hZ_ball ρ hρ).trans_lt hrR) hZ_zero
  have hpow_le : (R / r) ^ Z.card ≤ ∏ ρ ∈ Z, R / ‖ρ‖ := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => div_nonneg hR.le hr.le) fun ρ hρ => ?_
    have hρ_ne : ρ ≠ 0 := fun h => hf0 (h ▸ hZ_zero ρ hρ)
    exact div_le_div_of_nonneg_left hR.le (norm_pos_iff.mpr hρ_ne) (hZ_ball ρ hρ)
  have hle : (R / r) ^ Z.card ≤ M / ‖f 0‖ := by
    rw [le_div_iff₀ hf0_pos]
    exact (mul_le_mul_of_nonneg_right hpow_le hf0_pos.le).trans hprod
  have hlog_pos : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hlog := Real.log_le_log (pow_pos (div_pos hR hr) Z.card) hle
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ hlog_pos).mpr hlog

/-! ## Section 4: Effective Truncated Perron Formula -/

/-- The truncated Perron vertical-line integral kernel:
`P(y; c, T) = (1 / (2π i)) ∫_{c - iT}^{c + iT} (y^s / s) ds = (1 / (2π)) ∫_{-T}^T y^{c + it} / (c + it) dt`. -/
def perronKernel (y c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in (-T)..T, ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) / ((c : ℂ) + (t : ℂ) * Complex.I)

private lemma cpow_of_pos_eq_exp {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (y : ℂ) ^ s = Complex.exp (s * (Real.log y : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.ofReal_log hy.le,
    mul_comm]

private lemma norm_exp_mul_log {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖Complex.exp (s * (Real.log y : ℂ))‖ = y ^ s.re := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Real.rpow_def_of_pos hy, mul_comm]

private lemma integral_inv_add_mul_I_vertical {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    (∫ t in (-T)..T, ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) = ((2 * Real.arctan (T / a) : ℝ) : ℂ) := by
  have hre : ∀ t : ℝ, (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
      ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ) - Complex.I * ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    intro t
    have hden : (a ^ 2 + t ^ 2 : ℝ) ≠ 0 := by
      have : 0 < a ^ 2 + t ^ 2 := by positivity
      exact this.ne'
    have hdenC : ((a : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have := congr_arg Complex.re h0
      simp at this
      exact ha this
    rw [inv_eq_one_div, div_eq_iff hdenC]
    push_cast
    have hdenC2 : ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hden
    field_simp [hdenC2]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    calc (a : ℂ) ^ 2 + (t : ℂ) ^ 2
        = ((a : ℂ) - Complex.I * (t : ℂ)) * ((a : ℂ) + (t : ℂ) * Complex.I) +
            (t : ℂ) ^ 2 * (Complex.I ^ 2 + 1) := by ring
      _ = ((a : ℂ) - Complex.I * (t : ℂ)) * ((a : ℂ) + (t : ℂ) * Complex.I) := by rw [hI2]; ring
      _ = ((a : ℂ) - (t : ℂ) * Complex.I) * ((a : ℂ) + (t : ℂ) * Complex.I) := by ring
  have h1 : (∫ t in (-T)..T, a / (a ^ 2 + t ^ 2)) = 2 * Real.arctan (T / a) := by
    have hd : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt (fun x : ℝ => Real.arctan (x / a)) (a / (a ^ 2 + t ^ 2)) t := by
      intro t _
      have hdiv : HasDerivAt (fun x : ℝ => x / a) (1 / a) t := (hasDerivAt_id t).div_const a
      have hat := (Real.hasDerivAt_arctan (t / a)).comp t hdiv
      have hval : 1 / (1 + (t / a) ^ 2) * (1 / a) = a / (a ^ 2 + t ^ 2) := by
        have hpos : a ^ 2 + t ^ 2 ≠ 0 := (by positivity : 0 < a ^ 2 + t ^ 2).ne'
        field_simp [ha, hpos]
      rwa [hval] at hat
    have hint : IntervalIntegrable (fun t : ℝ => a / (a ^ 2 + t ^ 2)) volume (-T) T := by
      refine Continuous.intervalIntegrable ?_ (-T) T
      refine continuous_const.div (by fun_prop) fun t => (by positivity : 0 < a ^ 2 + t ^ 2).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, neg_div, Real.arctan_neg]
    ring
  have h2 : (∫ t in (-T)..T, t / (a ^ 2 + t ^ 2)) = 0 := by
    have hd : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log (a ^ 2 + x ^ 2)) (t / (a ^ 2 + t ^ 2)) t := by
      intro t _
      have hpos : a ^ 2 + t ^ 2 ≠ 0 := (by positivity : 0 < a ^ 2 + t ^ 2).ne'
      have hpoly : HasDerivAt (fun x : ℝ => a ^ 2 + x ^ 2) (2 * t) t := by
        have := (hasDerivAt_pow 2 t).const_add (a ^ 2)
        simpa using this
      have hlog := (hpoly.log hpos).const_mul (1 / 2 : ℝ)
      have hval : 1 / 2 * (2 * t / (a ^ 2 + t ^ 2)) = t / (a ^ 2 + t ^ 2) := by ring
      rwa [hval] at hlog
    have hint : IntervalIntegrable (fun t : ℝ => t / (a ^ 2 + t ^ 2)) volume (-T) T := by
      refine Continuous.intervalIntegrable ?_ (-T) T
      refine continuous_id.div (by fun_prop) fun t => (by positivity : 0 < a ^ 2 + t ^ 2).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  have hint1 : IntervalIntegrable (fun t : ℝ => ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) volume (-T) T := by
    refine (Complex.continuous_ofReal.comp ?_).intervalIntegrable (-T) T
    exact continuous_const.div (by fun_prop) fun t => (by positivity : 0 < a ^ 2 + t ^ 2).ne'
  have hint2 : IntervalIntegrable (fun t : ℝ => Complex.I * ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) volume (-T) T := by
    refine (continuous_const.mul (Complex.continuous_ofReal.comp ?_)).intervalIntegrable (-T) T
    exact continuous_id.div (by fun_prop) fun t => (by positivity : 0 < a ^ 2 + t ^ 2).ne'
  simp_rw [hre]
  rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, h1, h2]
  simp

private lemma integral_inv_add_mul_I_horizontal {b : ℝ} (hb : b ≠ 0) (x₁ x₂ : ℝ) :
    (∫ σ in x₁..x₂, ((σ : ℂ) + (b : ℂ) * Complex.I)⁻¹) =
      (((1 / 2 : ℝ) * (Real.log (x₂ ^ 2 + b ^ 2) - Real.log (x₁ ^ 2 + b ^ 2)) : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (x₂ / b) - Real.arctan (x₁ / b) : ℝ) : ℂ) := by
  have hre : ∀ σ : ℝ, (((σ : ℂ) + (b : ℂ) * Complex.I)⁻¹) =
      ((σ / (σ ^ 2 + b ^ 2) : ℝ) : ℂ) - Complex.I * ((b / (σ ^ 2 + b ^ 2) : ℝ) : ℂ) := by
    intro σ
    have hden : (σ ^ 2 + b ^ 2 : ℝ) ≠ 0 := (by positivity : 0 < σ ^ 2 + b ^ 2).ne'
    have hdenC : ((σ : ℂ) + (b : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have := congr_arg Complex.im h0
      simp at this
      exact hb this
    rw [inv_eq_one_div, div_eq_iff hdenC]
    push_cast
    have hdenC2 : ((σ : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hden
    field_simp [hdenC2]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    calc (σ : ℂ) ^ 2 + (b : ℂ) ^ 2
        = ((σ : ℂ) - Complex.I * (b : ℂ)) * ((σ : ℂ) + (b : ℂ) * Complex.I) +
            (b : ℂ) ^ 2 * (Complex.I ^ 2 + 1) := by ring
      _ = ((σ : ℂ) - Complex.I * (b : ℂ)) * ((σ : ℂ) + (b : ℂ) * Complex.I) := by rw [hI2]; ring
      _ = ((σ : ℂ) - (b : ℂ) * Complex.I) * ((σ : ℂ) + (b : ℂ) * Complex.I) := by ring
  have h1 : (∫ σ in x₁..x₂, σ / (σ ^ 2 + b ^ 2)) =
      (1 / 2 : ℝ) * (Real.log (x₂ ^ 2 + b ^ 2) - Real.log (x₁ ^ 2 + b ^ 2)) := by
    have hd : ∀ σ ∈ Set.uIcc x₁ x₂,
        HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log (x ^ 2 + b ^ 2)) (σ / (σ ^ 2 + b ^ 2)) σ := by
      intro σ _
      have hpos : σ ^ 2 + b ^ 2 ≠ 0 := (by positivity : 0 < σ ^ 2 + b ^ 2).ne'
      have hpoly : HasDerivAt (fun x : ℝ => x ^ 2 + b ^ 2) (2 * σ) σ := by
        have := (hasDerivAt_pow 2 σ).add_const (b ^ 2)
        simpa using this
      have hlog := (hpoly.log hpos).const_mul (1 / 2 : ℝ)
      have hval : 1 / 2 * (2 * σ / (σ ^ 2 + b ^ 2)) = σ / (σ ^ 2 + b ^ 2) := by ring
      rwa [hval] at hlog
    have hint : IntervalIntegrable (fun σ : ℝ => σ / (σ ^ 2 + b ^ 2)) volume x₁ x₂ :=
      (continuous_id.div (by fun_prop) fun σ => (by positivity : 0 < σ ^ 2 + b ^ 2).ne').intervalIntegrable x₁ x₂
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    ring
  have h2 : (∫ σ in x₁..x₂, b / (σ ^ 2 + b ^ 2)) = Real.arctan (x₂ / b) - Real.arctan (x₁ / b) := by
    have hd : ∀ σ ∈ Set.uIcc x₁ x₂,
        HasDerivAt (fun x : ℝ => Real.arctan (x / b)) (b / (σ ^ 2 + b ^ 2)) σ := by
      intro σ _
      have hdiv : HasDerivAt (fun x : ℝ => x / b) (1 / b) σ := (hasDerivAt_id σ).div_const b
      have hat := (Real.hasDerivAt_arctan (σ / b)).comp σ hdiv
      have hval : 1 / (1 + (σ / b) ^ 2) * (1 / b) = b / (σ ^ 2 + b ^ 2) := by
        have hpos : σ ^ 2 + b ^ 2 ≠ 0 := (by positivity : 0 < σ ^ 2 + b ^ 2).ne'
        field_simp [hb, hpos]; ring
      rwa [hval] at hat
    have hint : IntervalIntegrable (fun σ : ℝ => b / (σ ^ 2 + b ^ 2)) volume x₁ x₂ :=
      (continuous_const.div (by fun_prop) fun σ => (by positivity : 0 < σ ^ 2 + b ^ 2).ne').intervalIntegrable x₁ x₂
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have hint1 : IntervalIntegrable (fun σ : ℝ => ((σ / (σ ^ 2 + b ^ 2) : ℝ) : ℂ)) volume x₁ x₂ :=
    (Complex.continuous_ofReal.comp
      (continuous_id.div (by fun_prop) fun σ => (by positivity : 0 < σ ^ 2 + b ^ 2).ne')).intervalIntegrable x₁ x₂
  have hint2 : IntervalIntegrable (fun σ : ℝ => Complex.I * ((b / (σ ^ 2 + b ^ 2) : ℝ) : ℂ)) volume x₁ x₂ :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.div (by fun_prop) fun σ => (by positivity : 0 < σ ^ 2 + b ^ 2).ne'))).intervalIntegrable x₁ x₂
  simp_rw [hre]
  rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, h1, h2]

private lemma arctan_add_arctan_inv {u : ℝ} (hu : 0 < u) :
    Real.arctan u + Real.arctan u⁻¹ = Real.pi / 2 := by
  set F : ℝ → ℝ := fun x => Real.arctan x + Real.arctan x⁻¹
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F 0 x := by
    intro x hx
    have hx_ne : x ≠ 0 := (Set.mem_Ioi.mp hx).ne'
    have h1 := Real.hasDerivAt_arctan x
    have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx_ne
    have h2 := (Real.hasDerivAt_arctan x⁻¹).comp x hinv
    have hsum := h1.add h2
    have hval : 1 / (1 + x ^ 2) + 1 / (1 + x⁻¹ ^ 2) * -(x ^ 2)⁻¹ = 0 := by
      have hpos1 : 1 + x ^ 2 ≠ 0 := (by positivity : 0 < 1 + x ^ 2).ne'
      have hpos2 : 1 + x⁻¹ ^ 2 ≠ 0 := (by positivity : 0 < 1 + x⁻¹ ^ 2).ne'
      field_simp [hx_ne, hpos1, hpos2]
      ring
    rwa [hval] at hsum
  have hftc : (∫ _ in (1 : ℝ)..u, (0 : ℝ)) = F u - F 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (by
        have hmin : 0 < min (1 : ℝ) u := lt_min zero_lt_one hu
        rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact lt_of_lt_of_le hmin ((min_le_left _ _).trans h1)
        · exact lt_of_lt_of_le hmin ((min_le_right _ _).trans h1)))
      intervalIntegrable_const
  rw [intervalIntegral.integral_zero] at hftc
  have hconst : F u = F 1 := by linarith
  change F u = Real.pi / 2
  rw [hconst]
  dsimp [F]
  rw [inv_one, Real.arctan_one]
  ring

private lemma integral_boundary_rect_inv_eq_two_pi_I {X c T : ℝ}
    (hX : 0 < X) (hc : 0 < c) (hT : 0 < T) :
    ((∫ σ in (-X)..c, ((σ : ℂ) + (-T : ℝ) * Complex.I)⁻¹) -
      (∫ σ in (-X)..c, ((σ : ℂ) + (T : ℝ) * Complex.I)⁻¹) +
      Complex.I * (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹) -
      Complex.I * (∫ t in (-T)..T, (((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹)) =
      2 * (Real.pi : ℂ) * Complex.I := by
  rw [integral_inv_add_mul_I_horizontal (neg_ne_zero.mpr hT.ne') (-X) c,
    integral_inv_add_mul_I_horizontal hT.ne' (-X) c,
    integral_inv_add_mul_I_vertical hc.ne' T,
    integral_inv_add_mul_I_vertical (neg_ne_zero.mpr hX.ne') T]
  have h1 : Real.arctan (c / T) + Real.arctan (T / c) = Real.pi / 2 := by
    have := arctan_add_arctan_inv (div_pos hc hT)
    rwa [inv_div] at this
  have h2 : Real.arctan (X / T) + Real.arctan (T / X) = Real.pi / 2 := by
    have := arctan_add_arctan_inv (div_pos hX hT)
    rwa [inv_div] at this
  simp only [neg_sq, div_neg, neg_div, Real.arctan_neg, neg_neg, sub_neg_eq_add]
  have hcomb :
      ((Real.arctan (c / T) + Real.arctan (X / T)) + (Real.arctan (c / T) + Real.arctan (X / T)) +
        2 * Real.arctan (T / c) + 2 * Real.arctan (T / X) : ℝ) = 2 * Real.pi := by
    linarith
  have hcombC : (((Real.arctan (c / T) + Real.arctan (X / T)) + (Real.arctan (c / T) + Real.arctan (X / T)) +
      2 * Real.arctan (T / c) + 2 * Real.arctan (T / X) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    exact_mod_cast hcomb
  push_cast at hcombC ⊢
  linear_combination Complex.I * hcombC

/-- **Exact Evaluation and Error Bound of the Perron Kernel at `y = 1`**:
`P(1; c, T) = arctan(T / c) / π` and `‖P(1; c, T) - 1/2‖ ≤ c / (π T)`. -/
theorem perron_vertical_integral_one {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    perronKernel 1 c T = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) ∧
    ‖perronKernel 1 c T - (1 / 2 : ℂ)‖ ≤ c / (Real.pi * T) := by
  have heval : perronKernel 1 c T = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) := by
    unfold perronKernel
    have hfun : (fun t : ℝ => ((1 : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
      ext t; simp [one_div]
    rw [hfun, integral_inv_add_mul_I_vertical hc.ne' T]
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    push_cast
    field_simp [hpi_ne]
  refine ⟨heval, ?_⟩
  rw [heval]
  have hsub : ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) - (1 / 2 : ℂ) =
      ((Real.arctan (T / c) / Real.pi - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hsub, Complex.norm_real, Real.norm_eq_abs]
  have hpi2 : Real.arctan (T / c) + Real.arctan (c / T) = Real.pi / 2 := by
    have := arctan_add_arctan_inv (div_pos hT hc)
    rwa [inv_div] at this
  have hdiff : Real.arctan (T / c) / Real.pi - 1 / 2 = -(Real.arctan (c / T) / Real.pi) := by
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp [hpi_ne]
    linarith
  rw [hdiff, abs_neg, abs_of_nonneg (div_nonneg (Real.arctan_nonneg.mpr (div_pos hc hT).le) Real.pi_pos.le)]
  -- `Real.arctan u ≤ u` for `0 ≤ u` via MVT (`deriv arctan x = 1 / (1 + x^2) ≤ 1`)
  have harctan_le : ∀ u : ℝ, 0 ≤ u → Real.arctan u ≤ u := by
    intro u hu
    have hmono : MonotoneOn (fun x : ℝ => x - Real.arctan x) (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (continuous_id.sub Real.continuous_arctan).continuousOn
        (differentiable_id.sub Real.differentiable_arctan).differentiableOn fun x _ => ?_
      have hd : HasDerivAt (fun t : ℝ => t - Real.arctan t) (1 - 1 / (1 + x ^ 2)) x :=
        (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
      rw [hd.deriv]
      have h1 : 1 / (1 + x ^ 2) ≤ 1 := div_le_one_of_le₀ (by nlinarith [sq_nonneg x]) (by positivity)
      linarith
    have h0 := hmono (Set.mem_Ici.mpr le_rfl) hu hu
    simp only [Real.arctan_zero, sub_zero] at h0
    linarith
  calc Real.arctan (c / T) / Real.pi
      ≤ (c / T) / Real.pi := div_le_div_of_nonneg_right (harctan_le (c / T) (div_pos hc hT).le) Real.pi_pos.le
    _ = c / (Real.pi * T) := by rw [div_div, mul_comm]

/-- **Effective Perron Vertical-Line Integral Bound (`y > 0`, `y ≠ 1`)**:
For all `y > 0` with `y ≠ 1`, `c > 0`, and `T > 0`:
`‖(1 / (2π)) ∫_{-T}^T y^{c + it} / (c + it) dt - (if 1 < y then 1 else 0)‖ ≤ y^c / (π T |log y|)`. -/
theorem perron_vertical_integral_bound {y c T : ℝ}
    (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T - (if 1 < y then (1 : ℂ) else 0)‖ ≤
      y ^ c / (Real.pi * T * |Real.log y|) := by
  set L : ℝ := Real.log y
  set f : ℂ → ℂ := fun s => Complex.exp (s * (L : ℂ)) / s
  have hperron_eq : perronKernel y c T =
      (1 / (2 * (Real.pi : ℂ))) * ∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I) := by
    unfold perronKernel
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp [f, L]
    rw [cpow_of_pos_eq_exp hy]
  -- Helper: bound horizontal integral `‖∫_{a}^{b} f(σ ± i T) dσ‖ ≤ (y^b - y^a) / (T * L)`
  have hhoriz : ∀ (a b : ℝ), a ≤ b → ∀ (ε : ℝ), |ε| = T →
      ‖∫ σ in a..b, f ((σ : ℂ) + (ε : ℂ) * Complex.I)‖ ≤
        (y ^ b - y ^ a) / (T * L) := by
    intro a b hab ε hε
    have hnorm_le : ∀ σ ∈ Set.Ioc a b, ‖f ((σ : ℂ) + (ε : ℂ) * Complex.I)‖ ≤ y ^ σ / T := by
      intro σ _
      dsimp [f, L]
      rw [norm_div, norm_exp_mul_log hy]
      have hre_s : ((σ : ℂ) + (ε : ℂ) * Complex.I).re = σ := by simp
      have him_s : ((σ : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
      rw [hre_s]
      have hden_ge : T ≤ ‖(σ : ℂ) + (ε : ℂ) * Complex.I‖ := by
        have := Complex.abs_im_le_norm ((σ : ℂ) + (ε : ℂ) * Complex.I)
        rwa [him_s, hε] at this
      exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hy σ).le hT hden_ge
    have hint_rhs : IntervalIntegrable (fun σ : ℝ => y ^ σ / T) volume a b := by
      refine Continuous.intervalIntegrable ?_ a b
      exact (continuous_const.rpow continuous_id (fun _ => Or.inl hy.ne')).div_const T
    have hle1 := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall hnorm_le) hint_rhs
    have hint_eval : (∫ σ in a..b, y ^ σ / T) = (y ^ b - y ^ a) / (T * L) := by
      have hL_ne : L ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
      have hd : ∀ σ ∈ Set.uIcc a b,
          HasDerivAt (fun x : ℝ => Real.exp (x * L) / (T * L)) (y ^ σ / T) σ := by
        intro σ _
        have h1 : HasDerivAt (fun x : ℝ => x * L) L σ := by simpa using (hasDerivAt_id σ).mul_const L
        have h2 := (h1.exp).div_const (T * L)
        have hval : Real.exp (σ * L) * L / (T * L) = y ^ σ / T := by
          rw [Real.rpow_def_of_pos hy, mul_comm L σ]
          field_simp [hL_ne, hT.ne']
        rwa [hval] at h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_rhs]
      rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hy, mul_comm L b, mul_comm L a, sub_div]
    exact hle1.trans_eq hint_eval
  -- Helper: bound vertical integral `‖∫_{-T}^T f(a + i t) dt‖ ≤ 2 * T * y^a / |a|`
  have hvert : ∀ (a : ℝ), a ≠ 0 →
      ‖∫ t in (-T)..T, f ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * T * (y ^ a / |a|) := by
    intro a ha
    have hnorm_le : ∀ t ∈ Set.uIoc (-T) T, ‖f ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ y ^ a / |a| := by
      intro t _
      dsimp [f, L]
      rw [norm_div, norm_exp_mul_log hy]
      have hre_s : ((a : ℂ) + (t : ℂ) * Complex.I).re = a := by simp
      rw [hre_s]
      have hden_ge : |a| ≤ ‖(a : ℂ) + (t : ℂ) * Complex.I‖ := by
        have := Complex.abs_re_le_norm ((a : ℂ) + (t : ℂ) * Complex.I)
        rwa [hre_s] at this
      exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hy a).le (abs_pos.mpr ha) hden_ge
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hnorm_le
    have hlen : |T - (-T)| = 2 * T := by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
    rw [hlen] at hle
    linarith
  by_cases hgt : 1 < y
  · -- Case 1: `y > 1`, so `L = log y > 0`. Shift contour LEFT to `-X` (`X > 0`)!
    simp only [hgt, ↓reduceIte]
    have hL_pos : 0 < L := Real.log_pos hgt
    rw [abs_of_pos hL_pos, hperron_eq]
    -- For every `X > 0`, `‖I * ∫_{-T}^T f(c + it) dt - 2π I‖ ≤ 2 y^c / (T L) + 2 T y^(-X) / X`!
    have hX_bound : ∀ X : ℝ, 0 < X →
        ‖perronKernel y c T - 1‖ ≤ y ^ c / (Real.pi * T * L) + T * y ^ (-X) / (Real.pi * X) := by
      intro X hX
      -- Entire function `g(s) = dslope (fun s => exp(s * L)) 0 s` satisfies `f(s) = g(s) + s⁻¹` for `s ≠ 0`
      set g : ℂ → ℂ := dslope (fun s : ℂ => Complex.exp (s * (L : ℂ))) 0
      have hg_diff : Differentiable ℂ g := by
        have hexp_diff : Differentiable ℂ (fun s : ℂ => Complex.exp (s * (L : ℂ))) :=
          (differentiable_id.mul_const (L : ℂ)).cexp
        exact (Complex.differentiableOn_dslope (IsOpen.mem_nhds isOpen_univ (Set.mem_univ 0))).mpr
          hexp_diff.differentiableOn |> fun hd => fun z => hd.differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ z))
      have hfg : ∀ s : ℂ, s ≠ 0 → f s = g s + s⁻¹ := by
        intro s hs
        dsimp [f, g]
        rw [dslope_of_ne _ hs, slope_def_field, zero_mul, Complex.exp_zero, sub_zero]
        field_simp [hs]
        ring
      -- Cauchy's theorem on rectangle `[-X, c] × [-T, T]` for entire `g`:
      have hcauchy_g := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
        ((-X : ℝ) + (-T : ℝ) * Complex.I) ((c : ℝ) + (T : ℝ) * Complex.I)
        (hg_diff.differentiableOn.mono (Set.subset_univ _))
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add, smul_eq_mul] at hcauchy_g
      -- Combine `g` (= 0) and `s⁻¹` (= 2πi) on the 4 edges of `[-X, c] × [-T, T]`!
      have hcauchy_inv := integral_boundary_rect_inv_eq_two_pi_I hX hc hT
      have hsum_edge : ∀ (u v : ℝ) (φ : ℝ → ℂ),
          (∀ x ∈ Set.uIcc u v, φ x ≠ 0) →
          ContinuousOn φ (Set.uIcc u v) →
          (∫ x in u..v, f (φ x)) = (∫ x in u..v, g (φ x)) + (∫ x in u..v, (φ x)⁻¹) := by
        intro u v φ hne hcont
        have hcongr : Set.EqOn (fun x => f (φ x)) (fun x => g (φ x) + (φ x)⁻¹) (Set.uIcc u v) :=
          fun x hx => hfg (φ x) (hne x hx)
        rw [intervalIntegral.integral_congr hcongr]
        refine intervalIntegral.integral_add ?_ ?_
        · exact (hg_diff.continuous.comp_continuousOn hcont).intervalIntegrable
        · exact (hcont.inv₀ hne).intervalIntegrable
      have hbot : (∫ σ in (-X)..c, f ((σ : ℂ) + (-T : ℝ) * Complex.I)) =
          (∫ σ in (-X)..c, g ((σ : ℂ) + (-T : ℝ) * Complex.I)) +
          (∫ σ in (-X)..c, ((σ : ℂ) + (-T : ℝ) * Complex.I)⁻¹) :=
        hsum_edge (-X) c (fun σ => (σ : ℂ) + (-T : ℝ) * Complex.I)
          (fun σ _ h0 => by have := congr_arg Complex.im h0; simp at this; linarith)
          (by fun_prop)
      have htop : (∫ σ in (-X)..c, f ((σ : ℂ) + (T : ℝ) * Complex.I)) =
          (∫ σ in (-X)..c, g ((σ : ℂ) + (T : ℝ) * Complex.I)) +
          (∫ σ in (-X)..c, ((σ : ℂ) + (T : ℝ) * Complex.I)⁻¹) :=
        hsum_edge (-X) c (fun σ => (σ : ℂ) + (T : ℝ) * Complex.I)
          (fun σ _ h0 => by have := congr_arg Complex.im h0; simp at this; linarith)
          (by fun_prop)
      have hright : (∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) =
          (∫ t in (-T)..T, g ((c : ℂ) + (t : ℂ) * Complex.I)) +
          (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹) :=
        hsum_edge (-T) T (fun t => (c : ℂ) + (t : ℂ) * Complex.I)
          (fun t _ h0 => by have := congr_arg Complex.re h0; simp at this; linarith)
          (by fun_prop)
      have hleft : (∫ t in (-T)..T, f (((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
          (∫ t in (-T)..T, g (((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
          (∫ t in (-T)..T, (((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹) :=
        hsum_edge (-T) T (fun t => ((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          (fun t _ h0 => by have := congr_arg Complex.re h0; simp at this; linarith)
          (by fun_prop)
      have hrect_f :
          (∫ σ in (-X)..c, f ((σ : ℂ) + (-T : ℝ) * Complex.I)) -
          (∫ σ in (-X)..c, f ((σ : ℂ) + (T : ℝ) * Complex.I)) +
          Complex.I * (∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) -
          Complex.I * (∫ t in (-T)..T, f (((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
            2 * (Real.pi : ℂ) * Complex.I := by
        rw [hbot, htop, hright, hleft]
        linear_combination hcauchy_g + hcauchy_inv
      have hisolate : Complex.I * (∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) -
          2 * (Real.pi : ℂ) * Complex.I =
          Complex.I * (∫ t in (-T)..T, f (((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
          (∫ σ in (-X)..c, f ((σ : ℂ) + (T : ℝ) * Complex.I)) -
          (∫ σ in (-X)..c, f ((σ : ℂ) + (-T : ℝ) * Complex.I)) := by
        linear_combination hrect_f
      have hnorm_iso : ‖(∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) - 2 * (Real.pi : ℂ)‖ ≤
          2 * (y ^ c / (T * L)) + 2 * T * (y ^ (-X) / X) := by
        have hmulI : ‖(∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) - 2 * (Real.pi : ℂ)‖ =
            ‖Complex.I * (∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) -
              2 * (Real.pi : ℂ) * Complex.I‖ := by
          have : Complex.I * ((∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) - 2 * (Real.pi : ℂ)) =
              Complex.I * (∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) - 2 * (Real.pi : ℂ) * Complex.I := by ring
          rw [← this, norm_mul, Complex.norm_I, one_mul]
        rw [hmulI, hisolate]
        have hb_top := hhoriz (-X) c (by linarith) T (abs_of_pos hT)
        have hb_bot := hhoriz (-X) c (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT])
        have hb_left := hvert (-X) (neg_ne_zero.mpr hX.ne')
        rw [abs_neg, abs_of_pos hX] at hb_left
        have hsub_le : (y ^ c - y ^ (-X)) / (T * L) ≤ y ^ c / (T * L) :=
          div_le_div_of_nonneg_right (by linarith [Real.rpow_pos_of_pos hy (-X)]) (by positivity)
        have htri1 := norm_sub_le
          (Complex.I * (∫ t in (-T)..T, f (((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
            (∫ σ in (-X)..c, f ((σ : ℂ) + (T : ℝ) * Complex.I)))
          (∫ σ in (-X)..c, f ((σ : ℂ) + (-T : ℝ) * Complex.I))
        have htri2 := norm_add_le
          (Complex.I * (∫ t in (-T)..T, f (((-X : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
          (∫ σ in (-X)..c, f ((σ : ℂ) + (T : ℝ) * Complex.I))
        rw [norm_mul, Complex.norm_I, one_mul] at htri2
        linarith
      rw [hperron_eq]
      have hscale : (1 / (2 * (Real.pi : ℂ))) * (∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) - 1 =
          (1 / (2 * (Real.pi : ℂ))) * ((∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) - 2 * (Real.pi : ℂ)) := by
        have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
          mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
        rw [mul_sub, one_div_mul_cancel h2pi_ne]
      rw [hscale, norm_mul, one_div, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, show ‖(2 : ℂ)‖ = 2 by norm_num]
      calc (2 * Real.pi)⁻¹ * ‖(∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) - 2 * (Real.pi : ℂ)‖
          ≤ (2 * Real.pi)⁻¹ * (2 * (y ^ c / (T * L)) + 2 * T * (y ^ (-X) / X)) :=
            mul_le_mul_of_nonneg_left hnorm_iso (by positivity)
        _ = y ^ c / (Real.pi * T * L) + T * y ^ (-X) / (Real.pi * X) := by
            have hpi_ne := Real.pi_pos.ne'
            field_simp [hpi_ne, hT.ne', hL_pos.ne', hX.ne']
    -- Send `X → +∞`: since `y > 1`, `y ^ (-X) ≤ 1` for all `X > 0`, so `T * y^(-X) / (π X) ≤ T / (π X)`!
    rw [← hperron_eq]
    by_contra hgt_err
    push Not at hgt_err
    set δ : ℝ := ‖perronKernel y c T - 1‖ - y ^ c / (Real.pi * T * L)
    have hδ : 0 < δ := by linarith
    set X : ℝ := 2 * T / (Real.pi * δ)
    have hX : 0 < X := by positivity
    have hbound := hX_bound X hX
    have hyX : y ^ (-X) ≤ 1 := by
      rw [Real.rpow_def_of_pos hy]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hterm_le : T * y ^ (-X) / (Real.pi * X) ≤ δ / 2 := by
      calc T * y ^ (-X) / (Real.pi * X)
          ≤ T * 1 / (Real.pi * X) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyX hT.le) (by positivity)
        _ = δ / 2 := by
            dsimp [X]
            have hpi_ne := Real.pi_pos.ne'
            field_simp [hpi_ne, hT.ne', hδ.ne']
    linarith
  · -- Case 2: `0 < y < 1`, so `L = log y < 0`. Shift contour RIGHT to `+X` (`X > c`)!
    simp only [hgt, ↓reduceIte, sub_zero]
    have hylt : y < 1 := lt_of_le_of_ne (not_lt.mp hgt) hy1
    have hL_neg : L < 0 := Real.log_neg hy hylt
    rw [abs_of_neg hL_neg]
    have hX_bound : ∀ X : ℝ, c < X →
        ‖perronKernel y c T‖ ≤ y ^ c / (Real.pi * T * (-L)) + T * y ^ X / (Real.pi * X) := by
      intro X hX
      have hX_pos : 0 < X := hc.trans hX
      -- `f` is differentiable on the closed rectangle `[c, X] × [-T, T]` (all points have `re ≥ c > 0`, so `≠ 0`)!
      have hf_diff : DifferentiableOn ℂ f (Set.uIcc c X ×ℂ Set.uIcc (-T) T) := by
        intro s hs
        have hre_ge : c ≤ s.re := by
          have := hs.1
          rw [Set.uIcc_of_le hX.le] at this
          exact this.1
        have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre_ge; linarith
        have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w * (L : ℂ))) s :=
          (differentiableAt_id.mul_const (L : ℂ)).cexp
        exact (hexp.div differentiableAt_id hs0).differentiableWithinAt
      have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
        ((c : ℝ) + (-T : ℝ) * Complex.I) ((X : ℝ) + (T : ℝ) * Complex.I) (by
          simpa [Complex.add_re, Complex.add_im] using hf_diff)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add, smul_eq_mul] at hcauchy
      have hisolate : Complex.I * (∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)) =
          Complex.I * (∫ t in (-T)..T, f ((X : ℂ) + (t : ℂ) * Complex.I)) +
          (∫ σ in c..X, f ((σ : ℂ) + (-T : ℝ) * Complex.I)) -
          (∫ σ in c..X, f ((σ : ℂ) + (T : ℝ) * Complex.I)) := by
        linear_combination -hcauchy
      have hnorm_iso : ‖∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          2 * (y ^ c / (T * (-L))) + 2 * T * (y ^ X / X) := by
        have hmulI : ‖∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)‖ =
            ‖Complex.I * ∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
        rw [hmulI, hisolate]
        have hb_bot := hhoriz c X hX.le (-T) (by rw [abs_neg, abs_of_pos hT])
        have hb_top := hhoriz c X hX.le T (abs_of_pos hT)
        have hb_right := hvert X hX_pos.ne'
        rw [abs_of_pos hX_pos] at hb_right
        have hnegL_pos : 0 < -L := by linarith
        have hsub_le : (y ^ X - y ^ c) / (T * L) ≤ y ^ c / (T * (-L)) := by
          have heq : (y ^ X - y ^ c) / (T * L) = (y ^ c - y ^ X) / (T * (-L)) := by
            have hT_ne := hT.ne'
            have hL_ne := hL_neg.ne
            field_simp [hT_ne, hL_ne]
            ring
          rw [heq]
          exact div_le_div_of_nonneg_right (by linarith [Real.rpow_pos_of_pos hy X]) (by positivity)
        have htri1 := norm_sub_le
          (Complex.I * (∫ t in (-T)..T, f ((X : ℂ) + (t : ℂ) * Complex.I)) +
            (∫ σ in c..X, f ((σ : ℂ) + (-T : ℝ) * Complex.I)))
          (∫ σ in c..X, f ((σ : ℂ) + (T : ℝ) * Complex.I))
        have htri2 := norm_add_le
          (Complex.I * (∫ t in (-T)..T, f ((X : ℂ) + (t : ℂ) * Complex.I)))
          (∫ σ in c..X, f ((σ : ℂ) + (-T : ℝ) * Complex.I))
        rw [norm_mul, Complex.norm_I, one_mul] at htri2
        linarith
      rw [hperron_eq, norm_mul, one_div, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, show ‖(2 : ℂ)‖ = 2 by norm_num]
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, f ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (2 * Real.pi)⁻¹ * (2 * (y ^ c / (T * (-L))) + 2 * T * (y ^ X / X)) :=
            mul_le_mul_of_nonneg_left hnorm_iso (by positivity)
        _ = y ^ c / (Real.pi * T * (-L)) + T * y ^ X / (Real.pi * X) := by
            have hpi_ne := Real.pi_pos.ne'
            have hnegL_ne : (-L) ≠ 0 := by linarith
            field_simp [hpi_ne, hT.ne', hnegL_ne, hX_pos.ne']
    by_contra hgt_err
    push Not at hgt_err
    set δ : ℝ := ‖perronKernel y c T‖ - y ^ c / (Real.pi * T * (-L))
    have hδ : 0 < δ := by linarith
    set X : ℝ := max (c + 1) (2 * T / (Real.pi * δ))
    have hcX : c < X := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hX_pos : 0 < X := hc.trans hcX
    have hX_ge : 2 * T / (Real.pi * δ) ≤ X := le_max_right _ _
    have hbound := hX_bound X hcX
    have hyX : y ^ X ≤ 1 := by
      rw [Real.rpow_def_of_pos hy]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hterm_le : T * y ^ X / (Real.pi * X) ≤ δ / 2 := by
      calc T * y ^ X / (Real.pi * X)
          ≤ T * 1 / (Real.pi * X) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyX hT.le) (by positivity)
        _ ≤ T * 1 / (Real.pi * (2 * T / (Real.pi * δ))) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hX_ge Real.pi_pos.le)
        _ = δ / 2 := by
            have hpi_ne := Real.pi_pos.ne'
            field_simp [hpi_ne, hT.ne', hδ.ne']
    linarith

private lemma abs_log_div_nat_pos_lower_bound {x : ℝ} (hx : 0 < x)
    (hx_not_nat : ∀ n : ℕ, (n : ℝ) ≠ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 1 ≤ n → δ ≤ |Real.log (x / (n : ℝ))| := by
  set m : ℕ := Nat.floor x
  have hlt_succ : x < ((m + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one x
  have hlog2_pos : 0 < Real.log (((m + 1 : ℕ) : ℝ) / x) :=
    Real.log_pos ((one_lt_div hx).mpr hlt_succ)
  by_cases hm0 : m = 0
  · refine ⟨Real.log (((m + 1 : ℕ) : ℝ) / x), hlog2_pos, fun n hn => ?_⟩
    have hn_ge : ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ n)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hdiv_lt : x / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr (hlt_succ.trans_le hn_ge)
    rw [abs_of_neg (Real.log_neg (div_pos hx hn_pos) hdiv_lt), ← Real.log_inv, inv_div]
    exact Real.log_le_log (div_pos (by positivity) hx) (div_le_div_of_nonneg_right hn_ge hx.le)
  · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hm_lt : (m : ℝ) < x := lt_of_le_of_ne (Nat.floor_le hx.le) (hx_not_nat m)
    have hlog1_pos : 0 < Real.log (x / (m : ℝ)) := Real.log_pos ((one_lt_div hm_pos).mpr hm_lt)
    refine ⟨min (Real.log (x / (m : ℝ))) (Real.log (((m + 1 : ℕ) : ℝ) / x)),
      lt_min hlog1_pos hlog2_pos, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    by_cases hnm : n ≤ m
    · refine (min_le_left _ _).trans ?_
      have hn_r : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hdiv_gt : 1 < x / (n : ℝ) := (one_lt_div hn_pos).mpr (hn_r.trans_lt hm_lt)
      rw [abs_of_pos (Real.log_pos hdiv_gt)]
      exact Real.log_le_log (div_pos hx hm_pos) (div_le_div_of_nonneg_left hx.le hn_pos hn_r)
    · refine (min_le_right _ _).trans ?_
      have hn_ge : ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ n)
      have hdiv_lt : x / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr (hlt_succ.trans_le hn_ge)
      rw [abs_of_neg (Real.log_neg (div_pos hx hn_pos) hdiv_lt), ← Real.log_inv, inv_div]
      exact Real.log_le_log (div_pos (by positivity) hx) (div_le_div_of_nonneg_right hn_ge hx.le)

/-- **Effective Truncated Perron Formula for Arbitrary Absolutely Convergent Dirichlet Series**:
Let `a : ℕ → ℂ`, `c > 0`, `T > 0`, and `x > 0` with `x ∉ ℕ` (`∀ n : ℕ, (n : ℝ) ≠ x`).
If `∑_{n ≥ 1} ‖a n‖ * n^{-c} < ∞`, then:
`‖(1 / (2π)) ∫_{-T}^T L(a, c + it) * x^{c + it} / (c + it) dt - ∑_{n=1}^{⌊x⌋} a_n‖`
`  ≤ ∑'_{n ≥ 1} ‖a n‖ * (x / n)^c / (π * T * |log(x / n)|)`. -/
theorem perron_truncated_formula (a : ℕ → ℂ) {c T x : ℝ}
    (hc : 0 < c) (hT : 0 < T) (hx : 0 < x)
    (hx_not_nat : ∀ n : ℕ, (n : ℝ) ≠ x)
    (hsumm : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else ‖a n‖ * (n : ℝ) ^ (-c))) :
    ‖(1 / (2 * (Real.pi : ℂ))) *
        (∫ t in (-T)..T, LSeries a ((c : ℂ) + (t : ℂ) * Complex.I) *
          ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) /
            ((c : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.Icc 1 (Nat.floor x), a n‖ ≤
    ∑' n : ℕ, if n = 0 then (0 : ℝ)
      else ‖a n‖ * (x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|) := by
  -- Step 1: Uniform bound for exchanging `∫_{-T}^T` and `∑'_n`
  set s : ℝ → ℂ := fun t => (c : ℂ) + (t : ℂ) * Complex.I
  set term : ℕ → ℝ → ℂ := fun n t =>
    if n = 0 then 0 else a n * ((x / (n : ℝ) : ℝ) : ℂ) ^ (s t) / s t
  have hs_ne : ∀ t : ℝ, s t ≠ 0 := fun t h0 => by
    have := congr_arg Complex.re h0; simp [s] at this; linarith
  have hs_re : ∀ t : ℝ, (s t).re = c := fun t => by simp [s]
  have hs_norm_ge : ∀ t : ℝ, c ≤ ‖s t‖ := fun t => by
    have := Complex.abs_re_le_norm (s t)
    rwa [hs_re t, abs_of_pos hc] at this
  have hterm_eq : ∀ (n : ℕ) (t : ℝ),
      LSeries.term a (s t) n * ((x : ℂ) ^ (s t) / s t) = term n t := by
    intro n t
    by_cases hn0 : n = 0
    · simp [LSeries.term, term, hn0]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      simp only [LSeries.term_of_ne_zero hn0, term, hn0, ↓reduceIte]
      have hcpow : ((x / (n : ℝ) : ℝ) : ℂ) ^ (s t) = (x : ℂ) ^ (s t) / ((n : ℂ) ^ (s t)) := by
        rw [cpow_of_pos_eq_exp (div_pos hx hn_pos), cpow_of_pos_eq_exp hx,
          show ((n : ℂ) ^ (s t)) = Complex.exp (s t * (Real.log (n : ℝ) : ℂ)) from
            cpow_of_pos_eq_exp hn_pos (s t),
          Real.log_div hx.ne' hn_pos.ne', ← Complex.exp_sub]
        congr 1; push_cast; ring
      rw [hcpow]
      ring
  have hL_summ_t : ∀ t : ℝ, Summable (fun n => term n t) := by
    intro t
    refine Summable.of_norm_bounded (hsumm.mul_left (x ^ c / c)) fun n => ?_
    by_cases hn0 : n = 0
    · simp [term, hn0]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      simp only [term, hn0, ↓reduceIte, norm_div, norm_mul]
      rw [cpow_of_pos_eq_exp (div_pos hx hn_pos), norm_exp_mul_log (div_pos hx hn_pos), hs_re t,
        Real.div_rpow hx.le hn_pos.le]
      calc ‖a n‖ * (x ^ c / (n : ℝ) ^ c) / ‖s t‖
          ≤ ‖a n‖ * (x ^ c / (n : ℝ) ^ c) / c :=
            div_le_div_of_nonneg_left (by positivity) hc (hs_norm_ge t)
        _ = x ^ c / c * (‖a n‖ * (n : ℝ) ^ (-c)) := by
            rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv (x ^ c)]; ring
  have hpointwise : ∀ t : ℝ,
      LSeries a (s t) * (x : ℂ) ^ (s t) / s t = ∑' n : ℕ, term n t := by
    intro t
    unfold LSeries
    rw [mul_div_assoc, ← tsum_mul_right]
    exact tsum_congr fun n => hterm_eq n t
  -- Step 2: Exchange `∫ t in (-T)..T, ∑' n, term n t` with `∑' n, ∫ t in (-T)..T, term n t`
  have hswap : (∫ t in (-T)..T, ∑' n : ℕ, term n t) =
      ∑' n : ℕ, ∫ t in (-T)..T, term n t := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    have htsum_eq : (∑' n : ℕ, ∫ t in (-T)..T, term n t) =
        ∑' n : ℕ, ∫ t in Set.Ioc (-T) T, term n t :=
      tsum_congr fun n => intervalIntegral.integral_of_le (by linarith : -T ≤ T)
    rw [htsum_eq]
    refine MeasureTheory.integral_tsum (fun n => ?_) ?_
    · by_cases hn0 : n = 0
      · simp only [term, hn0, ↓reduceIte]
        exact aestronglyMeasurable_const
      · have hcont : Continuous (term n) := by
          have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
          have hfun : term n = fun t => a n * Complex.exp (s t * (Real.log (x / (n : ℝ)) : ℂ)) / s t := by
            ext t; simp only [term, hn0, ↓reduceIte, cpow_of_pos_eq_exp (div_pos hx hn_pos)]
          rw [hfun]
          refine (continuous_const.mul (Complex.continuous_exp.comp ?_)).div ?_ hs_ne
          · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const
          · exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        exact hcont.aestronglyMeasurable
    · -- `∑' n, ∫⁻ t in Set.Ioc (-T) T, ‖term n t‖ₑ ≠ ⊤`
      have hbound_n : ∀ n : ℕ,
          (∫⁻ t in Set.Ioc (-T) T, ‖term n t‖ₑ) ≤
            ENNReal.ofReal ((2 * T) * (x ^ c / c * (if n = 0 then (0 : ℝ) else ‖a n‖ * (n : ℝ) ^ (-c)))) := by
        intro n
        by_cases hn0 : n = 0
        · simp [term, hn0]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
          set C_n : ℝ := x ^ c / c * (‖a n‖ * (n : ℝ) ^ (-c))
          have hCn_nn : 0 ≤ C_n := by positivity
          have hle_pt : ∀ t : ℝ, ‖term n t‖ₑ ≤ ENNReal.ofReal C_n := fun t => by
            rw [← ofReal_norm]
            refine ENNReal.ofReal_le_ofReal ?_
            simp only [term, hn0, ↓reduceIte, norm_div, norm_mul]
            rw [cpow_of_pos_eq_exp (div_pos hx hn_pos), norm_exp_mul_log (div_pos hx hn_pos), hs_re t,
              Real.div_rpow hx.le hn_pos.le]
            calc ‖a n‖ * (x ^ c / (n : ℝ) ^ c) / ‖s t‖
                ≤ ‖a n‖ * (x ^ c / (n : ℝ) ^ c) / c :=
                  div_le_div_of_nonneg_left (by positivity) hc (hs_norm_ge t)
              _ = C_n := by dsimp [C_n]; rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv (x ^ c)]; ring
          calc ∫⁻ t in Set.Ioc (-T) T, ‖term n t‖ₑ
              ≤ ∫⁻ _t in Set.Ioc (-T) T, ENNReal.ofReal C_n := lintegral_mono hle_pt
            _ = ENNReal.ofReal C_n * volume (Set.Ioc (-T) T) := setLIntegral_const _ _
            _ = ENNReal.ofReal C_n * ENNReal.ofReal (T - (-T)) := by rw [Real.volume_Ioc]
            _ = ENNReal.ofReal ((2 * T) * C_n) := by
                rw [← ENNReal.ofReal_mul hCn_nn]
                congr 1; ring
            _ = ENNReal.ofReal ((2 * T) * (x ^ c / c * (if n = 0 then (0 : ℝ) else ‖a n‖ * (n : ℝ) ^ (-c)))) := by
                simp [hn0, C_n]
      have hsumm_real : Summable (fun n : ℕ =>
          (2 * T) * (x ^ c / c * (if n = 0 then (0 : ℝ) else ‖a n‖ * (n : ℝ) ^ (-c)))) :=
        (hsumm.mul_left (x ^ c / c)).mul_left (2 * T)
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound_n)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by split_ifs <;> positivity) hsumm_real]
      exact ENNReal.ofReal_ne_top
  -- Step 3: Summability of the Perron error series (from uniform lower bound on `|log (x / n)|`)
  rcases abs_log_div_nat_pos_lower_bound hx hx_not_nat with ⟨δ, hδ, hlog_ge⟩
  have herr_summ : Summable (fun n : ℕ => if n = 0 then (0 : ℝ)
      else ‖a n‖ * (x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|)) := by
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => ?_) (hsumm.mul_left (x ^ c / (Real.pi * T * δ)))
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      simp only [hn0, ↓reduceIte]
      rw [Real.div_rpow hx.le hn_pos.le]
      have hden_le : Real.pi * T * δ ≤ Real.pi * T * |Real.log (x / (n : ℝ))| :=
        mul_le_mul_of_nonneg_left (hlog_ge n hn1) (by positivity)
      calc ‖a n‖ * (x ^ c / (n : ℝ) ^ c) / (Real.pi * T * |Real.log (x / (n : ℝ))|)
          ≤ ‖a n‖ * (x ^ c / (n : ℝ) ^ c) / (Real.pi * T * δ) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden_le
        _ = x ^ c / (Real.pi * T * δ) * (‖a n‖ * (n : ℝ) ^ (-c)) := by
            rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv (x ^ c)]; ring
  -- Step 4: Express both the Perron integral and the finite sum as `∑'_n`, subtract, and bound termwise!
  set ind : ℕ → ℂ := fun n =>
    if n = 0 then 0 else a n * (if 1 < x / (n : ℝ) then (1 : ℂ) else 0)
  have hfin_eq_tsum : (∑ n ∈ Finset.Icc 1 (Nat.floor x), a n) = ∑' n : ℕ, ind n := by
    rw [tsum_eq_sum (s := Finset.Icc 1 (Nat.floor x))]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_le : n ≤ Nat.floor x := (Finset.mem_Icc.mp hn).2
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hn_lt_x : (n : ℝ) < x := lt_of_le_of_ne ((Nat.cast_le.mpr hn_le).trans (Nat.floor_le hx.le)) (hx_not_nat n)
      have hgt1 : 1 < x / (n : ℝ) := (one_lt_div hn_pos).mpr hn_lt_x
      simp [ind, show n ≠ 0 by omega, hgt1]
    · intro n hn
      by_cases hn0 : n = 0
      · simp [ind, hn0]
      · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
        have hn_gt : Nat.floor x < n := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at hn
          omega
        have hx_lt_n : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hn_gt)
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hnot1 : ¬ 1 < x / (n : ℝ) := not_lt.mpr ((div_le_one hn_pos).mpr hx_lt_n.le)
        simp [ind, hn0, hnot1]
  have hind_summ : Summable ind := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 (Nat.floor x)) fun n hn => ?_
    by_cases hn0 : n = 0
    · simp [ind, hn0]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      have hn_gt : Nat.floor x < n := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        omega
      have hx_lt_n : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hn_gt)
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hnot1 : ¬ 1 < x / (n : ℝ) := not_lt.mpr ((div_le_one hn_pos).mpr hx_lt_n.le)
      simp [ind, hn0, hnot1]
  have hperron_term : ∀ n : ℕ,
      (1 / (2 * (Real.pi : ℂ))) * (∫ t in (-T)..T, term n t) =
        if n = 0 then 0 else a n * perronKernel (x / (n : ℝ)) c T := by
    intro n
    by_cases hn0 : n = 0
    · simp [term, hn0]
    · simp only [term, hn0, ↓reduceIte, perronKernel, s]
      have hconst : (∫ t in (-T)..T, a n * ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
          ((c : ℂ) + (t : ℂ) * Complex.I)) =
          a n * (∫ t in (-T)..T, ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => by ring
      rw [hconst]
      ring
  have hperron_summ : Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else a n * perronKernel (x / (n : ℝ)) c T) := by
    have hdiff_summ : Summable (fun n : ℕ =>
        (if n = 0 then (0 : ℂ) else a n * perronKernel (x / (n : ℝ)) c T) - ind n) := by
      refine Summable.of_norm_bounded herr_summ fun n => ?_
      by_cases hn0 : n = 0
      · simp [ind, hn0]
      · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hne1 : x / (n : ℝ) ≠ 1 := fun h => hx_not_nat n ((div_eq_one_iff_eq hn_pos.ne').mp h).symm
        simp only [ind, hn0, ↓reduceIte, ← mul_sub, norm_mul, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left
          (perron_vertical_integral_bound (div_pos hx hn_pos) hne1 hc hT) (norm_nonneg _)
    simpa using hdiff_summ.add hind_summ
  have hdiff_eq :
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t in (-T)..T, LSeries a (s t) * (x : ℂ) ^ (s t) / s t) -
      ∑ n ∈ Finset.Icc 1 (Nat.floor x), a n =
      ∑' n : ℕ, ((if n = 0 then (0 : ℂ) else a n * perronKernel (x / (n : ℝ)) c T) - ind n) := by
    have hcongr : (∫ t in (-T)..T, LSeries a (s t) * (x : ℂ) ^ (s t) / s t) =
        ∫ t in (-T)..T, ∑' n : ℕ, term n t :=
      intervalIntegral.integral_congr fun t _ => hpointwise t
    rw [hcongr, hswap, ← tsum_mul_left, tsum_congr hperron_term, hfin_eq_tsum,
      ← hperron_summ.tsum_sub hind_summ]
  rw [hdiff_eq]
  have hnorm_le : ∀ n : ℕ,
      ‖(if n = 0 then (0 : ℂ) else a n * perronKernel (x / (n : ℝ)) c T) - ind n‖ ≤
        if n = 0 then (0 : ℝ)
        else ‖a n‖ * (x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|) := by
    intro n
    by_cases hn0 : n = 0
    · simp [ind, hn0]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hne1 : x / (n : ℝ) ≠ 1 := fun h => hx_not_nat n ((div_eq_one_iff_eq hn_pos.ne').mp h).symm
      simp only [ind, hn0, ↓reduceIte, ← mul_sub, norm_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (perron_vertical_integral_bound (div_pos hx hn_pos) hne1 hc hT) (norm_nonneg _)
  have hnorm_summ : Summable (fun n : ℕ =>
      ‖(if n = 0 then (0 : ℂ) else a n * perronKernel (x / (n : ℝ)) c T) - ind n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm_le herr_summ
  exact (norm_tsum_le_tsum_norm hnorm_summ).trans (hnorm_summ.tsum_le_tsum hnorm_le herr_summ)

/-- **Half-Integer Truncated Perron Formula Corollary (`x = N + 1/2`)**:
Plug-and-play form for `∑_{n=1}^N a_n` with automatic `x ∉ ℕ` and `⌊N + 1/2⌋ = N`. -/
theorem perron_truncated_formula_half_int (a : ℕ → ℂ) (N : ℕ) {c T : ℝ}
    (hc : 0 < c) (hT : 0 < T)
    (hsumm : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else ‖a n‖ * (n : ℝ) ^ (-c))) :
    ‖(1 / (2 * (Real.pi : ℂ))) *
        (∫ t in (-T)..T, LSeries a ((c : ℂ) + (t : ℂ) * Complex.I) *
          ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) /
            ((c : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.Icc 1 N, a n‖ ≤
    ∑' n : ℕ, if n = 0 then (0 : ℝ)
      else ‖a n‖ * (((N : ℝ) + 1 / 2) / (n : ℝ)) ^ c /
        (Real.pi * T * |Real.log (((N : ℝ) + 1 / 2) / (n : ℝ))|) := by
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hx_not_nat : ∀ n : ℕ, (n : ℝ) ≠ (N : ℝ) + 1 / 2 := by
    intro n heq
    have h2 : (2 * n : ℕ) = 2 * N + 1 := by
      have hr : ((2 * n : ℕ) : ℝ) = ((2 * N + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast hr
    omega
  have hfl : Nat.floor ((N : ℝ) + 1 / 2) = N := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  have h := perron_truncated_formula a hc hT hx hx_not_nat hsumm
  rwa [hfl] at h

end
end Arith4Ext.ZetaLFunctions
