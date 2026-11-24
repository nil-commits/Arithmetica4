import RHDirect.Stage7HadamardXiProduct
import RHDirect.Stage6LFunctionOrder
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Logic.Denumerable

/-!
# RHDirect.Stage8HadamardLFunction

Completely **UNCONDITIONAL** (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) formalization in
pure Mathlib `v4.33.1` of:

1. **Conjugation Symmetry, Multiplicity Symmetry, Infinitude of Zeros, & Multiplicity-Counted
   Zero Enumeration for Every Primitive `DirichletCharacter.completedLFunction χ`**:
   - `completedLFunction_conj`, `symmetricCompletedLFunction_one_sub_conj`, and
     `analyticOrderNatAt_completedLFunction_one_sub_conj`.
   - `infinite_completedLFunction_zeros`: unconditional proof that EVERY primitive
     `DirichletCharacter.completedLFunction χ` (`χ ≠ 1`) has infinitely many critical-strip zeros
     (via order-1 nonvanishing factorization + factorial growth of `Γ(n) = (n - 1)!` on both even
     and odd characters).
   - `completedLZeroSeq hprim hχ : ℕ → ℂ`: exact multiplicity-counted enumeration of ALL zeros of
     `completedLFunction χ`, with `isMultiplicityZeroSeq_completedLFunction`,
     `completedLZeroSeq_summable_inv_sq`, `completedLZeroSeq_summable_rpow_neg` (`σ > 1`), and
     functional-equation involution symmetry `completedLZeroSeq_symm_perm`.

2. **Unconditional Hadamard Product, Partial-Fraction Formula, & Exact Davenport `Re(B_χ)`
   Identity for Every Primitive `completedLFunction χ` and `symmetricCompletedLFunction χ`**:
   - `completedLFunction_hadamard_product` & `completedLFunction_hadamard_canonical`:
     `∃ a b : ℂ, ∀ s : ℂ, completedLFunction χ s = Complex.exp (a + b * s) * weierstrassProduct (completedLZeroSeq hprim hχ) s`
     (with canonical `b = completedLHadamardB χ = deriv (completedLFunction χ) 0 / completedLFunction χ 0`).
   - `completedLFunction_logDeriv_hadamard`:
     `∀ s : ℂ, completedLFunction χ s ≠ 0 → deriv (completedLFunction χ) s / completedLFunction χ s = completedLHadamardB χ + ∑' n, (1 / (s - ρ n) + 1 / ρ n)`.
   - Exact Davenport Real-Part Formulas:
     - `symmetricCompletedLFunction_hadamard_davenport_B`:
       `(symmetricCompletedLHadamardB χ).re = -∑' n, (ρ n)⁻¹.re` and
       `symmetricCompletedLFunction_re_logDeriv_eq_tsum`:
       `(deriv Λ_sym s / Λ_sym s).re = ∑' n, (1 / (s - ρ n)).re` (`1 < s.re`),
     - `completedLFunction_hadamard_davenport_B`:
       `(completedLHadamardB χ).re = -(1 / 2) * Real.log q - ∑' n, (ρ n)⁻¹.re` (matching Mathlib's
       exact `completedLFunction_one_sub` scaling) and
       `completedLFunction_hadamard_davenport_B_pi_normalized`:
       `(completedLHadamardB χ + Real.log π / 2).re = -(1 / 2) * Real.log (q / π) - ∑' n, (ρ n)⁻¹.re`
       (Davenport's classical normalization).

3. **Unconditional Digamma Strip Bound, Exact `-ζ'/ζ` & `-L'/L` Partial-Fraction Bounds, &
   0-Assumption Discharge of `Stage3ZeroFreeRegion.HadamardLogDerivPackage`**:
   - `norm_digamma_strip_le`: unconditional `‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2)` on
     `1 / 2 ≤ w.re ≤ 3 / 2` via `exists_holomorphic_log_ball` + Stirling + `borelCaratheodory_deriv_le`.
   - `norm_negLogDerivL_sub_primitive_le_log`: unconditional Euler-factor reduction
     `‖negLogDerivL χ s - negLogDerivL χ.primitiveCharacter s‖ ≤ Real.log q` for ALL `χ` and `1 < s.re`.
   - `hadamardPartialFractionSystem_unconditional` & `hadamardLogDerivPackage_unconditional`:
     complete **0-ASSUMPTION** discharge of `Stage5JensenHadamard.HadamardPartialFractionSystem` and
     `Stage3ZeroFreeRegion.HadamardLogDerivPackage`, yielding concrete uniform real-part
     partial-fraction inequalities for Mathlib's `riemannZeta` AND every `DirichletCharacter.LFunction`,
     plus unconditional classical zero-free regions and Landau–Page exceptional zero isolation!
-/

noncomputable section

open Complex DirichletCharacter Finset Filter Topology Metric
open scoped BigOperators Real ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage8HadamardLFunction

open RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage5JensenHadamard
open RHDirect.Stage5ZetaZeroFree
open RHDirect.Stage6LFunctionOrder
open RHDirect.Stage7HadamardXiProduct
open RHDirect.Stage3ZeroFreeRegion

/-! ## Section 1: Conjugation, Functional-Equation Symmetry, & Infinitude of Zeros -/

/-- Parity preservation for odd characters under character inversion: `χ⁻¹.Odd ↔ χ.Odd`. -/
theorem odd_inv_iff {q : ℕ} (χ : DirichletCharacter ℂ q) : χ⁻¹.Odd ↔ χ.Odd := by
  change χ⁻¹ (-1) = -1 ↔ χ (-1) = -1
  have hmul : χ (-1) * χ⁻¹ (-1) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply isUnit_one.neg]
  constructor
  · intro h
    rw [h] at hmul
    linear_combination -hmul
  · intro h
    rw [h] at hmul
    linear_combination -hmul

/-- Complex conjugation symmetry of `Complex.Gammaℝ`: `Gammaℝ (conj w) = conj (Gammaℝ w)`. -/
theorem Gammaℝ_conj (w : ℂ) :
    Complex.Gammaℝ (starRingEnd ℂ w) = starRingEnd ℂ (Complex.Gammaℝ w) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    rw [Complex.cpow_def_of_ne_zero hpiC, Complex.cpow_def_of_ne_zero hpiC, ← Complex.exp_conj,
      map_mul, ← Complex.ofReal_log Real.pi_pos.le, Complex.conj_ofReal, map_div₀, map_neg,
      map_ofNat]
  · have hdiv : starRingEnd ℂ w / 2 = starRingEnd ℂ (w / 2) := by rw [map_div₀, map_ofNat]
    rw [hdiv, Complex.Gamma_conj]

/-- Complex conjugation symmetry of `DirichletCharacter.gammaFactor`:
`gammaFactor χ⁻¹ (conj s) = conj (gammaFactor χ s)`. -/
theorem gammaFactor_conj {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    DirichletCharacter.gammaFactor χ⁻¹ (starRingEnd ℂ s) =
      starRingEnd ℂ (DirichletCharacter.gammaFactor χ s) := by
  rcases χ.even_or_odd with he | ho
  · have he' : χ⁻¹.Even := (even_inv_iff χ).mpr he
    rw [he'.gammaFactor_def, he.gammaFactor_def, Gammaℝ_conj]
  · have ho' : χ⁻¹.Odd := (odd_inv_iff χ).mpr ho
    rw [ho'.gammaFactor_def, ho.gammaFactor_def]
    have h1 : starRingEnd ℂ s + 1 = starRingEnd ℂ (s + 1) := by simp
    rw [h1, Gammaℝ_conj]

/-- **Global Conjugation Symmetry of `DirichletCharacter.completedLFunction`**:
for every non-principal `χ ≠ 1` and all `s : ℂ`,
`completedLFunction χ⁻¹ (conj s) = conj (completedLFunction χ s)`. -/
theorem completedLFunction_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ⁻¹ (starRingEnd ℂ s) =
      starRingEnd ℂ (DirichletCharacter.completedLFunction χ s) := by
  have hχinv : χ⁻¹ ≠ 1 := inv_ne_one_of_ne_one hχ
  let f₁ : ℂ → ℂ := DirichletCharacter.completedLFunction χ⁻¹
  let f₂ : ℂ → ℂ := fun z => starRingEnd ℂ (DirichletCharacter.completedLFunction χ (starRingEnd ℂ z))
  have hf₁_an : AnalyticOnNhd ℂ f₁ Set.univ :=
    (differentiable_completedLFunction_prim hχinv).differentiableOn.analyticOnNhd isOpen_univ
  have hf₂_diff : Differentiable ℂ f₂ := fun z =>
    (RHDirect.hasDerivAt_conj_conj
      ((differentiable_completedLFunction_prim hχ) (starRingEnd ℂ z)).hasDerivAt).differentiableAt
  have hf₂_an : AnalyticOnNhd ℂ f₂ Set.univ :=
    hf₂_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hev : f₁ =ᶠ[𝓝 (2 : ℂ)] f₂ := by
    refine Filter.eventually_of_mem
      ((Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : (0 : ℝ) < (2 : ℂ).re))
      fun z (hz : 0 < z.re) => ?_
    have hzc : 0 < (starRingEnd ℂ z).re := by simpa using hz
    dsimp only [f₁, f₂]
    rw [completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ⁻¹ hz,
      completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hzc,
      map_mul, ← RHDirect.LFunction_conj χ (.inl hχ), ← gammaFactor_conj χ, Complex.conj_conj]
  have heq : Set.EqOn f₁ f₂ Set.univ :=
    hf₁_an.eqOn_of_preconnected_of_eventuallyEq hf₂_an isPreconnected_univ (Set.mem_univ 2) hev
  have h := heq (Set.mem_univ (starRingEnd ℂ s))
  simpa [f₁, f₂] using h

/-- **Global Conjugation Symmetry of `symmetricCompletedLFunction`**:
for every non-principal `χ ≠ 1` and all `s : ℂ`,
`symmetricCompletedLFunction χ⁻¹ (conj s) = conj (symmetricCompletedLFunction χ s)`. -/
theorem symmetricCompletedLFunction_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (s : ℂ) :
    symmetricCompletedLFunction χ⁻¹ (starRingEnd ℂ s) =
      starRingEnd ℂ (symmetricCompletedLFunction χ s) := by
  unfold symmetricCompletedLFunction
  rw [map_mul, completedLFunction_conj hχ, RHDirect.natCast_cpow_conj, map_div₀, map_ofNat]

/-- **Self-Conjugation Functional Equation for `completedLFunction`**:
`completedLFunction χ (1 - conj s) = q ^ (conj s - 1 / 2) * rootNumber χ * conj (completedLFunction χ s)`. -/
theorem completedLFunction_one_sub_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - starRingEnd ℂ s) =
      (q : ℂ) ^ (starRingEnd ℂ s - 1 / 2) * DirichletCharacter.rootNumber χ *
        starRingEnd ℂ (DirichletCharacter.completedLFunction χ s) := by
  rw [hprim.completedLFunction_one_sub (starRingEnd ℂ s), completedLFunction_conj hχ]

/-- **Exact Self-Conjugation Functional Equation for `symmetricCompletedLFunction`**:
`Λ_sym(χ, 1 - conj s) = rootNumber χ * conj (Λ_sym(χ, s))` for all `s : ℂ`. -/
theorem symmetricCompletedLFunction_one_sub_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (s : ℂ) :
    symmetricCompletedLFunction χ (1 - starRingEnd ℂ s) =
      DirichletCharacter.rootNumber χ * starRingEnd ℂ (symmetricCompletedLFunction χ s) := by
  rw [symmetricCompletedLFunction_one_sub hprim (starRingEnd ℂ s),
    symmetricCompletedLFunction_conj hχ]

/-- Helper: holomorphic derivative of `z ↦ conj (h (1 - conj z))`. -/
private lemma hasDerivAt_conj_comp_one_sub_conj {h : ℂ → ℂ} {w : ℂ}
    (hh : DifferentiableAt ℂ h (1 - starRingEnd ℂ w)) :
    HasDerivAt (fun z : ℂ => starRingEnd ℂ (h (1 - starRingEnd ℂ z)))
      (-(starRingEnd ℂ (deriv h (1 - starRingEnd ℂ w)))) w := by
  have hd : HasDerivAt h (deriv h (1 - starRingEnd ℂ w)) (1 - starRingEnd ℂ w) := hh.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd ⊢
  have hmap_cont : Continuous (fun t : ℂ => -starRingEnd ℂ t) := Complex.continuous_conj.neg
  have hmap_nhds : Tendsto (fun t : ℂ => -starRingEnd ℂ t) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using (hmap_cont.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact neg_ne_zero.mpr ((map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr ht)
  have hcomp : Tendsto (fun t : ℂ =>
      -(starRingEnd ℂ ((-starRingEnd ℂ t)⁻¹ •
        (h (1 - starRingEnd ℂ w + (-starRingEnd ℂ t)) - h (1 - starRingEnd ℂ w)))))
      (𝓝[≠] (0 : ℂ)) (𝓝 (-(starRingEnd ℂ (deriv h (1 - starRingEnd ℂ w))))) :=
    (Complex.continuous_conj.neg.tendsto _).comp (hd.comp hmap_nhds)
  refine hcomp.congr fun t => ?_
  have harg : 1 - starRingEnd ℂ (w + t) = 1 - starRingEnd ℂ w + (-starRingEnd ℂ t) := by
    rw [map_add]; ring
  rw [harg]
  simp only [smul_eq_mul, map_mul, map_inv₀, map_neg, map_sub, Complex.conj_conj]
  ring

/-- **Exact Logarithmic-Derivative Reflection Identity for `symmetricCompletedLFunction`**:
`deriv Λ_sym (1 - conj s) / Λ_sym (1 - conj s) = -conj (deriv Λ_sym s / Λ_sym s)`! -/
theorem logDeriv_symmetricCompletedLFunction_one_sub_conj {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : symmetricCompletedLFunction χ s ≠ 0) :
    deriv (symmetricCompletedLFunction χ) (1 - starRingEnd ℂ s) /
        symmetricCompletedLFunction χ (1 - starRingEnd ℂ s) =
      -starRingEnd ℂ (deriv (symmetricCompletedLFunction χ) s /
        symmetricCompletedLFunction χ s) := by
  let Lsym : ℂ → ℂ := symmetricCompletedLFunction χ
  let ε : ℂ := DirichletCharacter.rootNumber χ
  have hε_ne : ε ≠ 0 := rootNumber_ne_zero hprim
  have hLsym_diff : Differentiable ℂ Lsym := differentiable_symmetricCompletedLFunction hχ
  have h1 : HasDerivAt (fun z => starRingEnd ℂ (Lsym (1 - starRingEnd ℂ z)))
      (-(starRingEnd ℂ (deriv Lsym (1 - starRingEnd ℂ s)))) s :=
    hasDerivAt_conj_comp_one_sub_conj (hLsym_diff (1 - starRingEnd ℂ s))
  have hfun : (fun z => starRingEnd ℂ (Lsym (1 - starRingEnd ℂ z))) =
      fun z => starRingEnd ℂ ε * Lsym z := by
    funext z
    dsimp only [Lsym, ε]
    rw [symmetricCompletedLFunction_one_sub_conj hprim hχ z, map_mul, Complex.conj_conj]
  have h2 : HasDerivAt (fun z => starRingEnd ℂ (Lsym (1 - starRingEnd ℂ z)))
      (starRingEnd ℂ ε * deriv Lsym s) s := by
    rw [hfun]
    exact (hLsym_diff s).hasDerivAt.const_mul (starRingEnd ℂ ε)
  have hderiv_eq : -(starRingEnd ℂ (deriv Lsym (1 - starRingEnd ℂ s))) =
      starRingEnd ℂ ε * deriv Lsym s := h1.unique h2
  have hderiv_conj := congrArg (starRingEnd ℂ) hderiv_eq
  simp only [map_neg, map_mul, Complex.conj_conj] at hderiv_conj
  have hderiv_val : deriv Lsym (1 - starRingEnd ℂ s) = -(ε * starRingEnd ℂ (deriv Lsym s)) := by
    linear_combination -hderiv_conj
  have hval : Lsym (1 - starRingEnd ℂ s) = ε * starRingEnd ℂ (Lsym s) :=
    symmetricCompletedLFunction_one_sub_conj hprim hχ s
  change deriv Lsym (1 - starRingEnd ℂ s) / Lsym (1 - starRingEnd ℂ s) =
    -starRingEnd ℂ (deriv Lsym s / Lsym s)
  rw [hderiv_val, hval, map_div₀]
  have hLsyms_conj : starRingEnd ℂ (Lsym s) ≠ 0 :=
    (map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr hs
  field_simp [hε_ne, hLsyms_conj]

/-- Helper: an entire function not vanishing at `0` has finite analytic order everywhere. -/
private lemma analyticOrderAt_ne_top_of_entire_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro htop
  have hev : ∀ᶠ w in 𝓝 z, f w = 0 := analyticOrderAt_eq_top.mp htop
  have hfreq : ∃ᶠ w in 𝓝[≠] z, f w = 0 := (hev.filter_mono nhdsWithin_le_nhds).frequently
  have hf_an : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have heq : Set.EqOn f (fun _ => (0 : ℂ)) Set.univ :=
    hf_an.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const isPreconnected_univ
      (Set.mem_univ z) hfreq
  exact hf0 (heq (Set.mem_univ 0))

/-- Helper: finite product of entire functions is entire. -/
private lemma differentiable_finset_prod {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, Differentiable ℂ (F i)) :
    Differentiable ℂ (fun z => ∏ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [differentiable_const]
  | @insert a t hat ih =>
    have hfun : (fun z => ∏ i ∈ insert a t, F i z) = fun z => F a z * ∏ i ∈ t, F i z := by
      funext z; exact Finset.prod_insert hat
    rw [hfun]
    exact (hF a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- `symmetricCompletedLFunction χ` and `completedLFunction χ` have identical analytic zero
multiplicities at every `ρ : ℂ`. -/
theorem analyticOrderNatAt_symmetricCompletedLFunction_eq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (ρ : ℂ) :
    analyticOrderNatAt (symmetricCompletedLFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow_diff : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) := by
    have heq : (fun s : ℂ => (q : ℂ) ^ (s / 2)) =
        fun s : ℂ => Complex.exp (Complex.log (q : ℂ) * (s / 2)) := by
      funext s; rw [Complex.cpow_def_of_ne_zero hqC]
    rw [heq]; fun_prop
  have hpow_an : AnalyticAt ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) ρ :=
    (hpow_diff.differentiableOn.analyticOnNhd isOpen_univ) ρ (Set.mem_univ ρ)
  have hpow_ne : (q : ℂ) ^ (ρ / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hqC]; exact Complex.exp_ne_zero _
  have hc_an : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) ρ :=
    ((differentiable_completedLFunction_prim hχ).differentiableOn.analyticOnNhd isOpen_univ) ρ
      (Set.mem_univ ρ)
  have hs_an : AnalyticAt ℂ (symmetricCompletedLFunction χ) ρ :=
    ((differentiable_symmetricCompletedLFunction hχ).differentiableOn.analyticOnNhd isOpen_univ) ρ
      (Set.mem_univ ρ)
  have hc0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 := completedLFunction_zero_ne_zero hprim hχ
  have hs0 : symmetricCompletedLFunction χ 0 ≠ 0 :=
    (symmetricCompletedLFunction_eq_zero_iff χ 0).not.mpr hc0
  have hne_top_c := analyticOrderAt_ne_top_of_entire_ne_zero
    (differentiable_completedLFunction_prim hχ) hc0 ρ
  have hne_top_s := analyticOrderAt_ne_top_of_entire_ne_zero
    (differentiable_symmetricCompletedLFunction hχ) hs0 ρ
  obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := hc_an.analyticOrderAt_ne_top.mp hne_top_c
  rw [hs_an.analyticOrderNatAt_eq_iff hne_top_s]
  refine ⟨fun z => (q : ℂ) ^ (z / 2) * h z, hpow_an.mul hh_an, mul_ne_zero hpow_ne hh_ne, ?_⟩
  filter_upwards [hh_eq] with z hz
  unfold symmetricCompletedLFunction
  simp only [smul_eq_mul] at hz ⊢
  rw [hz]; ring

/-- **Multiplicity Symmetry of `completedLFunction χ` under `ρ ↦ 1 - conj ρ`**:
`analyticOrderNatAt (completedLFunction χ) (1 - conj ρ) = analyticOrderNatAt (completedLFunction χ) ρ`. -/
theorem analyticOrderNatAt_completedLFunction_one_sub_conj {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (ρ : ℂ) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (1 - starRingEnd ℂ ρ) =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ := by
  rw [← analyticOrderNatAt_symmetricCompletedLFunction_eq hprim hχ,
    ← analyticOrderNatAt_symmetricCompletedLFunction_eq hprim hχ]
  let Lsym : ℂ → ℂ := symmetricCompletedLFunction χ
  have hLsym_diff : Differentiable ℂ Lsym := differentiable_symmetricCompletedLFunction hχ
  have hLsym_an : ∀ z : ℂ, AnalyticAt ℂ Lsym z := fun z =>
    (hLsym_diff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hLsym0 : Lsym 0 ≠ 0 :=
    (symmetricCompletedLFunction_eq_zero_iff χ 0).not.mpr (completedLFunction_zero_ne_zero hprim hχ)
  have hne_top : ∀ z : ℂ, analyticOrderAt Lsym z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_ne_zero hLsym_diff hLsym0
  set m : ℕ := analyticOrderNatAt Lsym ρ
  obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (hLsym_an ρ).analyticOrderAt_ne_top.mp (hne_top ρ)
  obtain ⟨U, hU_sub, hU_open, hρU⟩ := _root_.eventually_nhds_iff.mp
    (hh_an.eventually_analyticAt.and hh_eq)
  set ρ' : ℂ := 1 - starRingEnd ℂ ρ
  let ψ : ℂ → ℂ := fun z => 1 - starRingEnd ℂ z
  have hψ_cont : Continuous ψ := continuous_const.sub Complex.continuous_conj
  let V : Set ℂ := ψ ⁻¹' U
  have hV_open : IsOpen V := hU_open.preimage hψ_cont
  have hρ'V : ρ' ∈ V := by
    change 1 - starRingEnd ℂ (1 - starRingEnd ℂ ρ) ∈ U
    simpa [map_sub, map_one, Complex.conj_conj] using hρU
  let ε : ℂ := DirichletCharacter.rootNumber χ
  have hε_ne : ε ≠ 0 := rootNumber_ne_zero hprim
  let h' : ℂ → ℂ := fun z => ε * (-1 : ℂ) ^ m * starRingEnd ℂ (h (ψ z))
  have hh'_diff : DifferentiableOn ℂ h' V := fun z hz => by
    have hd := hasDerivAt_conj_comp_one_sub_conj (hU_sub (ψ z) hz).1.differentiableAt
    exact (hd.const_mul (ε * (-1 : ℂ) ^ m)).differentiableAt.differentiableWithinAt
  have hh'_an : AnalyticAt ℂ h' ρ' := hh'_diff.analyticAt (hV_open.mem_nhds hρ'V)
  have hh'_ne : h' ρ' ≠ 0 := by
    dsimp only [h', ψ, ρ']
    have harg : 1 - starRingEnd ℂ (1 - starRingEnd ℂ ρ) = ρ := by
      simp [map_sub, map_one]
    rw [harg]
    exact mul_ne_zero (mul_ne_zero hε_ne (pow_ne_zero m (by norm_num)))
      ((map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr hh_ne)
  rw [(hLsym_an ρ').analyticOrderNatAt_eq_iff (hne_top ρ')]
  refine ⟨h', hh'_an, hh'_ne, ?_⟩
  filter_upwards [hV_open.mem_nhds hρ'V] with z hz
  have hLsym_symm : Lsym z = ε * starRingEnd ℂ (Lsym (ψ z)) := by
    have hz_eq : z = 1 - starRingEnd ℂ (ψ z) := by
      dsimp only [ψ]; simp [map_sub, map_one]
    conv_lhs => rw [hz_eq]
    exact symmetricCompletedLFunction_one_sub_conj hprim hχ (ψ z)
  have hfac : Lsym (ψ z) = (ψ z - ρ) ^ m * h (ψ z) := by
    simpa [smul_eq_mul] using (hU_sub (ψ z) hz).2
  rw [hLsym_symm, hfac, map_mul, map_pow, map_sub, smul_eq_mul]
  have hbase : starRingEnd ℂ (ψ z) - starRingEnd ℂ ρ = -(z - ρ') := by
    dsimp only [ψ, ρ']
    rw [map_sub, map_one, Complex.conj_conj]
    ring
  rw [hbase, neg_eq_neg_one_mul, mul_pow]
  dsimp only [h']
  ring

/-- **UNCONDITIONAL INFINITUDE OF CRITICAL-STRIP ZEROS FOR EVERY PRIMITIVE `completedLFunction χ`
(`0` ASSUMPTIONS!)**: for every `q [NeZero q]` and every primitive `χ : DirichletCharacter ℂ q`
with `χ ≠ 1`, `{s : ℂ | DirichletCharacter.completedLFunction χ s = 0}.Infinite`! -/
theorem infinite_completedLFunction_zeros {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    {s : ℂ | DirichletCharacter.completedLFunction χ s = 0}.Infinite := by
  classical
  intro hfin
  let f : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let Z : Finset ℂ := hfin.toFinset
  let Q : ℂ → ℂ := fun s => ∏ ρ ∈ Z, (s - ρ) ^ analyticOrderNatAt f ρ
  have hf_diff : Differentiable ℂ f := differentiable_completedLFunction_prim hχ
  have hQ_diff : Differentiable ℂ Q :=
    differentiable_finset_prod Z (fun ρ s => (s - ρ) ^ analyticOrderNatAt f ρ) fun ρ _ =>
      (differentiable_id.sub (differentiable_const ρ)).pow _
  have hf_an : ∀ z : ℂ, AnalyticAt ℂ f z := fun z =>
    (hf_diff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hf0 : f 0 ≠ 0 := completedLFunction_zero_ne_zero hprim hχ
  have hne_top : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_ne_zero hf_diff hf0
  -- Dividing `f` by the finite zero polynomial `Q` produces an entire nonvanishing function `g`.
  let g : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) (fun z => f z / Q z)
  have hlocal : ∀ w : ℂ, ∃ q' : ℂ → ℂ, AnalyticAt ℂ q' w ∧ q' w ≠ 0 ∧
      g =ᶠ[𝓝 w] q' ∧ f w = q' w * Q w := by
    intro w
    obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (hf_an w).analyticOrderAt_ne_top.mp (hne_top w)
    have hQ_loc : ∃ Q₁ : ℂ → ℂ, AnalyticAt ℂ Q₁ w ∧ Q₁ w ≠ 0 ∧
        ∀ z : ℂ, Q z = (z - w) ^ analyticOrderNatAt f w * Q₁ z := by
      by_cases hwZ : w ∈ Z
      · refine ⟨fun z => ∏ ρ ∈ Z.erase w, (z - ρ) ^ analyticOrderNatAt f ρ, ?_, ?_, fun z => ?_⟩
        · exact (differentiable_finset_prod (Z.erase w) (fun ρ z => (z - ρ) ^ analyticOrderNatAt f ρ)
            fun ρ _ => (differentiable_id.sub (differentiable_const ρ)).pow _).differentiableOn.analyticAt
            Filter.univ_mem
        · refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
            pow_ne_zero _ (sub_ne_zero.mpr (Finset.mem_erase.mp hρ).1.symm)
        · exact (Finset.mul_prod_erase Z (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ) hwZ).symm
      · have hfw_ne : f w ≠ 0 := fun hw0 => hwZ (hfin.mem_toFinset.mpr hw0)
        have hord0 : analyticOrderNatAt f w = 0 := by
          have h0 : analyticOrderAt f w = 0 := (hf_an w).analyticOrderAt_eq_zero.mpr hfw_ne
          simp [analyticOrderNatAt, h0]
        refine ⟨Q, hQ_diff.differentiableOn.analyticAt Filter.univ_mem, ?_, fun z => by simp [hord0]⟩
        refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
          pow_ne_zero _ (sub_ne_zero.mpr fun heq => hwZ (heq ▸ hρ))
    obtain ⟨Q₁, hQ₁_an, hQ₁_ne, hQ₁_eq⟩ := hQ_loc
    let q' : ℂ → ℂ := fun z => h z / Q₁ z
    have hq'_an : AnalyticAt ℂ q' w := hh_an.div hQ₁_an hQ₁_ne
    have hq'_ne : q' w ≠ 0 := div_ne_zero hh_ne hQ₁_ne
    have hev_all : ∀ᶠ z in 𝓝 w,
        f z = (z - w) ^ analyticOrderNatAt f w * h z ∧
        Q₁ z ≠ 0 ∧ ContinuousAt q' z := by
      filter_upwards [hh_eq, hQ₁_an.continuousAt.eventually_ne hQ₁_ne,
        hq'_an.eventually_analyticAt.mono fun z hz => hz.continuousAt] with z h1 h2 h3
      exact ⟨by simpa [smul_eq_mul] using h1, h2, h3⟩
    obtain ⟨U, hU_sub, hU_open, hwU⟩ := _root_.eventually_nhds_iff.mp hev_all
    have hfp : ∀ z ∈ U, z ≠ w → f z / Q z = q' z := by
      intro z hzU hzw
      obtain ⟨h1, h2, _⟩ := hU_sub z hzU
      have hpow_ne : (z - w) ^ analyticOrderNatAt f w ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzw)
      rw [h1, hQ₁_eq z]
      dsimp only [q']
      field_simp [hpow_ne, h2]
    have hg_eq : ∀ z ∈ U, g z = q' z := by
      intro z hzU
      have htend_q : Tendsto q' (𝓝[≠] z) (𝓝 (q' z)) :=
        (hU_sub z hzU).2.2.tendsto.mono_left nhdsWithin_le_nhds
      have htend_fp : Tendsto (fun u => f u / Q u) (𝓝[≠] z) (𝓝 (q' z)) := by
        refine htend_q.congr' ?_
        have hmem_U : U ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hU_open.mem_nhds hzU)
        have hmem_ne : ({w}ᶜ : Set ℂ) ∈ 𝓝[≠] z := by
          by_cases hzw : z = w
          · subst hzw; exact self_mem_nhdsWithin
          · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hzw)
        filter_upwards [Filter.inter_mem hmem_U hmem_ne] with u ⟨huU, huw⟩
        exact (hfp u huU huw).symm
      exact htend_fp.limUnder_eq
    have hfw : f w = q' w * Q w := by
      obtain ⟨h1, h2, _⟩ := hU_sub w hwU
      rw [h1, hQ₁_eq w]
      dsimp only [q']
      field_simp [h2]
    exact ⟨q', hq'_an, hq'_ne, Filter.eventually_of_mem (hU_open.mem_nhds hwU) hg_eq, hfw⟩
  have hg_diff : Differentiable ℂ g := fun w => by
    obtain ⟨q', hq'_an, _, heq, _⟩ := hlocal w
    exact hq'_an.differentiableAt.congr_of_eventuallyEq heq
  have hg_nz : ∀ w : ℂ, g w ≠ 0 := fun w => by
    obtain ⟨q', _, hq'_ne, heq, _⟩ := hlocal w; rwa [heq.self_of_nhds]
  have hf_eq_gQ : ∀ w : ℂ, f w = g w * Q w := fun w => by
    obtain ⟨q', _, _, heq, hfw⟩ := hlocal w; rwa [heq.self_of_nhds]
  -- Order-1 growth bound for `g` from `hasOrderOneGrowth_completedLFunction`.
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  set A : ℝ := 15 * (2 * Real.log (q : ℝ) + 1)
  set B : ℝ := 15 * Real.log (3 * (q : ℝ)) + 8
  have hA_nn : 0 ≤ A := by dsimp only [A]; positivity
  have hf_ord := (hasOrderOneGrowth_completedLFunction hprim hχ).2
  set M_nat : ℕ := Z.sup (fun ρ => ⌈‖ρ‖⌉₊)
  set R₀ : ℝ := (M_nat : ℝ) + 2
  have hR₀_ge2 : 2 ≤ R₀ := by dsimp only [R₀]; linarith [Nat.cast_nonneg (α := ℝ) M_nat]
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) R₀).exists_bound_of_continuousOn
    hg_diff.continuous.continuousOn
  set B' : ℝ := max B (Real.log (max M₀ 1))
  have hg_bd : ∀ s : ℂ, ‖g s‖ ≤ Real.exp (A * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B') := by
    intro s
    have hlog_nn : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
    have hA_term_nn : 0 ≤ A * (‖s‖ + 2) * Real.log (‖s‖ + 2) := by positivity
    by_cases hs : ‖s‖ ≤ R₀
    · have h1 : ‖g s‖ ≤ max M₀ 1 :=
        (hM₀ s (mem_closedBall_zero_iff.mpr hs)).trans (le_max_left M₀ 1)
      have h2 : max M₀ 1 ≤ Real.exp B' := by
        rw [← Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right M₀ 1))]
        exact Real.exp_le_exp.mpr (le_max_right B _)
      exact h1.trans (h2.trans (Real.exp_le_exp.mpr (by linarith)))
    · push Not at hs
      have hQ_ge1 : (1 : ℝ) ≤ ‖Q s‖ := by
        dsimp only [Q]
        rw [norm_prod]
        have hfac : ∀ ρ ∈ Z, (1 : ℝ) ≤ ‖(s - ρ) ^ analyticOrderNatAt f ρ‖ := by
          intro ρ hρ
          rw [norm_pow]
          refine one_le_pow₀ ?_
          have hρ_le : ‖ρ‖ ≤ (M_nat : ℝ) := by
            have h1 : ‖ρ‖ ≤ (⌈‖ρ‖⌉₊ : ℝ) := Nat.le_ceil ‖ρ‖
            have h2 : ⌈‖ρ‖⌉₊ ≤ M_nat := Finset.le_sup (f := fun x => ⌈‖x‖⌉₊) hρ
            exact h1.trans (by exact_mod_cast h2)
          have htri : ‖s‖ - ‖ρ‖ ≤ ‖s - ρ‖ := norm_sub_norm_le s ρ
          dsimp only [R₀] at hs
          linarith
        simpa using Finset.prod_le_prod (fun _ _ => zero_le_one) hfac
      have hgn : ‖g s‖ ≤ ‖f s‖ := by
        rw [hf_eq_gQ s, norm_mul]
        have h1 : ‖g s‖ * 1 ≤ ‖g s‖ * ‖Q s‖ :=
          mul_le_mul_of_nonneg_left hQ_ge1 (norm_nonneg (g s))
        linarith
      have hle_exp : A * ‖s‖ * Real.log (‖s‖ + 2) + B ≤ A * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B' := by
        have h1 : A * ‖s‖ ≤ A * (‖s‖ + 2) := mul_le_mul_of_nonneg_left (by linarith) hA_nn
        have h2 : A * ‖s‖ * Real.log (‖s‖ + 2) ≤ A * (‖s‖ + 2) * Real.log (‖s‖ + 2) :=
          mul_le_mul_of_nonneg_right h1 hlog_nn
        linarith [le_max_left B (Real.log (max M₀ 1))]
      exact hgn.trans ((hf_ord s).trans (Real.exp_le_exp.mpr hle_exp))
  obtain ⟨a, b, hab⟩ := entire_nonvanishing_order_lt_two_eq_exp_linear hg_diff hg_nz hg_bd
  -- Compare factorial lower bound at `s_n = 2*(n+2)` (even `χ`) or `2*(n+2) - 1` (odd `χ`) against `O(K^(n+2))`.
  set D : ℕ := ∑ ρ ∈ Z, analyticOrderNatAt f ρ
  set C₁ : ℝ := Real.exp a.re * (R₀ + 2) ^ D
  set K : ℝ := Real.exp ((D : ℝ) + 2 * ‖b‖)
  have hC₁_pos : 0 < C₁ := by positivity
  have hK_pos : 0 < K := Real.exp_pos _
  have hcontra_bound : ∀ n : ℕ,
      1 ≤ 4 * C₁ * (Real.pi * K) * ((Real.pi * K) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
    intro n
    set m : ℕ := n + 2
    have hm_pos : 0 < m := by positivity
    have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ m by omega)
    set s : ℂ := if χ.Even then ((2 * m : ℕ) : ℂ) else ((2 * m - 1 : ℕ) : ℂ)
    have hs_re_ge2 : 2 ≤ s.re := by
      dsimp only [s]
      split_ifs
      · simp; linarith
      · have h3 : 2 ≤ 2 * m - 1 := by omega
        simp; exact_mod_cast h3
    have hs_re_pos : 0 < s.re := by linarith
    have hs_norm_le : ‖s‖ ≤ 2 * (m : ℝ) := by
      dsimp only [s]
      split_ifs
      · rw [Complex.norm_natCast]; push_cast; linarith
      · rw [Complex.norm_natCast]
        have hle : 2 * m - 1 ≤ 2 * m := Nat.sub_le _ _
        exact_mod_cast hle
    -- Exact Gamma evaluation: `‖gammaFactor χ s‖ = (n + 1)! / π ^ m` for BOTH even and odd `χ`!
    have hgamma_norm : ‖DirichletCharacter.gammaFactor χ s‖ =
        ((n + 1).factorial : ℝ) / Real.pi ^ m := by
      have hGammaℝ_2m : ‖Complex.Gammaℝ ((2 * m : ℕ) : ℂ)‖ =
          ((n + 1).factorial : ℝ) / Real.pi ^ m := by
        rw [Complex.Gammaℝ_def, norm_mul]
        have harg1 : -((2 * m : ℕ) : ℂ) / 2 = ((-(m : ℝ)) : ℂ) := by push_cast; ring
        have harg2 : ((2 * m : ℕ) : ℂ) / 2 = ((n + 1 : ℕ) : ℂ) + 1 := by
          dsimp only [m]; push_cast; ring
        rw [harg1, harg2, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
          Complex.Gamma_nat_eq_factorial (n + 1), Complex.norm_natCast]
        simp [Real.rpow_neg Real.pi_pos.le, div_eq_mul_inv, mul_comm]
      rcases χ.even_or_odd with he | ho
      · have hs_eq : s = ((2 * m : ℕ) : ℂ) := if_pos he
        rw [he.gammaFactor_def, hs_eq, hGammaℝ_2m]
      · have hne : ¬ χ.Even := fun he => by
          have h1 : χ (-1) = 1 := he
          have h2 : χ (-1) = -1 := ho
          rw [h1] at h2; norm_num at h2
        have hs_eq : s = ((2 * m - 1 : ℕ) : ℂ) := if_neg hne
        have hs1_eq : s + 1 = ((2 * m : ℕ) : ℂ) := by
          rw [hs_eq]
          have h1 : 1 ≤ 2 * m := by omega
          have hnat : (2 * m - 1) + 1 = 2 * m := Nat.sub_add_cancel h1
          exact_mod_cast hnat
        rw [ho.gammaFactor_def, hs1_eq, hGammaℝ_2m]
    -- Lower bound `(1/4) * (n+1)! / π^m ≤ ‖f s‖`
    have hf_lower : (1 / 4 : ℝ) * (((n + 1).factorial : ℝ) / Real.pi ^ m) ≤ ‖f s‖ := by
      dsimp only [f]
      rw [completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hs_re_pos, norm_mul,
        hgamma_norm]
      exact mul_le_mul_of_nonneg_right (quarter_le_norm_LFunction_of_two_le_re χ hs_re_ge2)
        (by positivity)
    -- Upper bound `‖f s‖ ≤ C₁ * K ^ m`
    have hexp_upper : ‖Complex.exp (a + b * s)‖ ≤ Real.exp a.re * Real.exp (2 * ‖b‖ * (m : ℝ)) := by
      rw [Complex.norm_exp, Complex.add_re, Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      have h1 : (b * s).re ≤ ‖b * s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      rw [norm_mul] at h1
      have h2 : ‖b‖ * ‖s‖ ≤ ‖b‖ * (2 * (m : ℝ)) := mul_le_mul_of_nonneg_left hs_norm_le (norm_nonneg b)
      linarith
    have hQ_upper : ‖Q s‖ ≤ (R₀ + 2) ^ D * Real.exp ((D : ℝ) * (m : ℝ)) := by
      dsimp only [Q]
      rw [norm_prod]
      have hfac : ∀ ρ ∈ Z, ‖(s - ρ) ^ analyticOrderNatAt f ρ‖ ≤
          ((R₀ + 2) * Real.exp (m : ℝ)) ^ analyticOrderNatAt f ρ := by
        intro ρ hρ
        rw [norm_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
        have hρ_le : ‖ρ‖ ≤ R₀ := by
          have h1 : ‖ρ‖ ≤ (⌈‖ρ‖⌉₊ : ℝ) := Nat.le_ceil ‖ρ‖
          have h2 : ⌈‖ρ‖⌉₊ ≤ M_nat := Finset.le_sup (f := fun x => ⌈‖x‖⌉₊) hρ
          have h3 : (⌈‖ρ‖⌉₊ : ℝ) ≤ (M_nat : ℝ) := by exact_mod_cast h2
          dsimp only [R₀]; linarith
        have hm_le_exp : (m : ℝ) ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
        have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
        calc ‖s - ρ‖ ≤ ‖s‖ + ‖ρ‖ := norm_sub_le s ρ
          _ ≤ 2 * (m : ℝ) + R₀ := by linarith
          _ ≤ (R₀ + 2) * (m : ℝ) := by nlinarith
          _ ≤ (R₀ + 2) * Real.exp (m : ℝ) := mul_le_mul_of_nonneg_left hm_le_exp (by linarith)
      calc ∏ ρ ∈ Z, ‖(s - ρ) ^ analyticOrderNatAt f ρ‖
          ≤ ∏ ρ ∈ Z, ((R₀ + 2) * Real.exp (m : ℝ)) ^ analyticOrderNatAt f ρ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfac
        _ = ((R₀ + 2) * Real.exp (m : ℝ)) ^ D := by rw [← Finset.prod_pow_eq_pow_sum]
        _ = (R₀ + 2) ^ D * Real.exp ((D : ℝ) * (m : ℝ)) := by
            rw [mul_pow, ← Real.exp_nat_mul]
    have hf_upper : ‖f s‖ ≤ C₁ * K ^ m := by
      rw [hf_eq_gQ s, hab s, norm_mul]
      calc ‖Complex.exp (a + b * s)‖ * ‖Q s‖
          ≤ (Real.exp a.re * Real.exp (2 * ‖b‖ * (m : ℝ))) *
              ((R₀ + 2) ^ D * Real.exp ((D : ℝ) * (m : ℝ))) :=
            mul_le_mul hexp_upper hQ_upper (norm_nonneg _) (by positivity)
        _ = C₁ * Real.exp ((m : ℝ) * ((D : ℝ) + 2 * ‖b‖)) := by
            dsimp only [C₁]; rw [mul_mul_mul_comm, ← Real.exp_add]; congr 2; ring
        _ = C₁ * K ^ m := by dsimp only [K]; rw [Real.exp_nat_mul]
    have hcomb : ((n + 1).factorial : ℝ) / Real.pi ^ m ≤ 4 * C₁ * K ^ m := by linarith
    have hfac_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hpi_pow_pos : (0 : ℝ) < Real.pi ^ m := pow_pos Real.pi_pos m
    have hmul := (div_le_iff₀ hpi_pow_pos).mp hcomb
    have hdiv : (1 : ℝ) ≤ 4 * C₁ * K ^ m * Real.pi ^ m / ((n + 1).factorial : ℝ) :=
      (le_div_iff₀ hfac_pos).mpr (by simpa [one_mul] using hmul)
    have hrhs : 4 * C₁ * K ^ m * Real.pi ^ m / ((n + 1).factorial : ℝ) =
        4 * C₁ * (Real.pi * K) * ((Real.pi * K) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
      have hm_eq : m = (n + 1) + 1 := rfl
      rw [hm_eq, pow_succ, pow_succ, mul_pow]
      ring
    linarith
  have htend_zero : Tendsto (fun n : ℕ =>
      4 * C₁ * (Real.pi * K) * ((Real.pi * K) ^ (n + 1) / ((n + 1).factorial : ℝ))) atTop (nhds 0) := by
    have h1 := (FloorSemiring.tendsto_pow_div_factorial_atTop (Real.pi * K)).comp
      (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using h1.const_mul (4 * C₁ * (Real.pi * K))
  have hle0 : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto htend_zero (Eventually.of_forall hcontra_bound)
  linarith

/-- Finiteness of zeros of `completedLFunction χ` up to height `T` (`T ≥ 2`). -/
theorem finite_completedLFunction_zeros_le_height {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {T : ℝ} (hT : 2 ≤ T) :
    {s : ℂ | DirichletCharacter.completedLFunction χ s = 0 ∧ |s.im| ≤ T}.Finite := by
  classical
  obtain ⟨C, hC_pos, hcount⟩ := LFunction_zero_count_height_le
  by_contra hinf
  obtain ⟨Z, hZsub, hZcard⟩ := Set.Infinite.exists_subset_card_eq hinf
    (Nat.floor (C * T * Real.log ((q : ℝ) * (T + 2))) + 1)
  have hle := hcount q χ hprim hχ T hT Z (fun ρ hρ => by
    have ⟨hz, him⟩ := hZsub hρ
    obtain ⟨h0, h1, hL⟩ := (completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hχ ρ).mp hz
    exact ⟨h0, h1, hL, him⟩)
  have hgt : C * T * Real.log ((q : ℝ) * (T + 2)) < (Z.card : ℝ) := by
    rw [hZcard]; push_cast; exact Nat.lt_floor_add_one _
  linarith

/-- Countability of all zeros of `completedLFunction χ` for every primitive `χ ≠ 1`. -/
theorem countable_completedLFunction_zeros {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    {s : ℂ | DirichletCharacter.completedLFunction χ s = 0}.Countable := by
  have hunion : {s : ℂ | DirichletCharacter.completedLFunction χ s = 0} =
      ⋃ N : ℕ, {s : ℂ | DirichletCharacter.completedLFunction χ s = 0 ∧ |s.im| ≤ (N : ℝ) + 2} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨⌈|s.im|⌉₊, h, ?_⟩
      linarith [Nat.le_ceil |s.im|]
    · rintro ⟨_, h, _⟩
      exact h
  rw [hunion]
  exact Set.countable_iUnion fun N =>
    (finite_completedLFunction_zeros_le_height hprim hχ (by linarith [Nat.cast_nonneg (α := ℝ) N])).countable

/-- Type of zeros of `completedLFunction χ` paired with their multiplicity index. -/
abbrev CompletedLZeroWithMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Type :=
  Σ z : {s : ℂ // DirichletCharacter.completedLFunction χ s = 0},
    Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z.1)

lemma analyticOrderNatAt_completedLFunction_pos {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {z : ℂ} (hz : DirichletCharacter.completedLFunction χ z = 0) :
    0 < analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z := by
  have hf_diff := differentiable_completedLFunction_prim hχ
  have hf_an : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) z :=
    (hf_diff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hne_top : analyticOrderAt (DirichletCharacter.completedLFunction χ) z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_ne_zero hf_diff (completedLFunction_zero_ne_zero hprim hχ) z
  have hne0 : analyticOrderAt (DirichletCharacter.completedLFunction χ) z ≠ 0 :=
    hf_an.analyticOrderAt_ne_zero.mpr hz
  have hnat_ne : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z ≠ 0 := by
    intro h0
    have hcoe : (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) z : ℕ∞) =
        analyticOrderAt (DirichletCharacter.completedLFunction χ) z := ENat.natCast_toNat hne_top
    rw [h0, Nat.cast_zero] at hcoe
    exact hne0 hcoe.symm
  exact Nat.pos_of_ne_zero hnat_ne

/-- Canonical bijection `ℕ ≃ CompletedLZeroWithMult χ` enumerating all zeros of
`completedLFunction χ` with exact analytic multiplicity. -/
def completedLZeroEquiv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) : ℕ ≃ CompletedLZeroWithMult χ :=
  letI : Countable {s : ℂ // DirichletCharacter.completedLFunction χ s = 0} :=
    (countable_completedLFunction_zeros hprim hχ).to_subtype
  letI : Infinite {s : ℂ // DirichletCharacter.completedLFunction χ s = 0} :=
    (infinite_completedLFunction_zeros hprim hχ).to_subtype
  letI : Countable (CompletedLZeroWithMult χ) := instCountableSigma
  letI : Infinite (CompletedLZeroWithMult χ) :=
    Infinite.of_injective
      (fun z : {s : ℂ // DirichletCharacter.completedLFunction χ s = 0} =>
        ⟨z, ⟨0, analyticOrderNatAt_completedLFunction_pos hprim hχ z.2⟩⟩)
      fun _ _ h => by cases h; rfl
  letI : Encodable (CompletedLZeroWithMult χ) := Encodable.ofCountable _
  letI : Denumerable (CompletedLZeroWithMult χ) := Denumerable.ofEncodableOfInfinite _
  (Denumerable.eqv (CompletedLZeroWithMult χ)).symm

/-- **Unconditional Multiplicity-Counted Zero Enumeration `completedLZeroSeq hprim hχ : ℕ → ℂ`**
of ALL zeros of Mathlib's actual `DirichletCharacter.completedLFunction χ`. -/
def completedLZeroSeq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (n : ℕ) : ℂ :=
  (completedLZeroEquiv hprim hχ n).1.1

theorem completedLZeroSeq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (n : ℕ) :
    DirichletCharacter.completedLFunction χ (completedLZeroSeq hprim hχ n) = 0 :=
  (completedLZeroEquiv hprim hχ n).1.2

theorem completedLZeroSeq_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (n : ℕ) :
    0 < (completedLZeroSeq hprim hχ n).re ∧ (completedLZeroSeq hprim hχ n).re < 1 := by
  have h := (completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hχ
    (completedLZeroSeq hprim hχ n)).mp (completedLZeroSeq_zero hprim hχ n)
  exact ⟨h.1, h.2.1⟩

theorem completedLZeroSeq_LFunction_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (n : ℕ) :
    DirichletCharacter.LFunction χ (completedLZeroSeq hprim hχ n) = 0 :=
  ((completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hχ
    (completedLZeroSeq hprim hχ n)).mp (completedLZeroSeq_zero hprim hχ n)).2.2

theorem completedLZeroSeq_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (n : ℕ) :
    completedLZeroSeq hprim hχ n ≠ 0 := by
  intro h
  have hpos := (completedLZeroSeq_strip hprim hχ n).1
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- `completedLZeroSeq hprim hχ` enumerates every zero of `completedLFunction χ` with its exact
analytic multiplicity `analyticOrderNatAt (completedLFunction χ) w`. -/
theorem isMultiplicityZeroSeq_completedLFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    IsMultiplicityZeroSeq (DirichletCharacter.completedLFunction χ)
      (completedLZeroSeq hprim hχ) := by
  classical
  refine ⟨completedLZeroSeq_ne_zero hprim hχ, fun w => ?_⟩
  by_cases hw : DirichletCharacter.completedLFunction χ w = 0
  · let f : Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) w) → ℕ :=
      fun j => (completedLZeroEquiv hprim hχ).symm ⟨⟨w, hw⟩, j⟩
    have hf_inj : Function.Injective f := fun _ _ h => by
      have h1 := (completedLZeroEquiv hprim hχ).symm.injective h
      cases h1; rfl
    have hset_eq : {n : ℕ | completedLZeroSeq hprim hχ n = w} = Set.range f := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_range, completedLZeroSeq, f]
      constructor
      · intro h
        refine ⟨(completedLZeroEquiv hprim hχ n).2.cast (by rw [h]), ?_⟩
        apply (completedLZeroEquiv hprim hχ).injective
        rw [Equiv.apply_symm_apply]
        refine Sigma.ext (Subtype.ext h.symm) ?_
        exact (Fin.heq_ext_iff
          (congrArg (analyticOrderNatAt (DirichletCharacter.completedLFunction χ)) h.symm)).mpr rfl
      · rintro ⟨j, rfl⟩
        simp
    refine ⟨by rw [hset_eq]; exact Set.finite_range f, fun F hF => ?_⟩
    have hF_eq : F = Finset.univ.image f := by
      ext n
      rw [hF n, Finset.mem_image]
      have hmem : n ∈ {m : ℕ | completedLZeroSeq hprim hχ m = w} ↔ n ∈ Set.range f := by
        rw [hset_eq]
      simpa using hmem
    rw [hF_eq, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  · have hf_an : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) w :=
      ((differentiable_completedLFunction_prim hχ).differentiableOn.analyticOnNhd isOpen_univ) w
        (Set.mem_univ w)
    have hord0 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) w = 0 := by
      have h0 : analyticOrderAt (DirichletCharacter.completedLFunction χ) w = 0 :=
        hf_an.analyticOrderAt_eq_zero.mpr hw
      simp [analyticOrderNatAt, h0]
    have hempty : {n : ℕ | completedLZeroSeq hprim hχ n = w} = ∅ := by
      ext n; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact hw (h ▸ completedLZeroSeq_zero hprim hχ n)
    refine ⟨by rw [hempty]; exact Set.finite_empty, fun F hF => ?_⟩
    have hFe : F = ∅ := by
      ext n; simp only [hF n, Finset.notMem_empty, iff_false]
      intro h; exact hw (h ▸ completedLZeroSeq_zero hprim hχ n)
    rw [hFe, Finset.card_empty, hord0]

/-- **Unconditional Convergence-Exponent Summability (`σ > 1`) of `completedLZeroSeq`**
(counted with multiplicity!). -/
theorem completedLZeroSeq_summable_rpow_neg {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖completedLZeroSeq hprim hχ n‖ ^ (-σ)) := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  set A : ℝ := 15 * (2 * Real.log (q : ℝ) + 1)
  set B : ℝ := 15 * Real.log (3 * (q : ℝ)) + 8
  have hA_nn : 0 ≤ A := by dsimp only [A]; positivity
  set C₀ : ℝ :=
    (4 * A + max B 0 + max (-Real.log ‖DirichletCharacter.completedLFunction χ 0‖) 0) / Real.log 2
  have hC₀ : 0 ≤ C₀ := div_nonneg
    (by linarith [le_max_right B 0, le_max_right (-Real.log ‖DirichletCharacter.completedLFunction χ 0‖) 0])
    (Real.log_pos (by norm_num)).le
  exact Stage5JensenHadamard.summable_rpow_neg_of_zero_counting hC₀
    (completedLZeroSeq_ne_zero hprim hχ)
    (order_one_multiplicity_zero_count_le hA_nn
      (hasOrderOneGrowth_completedLFunction hprim hχ)
      (completedLFunction_zero_ne_zero hprim hχ)
      (isMultiplicityZeroSeq_completedLFunction hprim hχ)) hσ

/-- **Unconditional Inverse-Square Summability of `completedLZeroSeq`** (counted with multiplicity!). -/
theorem completedLZeroSeq_summable_inv_sq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun n : ℕ => (‖completedLZeroSeq hprim hχ n‖ ^ 2)⁻¹) := by
  have h := completedLZeroSeq_summable_rpow_neg hprim hχ (σ := 2) (by norm_num)
  refine h.congr fun n => ?_
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two]

/-- **Functional-Equation Permutation Symmetry of `completedLZeroSeq`**:
there exists a permutation `τ : Equiv.Perm ℕ` such that
`∀ n, completedLZeroSeq hprim hχ (τ n) = 1 - starRingEnd ℂ (completedLZeroSeq hprim hχ n)`. -/
theorem completedLZeroSeq_symm_perm {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ τ : Equiv.Perm ℕ, ∀ n : ℕ,
      completedLZeroSeq hprim hχ (τ n) = 1 - starRingEnd ℂ (completedLZeroSeq hprim hχ n) := by
  have hzero_symm : ∀ s : ℂ, DirichletCharacter.completedLFunction χ s = 0 →
      DirichletCharacter.completedLFunction χ (1 - starRingEnd ℂ s) = 0 := fun s hs => by
    rw [completedLFunction_one_sub_conj hprim hχ s, hs, map_zero, mul_zero]
  let f : CompletedLZeroWithMult χ → CompletedLZeroWithMult χ := fun x =>
    ⟨⟨1 - starRingEnd ℂ x.1.1, hzero_symm x.1.1 x.1.2⟩,
      x.2.cast (analyticOrderNatAt_completedLFunction_one_sub_conj hprim hχ x.1.1).symm⟩
  have hf_inv : Function.Involutive f := by
    intro ⟨⟨s, hs⟩, j⟩
    dsimp only [f]
    have hs' : 1 - starRingEnd ℂ (1 - starRingEnd ℂ s) = s := by
      simp [map_sub, map_one]
    refine Sigma.ext (Subtype.ext hs') ?_
    exact (Fin.heq_ext_iff
      (congrArg (analyticOrderNatAt (DirichletCharacter.completedLFunction χ)) hs')).mpr rfl
  let f_perm : Equiv.Perm (CompletedLZeroWithMult χ) := hf_inv.toPerm f
  let e := completedLZeroEquiv hprim hχ
  refine ⟨e.trans (f_perm.trans e.symm), fun n => ?_⟩
  simp only [completedLZeroSeq, Equiv.trans_apply, Equiv.apply_symm_apply, f_perm,
    Function.Involutive.coe_toPerm, f, e]

/-! ## Section 2: Unconditional Hadamard Product, Partial Fractions, & Exact Davenport `Re(B_χ)` -/

/-- Canonical Hadamard exponential constant `B_χ = Λ'(χ, 0) / Λ(χ, 0)` for Mathlib's
`DirichletCharacter.completedLFunction χ`. -/
def completedLHadamardB {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (DirichletCharacter.completedLFunction χ) 0 / DirichletCharacter.completedLFunction χ 0

/-- Canonical Hadamard exponential constant `B_sym(χ) = Λ_sym'(χ, 0) / Λ_sym(χ, 0)` for
`symmetricCompletedLFunction χ`. -/
def symmetricCompletedLHadamardB {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (symmetricCompletedLFunction χ) 0 / symmetricCompletedLFunction χ 0

/-- Exact logarithmic derivative shift between `symmetricCompletedLFunction χ` and
`completedLFunction χ`:
`Λ_sym'(χ, s) / Λ_sym(χ, s) = (Real.log q / 2) + Λ'(χ, s) / Λ(χ, s)`. -/
theorem logDeriv_symmetricCompletedLFunction_eq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    deriv (symmetricCompletedLFunction χ) s / symmetricCompletedLFunction χ s =
      ((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
        deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow_eq : (fun w : ℂ => (q : ℂ) ^ (w / 2)) =
      fun w : ℂ => Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * w) := by
    funext w
    rw [Complex.cpow_def_of_ne_zero hqC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hq_pos.le]
    congr 1; push_cast; ring
  have hpow_deriv : HasDerivAt (fun w : ℂ => (q : ℂ) ^ (w / 2))
      (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * (q : ℂ) ^ (s / 2)) s := by
    rw [hpow_eq, congrFun hpow_eq s]
    have hlin : HasDerivAt (fun w : ℂ => ((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * w)
        ((Real.log (q : ℝ) / 2 : ℝ) : ℂ) s := by
      simpa using (hasDerivAt_id s).const_mul ((Real.log (q : ℝ) / 2 : ℝ) : ℂ)
    simpa [mul_comm] using hlin.cexp
  have hc_deriv : HasDerivAt (DirichletCharacter.completedLFunction χ)
      (deriv (DirichletCharacter.completedLFunction χ) s) s :=
    ((differentiable_completedLFunction_prim hχ) s).hasDerivAt
  have hsym_deriv : HasDerivAt (symmetricCompletedLFunction χ)
      (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * (q : ℂ) ^ (s / 2) *
          DirichletCharacter.completedLFunction χ s +
        (q : ℂ) ^ (s / 2) * deriv (DirichletCharacter.completedLFunction χ) s) s :=
    hpow_deriv.mul hc_deriv
  have hpow_ne : (q : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hqC]; exact Complex.exp_ne_zero _
  rw [hsym_deriv.deriv]
  unfold symmetricCompletedLFunction
  field_simp [hpow_ne, hs]

/-- Exact relation between the canonical Hadamard constants of `symmetricCompletedLFunction χ` and
`completedLFunction χ`:
`symmetricCompletedLHadamardB χ = (Real.log q / 2) + completedLHadamardB χ`. -/
theorem symmetricCompletedLHadamardB_eq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    symmetricCompletedLHadamardB χ =
      ((Real.log (q : ℝ) / 2 : ℝ) : ℂ) + completedLHadamardB χ :=
  logDeriv_symmetricCompletedLFunction_eq hχ (completedLFunction_zero_ne_zero hprim hχ)

/-- **UNCONDITIONAL CANONICAL HADAMARD PRODUCT FOR EVERY PRIMITIVE `completedLFunction χ`
(`0` ASSUMPTIONS!)**:
`completedLFunction χ s = completedLFunction χ 0 * exp(B_χ * s) * weierstrassProduct (completedLZeroSeq hprim hχ) s`. -/
theorem completedLFunction_hadamard_canonical {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.completedLFunction χ 0 *
        Complex.exp (completedLHadamardB χ * s) *
        weierstrassProduct (completedLZeroSeq hprim hχ) s := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  have hA_nn : 0 ≤ 15 * (2 * Real.log (q : ℝ) + 1) := by positivity
  have hf0 := completedLFunction_zero_ne_zero hprim hχ
  obtain ⟨_, a, b, hfac, hlogd⟩ := hadamard_factorization_order_one hA_nn
    (hasOrderOneGrowth_completedLFunction hprim hχ) hf0
    (isMultiplicityZeroSeq_completedLFunction hprim hχ)
  have hexpa : Complex.exp a = DirichletCharacter.completedLFunction χ 0 := by
    have h0 := hfac 0
    rw [mul_zero, add_zero, weierstrassProduct_zero, mul_one] at h0
    exact h0.symm
  have hb_eq : b = completedLHadamardB χ := by
    have h0_ne : ∀ n : ℕ, (0 : ℂ) ≠ completedLZeroSeq hprim hχ n :=
      fun n h => completedLZeroSeq_ne_zero hprim hχ n h.symm
    have hld0 := hlogd 0 h0_ne
    have hsum0 : ∑' n : ℕ, (1 / ((0 : ℂ) - completedLZeroSeq hprim hχ n) +
        1 / completedLZeroSeq hprim hχ n) = 0 := by
      simp [zero_sub, div_neg]
    rw [hsum0, add_zero] at hld0
    exact hld0.symm
  rw [hfac s, Complex.exp_add, hexpa, hb_eq]

/-- **UNCONDITIONAL HADAMARD PRODUCT FACTORIZATION OF EVERY PRIMITIVE `completedLFunction χ`
(`0` ASSUMPTIONS!)**:
`∃ a b : ℂ, ∀ s : ℂ, completedLFunction χ s = Complex.exp (a + b * s) * weierstrassProduct (completedLZeroSeq hprim hχ) s`. -/
theorem completedLFunction_hadamard_product {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ a b : ℂ, ∀ s : ℂ,
      DirichletCharacter.completedLFunction χ s =
        Complex.exp (a + b * s) * weierstrassProduct (completedLZeroSeq hprim hχ) s := by
  refine ⟨Complex.log (DirichletCharacter.completedLFunction χ 0), completedLHadamardB χ, fun s => ?_⟩
  rw [Complex.exp_add, Complex.exp_log (completedLFunction_zero_ne_zero hprim hχ)]
  exact completedLFunction_hadamard_canonical hprim hχ s

/-- **UNCONDITIONAL HADAMARD LOGARITHMIC-DERIVATIVE PARTIAL-FRACTION FORMULA FOR EVERY PRIMITIVE
`completedLFunction χ` (`0` ASSUMPTIONS!)**:
for every `s : ℂ` with `completedLFunction χ s ≠ 0`:
`deriv (completedLFunction χ) s / completedLFunction χ s = completedLHadamardB χ + ∑' n, (1 / (s - ρ n) + 1 / ρ n)`. -/
theorem completedLFunction_logDeriv_hadamard {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (s : ℂ) (hs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s =
      completedLHadamardB χ +
        ∑' n : ℕ, (1 / (s - completedLZeroSeq hprim hχ n) + 1 / completedLZeroSeq hprim hχ n) := by
  have hs_ne : ∀ n : ℕ, s ≠ completedLZeroSeq hprim hχ n :=
    fun n heq => hs (heq ▸ completedLZeroSeq_zero hprim hχ n)
  have hfun : DirichletCharacter.completedLFunction χ =
      fun w => DirichletCharacter.completedLFunction χ 0 *
        Complex.exp (completedLHadamardB χ * w) *
        weierstrassProduct (completedLZeroSeq hprim hχ) w :=
    funext (completedLFunction_hadamard_canonical hprim hχ)
  conv_lhs => rw [hfun]
  exact Stage5JensenHadamard.hadamard_canonical_logDeriv_eq
    (completedLFunction_zero_ne_zero hprim hχ)
    (completedLZeroSeq_ne_zero hprim hχ)
    (completedLZeroSeq_summable_inv_sq hprim hχ) hs_ne

/-- **UNCONDITIONAL HADAMARD LOGARITHMIC-DERIVATIVE PARTIAL-FRACTION FORMULA FOR
`symmetricCompletedLFunction χ` (`0` ASSUMPTIONS!)**. -/
theorem symmetricCompletedLFunction_logDeriv_hadamard {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (s : ℂ) (hs : symmetricCompletedLFunction χ s ≠ 0) :
    deriv (symmetricCompletedLFunction χ) s / symmetricCompletedLFunction χ s =
      symmetricCompletedLHadamardB χ +
        ∑' n : ℕ, (1 / (s - completedLZeroSeq hprim hχ n) + 1 / completedLZeroSeq hprim hχ n) := by
  have hcs : DirichletCharacter.completedLFunction χ s ≠ 0 :=
    (symmetricCompletedLFunction_eq_zero_iff χ s).not.mp hs
  rw [logDeriv_symmetricCompletedLFunction_eq hχ hcs,
    completedLFunction_logDeriv_hadamard hprim hχ s hcs,
    symmetricCompletedLHadamardB_eq hprim hχ, add_assoc]

/-- **UNCONDITIONAL EXACT DAVENPORT REAL-PART IDENTITY FOR `symmetricCompletedLFunction χ`**:
`(symmetricCompletedLHadamardB χ).re = -∑' n, (completedLZeroSeq hprim hχ n)⁻¹.re`! -/
theorem symmetricCompletedLFunction_hadamard_davenport_B {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    (symmetricCompletedLHadamardB χ).re =
      -∑' n : ℕ, (completedLZeroSeq hprim hχ n)⁻¹.re := by
  obtain ⟨τ, hτ⟩ := completedLZeroSeq_symm_perm hprim hχ
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hΛ2 : symmetricCompletedLFunction χ 2 ≠ 0 :=
    (symmetricCompletedLFunction_eq_zero_iff χ 2).not.mpr
      (completedLFunction_ne_zero_of_one_le_re hχ (by norm_num))
  have hΛ_sym : symmetricCompletedLFunction χ (1 - starRingEnd ℂ (2 : ℂ)) ≠ 0 := by
    rw [symmetricCompletedLFunction_one_sub_conj hprim hχ 2]
    exact mul_ne_zero (rootNumber_ne_zero hprim)
      ((map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr hΛ2)
  have hanti :
      (symmetricCompletedLHadamardB χ +
          ∑' n : ℕ, (1 / ((1 - starRingEnd ℂ (2 : ℂ)) - completedLZeroSeq hprim hχ n) +
            1 / completedLZeroSeq hprim hχ n)).re =
        -(symmetricCompletedLHadamardB χ +
          ∑' n : ℕ, (1 / ((2 : ℂ) - completedLZeroSeq hprim hχ n) +
            1 / completedLZeroSeq hprim hχ n)).re := by
    rw [← symmetricCompletedLFunction_logDeriv_hadamard hprim hχ _ hΛ_sym,
      ← symmetricCompletedLFunction_logDeriv_hadamard hprim hχ 2 hΛ2,
      logDeriv_symmetricCompletedLFunction_one_sub_conj hprim hχ hΛ2,
      Complex.neg_re, Complex.conj_re]
  have hdav := Stage5JensenHadamard.davenport_re_B_eq_neg_tsum_re_inv
    (completedLZeroSeq_strip hprim hχ)
    (completedLZeroSeq_summable_inv_sq hprim hχ) τ hτ hs hanti
  simpa [one_div] using hdav.1

/-- **UNCONDITIONAL EXACT REAL-PART PARTIAL-FRACTION FORMULA FOR `Λ_sym'/Λ_sym(χ, s)` ON `Re(s) > 1`**:
`(deriv (symmetricCompletedLFunction χ) s / symmetricCompletedLFunction χ s).re = ∑' n, (1 / (s - ρ n)).re`! -/
theorem symmetricCompletedLFunction_re_logDeriv_eq_tsum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (deriv (symmetricCompletedLFunction χ) s / symmetricCompletedLFunction χ s).re =
      ∑' n : ℕ, (1 / (s - completedLZeroSeq hprim hχ n)).re := by
  have hΛs : symmetricCompletedLFunction χ s ≠ 0 :=
    (symmetricCompletedLFunction_eq_zero_iff χ s).not.mpr
      (completedLFunction_ne_zero_of_one_le_re hχ hs.le)
  have hs_ne : ∀ n : ℕ, s ≠ completedLZeroSeq hprim hχ n :=
    fun n h => (completedLFunction_ne_zero_of_one_le_re hχ hs.le)
      (h ▸ completedLZeroSeq_zero hprim hχ n)
  rw [symmetricCompletedLFunction_logDeriv_hadamard hprim hχ s hΛs, Complex.add_re,
    Stage5JensenHadamard.re_tsum_hadamard_term_eq
      (completedLZeroSeq_strip hprim hχ)
      (completedLZeroSeq_summable_inv_sq hprim hχ) hs_ne,
    symmetricCompletedLFunction_hadamard_davenport_B hprim hχ]
  simp_rw [one_div]
  ring

/-- **UNCONDITIONAL EXACT DAVENPORT REAL-PART FORMULA FOR MATHLIB'S `completedLFunction χ`**:
`(completedLHadamardB χ).re = -(1 / 2) * Real.log q - ∑' n, (completedLZeroSeq hprim hχ n)⁻¹.re`
(matching Mathlib's `completedLFunction_one_sub` scaling, where `completedLFunction χ` includes
`π ^ (-(s + a) / 2)` inside `gammaFactor` and omits `q ^ (s / 2)`). -/
theorem completedLFunction_hadamard_davenport_B {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    (completedLHadamardB χ).re =
      -(1 / 2) * Real.log (q : ℝ) - ∑' n : ℕ, (completedLZeroSeq hprim hχ n)⁻¹.re := by
  have h1 := congrArg Complex.re (symmetricCompletedLHadamardB_eq hprim hχ)
  rw [Complex.add_re, Complex.ofReal_re,
    symmetricCompletedLFunction_hadamard_davenport_B hprim hχ] at h1
  linarith

/-- **Classical Davenport `q / π` Scaling Identity**:
adding `(Real.log π / 2)` (corresponding to stripping `π ^ (-(s + a) / 2)` from
`completedLFunction χ`) gives
`((completedLHadamardB χ) + (Real.log π / 2)).re = -(1 / 2) * Real.log (q / π) - ∑' n, (ρ n)⁻¹.re`. -/
theorem completedLFunction_hadamard_davenport_B_div_pi {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    (completedLHadamardB χ + ((Real.log Real.pi / 2 : ℝ) : ℂ)).re =
      -(1 / 2) * Real.log ((q : ℝ) / Real.pi) -
        ∑' n : ℕ, (completedLZeroSeq hprim hχ n)⁻¹.re := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  rw [Complex.add_re, Complex.ofReal_re, completedLFunction_hadamard_davenport_B hprim hχ,
    Real.log_div hq_pos.ne' Real.pi_pos.ne']
  ring

/-- **Exact Real-Part Partial-Fraction Formula for Mathlib's `completedLFunction χ` on `Re(s) > 1`**:
`(deriv Λ s / Λ s).re = -(1 / 2) * Real.log q + ∑' n, (1 / (s - ρ n)).re`. -/
theorem completedLFunction_re_logDeriv_eq_tsum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s).re =
      -(1 / 2) * Real.log (q : ℝ) + ∑' n : ℕ, (1 / (s - completedLZeroSeq hprim hχ n)).re := by
  have hcs := completedLFunction_ne_zero_of_one_le_re hχ hs.le
  have h1 := congrArg Complex.re (logDeriv_symmetricCompletedLFunction_eq hχ hcs)
  rw [Complex.add_re, Complex.ofReal_re,
    symmetricCompletedLFunction_re_logDeriv_eq_tsum hprim hχ hs] at h1
  linarith

/-! ## Section 3: Unconditional Digamma Strip Bound & 0-Assumption Discharge of `HadamardLogDerivPackage` -/

/-- **UNCONDITIONAL DIGAMMA VERTICAL-STRIP UPPER BOUND (`0` ASSUMPTIONS!)**:
there exists an absolute constant `C > 0` such that for EVERY `w : ℂ` with `1 / 2 ≤ w.re ≤ 3 / 2`,
`‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2)`. -/
theorem norm_digamma_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 3 / 2 →
      ‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2) := by
  obtain ⟨C₁, hC₁_pos, hStirl⟩ := norm_Gamma_strip_stirling_quarter_le 2
  set K₀ : ℝ := max (C₁ * (2 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (3 * Real.pi / 8)) 1
  have hK₀_ge1 : 1 ≤ K₀ := le_max_right _ _
  have hK₀_pos : 0 < K₀ := lt_of_lt_of_le zero_lt_one hK₀_ge1
  have hlogK₀_nn : 0 ≤ Real.log K₀ := Real.log_nonneg hK₀_ge1
  set C : ℝ := 80 * (2 * Real.log K₀ + 5 / 2)
  have hC_pos : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC_pos, fun w hw1 hw2 => ?_⟩
  set t : ℝ := w.im
  set w₀ : ℂ := (1 : ℂ) + I * (t : ℂ)
  have hball_re : ∀ z ∈ Metric.ball w₀ (3 / 4), 1 / 4 < z.re ∧ z.re < 7 / 4 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre := (Complex.abs_re_le_norm (z - w₀)).trans_lt hz
    have hdiff : (z - w₀).re = z.re - 1 := by simp [w₀]
    rw [hdiff, abs_lt] at hre
    exact ⟨by linarith, by linarith⟩
  have hball_im : ∀ z ∈ Metric.ball w₀ (3 / 4), |z.im - t| < 3 / 4 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have him := (Complex.abs_im_le_norm (z - w₀)).trans_lt hz
    have hdiff : (z - w₀).im = z.im - t := by simp [w₀]
    rwa [hdiff] at him
  have hne_neg_nat : ∀ z ∈ Metric.ball w₀ (3 / 4), ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m heq
    have hre := (hball_re z hz).1
    have hzm := congrArg Complex.re heq
    simp at hzm
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG_diff : DifferentiableOn ℂ Complex.Gamma (Metric.ball w₀ (3 / 4)) := fun z hz =>
    (Complex.differentiableAt_Gamma z (hne_neg_nat z hz)).differentiableWithinAt
  have hG_nz : ∀ z ∈ Metric.ball w₀ (3 / 4), Complex.Gamma z ≠ 0 := fun z hz =>
    Complex.Gamma_ne_zero (hne_neg_nat z hz)
  obtain ⟨L, hL0, hL_deriv, hL_exp⟩ :=
    Stage5ZetaZeroFree.exists_holomorphic_log_ball (by norm_num : (0 : ℝ) < 3 / 4) hG_diff hG_nz
  have hlogt_ge : (1 / 2 : ℝ) < Real.log (|t| + 2) := by
    have h2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    exact lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
  set M : ℝ := (2 * Real.log K₀ + 5 / 2) * Real.log (|t| + 2)
  have hcb_sub : Metric.closedBall w₀ (5 / 8) ⊆ Metric.ball w₀ (3 / 4) :=
    Metric.closedBall_subset_ball (by norm_num)
  have hL_diff_cb : DifferentiableOn ℂ L (Metric.closedBall w₀ (5 / 8)) := fun z hz =>
    (hL_deriv z (hcb_sub hz)).differentiableAt.differentiableWithinAt
  have hL_re_cb : ∀ z ∈ Metric.closedBall w₀ (5 / 8), (L z).re ≤ M := by
    intro z hz
    have hz_ball : z ∈ Metric.ball w₀ (3 / 4) := hcb_sub hz
    have hre_z := hball_re z hz_ball
    have him_z := hball_im z hz_ball
    have hst := hStirl z hre_z.1.le (by linarith : z.re ≤ 2)
    have him_up : |z.im| + 2 ≤ 2 * (|t| + 2) := by
      have htri : |z.im| ≤ |z.im - t| + |t| := by simpa [sub_add_cancel] using abs_add_le (z.im - t) t
      linarith [abs_nonneg t]
    have him_lo : |t| - 3 / 4 ≤ |z.im| := by
      have htri : |t| ≤ |z.im - t| + |z.im| := by
        have h1 : t = -(z.im - t) + z.im := by ring
        calc |t| = |-(z.im - t) + z.im| := congrArg abs h1
          _ ≤ |-(z.im - t)| + |z.im| := abs_add_le _ _
          _ = |z.im - t| + |z.im| := by rw [abs_neg]
      linarith
    have hpow_le : (|z.im| + 2) ^ ((2 : ℝ) + 1 / 2) ≤ (2 : ℝ) ^ (5 / 2 : ℝ) * (|t| + 2) ^ (5 / 2 : ℝ) := by
      have h52 : (2 : ℝ) + 1 / 2 = 5 / 2 := by norm_num
      rw [h52, ← Real.mul_rpow (by norm_num) (by linarith [abs_nonneg t])]
      exact Real.rpow_le_rpow (by linarith [abs_nonneg z.im]) him_up (by norm_num)
    have hexp_le : Real.exp (-Real.pi * |z.im| / 2) ≤
        Real.exp (3 * Real.pi / 8) * Real.exp (-Real.pi * |t| / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hnum_le : ‖Complex.Gamma z‖ ≤
        K₀ * (|t| + 2) ^ (5 / 2 : ℝ) * Real.exp (-Real.pi * |t| / 2) := by
      have hK_ge : C₁ * (2 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (3 * Real.pi / 8) ≤ K₀ := le_max_left _ _
      calc ‖Complex.Gamma z‖
          ≤ C₁ * (|z.im| + 2) ^ ((2 : ℝ) + 1 / 2) * Real.exp (-Real.pi * |z.im| / 2) := hst
        _ ≤ C₁ * ((2 : ℝ) ^ (5 / 2 : ℝ) * (|t| + 2) ^ (5 / 2 : ℝ)) *
              (Real.exp (3 * Real.pi / 8) * Real.exp (-Real.pi * |t| / 2)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hpow_le hC₁_pos.le) hexp_le
              (Real.exp_pos _).le (by positivity)
        _ = (C₁ * (2 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (3 * Real.pi / 8)) *
              (|t| + 2) ^ (5 / 2 : ℝ) * Real.exp (-Real.pi * |t| / 2) := by ring
        _ ≤ K₀ * (|t| + 2) ^ (5 / 2 : ℝ) * Real.exp (-Real.pi * |t| / 2) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hK_ge (by positivity)) (Real.exp_pos _).le
    have hden_ge : Real.exp (-Real.pi * |t| / 2) ≤ ‖Complex.Gamma w₀‖ :=
      Stage6XiZeroDensity.norm_Gamma_one_add_I_mul_ge t
    have hratio : ‖Complex.Gamma z‖ / ‖Complex.Gamma w₀‖ ≤ K₀ * (|t| + 2) ^ (5 / 2 : ℝ) := by
      rw [div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) hden_ge)]
      exact hnum_le.trans (mul_le_mul_of_nonneg_left hden_ge (by positivity))
    have hexp_norm : Real.exp (L z).re = ‖Complex.Gamma z‖ / ‖Complex.Gamma w₀‖ := by
      rw [← Complex.norm_exp, hL_exp z hz_ball, norm_div]
    have hre_eq : (L z).re = Real.log (‖Complex.Gamma z‖ / ‖Complex.Gamma w₀‖) := by
      rw [← hexp_norm, Real.log_exp]
    rw [hre_eq]
    have hratio_pos : 0 < ‖Complex.Gamma z‖ / ‖Complex.Gamma w₀‖ := by
      rw [← hexp_norm]; exact Real.exp_pos _
    calc Real.log (‖Complex.Gamma z‖ / ‖Complex.Gamma w₀‖)
        ≤ Real.log (K₀ * (|t| + 2) ^ (5 / 2 : ℝ)) := Real.log_le_log hratio_pos hratio
      _ = Real.log K₀ + (5 / 2 : ℝ) * Real.log (|t| + 2) := by
          rw [Real.log_mul hK₀_pos.ne' (by positivity), Real.log_rpow (by linarith [abs_nonneg t])]
      _ ≤ M := by dsimp only [M]; nlinarith
  have hw_dist : ‖w - w₀‖ ≤ 1 / 2 := by
    have heq : w - w₀ = ((w.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [w₀, t]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hw_ball : w ∈ Metric.ball w₀ (3 / 4) := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le (f := L) (z₀ := w₀) (z := w)
    (M := M) (R := 5 / 8) (r := 1 / 2) (by norm_num) (by norm_num) hL_diff_cb hL_re_cb hw_dist
  rw [hL0, Complex.zero_re, sub_zero] at hbc
  have hderiv_w : deriv L w = Complex.digamma w := by
    rw [(hL_deriv w hw_ball).deriv, Complex.digamma_def, logDeriv_apply]
  rw [hderiv_w] at hbc
  have hcoeff : (2 * (5 / 8 : ℝ) / (5 / 8 - 1 / 2) ^ 2) * M = C * Real.log (|t| + 2) := by
    dsimp only [C, M]; ring
  linarith

/-- Logarithmic derivative of `Complex.Gammaℝ` on `Re(w) > 0`:
`deriv Complex.Gammaℝ w / Complex.Gammaℝ w = -(Real.log π / 2) + (1 / 2) * Complex.digamma (w / 2)`. -/
theorem logDeriv_Gammaℝ {w : ℂ} (hw : 0 < w.re) :
    deriv Complex.Gammaℝ w / Complex.Gammaℝ w =
      -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (w / 2) := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hne_neg : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
    intro m heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG_ne : Complex.Gamma (w / 2) ≠ 0 := Complex.Gamma_ne_zero hne_neg
  have hpi_ne : (Real.pi : ℂ) ^ (-w / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpiC]; exact Complex.exp_ne_zero _
  have hpi_eq : (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) =
      fun z : ℂ => Complex.exp (-((Real.log Real.pi / 2 : ℝ) : ℂ) * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero hpiC, ← Complex.ofReal_log Real.pi_pos.le]
    congr 1; push_cast; ring
  have h1 : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      (-((Real.log Real.pi / 2 : ℝ) : ℂ) * (Real.pi : ℂ) ^ (-w / 2)) w := by
    rw [hpi_eq, congrFun hpi_eq w]
    have hlin : HasDerivAt (fun z : ℂ => -((Real.log Real.pi / 2 : ℝ) : ℂ) * z)
        (-((Real.log Real.pi / 2 : ℝ) : ℂ)) w := by
      simpa using (hasDerivAt_id w).const_mul (-((Real.log Real.pi / 2 : ℝ) : ℂ))
    simpa [mul_comm] using hlin.cexp
  have h2 : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
      (deriv Complex.Gamma (w / 2) * (1 / 2 : ℂ)) w := by
    have hdiv : HasDerivAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) w := by
      simpa using (hasDerivAt_id w).div_const (2 : ℂ)
    exact HasDerivAt.comp w (Complex.differentiableAt_Gamma (w / 2) hne_neg).hasDerivAt hdiv
  have hfun : Complex.Gammaℝ = fun z => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z; exact Complex.Gammaℝ_def z
  have hprod : HasDerivAt Complex.Gammaℝ
      (-((Real.log Real.pi / 2 : ℝ) : ℂ) * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) +
        (Real.pi : ℂ) ^ (-w / 2) * (deriv Complex.Gamma (w / 2) * (1 / 2 : ℂ))) w := by
    rw [hfun]; exact h1.mul h2
  rw [hprod.deriv, Complex.Gammaℝ_def, Complex.digamma_def, logDeriv_apply]
  field_simp [hpi_ne, hG_ne]

/-- Exact logarithmic derivative of `DirichletCharacter.gammaFactor χ` on `Re(s) > 0`. -/
theorem logDeriv_gammaFactor_even {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even)
    {s : ℂ} (hs : 0 < s.re) :
    deriv (DirichletCharacter.gammaFactor χ) s / DirichletCharacter.gammaFactor χ s =
      -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
    funext z; exact he.gammaFactor_def z
  rw [hfun]
  exact logDeriv_Gammaℝ hs

theorem logDeriv_gammaFactor_odd {q : ℕ} {χ : DirichletCharacter ℂ q} (ho : χ.Odd)
    {s : ℂ} (hs : 0 < s.re) :
    deriv (DirichletCharacter.gammaFactor χ) s / DirichletCharacter.gammaFactor χ s =
      -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
  have hfun : DirichletCharacter.gammaFactor χ = fun z => Complex.Gammaℝ (z + 1) := by
    funext z; exact ho.gammaFactor_def z
  rw [hfun]
  have hshift : deriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s = deriv Complex.Gammaℝ (s + 1) := by
    simpa using deriv_comp_add_const Complex.Gammaℝ (1 : ℂ) s
  rw [hshift]
  exact logDeriv_Gammaℝ (by simp; linarith)

/-- Exact partial-fraction identity for `negLogDerivZeta s = -ζ'(s) / ζ(s)` on `Re(s) > 1`,
derived unconditionally from `Stage7HadamardXiProduct.xi_logDeriv_hadamard`! -/
theorem negLogDerivZeta_eq_hadamard_partialFraction {s : ℂ} (hs : 1 < s.re) :
    negLogDerivZeta s =
      1 / (s - 1) - xiHadamardB -
        (∑' n : ℕ, (1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n)) +
        (1 / s - ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2)) := by
  have hs0_re : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs0_re
  have hs1 : s ≠ 1 := fun h => by simp [h] at hs
  have hG_ne : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0_re
  have hZ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hxi_ne : xi s ≠ 0 := xi_ne_zero_of_one_le_re hs.le
  have hG_diff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hne_neg : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m heq; have := congrArg Complex.re heq; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hfun : Complex.Gammaℝ = fun z => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) * Complex.Gamma (z / 2) := by
      funext z; rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
    rw [hfun]
    have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2))) s := by
      fun_prop
    have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
      (Complex.differentiableAt_Gamma (s / 2) hne_neg).comp s (differentiableAt_id.div_const 2)
    exact h1.mul h2
  have hZ_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hev : xi =ᶠ[𝓝 s] fun z => z * (z - 1) * Complex.Gammaℝ z * riemannZeta z := by
    filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs] with z (hz : 1 < z.re)
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz; linarith
    have hz1 : z ≠ 1 := fun h => by simp [h] at hz
    exact xi_eq_mul_Gammaℝ_mul_riemannZeta hz0 hz1 (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
  have hderiv_eq : deriv xi s =
      deriv (fun z => z * (z - 1) * Complex.Gammaℝ z * riemannZeta z) s := hev.deriv_eq
  have h1 : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have h2 : HasDerivAt (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z)
      ((1 * (s - 1) + s * 1) * Complex.Gammaℝ s + s * (s - 1) * deriv Complex.Gammaℝ s) s :=
    h1.mul hG_diff.hasDerivAt
  have h3 : HasDerivAt (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z * riemannZeta z)
      (((1 * (s - 1) + s * 1) * Complex.Gammaℝ s + s * (s - 1) * deriv Complex.Gammaℝ s) *
          riemannZeta s +
        s * (s - 1) * Complex.Gammaℝ s * deriv riemannZeta s) s :=
    h2.mul hZ_diff.hasDerivAt
  have hlogd : deriv xi s / xi s =
      1 / s + 1 / (s - 1) + deriv Complex.Gammaℝ s / Complex.Gammaℝ s +
        deriv riemannZeta s / riemannZeta s := by
    rw [hderiv_eq, h3.deriv, xi_eq_mul_Gammaℝ_mul_riemannZeta hs0 hs1 hG_ne]
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [hs0, hs1', hG_ne, hZ_ne]
  rw [xi_logDeriv_hadamard s hxi_ne, logDeriv_Gammaℝ hs0_re] at hlogd
  unfold negLogDerivZeta
  rw [neg_div]
  linear_combination hlogd

/-- Exact partial-fraction identity for primitive `negLogDerivL ψ s = -L'(ψ, s) / L(ψ, s)` on
`Re(s) > 1`, derived unconditionally from `symmetricCompletedLFunction_logDeriv_hadamard`! -/
theorem negLogDerivL_prim_eq_hadamard_partialFraction {f : ℕ} [NeZero f]
    {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    negLogDerivL ψ s =
      0 - symmetricCompletedLHadamardB ψ -
        (∑' n : ℕ, (1 / (s - completedLZeroSeq hprim hψ n) + 1 / completedLZeroSeq hprim hψ n)) +
        (((Real.log (f : ℝ) / 2 : ℝ) : ℂ) +
          deriv (DirichletCharacter.gammaFactor ψ) s / DirichletCharacter.gammaFactor ψ s) := by
  have hs0 : 0 < s.re := by linarith
  have hG_ne : DirichletCharacter.gammaFactor ψ s ≠ 0 := gammaFactor_ne_zero_of_re_pos ψ hs0
  have hL_ne : DirichletCharacter.LFunction ψ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (.inl hψ) hs.le
  have hΛ_ne : symmetricCompletedLFunction ψ s ≠ 0 :=
    (symmetricCompletedLFunction_eq_zero_iff ψ s).not.mpr
      (completedLFunction_ne_zero_of_one_le_re hψ hs.le)
  have hc_ne : DirichletCharacter.completedLFunction ψ s ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hψ hs.le
  have hG_diff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor ψ) s := by
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hGammaℝ_diff : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Complex.Gammaℝ w := by
      intro w hw
      have hne_neg : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
        intro m heq; have := congrArg Complex.re heq; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
      have hfun : Complex.Gammaℝ =
          fun z => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) * Complex.Gamma (z / 2) := by
        funext z; rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
      rw [hfun]
      have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2))) w := by
        fun_prop
      have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) w :=
        (Complex.differentiableAt_Gamma (w / 2) hne_neg).comp w (differentiableAt_id.div_const 2)
      exact h1.mul h2
    rcases ψ.even_or_odd with he | ho
    · have hfun : DirichletCharacter.gammaFactor ψ = Complex.Gammaℝ := funext he.gammaFactor_def
      rw [hfun]; exact hGammaℝ_diff s hs0
    · have hfun : DirichletCharacter.gammaFactor ψ = fun z => Complex.Gammaℝ (z + 1) :=
        funext ho.gammaFactor_def
      rw [hfun]
      exact (hGammaℝ_diff (s + 1) (by simp; linarith)).comp s (differentiableAt_id.add (differentiableAt_const 1))
  have hL_diff : DifferentiableAt ℂ (DirichletCharacter.LFunction ψ) s :=
    DirichletCharacter.differentiable_LFunction hψ s
  have hev : DirichletCharacter.completedLFunction ψ =ᶠ[𝓝 s]
      fun z => DirichletCharacter.LFunction ψ z * DirichletCharacter.gammaFactor ψ z := by
    filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs0] with z (hz : 0 < z.re)
    exact completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos ψ hz
  have hderiv_eq : deriv (DirichletCharacter.completedLFunction ψ) s =
      deriv (DirichletCharacter.LFunction ψ) s * DirichletCharacter.gammaFactor ψ s +
        DirichletCharacter.LFunction ψ s * deriv (DirichletCharacter.gammaFactor ψ) s := by
    rw [hev.deriv_eq, (hL_diff.hasDerivAt.fun_mul hG_diff.hasDerivAt).deriv]
  have hlogd_c : deriv (DirichletCharacter.completedLFunction ψ) s /
      DirichletCharacter.completedLFunction ψ s =
      deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s +
        deriv (DirichletCharacter.gammaFactor ψ) s / DirichletCharacter.gammaFactor ψ s := by
    rw [hderiv_eq, completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos ψ hs0]
    field_simp [hL_ne, hG_ne]
  have hlogd_sym := logDeriv_symmetricCompletedLFunction_eq hψ hc_ne
  rw [hlogd_c, symmetricCompletedLFunction_logDeriv_hadamard hprim hψ s hΛ_ne] at hlogd_sym
  unfold negLogDerivL
  rw [neg_div]
  linear_combination hlogd_sym

/-- **Unconditional Euler-Factor Reduction Bound (`0` ASSUMPTIONS!)**:
for EVERY modulus `q ≥ 1` (`[NeZero q]`), EVERY character `χ : DirichletCharacter ℂ q`, and EVERY
`s : ℂ` with `1 < s.re`:
`‖negLogDerivL χ s - negLogDerivL χ.primitiveCharacter s‖ ≤ Real.log q`. -/
theorem norm_negLogDerivL_sub_primitive_le_log {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ‖negLogDerivL χ s - negLogDerivL χ.primitiveCharacter s‖ ≤ Real.log (q : ℝ) := by
  classical
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
  rw [negLogDerivL_eq_LSeries χ hs, negLogDerivL_eq_LSeries ψ hs]
  have hsumχ : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) s := χ.LSeriesSummable_twist_vonMangoldt hs
  have hsumψ : LSeriesSummable (fun n => ψ n * (Λ n : ℂ)) s := ψ.LSeriesSummable_twist_vonMangoldt hs
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  unfold LSeries
  rw [← Summable.tsum_sub hsumχ hsumψ]
  set g : ℕ → ℝ := fun n => if ¬ Nat.Coprime n q then Λ n / (n : ℝ) ^ s.re else 0
  have hterm_norm : ∀ n : ℕ,
      ‖LSeries.term (fun m => χ m * (Λ m : ℂ)) s n -
        LSeries.term (fun m => ψ m * (Λ m : ℂ)) s n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, g]
    · simp only [LSeries.term, hn.ne', ↓reduceIte, g]
      by_cases hcop : Nat.Coprime n q
      · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hcop
        have hχ_eq : χ (n : ZMod q) = ψ (n : ZMod χ.conductor) := by
          obtain ⟨u, hu_eq⟩ := hu
          conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
          rw [← hu_eq, DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter
            χ.conductor_dvd_level u, hu_eq, ZMod.cast_natCast χ.conductor_dvd_level]
        rw [hχ_eq, sub_self, norm_zero, if_neg (not_not.mpr hcop)]
      · have hnu : ¬ IsUnit (n : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime n q).mp hu)
        rw [MulChar.map_nonunit _ hnu, zero_mul, zero_div, zero_sub, norm_neg, if_pos hcop,
          norm_div, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hn]
        calc ‖ψ (n : ZMod χ.conductor)‖ * Λ n / (n : ℝ) ^ s.re
            ≤ 1 * Λ n / (n : ℝ) ^ s.re :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (ψ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg)
                (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ = Λ n / (n : ℝ) ^ s.re := by rw [one_mul]
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => by
    dsimp only [g]
    split_ifs
    · exact le_rfl
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hg_summ : Summable g := by
    refine Summable.of_nonneg_of_le hg_nonneg (fun n => ?_) hsumZ.norm
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [g, LSeries.term]
    · dsimp only [g]
      split_ifs
      · exact norm_nonneg _
      · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hn]
        exact le_rfl
  have hsub_summ : Summable (fun n =>
      LSeries.term (fun m => χ m * (Λ m : ℂ)) s n -
        LSeries.term (fun m => ψ m * (Λ m : ℂ)) s n) := Summable.sub hsumχ hsumψ
  have htsum_le : ‖∑' n, (LSeries.term (fun m => χ m * (Λ m : ℂ)) s n -
        LSeries.term (fun m => ψ m * (Λ m : ℂ)) s n)‖ ≤ ∑' n, g n := by
    calc ‖∑' n, (LSeries.term (fun m => χ m * (Λ m : ℂ)) s n -
          LSeries.term (fun m => ψ m * (Λ m : ℂ)) s n)‖
        ≤ ∑' n, ‖LSeries.term (fun m => χ m * (Λ m : ℂ)) s n -
          LSeries.term (fun m => ψ m * (Λ m : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsub_summ.norm
      _ ≤ ∑' n, g n := hsub_summ.norm.tsum_le_tsum hterm_norm hg_summ
  refine htsum_le.trans ?_
  -- Bound `∑' n, g n ≤ Real.log q` identically to `norm_negLogDerivL_one_sub_negLogDerivZeta_le_log`!
  have h1 := Stage5JensenHadamard.norm_negLogDerivL_one_sub_negLogDerivZeta_le_log (q := q)
    (s := (s.re : ℂ)) (by simpa using hs)
  rw [negLogDerivL_eq_LSeries (1 : DirichletCharacter ℂ q) (by simpa using hs),
    negLogDerivZeta_eq_LSeries (by simpa using hs)] at h1
  have hsum1 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (s.re : ℂ) :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt (s := (s.re : ℂ))
      (by simpa using hs)
  have hsumZr : LSeriesSummable (fun n => (Λ n : ℂ)) (s.re : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (s.re : ℂ)) (by simpa using hs)
  unfold LSeries at h1
  rw [← Summable.tsum_sub hsum1 hsumZr] at h1
  have hterm_eq : ∀ n : ℕ,
      LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) (s.re : ℂ) n -
        LSeries.term (fun m => (Λ m : ℂ)) (s.re : ℂ) n = ((-g n : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, g]
    · simp only [LSeries.term, hn.ne', ↓reduceIte, g]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hcpow : ((n : ℂ) ^ (s.re : ℂ)) = (((n : ℝ) ^ s.re : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
      rw [hcpow]
      by_cases hcop : Nat.Coprime n q
      · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hcop
        rw [MulChar.one_apply hu, one_mul, sub_self, if_neg (not_not.mpr hcop)]
        simp
      · have hnu : ¬ IsUnit (n : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime n q).mp hu)
        rw [MulChar.map_nonunit _ hnu, zero_mul, zero_div, zero_sub, if_pos hcop]
        push_cast; ring
  simp_rw [hterm_eq] at h1
  have hcast_tsum : ∑' n : ℕ, ((-g n : ℝ) : ℂ) = (((∑' n : ℕ, (-g n)) : ℝ) : ℂ) := by
    simpa [Complex.ofRealCLM_apply] using (Complex.ofRealCLM.map_tsum hg_summ.neg).symm
  rw [hcast_tsum, tsum_neg, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (tsum_nonneg hg_nonneg)] at h1
  exact h1

/-- **UNCONDITIONAL 0-ASSUMPTION CONSTRUCTION OF `Stage5JensenHadamard.HadamardPartialFractionSystem`!** -/
theorem hadamardPartialFractionSystem_unconditional :
    ∃ B_err : ℝ, Nonempty (HadamardPartialFractionSystem B_err) := by
  obtain ⟨C_dig, hC_dig_pos, hdig⟩ := norm_digamma_strip_le
  set B_err : ℝ := C_dig + 4
  have hB_pos : 0 < B_err := by dsimp only [B_err]; linarith
  have hlog2_half : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpi_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  refine ⟨B_err, ⟨{
    B_pos := hB_pos
    zeta_rep := {
      ρ := xiZeroSeq
      hstrip := xiZeroSeq_strip
      hsum := xiZeroSeq_summable_inv_sq
      hcomplete := fun z h0 h1 hz =>
        isMultiplicityZeroSeq_xi.exists_of_eq_zero differentiable_xi (by simp)
          ((xi_eq_zero_iff_critical_strip_zeta_zero z).mpr ⟨h0, h1, hz⟩)
      B₀ := xiHadamardB
      E := fun s => 1 / s - ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2)
      hrep := fun σ t hσ1 _ => negLogDerivZeta_eq_hadamard_partialFraction (by simp [hσ1])
      hbound := fun σ t hσ1 hσ2 => ?_ }
    nonprincipal_rep := fun q _ χ hχ => ?_ }⟩⟩
  · -- Bound for `zeta_rep`
    set s : ℂ := (σ : ℂ) + I * (t : ℂ)
    have hB_cancel : xiHadamardB.re + ∑' n : ℕ, (1 / xiZeroSeq n).re = 0 := by
      simp_rw [one_div]; rw [xi_hadamard_davenport_B]; ring
    rw [hB_cancel, neg_zero, zero_add]
    have hre_E : (1 / s - ((Real.log Real.pi / 2 : ℝ) : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2)).re =
        (1 / s).re - Real.log Real.pi / 2 + (1 / 2) * (Complex.digamma (s / 2)).re := by
      simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
    rw [hre_E]
    have hinv_s : (1 / s).re ≤ 1 := by
      have hs_norm : 1 ≤ ‖s‖ := by
        have h1 := (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
        have hsre : s.re = σ := by simp [s]
        rw [hsre] at h1; linarith
      calc (1 / s).re ≤ ‖1 / s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
        _ = 1 / ‖s‖ := by rw [norm_div, norm_one]
        _ ≤ 1 := (div_le_one (by linarith)).mpr hs_norm
    have hs2_re1 : 1 / 2 ≤ (s / 2).re := by simp [s]; linarith
    have hs2_re2 : (s / 2).re ≤ 3 / 2 := by simp [s]; linarith
    have hdig_s2 := hdig (s / 2) hs2_re1 hs2_re2
    have him_s2 : |(s / 2).im| + 2 ≤ |t| + 2 := by
      have him : (s / 2).im = t / 2 := by simp [s]
      rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg t]
    have hdig_re : (Complex.digamma (s / 2)).re ≤ C_dig * Real.log (|t| + 2) :=
      ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
        (hdig_s2.trans (mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith [abs_nonneg (s / 2).im]) him_s2) hC_dig_pos.le))
    have hlogt : (1 / 2 : ℝ) < Real.log (|t| + 2) :=
      hlog2_half.trans_le (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
    dsimp only [B_err]
    nlinarith
  · -- Construct `nonprincipal_rep` for general (primitive OR imprimitive) `χ ≠ 1`!
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    set f : ℕ := χ.conductor
    set ψ : DirichletCharacter ℂ f := χ.primitiveCharacter
    have hprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hψ : ψ ≠ 1 := by
      intro h1
      dsimp only [ψ] at h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, map_one]
    have hf_le_q : f ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    refine {
      ρ := completedLZeroSeq hprim hψ
      hstrip := completedLZeroSeq_strip hprim hψ
      hsum := completedLZeroSeq_summable_inv_sq hprim hψ
      hcomplete := fun z h0 h1 hz => by
        have hLz : DirichletCharacter.LFunction ψ z = 0 :=
          (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ)).mp hz
        exact (isMultiplicityZeroSeq_completedLFunction hprim hψ).exists_of_eq_zero
          (differentiable_completedLFunction_prim hψ)
          (completedLFunction_zero_ne_zero hprim hψ)
          ((completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hψ z).mpr ⟨h0, h1, hLz⟩)
      B₀ := symmetricCompletedLHadamardB ψ
      E := fun s => ((Real.log (f : ℝ) / 2 : ℝ) : ℂ) +
        deriv (DirichletCharacter.gammaFactor ψ) s / DirichletCharacter.gammaFactor ψ s +
        (negLogDerivL χ s - negLogDerivL ψ s)
      hrep := fun σ t hσ1 _ => by
        have hprim_rep := negLogDerivL_prim_eq_hadamard_partialFraction hprim hψ
          (s := (σ : ℂ) + I * (t : ℂ)) (by simp [hσ1])
        linear_combination hprim_rep
      hbound := fun σ t hσ1 hσ2 => ?_ }
    set s : ℂ := (σ : ℂ) + I * (t : ℂ)
    have hs1 : 1 < s.re := by simp [s, hσ1]
    have hs0 : 0 < s.re := by linarith
    have hB_cancel : (symmetricCompletedLHadamardB ψ).re +
        ∑' n : ℕ, (1 / completedLZeroSeq hprim hψ n).re = 0 := by
      simp_rw [one_div]
      rw [symmetricCompletedLFunction_hadamard_davenport_B hprim hψ]
      ring
    rw [hB_cancel, neg_zero, zero_add]
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    have hf_pos : (0 : ℝ) < (f : ℝ) := Nat.cast_pos.mpr (NeZero.pos f)
    have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hlogf_le : Real.log (f : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_le_log hf_pos (by
        have hfqR : (f : ℝ) ≤ (q : ℝ) := by exact_mod_cast hf_le_q
        nlinarith [abs_nonneg t])
    have hlogq_le : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_le_log hq_pos (by nlinarith [abs_nonneg t])
    have hlogt_le : Real.log (|t| + 2) ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_le_log (by linarith [abs_nonneg t]) (by nlinarith [abs_nonneg t])
    have hlogqt_nn : 0 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg t])
    have heuler : (negLogDerivL χ s - negLogDerivL ψ s).re ≤ Real.log (q : ℝ) :=
      ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
        (norm_negLogDerivL_sub_primitive_le_log χ hs1)
    have hgamma_re :
        (deriv (DirichletCharacter.gammaFactor ψ) s / DirichletCharacter.gammaFactor ψ s).re ≤
          (1 / 2) * C_dig * Real.log (|t| + 2) := by
      rcases ψ.even_or_odd with he | ho
      · rw [logDeriv_gammaFactor_even he hs0]
        have hre : (-((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2)).re =
            -Real.log Real.pi / 2 + (1 / 2) * (Complex.digamma (s / 2)).re := by
          simp [Complex.add_re, Complex.mul_re]; ring
        rw [hre]
        have hdig_bd := hdig (s / 2) (by simp [s]; linarith) (by simp [s]; linarith)
        have him_le : |(s / 2).im| + 2 ≤ |t| + 2 := by
          have him : (s / 2).im = t / 2 := by simp [s]
          rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          linarith [abs_nonneg t]
        have h1 : (Complex.digamma (s / 2)).re ≤ C_dig * Real.log (|t| + 2) :=
          ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
            (hdig_bd.trans (mul_le_mul_of_nonneg_left
              (Real.log_le_log (by linarith [abs_nonneg (s / 2).im]) him_le) hC_dig_pos.le))
        linarith
      · rw [logDeriv_gammaFactor_odd ho hs0]
        have hre : (-((Real.log Real.pi / 2 : ℝ) : ℂ) +
            (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2)).re =
            -Real.log Real.pi / 2 + (1 / 2) * (Complex.digamma ((s + 1) / 2)).re := by
          simp [Complex.add_re, Complex.mul_re]; ring
        rw [hre]
        have hdig_bd := hdig ((s + 1) / 2) (by simp [s]; linarith) (by simp [s]; linarith)
        have him_le : |((s + 1) / 2).im| + 2 ≤ |t| + 2 := by
          have him : ((s + 1) / 2).im = t / 2 := by simp [s]
          rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          linarith [abs_nonneg t]
        have h1 : (Complex.digamma ((s + 1) / 2)).re ≤ C_dig * Real.log (|t| + 2) :=
          ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
            (hdig_bd.trans (mul_le_mul_of_nonneg_left
              (Real.log_le_log (by linarith [abs_nonneg ((s + 1) / 2).im]) him_le) hC_dig_pos.le))
        linarith
    have hre_E : (((Real.log (f : ℝ) / 2 : ℝ) : ℂ) +
        deriv (DirichletCharacter.gammaFactor ψ) s / DirichletCharacter.gammaFactor ψ s +
        (negLogDerivL χ s - negLogDerivL ψ s)).re =
        Real.log (f : ℝ) / 2 +
          (deriv (DirichletCharacter.gammaFactor ψ) s / DirichletCharacter.gammaFactor ψ s).re +
          (negLogDerivL χ s - negLogDerivL ψ s).re := by
      rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]
    rw [hre_E]
    have hdig_qt : (1 / 2) * C_dig * Real.log (|t| + 2) ≤
        (1 / 2) * C_dig * Real.log ((q : ℝ) * (|t| + 2)) :=
      mul_le_mul_of_nonneg_left hlogt_le (by positivity)
    dsimp only [B_err]
    nlinarith

/-- **UNCONDITIONAL 0-ASSUMPTION DISCHARGE OF `Stage3ZeroFreeRegion.HadamardLogDerivPackage`!**
There exists an explicit universal constant `B > 0` such that
`Stage3ZeroFreeRegion.HadamardLogDerivPackage B` holds UNCONDITIONALLY on Mathlib's actual
`riemannZeta` and EVERY `DirichletCharacter.LFunction`! -/
theorem hadamardLogDerivPackage_unconditional :
    ∃ B : ℝ, Stage3ZeroFreeRegion.HadamardLogDerivPackage B := by
  obtain ⟨B_err, ⟨H⟩⟩ := hadamardPartialFractionSystem_unconditional
  exact ⟨max B_err 1, hadamardLogDerivPackage_of_partialFractionSystem H⟩

/-- **UNCONDITIONAL UNIFORM REAL-PART PARTIAL-FRACTION INEQUALITY FOR MATHLIB'S `riemannZeta`
AND EVERY PRIMITIVE `DirichletCharacter.LFunction` (`0` ASSUMPTIONS!)**:
there exists an absolute constant `C > 0` such that for all `1 < σ ≤ 2`, `t : ℝ`, and any finite
set `F : Finset ℕ` of zero indices:
1. `Re(-ζ'/ζ(σ + i t)) ≤ C * log (|t| + 2) + Re(1 / (σ + i t - 1)) - ∑ n ∈ F, Re(1 / (σ + i t - xiZeroSeq n))`,
2. for every primitive `χ ≠ 1` mod `q`:
   `Re(-L'/L(χ, σ + i t)) ≤ C * log (q * (|t| + 2)) - ∑ n ∈ F, Re(1 / (σ + i t - completedLZeroSeq hprim hχ n))`. -/
theorem re_negLogDeriv_le_sub_finset_unconditional :
    ∃ C : ℝ, 0 < C ∧
      (∀ σ t : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
        (negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
          C * Real.log (|t| + 2) + (1 / (((σ : ℂ) + I * (t : ℂ)) - 1)).re -
            ∑ n ∈ F, (1 / (((σ : ℂ) + I * (t : ℂ)) - xiZeroSeq n)).re) ∧
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1),
        ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → ∀ F : Finset ℕ,
          (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re ≤
            C * Real.log ((q : ℝ) * (|t| + 2)) -
              ∑ n ∈ F, (1 / (((σ : ℂ) + I * (t : ℂ)) - completedLZeroSeq hprim hχ n)).re) := by
  obtain ⟨C_dig, hC_dig_pos, hdig⟩ := norm_digamma_strip_le
  set C : ℝ := C_dig + 4
  have hC_pos : 0 < C := by dsimp only [C]; linarith
  have hlog2_half : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpi_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  refine ⟨C, hC_pos, ?_, ?_⟩
  · intro σ t hσ1 hσ2 F
    set s : ℂ := (σ : ℂ) + I * (t : ℂ)
    have hs1 : 1 < s.re := by simp [s, hσ1]
    have hrep := negLogDerivZeta_eq_hadamard_partialFraction hs1
    have hM : -(xiHadamardB.re + ∑' n : ℕ, (1 / xiZeroSeq n).re) +
        (1 / s - ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2)).re ≤
        C * Real.log (|t| + 2) := by
      have hB_cancel : xiHadamardB.re + ∑' n : ℕ, (1 / xiZeroSeq n).re = 0 := by
        simp_rw [one_div]; rw [xi_hadamard_davenport_B]; ring
      rw [hB_cancel, neg_zero, zero_add]
      have hre_E : (1 / s - ((Real.log Real.pi / 2 : ℝ) : ℂ) +
          (1 / 2 : ℂ) * Complex.digamma (s / 2)).re =
          (1 / s).re - Real.log Real.pi / 2 + (1 / 2) * (Complex.digamma (s / 2)).re := by
        simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
      rw [hre_E]
      have hinv_s : (1 / s).re ≤ 1 := by
        have hs_norm : 1 ≤ ‖s‖ := by
          have h1 := (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
          have hsre : s.re = σ := by simp [s]
          rw [hsre] at h1; linarith
        calc (1 / s).re ≤ ‖1 / s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ = 1 / ‖s‖ := by rw [norm_div, norm_one]
          _ ≤ 1 := (div_le_one (by linarith)).mpr hs_norm
      have hdig_s2 := hdig (s / 2) (by simp [s]; linarith) (by simp [s]; linarith)
      have him_s2 : |(s / 2).im| + 2 ≤ |t| + 2 := by
        have him : (s / 2).im = t / 2 := by simp [s]
        rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [abs_nonneg t]
      have hdig_re : (Complex.digamma (s / 2)).re ≤ C_dig * Real.log (|t| + 2) :=
        ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
          (hdig_s2.trans (mul_le_mul_of_nonneg_left
            (Real.log_le_log (by linarith [abs_nonneg (s / 2).im]) him_s2) hC_dig_pos.le))
      have hlogt : (1 / 2 : ℝ) < Real.log (|t| + 2) :=
        hlog2_half.trans_le (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
      dsimp only [C]; nlinarith
    have hbound := Stage5JensenHadamard.re_le_sub_finset_of_hadamard_partialFraction
      (f := negLogDerivZeta) (P := fun z => 1 / (z - 1))
      (E := fun z => 1 / z - ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (z / 2))
      (B₀ := xiHadamardB)
      xiZeroSeq_strip xiZeroSeq_summable_inv_sq hs1 hrep hM F
    linarith
  · intro q _ χ hprim hχ σ t hσ1 hσ2 F
    set s : ℂ := (σ : ℂ) + I * (t : ℂ)
    have hs1 : 1 < s.re := by simp [s, hσ1]
    have hs0 : 0 < s.re := by linarith
    have hrep := negLogDerivL_prim_eq_hadamard_partialFraction hprim hχ hs1
    have hM : -((symmetricCompletedLHadamardB χ).re +
          ∑' n : ℕ, (1 / completedLZeroSeq hprim hχ n).re) +
        (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
          deriv (DirichletCharacter.gammaFactor χ) s / DirichletCharacter.gammaFactor χ s).re ≤
        C * Real.log ((q : ℝ) * (|t| + 2)) := by
      have hB_cancel : (symmetricCompletedLHadamardB χ).re +
          ∑' n : ℕ, (1 / completedLZeroSeq hprim hχ n).re = 0 := by
        simp_rw [one_div]; rw [symmetricCompletedLFunction_hadamard_davenport_B hprim hχ]; ring
      rw [hB_cancel, neg_zero, zero_add, Complex.add_re, Complex.ofReal_re]
      have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
      have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
      have hlogq_le : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
        Real.log_le_log hq_pos (by nlinarith [abs_nonneg t])
      have hlogt_le : Real.log (|t| + 2) ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
        Real.log_le_log (by linarith [abs_nonneg t]) (by nlinarith [abs_nonneg t])
      have hlogqt_nn : 0 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
        Real.log_nonneg (by nlinarith [abs_nonneg t])
      have hgamma_re :
          (deriv (DirichletCharacter.gammaFactor χ) s / DirichletCharacter.gammaFactor χ s).re ≤
            (1 / 2) * C_dig * Real.log (|t| + 2) := by
        rcases χ.even_or_odd with he | ho
        · rw [logDeriv_gammaFactor_even he hs0]
          have hre : (-((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2)).re =
              -Real.log Real.pi / 2 + (1 / 2) * (Complex.digamma (s / 2)).re := by
            simp [Complex.add_re, Complex.mul_re]; ring
          rw [hre]
          have hdig_bd := hdig (s / 2) (by simp [s]; linarith) (by simp [s]; linarith)
          have him_le : |(s / 2).im| + 2 ≤ |t| + 2 := by
            have him : (s / 2).im = t / 2 := by simp [s]
            rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            linarith [abs_nonneg t]
          have h1 : (Complex.digamma (s / 2)).re ≤ C_dig * Real.log (|t| + 2) :=
            ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
              (hdig_bd.trans (mul_le_mul_of_nonneg_left
                (Real.log_le_log (by linarith [abs_nonneg (s / 2).im]) him_le) hC_dig_pos.le))
          linarith
        · rw [logDeriv_gammaFactor_odd ho hs0]
          have hre : (-((Real.log Real.pi / 2 : ℝ) : ℂ) +
              (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2)).re =
              -Real.log Real.pi / 2 + (1 / 2) * (Complex.digamma ((s + 1) / 2)).re := by
            simp [Complex.add_re, Complex.mul_re]; ring
          rw [hre]
          have hdig_bd := hdig ((s + 1) / 2) (by simp [s]; linarith) (by simp [s]; linarith)
          have him_le : |((s + 1) / 2).im| + 2 ≤ |t| + 2 := by
            have him : ((s + 1) / 2).im = t / 2 := by simp [s]
            rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            linarith [abs_nonneg t]
          have h1 : (Complex.digamma ((s + 1) / 2)).re ≤ C_dig * Real.log (|t| + 2) :=
            ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
              (hdig_bd.trans (mul_le_mul_of_nonneg_left
                (Real.log_le_log (by linarith [abs_nonneg ((s + 1) / 2).im]) him_le) hC_dig_pos.le))
          linarith
      have hdig_qt : (1 / 2) * C_dig * Real.log (|t| + 2) ≤
          (1 / 2) * C_dig * Real.log ((q : ℝ) * (|t| + 2)) :=
        mul_le_mul_of_nonneg_left hlogt_le (by positivity)
      dsimp only [C]; nlinarith
    have hbound := Stage5JensenHadamard.re_le_sub_finset_of_hadamard_partialFraction
      (f := negLogDerivL χ) (P := fun _ => 0)
      (E := fun z => ((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
        deriv (DirichletCharacter.gammaFactor χ) z / DirichletCharacter.gammaFactor χ z)
      (B₀ := symmetricCompletedLHadamardB χ)
      (completedLZeroSeq_strip hprim hχ) (completedLZeroSeq_summable_inv_sq hprim hχ) hs1 hrep hM F
    simpa only [Complex.zero_re, zero_add] using hbound

/-! ## Section 4: Unconditional 0-Assumption Classical Zero-Free Regions & Landau–Page Isolation -/

/-- **UNCONDITIONAL LANDAU–PAGE EXCEPTIONAL ZERO ISOLATION (`0` ASSUMPTIONS!)**:
directly on Mathlib's actual `DirichletCharacter.LFunction`, discharged from
`hadamardLogDerivPackage_unconditional`! -/
theorem landau_page_exceptional_zero_isolation_unconditional :
    ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 2 ≤ Q →
      (∀ (ψ : RHDirect.PChar) (β : ℝ), ψ.χ ≠ 1 → (ψ.N : ℝ) ≤ Q → 0 < β → β < 1 →
          DirichletCharacter.LFunction ψ.χ (β : ℂ) = 0 →
          1 - c / Real.log (2 * Q) < β → ψ.IsReal) ∧
      (∀ (ψ₁ ψ₂ : RHDirect.PChar) (β₁ β₂ : ℝ),
          ψ₁.χ ≠ 1 → ψ₂.χ ≠ 1 → (ψ₁.N : ℝ) ≤ Q → (ψ₂.N : ℝ) ≤ Q →
          0 < β₁ → β₁ < 1 → 0 < β₂ → β₂ < 1 →
          DirichletCharacter.LFunction ψ₁.χ (β₁ : ℂ) = 0 →
          DirichletCharacter.LFunction ψ₂.χ (β₂ : ℂ) = 0 →
          1 - c / Real.log (2 * Q) < β₁ →
          1 - c / Real.log (2 * Q) < β₂ →
          ψ₁ = ψ₂ ∧ β₁ = β₂) := by
  obtain ⟨B, H⟩ := hadamardLogDerivPackage_unconditional
  set c : ℝ := 1 / (168 * max B 1)
  have hc_pos : 0 < c := by
    dsimp only [c]; positivity
  refine ⟨c, hc_pos, fun Q hQ => ?_⟩
  have hLP := Stage3ZeroFreeRegion.landau_page_exceptional_zero_isolation H hQ
  have hdiv_eq : c / Real.log (2 * Q) = 1 / (168 * max B 1 * Real.log (2 * Q)) := by
    dsimp only [c]; ring
  rw [hdiv_eq]
  exact hLP

/-- **UNCONDITIONAL UNIFIED NON-EXCEPTIONAL ZERO-FREE REGION FOR EVERY `χ ≠ 1` (`0` ASSUMPTIONS!)**:
directly on Mathlib's actual `DirichletCharacter.LFunction`, discharged from
`hadamardLogDerivPackage_unconditional`! -/
theorem zeroFreeRegion_nonexceptional_unconditional :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
          ρ.re ≤ 1 - c / Real.log ((q : ℝ) * (|ρ.im| + 2)) ∨
            (IsRealChar χ ∧ ρ.im = 0 ∧ 1 - c / Real.log (2 * (q : ℝ)) < ρ.re) := by
  obtain ⟨B, H⟩ := hadamardLogDerivPackage_unconditional
  set c : ℝ := 1 / (296 * max B 1)
  have hc_pos : 0 < c := by dsimp only [c]; positivity
  refine ⟨c, hc_pos, fun q _ χ hχ ρ h0 h1 hz => ?_⟩
  have h := Stage3ZeroFreeRegion.zeroFreeRegion_nonexceptional H hχ h0 h1 hz
  have h1' : c / Real.log ((q : ℝ) * (|ρ.im| + 2)) =
      1 / (296 * max B 1 * Real.log ((q : ℝ) * (|ρ.im| + 2))) := by
    dsimp only [c]; ring
  have h2' : c / Real.log (2 * (q : ℝ)) = 1 / (296 * max B 1 * Real.log (2 * (q : ℝ))) := by
    dsimp only [c]; ring
  rw [h1', h2']
  exact h

end RHDirect.Stage8HadamardLFunction
