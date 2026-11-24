import RHDirect.Interfaces
import RHDirect.ElementaryEquiv
import RHDirect.Stage3BombieriVinogradov
import RHDirect.Stage3ZeroFreeRegion
import RHDirect.Stage5StirlingPhragmen
import RHDirect.Stage5DirichletLZeroFree
import RHDirect.Stage5JensenHadamard
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# RHDirect.Stage6LFunctionOrder

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) Stage 6 complex-analytic engine
directly on Mathlib's ACTUAL `DirichletCharacter.completedLFunction` and
`DirichletCharacter.LFunction` in pure Mathlib `v4.33.1`, establishing:

1. **Unconditional Entirety, Root Number, Functional Equation & Critical-Strip Zero Equivalence**:
   - `norm_rootNumber_eq_one`: `‖DirichletCharacter.rootNumber χ‖ = 1` for every primitive `χ`.
   - `differentiable_completedLFunction_prim`: `Differentiable ℂ (completedLFunction χ)` (entire).
   - Exact functional equation modulus identity for Mathlib's `completedLFunction`:
     `‖completedLFunction χ (1 - s)‖ = (q : ℝ) ^ (s.re - 1 / 2) * ‖completedLFunction χ⁻¹ s‖`
     (`norm_completedLFunction_one_sub`, with `= ‖completedLFunction χ⁻¹ s‖` on `s.re = 1 / 2`)
     and exact global modulus symmetry `‖symmetricCompletedLFunction χ (1 - s)‖ = ‖symmetricCompletedLFunction χ⁻¹ s‖`
     for the normalized completion `Λ_sym(χ, s) = q ^ (s / 2) * completedLFunction χ s`.
   - Exact critical-strip zero equivalence `completedLFunction_eq_zero_iff_LFunction`,
     unconditional non-vanishing on `s.re ≥ 1` and `s.re ≤ 0` (including `completedLFunction χ 0 ≠ 0`),
     and exact `PrimitiveDirichletLZerosOnLine` equivalences via `completedLFunction`.

2. **Unconditional Order-1 Exponential Growth Bound for `completedLFunction χ`**:
   - Right-half-plane Dirichlet-series sandwich `1 / 4 ≤ ‖LFunction χ s‖ ≤ 2` on `s.re ≥ 2`.
   - Vertical-strip Gamma-factor and Pólya–Vinogradov combination on `1 / 2 ≤ s.re ≤ 2`, reflected
     across `s.re = 1 / 2` via the functional equation to yield unconditionally:
     `∃ A > 0, ∃ B > 0, ∀ q [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ, ‖completedLFunction χ s‖ ≤ Real.exp (A * (‖s‖ + 2) * Real.log (q * (‖s‖ + 2)) + B)`
     (explicitly with `A = 5`, `B = 8`), plus the bridge to `Stage5JensenHadamard.HasOrderOneGrowth`
     and convergence exponent `∑' n, ‖ρ n‖ ^ (-σ) < ∞` (`σ > 1`).

3. **Unconditional Quantitative Zero-Counting Bounds & Discharge of `Stage3ZeroFreeRegion.ZeroCountBound`**:
   - Polynomial vertical-strip bound `‖LFunction χ z‖ ≤ K * (q * (|z.im| + 2)) ^ 7` throughout
     `-3 ≤ z.re ≤ 7` via the functional equation, Euler's reflection formula, and
     `Stage5StirlingPhragmen.norm_Gamma_strip_stirling_upper` (with exact cancellation of
     `exp(-π |t| / 4) * exp(-π |t| / 4) * exp(π |t| / 2) = 1`).
   - Shifted-ball Jensen zero-counting at `s₀ = 2 + i T` (`r = 5 / 2, R = 5`) via
     `Stage5JensenHadamard.jensen_zero_count_le`:
     - `LFunction_zero_count_unit_interval_le`: `N(T+1, χ) - N(T, χ) ≤ C * log (q * (|T| + 2))`,
     - `LFunction_zero_count_height_le`: `N(T, χ) ≤ C * T * log (q * (T + 2))` (`T ≥ 2`),
     - `zeroCountBound_LFunction_unconditional` & `zeroCountBound_LFunction_nonprincipal_unconditional`:
       direct unconditional discharge of `Stage3ZeroFreeRegion.ZeroCountBound` for EVERY primitive
       (and every non-principal) Mathlib `DirichletCharacter.LFunction`.
-/

noncomputable section

open Complex DirichletCharacter Finset Metric
open scoped BigOperators Real

namespace RHDirect.Stage6LFunctionOrder

/-! ## Section 1: Entirety, Root Number, Functional Equation & Critical-Strip Zero Equivalence -/

/-- The inverse of a primitive Dirichlet character mod `q` is primitive mod `q`. -/
theorem isPrimitive_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  show χ⁻¹.conductor = q
  rw [DirichletCharacter.conductor_inv, hprim]

/-- The inverse of a non-principal Dirichlet character is non-principal. -/
theorem inv_ne_one_of_ne_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 := by
  intro h
  exact hχ (by simpa using congrArg Inv.inv h)

/-- A primitive Dirichlet character of level `q ≥ 2` is non-principal (`χ ≠ 1`). -/
theorem ne_one_of_isPrimitive_of_two_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hq : 2 ≤ q) : χ ≠ 1 := by
  intro h1
  have hc : χ.conductor = 1 := by rw [h1, DirichletCharacter.conductor_one]
  have hq1 : q = 1 := hprim.symm.trans hc
  omega

/-- Parity is preserved under character inversion: `χ⁻¹.Even ↔ χ.Even`. -/
theorem even_inv_iff {q : ℕ} (χ : DirichletCharacter ℂ q) : χ⁻¹.Even ↔ χ.Even := by
  change χ⁻¹ (-1) = 1 ↔ χ (-1) = 1
  have hmul : χ (-1) * χ⁻¹ (-1) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply isUnit_one.neg]
  constructor
  · intro h
    rw [h, mul_one] at hmul
    exact hmul
  · intro h
    rw [h, one_mul] at hmul
    exact hmul

/-- **Unit Modulus of the Global Root Number**: for every primitive `χ : DirichletCharacter ℂ q`,
`‖DirichletCharacter.rootNumber χ‖ = 1`. -/
theorem norm_rootNumber_eq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : ‖DirichletCharacter.rootNumber χ‖ = 1 := by
  have hq_pos : 0 < q := NeZero.pos q
  have hqR_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
  rw [DirichletCharacter.rootNumber, norm_div, norm_div,
    Stage3BombieriVinogradov.norm_gaussSum_eq_sqrt hprim, norm_pow, Complex.norm_I, one_pow,
    div_one, Complex.norm_natCast_cpow_of_pos hq_pos]
  have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by simp
  rw [hhalf, ← Real.sqrt_eq_rpow]
  exact div_self (Real.sqrt_pos.mpr hqR_pos).ne'

theorem rootNumber_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : DirichletCharacter.rootNumber χ ≠ 0 := by
  intro h
  have h1 := norm_rootNumber_eq_one hprim
  rw [h, norm_zero] at h1
  norm_num at h1

/-- **Unconditional Entirety of `completedLFunction χ`** for any non-principal `χ ≠ 1`
(in particular every primitive character of modulus `q ≥ 2`). -/
theorem differentiable_completedLFunction_prim {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
  DirichletCharacter.differentiable_completedLFunction hχ

/-- Non-vanishing of `DirichletCharacter.gammaFactor χ s` throughout the right half-plane `Re(s) > 0`. -/
theorem gammaFactor_ne_zero_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- Exact factorization `completedLFunction χ s = LFunction χ s * gammaFactor χ s` whenever
`s ≠ 0 ∨ q ≠ 1` and `gammaFactor χ s ≠ 0`. -/
theorem completedLFunction_eq_LFunction_mul_gammaFactor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (h : s ≠ 0 ∨ q ≠ 1)
    (hG : DirichletCharacter.gammaFactor χ s ≠ 0) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s h, div_mul_cancel₀ _ hG]

/-- Exact factorization `completedLFunction χ s = LFunction χ s * gammaFactor χ s` on `Re(s) > 0`. -/
theorem completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  exact completedLFunction_eq_LFunction_mul_gammaFactor χ (.inl hs0)
    (gammaFactor_ne_zero_of_re_pos χ hs)

/-- **Exact Functional Equation Modulus Identity for Mathlib's `completedLFunction`**:
for every primitive `χ : DirichletCharacter ℂ q` and every `s : ℂ`,
`‖completedLFunction χ (1 - s)‖ = q ^ (s.re - 1 / 2) * ‖completedLFunction χ⁻¹ s‖`. -/
theorem norm_completedLFunction_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (s : ℂ) :
    ‖DirichletCharacter.completedLFunction χ (1 - s)‖ =
      (q : ℝ) ^ (s.re - 1 / 2) * ‖DirichletCharacter.completedLFunction χ⁻¹ s‖ := by
  rw [hprim.completedLFunction_one_sub s, norm_mul, norm_mul, norm_rootNumber_eq_one hprim,
    mul_one, Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
  have hre : (s - (1 / 2 : ℂ)).re = s.re - 1 / 2 := by simp
  rw [hre]

/-- On the critical line `Re(s) = 1 / 2`, Mathlib's `completedLFunction` satisfies exact modulus
symmetry `‖completedLFunction χ (1 - s)‖ = ‖completedLFunction χ⁻¹ s‖`. -/
theorem norm_completedLFunction_one_sub_of_re_eq_half {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖DirichletCharacter.completedLFunction χ (1 - s)‖ =
      ‖DirichletCharacter.completedLFunction χ⁻¹ s‖ := by
  rw [norm_completedLFunction_one_sub hprim s, hs, sub_self, Real.rpow_zero, one_mul]

/-- The symmetrically normalized completed Dirichlet `L`-function:
`symmetricCompletedLFunction χ s = (q : ℂ) ^ (s / 2) * completedLFunction χ s`,
which includes the conductor factor `q^(s/2)` and therefore satisfies exact global modulus symmetry
`‖Λ_sym(χ, 1 - s)‖ = ‖Λ_sym(χ⁻¹, s)‖` on all of `ℂ`. -/
def symmetricCompletedLFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ s

theorem differentiable_symmetricCompletedLFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (symmetricCompletedLFunction χ) := by
  unfold symmetricCompletedLFunction
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) := by
    have heq : (fun s : ℂ => (q : ℂ) ^ (s / 2)) =
        fun s : ℂ => Complex.exp (Complex.log (q : ℂ) * (s / 2)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero hqC]
    rw [heq]
    fun_prop
  exact hpow.mul (differentiable_completedLFunction_prim hχ)

/-- Exact global functional equation for `symmetricCompletedLFunction`:
`Λ_sym(χ, 1 - s) = rootNumber χ * Λ_sym(χ⁻¹, s)` for all `s : ℂ`. -/
theorem symmetricCompletedLFunction_one_sub {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (s : ℂ) :
    symmetricCompletedLFunction χ (1 - s) =
      DirichletCharacter.rootNumber χ * symmetricCompletedLFunction χ⁻¹ s := by
  unfold symmetricCompletedLFunction
  rw [hprim.completedLFunction_one_sub s]
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2) = (q : ℂ) ^ (s / 2) := by
    rw [← Complex.cpow_add _ _ hqC]
    congr 1
    ring
  calc (q : ℂ) ^ ((1 - s) / 2) *
        ((q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
          DirichletCharacter.completedLFunction χ⁻¹ s)
      = DirichletCharacter.rootNumber χ *
          (((q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2)) *
            DirichletCharacter.completedLFunction χ⁻¹ s) := by ring
    _ = DirichletCharacter.rootNumber χ *
          ((q : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ⁻¹ s) := by rw [hpow]

/-- **Exact Global Functional Equation Modulus Symmetry**:
for every primitive `χ : DirichletCharacter ℂ q` and ALL `s : ℂ`,
`‖symmetricCompletedLFunction χ (1 - s)‖ = ‖symmetricCompletedLFunction χ⁻¹ s‖`. -/
theorem norm_symmetricCompletedLFunction_one_sub {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (s : ℂ) :
    ‖symmetricCompletedLFunction χ (1 - s)‖ = ‖symmetricCompletedLFunction χ⁻¹ s‖ := by
  rw [symmetricCompletedLFunction_one_sub hprim s, norm_mul, norm_rootNumber_eq_one hprim, one_mul]

theorem symmetricCompletedLFunction_eq_zero_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    symmetricCompletedLFunction χ s = 0 ↔ DirichletCharacter.completedLFunction χ s = 0 := by
  unfold symmetricCompletedLFunction
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hqC]
    exact Complex.exp_ne_zero _
  simp [hpow]

/-- Exact zero equivalence on `Re(s) > 0`:
`completedLFunction χ s = 0 ↔ LFunction χ s = 0`. -/
theorem completedLFunction_eq_zero_iff_LFunction_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by
  rw [completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hs, mul_eq_zero]
  simp [gammaFactor_ne_zero_of_re_pos χ hs]

/-- **Exact Critical-Strip Zero Equivalence**:
for `0 < Re(s) < 1`, `completedLFunction χ s = 0 ↔ LFunction χ s = 0`. -/
theorem completedLFunction_eq_zero_iff_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs0 : 0 < s.re) (_hs1 : s.re < 1) :
    DirichletCharacter.completedLFunction χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 :=
  completedLFunction_eq_zero_iff_LFunction_of_re_pos χ hs0

/-- Unconditional non-vanishing of `completedLFunction χ` on `Re(s) ≥ 1` (`χ ≠ 1`). -/
theorem completedLFunction_ne_zero_of_one_le_re {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  rw [completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hs0]
  exact mul_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs)
    (gammaFactor_ne_zero_of_re_pos χ hs0)

/-- Unconditional non-vanishing of `completedLFunction χ` on `Re(s) ≤ 0` (primitive `χ ≠ 1`). -/
theorem completedLFunction_ne_zero_of_re_le_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : s.re ≤ 0) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hs_eq : s = 1 - (1 - s) := by ring
  rw [hs_eq, hprim.completedLFunction_one_sub (1 - s)]
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℂ) ^ ((1 - s) - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hqC]
    exact Complex.exp_ne_zero _
  refine mul_ne_zero (mul_ne_zero hpow (rootNumber_ne_zero hprim)) ?_
  exact completedLFunction_ne_zero_of_one_le_re (inv_ne_one_of_ne_one hχ) (by simp; linarith)

/-- Unconditional non-vanishing at the origin: `completedLFunction χ 0 ≠ 0` for every primitive `χ ≠ 1`. -/
theorem completedLFunction_zero_ne_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
  completedLFunction_ne_zero_of_re_le_zero hprim hχ (by simp)

/-- Complete characterization of ALL zeros of `completedLFunction χ` in `ℂ` for primitive `χ ≠ 1`:
`completedLFunction χ s = 0 ↔ 0 < s.re ∧ s.re < 1 ∧ LFunction χ s = 0`. -/
theorem completedLFunction_eq_zero_iff_critical_strip_LFunction_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ s = 0 ↔
      0 < s.re ∧ s.re < 1 ∧ DirichletCharacter.LFunction χ s = 0 := by
  constructor
  · intro h
    have hs0 : 0 < s.re := by
      by_contra hle
      exact completedLFunction_ne_zero_of_re_le_zero hprim hχ (not_lt.mp hle) h
    have hs1 : s.re < 1 := by
      by_contra hge
      exact completedLFunction_ne_zero_of_one_le_re hχ (not_lt.mp hge) h
    exact ⟨hs0, hs1, (completedLFunction_eq_zero_iff_LFunction χ hs0 hs1).mp h⟩
  · rintro ⟨hs0, hs1, hL⟩
    exact (completedLFunction_eq_zero_iff_LFunction χ hs0 hs1).mpr hL

/-- **Exact `PrimitiveDirichletLZerosOnLine` Equivalence via `completedLFunction` (Strip Form)**:
`PrimitiveDirichletLZerosOnLine` holds iff every critical-strip zero of `completedLFunction χ`
for every primitive `χ` lies on `Re(s) = 1 / 2`. -/
theorem primitiveDirichletLZerosOnLine_iff_completedLFunction_strip :
    PrimitiveDirichletLZerosOnLine ↔
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
        ∀ s : ℂ, 0 < s.re → s.re < 1 →
          DirichletCharacter.completedLFunction χ s = 0 → s.re = 1 / 2 := by
  constructor
  · intro hP q _ χ hprim s hs0 hs1 hzero
    exact hP q χ hprim s hs0 hs1 ((completedLFunction_eq_zero_iff_LFunction χ hs0 hs1).mp hzero)
  · intro hC q _ χ hprim s hs0 hs1 hzero
    exact hC q χ hprim s hs0 hs1 ((completedLFunction_eq_zero_iff_LFunction χ hs0 hs1).mpr hzero)

/-- **Exact `PrimitiveDirichletLZerosOnLine` Equivalence via Entire Completions (`xi` + `completedLFunction`)**:
`PrimitiveDirichletLZerosOnLine` holds iff ALL zeros in `ℂ` of `Stage5StirlingPhragmen.xi` and ALL
zeros in `ℂ` of `completedLFunction χ` (for primitive `χ ≠ 1`) lie on `Re(s) = 1 / 2`. -/
theorem primitiveDirichletLZerosOnLine_iff_completedLFunction :
    PrimitiveDirichletLZerosOnLine ↔
      (∀ s : ℂ, Stage5StirlingPhragmen.xi s = 0 → s.re = 1 / 2) ∧
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ,
          DirichletCharacter.completedLFunction χ s = 0 → s.re = 1 / 2) := by
  constructor
  · intro hP
    constructor
    · intro s hxi
      obtain ⟨hs0, hs1, hzeta⟩ :=
        (Stage5StirlingPhragmen.xi_eq_zero_iff_critical_strip_zeta_zero s).mp hxi
      have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
        simpa [DirichletCharacter.LFunction_modOne_eq] using hzeta
      exact hP 1 (1 : DirichletCharacter ℂ 1) DirichletCharacter.isPrimitive_one_level_one
        s hs0 hs1 hL
    · intro q _ χ hprim hχ s hzero
      obtain ⟨hs0, hs1, hL⟩ :=
        (completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hχ s).mp hzero
      exact hP q χ hprim s hs0 hs1 hL
  · rintro ⟨hxi, hcomp⟩ q _ χ hprim s hs0 hs1 hL
    by_cases hχ1 : χ = 1
    · subst hχ1
      have hq1 : q = 1 := hprim.symm.trans DirichletCharacter.conductor_one
      subst hq1
      have hzeta : riemannZeta s = 0 := by
        simpa [DirichletCharacter.LFunction_modOne_eq] using hL
      exact hxi s ((Stage5StirlingPhragmen.xi_eq_zero_iff_riemannZeta_eq_zero hs0 hs1).mpr hzeta)
    · exact hcomp q χ hprim hχ1 s
        ((completedLFunction_eq_zero_iff_LFunction χ hs0 hs1).mpr hL)

/-! ## Section 2: Unconditional Order-1 Exponential Growth Bound for `completedLFunction χ` -/

/-- Elementary telescoping bound `∑' k : ℕ, 1 / ((k + 2 : ℕ) : ℝ) ^ 2 ≤ 3 / 4`. -/
lemma tsum_inv_add_two_sq_le_three_quarters :
    ∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 ≤ 3 / 4 := by
  have hsumm0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    simp [one_div, Real.summable_nat_pow_inv]
  have hsumm : Summable (fun k : ℕ => (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) :=
    hsumm0.comp_injective (fun a b h => by omega)
  refine hsumm.tsum_le_of_sum_range_le fun N => ?_
  have hbound : ∀ m : ℕ,
      ∑ k ∈ Finset.range (m + 1), (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 ≤
        3 / 4 - 1 / ((m + 2 : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero =>
      simp
      norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hterm : (1 : ℝ) / ((m + 3 : ℕ) : ℝ) ^ 2 ≤
          1 / ((m + 2 : ℕ) : ℝ) - 1 / ((m + 3 : ℕ) : ℝ) := by
        push_cast
        have hstep : 1 / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) =
            1 / (((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
          field_simp; ring
        rw [hstep]
        refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
        nlinarith
      have hcast : ((m + 1 + 2 : ℕ) : ℝ) = ((m + 3 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      linarith
  cases N with
  | zero => simp; norm_num
  | succ m =>
    have h1 := hbound m
    have hnn : (0 : ℝ) ≤ 1 / ((m + 2 : ℕ) : ℝ) := by positivity
    linarith

/-- Unconditional Dirichlet-series upper bound `‖LFunction χ s‖ ≤ 2` on `Re(s) ≥ 2`
(for EVERY modulus `q` and EVERY character `χ`). -/
theorem norm_LFunction_le_two_of_two_le_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 2 ≤ s.re) : ‖DirichletCharacter.LFunction χ s‖ ≤ 2 := by
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
  unfold LSeries
  have hsumm_real : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    simp [one_div, Real.summable_nat_pow_inv]
  have hterm : ∀ n : ℕ, ‖LSeries.term (χ ·) s n‖ ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn]
      have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ s.re := by
        simpa [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hn1 hs
      calc ‖χ (n : ZMod q)‖ / (n : ℝ) ^ s.re
          ≤ 1 / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ ≤ 1 / (n : ℝ) ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) hpow
  have hsumm_norm : Summable (fun n : ℕ => ‖LSeries.term (χ ·) s n‖) :=
    hsumm_real.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc ‖∑' n : ℕ, LSeries.term (χ ·) s n‖
      ≤ ∑' n : ℕ, ‖LSeries.term (χ ·) s n‖ := norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := hsumm_norm.tsum_le_tsum hterm hsumm_real
    _ ≤ 2 := Stage5StirlingPhragmen.tsum_inv_nat_sq_le_two

/-- **Unconditional Right-Half-Plane Lower Bound `1 / 4 ≤ ‖LFunction χ s‖` on `Re(s) ≥ 2`**:
for EVERY modulus `q`, EVERY character `χ : DirichletCharacter ℂ q`, and EVERY `s : ℂ`
with `2 ≤ s.re`, `1 / 4 ≤ ‖LFunction χ s‖`. -/
theorem quarter_le_norm_LFunction_of_two_le_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 2 ≤ s.re) : (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
  have hsum : LSeriesSummable (χ ·) s := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs1
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hhead : ∑ i ∈ Finset.range 2, LSeries.term (χ ·) s i = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, LSeries.term_zero, zero_add,
      LSeries.term_of_ne_zero one_ne_zero]
    simp
  rw [hhead] at hsplit
  have htail_le : ‖∑' k : ℕ, LSeries.term (χ ·) s (k + 2)‖ ≤ 3 / 4 := by
    have hsumm0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
      simp [one_div, Real.summable_nat_pow_inv]
    have hsumm_real : Summable (fun k : ℕ => (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) :=
      hsumm0.comp_injective (fun a b h => by omega)
    have hterm : ∀ k : ℕ, ‖LSeries.term (χ ·) s (k + 2)‖ ≤ (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      intro k
      have hk_pos : 0 < k + 2 := by omega
      have hk1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.one_le_cast.mpr hk_pos
      rw [LSeries.term_of_ne_zero hk_pos.ne', norm_div, Complex.norm_natCast_cpow_of_pos hk_pos]
      have hpow : ((k + 2 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) ^ s.re := by
        simpa [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hk1 hs
      calc ‖χ ((k + 2 : ℕ) : ZMod q)‖ / ((k + 2 : ℕ) : ℝ) ^ s.re
          ≤ 1 / ((k + 2 : ℕ) : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 1 / ((k + 2 : ℕ) : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) hpow
    have hsumm_norm : Summable (fun k : ℕ => ‖LSeries.term (χ ·) s (k + 2)‖) :=
      hsumm_real.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    calc ‖∑' k : ℕ, LSeries.term (χ ·) s (k + 2)‖
        ≤ ∑' k : ℕ, ‖LSeries.term (χ ·) s (k + 2)‖ := norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 := hsumm_norm.tsum_le_tsum hterm hsumm_real
      _ ≤ 3 / 4 := tsum_inv_add_two_sq_le_three_quarters
  have hrev : (1 : ℝ) - ‖∑' k : ℕ, LSeries.term (χ ·) s (k + 2)‖ ≤
      ‖(1 : ℂ) + ∑' k : ℕ, LSeries.term (χ ·) s (k + 2)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-(∑' k : ℕ, LSeries.term (χ ·) s (k + 2)))
    simpa [sub_neg_eq_add, norm_neg, norm_one] using h
  unfold LSeries
  rw [← hsplit]
  linarith

/-- Uniform upper bound on `Complex.Gammaℝ w` throughout the vertical strip `1 / 2 ≤ w.re ≤ 3`:
`‖Complex.Gammaℝ w‖ ≤ 36`. -/
lemma norm_Gammaℝ_le_of_half_le_re_le_three {w : ℂ} (hw1 : 1 / 2 ≤ w.re) (hw3 : w.re ≤ 3) :
    ‖Complex.Gammaℝ w‖ ≤ 36 := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hpi : ‖(Real.pi : ℂ) ^ (-w / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-w / 2).re = -w.re / 2 := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) (by linarith)
  have hG : ‖Complex.Gamma (w / 2)‖ ≤ 36 := by
    have hre_pos : 0 < (w / 2).re := by simp; linarith
    have h1 := Stage5StirlingPhragmen.norm_Gamma_le_of_re_pos hre_pos
    have hre_eq : (w / 2).re = w.re / 2 := by simp
    rw [hre_eq] at h1
    have hinv : 1 / (w.re / 2) ≤ 4 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < w.re / 2)]
      linarith
    have hpow : (w.re / 2 + 1) ^ (w.re / 2) ≤ 9 := by
      calc (w.re / 2 + 1) ^ (w.re / 2)
          ≤ (3 : ℝ) ^ (w.re / 2) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
        _ ≤ (3 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 9 := by norm_num
    calc ‖Complex.Gamma (w / 2)‖
        ≤ (1 / (w.re / 2)) * (w.re / 2 + 1) ^ (w.re / 2) := h1
      _ ≤ 4 * 9 := mul_le_mul hinv hpow (Real.rpow_nonneg (by linarith) _) (by norm_num)
      _ = 36 := by norm_num
  calc ‖(Real.pi : ℂ) ^ (-w / 2)‖ * ‖Complex.Gamma (w / 2)‖
      ≤ 1 * 36 := mul_le_mul hpi hG (norm_nonneg _) zero_le_one
    _ = 36 := one_mul _

/-- Upper bound on `DirichletCharacter.gammaFactor χ s` on `1 / 2 ≤ s.re ≤ 2`:
`‖gammaFactor χ s‖ ≤ 36`. -/
theorem norm_gammaFactor_le_of_half_le_re_le_two {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖DirichletCharacter.gammaFactor χ s‖ ≤ 36 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact norm_Gammaℝ_le_of_half_le_re_le_three hs1 (by linarith)
  · rw [h.gammaFactor_def]
    exact norm_Gammaℝ_le_of_half_le_re_le_three (by simp; linarith) (by simp; linarith)

/-- Upper bound on `DirichletCharacter.gammaFactor χ s` on `2 ≤ s.re`:
`‖gammaFactor χ s‖ ≤ (‖s‖ + 2) ^ (‖s‖ + 2)`. -/
theorem norm_gammaFactor_le_of_two_le_re {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.gammaFactor χ s‖ ≤ (‖s‖ + 2) ^ (‖s‖ + 2) := by
  have hmain : ∀ w : ℂ, 2 ≤ w.re → ‖w‖ ≤ ‖s‖ + 1 →
      ‖Complex.Gammaℝ w‖ ≤ (‖s‖ + 2) ^ (‖s‖ + 2) := by
    intro w hw hwnorm
    rw [Complex.Gammaℝ_def, norm_mul]
    have hpi : ‖(Real.pi : ℂ) ^ (-w / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      have hre : (-w / 2).re = -w.re / 2 := by simp
      rw [hre]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) (by linarith)
    have hre1 : 1 ≤ (w / 2).re := by simp; linarith
    have hG1 := Stage5StirlingPhragmen.norm_Gamma_le_norm_add_one_rpow hre1
    have hre_eq : (w / 2).re = w.re / 2 := by simp
    rw [hre_eq] at hG1
    have hbase : ‖w / 2‖ + 1 ≤ ‖s‖ + 2 := by
      rw [norm_div, Complex.norm_ofNat]
      linarith [norm_nonneg w, norm_nonneg s]
    have hexp : w.re / 2 ≤ ‖s‖ + 2 := by
      have hwre : w.re ≤ ‖w‖ := le_trans (le_abs_self w.re) (Complex.abs_re_le_norm w)
      linarith [norm_nonneg s]
    have hG : ‖Complex.Gamma (w / 2)‖ ≤ (‖s‖ + 2) ^ (‖s‖ + 2) := by
      calc ‖Complex.Gamma (w / 2)‖
          ≤ (‖w / 2‖ + 1) ^ (w.re / 2) := hG1
        _ ≤ (‖s‖ + 2) ^ (w.re / 2) :=
            Real.rpow_le_rpow (by linarith [norm_nonneg (w / 2)]) hbase (by linarith)
        _ ≤ (‖s‖ + 2) ^ (‖s‖ + 2) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg s]) hexp
    calc ‖(Real.pi : ℂ) ^ (-w / 2)‖ * ‖Complex.Gamma (w / 2)‖
        ≤ 1 * (‖s‖ + 2) ^ (‖s‖ + 2) := mul_le_mul hpi hG (norm_nonneg _) zero_le_one
      _ = (‖s‖ + 2) ^ (‖s‖ + 2) := one_mul _
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact hmain s hs (by linarith)
  · rw [h.gammaFactor_def]
    refine hmain (s + 1) (by simp; linarith) ?_
    calc ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le s 1
      _ = ‖s‖ + 1 := by simp

private lemma two_hundred_fifty_six_le_exp_eight : (256 : ℝ) ≤ Real.exp 8 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hpow : (2 : ℝ) ^ 8 ≤ (Real.exp 1) ^ 8 := pow_le_pow_left₀ (by norm_num) h2 8
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow ⊢
  exact hpow

/-- Explicit right-half-plane (`Re(s) ≥ 1 / 2`) order-1 growth bound for `completedLFunction χ`:
`‖completedLFunction χ s‖ ≤ Real.exp ((‖s‖ + 2) * Real.log (q * (‖s‖ + 2)) + 8)`. -/
theorem norm_completedLFunction_le_of_half_le_re {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.completedLFunction χ s‖ ≤
      Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hs0 : 0 < s.re := by linarith
  have hbase_ge2 : 2 ≤ ‖s‖ + 2 := by linarith [norm_nonneg s]
  have hbase_pos : 0 < ‖s‖ + 2 := by linarith
  have hqbase_ge4 : 4 ≤ (q : ℝ) * (‖s‖ + 2) := by nlinarith
  have hqbase_pos : 0 < (q : ℝ) * (‖s‖ + 2) := by linarith
  have hlog_nn : 0 ≤ Real.log ((q : ℝ) * (‖s‖ + 2)) := Real.log_nonneg (by linarith)
  rw [completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hs0, norm_mul]
  rcases le_or_gt 2 s.re with hs2 | hs2
  · have hL := norm_LFunction_le_two_of_two_le_re χ hs2
    have hG := norm_gammaFactor_le_of_two_le_re χ hs2
    have h2_exp : (2 : ℝ) ≤ Real.exp 8 := by linarith [two_hundred_fifty_six_le_exp_eight]
    have hpow_le : (‖s‖ + 2) ^ (‖s‖ + 2) ≤
        Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) := by
      rw [Real.rpow_def_of_pos hbase_pos]
      refine Real.exp_le_exp.mpr ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log hbase_pos (by nlinarith)) hbase_pos.le
    calc ‖DirichletCharacter.LFunction χ s‖ * ‖DirichletCharacter.gammaFactor χ s‖
        ≤ 2 * (‖s‖ + 2) ^ (‖s‖ + 2) :=
          mul_le_mul hL hG (norm_nonneg _) (by norm_num)
      _ ≤ Real.exp 8 * Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) :=
          mul_le_mul h2_exp hpow_le (Real.rpow_nonneg hbase_pos.le _) (Real.exp_pos _).le
      _ = Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) := by
          rw [← Real.exp_add]; congr 1; ring
  · have hG := norm_gammaFactor_le_of_half_le_re_le_two χ hs hs2.le
    have hL_raw : ‖DirichletCharacter.LFunction χ s‖ ≤
        (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|s.im| + 2) / s.re := by
      have hs_eq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
        apply Complex.ext <;> simp
      simpa only [hs_eq] using
        Stage5DirichletLZeroFree.norm_LFunction_strip_le_polya_vinogradov hprim hχ hs0 hs2.le s.im
    have hsqrt_le : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
      calc Real.sqrt (q : ℝ) ≤ Real.sqrt ((q : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = (q : ℝ) := Real.sqrt_sq hqR_pos.le
    have hlogq_le : Real.log (q : ℝ) + 2 ≤ 2 * (q : ℝ) := by
      have h1 : Real.log (q : ℝ) ≤ (q : ℝ) :=
        le_trans (Real.log_le_sub_one_of_pos hqR_pos) (by linarith)
      linarith
    have him_le : |s.im| + 2 ≤ ‖s‖ + 2 := by linarith [Complex.abs_im_le_norm s]
    have hB_le : Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2) ≤ 2 * (q : ℝ) ^ 2 := by
      calc Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)
          ≤ (q : ℝ) * (2 * (q : ℝ)) :=
            mul_le_mul hsqrt_le hlogq_le (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ q)])
              hqR_pos.le
        _ = 2 * (q : ℝ) ^ 2 := by ring
    have hL_le : ‖DirichletCharacter.LFunction χ s‖ ≤ 4 * ((q : ℝ) * (‖s‖ + 2)) ^ 2 := by
      have hdiv : ((Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|s.im| + 2)) / s.re ≤
          2 * ((Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|s.im| + 2)) := by
        rw [div_le_iff₀ hs0]
        have hnn : 0 ≤ (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|s.im| + 2) := by
          have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
          positivity
        nlinarith
      have hmul : (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|s.im| + 2) ≤
          2 * (q : ℝ) ^ 2 * (‖s‖ + 2) :=
        mul_le_mul hB_le him_le (by positivity) (by positivity)
      have hsq : (q : ℝ) ^ 2 * (‖s‖ + 2) ≤ ((q : ℝ) * (‖s‖ + 2)) ^ 2 := by
        have : ((q : ℝ) * (‖s‖ + 2)) ^ 2 = (q : ℝ) ^ 2 * (‖s‖ + 2) ^ 2 := by ring
        rw [this]
        have : ‖s‖ + 2 ≤ (‖s‖ + 2) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
      linarith [hL_raw.trans hdiv]
    have h144_exp : (144 : ℝ) ≤ Real.exp 8 := by linarith [two_hundred_fifty_six_le_exp_eight]
    have hsq_exp : ((q : ℝ) * (‖s‖ + 2)) ^ 2 ≤
        Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) := by
      calc ((q : ℝ) * (‖s‖ + 2)) ^ 2
          = ((q : ℝ) * (‖s‖ + 2)) ^ (2 : ℝ) := (Real.rpow_two _).symm
        _ = Real.exp (2 * Real.log ((q : ℝ) * (‖s‖ + 2))) := by
            rw [Real.rpow_def_of_pos hqbase_pos, mul_comm]
        _ ≤ Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hbase_ge2 hlog_nn)
    calc ‖DirichletCharacter.LFunction χ s‖ * ‖DirichletCharacter.gammaFactor χ s‖
        ≤ (4 * ((q : ℝ) * (‖s‖ + 2)) ^ 2) * 36 :=
          mul_le_mul hL_le hG (norm_nonneg _) (by positivity)
      _ = 144 * ((q : ℝ) * (‖s‖ + 2)) ^ 2 := by ring
      _ ≤ Real.exp 8 * Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) :=
          mul_le_mul h144_exp hsq_exp (sq_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) := by
          rw [← Real.exp_add]; congr 1; ring

/-- **Explicit Global Unconditional Order-1 Growth Bound for `completedLFunction χ`**:
for EVERY primitive `χ ≠ 1` mod `q` and ALL `s : ℂ`,
`‖completedLFunction χ s‖ ≤ Real.exp (5 * (‖s‖ + 2) * Real.log (q * (‖s‖ + 2)) + 8)`. -/
theorem norm_completedLFunction_order_one_explicit {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (s : ℂ) :
    ‖DirichletCharacter.completedLFunction χ s‖ ≤
      Real.exp (5 * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hbase_ge2 : 2 ≤ ‖s‖ + 2 := by linarith [norm_nonneg s]
  have hqbase_ge4 : 4 ≤ (q : ℝ) * (‖s‖ + 2) := by nlinarith
  have hqbase_pos : 0 < (q : ℝ) * (‖s‖ + 2) := by linarith
  have hlog_nn : 0 ≤ Real.log ((q : ℝ) * (‖s‖ + 2)) := Real.log_nonneg (by linarith)
  rcases le_or_gt (1 / 2 : ℝ) s.re with hs | hs
  · refine (norm_completedLFunction_le_of_half_le_re hprim hχ hs).trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  · have hs_eq : s = 1 - (1 - s) := by ring
    have hre_1s : 1 / 2 ≤ (1 - s).re := by simp; linarith
    have hfe := norm_completedLFunction_one_sub hprim (1 - s)
    rw [← hs_eq] at hfe
    rw [hfe]
    have hre_sub : (1 - s).re - 1 / 2 = 1 / 2 - s.re := by simp; ring
    rw [hre_sub]
    have hqpow_le : (q : ℝ) ^ (1 / 2 - s.re) ≤
        Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) := by
      rw [Real.rpow_def_of_pos hqR_pos, mul_comm]
      refine Real.exp_le_exp.mpr ?_
      have hexp_le : 1 / 2 - s.re ≤ ‖s‖ + 2 := by
        have : -s.re ≤ ‖s‖ := le_trans (neg_le_abs s.re) (Complex.abs_re_le_norm s)
        linarith
      have hlogq : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (‖s‖ + 2)) :=
        Real.log_le_log hqR_pos (by nlinarith)
      exact mul_le_mul hexp_le hlogq (Real.log_nonneg (by linarith)) (by linarith)
    have hcomp_inv := norm_completedLFunction_le_of_half_le_re
      (isPrimitive_inv hprim) (inv_ne_one_of_ne_one hχ) hre_1s
    have hnorm1s : ‖1 - s‖ + 2 ≤ 2 * (‖s‖ + 2) := by
      have htri : ‖1 - s‖ ≤ 1 + ‖s‖ := by
        calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le 1 s
          _ = 1 + ‖s‖ := by simp
      linarith [norm_nonneg s]
    have hlog1s : Real.log ((q : ℝ) * (‖1 - s‖ + 2)) ≤ 2 * Real.log ((q : ℝ) * (‖s‖ + 2)) := by
      have harg : (q : ℝ) * (‖1 - s‖ + 2) ≤ ((q : ℝ) * (‖s‖ + 2)) ^ 2 := by
        calc (q : ℝ) * (‖1 - s‖ + 2)
            ≤ (q : ℝ) * (2 * (‖s‖ + 2)) := mul_le_mul_of_nonneg_left hnorm1s hqR_pos.le
          _ = 2 * ((q : ℝ) * (‖s‖ + 2)) := by ring
          _ ≤ ((q : ℝ) * (‖s‖ + 2)) ^ 2 := by nlinarith
      calc Real.log ((q : ℝ) * (‖1 - s‖ + 2))
          ≤ Real.log (((q : ℝ) * (‖s‖ + 2)) ^ 2) :=
            Real.log_le_log (by positivity) harg
        _ = 2 * Real.log ((q : ℝ) * (‖s‖ + 2)) := by rw [Real.log_pow]; norm_num
    have hprod_exp : (‖1 - s‖ + 2) * Real.log ((q : ℝ) * (‖1 - s‖ + 2)) ≤
        4 * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) := by
      have hlog1s_nn : 0 ≤ Real.log ((q : ℝ) * (‖1 - s‖ + 2)) :=
        Real.log_nonneg (by nlinarith [norm_nonneg (1 - s)])
      have hmul := mul_le_mul hnorm1s hlog1s hlog1s_nn (by positivity)
      linarith
    have hcomp_le : ‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖ ≤
        Real.exp (4 * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) :=
      hcomp_inv.trans (Real.exp_le_exp.mpr (by linarith))
    calc (q : ℝ) ^ (1 / 2 - s.re) * ‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖
        ≤ Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) *
            Real.exp (4 * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) :=
          mul_le_mul hqpow_le hcomp_le (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (5 * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) := by
          rw [← Real.exp_add]; congr 1; ring

/-- **UNCONDITIONAL ORDER-1 EXPONENTIAL GROWTH BOUND FOR `DirichletCharacter.completedLFunction`**
(`0` assumptions, uniform across ALL conductors `q`, ALL primitive `χ ≠ 1`, and ALL `s : ℂ`):
`∃ A > 0, ∃ B > 0, ∀ q [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ, ‖completedLFunction χ s‖ ≤ Real.exp (A * (‖s‖ + 2) * Real.log (q * (‖s‖ + 2)) + B)`. -/
theorem norm_completedLFunction_order_one_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ,
          ‖DirichletCharacter.completedLFunction χ s‖ ≤
            Real.exp (A * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + B) :=
  ⟨5, by norm_num, 8, by norm_num, fun _ _ _ hprim hχ s =>
    norm_completedLFunction_order_one_explicit hprim hχ s⟩

/-- Matching unconditional order-1 growth bound for `symmetricCompletedLFunction χ`. -/
theorem norm_symmetricCompletedLFunction_order_one_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ,
          ‖symmetricCompletedLFunction χ s‖ ≤
            Real.exp (A * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + B) := by
  refine ⟨6, by norm_num, 8, by norm_num, fun q _ χ hprim hχ s => ?_⟩
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  unfold symmetricCompletedLFunction
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
  have hre : (s / 2).re = s.re / 2 := by simp
  rw [hre]
  have hqpow : (q : ℝ) ^ (s.re / 2) ≤ Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) := by
    rw [Real.rpow_def_of_pos hqR_pos, mul_comm]
    refine Real.exp_le_exp.mpr ?_
    have h1 : s.re / 2 ≤ ‖s‖ + 2 := by
      have : s.re ≤ ‖s‖ := le_trans (le_abs_self s.re) (Complex.abs_re_le_norm s)
      linarith [norm_nonneg s]
    have hlogq : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (‖s‖ + 2)) :=
      Real.log_le_log hqR_pos (by nlinarith [norm_nonneg s])
    have hlog_nn : 0 ≤ Real.log ((q : ℝ) * (‖s‖ + 2)) :=
      Real.log_nonneg (by nlinarith [norm_nonneg s])
    rcases le_total 0 (s.re / 2) with hnn | hnp
    · exact mul_le_mul h1 hlogq (Real.log_nonneg (by linarith)) (by linarith [norm_nonneg s])
    · have hleft : s.re / 2 * Real.log (q : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnp (Real.log_nonneg (by linarith))
      have hright : 0 ≤ (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) := by positivity
      linarith
  calc (q : ℝ) ^ (s.re / 2) * ‖DirichletCharacter.completedLFunction χ s‖
      ≤ Real.exp ((‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2))) *
          Real.exp (5 * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) :=
        mul_le_mul hqpow (norm_completedLFunction_order_one_explicit hprim hχ s)
          (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (6 * (‖s‖ + 2) * Real.log ((q : ℝ) * (‖s‖ + 2)) + 8) := by
        rw [← Real.exp_add]; congr 1; ring

/-- **Direct Bridge to `Stage5JensenHadamard.HasOrderOneGrowth`**:
for every primitive `χ ≠ 1` mod `q`, `completedLFunction χ` satisfies `HasOrderOneGrowth`
with explicit conductor-dependent parameters `A_q = 15 * (2 * log q + 1)` and
`B_q = 15 * log (3 * q) + 8`. -/
theorem hasOrderOneGrowth_completedLFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Stage5JensenHadamard.HasOrderOneGrowth (DirichletCharacter.completedLFunction χ)
      (15 * (2 * Real.log (q : ℝ) + 1)) (15 * Real.log (3 * (q : ℝ)) + 8) := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  refine ⟨differentiable_completedLFunction_prim hχ, fun z => ?_⟩
  refine (norm_completedLFunction_order_one_explicit hprim hχ z).trans (Real.exp_le_exp.mpr ?_)
  have hbase_ge2 : 2 ≤ ‖z‖ + 2 := by linarith [norm_nonneg z]
  have hbase_pos : 0 < ‖z‖ + 2 := by linarith
  have hlogz_ge : (1 / 2 : ℝ) ≤ Real.log (‖z‖ + 2) := by
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact h2.le.trans (Real.log_le_log (by norm_num) hbase_ge2)
  rcases le_or_gt 1 ‖z‖ with hz1 | hz1
  · have hnorm3 : ‖z‖ + 2 ≤ 3 * ‖z‖ := by linarith
    have hlog_split : Real.log ((q : ℝ) * (‖z‖ + 2)) ≤
        (2 * Real.log (q : ℝ) + 1) * Real.log (‖z‖ + 2) := by
      rw [Real.log_mul hqR_pos.ne' hbase_pos.ne']
      nlinarith
    have hmul : 5 * (‖z‖ + 2) * Real.log ((q : ℝ) * (‖z‖ + 2)) ≤
        15 * (2 * Real.log (q : ℝ) + 1) * ‖z‖ * Real.log (‖z‖ + 2) := by
      have h1 := mul_le_mul hnorm3 hlog_split
        (Real.log_nonneg (by nlinarith)) (by positivity)
      linarith
    have hB_nn : 0 ≤ 15 * Real.log (3 * (q : ℝ)) :=
      mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
    linarith
  · have hlog3q : Real.log ((q : ℝ) * (‖z‖ + 2)) ≤ Real.log (3 * (q : ℝ)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hsmall : 5 * (‖z‖ + 2) * Real.log ((q : ℝ) * (‖z‖ + 2)) ≤ 15 * Real.log (3 * (q : ℝ)) := by
      have h1 : 5 * (‖z‖ + 2) ≤ 15 := by linarith
      exact mul_le_mul h1 hlog3q (Real.log_nonneg (by nlinarith)) (by norm_num)
    have hA_nn : 0 ≤ 15 * (2 * Real.log (q : ℝ) + 1) * ‖z‖ * Real.log (‖z‖ + 2) := by
      have : 0 ≤ Real.log (‖z‖ + 2) := by linarith
      positivity
    linarith

/-- **Unconditional Convergence Exponent (`σ > 1`) of Zeros of `completedLFunction χ`**:
for every primitive `χ ≠ 1` mod `q`, every injective enumeration `ρ : ℕ → ℂ` of zeros of
`completedLFunction χ` satisfies `∑' n, ‖ρ n‖ ^ (-σ) < ∞` for every `σ > 1`. -/
theorem completedLFunction_zero_seq_summable_rpow_neg {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {ρ : ℕ → ℂ} (hinj : Function.Injective ρ)
    (hzeros : ∀ n, DirichletCharacter.completedLFunction χ (ρ n) = 0)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n => ‖ρ n‖ ^ (-σ)) := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hA_nn : 0 ≤ 15 * (2 * Real.log (q : ℝ) + 1) := by
    have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
    positivity
  exact Stage5JensenHadamard.order_one_zero_seq_summable_rpow_neg hA_nn
    (hasOrderOneGrowth_completedLFunction hprim hχ)
    (completedLFunction_zero_ne_zero hprim hχ) hinj hzeros hσ

/-- Specialization `σ = 2`: `∑' n, (‖ρ n‖ ^ 2)⁻¹ < ∞` for every primitive `χ ≠ 1`. -/
theorem completedLFunction_zero_seq_summable_inv_sq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {ρ : ℕ → ℂ} (hinj : Function.Injective ρ)
    (hzeros : ∀ n, DirichletCharacter.completedLFunction χ (ρ n) = 0) :
    Summable (fun n => (‖ρ n‖ ^ 2)⁻¹) := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hA_nn : 0 ≤ 15 * (2 * Real.log (q : ℝ) + 1) := by
    have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
    positivity
  exact Stage5JensenHadamard.order_one_zero_seq_summable_inv_sq hA_nn
    (hasOrderOneGrowth_completedLFunction hprim hχ)
    (completedLFunction_zero_ne_zero hprim hχ) hinj hzeros

/-! ## Section 3: Unconditional Zero-Counting Bounds & Direct `ZeroCountBound` Discharge -/

/-- Shifted Stirling vertical-strip upper bound on `1 / 4 ≤ w.re ≤ b` via `Γ(w) = Γ(w + 1) / w`
and `Stage5StirlingPhragmen.norm_Gamma_strip_stirling_upper`. -/
lemma norm_Gamma_strip_stirling_quarter_le (b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 1 / 4 ≤ w.re → w.re ≤ b →
      ‖Complex.Gamma w‖ ≤ C * (|w.im| + 2) ^ (b + 1 / 2) * Real.exp (-Real.pi * |w.im| / 2) := by
  obtain ⟨C₀, hC₀, hS⟩ := Stage5StirlingPhragmen.norm_Gamma_strip_stirling_upper (b + 1)
  refine ⟨4 * C₀, by positivity, fun w hw1 hwb => ?_⟩
  have hw_ne : w ≠ 0 := fun h => by simp [h] at hw1; norm_num at hw1
  have hw_norm : (1 / 4 : ℝ) ≤ ‖w‖ :=
    hw1.trans (le_trans (le_abs_self w.re) (Complex.abs_re_le_norm w))
  have hshift : Complex.Gamma (w + 1) = w * Complex.Gamma w := Complex.Gamma_add_one w hw_ne
  have hnorm_div : ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ / ‖w‖ := by
    rw [hshift, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hw_ne)]
  have hw1_eq : ((w.re + 1 : ℝ) : ℂ) + I * (w.im : ℂ) = w + 1 := by
    apply Complex.ext <;> simp
  have hmem : w.re + 1 ∈ Set.Icc (1 / 2 : ℝ) (b + 1) := ⟨by linarith, by linarith⟩
  have hG1 : ‖Complex.Gamma (w + 1)‖ ≤
      C₀ * (|w.im| + 2) ^ (w.re + 1 / 2) * Real.exp (-Real.pi * |w.im| / 2) := by
    have h := hS (w.re + 1) hmem w.im
    rw [hw1_eq] at h
    have hexp : w.re + 1 - 1 / 2 = w.re + 1 / 2 := by ring
    rwa [hexp] at h
  have hpow_le : (|w.im| + 2) ^ (w.re + 1 / 2) ≤ (|w.im| + 2) ^ (b + 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg w.im]) (by linarith)
  rw [hnorm_div]
  calc ‖Complex.Gamma (w + 1)‖ / ‖w‖
      ≤ (C₀ * (|w.im| + 2) ^ (w.re + 1 / 2) * Real.exp (-Real.pi * |w.im| / 2)) / (1 / 4) :=
        div_le_div₀ (by positivity) hG1 (by norm_num) hw_norm
    _ = 4 * C₀ * (|w.im| + 2) ^ (w.re + 1 / 2) * Real.exp (-Real.pi * |w.im| / 2) := by ring
    _ ≤ 4 * C₀ * (|w.im| + 2) ^ (b + 1 / 2) * Real.exp (-Real.pi * |w.im| / 2) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_le (by positivity)) (Real.exp_pos _).le

/-- Elementary exponential upper bound for `Complex.sin (π * u)`:
`‖Complex.sin ((Real.pi : ℂ) * u)‖ ≤ Real.exp (Real.pi * |u.im|)`. -/
lemma norm_sin_pi_mul_le (u : ℂ) :
    ‖Complex.sin ((Real.pi : ℂ) * u)‖ ≤ Real.exp (Real.pi * |u.im|) := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  have h1 : ‖Complex.exp (-((Real.pi : ℂ) * u) * I)‖ ≤ Real.exp (Real.pi * |u.im|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-((Real.pi : ℂ) * u) * I).re = Real.pi * u.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    exact mul_le_mul_of_nonneg_left (le_abs_self u.im) Real.pi_pos.le
  have h2 : ‖Complex.exp (((Real.pi : ℂ) * u) * I)‖ ≤ Real.exp (Real.pi * |u.im|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (((Real.pi : ℂ) * u) * I).re = -(Real.pi * u.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have : -u.im ≤ |u.im| := neg_le_abs u.im
    nlinarith [Real.pi_pos]
  calc ‖Complex.exp (-((Real.pi : ℂ) * u) * I) - Complex.exp (((Real.pi : ℂ) * u) * I)‖ / 2
      ≤ (‖Complex.exp (-((Real.pi : ℂ) * u) * I)‖ +
          ‖Complex.exp (((Real.pi : ℂ) * u) * I)‖) / 2 :=
        div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ ≤ (Real.exp (Real.pi * |u.im|) + Real.exp (Real.pi * |u.im|)) / 2 := by linarith
    _ = Real.exp (Real.pi * |u.im|) := by ring

/-- **Unconditional Polynomial Vertical-Strip Bound for `DirichletCharacter.LFunction χ`** on
`-3 ≤ z.re ≤ 7`: there exists an absolute constant `K > 0` such that for EVERY primitive `χ ≠ 1`
mod `q` and EVERY `z : ℂ` with `-3 ≤ z.re ≤ 7`,
`‖LFunction χ z‖ ≤ K * (q * (|z.im| + 2)) ^ 7`. -/
theorem norm_LFunction_strip_poly_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ z : ℂ, -3 ≤ z.re → z.re ≤ 7 →
          ‖DirichletCharacter.LFunction χ z‖ ≤ K * ((q : ℝ) * (|z.im| + 2)) ^ 7 := by
  obtain ⟨C₁, hC₁_pos, hG_stirling⟩ := norm_Gamma_strip_stirling_quarter_le (5 / 2)
  -- Helper: on `1 / 2 ≤ w.re`, `‖LFunction ψ w‖ ≤ 4 * q^2 * (|w.im| + 2)` for primitive `ψ ≠ 1`.
  have hRightHalf : ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
      ψ.IsPrimitive → ψ ≠ 1 → ∀ w : ℂ, 1 / 2 ≤ w.re →
        ‖DirichletCharacter.LFunction ψ w‖ ≤ 4 * (q : ℝ) ^ 2 * (|w.im| + 2) := by
    intro q _ ψ hprimψ hψ w hw
    have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hψ
    have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
    rcases le_or_gt 2 w.re with hw2 | hw2
    · have h2 := norm_LFunction_le_two_of_two_le_re ψ hw2
      have hbig : 2 ≤ 4 * (q : ℝ) ^ 2 * (|w.im| + 2) := by
        have : 2 ≤ |w.im| + 2 := by linarith [abs_nonneg w.im]
        nlinarith
      exact h2.trans hbig
    · have hw0 : 0 < w.re := by linarith
      have hw_eq : (w.re : ℂ) + I * (w.im : ℂ) = w := by
        apply Complex.ext <;> simp
      have hpv : ‖DirichletCharacter.LFunction ψ w‖ ≤
          (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|w.im| + 2) / w.re := by
        simpa only [hw_eq] using
          Stage5DirichletLZeroFree.norm_LFunction_strip_le_polya_vinogradov hprimψ hψ hw0 hw2.le w.im
      have hsqrt_le : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
        calc Real.sqrt (q : ℝ) ≤ Real.sqrt ((q : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = (q : ℝ) := Real.sqrt_sq hqR_pos.le
      have hlogq_le : Real.log (q : ℝ) + 2 ≤ 2 * (q : ℝ) := by
        have h1 : Real.log (q : ℝ) ≤ (q : ℝ) :=
          le_trans (Real.log_le_sub_one_of_pos hqR_pos) (by linarith)
        linarith
      have hB_le : Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2) ≤ 2 * (q : ℝ) ^ 2 := by
        calc Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)
            ≤ (q : ℝ) * (2 * (q : ℝ)) :=
              mul_le_mul hsqrt_le hlogq_le (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ q)])
                hqR_pos.le
          _ = 2 * (q : ℝ) ^ 2 := by ring
      have hdiv : ((Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|w.im| + 2)) / w.re ≤
          2 * ((Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|w.im| + 2)) := by
        rw [div_le_iff₀ hw0]
        have hnn : 0 ≤ (Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 2)) * (|w.im| + 2) := by
          have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
          positivity
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hB_le (by positivity : 0 ≤ |w.im| + 2)
      linarith [hpv.trans hdiv]
  refine ⟨max 4 (4 * C₁ ^ 2), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    fun q _ χ hprim hχ z hz1 _hz7 => ?_⟩
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hq1 : q ≠ 1 := by omega
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have ht_ge2 : 2 ≤ |z.im| + 2 := by linarith [abs_nonneg z.im]
  rcases le_or_gt (1 / 2 : ℝ) z.re with hz_half | hz_half
  · have h1 := hRightHalf q χ hprim hχ z hz_half
    have hpow : (q : ℝ) ^ 2 * (|z.im| + 2) ≤ ((q : ℝ) * (|z.im| + 2)) ^ 7 := by
      have hq_pow : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 7 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      have ht_pow : |z.im| + 2 ≤ (|z.im| + 2) ^ 7 := by
        calc |z.im| + 2 = (|z.im| + 2) ^ 1 := (pow_one _).symm
          _ ≤ (|z.im| + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
      rw [mul_pow]
      exact mul_le_mul hq_pow ht_pow (by positivity) (by positivity)
    have hK4 : (4 : ℝ) ≤ max 4 (4 * C₁ ^ 2) := le_max_left _ _
    calc ‖DirichletCharacter.LFunction χ z‖
        ≤ 4 * ((q : ℝ) ^ 2 * (|z.im| + 2)) := by linarith
      _ ≤ max 4 (4 * C₁ ^ 2) * ((q : ℝ) * (|z.im| + 2)) ^ 7 :=
          mul_le_mul hK4 hpow (by positivity) (by positivity)
  · -- Region `z.re < 1 / 2` (with `-3 ≤ z.re`): reflect via functional equation + Euler reflection!
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (.inr hq1)]
    by_cases hG0 : DirichletCharacter.gammaFactor χ z = 0
    · rw [hG0, div_zero, norm_zero]
      positivity
    · have hz_eq : z = 1 - (1 - z) := by ring
      have h1z_re : 1 / 2 ≤ (1 - z).re := by simp; linarith
      have h1z_pos : 0 < (1 - z).re := by linarith
      have hfe : DirichletCharacter.completedLFunction χ z =
          (q : ℂ) ^ (1 / 2 - z) * DirichletCharacter.rootNumber χ *
            DirichletCharacter.LFunction χ⁻¹ (1 - z) *
            DirichletCharacter.gammaFactor χ⁻¹ (1 - z) := by
        have h := hprim.completedLFunction_one_sub (1 - z)
        rw [← hz_eq] at h
        have hexp : (1 - z) - (1 / 2 : ℂ) = 1 / 2 - z := by ring
        rw [hexp, completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ⁻¹ h1z_pos] at h
        rw [h]; ring
      rw [hfe, mul_div_assoc, norm_mul, norm_mul, norm_mul, norm_rootNumber_eq_one hprim, mul_one,
        Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
      have hq_exp : (1 / 2 - z).re = 1 / 2 - z.re := by simp
      rw [hq_exp]
      -- Bound `q^(1/2 - z.re) ≤ q^4`
      have hqpow_le : (q : ℝ) ^ (1 / 2 - z.re) ≤ (q : ℝ) ^ 4 := by
        calc (q : ℝ) ^ (1 / 2 - z.re)
            ≤ (q : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = (q : ℝ) ^ 4 := Real.rpow_natCast (q : ℝ) 4
      -- Bound `‖LFunction χ⁻¹ (1 - z)‖ ≤ 4 * q^2 * (|z.im| + 2)`
      have hL_inv : ‖DirichletCharacter.LFunction χ⁻¹ (1 - z)‖ ≤ 4 * (q : ℝ) ^ 2 * (|z.im| + 2) := by
        have h := hRightHalf q χ⁻¹ (isPrimitive_inv hprim) (inv_ne_one_of_ne_one hχ) (1 - z) h1z_re
        have him : |(1 - z).im| = |z.im| := by simp
        rwa [him] at h
      -- Bound the gamma-factor ratio `‖gammaFactor χ⁻¹ (1 - z) / gammaFactor χ z‖ ≤ C₁^2 * (|z.im| + 2)^6`
      have hGammaRatio :
          ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - z) / DirichletCharacter.gammaFactor χ z‖ ≤
            C₁ ^ 2 * (|z.im| + 2) ^ 6 := by
        -- Unified bound on `‖Gammaℝ (1 - z + a) / Gammaℝ (z + a)‖` for `a ∈ {0, 1}`!
        have hratio_aux : ∀ a : ℝ, (a = 0 ∨ a = 1) → Complex.Gammaℝ (z + (a : ℂ)) ≠ 0 →
            ‖Complex.Gammaℝ (1 - z + (a : ℂ)) / Complex.Gammaℝ (z + (a : ℂ))‖ ≤
              C₁ ^ 2 * (|z.im| + 2) ^ 6 := by
          intro a ha hGa_ne
          set u : ℂ := (z + (a : ℂ)) / 2
          set w₁ : ℂ := (1 - z + (a : ℂ)) / 2
          set w₂ : ℂ := 1 - u
          have ha_lo : 0 ≤ a := by rcases ha with rfl | rfl <;> norm_num
          have ha_hi : a ≤ 1 := by rcases ha with rfl | rfl <;> norm_num
          have hGu_ne : Complex.Gamma u ≠ 0 := by
            intro h0
            apply hGa_ne
            rw [Complex.Gammaℝ_def]
            change (Real.pi : ℂ) ^ (-(z + (a : ℂ)) / 2) * Complex.Gamma u = 0
            rw [h0, mul_zero]
          have hsin_ne : Complex.sin ((Real.pi : ℂ) * u) ≠ 0 := by
            intro hsin0
            rw [Complex.sin_eq_zero_iff] at hsin0
            rcases hsin0 with ⟨k, hk⟩
            have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
            have hu_eq : u = (k : ℂ) := by
              apply mul_left_cancel₀ hpiC
              exact hk.trans (mul_comm _ _)
            rcases le_or_gt k 0 with hk0 | hk1
            · have hk_neg : u = -(((-k).toNat : ℕ) : ℂ) := by
                rw [hu_eq]
                have hnat : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
                have hcast : (((-k).toNat : ℕ) : ℂ) = -(k : ℂ) := by
                  exact_mod_cast hnat
                rw [hcast, neg_neg]
              rw [hk_neg, Complex.Gamma_neg_nat_eq_zero] at hGu_ne
              exact hGu_ne rfl
            · have hure : u.re = (k : ℝ) := by rw [hu_eq]; simp
              have hure_le : u.re ≤ 3 / 4 := by
                dsimp only [u]; simp; linarith
              have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
              linarith
          have hrefl := Complex.Gamma_mul_Gamma_one_sub u
          have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
          have hinvG : (Complex.Gamma u)⁻¹ =
              Complex.Gamma w₂ * Complex.sin ((Real.pi : ℂ) * u) / (Real.pi : ℂ) := by
            dsimp only [w₂]
            have h1 : Complex.Gamma u * (Complex.Gamma (1 - u) * Complex.sin ((Real.pi : ℂ) * u)) =
                (Real.pi : ℂ) := by
              rw [← mul_assoc, hrefl, div_mul_cancel₀ _ hsin_ne]
            have h2 : (Complex.Gamma u)⁻¹ * (Real.pi : ℂ) =
                Complex.Gamma (1 - u) * Complex.sin ((Real.pi : ℂ) * u) := by
              calc (Complex.Gamma u)⁻¹ * (Real.pi : ℂ)
                  = (Complex.Gamma u)⁻¹ * (Complex.Gamma u *
                      (Complex.Gamma (1 - u) * Complex.sin ((Real.pi : ℂ) * u))) := by rw [h1]
                _ = Complex.Gamma (1 - u) * Complex.sin ((Real.pi : ℂ) * u) :=
                    inv_mul_cancel_left₀ hGu_ne _
            exact eq_div_of_mul_eq hpiC h2
          -- Simplify `Gammaℝ (1 - z + a) / Gammaℝ (z + a)`
          have hpi_ratio :
              (Real.pi : ℂ) ^ (-(1 - z + (a : ℂ)) / 2) / (Real.pi : ℂ) ^ (-(z + (a : ℂ)) / 2) =
                (Real.pi : ℂ) ^ (z - 1 / 2) := by
            rw [← Complex.cpow_sub _ _ hpiC]
            congr 1
            ring
          have hfrac_eq :
              Complex.Gammaℝ (1 - z + (a : ℂ)) / Complex.Gammaℝ (z + (a : ℂ)) =
                (Real.pi : ℂ) ^ (z - 1 / 2) * Complex.Gamma w₁ *
                  (Complex.Gamma w₂ * Complex.sin ((Real.pi : ℂ) * u) / (Real.pi : ℂ)) := by
            rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
            change ((Real.pi : ℂ) ^ (-(1 - z + (a : ℂ)) / 2) * Complex.Gamma w₁) /
              ((Real.pi : ℂ) ^ (-(z + (a : ℂ)) / 2) * Complex.Gamma u) = _
            rw [div_mul_eq_div_div, mul_div_right_comm, hpi_ratio, div_eq_mul_inv, hinvG]
          rw [hfrac_eq, norm_mul, norm_mul, norm_div, norm_mul,
            Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
            Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
          have hpi_z : Real.pi ^ (z - (1 / 2 : ℂ)).re ≤ 1 := by
            have hre : (z - (1 / 2 : ℂ)).re = z.re - 1 / 2 := by simp
            rw [hre]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) (by linarith)
          have hw1_re1 : 1 / 4 ≤ w₁.re := by dsimp only [w₁]; simp; linarith
          have hw1_re2 : w₁.re ≤ 5 / 2 := by dsimp only [w₁]; simp; linarith
          have hw2_re1 : 1 / 4 ≤ w₂.re := by dsimp only [w₂, u]; simp; linarith
          have hw2_re2 : w₂.re ≤ 5 / 2 := by dsimp only [w₂, u]; simp; linarith
          have hw1_im : |w₁.im| = |z.im| / 2 := by
            dsimp only [w₁]; simp [abs_div]
          have hw2_im : |w₂.im| = |z.im| / 2 := by
            dsimp only [w₂, u]; simp [abs_div]
          have hu_im : |u.im| = |z.im| / 2 := by
            dsimp only [u]; simp [abs_div]
          have hGw1 := hG_stirling w₁ hw1_re1 hw1_re2
          have hGw2 := hG_stirling w₂ hw2_re1 hw2_re2
          rw [hw1_im] at hGw1
          rw [hw2_im] at hGw2
          have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * u)‖ ≤ Real.exp (Real.pi * |z.im| / 2) := by
            have h := norm_sin_pi_mul_le u
            rw [hu_im] at h
            simpa [mul_div_assoc] using h
          have hbase_half : |z.im| / 2 + 2 ≤ |z.im| + 2 := by linarith [abs_nonneg z.im]
          have hpow3 : (|z.im| / 2 + 2) ^ ((5 / 2 : ℝ) + 1 / 2) ≤ (|z.im| + 2) ^ 3 := by
            have h3 : (5 / 2 : ℝ) + 1 / 2 = (3 : ℕ) := by norm_num
            rw [h3, Real.rpow_natCast]
            exact pow_le_pow_left₀ (by positivity) hbase_half 3
          have hGw1' : ‖Complex.Gamma w₁‖ ≤
              C₁ * (|z.im| + 2) ^ 3 * Real.exp (-Real.pi * |z.im| / 4) := by
            have he : -Real.pi * (|z.im| / 2) / 2 = -Real.pi * |z.im| / 4 := by ring
            rw [he] at hGw1
            exact hGw1.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow3 hC₁_pos.le) (Real.exp_pos _).le)
          have hGw2' : ‖Complex.Gamma w₂‖ ≤
              C₁ * (|z.im| + 2) ^ 3 * Real.exp (-Real.pi * |z.im| / 4) := by
            have he : -Real.pi * (|z.im| / 2) / 2 = -Real.pi * |z.im| / 4 := by ring
            rw [he] at hGw2
            exact hGw2.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow3 hC₁_pos.le) (Real.exp_pos _).le)
          have hdiv_pi :
              ‖Complex.Gamma w₂‖ * ‖Complex.sin ((Real.pi : ℂ) * u)‖ / Real.pi ≤
                ‖Complex.Gamma w₂‖ * ‖Complex.sin ((Real.pi : ℂ) * u)‖ :=
            div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by linarith [Real.two_le_pi])
          have hexp_cancel :
              Real.exp (-Real.pi * |z.im| / 4) * Real.exp (-Real.pi * |z.im| / 4) *
                Real.exp (Real.pi * |z.im| / 2) = 1 := by
            rw [← Real.exp_add, ← Real.exp_add]
            have : -Real.pi * |z.im| / 4 + -Real.pi * |z.im| / 4 + Real.pi * |z.im| / 2 = 0 := by
              ring
            rw [this, Real.exp_zero]
          calc Real.pi ^ (z - (1 / 2 : ℂ)).re * ‖Complex.Gamma w₁‖ *
                (‖Complex.Gamma w₂‖ * ‖Complex.sin ((Real.pi : ℂ) * u)‖ / Real.pi)
              ≤ 1 * ‖Complex.Gamma w₁‖ *
                  (‖Complex.Gamma w₂‖ * ‖Complex.sin ((Real.pi : ℂ) * u)‖) := by
                refine mul_le_mul
                  (mul_le_mul_of_nonneg_right hpi_z (norm_nonneg _))
                  hdiv_pi (by positivity) (by positivity)
            _ = ‖Complex.Gamma w₁‖ * ‖Complex.Gamma w₂‖ * ‖Complex.sin ((Real.pi : ℂ) * u)‖ := by
                ring
            _ ≤ (C₁ * (|z.im| + 2) ^ 3 * Real.exp (-Real.pi * |z.im| / 4)) *
                  (C₁ * (|z.im| + 2) ^ 3 * Real.exp (-Real.pi * |z.im| / 4)) *
                  Real.exp (Real.pi * |z.im| / 2) := by
                refine mul_le_mul (mul_le_mul hGw1' hGw2' (norm_nonneg _) (by positivity))
                  hsin_le (norm_nonneg _) (by positivity)
            _ = C₁ ^ 2 * (|z.im| + 2) ^ 6 *
                  (Real.exp (-Real.pi * |z.im| / 4) * Real.exp (-Real.pi * |z.im| / 4) *
                    Real.exp (Real.pi * |z.im| / 2)) := by ring
            _ = C₁ ^ 2 * (|z.im| + 2) ^ 6 := by rw [hexp_cancel, mul_one]
        rcases χ.even_or_odd with heven | hodd
        · have heven_inv : χ⁻¹.Even := (even_inv_iff χ).mpr heven
          rw [heven_inv.gammaFactor_def, heven.gammaFactor_def]
          rw [heven.gammaFactor_def] at hG0
          simpa using hratio_aux 0 (.inl rfl) (by simpa using hG0)
        · have hodd_inv : χ⁻¹.Odd := by
            refine χ⁻¹.even_or_odd.resolve_left fun h => ?_
            have h1 : χ (-1) = 1 := (even_inv_iff χ).mp h
            have h2 : χ (-1) = -1 := hodd
            rw [h1] at h2
            norm_num at h2
          rw [hodd_inv.gammaFactor_def, hodd.gammaFactor_def]
          rw [hodd.gammaFactor_def] at hG0
          simpa using hratio_aux 1 (.inr rfl) (by simpa using hG0)
      have hq6_le : (q : ℝ) ^ 6 ≤ (q : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have hK_ge : 4 * C₁ ^ 2 ≤ max 4 (4 * C₁ ^ 2) := le_max_right _ _
      calc (q : ℝ) ^ (1 / 2 - z.re) * ‖DirichletCharacter.LFunction χ⁻¹ (1 - z)‖ *
            ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - z) / DirichletCharacter.gammaFactor χ z‖
          ≤ (q : ℝ) ^ 4 * (4 * (q : ℝ) ^ 2 * (|z.im| + 2)) * (C₁ ^ 2 * (|z.im| + 2) ^ 6) := by
            refine mul_le_mul (mul_le_mul hqpow_le hL_inv (norm_nonneg _) (by positivity))
              hGammaRatio (norm_nonneg _) (by positivity)
        _ = (4 * C₁ ^ 2) * ((q : ℝ) ^ 6 * (|z.im| + 2) ^ 7) := by ring
        _ ≤ max 4 (4 * C₁ ^ 2) * ((q : ℝ) ^ 7 * (|z.im| + 2) ^ 7) :=
            mul_le_mul hK_ge (mul_le_mul_of_nonneg_right hq6_le (by positivity))
              (by positivity) (by positivity)
        _ = max 4 (4 * C₁ ^ 2) * ((q : ℝ) * (|z.im| + 2)) ^ 7 := by rw [mul_pow]

/-- **UNCONDITIONAL UNIT-INTERVAL ZERO-COUNT BOUND `N(T+1, χ) - N(T, χ) ≤ C log(q (|T| + 2))`**
(`0` assumptions, directly on EVERY primitive Mathlib `DirichletCharacter.LFunction`, `χ ≠ 1`):
via shifted-ball Jensen zero counting centered at `s₀ = 2 + I * T` (`r = 5 / 2, R = 5`). -/
theorem LFunction_zero_count_unit_interval_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, ∀ Z : Finset ℂ,
          (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0 ∧
            |ρ.im - T| ≤ 1) →
          (Z.card : ℝ) ≤ C * Real.log ((q : ℝ) * (|T| + 2)) := by
  classical
  obtain ⟨K, hK_pos, hpoly⟩ := norm_LFunction_strip_poly_bound
  set C : ℝ := (max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 + 7) / Real.log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC_pos : 0 < C := by
    dsimp only [C]
    exact div_pos (by linarith [le_max_right (Real.log (4 * K * (4 : ℝ) ^ 7)) 0]) hlog2_pos
  refine ⟨C, hC_pos, fun q _ χ hprim hχ T Z hZ => ?_⟩
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hT_ge2 : 2 ≤ |T| + 2 := by linarith [abs_nonneg T]
  have hqT_ge4 : 4 ≤ (q : ℝ) * (|T| + 2) := by nlinarith
  have hlog_ge1 : 1 ≤ Real.log ((q : ℝ) * (|T| + 2)) := by
    have h4 : (1 : ℝ) < Real.log 4 := by
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_gt_d9]
    exact h4.le.trans (Real.log_le_log (by norm_num) hqT_ge4)
  set s₀ : ℂ := (2 : ℂ) + I * (T : ℂ)
  set f : ℂ → ℂ := fun w => DirichletCharacter.LFunction χ (s₀ + w)
  have hf_diff : Differentiable ℂ f :=
    (DirichletCharacter.differentiable_LFunction hχ).comp (differentiable_id.const_add s₀)
  have hf0_ge : (1 / 4 : ℝ) ≤ ‖f 0‖ := by
    dsimp only [f, s₀]
    rw [add_zero]
    exact quarter_le_norm_LFunction_of_two_le_re χ (by simp)
  have hf0_ne : f 0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hf0_ge
    norm_num at hf0_ge
  set M : ℝ := K * (4 : ℝ) ^ 7 * ((q : ℝ) * (|T| + 2)) ^ 7
  have hM_bound : ∀ w ∈ sphere (0 : ℂ) 5, ‖f w‖ ≤ M := by
    intro w hw
    have hw_norm : ‖w‖ = 5 := mem_sphere_zero_iff_norm.mp hw
    have hw_re : |w.re| ≤ 5 := (Complex.abs_re_le_norm w).trans hw_norm.le
    have hw_im : |w.im| ≤ 5 := (Complex.abs_im_le_norm w).trans hw_norm.le
    have hre_lo : -3 ≤ (s₀ + w).re := by
      have := (abs_le.mp hw_re).1
      simp only [s₀, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, zero_mul, sub_zero, Complex.re_ofNat, Complex.ofReal_im, mul_zero]
      linarith
    have hre_hi : (s₀ + w).re ≤ 7 := by
      have := (abs_le.mp hw_re).2
      simp only [s₀, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, zero_mul, sub_zero, Complex.re_ofNat, Complex.ofReal_im, mul_zero]
      linarith
    have him_le : |(s₀ + w).im| + 2 ≤ 4 * (|T| + 2) := by
      have him_eq : (s₀ + w).im = T + w.im := by simp [s₀]
      rw [him_eq]
      have htri : |T + w.im| ≤ |T| + |w.im| := abs_add_le T w.im
      linarith [abs_nonneg T]
    have hbase_le : (q : ℝ) * (|(s₀ + w).im| + 2) ≤ 4 * ((q : ℝ) * (|T| + 2)) := by
      calc (q : ℝ) * (|(s₀ + w).im| + 2)
          ≤ (q : ℝ) * (4 * (|T| + 2)) := mul_le_mul_of_nonneg_left him_le hqR_pos.le
        _ = 4 * ((q : ℝ) * (|T| + 2)) := by ring
    calc ‖f w‖
        ≤ K * ((q : ℝ) * (|(s₀ + w).im| + 2)) ^ 7 := hpoly q χ hprim hχ (s₀ + w) hre_lo hre_hi
      _ ≤ K * (4 * ((q : ℝ) * (|T| + 2))) ^ 7 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hbase_le 7) hK_pos.le
      _ = M := by dsimp only [M]; rw [mul_pow]; ring
  set Z' : Finset ℂ := Z.image (fun ρ => ρ - s₀)
  have hcard : Z'.card = Z.card :=
    Finset.card_image_of_injective Z (fun a b h => by linear_combination h)
  have hZ'_ball : ∀ w ∈ Z', w ∈ closedBall (0 : ℂ) (5 / 2) := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨ρ, hρ, rfl⟩
    obtain ⟨hρ0, hρ1, _, hρim⟩ := hZ ρ hρ
    rw [mem_closedBall_zero_iff]
    have hre_sq : ((ρ - s₀).re) ^ 2 ≤ 4 := by
      have hre : (ρ - s₀).re = ρ.re - 2 := by simp [s₀]
      rw [hre]; nlinarith
    have him_sq : ((ρ - s₀).im) ^ 2 ≤ 1 := by
      have him : (ρ - s₀).im = ρ.im - T := by simp [s₀]
      rw [him, ← sq_abs]
      nlinarith [abs_nonneg (ρ.im - T)]
    have hns : ‖ρ - s₀‖ ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith
    nlinarith [norm_nonneg (ρ - s₀)]
  have hZ'_zero : ∀ w ∈ Z', f w = 0 := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨ρ, hρ, rfl⟩
    dsimp only [f]
    rw [add_sub_cancel]
    exact (hZ ρ hρ).2.2.1
  have hj := Stage5JensenHadamard.jensen_zero_count_le
    (r := 5 / 2) (R := 5) (M := M) (by norm_num) (by norm_num)
    hf_diff.diffContOnCl hf0_ne hM_bound Z' hZ'_ball hZ'_zero
  rw [hcard] at hj
  have hdiv5 : (5 : ℝ) / (5 / 2) = 2 := by norm_num
  rw [hdiv5] at hj
  have hratio_le : M / ‖f 0‖ ≤ (4 * K * (4 : ℝ) ^ 7) * ((q : ℝ) * (|T| + 2)) ^ 7 := by
    have h1 : M / ‖f 0‖ ≤ M / (1 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hf0_ge
    refine h1.trans_eq ?_
    dsimp only [M]; ring
  have hlog_le : Real.log (M / ‖f 0‖) ≤
      (max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 + 7) * Real.log ((q : ℝ) * (|T| + 2)) := by
    have hpos_lhs : 0 < M / ‖f 0‖ := div_pos (by positivity) (norm_pos_iff.mpr hf0_ne)
    calc Real.log (M / ‖f 0‖)
        ≤ Real.log ((4 * K * (4 : ℝ) ^ 7) * ((q : ℝ) * (|T| + 2)) ^ 7) :=
          Real.log_le_log hpos_lhs hratio_le
      _ = Real.log (4 * K * (4 : ℝ) ^ 7) + 7 * Real.log ((q : ℝ) * (|T| + 2)) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
          push_cast; ring
      _ ≤ max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 * Real.log ((q : ℝ) * (|T| + 2)) +
            7 * Real.log ((q : ℝ) * (|T| + 2)) := by
          have h1 : Real.log (4 * K * (4 : ℝ) ^ 7) ≤ max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 :=
            le_max_left _ 0
          have h2 : 0 ≤ max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 := le_max_right _ 0
          nlinarith
      _ = (max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 + 7) * Real.log ((q : ℝ) * (|T| + 2)) := by ring
  calc (Z.card : ℝ)
      ≤ Real.log (M / ‖f 0‖) / Real.log 2 := hj
    _ ≤ ((max (Real.log (4 * K * (4 : ℝ) ^ 7)) 0 + 7) *
          Real.log ((q : ℝ) * (|T| + 2))) / Real.log 2 :=
        div_le_div_of_nonneg_right hlog_le hlog2_pos.le
    _ = C * Real.log ((q : ℝ) * (|T| + 2)) := by dsimp only [C]; ring

/-- **UNCONDITIONAL CUMULATIVE HEIGHT ZERO-COUNT BOUND (`T ≥ 1`)**:
`N(T, χ) ≤ C * T * log (q * (T + 2))` for ALL `T ≥ 1` and ALL primitive `χ ≠ 1` mod `q`. -/
theorem LFunction_zero_count_height_ge_one_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 1 ≤ T → ∀ Z : Finset ℂ,
          (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0 ∧ |ρ.im| ≤ T) →
          (Z.card : ℝ) ≤ C * T * Real.log ((q : ℝ) * (T + 2)) := by
  classical
  obtain ⟨C₀, hC₀_pos, hunit⟩ := LFunction_zero_count_unit_interval_le
  refine ⟨12 * C₀, by positivity, fun q _ χ hprim hχ T hT Z hZ => ?_⟩
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR_ge2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by linarith
  set N : ℕ := ⌈T⌉₊
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  have hN_ge : T ≤ (N : ℝ) := Nat.le_ceil T
  have hN_le : (N : ℝ) ≤ 2 * T := by
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ T by linarith)
    linarith
  set I : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hcover : Z ⊆ I.biUnion (fun k => Z.filter fun ρ => |ρ.im - (k : ℝ)| ≤ 1) := by
    intro ρ hρ
    rw [Finset.mem_biUnion]
    set k : ℤ := round ρ.im
    have hk_half : |ρ.im - (k : ℝ)| ≤ 1 / 2 := abs_sub_round ρ.im
    have hk_dist : |ρ.im - (k : ℝ)| ≤ 1 := hk_half.trans (by norm_num)
    have hρim := (hZ ρ hρ).2.2.2
    have hle_N : -(N : ℝ) ≤ ρ.im ∧ ρ.im ≤ (N : ℝ) := by
      have h1 := abs_le.mp hρim
      exact ⟨by linarith, by linarith⟩
    have hk_mem : k ∈ I := by
      rw [Finset.mem_Icc]
      have hdiff := abs_le.mp hk_half
      constructor
      · have hlt : ((-(N : ℤ) - 1 : ℤ) : ℝ) < (k : ℝ) := by push_cast; linarith
        have hltZ : -(N : ℤ) - 1 < k := Int.cast_lt.mp hlt
        omega
      · have hlt : (k : ℝ) < (((N : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
        have hltZ : k < (N : ℤ) + 1 := Int.cast_lt.mp hlt
        omega
    exact ⟨k, hk_mem, Finset.mem_filter.mpr ⟨hρ, hk_dist⟩⟩
  have hcard_le : (Z.card : ℝ) ≤
      ∑ k ∈ I, ((Z.filter fun ρ => |ρ.im - (k : ℝ)| ≤ 1).card : ℝ) := by
    have hnat : Z.card ≤ ∑ k ∈ I, (Z.filter fun ρ => |ρ.im - (k : ℝ)| ≤ 1).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  have hterm : ∀ k ∈ I,
      ((Z.filter fun ρ => |ρ.im - (k : ℝ)| ≤ 1).card : ℝ) ≤
        2 * C₀ * Real.log ((q : ℝ) * (T + 2)) := by
    intro k hk
    have h1 := hunit q χ hprim hχ (k : ℝ) (Z.filter fun ρ => |ρ.im - (k : ℝ)| ≤ 1)
      (fun ρ hρ => by
        rcases Finset.mem_filter.mp hρ with ⟨hρZ, hρk⟩
        obtain ⟨h0, h1', hz, _⟩ := hZ ρ hρZ
        exact ⟨h0, h1', hz, hρk⟩)
    have hk_abs : |(k : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le]
      rcases Finset.mem_Icc.mp hk with ⟨hlo, hhi⟩
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    have hlog_le : Real.log ((q : ℝ) * (|(k : ℝ)| + 2)) ≤ 2 * Real.log ((q : ℝ) * (T + 2)) := by
      have harg : (q : ℝ) * (|(k : ℝ)| + 2) ≤ ((q : ℝ) * (T + 2)) ^ 2 := by
        have hstep : |(k : ℝ)| + 2 ≤ 2 * (T + 2) := by linarith
        have hqT_ge2 : (2 : ℝ) ≤ (q : ℝ) * (T + 2) := by nlinarith
        calc (q : ℝ) * (|(k : ℝ)| + 2)
            ≤ (q : ℝ) * (2 * (T + 2)) := mul_le_mul_of_nonneg_left hstep hqR_pos.le
          _ = 2 * ((q : ℝ) * (T + 2)) := by ring
          _ ≤ ((q : ℝ) * (T + 2)) ^ 2 := by nlinarith
      calc Real.log ((q : ℝ) * (|(k : ℝ)| + 2))
          ≤ Real.log (((q : ℝ) * (T + 2)) ^ 2) :=
            Real.log_le_log (by positivity) harg
        _ = 2 * Real.log ((q : ℝ) * (T + 2)) := by rw [Real.log_pow]; norm_num
    calc ((Z.filter fun ρ => |ρ.im - (k : ℝ)| ≤ 1).card : ℝ)
        ≤ C₀ * Real.log ((q : ℝ) * (|(k : ℝ)| + 2)) := h1
      _ ≤ C₀ * (2 * Real.log ((q : ℝ) * (T + 2))) :=
          mul_le_mul_of_nonneg_left hlog_le hC₀_pos.le
      _ = 2 * C₀ * Real.log ((q : ℝ) * (T + 2)) := by ring
  have hI_card : (I.card : ℝ) ≤ 6 * T := by
    have hcard_eq : I.card = 2 * N + 1 := by
      dsimp only [I]
      rw [Int.card_Icc]
      omega
    rw [hcard_eq]
    push_cast
    have h1N : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
    linarith
  have hlog_nn : 0 ≤ Real.log ((q : ℝ) * (T + 2)) := Real.log_nonneg (by nlinarith)
  calc (Z.card : ℝ)
      ≤ ∑ k ∈ I, ((Z.filter fun ρ => |ρ.im - (k : ℝ)| ≤ 1).card : ℝ) := hcard_le
    _ ≤ ∑ _k ∈ I, (2 * C₀ * Real.log ((q : ℝ) * (T + 2))) := Finset.sum_le_sum hterm
    _ = (I.card : ℝ) * (2 * C₀ * Real.log ((q : ℝ) * (T + 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (6 * T) * (2 * C₀ * Real.log ((q : ℝ) * (T + 2))) :=
        mul_le_mul_of_nonneg_right hI_card (by positivity)
    _ = 12 * C₀ * T * Real.log ((q : ℝ) * (T + 2)) := by ring

/-- **UNCONDITIONAL ZERO-COUNT BOUND `N(T, χ) ≤ C * T * log(q * (T + 2))`** (`T ≥ 2`, `0` assumptions)
directly on EVERY primitive Mathlib `DirichletCharacter.LFunction` (`χ ≠ 1`). -/
theorem LFunction_zero_count_height_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
          (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0 ∧ |ρ.im| ≤ T) →
          (Z.card : ℝ) ≤ C * T * Real.log ((q : ℝ) * (T + 2)) := by
  obtain ⟨C, hC, h⟩ := LFunction_zero_count_height_ge_one_le
  exact ⟨C, hC, fun q _ χ hprim hχ T hT Z hZ => h q χ hprim hχ T (by linarith) Z hZ⟩

/-- **DIRECT UNCONDITIONAL DISCHARGE OF `Stage3ZeroFreeRegion.ZeroCountBound` FOR EVERY PRIMITIVE
MATHLIB `DirichletCharacter.LFunction`** (`0` assumptions!):
there exists a single universal constant `C_N > 0` such that for EVERY `q`, EVERY primitive
`χ ≠ 1` mod `q`, and EVERY finite set `Z` of critical-strip zeros of `LFunction χ`,
`Stage3ZeroFreeRegion.ZeroCountBound C_N Z q` holds. -/
theorem zeroCountBound_LFunction_unconditional :
    ∃ C_N : ℝ, 0 < C_N ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ Z : Finset ℂ,
          (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0) →
          Stage3ZeroFreeRegion.ZeroCountBound C_N Z q := by
  obtain ⟨C_N, hCN_pos, hcount⟩ := LFunction_zero_count_height_ge_one_le
  refine ⟨C_N, hCN_pos, fun q _ χ hprim hχ Z hZ => ⟨hCN_pos.le, fun t ht => ?_⟩⟩
  refine hcount q χ hprim hχ t ht (Z.filter fun ρ => |ρ.im| ≤ t) fun ρ hρ => ?_
  rcases Finset.mem_filter.mp hρ with ⟨hρZ, hρt⟩
  obtain ⟨h0, h1, hz⟩ := hZ ρ hρZ
  exact ⟨h0, h1, hz, hρt⟩

/-- **Extension to ALL Non-Principal Dirichlet Characters (Primitive OR Imprimitive)**:
unconditional `Stage3ZeroFreeRegion.ZeroCountBound C_N Z q` for EVERY `χ ≠ 1` mod `q` via
`ElementaryEquiv.LFunction_eq_zero_iff_primitive_of_re_pos` and `χ.conductor ≤ q`. -/
theorem zeroCountBound_LFunction_nonprincipal_unconditional :
    ∃ C_N : ℝ, 0 < C_N ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ ≠ 1 → ∀ Z : Finset ℂ,
          (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0) →
          Stage3ZeroFreeRegion.ZeroCountBound C_N Z q := by
  obtain ⟨C_N, hCN_pos, hprim_bound⟩ := zeroCountBound_LFunction_unconditional
  refine ⟨C_N, hCN_pos, fun q _ χ hχ Z hZ => ⟨hCN_pos.le, fun t ht => ?_⟩⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ_ne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, map_one]
  have hZ_prim : ∀ ρ ∈ Z,
      0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    intro ρ hρ
    obtain ⟨h0, h1, hz⟩ := hZ ρ hρ
    exact ⟨h0, h1, (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ)).mp hz⟩
  have hbd := (hprim_bound χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
    hψ_ne1 Z hZ_prim).2 t ht
  have hd_le : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hd_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (NeZero.pos χ.conductor)
  have hlog_le : Real.log ((χ.conductor : ℝ) * (t + 2)) ≤ Real.log ((q : ℝ) * (t + 2)) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hd_le (by linarith))
  exact hbd.trans (mul_le_mul_of_nonneg_left hlog_le (by positivity))

end RHDirect.Stage6LFunctionOrder

end
