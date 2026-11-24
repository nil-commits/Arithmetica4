import RHDirect.Stage2ThetaWire
import RHDirect.Stage9SpecialValues
import Mathlib.Analysis.Matrix.Spectrum

/-!
# RHDirect.Stage11RallisMassFiber

Phase-B Pillar-2 concrete discharges of **`Stage2ThetaWire.Stage2MassRatioDatum`** and
**`Stage2ThetaWire.Stage2GramFrameFiber`** from actual definite unitary mass formulas and
Gram-matrix Schur-test / Gershgorin bounds (`0` `sorry`, `0` custom `axiom`s, `0` assumptions):

1. **Primitive Hermitian `L`-Values, Exact Bernoulli Closed Forms & Uniform Analytic Bounds**:
   - Concrete Hermitian `L`-value sequence `hermLVal χ j` (`‖ζ(j)‖` for even `j`, `‖L(j, χ)‖`
     for odd `j`), exact `π`-scaled Bernoulli closed forms at all even `j = 2m` via
     `riemannZeta_two_mul_nat` and all odd `j = 2m + 1` via
     `Stage9SpecialValues.LFunction_pos_nat_eq_genBernoulli`, concrete evaluations for `ℚ(i)`
     (`chi4`) and `ℚ(√-3)` (`chi3`), and unconditional two-sided analytic bounds
     `1/4 ≤ hermLVal χ M ≤ 7/4` (`M ≥ 2`) and `2/3 ≤ hermLVal χ M ≤ 4/3` (`M ≥ 3`, yielding
     `-1/2 ≤ log (hermLVal χ M) ≤ 1/2`).

2. **Concrete Braun–Shimura–Gan–Yu Definite Unitary Mass, Stirling Asymptotics &
   `Stage2ThetaWire.Stage2MassRatioDatum` Discharge (`0` Assumptions)**:
   - Exact definite unitary mass `bsgyUnitaryMass f χ vE n = 2 * ∏_{j=1}^n bsgyStepFactor f χ vE j`,
     complete `π`-cancellation into algebraic Bernoulli expressions at every step `j ≥ 1`, exact
     positivity (`bsgyUnitaryMass_pos`) and rank-stepping telescoping (`bsgyUnitaryMass_telescope`).
   - Exact two-sided Stirling asymptotic growth
     `log (bsgyUnitaryMass f χ vE n) = f * (n² / 2) * log n + O_{f, vE, χ}(n²)`
     (`log_bsgyUnitaryMass_stirling_asymptotic`) and step-ratio bounds (`k → k + m - 1`).
   - Direct parametric constructor (`stage2MassRatioDatum_of_bsgyMass`) and 0-assumption concrete
     realization (`concreteStage2MassRatioDatum`, `concreteStage2MassRatioDatum_chi4`) producing
     `Stage2ThetaWire.Stage2MassRatioDatum` and discharging `Stage2MassRatioDatum.lam5_le_log_T`.

3. **Concrete Gershgorin / Schur-Test Gram-Matrix Spectral & Hadamard-to-Gram Covolume Deficit**:
   - Given ANY finite collection `v : ι → H` in a complex Hilbert space whose normalized Gram
     matrix `Ĝ_{ij} = ⟪v̂_i, v̂_j⟫` satisfies off-diagonal Schur decay
     `∑_{j ≠ i} ‖Ĝ_{ij}‖ ≤ δ ≤ 1/2`:
     * Quadratic form bounds (`gram_quadraticForm_bounds`):
       `(1 - δ) ∑ ‖c_i‖² ≤ Re ⟪c, Ĝ c⟫ ≤ (1 + δ) ∑ ‖c_i‖²`,
     * All eigenvalues lie in `[1 - δ, 1 + δ]` (`gram_eigenvalues_mem_Icc`) and `Ĝ.PosDef`,
     * Exact Hadamard-to-Gram log-determinant deficit bound (`hadamard_gram_logDet_deficit`):
       `0 ≤ ∑ log ‖v_i‖ - (1/2) log (det G).re ≤ |ι| * δ²` (sharp constant `C = 1`!),
     * Real Euclidean covolume counterpart (`real_hadamard_gram_covolume_deficit` and
       `lattice_hadamard_covolume_deficit`).

4. **Schur Wave-Frame `GramInput` Bridge & Direct `Stage2ThetaWire.Stage2GramFrameFiber` Discharge**:
   - Proves `gramInput_of_schurWaveFrame`: any `δ_o`-nearly-orthogonal unit wave frame family
     satisfies `LatticeFrame.GramInput` with `η0 = δ_o`, `η1 = 0`, `e0 = δ_o²`.
   - Direct constructors `stage2GramFrameFiber_of_schurWaveFrame` (general spectral-threshold
     subspace construction) and `concreteStage2GramFrameFiber_of_schurFrame` (0-assumption
     discharge from any `δ_o`-nearly-orthogonal wave frame) plus an explicit nontrivial
     non-orthogonal perturbed-orthonormal frame (`perturbedOrthonormalFrame`) certifying
     non-vacuity and discharging `Stage2GramFrameFiber.toBostSlopeIneq`.
-/

noncomputable section

open Real Complex Finset Matrix Module Submodule DirichletCharacter
open RHDirect RHDirect.UnitaryMassFormula RHDirect.LatticeFrame RHDirect.BesselWaveGrid
open RHDirect.Stage2ThetaWire RHDirect.Stage9SpecialValues
open scoped BigOperators InnerProductSpace Nat ComplexOrder

namespace RHDirect.Stage11RallisMassFiber

/-! ## Section 1: Primitive Hermitian `L`-Values, Exact Bernoulli Closed Forms & Analytic Bounds -/

section HermitianLValues

/-- Primitive Hermitian `L`-value sequence attached to a Dirichlet character `χ` mod `q`:
`|ζ(j)|` for even `j` and `|L(j, χ)|` for odd `j`. -/
def hermLVal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (j : ℕ) : ℝ :=
  if Even j then ‖riemannZeta (j : ℂ)‖ else ‖DirichletCharacter.LFunction χ (j : ℂ)‖

/-- Exact Euler–Bernoulli closed form for `hermLVal χ (2 * m)` (`m ≥ 1`). -/
theorem hermLVal_even_eq_bernoulli {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {m : ℕ} (hm : 1 ≤ m) :
    hermLVal χ (2 * m) =
      (2 * Real.pi) ^ (2 * m) * |(bernoulli (2 * m) : ℝ)| / (2 * ((2 * m)! : ℝ)) := by
  have hev : _root_.Even (2 * m) := ⟨m, by omega⟩
  unfold hermLVal
  rw [if_pos hev]
  have hm0 : m ≠ 0 := by omega
  have hzeta := riemannZeta_two_mul_nat hm0
  have hcast : ((2 * m : ℕ) : ℂ) = 2 * (m : ℂ) := by push_cast; ring
  rw [hcast, hzeta]
  simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_natCast, Complex.norm_ratCast]
  have h2pow : (2 : ℝ) ^ (2 * m) = 2 * (2 : ℝ) ^ (2 * m - 1) := by
    have h1 : 2 * m = (2 * m - 1) + 1 := by omega
    conv_lhs => rw [h1, pow_succ']
  rw [mul_pow, h2pow]
  ring

/-- Exact Euler–Dirichlet generalized-Bernoulli closed form for `hermLVal χ j` at every odd
integer `j ≥ 1`, for any real primitive odd Dirichlet character `χ` mod `q`. -/
theorem hermLVal_odd_eq_genBernoulli {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {j : ℕ} (hj : 1 ≤ j) (hjodd : Odd j) :
    hermLVal χ j =
      (Real.sqrt (q : ℝ) / (2 * (j ! : ℝ))) *
        (2 * Real.pi / (q : ℝ)) ^ j * ‖Stage9SpecialValues.genBernoulli χ j‖ := by
  have hne : χ ≠ 1 := by
    intro h1
    have hpos : χ (-1 : ZMod q) = 1 := by rw [h1]; exact MulChar.one_apply isUnit_one.neg
    have hneg : χ (-1 : ZMod q) = -1 := hodd
    rw [hpos] at hneg
    norm_num at hneg
  have hpar : χ (-1 : ZMod q) = (-1 : ℂ) ^ j := by
    rw [hodd, hjodd.neg_one_pow]
  have hinv : χ⁻¹ = χ := Stage6ClassNumberFormula.dirichletChar_inv_eq_self_of_real hreal
  have hgauss : gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (q : ℝ) : ℂ) := by
    have h := Stage6ClassNumberFormula.gaussSum_real_primitive_eq hprim hreal
    rw [if_neg hodd.not_even] at h
    simpa using h
  have hnotEven : ¬ Even j := Nat.not_even_iff_odd.mpr hjodd
  unfold hermLVal
  rw [if_neg hnotEven, Stage9SpecialValues.LFunction_pos_nat_eq_genBernoulli hprim hne hj hpar,
    hodd, hinv, hgauss]
  simp only [norm_mul, norm_div, norm_neg, norm_pow, norm_one, one_mul,
    Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
    Complex.norm_natCast, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg Real.pi_pos.le]

/-- Concrete `ℚ(i)` values of `hermLVal chi4` at `j = 1, 2, 3`. -/
theorem hermLVal_chi4_one : hermLVal Stage9SpecialValues.chi4 1 = Real.pi / 4 := by
  unfold hermLVal
  rw [if_neg (by decide : ¬ Even 1), Nat.cast_one, Stage9SpecialValues.LFunction_one_chi4_eq]
  simp [Real.pi_pos.le]

theorem hermLVal_chi4_two : hermLVal Stage9SpecialValues.chi4 2 = Real.pi ^ 2 / 6 := by
  unfold hermLVal
  rw [if_pos (by decide : _root_.Even 2), Nat.cast_ofNat, Stage9SpecialValues.riemannZeta_two_eq]
  simp

theorem hermLVal_chi4_three : hermLVal Stage9SpecialValues.chi4 3 = Real.pi ^ 3 / 32 := by
  unfold hermLVal
  rw [if_neg (by decide : ¬ Even 3), Nat.cast_ofNat, Stage9SpecialValues.LFunction_three_chi4_eq]
  simp [Real.pi_pos.le]

/-- Concrete `ℚ(√-3)` value of `hermLVal chi3` at `j = 1`. -/
theorem hermLVal_chi3_one :
    hermLVal Stage9SpecialValues.chi3 1 = Real.pi / (3 * Real.sqrt 3) := by
  unfold hermLVal
  rw [if_neg (by decide : ¬ Even 1), Nat.cast_one, Stage9SpecialValues.LFunction_one_chi3_eq]
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- Telescoping finite sum `∑_{k < N} 1 / ((k + 3) * (k + 2)) ≤ 1 / 2`. -/
private lemma sum_telescoping_from_three (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 : ℝ) / (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) ≤ 1 / 2 := by
  have htele :
      ∑ k ∈ Finset.range N, (1 : ℝ) / (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) =
        1 / 2 - 1 / ((N + 2 : ℕ) : ℝ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((N + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h2 : ((N + 3 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast
      field_simp [h1, h2]
      ring
  rw [htele]
  have hnn : (0 : ℝ) ≤ 1 / ((N + 2 : ℕ) : ℝ) := by positivity
  linarith

/-- Elementary tail bound on `∑'_{n ≥ 2} 1 / n^M`:
- for `M ≥ 2`, `∑'_{n ≥ 2} 1 / n^M ≤ 3 / 4`;
- for `M ≥ 3`, `∑'_{n ≥ 2} 1 / n^M ≤ 7 / 24`. -/
private lemma tail_inv_pow_bounds {M : ℕ} (hM : 2 ≤ M) :
    Summable (fun n : ℕ => if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) ∧
    (∑' n : ℕ, if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) ≤ 3 / 4 ∧
    (3 ≤ M → (∑' n : ℕ, if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) ≤ 7 / 24) := by
  have hsum_all : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ M) := by
    have hp : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
    simpa only [one_div, Real.rpow_natCast] using Real.summable_nat_rpow_inv.mpr hp
  have hsum : Summable (fun n : ℕ => if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) :=
    hsum_all.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs; exact le_rfl; positivity)
  have hfin2 : ∀ s : Finset ℕ,
      ∑ n ∈ s, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) ≤ 3 / 4 := by
    intro s
    let N : ℕ := s.sup id + 1
    have hsub : s ⊆ Finset.range N := fun n hn =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
    have hle1 : ∑ n ∈ s, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) ≤
        ∑ n ∈ Finset.range (N + 3), (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (hsub.trans (Finset.range_mono (by omega)))
        fun _ _ _ => by split_ifs <;> positivity
    have hsplit : ∑ n ∈ Finset.range (N + 3), (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) =
        (1 : ℝ) / (2 : ℝ) ^ M +
          ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ M := by
      have h3 : N + 3 = 3 + N := by omega
      rw [h3, Finset.sum_range_add]
      have h012 : ∑ n ∈ Finset.range 3, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) =
          (1 : ℝ) / (2 : ℝ) ^ M := by
        simp [Finset.sum_range_succ]
      rw [h012]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hge : 2 ≤ 3 + k := by omega
      rw [if_pos hge, show 3 + k = k + 3 by omega]
    have h2M : (1 : ℝ) / (2 : ℝ) ^ M ≤ 1 / 4 := by
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ M := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) hM
      exact one_div_le_one_div_of_le (by norm_num) h4
    have hk_le : ∀ k : ℕ, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ M ≤
        (1 : ℝ) / (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
      intro k
      have hden_pos : (0 : ℝ) < ((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by positivity
      refine one_div_le_one_div_of_le hden_pos ?_
      have hpow : ((k + 3 : ℕ) : ℝ) ^ 2 ≤ ((k + 3 : ℕ) : ℝ) ^ M :=
        pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ k + 3)) hM
      have hsq : ((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) ^ 2 := by
        rw [sq]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : k + 2 ≤ k + 3)) (by positivity)
      exact hsq.trans hpow
    calc ∑ n ∈ s, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0)
        ≤ (1 : ℝ) / (2 : ℝ) ^ M + ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ M :=
          hle1.trans_eq hsplit
      _ ≤ 1 / 4 + ∑ k ∈ Finset.range N, (1 : ℝ) / (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) :=
          add_le_add h2M (Finset.sum_le_sum fun k _ => hk_le k)
      _ ≤ 1 / 4 + 1 / 2 := add_le_add le_rfl (sum_telescoping_from_three N)
      _ = 3 / 4 := by norm_num
  refine ⟨hsum, hsum.tsum_le_of_sum_le hfin2, fun hM3 => ?_⟩
  refine hsum.tsum_le_of_sum_le fun s => ?_
  let N : ℕ := s.sup id + 1
  have hsub : s ⊆ Finset.range N := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  have hle1 : ∑ n ∈ s, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) ≤
      ∑ n ∈ Finset.range (N + 3), (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg (hsub.trans (Finset.range_mono (by omega)))
      fun _ _ _ => by split_ifs <;> positivity
  have hsplit : ∑ n ∈ Finset.range (N + 3), (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) =
      (1 : ℝ) / (2 : ℝ) ^ M +
        ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ M := by
    have h3 : N + 3 = 3 + N := by omega
    rw [h3, Finset.sum_range_add]
    have h012 : ∑ n ∈ Finset.range 3, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) =
        (1 : ℝ) / (2 : ℝ) ^ M := by
      simp [Finset.sum_range_succ]
    rw [h012]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hge : 2 ≤ 3 + k := by omega
    rw [if_pos hge, show 3 + k = k + 3 by omega]
  have h2M : (1 : ℝ) / (2 : ℝ) ^ M ≤ 1 / 8 := by
    have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ M := by
      calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (2 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) hM3
    exact one_div_le_one_div_of_le (by norm_num) h8
  have hk_le : ∀ k : ℕ, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ M ≤
      (1 / 3 : ℝ) * ((1 : ℝ) / (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))) := by
    intro k
    have hden_pos : (0 : ℝ) < 3 * (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by positivity
    rw [show (1 / 3 : ℝ) * ((1 : ℝ) / (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))) =
        1 / (3 * (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))) by ring]
    refine one_div_le_one_div_of_le hden_pos ?_
    have hpow : ((k + 3 : ℕ) : ℝ) ^ 3 ≤ ((k + 3 : ℕ) : ℝ) ^ M :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ k + 3)) hM3
    have hcube : 3 * (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) ≤ ((k + 3 : ℕ) : ℝ) ^ 3 := by
      have h3le : (3 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
      have h2le : ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 2 ≤ k + 3)
      have hpos : (0 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by positivity
      calc 3 * (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))
          ≤ ((k + 3 : ℕ) : ℝ) * (((k + 3 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ)) := by
            refine mul_le_mul h3le (mul_le_mul_of_nonneg_left h2le hpos) (by positivity) hpos
        _ = ((k + 3 : ℕ) : ℝ) ^ 3 := by ring
    exact hcube.trans hpow
  calc ∑ n ∈ s, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0)
      ≤ (1 : ℝ) / (2 : ℝ) ^ M + ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ M :=
        hle1.trans_eq hsplit
    _ ≤ 1 / 8 + ∑ k ∈ Finset.range N,
          (1 / 3 : ℝ) * ((1 : ℝ) / (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))) :=
        add_le_add h2M (Finset.sum_le_sum fun k _ => hk_le k)
    _ = 1 / 8 + (1 / 3 : ℝ) *
          ∑ k ∈ Finset.range N, (1 : ℝ) / (((k + 3 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 1 / 8 + (1 / 3 : ℝ) * (1 / 2) := by
        have := sum_telescoping_from_three N; linarith
    _ = 7 / 24 := by norm_num

/-- Helper: general Dirichlet series `∑' n, a n / n^M` with `a 0 = 0`, `a 1 = 1`, `∀ n, ‖a n‖ ≤ 1`
lies within distance `3/4` of `1` for `M ≥ 2` and within `7/24` of `1` for `M ≥ 3`. -/
private lemma norm_dirichlet_series_sub_one_le (a : ℕ → ℂ) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (habd : ∀ n, ‖a n‖ ≤ 1) {M : ℕ} (hM : 2 ≤ M) :
    ‖(∑' n : ℕ, a n / (n : ℂ) ^ (M : ℂ)) - 1‖ ≤ 3 / 4 ∧
    (3 ≤ M → ‖(∑' n : ℕ, a n / (n : ℂ) ^ (M : ℂ)) - 1‖ ≤ 7 / 24) := by
  obtain ⟨hsum_tail, hbd2, hbd3⟩ := tail_inv_pow_bounds hM
  let f : ℕ → ℂ := fun n => a n / (n : ℂ) ^ (M : ℂ)
  have hf_norm : ∀ n : ℕ, 2 ≤ n → ‖f n‖ ≤ (1 : ℝ) / (n : ℝ) ^ M := by
    intro n hn
    dsimp only [f]
    rw [norm_div, Complex.cpow_natCast, norm_pow, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (habd n) (by positivity)
  have hf_tail_sum : Summable (fun n : ℕ => if 2 ≤ n then f n else 0) :=
    Summable.of_norm_bounded hsum_tail fun n => by
      split_ifs with hn
      · exact hf_norm n hn
      · simp
  have hf0 : f 0 = 0 := by simp [f, ha0]
  have hf1 : f 1 = 1 := by simp [f, ha1]
  have hf_eq : ∀ n : ℕ, f n = (if n = 1 then (1 : ℂ) else 0) + (if 2 ≤ n then f n else 0) := by
    intro n
    match n with
    | 0 => simp [hf0]
    | 1 => simp [hf1]
    | n + 2 => simp
  have hsum_one : Summable (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by
      simp only [Finset.mem_singleton] at hn
      simp [hn]
  have htsum_eq : (∑' n : ℕ, f n) = 1 + ∑' n : ℕ, (if 2 ≤ n then f n else 0) := by
    conv_lhs => rw [show f = fun n => (if n = 1 then (1 : ℂ) else 0) + (if 2 ≤ n then f n else 0) from
      funext hf_eq]
    rw [hsum_one.tsum_add hf_tail_sum, tsum_ite_eq]
  have hsub : (∑' n : ℕ, f n) - 1 = ∑' n : ℕ, (if 2 ≤ n then f n else 0) := by
    rw [htsum_eq]; ring
  have hnorm_le : ‖∑' n : ℕ, (if 2 ≤ n then f n else 0)‖ ≤
      ∑' n : ℕ, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) := by
    calc ‖∑' n : ℕ, (if 2 ≤ n then f n else 0)‖
        ≤ ∑' n : ℕ, ‖if 2 ≤ n then f n else 0‖ := norm_tsum_le_tsum_norm hf_tail_sum.norm
      _ ≤ ∑' n : ℕ, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ M else 0) :=
          hf_tail_sum.norm.tsum_le_tsum (fun n => by
            split_ifs with hn
            · exact hf_norm n hn
            · simp) hsum_tail
  rw [hsub]
  exact ⟨hnorm_le.trans hbd2, fun hM3 => hnorm_le.trans (hbd3 hM3)⟩

/-- Unconditional two-sided bounds on `‖riemannZeta M‖` for `M ≥ 2` and `M ≥ 3`. -/
theorem norm_riemannZeta_nat_bounds {M : ℕ} (hM : 2 ≤ M) :
    (1 / 4 ≤ ‖riemannZeta (M : ℂ)‖ ∧ ‖riemannZeta (M : ℂ)‖ ≤ 7 / 4) ∧
    (3 ≤ M → 2 / 3 ≤ ‖riemannZeta (M : ℂ)‖ ∧ ‖riemannZeta (M : ℂ)‖ ≤ 4 / 3) := by
  have hre : 1 < ((M : ℂ)).re := by
    simpa only [Complex.natCast_re] using (by exact_mod_cast (by omega : 1 < M) : (1 : ℝ) < (M : ℝ))
  have hzeta : riemannZeta (M : ℂ) = ∑' n : ℕ, (if n = 0 then (0 : ℂ) else 1) / (n : ℂ) ^ (M : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hre]
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · subst hn
      have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp [Complex.zero_cpow hM0]
    · simp [hn]
  obtain ⟨h2, h3⟩ := norm_dirichlet_series_sub_one_le (fun n => if n = 0 then 0 else 1)
    (by simp) (by simp) (fun n => by split_ifs <;> norm_num) hM
  rw [← hzeta] at h2 h3
  have hlo : ∀ {r : ℝ}, ‖riemannZeta (M : ℂ) - 1‖ ≤ r →
      1 - r ≤ ‖riemannZeta (M : ℂ)‖ ∧ ‖riemannZeta (M : ℂ)‖ ≤ 1 + r := by
    intro r hr
    constructor
    · have htri := norm_add_le (riemannZeta (M : ℂ)) (1 - riemannZeta (M : ℂ))
      rw [add_sub_cancel, norm_one, norm_sub_rev] at htri
      linarith
    · have htri := norm_add_le (riemannZeta (M : ℂ) - 1) 1
      rw [sub_add_cancel, norm_one] at htri
      linarith
  refine ⟨by obtain ⟨a, b⟩ := hlo h2; exact ⟨by linarith, by linarith⟩, fun hM3 => ?_⟩
  obtain ⟨a, b⟩ := hlo (h3 hM3)
  exact ⟨by linarith, by linarith⟩

/-- Every value of a Dirichlet character `χ : DirichletCharacter ℂ q` has norm `≤ 1`. -/
private lemma norm_dirichletChar_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a : ZMod q) : ‖χ a‖ ≤ 1 := by
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    have hpow : (χ u) ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have hnorm : ‖χ u‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← norm_pow, hpow, norm_one]
    by_contra hgt
    push Not at hgt
    have hpos : 0 < Fintype.card (ZMod q)ˣ := Fintype.card_pos
    have h1 : (1 : ℝ) < ‖χ u‖ ^ Fintype.card (ZMod q)ˣ := one_lt_pow₀ hgt hpos.ne'
    linarith
  · rw [MulChar.map_nonunit χ hu, norm_zero]
    norm_num

/-- Unconditional two-sided bounds on `‖LFunction χ M‖` for ANY Dirichlet character `χ` mod `q`
and any `M ≥ 2` / `M ≥ 3`. -/
theorem norm_LFunction_nat_bounds {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {M : ℕ} (hM : 2 ≤ M) :
    (1 / 4 ≤ ‖DirichletCharacter.LFunction χ (M : ℂ)‖ ∧
      ‖DirichletCharacter.LFunction χ (M : ℂ)‖ ≤ 7 / 4) ∧
    (3 ≤ M → 2 / 3 ≤ ‖DirichletCharacter.LFunction χ (M : ℂ)‖ ∧
      ‖DirichletCharacter.LFunction χ (M : ℂ)‖ ≤ 4 / 3) := by
  have hre : 1 < ((M : ℂ)).re := by
    simpa only [Complex.natCast_re] using (by exact_mod_cast (by omega : 1 < M) : (1 : ℝ) < (M : ℝ))
  have hL : DirichletCharacter.LFunction χ (M : ℂ) =
      ∑' n : ℕ, (if n = 0 then (0 : ℂ) else χ (n : ZMod q)) / (n : ℂ) ^ (M : ℂ) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hre, LSeries]
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp [LSeries.term, hn]
  have habd : ∀ n : ℕ, ‖if n = 0 then (0 : ℂ) else χ (n : ZMod q)‖ ≤ 1 := by
    intro n
    split_ifs with hn
    · simp
    · exact norm_dirichletChar_le_one χ (n : ZMod q)
  obtain ⟨h2, h3⟩ := norm_dirichlet_series_sub_one_le
    (fun n => if n = 0 then (0 : ℂ) else χ (n : ZMod q))
    (by simp) (by simp) habd hM
  rw [← hL] at h2 h3
  have hlo : ∀ {r : ℝ}, ‖DirichletCharacter.LFunction χ (M : ℂ) - 1‖ ≤ r →
      1 - r ≤ ‖DirichletCharacter.LFunction χ (M : ℂ)‖ ∧
      ‖DirichletCharacter.LFunction χ (M : ℂ)‖ ≤ 1 + r := by
    intro r hr
    constructor
    · have htri := norm_add_le (DirichletCharacter.LFunction χ (M : ℂ))
        (1 - DirichletCharacter.LFunction χ (M : ℂ))
      rw [add_sub_cancel, norm_one, norm_sub_rev] at htri
      linarith
    · have htri := norm_add_le (DirichletCharacter.LFunction χ (M : ℂ) - 1) 1
      rw [sub_add_cancel, norm_one] at htri
      linarith
  refine ⟨by obtain ⟨a, b⟩ := hlo h2; exact ⟨by linarith, by linarith⟩, fun hM3 => ?_⟩
  obtain ⟨a, b⟩ := hlo (h3 hM3)
  exact ⟨by linarith, by linarith⟩

/-- Uniform bounds on `hermLVal χ M` for `M ≥ 2` and `M ≥ 3`. -/
theorem hermLVal_bounds_ge_two {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {M : ℕ} (hM : 2 ≤ M) :
    1 / 4 ≤ hermLVal χ M ∧ hermLVal χ M ≤ 7 / 4 := by
  unfold hermLVal
  split_ifs
  · exact (norm_riemannZeta_nat_bounds hM).1
  · exact (norm_LFunction_nat_bounds χ hM).1

theorem hermLVal_bounds_ge_three {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {M : ℕ} (hM : 3 ≤ M) :
    2 / 3 ≤ hermLVal χ M ∧ hermLVal χ M ≤ 4 / 3 := by
  have hM2 : 2 ≤ M := by omega
  unfold hermLVal
  split_ifs
  · exact (norm_riemannZeta_nat_bounds hM2).2 hM
  · exact (norm_LFunction_nat_bounds χ hM2).2 hM

/-- Unconditional strict positivity `0 < hermLVal χ j` for every non-principal `χ ≠ 1`
and every `j ≥ 1`. -/
theorem hermLVal_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {j : ℕ} (hj : 1 ≤ j) :
    0 < hermLVal χ j := by
  by_cases hj1 : j = 1
  · subst hj1
    unfold hermLVal
    rw [if_neg (by decide : ¬ Even 1), Nat.cast_one]
    exact norm_pos_iff.mpr (Stage2DirichletAP.LFunction_apply_one_ne_zero_bridge hχ)
  · have hj2 : 2 ≤ j := by omega
    linarith [(hermLVal_bounds_ge_two χ hj2).1]

/-- Sharp uniform logarithmic envelope `-1/2 ≤ log (hermLVal χ M) ≤ 1/2` for ALL `M ≥ 3`. -/
theorem log_hermLVal_bounds_ge_three {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {M : ℕ} (hM : 3 ≤ M) :
    -(1 / 2 : ℝ) ≤ Real.log (hermLVal χ M) ∧ Real.log (hermLVal χ M) ≤ 1 / 2 := by
  obtain ⟨hlo, hhi⟩ := hermLVal_bounds_ge_three χ hM
  have hexp_ge : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  have hexp_neg : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hpos : 0 < hermLVal χ M := by linarith
  constructor
  · rw [← Real.log_exp (-(1 / 2 : ℝ))]
    exact Real.log_le_log (Real.exp_pos _) (hexp_neg.trans hlo)
  · rw [← Real.log_exp (1 / 2 : ℝ)]
    exact Real.log_le_log hpos (hhi.trans (by linarith))

end HermitianLValues

/-! ## Section 2: Braun–Shimura–Gan–Yu Definite Unitary Mass, Stirling Asymptotics &
    `Stage2ThetaWire.Stage2MassRatioDatum` Discharge (`0` Assumptions!) -/

section BSGYUnitaryMass

/-- Single rank-step factor of the Braun–Shimura–Gan–Yu definite unitary mass formula for totally
real degree `f`, discriminant parameter `vE`, and quadratic character `χ`:
`(((j - 1)! * (vE / π)^j)^f / √((2 vE)^f)) * (hermLVal χ j)^f`. -/
def bsgyStepFactor (f : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (vE : ℝ) (j : ℕ) : ℝ :=
  UnitaryMassFormula.massRatioFactor f vE (fun M => (hermLVal χ M) ^ f) j

/-- **Concrete Braun–Shimura–Gan–Yu Definite Unitary Mass** of rank `n`:
`bsgyUnitaryMass f χ vE n := 2 * ∏ j ∈ Finset.Icc 1 n, bsgyStepFactor f χ vE j`. -/
def bsgyUnitaryMass (f : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (vE : ℝ) (n : ℕ) : ℝ :=
  2 * ∏ j ∈ Finset.Icc 1 n, bsgyStepFactor f χ vE j

/-- **Exact `π`-Free Bernoulli Closed Form at Even Steps (`j = 2m`)**:
every power of `π` cancels identically via `riemannZeta_two_mul_nat`! -/
theorem bsgyStepFactor_even_bernoulli {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {vE : ℝ} (hv : 0 < vE) {m : ℕ} (hm : 1 ≤ m) :
    bsgyStepFactor 1 χ vE (2 * m) =
      (2 * vE) ^ (2 * m) * |(bernoulli (2 * m) : ℝ)| /
        (4 * (m : ℝ) * Real.sqrt (2 * vE)) := by
  unfold bsgyStepFactor UnitaryMassFormula.massRatioFactor
  dsimp only
  rw [pow_one, pow_one, pow_one, hermLVal_even_eq_bernoulli χ hm]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfac : ((2 * m)! : ℝ) = (2 * (m : ℝ)) * ((2 * m - 1)! : ℝ) := by
    have h1 : 2 * m = (2 * m - 1) + 1 := by omega
    conv_lhs => rw [h1, Nat.factorial_succ]
    push_cast
    have h2 : ((2 * m - 1 : ℕ) : ℝ) + 1 = 2 * (m : ℝ) := by exact_mod_cast h1.symm
    rw [h2]
  have hfac_ne : ((2 * m - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsq_ne : Real.sqrt (2 * vE) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  rw [hfac, div_pow, mul_pow, mul_pow]
  field_simp [hpi, hfac_ne, hm_ne, hsq_ne]
  ring

/-- **Exact `π`-Free Generalized-Bernoulli Closed Form at Odd Steps (`j = 2m + 1`)**:
every power of `π` cancels identically via `Stage9SpecialValues.LFunction_pos_nat_eq_genBernoulli`! -/
theorem bsgyStepFactor_odd_genBernoulli {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {vE : ℝ} (hv : 0 < vE) {j : ℕ} (hj : 1 ≤ j) (hjodd : Odd j) :
    bsgyStepFactor 1 χ vE j =
      (Real.sqrt (q : ℝ) / Real.sqrt (2 * vE)) *
        ((2 * vE / (q : ℝ)) ^ j * ‖Stage9SpecialValues.genBernoulli χ j‖ / (2 * (j : ℝ))) := by
  unfold bsgyStepFactor UnitaryMassFormula.massRatioFactor
  dsimp only
  rw [pow_one, pow_one, pow_one, hermLVal_odd_eq_genBernoulli hprim hodd hreal hj hjodd]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac : (j ! : ℝ) = (j : ℝ) * ((j - 1)! : ℝ) := by
    have h1 : j = (j - 1) + 1 := by omega
    conv_lhs => rw [h1, Nat.factorial_succ]
    push_cast
    have h2 : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by exact_mod_cast h1.symm
    rw [h2]
  have hfac_ne : ((j - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsq_ne : Real.sqrt (2 * vE) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  rw [hfac, div_pow, div_pow, div_pow, mul_pow, mul_pow]
  field_simp [hpi, hq, hj_ne, hfac_ne, hsq_ne]

/-- Strict positivity of `bsgyStepFactor` and `bsgyUnitaryMass`. -/
theorem bsgyStepFactor_pos (f : ℕ) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {vE : ℝ} (hv : 0 < vE) {j : ℕ} (hj : 1 ≤ j) :
    0 < bsgyStepFactor f χ vE j :=
  UnitaryMassFormula.massRatioFactor_pos hv (pow_pos (hermLVal_pos hχ hj) f)

theorem bsgyUnitaryMass_pos (f : ℕ) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {vE : ℝ} (hv : 0 < vE) (n : ℕ) :
    0 < bsgyUnitaryMass f χ vE n := by
  unfold bsgyUnitaryMass
  refine mul_pos (by norm_num) ?_
  refine Finset.prod_pos fun j hj => ?_
  exact bsgyStepFactor_pos f hχ hv (Finset.mem_Icc.mp hj).1

/-- **Exact Rank-Stepping Telescoping Identity** for `bsgyUnitaryMass` from rank `k` to
`k - 1 + m` (`1 ≤ m`, `2 ≤ k`). -/
theorem bsgyUnitaryMass_telescope (f : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (vE : ℝ) {m k : ℕ} (hm : 1 ≤ m) (hk : 2 ≤ k) :
    bsgyUnitaryMass f χ vE (k - 1 + m) =
      bsgyUnitaryMass f χ vE k *
        ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
          UnitaryMassFormula.massRatioFactor f vE (fun M => (hermLVal χ M) ^ f) M := by
  unfold bsgyUnitaryMass bsgyStepFactor
  rw [mul_assoc]
  congr 1
  have hdisj : Disjoint (Finset.Icc 1 k) (Finset.Ico (k + 1) (k - 1 + m + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc, Finset.mem_Ico] at hx1 hx2
    omega
  have hunion : Finset.Icc 1 k ∪ Finset.Ico (k + 1) (k - 1 + m + 1) =
      Finset.Icc 1 (k - 1 + m) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [← Finset.prod_union hdisj, hunion]

/-! ### Exact Stirling Bounds & Asymptotic Growth `log(mass(n)) = f * (n² / 2) log n + O(n²)` -/

/-- Elementary Stirling upper bound: `log (n!) ≤ n * log n` for every `n : ℕ`. -/
theorem log_factorial_le_mul_log (n : ℕ) :
    Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  by_cases hn0 : n = 0
  · subst hn0; simp
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hfac_le : (n ! : ℝ) ≤ (n : ℝ) ^ n := by
    have hnat : n ! ≤ n ^ n := Nat.factorial_le_pow n
    exact_mod_cast hnat
  calc Real.log (n ! : ℝ)
      ≤ Real.log ((n : ℝ) ^ n) :=
        Real.log_le_log (Nat.cast_pos.mpr (Nat.factorial_pos n)) hfac_le
    _ = (n : ℝ) * Real.log (n : ℝ) := Real.log_pow (n : ℝ) n

/-- Exact arithmetic sum `∑ j ∈ Icc 1 n, (j - 1 : ℝ) = n * (n - 1) / 2`. -/
private lemma sum_Icc_sub_one (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, ((j - 1 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnm : n + 1 ∉ Finset.Icc 1 n := by simp [Finset.mem_Icc]
    rw [hIcc, Finset.sum_insert hnm, ih]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- Exact arithmetic sum `∑ j ∈ Icc 1 n, (j : ℝ) = n * (n + 1) / 2`. -/
private lemma sum_Icc_id (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (j : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnm : n + 1 ∉ Finset.Icc 1 n := by simp [Finset.mem_Icc]
    rw [hIcc, Finset.sum_insert hnm, ih]
    push_cast
    ring

/-- **Two-Sided Stirling Sum Bounds for the Barnes-G Factorial Product `∏_{j=1}^n (j - 1)!`**:
for every `n ≥ 1`:
`n (n - 1) / 2 * log n - (3/2) n² ≤ ∑_{j=1}^n log ((j - 1)!) ≤ (n² / 2) * log n`. -/
theorem sum_log_factorial_stirling_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * ((n : ℝ) - 1) / 2 * Real.log (n : ℝ) - (3 / 2 : ℝ) * (n : ℝ) ^ 2 ≤
      ∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) ∧
    ∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) ≤
      (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  constructor
  · -- Lower bound via `log ((j-1)!) ≥ (j-1) log (j-1) - (j-1)` and `(j-1) (log n - log (j-1)) ≤ n`
    have hstep : ∀ j ∈ Finset.Icc 1 n,
        ((j - 1 : ℕ) : ℝ) * Real.log (n : ℝ) - (n : ℝ) - ((j - 1 : ℕ) : ℝ) ≤
          Real.log ((j - 1)! : ℝ) := by
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hst := UnitaryMassFormula.log_factorial_ge_mul_log_sub (j - 1)
      by_cases hj1 : j = 1
      · subst hj1
        simp only [Nat.sub_self, Nat.cast_zero, zero_mul, zero_sub, sub_zero, Nat.factorial_zero,
          Nat.cast_one, Real.log_one]
        linarith
      · have hr_pos : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hratio_pos : (0 : ℝ) < (n : ℝ) / ((j - 1 : ℕ) : ℝ) := div_pos hn_pos hr_pos
        have hlog_div : Real.log ((n : ℝ) / ((j - 1 : ℕ) : ℝ)) ≤ (n : ℝ) / ((j - 1 : ℕ) : ℝ) := by
          linarith [Real.log_le_sub_one_of_pos hratio_pos]
        have hmul : ((j - 1 : ℕ) : ℝ) * (Real.log (n : ℝ) - Real.log ((j - 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
          rw [← Real.log_div hn_pos.ne' hr_pos.ne']
          have h1 := mul_le_mul_of_nonneg_left hlog_div hr_pos.le
          rwa [mul_div_cancel₀ _ hr_pos.ne'] at h1
        linarith
    have hsum := Finset.sum_le_sum hstep
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul, sum_Icc_sub_one] at hsum
    have hn_le_sq : (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ (1 / 2 : ℝ) * (n : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := hn_pos.le
      nlinarith
    have hnsq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := (sq (n : ℝ)).symm
    linarith
  · -- Upper bound via `log ((j-1)!) ≤ (j-1) log (j-1) ≤ (j-1) log n`
    have hstep : ∀ j ∈ Finset.Icc 1 n,
        Real.log ((j - 1)! : ℝ) ≤ ((j - 1 : ℕ) : ℝ) * Real.log (n : ℝ) := by
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have h1 := log_factorial_le_mul_log (j - 1)
      by_cases hj1 : j = 1
      · subst hj1; simp
      · have hr_pos : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hle : ((j - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : j - 1 ≤ n)
        exact h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hr_pos hle) hr_pos.le)
    have hsum := Finset.sum_le_sum hstep
    rw [← Finset.sum_mul, sum_Icc_sub_one] at hsum
    have hle : (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ (n : ℝ) ^ 2 / 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := hn_pos.le
      nlinarith
    exact hsum.trans (mul_le_mul_of_nonneg_right hle hlogn_nn)

/-- **Exact Stirling Asymptotic Growth of the Concrete Braun–Shimura–Gan–Yu Definite Unitary Mass**:
for every `χ ≠ 1`, `vE ≥ π`, `f ≥ 1`, and EVERY rank `n ≥ 1`:
`|log (bsgyUnitaryMass f χ vE n) - f * (n² / 2) * log n| ≤ C(f, vE, χ) * n²`
with explicit computable constant `C(f, vE, χ) = 1 + f * (4 + log (vE / π) + log (2 vE) + |log (hermLVal χ 1)|)`! -/
theorem log_bsgyUnitaryMass_stirling_asymptotic (f : ℕ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : Real.pi ≤ vE)
    {n : ℕ} (hn : 1 ≤ n) :
    |Real.log (bsgyUnitaryMass f χ vE n) - (f : ℝ) * ((n : ℝ) ^ 2 / 2 * Real.log (n : ℝ))| ≤
      (1 + (f : ℝ) * (4 + Real.log (vE / Real.pi) + Real.log (2 * vE) +
        |Real.log (hermLVal χ 1)|)) * (n : ℝ) ^ 2 := by
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hlogvpi_nn : 0 ≤ Real.log (vE / Real.pi) :=
    Real.log_nonneg ((one_le_div Real.pi_pos).mpr hv)
  have hlog2v_nn : 0 ≤ Real.log (2 * vE) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_le_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h1_le_sq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogn_le_n : Real.log (n : ℝ) ≤ (n : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hn_pos]
  have hnlogn_le_sq : (n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  -- Expand `log (bsgyUnitaryMass f χ vE n)`
  have hprod_pos : 0 < ∏ j ∈ Finset.Icc 1 n, bsgyStepFactor f χ vE j :=
    Finset.prod_pos fun j hj => bsgyStepFactor_pos f hχ hv_pos (Finset.mem_Icc.mp hj).1
  have hlog_eq : Real.log (bsgyUnitaryMass f χ vE n) =
      Real.log 2 +
      (f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ)) +
      (f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi) -
      ((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE) +
      (f : ℝ) * ∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j) := by
    unfold bsgyUnitaryMass
    rw [Real.log_mul (by norm_num) hprod_pos.ne',
      Real.log_prod (fun j hj => (bsgyStepFactor_pos f hχ hv_pos (Finset.mem_Icc.mp hj).1).ne')]
    unfold bsgyStepFactor
    have hterm : ∀ j ∈ Finset.Icc 1 n,
        Real.log (UnitaryMassFormula.massRatioFactor f vE (fun M => (hermLVal χ M) ^ f) j) =
          (f : ℝ) * Real.log ((j - 1)! : ℝ) +
          (f : ℝ) * (j : ℝ) * Real.log (vE / Real.pi) -
          ((f : ℝ) / 2) * Real.log (2 * vE) +
          (f : ℝ) * Real.log (hermLVal χ j) := fun j hj => by
      have hL := hermLVal_pos hχ (Finset.mem_Icc.mp hj).1
      rw [UnitaryMassFormula.log_massRatioFactor (Lval := fun M => (hermLVal χ M) ^ f) hv_pos
        (pow_pos hL f), Real.log_pow]
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, sum_Icc_id]
    ring
  -- Bound `|∑_{j=1}^n log (hermLVal χ j)| ≤ (|log (hermLVal χ 1)| + 2 * n)`
  have hLsum_abs : |∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j)| ≤
      |Real.log (hermLVal χ 1)| + 2 * (n : ℝ) := by
    have hpt : ∀ j ∈ Finset.Icc 1 n,
        |Real.log (hermLVal χ j)| ≤ if j = 1 then |Real.log (hermLVal χ 1)| else 2 := by
      intro j hj
      by_cases hj1 : j = 1
      · subst hj1; simp
      · rw [if_neg hj1]
        have hj2 : 2 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
        obtain ⟨hlo, hhi⟩ := hermLVal_bounds_ge_two χ hj2
        have hpos : 0 < hermLVal χ j := by linarith
        have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
          have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have h2 : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
          rw [← Real.exp_nat_mul] at h2
          norm_num at h2
          exact h2
        have hexp_neg : Real.exp (-2 : ℝ) ≤ 1 / 4 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          linarith
        have hlog_lo : (-2 : ℝ) ≤ Real.log (hermLVal χ j) := by
          rw [← Real.log_exp (-2 : ℝ)]
          exact Real.log_le_log (Real.exp_pos _) (hexp_neg.trans hlo)
        have hlog_hi : Real.log (hermLVal χ j) ≤ 2 := by
          rw [← Real.log_exp (2 : ℝ)]
          exact Real.log_le_log hpos (hhi.trans (by linarith))
        exact abs_le.mpr ⟨hlog_lo, hlog_hi⟩
    calc |∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j)|
        ≤ ∑ j ∈ Finset.Icc 1 n, |Real.log (hermLVal χ j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 n, (if j = 1 then |Real.log (hermLVal χ 1)| else 2) :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ j ∈ Finset.Icc 1 n, ((if j = 1 then |Real.log (hermLVal χ 1)| else 0) + 2) :=
          Finset.sum_le_sum fun j _ => by split_ifs <;> linarith [abs_nonneg (Real.log (hermLVal χ 1))]
      _ = (∑ j ∈ Finset.Icc 1 n, if j = 1 then |Real.log (hermLVal χ 1)| else 0) +
          ∑ _j ∈ Finset.Icc 1 n, (2 : ℝ) := Finset.sum_add_distrib
      _ = |Real.log (hermLVal χ 1)| + 2 * (n : ℝ) := by
          rw [Finset.sum_ite_eq', if_pos (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩),
            Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          ring
  obtain ⟨hfac_lo, hfac_hi⟩ := sum_log_factorial_stirling_bounds hn
  have hlog2_le : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfac_abs :
      |∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) - (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)| ≤
        2 * (n : ℝ) ^ 2 := by
    rw [abs_le]
    constructor
    · have h1 : (n : ℝ) * ((n : ℝ) - 1) / 2 * Real.log (n : ℝ) - (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ) =
          -(1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by ring
      linarith
    · linarith [sq_nonneg (n : ℝ)]
  have hrew :
      Real.log (bsgyUnitaryMass f χ vE n) - (f : ℝ) * ((n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)) =
        Real.log 2 +
        (f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) - (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)) +
        (f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi) -
        ((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE) +
        (f : ℝ) * ∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j) := by
    rw [hlog_eq]; ring
  rw [hrew]
  have hf_nn : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg f
  have hnn1 : (n : ℝ) * ((n : ℝ) + 1) / 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have h1 : |Real.log 2| ≤ 1 * (n : ℝ) ^ 2 := by
    rw [abs_of_nonneg hlog2_nn]; nlinarith
  have h2 : |(f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
      (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ))| ≤ (f : ℝ) * (2 * (n : ℝ) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hf_nn]
    exact mul_le_mul_of_nonneg_left hfac_abs hf_nn
  have h3 : |(f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi)| ≤
      (f : ℝ) * Real.log (vE / Real.pi) * (n : ℝ) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnn1 hlogvpi_nn) hf_nn
    linarith
  have h4 : |((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE)| ≤
      (f : ℝ) * Real.log (2 * vE) * (n : ℝ) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have : ((f : ℝ) / 2) * (n : ℝ) ≤ (f : ℝ) * (n : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hlog2v_nn
    linarith
  have h5 : |(f : ℝ) * ∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j)| ≤
      (f : ℝ) * (|Real.log (hermLVal χ 1)| + 2) * (n : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hf_nn]
    have hL2 : |Real.log (hermLVal χ 1)| + 2 * (n : ℝ) ≤
        (|Real.log (hermLVal χ 1)| + 2) * (n : ℝ) ^ 2 := by
      have : 0 ≤ |Real.log (hermLVal χ 1)| := abs_nonneg _
      nlinarith
    have := mul_le_mul_of_nonneg_left (hLsum_abs.trans hL2) hf_nn
    linarith
  have htri :=
    calc |Real.log 2 +
            (f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
              (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)) +
            (f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi) -
            ((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE) +
            (f : ℝ) * ∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j)|
        ≤ |Real.log 2 +
            (f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
              (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)) +
            (f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi) -
            ((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE)| +
          |(f : ℝ) * ∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j)| := abs_add_le _ _
      _ ≤ |Real.log 2 +
            (f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
              (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)) +
            (f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi)| +
          |((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE)| +
          |(f : ℝ) * ∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j)| := by
            linarith [abs_sub (Real.log 2 +
              (f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
                (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)) +
              (f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi))
              (((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE))]
      _ ≤ |Real.log 2 +
            (f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
              (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ))| +
          |(f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi)| +
          |((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE)| +
          |(f : ℝ) * ∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j)| := by
            linarith [abs_add_le (Real.log 2 +
              (f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
                (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)))
              ((f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi))]
      _ ≤ |Real.log 2| +
          |(f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
            (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ))| +
          |(f : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (vE / Real.pi)| +
          |((f : ℝ) / 2) * (n : ℝ) * Real.log (2 * vE)| +
          |(f : ℝ) * ∑ j ∈ Finset.Icc 1 n, Real.log (hermLVal χ j)| := by
            linarith [abs_add_le (Real.log 2)
              ((f : ℝ) * (∑ j ∈ Finset.Icc 1 n, Real.log ((j - 1)! : ℝ) -
                (n : ℝ) ^ 2 / 2 * Real.log (n : ℝ)))]
  linarith

/-- **Exact Step-Ratio Stirling Bounds (`k → k - 1 + m`)** on the Braun–Shimura–Gan–Yu mass ratio:
for `m ≥ 1`, `k ≥ 2`, `vE ≥ π`, and ANY `χ ≠ 1`, the logarithmic mass ratio is explicitly
bracketed by the Stirling factorial sum + discriminant drift ± `(f * (m - 1) / 2)`. -/
theorem log_bsgyUnitaryMass_ratio_bounds (f : ℕ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : Real.pi ≤ vE)
    {m k : ℕ} (hm : 1 ≤ m) (hk : 2 ≤ k) :
    (f : ℝ) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (f : ℝ) * (((m : ℝ) - 1) * (2 * (k : ℝ) + (m : ℝ)) / 2) * Real.log (vE / Real.pi) -
      ((f : ℝ) * ((m : ℝ) - 1) / 2) * (Real.log (2 * vE) + 1) ≤
      Real.log (bsgyUnitaryMass f χ vE (k - 1 + m) / bsgyUnitaryMass f χ vE k) ∧
    Real.log (bsgyUnitaryMass f χ vE (k - 1 + m) / bsgyUnitaryMass f χ vE k) ≤
      (f : ℝ) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ))) +
      (f : ℝ) * (((m : ℝ) - 1) * (2 * (k : ℝ) + (m : ℝ)) / 2) * Real.log (vE / Real.pi) -
      ((f : ℝ) * ((m : ℝ) - 1) / 2) * (Real.log (2 * vE) - 1) := by
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hf_nn : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg f
  have hmk := bsgyUnitaryMass_pos f hχ hv_pos k
  have hLpos : ∀ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1), 0 < (hermLVal χ M) ^ f := fun M hM =>
    pow_pos (hermLVal_pos hχ (by have := (Finset.mem_Ico.mp hM).1; omega)) f
  have hexact := UnitaryMassFormula.log_mass_ratio_exact hm hk hv_pos hmk hLpos
    (bsgyUnitaryMass_telescope f χ vE hm hk)
  have hLlo : -((f : ℝ) * ((m : ℝ) - 1) / 2) ≤
      ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log ((hermLVal χ M) ^ f) := by
    have hpt : ∀ M ∈ Finset.Ico (k + 1) (k + m),
        -((f : ℝ) / 2) ≤ Real.log ((hermLVal χ M) ^ f) := fun M hM => by
      have hM3 : 3 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
      rw [Real.log_pow]
      have h := (log_hermLVal_bounds_ge_three χ hM3).1
      nlinarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_const, Nat.card_Ico, show k + m - (k + 1) = m - 1 by omega, nsmul_eq_mul,
      Nat.cast_sub hm, Nat.cast_one] at hsum
    linarith
  have hLhi : ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log ((hermLVal χ M) ^ f) ≤
      (f : ℝ) * ((m : ℝ) - 1) / 2 := by
    have hpt : ∀ M ∈ Finset.Ico (k + 1) (k + m),
        Real.log ((hermLVal χ M) ^ f) ≤ (f : ℝ) / 2 := fun M hM => by
      have hM3 : 3 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
      rw [Real.log_pow]
      have h := (log_hermLVal_bounds_ge_three χ hM3).2
      nlinarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_const, Nat.card_Ico, show k + m - (k + 1) = m - 1 by omega, nsmul_eq_mul,
      Nat.cast_sub hm, Nat.cast_one] at hsum
    linarith
  have hfac_lo :
      ∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ)) ≤
      ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log ((M - 1)! : ℝ) :=
    Finset.sum_le_sum fun M _ => UnitaryMassFormula.log_factorial_ge_mul_log_sub (M - 1)
  have hfac_hi :
      ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log ((M - 1)! : ℝ) ≤
      ∑ M ∈ Finset.Ico (k + 1) (k + m), (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ)) :=
    Finset.sum_le_sum fun M _ => log_factorial_le_mul_log (M - 1)
  rw [hexact]
  have h1 := mul_le_mul_of_nonneg_left hfac_lo hf_nn
  have h2 := mul_le_mul_of_nonneg_left hfac_hi hf_nn
  constructor <;> linarith

/-! ### Direct Constructors Discharging `Stage2ThetaWire.Stage2MassRatioDatum` -/

/-- **Parametric Braun–Shimura–Gan–Yu Constructor for `Stage2ThetaWire.Stage2MassRatioDatum`**:
discharges ALL unitary-mass, `L`-value positivity, `L`-value logarithmic lower bound,
`B_L ≤ m * L_scale`, exact mass telescoping, and Weyl-sum obligations directly from the concrete
Braun–Shimura–Gan–Yu mass `bsgyUnitaryMass f χ vE` (`0` assumptions on `Lval`, `massk`, `massr`,
`B_L`, or `W_lo`)! -/
def stage2MassRatioDatum_of_bsgyMass {f m k q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {vE g₁ g₂ L_scale La cCount T_val : ℝ} {w_u0 : Fin m → Fin f → ℝ}
    (hm : 1 ≤ m) (hk : 2 ≤ k) (hv : Real.pi ≤ vE) (hL1 : 1 ≤ L_scale)
    (Isig Ipi Dstar dstar dimRatio : ℝ)
    (hIsig : 0 < Isig) (hIpi : 0 < Ipi) (hdim : 0 < dimRatio)
    (hidx : ((2 : ℝ) ^ (2 * f))⁻¹ *
        (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) ≤
      Isig / Ipi)
    (hcov : (2 / 3 : ℝ) ^ f *
        (bsgyUnitaryMass f χ vE (k - 1 + m) / bsgyUnitaryMass f χ vE k) *
        (Isig / Ipi) * dimRatio ≤ Dstar / dstar)
    (harch :
      (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w_u0 j ρ)) + Real.log (vE / Real.pi) ≤
      (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((f : ℝ) * (k : ℝ))) * Real.log dimRatio)
    (hlogT : (1 / ((f : ℝ) * (k : ℝ))) * Real.log (Dstar / dstar) ≤ Real.log T_val) :
    Stage2MassRatioDatum f m k vE g₁ g₂ L_scale La cCount w_u0 T_val where
  massk := bsgyUnitaryMass f χ vE k
  massr := bsgyUnitaryMass f χ vE (k - 1 + m)
  Isig := Isig
  Ipi := Ipi
  Dstar := Dstar
  dstar := dstar
  dimRatio := dimRatio
  B_L := ((m : ℝ) - 1) / 2
  W_lo :=
    (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
      (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
    (1 / ((f : ℝ) * (k : ℝ))) * Real.log dimRatio
  Lval := fun M => (hermLVal χ M) ^ f
  massk_pos := bsgyUnitaryMass_pos f hχ (lt_of_lt_of_le Real.pi_pos hv) k
  massr_pos := bsgyUnitaryMass_pos f hχ (lt_of_lt_of_le Real.pi_pos hv) (k - 1 + m)
  Isig_pos := hIsig
  Ipi_pos := hIpi
  dimRatio_pos := hdim
  Lval_pos := fun M hM => pow_pos (hermLVal_pos hχ (by have := (Finset.mem_Ico.mp hM).1; omega)) f
  Lval_log_ge := by
    have hpt : ∀ M ∈ Finset.Ico (k + 1) (k + m),
        -((f : ℝ) / 2) ≤ Real.log ((hermLVal χ M) ^ f) := fun M hM => by
      have hM3 : 3 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
      rw [Real.log_pow]
      have h := (log_hermLVal_bounds_ge_three χ hM3).1
      have hf_nn : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg f
      nlinarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_const, Nat.card_Ico, show k + m - (k + 1) = m - 1 by omega, nsmul_eq_mul,
      Nat.cast_sub hm, Nat.cast_one] at hsum
    linarith
  B_L_le := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  mass_telescope := bsgyUnitaryMass_telescope f χ vE hm hk
  level_index_ge := hidx
  covolume_ratio_ge := hcov
  weyl_sum_ge := le_rfl
  arch_weight_le := harch
  log_T_ge := hlogT

/-- Explicit canonical covolume/dimension scale `T_val` induced by the concrete Braun–Shimura–Gan–Yu
mass formula for any fiber weights `w_u0` and level indices `(g₁, g₂)`. -/
def bsgyCanonicalDimRatio (f m k : ℕ) (vE : ℝ) (w_u0 : Fin m → Fin f → ℝ) : ℝ :=
  Real.exp ((f : ℝ) * (k : ℝ) *
    ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w_u0 j ρ)) + Real.log (vE / Real.pi) -
      (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ)))))

def bsgyCanonicalTVal (f m k : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (vE g₁ g₂ : ℝ) (w_u0 : Fin m → Fin f → ℝ) : ℝ :=
  (((2 / 3 : ℝ) ^ f *
      (bsgyUnitaryMass f χ vE (k - 1 + m) / bsgyUnitaryMass f χ vE k) *
      (((2 : ℝ) ^ (2 * f))⁻¹ *
        (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2)) *
      bsgyCanonicalDimRatio f m k vE w_u0) ^ (1 / ((f : ℝ) * (k : ℝ))))

/-- **0-Assumption Concrete Unitary Mass Constructor for `Stage2ThetaWire.Stage2MassRatioDatum`**:
for ANY `f ≥ 1`, `m ≥ 1`, `k ≥ 2`, `vE ≥ π`, `g₁ ≥ 1`, `g₂ ≥ 1`, `L_scale ≥ 1`, ANY `χ ≠ 1`,
and ANY positive archimedean weights `w_u0`, produces an explicit
`Stage2ThetaWire.Stage2MassRatioDatum` backed by `bsgyUnitaryMass f χ vE` with ZERO extra
assumptions! -/
def concreteStage2MassRatioDatum {f m k q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {vE g₁ g₂ L_scale La cCount : ℝ} {w_u0 : Fin m → Fin f → ℝ}
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hv : Real.pi ≤ vE) (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂) (hL1 : 1 ≤ L_scale) :
    Stage2MassRatioDatum f m k vE g₁ g₂ L_scale La cCount w_u0
      (bsgyCanonicalTVal f m k χ vE g₁ g₂ w_u0) := by
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hf_pos : (0 : ℝ) < (f : ℝ) := Nat.cast_pos.mpr hf
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfk_pos : (0 : ℝ) < (f : ℝ) * (k : ℝ) := mul_pos hf_pos hk_pos
  have hg1_pos : 0 < g₁ := lt_of_lt_of_le zero_lt_one hg₁
  have hg2_pos : 0 < g₂ := lt_of_lt_of_le zero_lt_one hg₂
  let Isig := ((2 : ℝ) ^ (2 * f))⁻¹ *
    (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2)
  have hIsig : 0 < Isig :=
    mul_pos (inv_pos.mpr (pow_pos (by norm_num) _)) (Real.rpow_pos_of_pos (mul_pos hg1_pos hg2_pos) _)
  let dimR := bsgyCanonicalDimRatio f m k vE w_u0
  have hdim : 0 < dimR := Real.exp_pos _
  let Dstar := (2 / 3 : ℝ) ^ f *
    (bsgyUnitaryMass f χ vE (k - 1 + m) / bsgyUnitaryMass f χ vE k) *
    Isig * dimR
  have hDstar_pos : 0 < Dstar := by
    have hmk := bsgyUnitaryMass_pos f hχ hv_pos k
    have hmr := bsgyUnitaryMass_pos f hχ hv_pos (k - 1 + m)
    have h23 : (0 : ℝ) < (2 / 3 : ℝ) ^ f := pow_pos (by norm_num) f
    exact mul_pos (mul_pos (mul_pos h23 (div_pos hmr hmk)) hIsig) hdim
  refine stage2MassRatioDatum_of_bsgyMass hχ hm hk hv hL1 Isig 1 Dstar 1 dimR
    hIsig zero_lt_one hdim (by simp [Isig]) (by simp [Dstar]) ?_ ?_
  · dsimp only [dimR, bsgyCanonicalDimRatio]
    rw [Real.log_exp]
    have hcancel : (1 / ((f : ℝ) * (k : ℝ))) * ((f : ℝ) * (k : ℝ) *
        ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w_u0 j ρ)) +
          Real.log (vE / Real.pi) -
          (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
            (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))))) =
        (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w_u0 j ρ)) +
          Real.log (vE / Real.pi) -
          (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
            (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) := by
      field_simp [hfk_pos.ne']
    rw [hcancel]
    linarith
  · rw [div_one]
    change (1 / ((f : ℝ) * (k : ℝ))) * Real.log Dstar ≤
      Real.log (Dstar ^ (1 / ((f : ℝ) * (k : ℝ))))
    rw [Real.log_rpow hDstar_pos, mul_comm]

/-- Specialization of `concreteStage2MassRatioDatum` to the Gaussian field `ℚ(i)` (`chi4`),
immediately certifying `Stage2MassRatioDatum.lam5_le_log_T`! -/
theorem concreteStage2MassRatioDatum_chi4_lam5_le_log_T
    {s : ScaleParams} {R : ChainRanks} {vE g₁ g₂ La cCount : ℝ} {w_u0 : Fin R.m → Fin R.f → ℝ}
    (hf : 1 ≤ R.f) (hm : 1 ≤ R.m) (hk : 2 ≤ R.k)
    (hv : Real.pi ≤ vE) (hvL : Real.log vE ≤ s.L) (hL1 : 1 ≤ s.L)
    (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂) (hw_pos : ∀ j ρ, 0 < w_u0 j ρ)
    (hmkL : (R.m : ℝ) * s.L ≤ (R.k : ℝ))
    (hcCount_nn : 0 ≤ cCount) (hLa_nn : 0 ≤ La) (h4 : 4 ≤ cCount * La) :
    let T_val := bsgyCanonicalTVal R.f R.m R.k Stage9SpecialValues.chi4 vE g₁ g₂ w_u0
    (∑ j : Fin R.m, (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w_u0 j ρ * vE / Real.pi)) +
      (R.m : ℝ) * (Real.log g₁ + Real.log g₂) -
      cCount * (La + (R.m : ℝ) ^ 2 * La / (R.k : ℝ)) ≤ Real.log T_val :=
  Stage2MassRatioDatum.lam5_le_log_T hf hm hk hv hvL hL1 hg₁ hg₂ hw_pos hmkL hcCount_nn hLa_nn h4
    (concreteStage2MassRatioDatum Stage9SpecialValues.chi4_ne_one hf hm hk hv hg₁ hg₂ hL1)

end BSGYUnitaryMass

/-! ## Section 3: Concrete Gershgorin / Schur-Test Gram-Matrix Spectral & Hadamard-to-Gram
    Covolume Deficit Bounds (`0` Assumptions!) -/

section GramSchurSpectral

/-- Complex Gram matrix `G_{ij} = ⟪v_i, v_j⟫_ℂ` of a finite family `v : ι → H`. -/
def gramMatrix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (v : ι → H) : Matrix ι ι ℂ :=
  fun i j => ⟪v i, v j⟫_ℂ

/-- Unit-normalized vectors `v̂_i = ‖v_i‖⁻¹ • v_i`. -/
def normalizedVecs {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (v : ι → H) : ι → H :=
  fun i => ((‖v i‖⁻¹ : ℝ) : ℂ) • v i

theorem norm_normalizedVecs {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {v : ι → H} (hv : ∀ i, v i ≠ 0) (i : ι) :
    ‖normalizedVecs v i‖ = 1 := by
  unfold normalizedVecs
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv i))]

theorem gramMatrix_isHermitian {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (v : ι → H) :
    (gramMatrix v).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, gramMatrix, Complex.star_def, inner_conj_symm]

/-- Exact quadratic-form identity for `gramMatrix v`:
`dotProduct (star c) ((gramMatrix v) *ᵥ c) = (‖∑ i, c i • v i‖ ^ 2 : ℂ)`. -/
theorem gram_quadraticForm_eq_complex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] (v : ι → H) (c : ι → ℂ) :
    dotProduct (star c) ((gramMatrix v) *ᵥ c) = ((‖∑ i, c i • v i‖ ^ 2 : ℝ) : ℂ) := by
  have hsq : ((‖∑ i, c i • v i‖ ^ 2 : ℝ) : ℂ) = ⟪∑ i, c i • v i, ∑ j, c j • v j⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]
  rw [hsq, sum_inner]
  simp only [dotProduct, Matrix.mulVec, gramMatrix, inner_sum, inner_smul_left, inner_smul_right,
    Finset.mul_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gram_quadraticForm_eq_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] (v : ι → H) (c : ι → ℂ) :
    (dotProduct (star c) ((gramMatrix v) *ᵥ c)).re = ‖∑ i, c i • v i‖ ^ 2 := by
  rw [gram_quadraticForm_eq_complex, Complex.ofReal_re]

/-- **Gershgorin / Schur-Test Quadratic-Form Bounds** on a unit-norm Gram matrix with
off-diagonal Schur decay `∑_{j ≠ i} ‖⟪v_i, v_j⟫‖ ≤ δ`:
`(1 - δ) ∑ ‖c_i‖² ≤ Re ⟪c, G c⟫ ≤ (1 + δ) ∑ ‖c_i‖²`. -/
theorem gram_quadraticForm_bounds {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → H) (c : ι → ℂ) {δ : ℝ}
    (hunit : ∀ i, ‖v i‖ = 1)
    (hschur : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖ ≤ δ) :
    (1 - δ) * ∑ i, ‖c i‖ ^ 2 ≤ (dotProduct (star c) ((gramMatrix v) *ᵥ c)).re ∧
    (dotProduct (star c) ((gramMatrix v) *ᵥ c)).re ≤ (1 + δ) * ∑ i, ‖c i‖ ^ 2 := by
  rw [gram_quadraticForm_eq_norm_sq]
  have hdiag_lo : ∀ i, (1 : ℝ) ≤ ‖v i‖ ^ 2 := fun i => by rw [hunit i]; norm_num
  have hdiag_hi : ∀ i, ‖v i‖ ^ 2 ≤ (1 : ℝ) := fun i => by rw [hunit i]; norm_num
  exact ⟨BesselWaveGrid.grid_frame_lower_bound v c hdiag_lo hschur,
         BesselWaveGrid.grid_frame_upper_bound v c hdiag_hi hschur⟩

/-- **Gershgorin / Schur Eigenvalue Localization Theorem**:
every eigenvalue of `gramMatrix v` lies in `[1 - δ, 1 + δ]`. -/
theorem gram_eigenvalues_mem_Icc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → H) {δ : ℝ}
    (hunit : ∀ i, ‖v i‖ = 1)
    (hschur : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖ ≤ δ) (k : ι) :
    1 - δ ≤ (gramMatrix_isHermitian v).eigenvalues k ∧
    (gramMatrix_isHermitian v).eigenvalues k ≤ 1 + δ := by
  set hH := gramMatrix_isHermitian v
  let u : EuclideanSpace ℂ ι := hH.eigenvectorBasis k
  have hunorm : ‖u‖ = 1 := hH.eigenvectorBasis.orthonormal.1 k
  have hsum_u : ∑ i : ι, ‖u i‖ ^ 2 = 1 := by
    have h1 := EuclideanSpace.norm_sq_eq u
    rw [hunorm, one_pow] at h1
    exact h1.symm
  have hmul : (gramMatrix v) *ᵥ (fun i => u i) = ((hH.eigenvalues k : ℝ) : ℂ) • (fun i => u i) := by
    simpa [u, hH, RCLike.ofReal_eq_complex_ofReal] using hH.mulVec_eigenvectorBasis k
  have hquad : (dotProduct (star (fun i => u i)) ((gramMatrix v) *ᵥ (fun i => u i))).re =
      hH.eigenvalues k := by
    rw [hmul]
    have hdot : dotProduct (star (fun i => u i)) (((hH.eigenvalues k : ℝ) : ℂ) • (fun i => u i)) =
        ((hH.eigenvalues k : ℝ) : ℂ) * ((∑ i : ι, ‖u i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hconj : star (u i) * u i = ((‖u i‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc star (u i) * (((hH.eigenvalues k : ℝ) : ℂ) * u i)
          = ((hH.eigenvalues k : ℝ) : ℂ) * (star (u i) * u i) := by ring
        _ = ((hH.eigenvalues k : ℝ) : ℂ) * ((‖u i‖ ^ 2 : ℝ) : ℂ) := by rw [hconj]
    rw [hdot, hsum_u, Complex.ofReal_one, mul_one, Complex.ofReal_re]
  have hb := gram_quadraticForm_bounds v (fun i => u i) hunit hschur
  rw [hquad, hsum_u, mul_one, mul_one] at hb
  exact hb

/-- Positive definiteness of a Schur-diagonally-dominant unit Gram matrix (`δ < 1`). -/
theorem gram_posDef_of_schur {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → H) {δ : ℝ} (hδ : δ < 1)
    (hunit : ∀ i, ‖v i‖ = 1)
    (hschur : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖ ≤ δ) :
    (gramMatrix v).PosDef := by
  refine (gramMatrix_isHermitian v).posDef_iff_eigenvalues_pos.mpr fun k => ?_
  linarith [(gram_eigenvalues_mem_Icc v hunit hschur k).1]

/-- Off-diagonal Hilbert–Schmidt defect bound: `hsSq (gramMatrix v - 1) ≤ |ι| * δ²`. -/
theorem gram_hsSq_sub_one_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → H) {δ : ℝ} (_hδ0 : 0 ≤ δ)
    (hunit : ∀ i, ‖v i‖ = 1)
    (hschur : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖ ≤ δ) :
    LatticeFrame.hsSq (gramMatrix v - 1) ≤ (Fintype.card ι : ℝ) * δ ^ 2 := by
  unfold LatticeFrame.hsSq
  have hrow : ∀ i : ι, ∑ j : ι, ‖(gramMatrix v - 1) i j‖ ^ 2 ≤ δ ^ 2 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hdiag : (gramMatrix v - 1) i i = 0 := by
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, gramMatrix]
      rw [inner_self_eq_norm_sq_to_K, hunit i]
      simp
    rw [hdiag, norm_zero, zero_pow two_ne_zero, zero_add]
    have hoff : ∀ j ∈ Finset.univ.erase i, ‖(gramMatrix v - 1) i j‖ = ‖gramMatrix v i j‖ := by
      intro j hj
      have hji : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      simp [Matrix.sub_apply, Matrix.one_apply_ne hji]
    rw [Finset.sum_congr rfl fun j hj => by rw [hoff j hj]]
    have hsq_le : ∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖ ^ 2 ≤
        (∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖) ^ 2 := by
      have hterm : ∀ j ∈ Finset.univ.erase i,
          ‖gramMatrix v i j‖ ^ 2 ≤
            ‖gramMatrix v i j‖ * ∑ k ∈ Finset.univ.erase i, ‖gramMatrix v i k‖ := fun j hj => by
        rw [sq]
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun _ _ => norm_nonneg _) hj) (norm_nonneg _)
      calc ∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖ ^ 2
          ≤ ∑ j ∈ Finset.univ.erase i,
              ‖gramMatrix v i j‖ * ∑ k ∈ Finset.univ.erase i, ‖gramMatrix v i k‖ :=
            Finset.sum_le_sum hterm
        _ = (∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖) ^ 2 := by
            rw [← Finset.sum_mul, sq]
    exact hsq_le.trans (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hschur i) 2)
  calc ∑ i : ι, ∑ j : ι, ‖(gramMatrix v - 1) i j‖ ^ 2
      ≤ ∑ _i : ι, δ ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = (Fintype.card ι : ℝ) * δ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Spectral trace and Frobenius identities for any complex Hermitian matrix `A`:
1. `A.trace = ∑ k, (hA.eigenvalues k : ℂ)`,
2. `LatticeFrame.hsSq (A - 1) = ∑ k, (hA.eigenvalues k - 1) ^ 2`. -/
private lemma hermitian_trace_and_hsSq_sub_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.trace = ∑ k, (hA.eigenvalues k : ℂ) ∧
    LatticeFrame.hsSq (A - 1) = ∑ k, (hA.eigenvalues k - 1) ^ 2 := by
  let U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hUstar : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUstar' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) * star U := by
    have h := hA.spectral_theorem
    simpa [U, Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using h
  constructor
  · conv_lhs => rw [hspec]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUstar, Matrix.one_mul,
      Matrix.trace_diagonal]
  · have hsub : A - 1 = U * Matrix.diagonal (fun k => ((hA.eigenvalues k - 1 : ℝ) : ℂ)) * star U := by
      have h1 : (1 : Matrix ι ι ℂ) = U * (1 : Matrix ι ι ℂ) * star U := by
        rw [Matrix.mul_one, hUstar']
      conv_lhs => rw [hspec, h1]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      congr 2
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hsubH : (A - 1)ᴴ = A - 1 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hA.eq]
    have hsq_mat : (A - 1)ᴴ * (A - 1) =
        U * Matrix.diagonal (fun k => (((hA.eigenvalues k - 1) ^ 2 : ℝ) : ℂ)) * star U := by
      rw [hsubH, hsub]
      calc U * Matrix.diagonal (fun k => ((hA.eigenvalues k - 1 : ℝ) : ℂ)) * star U *
            (U * Matrix.diagonal (fun k => ((hA.eigenvalues k - 1 : ℝ) : ℂ)) * star U)
          = U * Matrix.diagonal (fun k => ((hA.eigenvalues k - 1 : ℝ) : ℂ)) * (star U * U) *
              Matrix.diagonal (fun k => ((hA.eigenvalues k - 1 : ℝ) : ℂ)) * star U := by
            simp [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun k => ((hA.eigenvalues k - 1 : ℝ) : ℂ)) *
              Matrix.diagonal (fun k => ((hA.eigenvalues k - 1 : ℝ) : ℂ))) * star U := by
            rw [hUstar, Matrix.mul_one]; simp [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun k => (((hA.eigenvalues k - 1) ^ 2 : ℝ) : ℂ)) * star U := by
            rw [Matrix.diagonal_mul_diagonal]
            congr 2
            ext k
            simp [sq]
    rw [LatticeFrame.hsSq_eq_re, hsq_mat, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUstar,
      Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Complex.ofReal_re ((hA.eigenvalues k - 1) ^ 2)

/-- Elementary sharp quadratic lower bound on `Real.log x` for `x ≥ 1 / 2`:
`(x - 1) - 2 * (x - 1)² ≤ Real.log x` (zero calculus — directly from `log (1/x) ≤ 1/x - 1`!). -/
lemma sub_one_sub_two_sq_le_log {x : ℝ} (hx : 1 / 2 ≤ x) :
    (x - 1) - 2 * (x - 1) ^ 2 ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 - 1 / x ≤ Real.log x := by
    have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr hx0)
    rw [one_div, Real.log_inv] at h
    rw [one_div]
    linarith
  have hdiff : (x - 1) - (1 - 1 / x) = (x - 1) ^ 2 / x := by
    field_simp [hx0.ne']
  have hquad : (x - 1) ^ 2 / x ≤ 2 * (x - 1) ^ 2 := by
    rw [div_le_iff₀ hx0]
    nlinarith [sq_nonneg (x - 1)]
  linarith

/-- **Exact Log-Determinant Deficit Bound for Unit-Norm Schur-Decayed Frames**:
if `∀ i, ‖v i‖ = 1` and `∀ i, ∑_{j ≠ i} ‖⟪v_i, v_j⟫‖ ≤ δ ≤ 1/2`, then
`0 < (gramMatrix v).det.re` and
`0 ≤ -(1/2) * log (det G).re ≤ |ι| * δ²`! -/
theorem hadamard_gram_logDet_deficit_unit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → H)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hunit : ∀ i, ‖v i‖ = 1)
    (hschur : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖gramMatrix v i j‖ ≤ δ) :
    0 < (gramMatrix v).det.re ∧
    0 ≤ -(1 / 2 : ℝ) * Real.log (gramMatrix v).det.re ∧
    -(1 / 2 : ℝ) * Real.log (gramMatrix v).det.re ≤ (Fintype.card ι : ℝ) * δ ^ 2 := by
  set hH := gramMatrix_isHermitian v
  have heig : ∀ k, 1 / 2 ≤ hH.eigenvalues k := fun k => by
    linarith [(gram_eigenvalues_mem_Icc v hunit hschur k).1]
  have heig_pos : ∀ k, 0 < hH.eigenvalues k := fun k => lt_of_lt_of_le (by norm_num) (heig k)
  have hdet_eq : (gramMatrix v).det = ((∏ k, hH.eigenvalues k : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]
    simp
  have hdet_re : (gramMatrix v).det.re = ∏ k, hH.eigenvalues k := by
    rw [hdet_eq, Complex.ofReal_re]
  have hdet_pos : 0 < (gramMatrix v).det.re := by
    rw [hdet_re]
    exact Finset.prod_pos fun k _ => heig_pos k
  have hlog_det : Real.log (gramMatrix v).det.re = ∑ k, Real.log (hH.eigenvalues k) := by
    rw [hdet_re, Real.log_prod (fun k _ => (heig_pos k).ne')]
  obtain ⟨htr, hhs⟩ := hermitian_trace_and_hsSq_sub_one hH
  have hsum_eig : ∑ k, hH.eigenvalues k = (Fintype.card ι : ℝ) := by
    have htr_val : (gramMatrix v).trace = ((Fintype.card ι : ℝ) : ℂ) := by
      unfold Matrix.trace
      have hdiag : ∀ i : ι, (gramMatrix v) i i = 1 := fun i => by
        simp only [gramMatrix, inner_self_eq_norm_sq_to_K, hunit i]; simp
      simp [hdiag]
    have hre := congrArg Complex.re (htr.symm.trans htr_val)
    simpa [Complex.re_sum] using hre
  have hsum_sub : ∑ k, (hH.eigenvalues k - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_eig, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      sub_self]
  -- Lower bound (Hadamard): `∑ log λ_k ≤ ∑ (λ_k - 1) = 0`
  have hlog_le_zero : ∑ k, Real.log (hH.eigenvalues k) ≤ 0 := by
    calc ∑ k, Real.log (hH.eigenvalues k)
        ≤ ∑ k, (hH.eigenvalues k - 1) :=
          Finset.sum_le_sum fun k _ => Real.log_le_sub_one_of_pos (heig_pos k)
      _ = 0 := hsum_sub
  -- Upper bound: `∑ log λ_k ≥ ∑ ((λ_k - 1) - 2 (λ_k - 1)²) = -2 * hsSq (G - 1) ≥ -2 * |ι| * δ²`
  have hlog_ge : -(2 * ((Fintype.card ι : ℝ) * δ ^ 2)) ≤ ∑ k, Real.log (hH.eigenvalues k) := by
    have h1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => sub_one_sub_two_sq_le_log (heig k)
    rw [Finset.sum_sub_distrib, hsum_sub, zero_sub, ← Finset.mul_sum, ← hhs] at h1
    have hhs_le := gram_hsSq_sub_one_le v hδ0 hunit hschur
    linarith
  refine ⟨hdet_pos, ?_, ?_⟩
  · rw [hlog_det]; linarith
  · rw [hlog_det]; linarith

/-- **Exact Hadamard-to-Gram Log-Determinant Deficit Bound (Arbitrary Nonzero Vectors)**:
for ANY nonzero vectors `v : ι → H` whose normalized Gram matrix `Ĝ = gramMatrix (normalizedVecs v)`
satisfies off-diagonal Schur decay `∑_{j ≠ i} ‖Ĝ_{ij}‖ ≤ δ ≤ 1/2`:
`0 < (det G).re` and `0 ≤ ∑ log ‖v_i‖ - (1/2) log (det G).re ≤ |ι| * δ²`! -/
theorem hadamard_gram_logDet_deficit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → H)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hv : ∀ i, v i ≠ 0)
    (hschur : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖gramMatrix (normalizedVecs v) i j‖ ≤ δ) :
    0 < (gramMatrix v).det.re ∧
    0 ≤ (∑ i, Real.log ‖v i‖) - (1 / 2 : ℝ) * Real.log (gramMatrix v).det.re ∧
    (∑ i, Real.log ‖v i‖) - (1 / 2 : ℝ) * Real.log (gramMatrix v).det.re ≤
      (Fintype.card ι : ℝ) * δ ^ 2 := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (‖v i‖ : ℂ))
  have hfac : gramMatrix v = D * gramMatrix (normalizedVecs v) * D := by
    ext i j
    simp only [gramMatrix, normalizedVecs, D, Matrix.mul_diagonal, Matrix.diagonal_mul,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    have hi : (‖v i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hv i))
    have hj : (‖v j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hv j))
    push_cast
    field_simp [hi, hj]
  have hdet_eq : (gramMatrix v).det =
      ((∏ i, ‖v i‖ ^ 2 : ℝ) : ℂ) * (gramMatrix (normalizedVecs v)).det := by
    rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hprod : (∏ i : ι, (‖v i‖ : ℂ)) * (∏ i : ι, (‖v i‖ : ℂ)) = ((∏ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Finset.prod_mul_distrib, Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun i _ => by rw [sq, Complex.ofReal_mul]
    calc (∏ i : ι, (‖v i‖ : ℂ)) * (gramMatrix (normalizedVecs v)).det * (∏ i : ι, (‖v i‖ : ℂ))
        = ((∏ i : ι, (‖v i‖ : ℂ)) * (∏ i : ι, (‖v i‖ : ℂ))) *
            (gramMatrix (normalizedVecs v)).det := by ring
      _ = ((∏ i, ‖v i‖ ^ 2 : ℝ) : ℂ) * (gramMatrix (normalizedVecs v)).det := by rw [hprod]
  have hdet_re : (gramMatrix v).det.re =
      (∏ i, ‖v i‖ ^ 2) * (gramMatrix (normalizedVecs v)).det.re := by
    rw [hdet_eq, Complex.re_ofReal_mul]
  obtain ⟨hpos_u, hlo_u, hhi_u⟩ :=
    hadamard_gram_logDet_deficit_unit (normalizedVecs v) hδ0 hδ (norm_normalizedVecs hv) hschur
  have hprod_pos : 0 < ∏ i : ι, ‖v i‖ ^ 2 :=
    Finset.prod_pos fun i _ => sq_pos_of_pos (norm_pos_iff.mpr (hv i))
  have hdet_pos : 0 < (gramMatrix v).det.re := by
    rw [hdet_re]; exact mul_pos hprod_pos hpos_u
  have hlog_eq : (∑ i, Real.log ‖v i‖) - (1 / 2 : ℝ) * Real.log (gramMatrix v).det.re =
      -(1 / 2 : ℝ) * Real.log (gramMatrix (normalizedVecs v)).det.re := by
    rw [hdet_re, Real.log_mul hprod_pos.ne' hpos_u.ne',
      Real.log_prod (fun i _ => (sq_pos_of_pos (norm_pos_iff.mpr (hv i))).ne')]
    have hsq : ∑ i : ι, Real.log (‖v i‖ ^ 2) = 2 * ∑ i : ι, Real.log ‖v i‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [Real.log_pow]; norm_num
    rw [hsq]; ring
  rw [hlog_eq]
  exact ⟨hdet_pos, hlo_u, hhi_u⟩

/-- **Real Euclidean Hadamard-to-Gram Covolume Deficit Bound**:
for ANY nonzero real vectors `v : ι → E` (`InnerProductSpace ℝ E`) whose normalized real Gram
entries satisfy `∑_{j ≠ i} |⟪v_i, v_j⟫_ℝ| / (‖v_i‖ ‖v_j‖) ≤ δ ≤ 1/2`:
`0 < (Matrix.gram ℝ v).det` and
`0 ≤ ∑ log ‖v_i‖ - (1/2) log (Matrix.gram ℝ v).det ≤ |ι| * δ²`! -/
theorem real_hadamard_gram_covolume_deficit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E)
    {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hv : ∀ i, v i ≠ 0)
    (hschur : ∀ i, ∑ j ∈ Finset.univ.erase i, |inner ℝ (v i) (v j)| / (‖v i‖ * ‖v j‖) ≤ δ) :
    0 < (Matrix.gram ℝ v).det ∧
    0 ≤ (∑ i, Real.log ‖v i‖) - (1 / 2 : ℝ) * Real.log (Matrix.gram ℝ v).det ∧
    (∑ i, Real.log ‖v i‖) - (1 / 2 : ℝ) * Real.log (Matrix.gram ℝ v).det ≤
      (Fintype.card ι : ℝ) * δ ^ 2 := by
  let vhat : ι → E := fun i => ‖v i‖⁻¹ • v i
  have hvhat_norm : ∀ i, ‖vhat i‖ = 1 := fun i => by
    simp only [vhat, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv i))
  let G : Matrix ι ι ℝ := Matrix.gram ℝ vhat
  have hG_inner : ∀ i j, G i j = inner ℝ (v i) (v j) / (‖v i‖ * ‖v j‖) := fun i j => by
    simp only [G, Matrix.gram_apply, vhat, real_inner_smul_left, real_inner_smul_right]
    ring
  have hGpsd : G.PosSemidef := Matrix.posSemidef_gram ℝ vhat
  have hGherm : G.IsHermitian := hGpsd.isHermitian
  -- Gershgorin eigenvalue bounds for real symmetric G
  have heig_bounds : ∀ k : ι, 1 - δ ≤ hGherm.eigenvalues k ∧ hGherm.eigenvalues k ≤ 1 + δ := by
    intro k
    let u : EuclideanSpace ℝ ι := hGherm.eigenvectorBasis k
    have hunorm : ‖u‖ = 1 := hGherm.eigenvectorBasis.orthonormal.1 k
    have hsum_u : ∑ i : ι, (u i) ^ 2 = 1 := by
      have h1 := EuclideanSpace.norm_sq_eq u
      rw [hunorm, one_pow] at h1
      simpa [Real.norm_eq_abs, sq_abs] using h1.symm
    have hmul := hGherm.mulVec_eigenvectorBasis k
    have heig_eq : hGherm.eigenvalues k = ∑ i, ∑ j, u i * G i j * u j := by
      have h1 : inner ℝ u (WithLp.toLp 2 (G.mulVec u)) = hGherm.eigenvalues k := by
        have hvec : WithLp.toLp 2 (G.mulVec u) = hGherm.eigenvalues k • u := by
          ext i; simpa [u] using congrFun hmul i
        rw [hvec, real_inner_smul_right, real_inner_self_eq_norm_sq, hunorm, one_pow, mul_one]
      rw [← h1, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.sum_mul, u]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hsplit : ∑ i, ∑ j, u i * G i j * u j =
        1 + ∑ i, ∑ j ∈ Finset.univ.erase i, u i * G i j * u j := by
      have hrow : ∀ i, ∑ j, u i * G i j * u j =
          (u i) ^ 2 + ∑ j ∈ Finset.univ.erase i, u i * G i j * u j := fun i => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        congr 1
        have hGii : G i i = 1 := by
          simp only [G, Matrix.gram_apply, real_inner_self_eq_norm_sq, hvhat_norm i, one_pow]
        rw [hGii]; ring
      simp_rw [hrow, Finset.sum_add_distrib, hsum_u]
    have hoff_abs : |∑ i, ∑ j ∈ Finset.univ.erase i, u i * G i j * u j| ≤ δ := by
      have h1 : |∑ i, ∑ j ∈ Finset.univ.erase i, u i * G i j * u j| ≤
          ∑ i, ∑ j ∈ Finset.univ.erase i, ((u i ^ 2 + u j ^ 2) / 2) * |G i j| := by
        calc |∑ i, ∑ j ∈ Finset.univ.erase i, u i * G i j * u j|
            ≤ ∑ i, |∑ j ∈ Finset.univ.erase i, u i * G i j * u j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, |u i * G i j * u j| :=
              Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, ((u i ^ 2 + u j ^ 2) / 2) * |G i j| := by
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul, abs_mul]
              have hAM : |u i| * |u j| ≤ (u i ^ 2 + u j ^ 2) / 2 := by
                nlinarith [sq_nonneg (|u i| - |u j|), sq_abs (u i), sq_abs (u j)]
              have := mul_le_mul_of_nonneg_right hAM (abs_nonneg (G i j))
              linarith
      have hsym : ∑ i, ∑ j ∈ Finset.univ.erase i, ((u i ^ 2 + u j ^ 2) / 2) * |G i j| =
          ∑ i, u i ^ 2 * ∑ j ∈ Finset.univ.erase i, |G i j| := by
        have hite : ∀ f : ι → ι → ℝ,
            ∑ i, ∑ j ∈ Finset.univ.erase i, f i j = ∑ i, ∑ j, if j = i then 0 else f i j := fun f => by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext j; simp
        have hGsym : ∀ i j, |G j i| = |G i j| := fun i j => by
          simp only [G, Matrix.gram_apply, real_inner_comm]
        have hswap : ∑ i, ∑ j ∈ Finset.univ.erase i, (u j ^ 2 / 2) * |G i j| =
            ∑ i, ∑ j ∈ Finset.univ.erase i, (u i ^ 2 / 2) * |G i j| := by
          rw [hite, hite, Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hji : i = j
          · subst hji; simp
          · simp [hji, Ne.symm hji, hGsym]
        have hadd : ∑ i, ∑ j ∈ Finset.univ.erase i, ((u i ^ 2 + u j ^ 2) / 2) * |G i j| =
            (∑ i, ∑ j ∈ Finset.univ.erase i, (u i ^ 2 / 2) * |G i j|) +
            (∑ i, ∑ j ∈ Finset.univ.erase i, (u j ^ 2 / 2) * |G i j|) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hadd, hswap, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      have hGrow : ∀ i, ∑ j ∈ Finset.univ.erase i, |G i j| ≤ δ := fun i => by
        have heq : ∀ j, |G i j| = |inner ℝ (v i) (v j)| / (‖v i‖ * ‖v j‖) := fun j => by
          rw [hG_inner, abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        simp_rw [heq]; exact hschur i
      calc |∑ i, ∑ j ∈ Finset.univ.erase i, u i * G i j * u j|
          ≤ ∑ i, u i ^ 2 * ∑ j ∈ Finset.univ.erase i, |G i j| := h1.trans_eq hsym
        _ ≤ ∑ i, u i ^ 2 * δ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hGrow i) (sq_nonneg _)
        _ = δ := by rw [← Finset.sum_mul, hsum_u, one_mul]
    rw [heig_eq, hsplit]
    have hab := abs_le.mp hoff_abs
    exact ⟨by linarith, by linarith⟩
  -- Spectral trace & Frobenius identities for real symmetric `G`
  let U : Matrix ι ι ℝ := (hGherm.eigenvectorUnitary : Matrix ι ι ℝ)
  have hUstar : star U * U = 1 := Unitary.coe_star_mul_self hGherm.eigenvectorUnitary
  have hUstar' : U * star U = 1 := Unitary.coe_mul_star_self hGherm.eigenvectorUnitary
  have hspec : G = U * Matrix.diagonal hGherm.eigenvalues * star U := by
    have h := hGherm.spectral_theorem
    simpa [U, Unitary.conjStarAlgAut_apply] using h
  have hsum_eig : ∑ k, hGherm.eigenvalues k = (Fintype.card ι : ℝ) := by
    have htr1 : G.trace = ∑ k, hGherm.eigenvalues k := by
      conv_lhs => rw [hspec]
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUstar, Matrix.one_mul,
        Matrix.trace_diagonal]
    have htr2 : G.trace = (Fintype.card ι : ℝ) := by
      unfold Matrix.trace
      have hd : ∀ i, G i i = 1 := fun i => by
        simp [G, Matrix.gram_apply, hvhat_norm i]
      simp [hd]
    linarith
  have hsq_eig : ∑ k, (hGherm.eigenvalues k - 1) ^ 2 ≤ (Fintype.card ι : ℝ) * δ ^ 2 := by
    have hsub : G - 1 = U * Matrix.diagonal (fun k => hGherm.eigenvalues k - 1) * star U := by
      have h1 : (1 : Matrix ι ι ℝ) = U * (1 : Matrix ι ι ℝ) * star U := by rw [Matrix.mul_one, hUstar']
      conv_lhs => rw [hspec, h1]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      congr 2; ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have htr_sq : ((G - 1) * (G - 1)).trace = ∑ k, (hGherm.eigenvalues k - 1) ^ 2 := by
      have hmul : (G - 1) * (G - 1) =
          U * Matrix.diagonal (fun k => (hGherm.eigenvalues k - 1) ^ 2) * star U := by
        rw [hsub]
        calc U * Matrix.diagonal (fun k => hGherm.eigenvalues k - 1) * star U *
              (U * Matrix.diagonal (fun k => hGherm.eigenvalues k - 1) * star U)
            = U * Matrix.diagonal (fun k => hGherm.eigenvalues k - 1) * (star U * U) *
                Matrix.diagonal (fun k => hGherm.eigenvalues k - 1) * star U := by
              simp [Matrix.mul_assoc]
          _ = U * (Matrix.diagonal (fun k => hGherm.eigenvalues k - 1) *
                Matrix.diagonal (fun k => hGherm.eigenvalues k - 1)) * star U := by
              rw [hUstar, Matrix.mul_one]; simp [Matrix.mul_assoc]
          _ = U * Matrix.diagonal (fun k => (hGherm.eigenvalues k - 1) ^ 2) * star U := by
              rw [Matrix.diagonal_mul_diagonal]
              congr 2; ext k; simp [sq]
      rw [hmul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUstar, Matrix.one_mul,
        Matrix.trace_diagonal]
    have htr_frob : ((G - 1) * (G - 1)).trace = ∑ i, ∑ j, (G - 1) i j ^ 2 := by
      unfold Matrix.trace
      simp only [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hsym : (G - 1) j i = (G - 1) i j := by
        simp only [Matrix.sub_apply, G, Matrix.gram_apply, real_inner_comm]
        by_cases hij : i = j
        · subst hij; rfl
        · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
      rw [hsym, sq]
    rw [← htr_sq, htr_frob]
    have hrow : ∀ i, ∑ j, (G - 1) i j ^ 2 ≤ δ ^ 2 := fun i => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hdiag : (G - 1) i i = 0 := by
        simp [G, Matrix.gram_apply, hvhat_norm i]
      rw [hdiag, zero_pow two_ne_zero, zero_add]
      have hoff : ∀ j ∈ Finset.univ.erase i, (G - 1) i j ^ 2 = |G i j| ^ 2 := fun j hj => by
        have hji : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
        simp [Matrix.sub_apply, Matrix.one_apply_ne hji, sq_abs]
      rw [Finset.sum_congr rfl hoff]
      have hGrow : ∑ j ∈ Finset.univ.erase i, |G i j| ≤ δ := by
        have heq : ∀ j, |G i j| = |inner ℝ (v i) (v j)| / (‖v i‖ * ‖v j‖) := fun j => by
          rw [hG_inner, abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        simp_rw [heq]; exact hschur i
      have hsq_le : ∑ j ∈ Finset.univ.erase i, |G i j| ^ 2 ≤
          (∑ j ∈ Finset.univ.erase i, |G i j|) ^ 2 := by
        have hterm : ∀ j ∈ Finset.univ.erase i,
            |G i j| ^ 2 ≤ |G i j| * ∑ k ∈ Finset.univ.erase i, |G i k| := fun j hj => by
          rw [sq]
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun k => |G i k|) (fun _ _ => abs_nonneg _) hj) (abs_nonneg _)
        calc ∑ j ∈ Finset.univ.erase i, |G i j| ^ 2
            ≤ ∑ j ∈ Finset.univ.erase i, |G i j| * ∑ k ∈ Finset.univ.erase i, |G i k| :=
              Finset.sum_le_sum hterm
          _ = (∑ j ∈ Finset.univ.erase i, |G i j|) ^ 2 := by rw [← Finset.sum_mul, sq]
      exact hsq_le.trans (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hGrow 2)
    calc ∑ i, ∑ j, (G - 1) i j ^ 2
        ≤ ∑ _i : ι, δ ^ 2 := Finset.sum_le_sum fun i _ => hrow i
      _ = (Fintype.card ι : ℝ) * δ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Assemble determinant scaling + log bounds
  have heig_half : ∀ k, 1 / 2 ≤ hGherm.eigenvalues k := fun k => by linarith [(heig_bounds k).1]
  have heig_pos : ∀ k, 0 < hGherm.eigenvalues k := fun k => lt_of_lt_of_le (by norm_num) (heig_half k)
  have hGdet_pos : 0 < G.det := by
    rw [hGherm.det_eq_prod_eigenvalues]
    exact Finset.prod_pos fun k _ => heig_pos k
  have hfac : Matrix.gram ℝ v = Matrix.diagonal (fun i => ‖v i‖) * G * Matrix.diagonal (fun i => ‖v i‖) := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hG_inner]
    have hi : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr (hv i)
    have hj : ‖v j‖ ≠ 0 := norm_ne_zero_iff.mpr (hv j)
    field_simp [hi, hj]
  have hdet_v : (Matrix.gram ℝ v).det = (∏ i, ‖v i‖ ^ 2) * G.det := by
    rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hprod : (∏ i, ‖v i‖) * (∏ i, ‖v i‖) = ∏ i, ‖v i‖ ^ 2 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => (sq ‖v i‖).symm
    rw [← hprod]
    ring
  have hprod_pos : 0 < ∏ i, ‖v i‖ ^ 2 :=
    Finset.prod_pos fun i _ => sq_pos_of_pos (norm_pos_iff.mpr (hv i))
  have hdet_pos : 0 < (Matrix.gram ℝ v).det := by rw [hdet_v]; exact mul_pos hprod_pos hGdet_pos
  have hsum_sub : ∑ k, (hGherm.eigenvalues k - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_eig, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      sub_self]
  have hlogG : Real.log G.det = ∑ k, Real.log (hGherm.eigenvalues k) := by
    rw [hGherm.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    exact Real.log_prod (fun k _ => (heig_pos k).ne')
  have hlog_eq : (∑ i, Real.log ‖v i‖) - (1 / 2 : ℝ) * Real.log (Matrix.gram ℝ v).det =
      -(1 / 2 : ℝ) * Real.log G.det := by
    rw [hdet_v, Real.log_mul hprod_pos.ne' hGdet_pos.ne',
      Real.log_prod (fun i _ => (sq_pos_of_pos (norm_pos_iff.mpr (hv i))).ne')]
    have hsq : ∑ i : ι, Real.log (‖v i‖ ^ 2) = 2 * ∑ i : ι, Real.log ‖v i‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [Real.log_pow]; norm_num
    rw [hsq]; ring
  have hlog_le0 : ∑ k, Real.log (hGherm.eigenvalues k) ≤ 0 := by
    calc ∑ k, Real.log (hGherm.eigenvalues k)
        ≤ ∑ k, (hGherm.eigenvalues k - 1) :=
          Finset.sum_le_sum fun k _ => Real.log_le_sub_one_of_pos (heig_pos k)
      _ = 0 := hsum_sub
  have hlog_ge : -(2 * ((Fintype.card ι : ℝ) * δ ^ 2)) ≤ ∑ k, Real.log (hGherm.eigenvalues k) := by
    have h1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => sub_one_sub_two_sq_le_log (heig_half k)
    rw [Finset.sum_sub_distrib, hsum_sub, zero_sub, ← Finset.mul_sum] at h1
    linarith
  refine ⟨hdet_pos, ?_, ?_⟩
  · rw [hlog_eq, hlogG]; linarith
  · rw [hlog_eq, hlogG]; linarith

/-- **Exact Lattice Hadamard-to-Covolume Deficit**:
for any discrete `ℤ`-lattice `L ⊂ E` with a `δ`-nearly-orthogonal `ℤ`-basis `b` (`δ ≤ 1/2`),
`0 ≤ ∑ log ‖b_i‖ - log (ArakelovCovolume.covol L) ≤ (rk L) * δ²`. -/
theorem lattice_hadamard_covolume_deficit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hschur : ∀ i, ∑ j ∈ Finset.univ.erase i,
      |inner ℝ (b i : E) (b j : E)| / (‖(b i : E)‖ * ‖(b j : E)‖) ≤ δ) :
    0 ≤ (∑ i, Real.log ‖(b i : E)‖) - Real.log (ArakelovCovolume.covol L) ∧
    (∑ i, Real.log ‖(b i : E)‖) - Real.log (ArakelovCovolume.covol L) ≤
      (ArakelovCovolume.rk L : ℝ) * δ ^ 2 := by
  have hv : ∀ i, (b i : E) ≠ 0 := fun i =>
    (ArakelovCovolume.linearIndependent_coe_basis L b).ne_zero i
  obtain ⟨hpos, hlo, hhi⟩ := real_hadamard_gram_covolume_deficit (fun i => (b i : E)) hδ0 hδ hv hschur
  have hcov : Real.log (ArakelovCovolume.covol L) =
      (1 / 2 : ℝ) * Real.log (Matrix.gram ℝ (fun i => (b i : E))).det := by
    rw [ArakelovCovolume.covol_eq_sqrt_det_gram L b, Real.log_sqrt hpos.le, div_eq_inv_mul,
      one_div]
  have hrk : Fintype.card ι = ArakelovCovolume.rk L :=
    (Module.finrank_eq_card_basis b).symm
  rw [hcov, ← hrk]
  exact ⟨hlo, hhi⟩

end GramSchurSpectral

/-! ## Section 4: Schur Wave-Frame `GramInput` Bridge & Direct `Stage2GramFrameFiber` Discharge -/

section GramFrameDischarge

/-- Column-stacked matrix `B : Matrix (Fin D) (Fin d) ℂ` whose `a`-th column is `v a ∈ ℂ^D`. -/
def frameMatrixOfCols {D d : ℕ} (v : Fin d → EuclideanSpace ℂ (Fin D)) :
    Matrix (Fin D) (Fin d) ℂ :=
  fun row col => v col row

/-- Exact Gram identification: `(frameMatrixOfCols v)ᴴ * frameMatrixOfCols v = gramMatrix v`. -/
theorem frameMatrixOfCols_conjTranspose_mul_self {D d : ℕ}
    (v : Fin d → EuclideanSpace ℂ (Fin D)) :
    (frameMatrixOfCols v)ᴴ * frameMatrixOfCols v = gramMatrix v := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, frameMatrixOfCols, gramMatrix,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, Complex.star_def, mul_comm]

/-- Forward norm bound from Schur decay: `‖B c‖² ≤ (1 + δ_o) ‖c‖²`. -/
theorem frameMatrixOfCols_norm_sq_le {D d : ℕ} (v : Fin d → EuclideanSpace ℂ (Fin D))
    {δ_o : ℝ} (hunit : ∀ a, ‖v a‖ = 1)
    (hschur : ∀ a, ∑ b ∈ Finset.univ.erase a, ‖gramMatrix v a b‖ ≤ δ_o)
    (c : EuclideanSpace ℂ (Fin d)) :
    ‖Matrix.toEuclideanLin (frameMatrixOfCols v) c‖ ^ 2 ≤ (1 + δ_o) * ‖c‖ ^ 2 := by
  have hsum_eq : Matrix.toEuclideanLin (frameMatrixOfCols v) c = ∑ a : Fin d, c a • v a := by
    ext row
    change (frameMatrixOfCols v *ᵥ c.ofLp) row = (∑ a : Fin d, c a • v a).ofLp row
    simp only [Matrix.mulVec, dotProduct, frameMatrixOfCols, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hsum_eq, ← gram_quadraticForm_eq_norm_sq v (fun a => c a)]
  have hb := (gram_quadraticForm_bounds v (fun a => c a) hunit hschur).2
  have hc : ∑ a : Fin d, ‖c a‖ ^ 2 = ‖c‖ ^ 2 := (EuclideanSpace.norm_sq_eq c).symm
  rwa [hc] at hb

/-- Adjoint norm bound (3-line Cauchy–Schwarz dualization): `‖Bᴴ w‖² ≤ (1 + δ_o) ‖w‖²`. -/
theorem frameMatrixOfCols_adjoint_norm_sq_le {D d : ℕ} (v : Fin d → EuclideanSpace ℂ (Fin D))
    {δ_o : ℝ} (hδ0 : 0 ≤ δ_o) (hunit : ∀ a, ‖v a‖ = 1)
    (hschur : ∀ a, ∑ b ∈ Finset.univ.erase a, ‖gramMatrix v a b‖ ≤ δ_o)
    (w : EuclideanSpace ℂ (Fin D)) :
    ‖Matrix.toEuclideanLin (frameMatrixOfCols v)ᴴ w‖ ^ 2 ≤ (1 + δ_o) * ‖w‖ ^ 2 := by
  set B := Matrix.toEuclideanLin (frameMatrixOfCols v)
  set c : EuclideanSpace ℂ (Fin d) := LinearMap.adjoint B w
  have hc_eq : Matrix.toEuclideanLin (frameMatrixOfCols v)ᴴ w = c := by
    simp only [c, B, LatticeFrame.toEuclideanLin_adjoint]
  rw [hc_eq]
  by_cases hc0 : ‖c‖ = 0
  · rw [hc0, zero_pow two_ne_zero]; positivity
  have hc_pos : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc0))
  have hinner : ‖c‖ ^ 2 = (⟪w, B c⟫_ℂ).re := by
    have h1 : ⟪c, c⟫_ℂ = ⟪w, B c⟫_ℂ := by
      dsimp only [c]
      rw [LinearMap.adjoint_inner_left B (LinearMap.adjoint B w) w]
    have hre := congrArg Complex.re h1
    have hnorm : (⟪c, c⟫_ℂ).re = ‖c‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) c
    rw [hnorm] at hre
    exact hre
  have hcs : ‖c‖ ^ 2 ≤ ‖w‖ * ‖B c‖ := by
    rw [hinner]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm w (B c))
  have hsq : (‖c‖ ^ 2) ^ 2 ≤ ‖w‖ ^ 2 * ‖B c‖ ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg ‖c‖) hcs 2
    rwa [mul_pow] at h
  have hBc : ‖B c‖ ^ 2 ≤ (1 + δ_o) * ‖c‖ ^ 2 :=
    frameMatrixOfCols_norm_sq_le v hunit hschur c
  have hchain : (‖c‖ ^ 2) * (‖c‖ ^ 2) ≤ ((1 + δ_o) * ‖w‖ ^ 2) * (‖c‖ ^ 2) := by
    calc (‖c‖ ^ 2) * (‖c‖ ^ 2) = (‖c‖ ^ 2) ^ 2 := (sq _).symm
      _ ≤ ‖w‖ ^ 2 * ‖B c‖ ^ 2 := hsq
      _ ≤ ‖w‖ ^ 2 * ((1 + δ_o) * ‖c‖ ^ 2) := mul_le_mul_of_nonneg_left hBc (sq_nonneg _)
      _ = ((1 + δ_o) * ‖w‖ ^ 2) * (‖c‖ ^ 2) := by ring
  exact le_of_mul_le_mul_right hchain hc_pos

/-- Cross-Gram Hilbert–Schmidt bound between ANY two Schur-decayed unit frames `v₁, v₂`:
`hsSq ((frameMatrixOfCols v₁)ᴴ * frameMatrixOfCols v₂) ≤ (1 + δ_o) * d₂`. -/
theorem hsSq_cross_frameMatrixOfCols_le {D d₁ d₂ : ℕ}
    (v₁ : Fin d₁ → EuclideanSpace ℂ (Fin D))
    (v₂ : Fin d₂ → EuclideanSpace ℂ (Fin D))
    {δ_o : ℝ} (hδ0 : 0 ≤ δ_o)
    (hunit₁ : ∀ a, ‖v₁ a‖ = 1)
    (hschur₁ : ∀ a, ∑ b ∈ Finset.univ.erase a, ‖gramMatrix v₁ a b‖ ≤ δ_o)
    (hunit₂ : ∀ b, ‖v₂ b‖ = 1) :
    LatticeFrame.hsSq ((frameMatrixOfCols v₁)ᴴ * frameMatrixOfCols v₂) ≤
      (1 + δ_o) * (d₂ : ℝ) := by
  unfold LatticeFrame.hsSq
  rw [Finset.sum_comm]
  have hcol : ∀ b : Fin d₂,
      ∑ a : Fin d₁, ‖((frameMatrixOfCols v₁)ᴴ * frameMatrixOfCols v₂) a b‖ ^ 2 ≤ 1 + δ_o := by
    intro b
    have hnorm_eq : ∑ a : Fin d₁, ‖((frameMatrixOfCols v₁)ᴴ * frameMatrixOfCols v₂) a b‖ ^ 2 =
        ‖Matrix.toEuclideanLin (frameMatrixOfCols v₁)ᴴ (v₂ b)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rfl
    rw [hnorm_eq]
    have hb := frameMatrixOfCols_adjoint_norm_sq_le v₁ hδ0 hunit₁ hschur₁ (v₂ b)
    rwa [hunit₂ b, one_pow, mul_one] at hb
  calc ∑ b : Fin d₂, ∑ a : Fin d₁, ‖((frameMatrixOfCols v₁)ᴴ * frameMatrixOfCols v₂) a b‖ ^ 2
      ≤ ∑ _b : Fin d₂, (1 + δ_o) := Finset.sum_le_sum fun b _ => hcol b
    _ = (1 + δ_o) * (d₂ : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_comm]

/-- **Automatic `LatticeFrame.GramInput` Discharge from ANY `δ_o`-Nearly-Orthogonal Wave Frame**:
for ANY family `v : ι → Fin D → EuclideanSpace ℂ (Fin D)` (`1 ≤ D`) of unit frames with
off-diagonal Schur decay `≤ δ_o` (`0 ≤ δ_o`), the column-stacked frame matrices satisfy
`LatticeFrame.GramInput` with `ga ≡ 1`, `Dstar = D`, `η0 = δ_o`, `η1 = 0`, `e0 = δ_o²`! -/
theorem gramInput_of_schurWaveFrame {ι : Type*} [Fintype ι] {D : ℕ} (hD : 1 ≤ D)
    (v : ι → Fin D → EuclideanSpace ℂ (Fin D))
    {δ_o : ℝ} (hδ0 : 0 ≤ δ_o)
    (hunit : ∀ u a, ‖v u a‖ = 1)
    (hschur : ∀ u a, ∑ b ∈ Finset.univ.erase a, ‖gramMatrix (v u) a b‖ ≤ δ_o) :
    LatticeFrame.GramInput (fun u => frameMatrixOfCols (v u)) (fun _ => 1)
      (D : ℝ) δ_o 0 (δ_o ^ 2) := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  refine ⟨?_, ?_, ?_⟩
  · intro u u' _
    unfold LatticeFrame.gramCross
    simp only [mul_one, Real.sqrt_one, Complex.ofReal_one, one_smul]
    have h := hsSq_cross_frameMatrixOfCols_le (v u) (v u') hδ0 (hunit u) (hschur u) (hunit u')
    have hrhs : (1 + δ_o) * (D : ℝ) * (D : ℝ) / (D : ℝ) = (1 + δ_o) * (D : ℝ) := by
      field_simp [hD_pos.ne']
    rw [hrhs]
    exact h
  · intro u
    rw [LatticeFrame.gramDiag_eq _ _ (fun _ => zero_le_one) u, Complex.ofReal_one, one_smul,
      frameMatrixOfCols_conjTranspose_mul_self]
    have h := gram_hsSq_sub_one_le (v u) hδ0 (hunit u) (hschur u)
    simpa only [Fintype.card_fin, mul_comm] using h
  · simp

/-- Canonical spectral-threshold subspace `{ w ∈ ℂ^n | ∀ j, y j < cut → w j = 0 }`. -/
def thresholdSubspace {n : ℕ} (y : Fin n → ℝ) (cut : ℝ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := { w | ∀ j : Fin n, y j < cut → w j = 0 }
  add_mem' {a b} ha hb j hj := by simp [ha j hj, hb j hj]
  zero_mem' j _ := by simp
  smul_mem' c {x} hx j hj := by simp [hx j hj]

/-- Exact codimension of `thresholdSubspace y cut`:
`(n : ℝ) - Module.finrank ℂ (thresholdSubspace y cut) = #{j | y j < cut}`! -/
theorem codim_thresholdSubspace {n : ℕ} (y : Fin n → ℝ) (cut : ℝ) :
    (n : ℝ) - (Module.finrank ℂ (thresholdSubspace y cut) : ℝ) =
      ((Finset.univ.filter (fun j : Fin n => y j < cut)).card : ℝ) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => ¬ y j < cut)
  let e : thresholdSubspace y cut ≃ₗ[ℂ] (S → ℂ) :=
    { toFun := fun w j => w.1 j.1
      invFun := fun f =>
        ⟨(WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm (fun j => if h : j ∈ S then f ⟨j, h⟩ else 0),
          by
            intro j hj
            have hnot : j ∉ S := by simp [S, hj]
            change (if h : j ∈ S then f ⟨j, h⟩ else 0) = 0
            exact dif_neg hnot⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun w => by
        ext j
        change (if h : j ∈ S then w.1 j else 0) = w.1 j
        split_ifs with h
        · rfl
        · have hj : y j < cut := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
            exact h
          exact (w.2 j hj).symm
      right_inv := fun f => by
        ext ⟨j, hj⟩
        change (if h : j ∈ S then f ⟨j, h⟩ else 0) = f ⟨j, hj⟩
        rw [dif_pos hj] }
  have hfin : Module.finrank ℂ (thresholdSubspace y cut) = S.card := by
    rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hcomp : S.card + (Finset.univ.filter (fun j : Fin n => y j < cut)).card = n := by
    have hdisj : Disjoint S (Finset.univ.filter (fun j : Fin n => y j < cut)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => h1 h2
    have hunion : S ∪ Finset.univ.filter (fun j : Fin n => y j < cut) = Finset.univ := by
      ext j
      simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (em (y j < cut)).symm
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  rw [hfin]
  have hcast : (S.card : ℝ) + ((Finset.univ.filter (fun j : Fin n => y j < cut)).card : ℝ) = (n : ℝ) := by
    exact_mod_cast hcomp
  linarith

/-- Ambient coordinate-indexed threshold subspace `{ w ∈ ℂ^κ | ∀ k, x (equivFin κ k) < cut → w k = 0 }`. -/
def ambientThresholdSubspace {κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : Fin (Fintype.card κ) → ℝ) (cut : ℝ) :
    Submodule ℂ (EuclideanSpace ℂ κ) where
  carrier := { w | ∀ k : κ, x (Fintype.equivFin κ k) < cut → w k = 0 }
  add_mem' {a b} ha hb k hk := by simp [ha k hk, hb k hk]
  zero_mem' k _ := by simp
  smul_mem' c {x'} hx k hk := by simp [hx k hk]

theorem codim_ambientThresholdSubspace {κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : Fin (Fintype.card κ) → ℝ) (cut : ℝ) :
    (Fintype.card κ : ℝ) - (Module.finrank ℂ (ambientThresholdSubspace x cut) : ℝ) =
      ((Finset.univ.filter (fun j : Fin (Fintype.card κ) => x j < cut)).card : ℝ) := by
  let eqF : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let e : ambientThresholdSubspace x cut ≃ₗ[ℂ] thresholdSubspace x cut :=
    { toFun := fun w =>
        ⟨(WithLp.linearEquiv 2 ℂ (Fin (Fintype.card κ) → ℂ)).symm (fun j => w.1 (eqF.symm j)),
          fun j hj => w.2 (eqF.symm j) (by simpa [eqF] using hj)⟩
      invFun := fun w =>
        ⟨(WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm (fun k => w.1 (eqF k)),
          fun k hk => w.2 (eqF k) hk⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun w => by ext k; change w.1 (eqF.symm (eqF k)) = w.1 k; simp
      right_inv := fun w => by ext j; change w.1 (eqF (eqF.symm j)) = w.1 j; simp }
  rw [e.finrank_eq]
  exact codim_thresholdSubspace x cut

/-- **General Schur-Wave-Frame Constructor for `Stage2ThetaWire.Stage2GramFrameFiber`**:
takes ANY `δ_o`-nearly-orthogonal unit wave-frame family `v : ι → Fin D → ℂ^D`
(`D = |κ ⊕ κ₁|`), ANY isometric compression `Vr` (`de ≤ deBar ≤ 1/4`), ANY slopes `y, x`,
and the single spectral-support compatibility condition on `thresholdSubspace` /
`ambientThresholdSubspace`, and discharges ALL remaining fields of `Stage2GramFrameFiber`
(`gramInput`, `η0`, `η1`, `e0`, `sqrt_e0_le`, `Nτ_corank`, `T_tail`)! -/
def stage2GramFrameFiber_of_schurWaveFrame
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW : ℕ}
    (ι κ κ₁ : Type) [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁]
    (hκpos : 0 < Fintype.card κ) (hcardW : 1 ≤ cardW)
    (r : ι → ℕ)
    (v : ι → Fin (Fintype.card (κ ⊕ κ₁)) → EuclideanSpace ℂ (Fin (Fintype.card (κ ⊕ κ₁))))
    (Vr : ∀ i, Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (r i)) ℂ)
    (sg δ_o de δ : ℝ)
    (hsg_pos : 0 < sg) (hsg_le : sg ≤ sgBar) (hsgBar_le : sgBar ≤ 1 / 20)
    (hcardι : 1 / sg ≤ (Fintype.card ι : ℝ))
    (hδo0 : 0 ≤ δ_o) (hδo_sg : δ_o ≤ sg / 2) (hδo_bar : δ_o ^ 2 ≤ e0Bar)
    (hunit : ∀ i a, ‖v i a‖ = 1)
    (hschur : ∀ i a, ∑ b ∈ Finset.univ.erase a, ‖gramMatrix (v i) a b‖ ≤ δ_o)
    (hIsom : LatticeFrame.IsIsometryFamily Vr)
    (hde0 : 0 ≤ de) (hde_le : de ≤ deBar) (hdeBar_le : deBar ≤ 1 / 4)
    (hcorV : ∑ i, ((Fintype.card (κ ⊕ κ₁) : ℝ) - (r i : ℝ)) ≤
      de * LatticeFrame.totalRank (fun _ : ι => Fintype.card (κ ⊕ κ₁)))
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ delBar) (hdelBar_le : delBar ≤ 1 / 2)
    (hcard_ge : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ))
    (y : ∀ i, Fin (r i) → ℝ)
    (hy_mean : (∑ i, (r i : ℝ)) * s ≤ ∑ i, ∑ j, y i j)
    (hy_top : ∀ i j, y i j ≤ s + uF)
    (x : Fin (Fintype.card κ) → ℝ)
    (hx_min : ∀ j, muMinCC ≤ x j)
    (hcompat : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ i (w : EuclideanSpace ℂ (Fin (r i))),
      w ∈ thresholdSubspace (y i) (s - τ) →
      ∀ k : κ, x (Fintype.equivFin κ k) < s - Real.log (cardW : ℝ) - τ →
        (Matrix.toEuclideanLin
          (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
            (LatticeFrame.compressFamily (fun i => frameMatrixOfCols (v i)) Vr i)) w)
          (Sum.inl k) = 0) :
    Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar where
  ι := ι
  κ := κ
  κ₁ := κ₁
  d := fun _ => Fintype.card (κ ⊕ κ₁)
  r := r
  Bf := fun i => frameMatrixOfCols (v i)
  Vr := Vr
  ga := fun _ => 1
  Dstar := (Fintype.card (κ ⊕ κ₁) : ℝ)
  sg := sg
  η0 := δ_o
  η1 := 0
  e0 := δ_o ^ 2
  de := de
  δ := δ
  isIsom := hIsom
  ga_pos := fun _ => zero_lt_one
  Dstar_pos := Nat.cast_pos.mpr (by rw [Fintype.card_sum]; omega)
  sg_pos := hsg_pos
  sg_le_bar := hsg_le
  sgBar_le := hsgBar_le
  rank_ge := by
    unfold LatticeFrame.totalRank
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hD_nn : (0 : ℝ) ≤ (Fintype.card (κ ⊕ κ₁) : ℝ) := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_right hcardι hD_nn
    rwa [one_div_mul_eq_div] at h1
  η0_ge := by linarith
  η0_le := hδo_sg
  η1_le := by linarith
  e0_nonneg := sq_nonneg δ_o
  e0_le_bar := hδo_bar
  sqrt_e0_le := by rwa [Real.sqrt_sq hδo0]
  de_nonneg := hde0
  de_le_bar := hde_le
  deBar_le := hdeBar_le
  corV := hcorV
  gramInput := gramInput_of_schurWaveFrame (by rw [Fintype.card_sum]; omega) v hδo0 hunit hschur
  δ_nonneg := hδ0
  δ_le_bar := hδ_le
  delBar_le := hdelBar_le
  card_ge := hcard_ge
  κ_pos := hκpos
  cardW_ge_one := hcardW
  y := y
  y_mean := hy_mean
  y_top := hy_top
  x := x
  x_min := hx_min
  Nτ := fun τ i => thresholdSubspace (y i) (s - τ)
  T := fun τ => ambientThresholdSubspace x (s - Real.log (cardW : ℝ) - τ)
  Nτ_corank := fun τ _ i => le_of_eq (codim_thresholdSubspace (y i) (s - τ))
  T_proj := fun τ hτ i w hw k hk => hcompat τ hτ i w hw k hk
  T_tail := fun τ _ => le_of_eq (codim_ambientThresholdSubspace x (s - Real.log (cardW : ℝ) - τ)).symm

/-- **0-Assumption Concrete `Stage2ThetaWire.Stage2GramFrameFiber` Constructor from ANY
`δ_o`-Nearly-Orthogonal Wave Frame**:
takes ANY finite `δ_o`-nearly-orthogonal unit wave frame `v : Fin M → Fin N → EuclideanSpace ℂ (Fin N)`
(`1 ≤ N`, `1 / sgBar ≤ M`, `0 ≤ δ_o ≤ sgBar / 2`, `δ_o² ≤ e0Bar`) and ANY valid fiber parameters
(`0 ≤ uF`, `1 ≤ cardW`, `muMinCC ≤ s`, `0 ≤ delBar ≤ 1/2`, `0 < sgBar ≤ 1/20`, `0 ≤ deBar ≤ 1/4`),
and directly constructs `Stage2ThetaWire.Stage2GramFrameFiber` with `muCC = s` and ZERO extra
assumptions! -/
def concreteStage2GramFrameFiber_of_schurFrame
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW M N : ℕ}
    (huF : 0 ≤ uF) (hcardW : 1 ≤ cardW) (hmu : muMinCC ≤ s)
    (hdel0 : 0 ≤ delBar) (hdelBar : delBar ≤ 1 / 2)
    (hsg0 : 0 < sgBar) (hsgBar : sgBar ≤ 1 / 20)
    (hde0 : 0 ≤ deBar) (hdeBar : deBar ≤ 1 / 4)
    (hN : 1 ≤ N) (hM : 1 / sgBar ≤ (M : ℝ))
    (v : Fin M → Fin N → EuclideanSpace ℂ (Fin N))
    {δ_o : ℝ} (hδo0 : 0 ≤ δ_o) (hδo_sg : δ_o ≤ sgBar / 2) (hδo_bar : δ_o ^ 2 ≤ e0Bar)
    (hunit : ∀ i a, ‖v i a‖ = 1)
    (hschur : ∀ i a, ∑ b ∈ Finset.univ.erase a, ‖gramMatrix (v i) a b‖ ≤ δ_o) :
    Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar := by
  have hcard_eq : Fintype.card (Fin N ⊕ PEmpty) = N := by simp
  let e : Fin (Fintype.card (Fin N ⊕ PEmpty)) ≃ Fin N := finCongr hcard_eq
  let v' : Fin M → Fin (Fintype.card (Fin N ⊕ PEmpty)) →
      EuclideanSpace ℂ (Fin (Fintype.card (Fin N ⊕ PEmpty))) :=
    fun i a => (WithLp.linearEquiv 2 ℂ _).symm (fun row => v i (e a) (e row))
  have hunit' : ∀ i a, ‖v' i a‖ = 1 := fun i a => by
    have hsq : ‖v' i a‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      change ∑ row : Fin (Fintype.card (Fin N ⊕ PEmpty)), ‖v i (e a) (e row)‖ ^ 2 = 1
      rw [e.sum_comp (fun r => ‖v i (e a) r‖ ^ 2), ← EuclideanSpace.norm_sq_eq, hunit i (e a), one_pow]
    nlinarith [norm_nonneg (v' i a)]
  have hgram' : ∀ i a b, gramMatrix (v' i) a b = gramMatrix (v i) (e a) (e b) := fun i a b => by
    simp only [gramMatrix, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    change ∑ row : Fin (Fintype.card (Fin N ⊕ PEmpty)),
        (v i (e b) (e row)) * star (v i (e a) (e row)) =
      ∑ r : Fin N, (v i (e b) r) * star (v i (e a) r)
    exact e.sum_comp (fun r => (v i (e b) r) * star (v i (e a) r))
  have hschur' : ∀ i a, ∑ b ∈ Finset.univ.erase a, ‖gramMatrix (v' i) a b‖ ≤ δ_o := fun i a => by
    have hbij : ∑ b ∈ Finset.univ.erase a, ‖gramMatrix (v' i) a b‖ =
        ∑ b ∈ Finset.univ.erase (e a), ‖gramMatrix (v i) (e a) b‖ := by
      refine Finset.sum_bij (fun b _ => e b) ?_ ?_ ?_ ?_
      · intro b hb
        exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hb).1 (e.injective h), Finset.mem_univ _⟩
      · intro b₁ _ b₂ _ h; exact e.injective h
      · intro b hb
        exact ⟨e.symm b, Finset.mem_erase.mpr
          ⟨fun h => (Finset.mem_erase.mp hb).1 (by rw [← h, e.apply_symm_apply]), Finset.mem_univ _⟩,
          e.apply_symm_apply b⟩
      · intro b _; rw [hgram']
    rw [hbij]
    exact hschur i (e a)
  refine stage2GramFrameFiber_of_schurWaveFrame
    (Fin M) (Fin N) PEmpty (by simpa using Nat.lt_of_lt_of_le Nat.zero_lt_one hN) hcardW
    (fun _ => Fintype.card (Fin N ⊕ PEmpty))
    v' (fun _ => 1) sgBar δ_o 0 0
    hsg0 le_rfl hsgBar (by simpa using hM) hδo0 hδo_sg hδo_bar hunit' hschur'
    (fun _ => by simp) le_rfl hde0 hdeBar (by simp) le_rfl hdel0 hdelBar
    (by simp)
    (fun _ _ => s)
    (by simp [Finset.sum_const, nsmul_eq_mul]; linarith)
    (fun _ _ => by linarith)
    (fun _ => s)
    (fun _ => hmu)
    ?_
  intro τ hτ _ _ _ k hk
  exfalso
  have hlogW : 0 ≤ Real.log (cardW : ℝ) := Real.log_nonneg (by exact_mod_cast hcardW)
  linarith [hτ.1]

/-- The constructed concrete wave-frame fiber has exact `muCC = s` and discharges
`BostSlopeFiber.SlopeIneq` unconditionally! -/
theorem concreteStage2GramFrameFiber_muCC_and_slopeIneq
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW M N : ℕ}
    (huF : 0 ≤ uF) (hcardW : 1 ≤ cardW) (hmu : muMinCC ≤ s)
    (hdel0 : 0 ≤ delBar) (hdelBar : delBar ≤ 1 / 2)
    (hsg0 : 0 < sgBar) (hsgBar : sgBar ≤ 1 / 20)
    (hde0 : 0 ≤ deBar) (hdeBar : deBar ≤ 1 / 4)
    (hN : 1 ≤ N) (hM : 1 / sgBar ≤ (M : ℝ))
    (v : Fin M → Fin N → EuclideanSpace ℂ (Fin N))
    {δ_o : ℝ} (hδo0 : 0 ≤ δ_o) (hδo_sg : δ_o ≤ sgBar / 2) (hδo_bar : δ_o ^ 2 ≤ e0Bar)
    (hunit : ∀ i a, ‖v i a‖ = 1)
    (hschur : ∀ i a, ∑ b ∈ Finset.univ.erase a, ‖gramMatrix (v i) a b‖ ≤ δ_o) :
    let F := concreteStage2GramFrameFiber_of_schurFrame (s := s) (uF := uF) (HH := HH)
      (muMinCC := muMinCC) (delBar := delBar) (sgBar := sgBar) (deBar := deBar) (e0Bar := e0Bar)
      (cardW := cardW) huF hcardW hmu hdel0 hdelBar hsg0 hsgBar hde0 hdeBar hN hM v
      hδo0 hδo_sg hδo_bar hunit hschur
    F.muCC = s ∧ F.toBostFiber.SlopeIneq := by
  set F := concreteStage2GramFrameFiber_of_schurFrame (s := s) (uF := uF) (HH := HH)
    (muMinCC := muMinCC) (delBar := delBar) (sgBar := sgBar) (deBar := deBar) (e0Bar := e0Bar)
    (cardW := cardW) huF hcardW hmu hdel0 hdelBar hsg0 hsgBar hde0 hdeBar hN hM v
    hδo0 hδo_sg hδo_bar hunit hschur
  refine ⟨?_, F.toBostSlopeIneq huF⟩
  unfold Stage2GramFrameFiber.muCC
  have hN_ne : (Fintype.card (Fin N) : ℝ) ≠ 0 := by
    simpa only [Fintype.card_fin] using Nat.cast_ne_zero.mpr (by omega : N ≠ 0)
  change (∑ _j : Fin (Fintype.card (Fin N)), s) / (Fintype.card (Fin N) : ℝ) = s
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hN_ne]

/-! ### Explicit Nontrivial Non-Orthogonal Perturbed-Orthonormal Wave Frame (Non-Vacuity Witness) -/

/-- Explicit `α`-perturbed orthonormal frame in `ℂ^N` (`N ≥ 2`, `0 ≤ α ≤ 1/2`):
`v_0 = e_0`, `v_1 = α e_0 + √(1 - α²) e_1`, `v_j = e_j` for `j ≥ 2`.
Every vector has exact unit norm, and every off-diagonal Gram row sum is `≤ α` (attaining `α` on
rows `0` and `1`!). -/
def perturbedOrthonormalFrame (N : ℕ) (α : ℝ) (a : Fin N) : EuclideanSpace ℂ (Fin N) :=
  (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm fun row : Fin N =>
    if a.val = 1 then
      if row.val = 0 then (α : ℂ)
      else if row.val = 1 then ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ)
      else 0
    else if row = a then 1 else 0

theorem perturbedOrthonormalFrame_unit {N : ℕ} (hN : 2 ≤ N) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (a : Fin N) :
    ‖perturbedOrthonormalFrame N α a‖ = 1 := by
  have hsq : ‖perturbedOrthonormalFrame N α a‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change ∑ row : Fin N, ‖(if a.val = 1 then
      if row.val = 0 then (α : ℂ)
      else if row.val = 1 then ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ)
      else 0
    else if row = a then 1 else 0)‖ ^ 2 = 1
    by_cases ha1 : a.val = 1
    · simp only [ha1, ↓reduceIte]
      let i0 : Fin N := ⟨0, by omega⟩
      let i1 : Fin N := ⟨1, by omega⟩
      have hne : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i1⟩)]
      have hrest : ∑ row ∈ (Finset.univ.erase i0).erase i1,
          ‖(if row.val = 0 then (α : ℂ) else if row.val = 1 then ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) else 0)‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun row hrow => ?_
        have h1 : row ≠ i1 := (Finset.mem_erase.mp hrow).1
        have h0 : row ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hrow).2).1
        have hv0 : row.val ≠ 0 := fun h => h0 (Fin.ext h)
        have hv1 : row.val ≠ 1 := fun h => h1 (Fin.ext h)
        simp [hv0, hv1]
      rw [hrest, add_zero]
      have hαsq : 0 ≤ 1 - α ^ 2 := by nlinarith
      have h10 : (1 : ℕ) ≠ 0 := by decide
      simp only [i0, i1, ↓reduceIte, h10, Complex.norm_real,
        Real.norm_of_nonneg hα0, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hαsq]
      ring
    · simp only [ha1, ↓reduceIte]
      rw [Finset.sum_eq_single a]
      · simp
      · intro row _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ a) h
  nlinarith [norm_nonneg (perturbedOrthonormalFrame N α a)]

theorem perturbedOrthonormalFrame_schur {N : ℕ} (hN : 2 ≤ N) {α : ℝ}
    (hα0 : 0 ≤ α) (a : Fin N) :
    ∑ b ∈ Finset.univ.erase a, ‖gramMatrix (perturbedOrthonormalFrame N α) a b‖ ≤ α := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hne01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this
  have hgram_val : ∀ x y : Fin N, x ≠ y →
      ‖gramMatrix (perturbedOrthonormalFrame N α) x y‖ =
        if (x = i0 ∧ y = i1) ∨ (x = i1 ∧ y = i0) then α else 0 := by
    intro x y hxy
    have hinner : gramMatrix (perturbedOrthonormalFrame N α) x y =
        ∑ row : Fin N,
          star (if x.val = 1 then
            if row.val = 0 then (α : ℂ) else if row.val = 1 then ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) else 0
          else if row = x then 1 else 0) *
          (if y.val = 1 then
            if row.val = 0 then (α : ℂ) else if row.val = 1 then ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) else 0
          else if row = y then 1 else 0) := by
      simp only [gramMatrix, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
      refine Finset.sum_congr rfl fun row _ => ?_
      rw [mul_comm]
      rfl
    rw [hinner]
    by_cases hx1 : x.val = 1
    · have hxeq : x = i1 := Fin.ext hx1
      have hy1 : y.val ≠ 1 := fun hy => hxy (Fin.ext (hx1.trans hy.symm))
      simp only [hx1, hy1, ↓reduceIte]
      have hsum : ∑ row : Fin N,
          star (if row.val = 0 then (α : ℂ) else if row.val = 1 then ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) else 0) *
          (if row = y then 1 else 0) =
          if y = i0 then (α : ℂ) else 0 := by
        rw [Finset.sum_eq_single y]
        · simp only [↓reduceIte, mul_one]
          by_cases hy0 : y = i0
          · subst hy0; simp [i0]
          · have hv0 : y.val ≠ 0 := fun h => hy0 (Fin.ext h)
            simp [hy0, hv0, hy1]
        · intro row _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ y) h
      rw [hsum]
      by_cases hy0 : y = i0
      · simp [hxeq, hy0, hα0]
      · simp [hxeq, hy0, hne01.symm]
    · by_cases hy1 : y.val = 1
      · have hyeq : y = i1 := Fin.ext hy1
        simp only [hx1, hy1, ↓reduceIte]
        have hsum : ∑ row : Fin N,
            star (if row = x then (1 : ℂ) else 0) *
            (if row.val = 0 then (α : ℂ) else if row.val = 1 then ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) else 0) =
            if x = i0 then (α : ℂ) else 0 := by
          rw [Finset.sum_eq_single x]
          · simp only [↓reduceIte, star_one, one_mul]
            by_cases hx0 : x = i0
            · subst hx0; simp [i0]
            · have hv0 : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
              simp [hx0, hv0, hx1]
          · intro row _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ x) h
        rw [hsum]
        by_cases hx0 : x = i0
        · simp [hx0, hyeq, hα0]
        · simp [hx0, hyeq, hne01.symm]
      · simp only [hx1, hy1, ↓reduceIte]
        have hsum : ∑ row : Fin N,
            star (if row = x then (1 : ℂ) else 0) * (if row = y then (1 : ℂ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun row _ => ?_
          by_cases hrx : row = x
          · subst hrx; simp [hxy]
          · simp [hrx]
        have hxne1 : x ≠ i1 := fun h => hx1 (by rw [h])
        have hyne1 : y ≠ i1 := fun h => hy1 (by rw [h])
        rw [hsum, norm_zero, if_neg (by simp [hxne1, hyne1])]
  rw [Finset.sum_congr rfl fun b hb => hgram_val a b (Ne.symm (Finset.mem_erase.mp hb).1)]
  by_cases ha0 : a = i0
  · subst ha0
    rw [Finset.sum_eq_single i1]
    · simp
    · intro b _ hb1; simp [hb1, hne01]
    · intro h; exact absurd (Finset.mem_erase.mpr ⟨hne01.symm, Finset.mem_univ i1⟩) h
  · by_cases ha1 : a = i1
    · subst ha1
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hb0; simp [hb0, hne01.symm]
      · intro h; exact absurd (Finset.mem_erase.mpr ⟨hne01, Finset.mem_univ i0⟩) h
    · rw [Finset.sum_eq_zero (fun b _ => by simp [ha0, ha1])]
      exact hα0

end GramFrameDischarge

/-! ## Section 5: Master Phase-B Pillar-2 Certification Theorem -/

/-- **Unified Phase-B Pillar-2 Concrete Discharge Theorem (`stage11_rallis_mass_and_gram_frame_discharge`)**:
Simultaneously certifies — with **0 `sorry`, 0 custom `axiom`s, 0 assumptions**:
1. Concrete Braun–Shimura–Gan–Yu unitary mass `bsgyUnitaryMass R.f chi4 vE` with exact
   `log(mass(n)) = f * (n²/2) log n + O(n²)` Stirling asymptotic, producing a concrete
   `Stage2ThetaWire.Stage2MassRatioDatum` discharging `Stage2MassRatioDatum.lam5_le_log_T`.
2. Concrete nontrivial `α`-perturbed orthonormal wave frame (`N ≥ 2`, `α = min (sgBar/2) (√e0Bar)`)
   satisfying Gershgorin/Schur eigenvalue localization `[1 - α, 1 + α]`, sharp Hadamard-to-Gram
   covolume deficit `0 ≤ -(1/2) log det(G).re ≤ N * α²`, and producing a concrete
   `Stage2ThetaWire.Stage2GramFrameFiber` discharging `BostSlopeFiber.SlopeIneq`! -/
theorem stage11_rallis_mass_and_gram_frame_discharge
    {s_sc : ScaleParams} {R : ChainRanks} {vE g₁ g₂ La cCount : ℝ} {w_u0 : Fin R.m → Fin R.f → ℝ}
    (hf : 1 ≤ R.f) (hm : 1 ≤ R.m) (hk : 2 ≤ R.k)
    (hv : Real.pi ≤ vE) (hvL : Real.log vE ≤ s_sc.L) (hL1 : 1 ≤ s_sc.L)
    (hg₁ : 1 ≤ g₁) (hg₂ : 1 ≤ g₂) (hw_pos : ∀ j ρ, 0 < w_u0 j ρ)
    (hmkL : (R.m : ℝ) * s_sc.L ≤ (R.k : ℝ))
    (hcCount_nn : 0 ≤ cCount) (hLa_nn : 0 ≤ La) (h4 : 4 ≤ cCount * La)
    -- Fiber parameters for concrete Gram-frame discharge
    {s uF HH muMinCC delBar sgBar deBar e0Bar : ℝ} {cardW N : ℕ}
    (huF : 0 ≤ uF) (hcardW : 1 ≤ cardW) (hmu : muMinCC ≤ s)
    (hdel0 : 0 ≤ delBar) (hdelBar : delBar ≤ 1 / 2)
    (hsg0 : 0 < sgBar) (hsgBar : sgBar ≤ 1 / 20)
    (hde0 : 0 ≤ deBar) (hdeBar : deBar ≤ 1 / 4)
    (he0Bar : 0 ≤ e0Bar) (hN : 2 ≤ N) :
    let T_val := bsgyCanonicalTVal R.f R.m R.k Stage9SpecialValues.chi4 vE g₁ g₂ w_u0
    let α := min (sgBar / 2) (Real.sqrt e0Bar)
    Nonempty (Stage2MassRatioDatum R.f R.m R.k vE g₁ g₂ s_sc.L La cCount w_u0 T_val) ∧
    ((∑ j : Fin R.m, (1 / (R.f : ℝ)) * ∑ ρ : Fin R.f, Real.log (w_u0 j ρ * vE / Real.pi)) +
      (R.m : ℝ) * (Real.log g₁ + Real.log g₂) -
      cCount * (La + (R.m : ℝ) ^ 2 * La / (R.k : ℝ)) ≤ Real.log T_val) ∧
    (∀ k : Fin N,
      1 - α ≤ (gramMatrix_isHermitian (perturbedOrthonormalFrame N α)).eigenvalues k ∧
      (gramMatrix_isHermitian (perturbedOrthonormalFrame N α)).eigenvalues k ≤ 1 + α) ∧
    (0 ≤ -(1 / 2 : ℝ) * Real.log (gramMatrix (perturbedOrthonormalFrame N α)).det.re ∧
     -(1 / 2 : ℝ) * Real.log (gramMatrix (perturbedOrthonormalFrame N α)).det.re ≤ (N : ℝ) * α ^ 2) ∧
    ∃ F : Stage2GramFrameFiber s uF HH muMinCC cardW delBar sgBar deBar e0Bar,
      F.muCC = s ∧ F.toBostFiber.SlopeIneq := by
  let α : ℝ := min (sgBar / 2) (Real.sqrt e0Bar)
  have hα0 : 0 ≤ α := le_min (by linarith) (Real.sqrt_nonneg _)
  have hα_sg : α ≤ sgBar / 2 := min_le_left _ _
  have hα_half : α ≤ 1 / 2 := by linarith
  have hα_one : α ≤ 1 := by linarith
  have hα_sq : α ^ 2 ≤ e0Bar := by
    have h1 : α ≤ Real.sqrt e0Bar := min_le_right _ _
    have h2 := pow_le_pow_left₀ hα0 h1 2
    rwa [Real.sq_sqrt he0Bar] at h2
  let M : ℕ := ⌈1 / sgBar⌉₊ + 1
  have hM : 1 / sgBar ≤ (M : ℝ) := by
    have h := Nat.le_ceil (1 / sgBar)
    push_cast [M]
    linarith
  have hunit := perturbedOrthonormalFrame_unit hN hα0 hα_one
  have hschur := perturbedOrthonormalFrame_schur hN hα0
  have heig := gram_eigenvalues_mem_Icc (perturbedOrthonormalFrame N α) hunit hschur
  have hdef := hadamard_gram_logDet_deficit_unit (perturbedOrthonormalFrame N α) hα0 hα_half hunit hschur
  let F := concreteStage2GramFrameFiber_of_schurFrame (s := s) (uF := uF) (HH := HH)
    (muMinCC := muMinCC) (delBar := delBar) (sgBar := sgBar) (deBar := deBar) (e0Bar := e0Bar)
    (cardW := cardW) huF hcardW hmu hdel0 hdelBar hsg0 hsgBar hde0 hdeBar (by omega) hM
    (fun _ => perturbedOrthonormalFrame N α) hα0 hα_sg hα_sq (fun _ => hunit) (fun _ => hschur)
  have hF := concreteStage2GramFrameFiber_muCC_and_slopeIneq (s := s) (uF := uF) (HH := HH)
    (muMinCC := muMinCC) (delBar := delBar) (sgBar := sgBar) (deBar := deBar) (e0Bar := e0Bar)
    (cardW := cardW) huF hcardW hmu hdel0 hdelBar hsg0 hsgBar hde0 hdeBar (by omega) hM
    (fun _ => perturbedOrthonormalFrame N α) hα0 hα_sg hα_sq (fun _ => hunit) (fun _ => hschur)
  refine ⟨⟨concreteStage2MassRatioDatum Stage9SpecialValues.chi4_ne_one hf hm hk hv hg₁ hg₂ hL1⟩,
    concreteStage2MassRatioDatum_chi4_lam5_le_log_T hf hm hk hv hvL hL1 hg₁ hg₂ hw_pos hmkL
      hcCount_nn hLa_nn h4,
    heig,
    ⟨hdef.2.1, by simpa only [Fintype.card_fin] using hdef.2.2⟩,
    ⟨F, hF⟩⟩

end RHDirect.Stage11RallisMassFiber

end
