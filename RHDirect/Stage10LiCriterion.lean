import RHDirect.Stage7HadamardXiProduct
import RHDirect.Stage7VonMangoldtExplicit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Stage 10 — Unconditional Concrete Li's 1997 Criterion Directly on Mathlib's `riemannZeta` & `xi(s)`

This module establishes **unconditionally (`0` assumptions, `0` custom axioms, `0` `sorry`)**
in pure Mathlib `v4.33.1`:

1. **Cayley Transform & Paired Li Zero-Sum (`liCoeff`)**:
   - `cayley (ρ : ℂ) := 1 - 1 / ρ` maps `{Re(ρ) > 1/2}` bijectively onto `{‖w‖ < 1}`,
     `{Re(ρ) = 1/2}` onto `{‖w‖ = 1}`, and `{Re(ρ) < 1/2}` onto `{‖w‖ > 1}`, while the
     functional equation `ρ ↦ 1 - ρ` corresponds to inversion `w ↦ w⁻¹`.
   - The paired Li summand `liPairTerm ρ n := (1 - cayley ρ ^ n) + (1 - cayley (1 - ρ) ^ n)`
     admits the exact algebraic factorization
     `liPairTerm ρ n = (1 / (ρ * (1 - ρ))) * (∑ j ∈ range n, w ^ j) * (∑ l ∈ range n, (w⁻¹) ^ l)`
     and hence is unconditionally absolutely summable over `xiZeroSeq` for every `n : ℕ`
     directly from `Stage7HadamardXiProduct.xiZeroSeq_summable_inv_sq`.
   - `liCoeff (n : ℕ) : ℝ := (1 / 2) * ∑' k, (liPairTerm (xiZeroSeq k) n).re`.

2. **Generating Function & Keiper–Li Analytic Representation**:
   - Let `xiCayley (z : ℂ) := xi (1 / (1 - z))` and `liGenFun (z : ℂ) := z * logDeriv xiCayley z`.
   - On the open disk `‖z‖ < liMinRadius` (where `liMinRadius := ⨅ k, ‖cayley (xiZeroSeq k)‖ ∈ (0, 1]`),
     `HasSum (fun n => (liCoeff n : ℂ) * z ^ n) (liGenFun z)`.
   - `liCoeff n = (n! : ℝ)⁻¹ * (iteratedDeriv n liGenFun 0).re` for all `n : ℕ`, and for all `n ≥ 1`,
     `liCoeff n = liCoeffAnalytic n := ((n - 1)! : ℝ)⁻¹ * (iteratedDeriv n (fun s => s ^ (n - 1) * Complex.log (xi s)) 1).re`.

3. **Unconditional Li's 1997 Criterion (via Bombieri–Lagarias / Pringsheim)**:
   - `riemannHypothesis_iff_liCoeff_nonneg : RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff n`
   - `riemannHypothesis_iff_liCoeff_pos : RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 < liCoeff n`
   - `riemannHypothesis_iff_liCoeffAnalytic_nonneg : RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeffAnalytic n`.

4. **Exact Value of `λ₁` & Davenport–Hadamard Constant `xiHadamardB`**:
   - `digamma_half_eq : Complex.digamma (1 / 2 : ℂ) = -((Real.eulerMascheroniConstant + 2 * Real.log 2 : ℝ) : ℂ)`
   - `deriv_xi_one : deriv xi 1 = ((1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 : ℝ) : ℂ)`
   - `xiHadamardB_eq : xiHadamardB = ((-1 - Real.eulerMascheroniConstant / 2 + Real.log (4 * Real.pi) / 2 : ℝ) : ℂ)`
   - `liCoeff_one_eq : liCoeff 1 = 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2`
   - `liCoeff_one_pos : 0 < liCoeff 1`.
-/

noncomputable section

open Complex Filter Topology Set Finset
open RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage7HadamardXiProduct

namespace RHDirect.Stage10LiCriterion

/-! ## Section 1: Cayley Transform & Functional-Equation Symmetries of `xiZeroSeq` -/

/-- The Cayley transform `ρ ↦ 1 - 1 / ρ` mapping the critical line `Re(ρ) = 1/2` to the
unit circle `‖w‖ = 1` and `Re(ρ) > 1/2` to the open unit disk `‖w‖ < 1`. -/
def cayley (ρ : ℂ) : ℂ := 1 - 1 / ρ

lemma cayley_one_sub {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    cayley (1 - ρ) = (cayley ρ)⁻¹ := by
  have h1ρ : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr h1.symm
  unfold cayley
  field_simp [h0, h1ρ]
  ring

lemma cayley_conj (ρ : ℂ) :
    cayley (starRingEnd ℂ ρ) = starRingEnd ℂ (cayley ρ) := by
  simp [cayley]

lemma inv_one_sub_cayley {ρ : ℂ} (h0 : ρ ≠ 0) :
    1 / (1 - cayley ρ) = ρ := by
  unfold cayley
  field_simp [h0]
  ring

lemma cayley_inv_one_sub {z : ℂ} (hz : z ≠ 1) :
    cayley (1 / (1 - z)) = z := by
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold cayley
  field_simp [h1z]
  ring

lemma cayley_ne_zero {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : cayley ρ ≠ 0 := by
  unfold cayley
  rw [sub_ne_zero, one_div]
  intro h
  have : ρ = 1 := by
    have hmul := congrArg (· * ρ) h
    simpa [inv_mul_cancel₀ h0] using hmul
  exact h1 this

lemma cayley_ne_one {ρ : ℂ} (h0 : ρ ≠ 0) : cayley ρ ≠ 1 := by
  unfold cayley
  simp [h0]

lemma normSq_cayley_eq {ρ : ℂ} (h0 : ρ ≠ 0) :
    Complex.normSq (cayley ρ) = 1 + (1 - 2 * ρ.re) / Complex.normSq ρ := by
  have hns' : ρ.re ^ 2 + ρ.im ^ 2 ≠ 0 := by
    have hpos := Complex.normSq_pos.mpr h0
    rw [Complex.normSq_apply] at hpos
    nlinarith
  have hrew : cayley ρ = (ρ - 1) / ρ := by
    unfold cayley
    field_simp [h0]
  rw [hrew, map_div₀, Complex.normSq_apply (ρ - 1), Complex.normSq_apply ρ]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, ← sq]
  field_simp [hns']
  ring

lemma norm_cayley_lt_one_iff {ρ : ℂ} (h0 : ρ ≠ 0) :
    ‖cayley ρ‖ < 1 ↔ 1 / 2 < ρ.re := by
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr h0
  have hsq : ‖cayley ρ‖ < 1 ↔ Complex.normSq (cayley ρ) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    constructor
    · intro h; nlinarith [norm_nonneg (cayley ρ)]
    · intro h; nlinarith [norm_nonneg (cayley ρ)]
  rw [hsq, normSq_cayley_eq h0]
  constructor
  · intro h
    have hneg : (1 - 2 * ρ.re) / Complex.normSq ρ < 0 := by linarith
    have hnum : 1 - 2 * ρ.re < 0 :=
      (div_neg_iff.mp hneg).resolve_left (fun hc => by linarith [hc.2]) |>.1
    linarith
  · intro h
    have hnum : 1 - 2 * ρ.re < 0 := by linarith
    have hneg : (1 - 2 * ρ.re) / Complex.normSq ρ < 0 := div_neg_of_neg_of_pos hnum hns
    linarith

lemma norm_cayley_eq_one_iff {ρ : ℂ} (h0 : ρ ≠ 0) :
    ‖cayley ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr h0
  have hsq : ‖cayley ρ‖ = 1 ↔ Complex.normSq (cayley ρ) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    constructor
    · intro h; rw [h]; norm_num
    · intro h; nlinarith [norm_nonneg (cayley ρ)]
  rw [hsq, normSq_cayley_eq h0]
  constructor
  · intro h
    have hz : (1 - 2 * ρ.re) / Complex.normSq ρ = 0 := by linarith
    have hnum : 1 - 2 * ρ.re = 0 := (div_eq_zero_iff.mp hz).resolve_right hns.ne'
    linarith
  · intro h
    have hnum : 1 - 2 * ρ.re = 0 := by linarith
    rw [hnum, zero_div, add_zero]

/-- Exact Cayley characterization of the critical line `Re(ρ) = 1/2`. -/
theorem abs_cayley_eq_one_iff_re_eq_half {ρ : ℂ} (h0 : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = 1 / 2 :=
  norm_cayley_eq_one_iff h0

lemma norm_cayley_gt_one_iff {ρ : ℂ} (h0 : ρ ≠ 0) :
    1 < ‖cayley ρ‖ ↔ ρ.re < 1 / 2 := by
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr h0
  have hsq : 1 < ‖cayley ρ‖ ↔ 1 < Complex.normSq (cayley ρ) := by
    rw [Complex.normSq_eq_norm_sq]
    constructor
    · intro h; nlinarith [norm_nonneg (cayley ρ)]
    · intro h; nlinarith [norm_nonneg (cayley ρ)]
  rw [hsq, normSq_cayley_eq h0]
  constructor
  · intro h
    have hpos : 0 < (1 - 2 * ρ.re) / Complex.normSq ρ := by linarith
    have hnum : 0 < 1 - 2 * ρ.re :=
      (div_pos_iff.mp hpos).resolve_right (fun hc => by linarith [hc.2]) |>.1
    linarith
  · intro h
    have hnum : 0 < 1 - 2 * ρ.re := by linarith
    have hpos : 0 < (1 - 2 * ρ.re) / Complex.normSq ρ := div_pos hnum hns
    linarith

private lemma exists_xiZeroSeq_eq {s : ℂ} (hs : xi s = 0) :
    ∃ k : ℕ, xiZeroSeq k = s :=
  isMultiplicityZeroSeq_xi.exists_of_eq_zero differentiable_xi (by simp) hs

lemma xiZeroSeq_ne_one (k : ℕ) : xiZeroSeq k ≠ 1 := by
  intro h
  have hlt := (xiZeroSeq_strip k).2
  rw [h, Complex.one_re] at hlt
  exact lt_irrefl 1 hlt

lemma xiZeroSeq_one_sub_ne_zero (k : ℕ) : 1 - xiZeroSeq k ≠ 0 :=
  sub_ne_zero.mpr (xiZeroSeq_ne_one k).symm

lemma xiZeroSeq_cayley_ne_zero (k : ℕ) : cayley (xiZeroSeq k) ≠ 0 :=
  cayley_ne_zero (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k)

lemma xiZeroSeq_cayley_ne_one (k : ℕ) : cayley (xiZeroSeq k) ≠ 1 :=
  cayley_ne_one (xiZeroSeq_ne_zero k)

/-- Complex-conjugation permutation symmetry of `xiZeroSeq`:
`∃ κ : Equiv.Perm ℕ, ∀ k, xiZeroSeq (κ k) = starRingEnd ℂ (xiZeroSeq k)`. -/
theorem xiZeroSeq_conj_perm :
    ∃ κ : Equiv.Perm ℕ, ∀ k : ℕ, xiZeroSeq (κ k) = starRingEnd ℂ (xiZeroSeq k) := by
  have hzero_conj : ∀ s : ℂ, xi s = 0 → xi (starRingEnd ℂ s) = 0 := fun s hs => by
    rw [RHDirect.Stage6XiZeroDensity.xi_conj, hs, map_zero]
  let f : XiZeroWithMult → XiZeroWithMult := fun x =>
    ⟨⟨starRingEnd ℂ x.1.1, hzero_conj x.1.1 x.1.2⟩,
      x.2.cast (RHDirect.Stage7VonMangoldtExplicit.analyticOrderNatAt_xi_conj x.1.1).symm⟩
  have hf_inv : Function.Involutive f := by
    intro ⟨⟨s, hs⟩, j⟩
    dsimp only [f]
    have hs' : starRingEnd ℂ (starRingEnd ℂ s) = s := Complex.conj_conj s
    refine Sigma.ext (Subtype.ext hs') ?_
    exact (Fin.heq_ext_iff (congrArg (analyticOrderNatAt xi) hs')).mpr rfl
  let f_perm : Equiv.Perm XiZeroWithMult := hf_inv.toPerm f
  refine ⟨xiZeroEquiv.trans (f_perm.trans xiZeroEquiv.symm), fun k => ?_⟩
  simp only [xiZeroSeq, Equiv.trans_apply, Equiv.apply_symm_apply, f_perm,
    Function.Involutive.coe_toPerm, f]

/-- Functional-equation reflection permutation symmetry of `xiZeroSeq`:
`∃ σ : Equiv.Perm ℕ, ∀ k, xiZeroSeq (σ k) = 1 - xiZeroSeq k`. -/
theorem xiZeroSeq_one_sub_perm :
    ∃ σ : Equiv.Perm ℕ, ∀ k : ℕ, xiZeroSeq (σ k) = 1 - xiZeroSeq k := by
  obtain ⟨τ, hτ⟩ := xiZeroSeq_symm_perm
  obtain ⟨κ, hκ⟩ := xiZeroSeq_conj_perm
  refine ⟨κ.trans τ, fun k => ?_⟩
  simp only [Equiv.trans_apply, hτ, hκ, Complex.conj_conj]

lemma tendsto_norm_xiZeroSeq_atTop :
    Tendsto (fun k : ℕ => ‖xiZeroSeq k‖) atTop atTop :=
  RHDirect.Stage5JensenHadamard.tendsto_norm_atTop_of_summable_inv_sq
    xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq

lemma tendsto_cayley_xiZeroSeq_one :
    Tendsto (fun k : ℕ => cayley (xiZeroSeq k)) atTop (𝓝 (1 : ℂ)) := by
  have hinv : Tendsto (fun k : ℕ => 1 / xiZeroSeq k) atTop (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun k : ℕ => ‖xiZeroSeq k‖⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp tendsto_norm_xiZeroSeq_atTop
    exact h1.congr fun k => by simp [one_div]
  simpa [cayley] using tendsto_const_nhds.sub hinv

lemma tendsto_norm_cayley_xiZeroSeq_one :
    Tendsto (fun k : ℕ => ‖cayley (xiZeroSeq k)‖) atTop (𝓝 (1 : ℝ)) := by
  simpa using tendsto_cayley_xiZeroSeq_one.norm

/-! ## Section 2: Minimum Cayley Radius `liMinRadius` & Unconditional Convergence of `liCoeff` -/

/-- The minimum modulus `R₀ = ⨅ k, ‖1 - 1 / ρ_k‖` of all Cayley-transformed zeros of `xi`.
It satisfies `0 < liMinRadius ≤ 1`, with `liMinRadius = 1 ↔ RiemannHypothesis`. -/
def liMinRadius : ℝ := ⨅ k : ℕ, ‖cayley (xiZeroSeq k)‖

lemma liMinRadius_le_norm_cayley (k : ℕ) : liMinRadius ≤ ‖cayley (xiZeroSeq k)‖ :=
  ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ k

lemma liMinRadius_le_one : liMinRadius ≤ 1 :=
  ge_of_tendsto tendsto_norm_cayley_xiZeroSeq_one
    (Eventually.of_forall liMinRadius_le_norm_cayley)

lemma liMinRadius_pos : 0 < liMinRadius := by
  have hev : ∀ᶠ k : ℕ in atTop, (1 / 2 : ℝ) < ‖cayley (xiZeroSeq k)‖ :=
    tendsto_norm_cayley_xiZeroSeq_one.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  let S : Finset ℝ := insert (1 / 2 : ℝ) ((Finset.range N).image fun k => ‖cayley (xiZeroSeq k)‖)
  have hSne : S.Nonempty := Finset.insert_nonempty _ _
  set m : ℝ := S.min' hSne
  have hm_pos : 0 < m := by
    rw [Finset.lt_min'_iff]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · norm_num
    · rcases Finset.mem_image.mp hx' with ⟨k, _, rfl⟩
      exact norm_pos_iff.mpr (xiZeroSeq_cayley_ne_zero k)
  have hm_le : ∀ k : ℕ, m ≤ ‖cayley (xiZeroSeq k)‖ := fun k => by
    by_cases hk : k < N
    · exact Finset.min'_le S _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk)))
    · have hhalf : m ≤ (1 / 2 : ℝ) := Finset.min'_le S _ (Finset.mem_insert_self _ _)
      exact le_trans hhalf (hN k (not_lt.mp hk)).le
  exact lt_of_lt_of_le hm_pos (le_ciInf hm_le)

lemma exists_min_cayley_of_lt_one (hR : liMinRadius < 1) :
    ∃ k : ℕ, ‖cayley (xiZeroSeq k)‖ = liMinRadius := by
  let mid : ℝ := (liMinRadius + 1) / 2
  have hR_lt_mid : liMinRadius < mid := by dsimp only [mid]; linarith
  have hmid_lt_one : mid < 1 := by dsimp only [mid]; linarith
  have hev : ∀ᶠ k : ℕ in atTop, mid < ‖cayley (xiZeroSeq k)‖ :=
    tendsto_norm_cayley_xiZeroSeq_one.eventually (Ioi_mem_nhds hmid_lt_one)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hN_pos : 0 < N := by
    by_contra h0
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos h0
    have hge : mid ≤ liMinRadius := le_ciInf fun k => (hN k (by omega)).le
    linarith
  have hne : (Finset.range N).Nonempty := Finset.nonempty_range_iff.mpr hN_pos.ne'
  obtain ⟨k₀, hk₀_mem, hk₀_min⟩ := Finset.exists_min_image (Finset.range N)
    (fun k => ‖cayley (xiZeroSeq k)‖) hne
  refine ⟨k₀, le_antisymm ?_ (liMinRadius_le_norm_cayley k₀)⟩
  have hlt_mid : ∃ j : ℕ, ‖cayley (xiZeroSeq j)‖ < mid := by
    by_contra hall
    push Not at hall
    have : mid ≤ liMinRadius := le_ciInf hall
    linarith
  obtain ⟨j, hj⟩ := hlt_mid
  have hjN : j < N := by
    by_contra hge
    exact not_lt.mpr (hN j (not_lt.mp hge)).le hj
  have hk₀_lt_mid : ‖cayley (xiZeroSeq k₀)‖ < mid :=
    lt_of_le_of_lt (hk₀_min j (Finset.mem_range.mpr hjN)) hj
  have hle_all : ∀ k : ℕ, ‖cayley (xiZeroSeq k₀)‖ ≤ ‖cayley (xiZeroSeq k)‖ := fun k => by
    by_cases hk : k < N
    · exact hk₀_min k (Finset.mem_range.mpr hk)
    · exact le_trans hk₀_lt_mid.le (hN k (not_lt.mp hk)).le
  exact le_ciInf hle_all

theorem liMinRadius_eq_one_iff_RH : liMinRadius = 1 ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zeros_on_half_line]
  constructor
  · intro hR s hs
    have hlt_ge : ∀ k : ℕ, 1 ≤ ‖cayley (xiZeroSeq k)‖ := fun k => hR ▸ liMinRadius_le_norm_cayley k
    obtain ⟨k, hk⟩ := exists_xiZeroSeq_eq hs
    have hge1 : 1 ≤ ‖cayley s‖ := hk ▸ hlt_ge k
    have hs0 : s ≠ 0 := hk ▸ xiZeroSeq_ne_zero k
    have hs1 : s ≠ 1 := hk ▸ xiZeroSeq_ne_one k
    have hle_half : s.re ≤ 1 / 2 := by
      by_contra hgt
      exact not_lt.mpr hge1 ((norm_cayley_lt_one_iff hs0).mpr (not_le.mp hgt))
    have h1s_zero : xi (1 - s) = 0 := by rw [xi_one_sub]; exact hs
    obtain ⟨k', hk'⟩ := exists_xiZeroSeq_eq h1s_zero
    have hge1' : 1 ≤ ‖cayley (1 - s)‖ := hk' ▸ hlt_ge k'
    have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
    have hge_half : 1 / 2 ≤ s.re := by
      by_contra hlt
      have hgt' : 1 / 2 < (1 - s).re := by simp; linarith
      exact not_lt.mpr hge1' ((norm_cayley_lt_one_iff h1s0).mpr hgt')
    linarith
  · intro hRH
    refine le_antisymm liMinRadius_le_one (le_ciInf fun k => ?_)
    have hre : (xiZeroSeq k).re = 1 / 2 := hRH (xiZeroSeq k) (xiZeroSeq_zero k)
    rw [(norm_cayley_eq_one_iff (xiZeroSeq_ne_zero k)).mpr hre]

/-- The paired Li zero-sum term `(1 - (1 - 1/ρ)^n) + (1 - (1 - 1/(1 - ρ))^n)` for a zero `ρ`
paired with its functional-equation reflection `1 - ρ`. -/
def liPairTerm (ρ : ℂ) (n : ℕ) : ℂ :=
  (1 - cayley ρ ^ n) + (1 - cayley (1 - ρ) ^ n)

@[simp]
lemma liPairTerm_zero (ρ : ℂ) : liPairTerm ρ 0 = 0 := by
  simp [liPairTerm]

lemma liPairTerm_one {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    liPairTerm ρ 1 = 1 / ρ + 1 / (1 - ρ) := by
  have h1ρ : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr h1.symm
  simp only [liPairTerm, pow_one, cayley]
  field_simp [h0, h1ρ]
  ring

lemma liPairTerm_conj (ρ : ℂ) (n : ℕ) :
    liPairTerm (starRingEnd ℂ ρ) n = starRingEnd ℂ (liPairTerm ρ n) := by
  have h1 : (1 : ℂ) - starRingEnd ℂ ρ = starRingEnd ℂ (1 - ρ) := by
    simp only [map_sub, map_one]
  rw [liPairTerm, liPairTerm, h1, cayley_conj, cayley_conj]
  simp only [map_add, map_sub, map_one, map_pow]

lemma liPairTerm_one_sub (ρ : ℂ) (n : ℕ) :
    liPairTerm (1 - ρ) n = liPairTerm ρ n := by
  simp only [liPairTerm, sub_sub_cancel]
  ring

/-- **Exact Algebraic Factorization of `liPairTerm`**:
for every `ρ ≠ 0, 1` and `n : ℕ`,
`(1 - w^n) + (1 - w^{-n}) = (1 / (ρ * (1 - ρ))) * (∑ j ∈ range n, w^j) * (∑ l ∈ range n, (w⁻¹)^l)`. -/
lemma liPairTerm_eq_prod {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (n : ℕ) :
    liPairTerm ρ n =
      (1 / (ρ * (1 - ρ))) *
        (∑ j ∈ Finset.range n, cayley ρ ^ j) *
        (∑ l ∈ Finset.range n, (cayley ρ)⁻¹ ^ l) := by
  have hw : cayley ρ ≠ 0 := cayley_ne_zero h0 h1
  have h1ρ : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr h1.symm
  have hstep1 : liPairTerm ρ n = (1 - cayley ρ ^ n) * (1 - (cayley ρ)⁻¹ ^ n) := by
    rw [liPairTerm, cayley_one_sub h0 h1]
    have hmul : cayley ρ ^ n * (cayley ρ)⁻¹ ^ n = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
    linear_combination -hmul
  have hgeom1 : 1 - cayley ρ ^ n = (1 - cayley ρ) * ∑ j ∈ Finset.range n, cayley ρ ^ j := by
    have h := geom_sum_mul_neg (cayley ρ) n
    linear_combination -h
  have hgeom2 : 1 - (cayley ρ)⁻¹ ^ n =
      (1 - (cayley ρ)⁻¹) * ∑ l ∈ Finset.range n, (cayley ρ)⁻¹ ^ l := by
    have h := geom_sum_mul_neg (cayley ρ)⁻¹ n
    linear_combination -h
  have hcoef : (1 - cayley ρ) * (1 - (cayley ρ)⁻¹) = 1 / (ρ * (1 - ρ)) := by
    rw [← cayley_one_sub h0 h1]
    unfold cayley
    field_simp [h0, h1ρ]
    ring
  rw [hstep1, hgeom1, hgeom2]
  calc (1 - cayley ρ) * (∑ j ∈ Finset.range n, cayley ρ ^ j) *
        ((1 - (cayley ρ)⁻¹) * ∑ l ∈ Finset.range n, (cayley ρ)⁻¹ ^ l)
      = ((1 - cayley ρ) * (1 - (cayley ρ)⁻¹)) *
          (∑ j ∈ Finset.range n, cayley ρ ^ j) *
          (∑ l ∈ Finset.range n, (cayley ρ)⁻¹ ^ l) := by ring
    _ = (1 / (ρ * (1 - ρ))) *
          (∑ j ∈ Finset.range n, cayley ρ ^ j) *
          (∑ l ∈ Finset.range n, (cayley ρ)⁻¹ ^ l) := by rw [hcoef]

/-- Sharp uniform norm bound on `liPairTerm ρ n`:
whenever `0 < R ≤ 1`, `R ≤ ‖cayley ρ‖`, and `R ≤ ‖(cayley ρ)⁻¹‖`,
`‖liPairTerm ρ n‖ ≤ (n : ℝ) ^ 2 * R⁻¹ ^ n / (‖ρ‖ * ‖1 - ρ‖)`. -/
lemma norm_liPairTerm_le {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) {R : ℝ} (hRpos : 0 < R)
    (hR1 : R ≤ 1) (hRw : R ≤ ‖cayley ρ‖) (hRwinv : R ≤ ‖(cayley ρ)⁻¹‖) (n : ℕ) :
    ‖liPairTerm ρ n‖ ≤ (n : ℝ) ^ 2 * R⁻¹ ^ n / (‖ρ‖ * ‖1 - ρ‖) := by
  have hw : cayley ρ ≠ 0 := cayley_ne_zero h0 h1
  have hRinv_ge : 1 ≤ R⁻¹ := (one_le_inv₀ hRpos).mpr hR1
  have hsum_le_one : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖∑ j ∈ Finset.range n, u ^ j‖ ≤ (n : ℝ) := fun u hu => by
    calc ‖∑ j ∈ Finset.range n, u ^ j‖
        ≤ ∑ j ∈ Finset.range n, ‖u ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_pow]; exact pow_le_one₀ (norm_nonneg u) hu
      _ = (n : ℝ) := by simp
  have hsum_le_Rinv : ∀ u : ℂ, ‖u‖ ≤ R⁻¹ →
      ‖∑ j ∈ Finset.range n, u ^ j‖ ≤ (n : ℝ) * R⁻¹ ^ n := fun u hu => by
    calc ‖∑ j ∈ Finset.range n, u ^ j‖
        ≤ ∑ j ∈ Finset.range n, ‖u ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, R⁻¹ ^ n := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [norm_pow]
          exact le_trans (pow_le_pow_left₀ (norm_nonneg u) hu j)
            (pow_le_pow_right₀ hRinv_ge (Finset.mem_range.mp hj).le)
      _ = (n : ℝ) * R⁻¹ ^ n := by simp
  have hprod_bound :
      ‖∑ j ∈ Finset.range n, cayley ρ ^ j‖ * ‖∑ l ∈ Finset.range n, (cayley ρ)⁻¹ ^ l‖ ≤
        (n : ℝ) ^ 2 * R⁻¹ ^ n := by
    by_cases hle : ‖cayley ρ‖ ≤ 1
    · have h1' := hsum_le_one (cayley ρ) hle
      have h2' : ‖(cayley ρ)⁻¹‖ ≤ R⁻¹ := by
        rw [norm_inv]
        exact inv_anti₀ hRpos hRw
      have h3' := hsum_le_Rinv (cayley ρ)⁻¹ h2'
      calc ‖∑ j ∈ Finset.range n, cayley ρ ^ j‖ * ‖∑ l ∈ Finset.range n, (cayley ρ)⁻¹ ^ l‖
          ≤ (n : ℝ) * ((n : ℝ) * R⁻¹ ^ n) := mul_le_mul h1' h3' (norm_nonneg _) (Nat.cast_nonneg n)
        _ = (n : ℝ) ^ 2 * R⁻¹ ^ n := by ring
    · have hgt : 1 < ‖cayley ρ‖ := not_le.mp hle
      have hinv_le : ‖(cayley ρ)⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ hgt.le
      have hw_le : ‖cayley ρ‖ ≤ R⁻¹ := by
        have h' : ‖cayley ρ‖⁻¹ ≥ R := by simpa [norm_inv] using hRwinv
        rw [← inv_inv ‖cayley ρ‖]
        exact inv_anti₀ hRpos h'
      have h1' := hsum_le_Rinv (cayley ρ) hw_le
      have h2' := hsum_le_one (cayley ρ)⁻¹ hinv_le
      calc ‖∑ j ∈ Finset.range n, cayley ρ ^ j‖ * ‖∑ l ∈ Finset.range n, (cayley ρ)⁻¹ ^ l‖
          ≤ ((n : ℝ) * R⁻¹ ^ n) * (n : ℝ) :=
            mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
        _ = (n : ℝ) ^ 2 * R⁻¹ ^ n := by ring
  rw [liPairTerm_eq_prod h0 h1 n, norm_mul, norm_mul, one_div, norm_inv, norm_mul]
  rw [mul_assoc, div_eq_inv_mul]
  have hden_nonneg : 0 ≤ (‖ρ‖ * ‖1 - ρ‖)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hprod_bound hden_nonneg

lemma summable_inv_mul_one_sub :
    Summable (fun k : ℕ => (‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹) := by
  have hev : ∀ᶠ k : ℕ in atTop, (2 : ℝ) ≤ ‖xiZeroSeq k‖ :=
    tendsto_norm_xiZeroSeq_atTop.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  have hev_bound : ∀ᶠ k : ℕ in atTop,
      ‖(‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹‖ ≤ 2 * (‖xiZeroSeq k‖ ^ 2)⁻¹ := by
    refine hev.mono fun k hk => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have htri : ‖xiZeroSeq k‖ - 1 ≤ ‖1 - xiZeroSeq k‖ := by
      have h1 := norm_sub_norm_le (xiZeroSeq k) 1
      rw [norm_one, norm_sub_rev] at h1
      exact h1
    have hhalf : ‖xiZeroSeq k‖ / 2 ≤ ‖1 - xiZeroSeq k‖ := by linarith
    have hpos1 : 0 < ‖xiZeroSeq k‖ := by linarith
    have hpos2 : 0 < ‖1 - xiZeroSeq k‖ := by linarith
    have hprod : ‖xiZeroSeq k‖ ^ 2 / 2 ≤ ‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖ := by
      nlinarith
    have hinv := inv_anti₀ (by positivity : 0 < ‖xiZeroSeq k‖ ^ 2 / 2) hprod
    calc (‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹
        ≤ (‖xiZeroSeq k‖ ^ 2 / 2)⁻¹ := hinv
      _ = 2 * (‖xiZeroSeq k‖ ^ 2)⁻¹ := by field_simp
  exact Summable.of_norm_bounded_eventually (xiZeroSeq_summable_inv_sq.mul_left 2)
    (Nat.cofinite_eq_atTop.symm ▸ hev_bound)

lemma liMinRadius_le_norm_cayley_inv (k : ℕ) :
    liMinRadius ≤ ‖(cayley (xiZeroSeq k))⁻¹‖ := by
  obtain ⟨σ, hσ⟩ := xiZeroSeq_one_sub_perm
  have h1 : cayley (xiZeroSeq (σ k)) = (cayley (xiZeroSeq k))⁻¹ := by
    rw [hσ k, cayley_one_sub (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k)]
  rw [← h1]
  exact liMinRadius_le_norm_cayley (σ k)

lemma norm_liPairTerm_xiZeroSeq_le (k n : ℕ) :
    ‖liPairTerm (xiZeroSeq k) n‖ ≤
      (n : ℝ) ^ 2 * liMinRadius⁻¹ ^ n * (‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹ := by
  have h := norm_liPairTerm_le (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k)
    liMinRadius_pos liMinRadius_le_one (liMinRadius_le_norm_cayley k)
    (liMinRadius_le_norm_cayley_inv k) n
  simpa [div_eq_mul_inv] using h

/-- **Unconditional Absolute Summability of Paired Li Terms** for every `n : ℕ`. -/
theorem summable_liPairTerm (n : ℕ) :
    Summable (fun k : ℕ => liPairTerm (xiZeroSeq k) n) := by
  refine Summable.of_norm_bounded (g := fun k =>
    ((n : ℝ) ^ 2 * liMinRadius⁻¹ ^ n) * (‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹) ?_ ?_
  · exact summable_inv_mul_one_sub.mul_left _
  · intro k; exact norm_liPairTerm_xiZeroSeq_le k n

/-- Unconditional summability of the real parts of paired Li terms for every `n : ℕ`. -/
theorem summable_liPairTerm_re (n : ℕ) :
    Summable (fun k : ℕ => (liPairTerm (xiZeroSeq k) n).re) :=
  Complex.reCLM.summable (summable_liPairTerm n)

/-- **Concrete Li Coefficient `λ_n`** defined directly on Mathlib's `xiZeroSeq`:
`liCoeff n = (1/2) * ∑'_k Re((1 - (1 - 1/ρ_k)^n) + (1 - (1 - 1/(1 - ρ_k))^n))`. -/
def liCoeff (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑' k : ℕ, (liPairTerm (xiZeroSeq k) n).re

@[simp]
theorem liCoeff_zero : liCoeff 0 = 0 := by
  simp [liCoeff]

/-- Reality of the complex paired zero-sum: `(liCoeff n : ℂ) = (1 / 2) * ∑'_k liPairTerm (xiZeroSeq k) n`. -/
theorem liCoeff_ofReal_eq_tsum (n : ℕ) :
    (liCoeff n : ℂ) = (1 / 2 : ℂ) * ∑' k : ℕ, liPairTerm (xiZeroSeq k) n := by
  obtain ⟨κ, hκ⟩ := xiZeroSeq_conj_perm
  have hsum := summable_liPairTerm n
  have hconj : starRingEnd ℂ (∑' k : ℕ, liPairTerm (xiZeroSeq k) n) =
      ∑' k : ℕ, liPairTerm (xiZeroSeq k) n := by
    rw [Complex.conj_tsum]
    calc ∑' k : ℕ, starRingEnd ℂ (liPairTerm (xiZeroSeq k) n)
        = ∑' k : ℕ, liPairTerm (xiZeroSeq (κ k)) n :=
          tsum_congr fun k => by rw [hκ k, liPairTerm_conj]
      _ = ∑' k : ℕ, liPairTerm (xiZeroSeq k) n :=
          Equiv.tsum_eq κ (fun k => liPairTerm (xiZeroSeq k) n)
  have him : (∑' k : ℕ, liPairTerm (xiZeroSeq k) n).im = 0 :=
    Complex.conj_eq_iff_im.mp hconj
  have hre : (∑' k : ℕ, liPairTerm (xiZeroSeq k) n).re =
      ∑' k : ℕ, (liPairTerm (xiZeroSeq k) n).re := by
    simpa using (Complex.reCLM.map_tsum hsum)
  have hreal : ((∑' k : ℕ, (liPairTerm (xiZeroSeq k) n).re : ℝ) : ℂ) =
      ∑' k : ℕ, liPairTerm (xiZeroSeq k) n := by
    apply Complex.ext
    · simp [hre]
    · simp [him]
  simp only [liCoeff, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, hreal]

/-! ## Section 3: Cayley Generating Function `liGenFun` & Keiper–Li Analytic Identity -/

/-- The Cayley-pulled-back xi function `g(z) := xi(1 / (1 - z))`, holomorphic on `ℂ \ {1}`
with `g(0) = xi(1) = 1 ≠ 0`. -/
def xiCayley (z : ℂ) : ℂ := xi (1 / (1 - z))

/-- The Li generating function `φ(z) := z * (g'(z) / g(z))` where `g(z) = xi(1 / (1 - z))`. -/
def liGenFun (z : ℂ) : ℂ := z * logDeriv xiCayley z

@[simp]
lemma xiCayley_zero : xiCayley 0 = 1 := by
  simp [xiCayley]

lemma xiCayley_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < liMinRadius) :
    xiCayley z ≠ 0 := by
  intro hzero
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hz
    linarith [liMinRadius_le_one]
  obtain ⟨k, hk⟩ := exists_xiZeroSeq_eq hzero
  have hzw : z = cayley (xiZeroSeq k) := by
    rw [hk, cayley_inv_one_sub hz1]
  have hge := liMinRadius_le_norm_cayley k
  rw [← hzw] at hge
  linarith

lemma hasDerivAt_xiCayley {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt xiCayley (deriv xi (1 / (1 - z)) * (1 / (1 - z) ^ 2)) z := by
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have hsub : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hinv : HasDerivAt (fun w : ℂ => 1 / (1 - w)) (1 / (1 - z) ^ 2) z := by
    have h := hsub.inv h1z
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp [one_div]) |>.congr_deriv ?_
    field_simp [h1z]
  exact ((differentiable_xi (1 / (1 - z))).hasDerivAt).comp z hinv

lemma differentiableAt_xiCayley {z : ℂ} (hz : z ≠ 1) : DifferentiableAt ℂ xiCayley z :=
  (hasDerivAt_xiCayley hz).differentiableAt

lemma logDeriv_xiCayley_eq {z : ℂ} (hz : z ≠ 1) :
    logDeriv xiCayley z = (1 / (1 - z) ^ 2) * (deriv xi (1 / (1 - z)) / xi (1 / (1 - z))) := by
  rw [logDeriv_apply, (hasDerivAt_xiCayley hz).deriv]
  simp only [xiCayley]
  ring

/-- Complex-exact Davenport pairing formula for `xiHadamardB = deriv xi 0`:
`xiHadamardB = -(1 / 2) * ∑' k, (1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k))`. -/
theorem xiHadamardB_eq_neg_half_tsum :
    xiHadamardB = -(1 / 2 : ℂ) * ∑' k : ℕ, (1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k)) := by
  have hxi1 : xi 1 ≠ 0 := by simp
  have hld1 := xi_logDeriv_hadamard 1 hxi1
  have hanti : deriv xi 1 / xi 1 = -xiHadamardB := by
    have h := logDeriv_xi_one_sub 0
    simp only [sub_zero, xi_zero, div_one] at h
    exact h
  rw [hanti] at hld1
  have h2B : (2 : ℂ) * xiHadamardB =
      -∑' k : ℕ, (1 / (1 - xiZeroSeq k) + 1 / xiZeroSeq k) := by
    linear_combination -hld1
  have hcomm : ∑' k : ℕ, (1 / (1 - xiZeroSeq k) + 1 / xiZeroSeq k) =
      ∑' k : ℕ, (1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k)) :=
    tsum_congr fun k => add_comm _ _
  rw [hcomm] at h2B
  linear_combination (1 / 2 : ℂ) * h2B

/-- Partial-fraction identity for a single zero `ρ` under the Cayley substitution `s = 1 / (1 - z)`. -/
private lemma cayley_hadamard_single_term {ρ z : ℂ} (h0 : ρ ≠ 0) (hz1 : z ≠ 1)
    (hzw : z ≠ cayley ρ) :
    (1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - ρ) + 1 / ρ) =
      (1 / (1 - z) - 1 / (cayley ρ - z)) + (1 / ρ) * (1 / (1 - z) ^ 2) := by
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hwz : cayley ρ - z ≠ 0 := sub_ne_zero.mpr hzw.symm
  have hrel : 1 / (1 - z) - ρ = -ρ * (cayley ρ - z) / (1 - z) := by
    unfold cayley
    field_simp [h0, h1z]
    ring
  rw [hrel]
  field_simp [h0, h1z, hwz]
  unfold cayley
  field_simp [h0, h1z]
  ring

/-- Exact paired partial-fraction expansion of `logDeriv xiCayley z` on the open disk `‖z‖ < liMinRadius`. -/
theorem logDeriv_xiCayley_eq_paired_tsum {z : ℂ} (hz : ‖z‖ < liMinRadius) :
    logDeriv xiCayley z =
      (1 / 2 : ℂ) * ∑' k : ℕ,
        ((1 / (1 - z) - 1 / (cayley (xiZeroSeq k) - z)) +
         (1 / (1 - z) - 1 / (cayley (1 - xiZeroSeq k) - z))) := by
  have hz1 : z ≠ 1 := by
    intro h; rw [h, norm_one] at hz; linarith [liMinRadius_le_one]
  have hxis : xi (1 / (1 - z)) ≠ 0 := xiCayley_ne_zero_of_norm_lt hz
  have hs_ne : ∀ k : ℕ, 1 / (1 - z) ≠ xiZeroSeq k := fun k h => hxis (h ▸ xiZeroSeq_zero k)
  have hzw : ∀ k : ℕ, z ≠ cayley (xiZeroSeq k) := fun k h => by
    have hge := liMinRadius_le_norm_cayley k
    rw [← h] at hge; linarith
  have hzw' : ∀ k : ℕ, z ≠ cayley (1 - xiZeroSeq k) := fun k h => by
    have hge := liMinRadius_le_norm_cayley_inv k
    rw [← cayley_one_sub (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k), ← h] at hge
    linarith
  obtain ⟨σ, hσ⟩ := xiZeroSeq_one_sub_perm
  have hsum_had : Summable (fun k : ℕ => 1 / (1 / (1 - z) - xiZeroSeq k) + 1 / xiZeroSeq k) :=
    RHDirect.Stage5JensenHadamard.summable_hadamard_term xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq hs_ne
  have hsum_had_scaled :
      Summable (fun k : ℕ =>
        (1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - xiZeroSeq k) + 1 / xiZeroSeq k)) :=
    hsum_had.mul_left _
  have hsum_had1 : Summable (fun k : ℕ => 1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k)) := by
    have h1 : ∀ k : ℕ, (1 : ℂ) ≠ xiZeroSeq k := fun k h => xiZeroSeq_ne_one k h.symm
    have hs := RHDirect.Stage5JensenHadamard.summable_hadamard_term
      xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq h1
    exact hs.congr fun k => add_comm _ _
  have hsum_had1_scaled :
      Summable (fun k : ℕ => (-(1 / 2 : ℂ) * (1 / (1 - z) ^ 2)) *
        (1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k))) :=
    hsum_had1.mul_left _
  have hsum_had_σ :
      Summable (fun k : ℕ =>
        (1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - xiZeroSeq (σ k)) + 1 / xiZeroSeq (σ k))) :=
    hsum_had_scaled.comp_injective σ.injective
  have hpair_eq : ∀ k : ℕ,
      (-(1 / 2 : ℂ) * (1 / (1 - z) ^ 2)) * (1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k)) +
      (1 / 2 : ℂ) * ((1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - xiZeroSeq k) + 1 / xiZeroSeq k) +
        (1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - xiZeroSeq (σ k)) + 1 / xiZeroSeq (σ k))) =
      (1 / 2 : ℂ) * ((1 / (1 - z) - 1 / (cayley (xiZeroSeq k) - z)) +
        (1 / (1 - z) - 1 / (cayley (1 - xiZeroSeq k) - z))) := fun k => by
    rw [hσ k,
      cayley_hadamard_single_term (xiZeroSeq_ne_zero k) hz1 (hzw k),
      cayley_hadamard_single_term (xiZeroSeq_one_sub_ne_zero k) hz1 (hzw' k)]
    ring
  rw [logDeriv_xiCayley_eq hz1, xi_logDeriv_hadamard _ hxis, mul_add, ← tsum_mul_left,
    xiHadamardB_eq_neg_half_tsum]
  have hB_rw : (1 / (1 - z) ^ 2) * (-(1 / 2 : ℂ) *
      ∑' k : ℕ, (1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k))) =
      ∑' k : ℕ, (-(1 / 2 : ℂ) * (1 / (1 - z) ^ 2)) *
        (1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k)) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  have hsymm_tsum :
      ∑' k : ℕ, (1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - xiZeroSeq k) + 1 / xiZeroSeq k) =
      (1 / 2 : ℂ) * ∑' k : ℕ,
        ((1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - xiZeroSeq k) + 1 / xiZeroSeq k) +
         (1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - xiZeroSeq (σ k)) + 1 / xiZeroSeq (σ k))) := by
    rw [hsum_had_scaled.tsum_add hsum_had_σ,
      Equiv.tsum_eq σ (fun k => (1 / (1 - z) ^ 2) * (1 / (1 / (1 - z) - xiZeroSeq k) + 1 / xiZeroSeq k))]
    ring
  rw [hB_rw, hsymm_tsum, ← tsum_mul_left,
    ← hsum_had1_scaled.tsum_add ((hsum_had_scaled.add hsum_had_σ).mul_left (1 / 2 : ℂ))]
  rw [← tsum_mul_left]
  exact tsum_congr hpair_eq

/-- Geometric-series expansion of `z * (1 / (1 - z) - 1 / (w - z))` for `‖z‖ < min(1, ‖w‖)`. -/
private lemma hasSum_one_sub_inv_pow {w z : ℂ} (hw : w ≠ 0) (hz1 : ‖z‖ < 1) (hzw : ‖z‖ < ‖w‖) :
    HasSum (fun n : ℕ => (1 - (w⁻¹) ^ n) * z ^ n) (z * (1 / (1 - z) - 1 / (w - z))) := by
  have h1 : HasSum (fun n : ℕ => z ^ n) (1 - z)⁻¹ := hasSum_geometric_of_norm_lt_one hz1
  have hzw_norm : ‖z * w⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv]
    exact (mul_inv_lt_iff₀ (norm_pos_iff.mpr hw)).mpr (by simpa using hzw)
  have h2 : HasSum (fun n : ℕ => (z * w⁻¹) ^ n) (1 - z * w⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hzw_norm
  have h2' : HasSum (fun n : ℕ => w⁻¹ * (z * w⁻¹) ^ n) (w⁻¹ * (1 - z * w⁻¹)⁻¹) :=
    h2.mul_left w⁻¹
  have hdiff := h1.sub h2'
  have hmul := hdiff.mul_left z
  have hval : z * ((1 - z)⁻¹ - w⁻¹ * (1 - z * w⁻¹)⁻¹) = z * (1 / (1 - z) - 1 / (w - z)) := by
    have hwz : w - z ≠ 0 := by
      intro h; rw [sub_eq_zero.mp h] at hzw; exact lt_irrefl _ hzw
    have h1zw : 1 - z * w⁻¹ ≠ 0 := by
      intro h; have : z * w⁻¹ = 1 := (sub_eq_zero.mp h).symm
      rw [this, norm_one] at hzw_norm; exact lt_irrefl _ hzw_norm
    congr 1
    rw [one_div, one_div]
    congr 1
    field_simp [hw, hwz, h1zw]
  rw [hval] at hmul
  have hshift : HasSum (fun n : ℕ => (1 - (w⁻¹) ^ n) * z ^ n)
      (z * (1 / (1 - z) - 1 / (w - z))) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, pow_zero, sub_self, zero_mul, sub_zero]
    refine hmul.congr_fun fun m => ?_
    rw [pow_succ, pow_succ, mul_pow]
    ring
  exact hshift

/-- Termwise power-series identity for each paired zero `{ρ, 1 - ρ}` on `‖z‖ < liMinRadius`. -/
private lemma hasSum_liPairTerm_mul_pow (k : ℕ) {z : ℂ} (hz : ‖z‖ < liMinRadius) :
    HasSum (fun n : ℕ => liPairTerm (xiZeroSeq k) n * z ^ n)
      (z * ((1 / (1 - z) - 1 / (cayley (xiZeroSeq k) - z)) +
            (1 / (1 - z) - 1 / (cayley (1 - xiZeroSeq k) - z)))) := by
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hz liMinRadius_le_one
  have hzw1 : ‖z‖ < ‖cayley (xiZeroSeq k)‖ := lt_of_lt_of_le hz (liMinRadius_le_norm_cayley k)
  have hzw2 : ‖z‖ < ‖cayley (1 - xiZeroSeq k)‖ := by
    rw [cayley_one_sub (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k)]
    exact lt_of_lt_of_le hz (liMinRadius_le_norm_cayley_inv k)
  have hs1 := hasSum_one_sub_inv_pow (xiZeroSeq_cayley_ne_zero k) hz1 hzw1
  have hs2 := hasSum_one_sub_inv_pow
    (cayley_ne_zero (xiZeroSeq_one_sub_ne_zero k) (by
      intro h; exact xiZeroSeq_ne_zero k (by linear_combination -h))) hz1 hzw2
  have hadd := hs1.add hs2
  have hsum_val : z * (1 / (1 - z) - 1 / (cayley (xiZeroSeq k) - z)) +
      z * (1 / (1 - z) - 1 / (cayley (1 - xiZeroSeq k) - z)) =
      z * ((1 / (1 - z) - 1 / (cayley (xiZeroSeq k) - z)) +
           (1 / (1 - z) - 1 / (cayley (1 - xiZeroSeq k) - z))) := by ring
  rw [hsum_val] at hadd
  refine hadd.congr_fun fun n => ?_
  have hinv1 : (cayley (xiZeroSeq k))⁻¹ = cayley (1 - xiZeroSeq k) :=
    (cayley_one_sub (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k)).symm
  have hinv2 : (cayley (1 - xiZeroSeq k))⁻¹ = cayley (xiZeroSeq k) := by
    rw [cayley_one_sub (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k), inv_inv]
  rw [hinv1, hinv2, liPairTerm]
  ring

/-- Helper: `∑_n (n : ℝ)^2 * q^n` is summable for `0 ≤ q < 1`. -/
private lemma summable_sq_mul_pow_of_lt_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * q ^ n) := by
  let r : ℝ := (q + 1) / 2
  have hr0 : 0 < r := by dsimp only [r]; linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hqr : q / r < 1 := (div_lt_one hr0).mpr (by dsimp only [r]; linarith)
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (q / r) ^ n) atTop (𝓝 0) := by
    by_cases hq : q = 0
    · subst hq
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      simp [zero_div, zero_pow hn]
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      have hratio_gt : 1 < (q / r)⁻¹ := (one_lt_inv₀ (div_pos hqpos hr0)).mpr hqr
      have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 hratio_gt
      refine ht.congr fun n => ?_
      rw [inv_pow, div_inv_eq_mul]
  have hev : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) ^ 2 * q ^ n‖ ≤ r ^ n := by
    refine (htend.eventually (Iio_mem_nhds zero_lt_one)).mono fun n hn => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have hrn : 0 < r ^ n := pow_pos hr0 n
    have h2 : (n : ℝ) ^ 2 * q ^ n / r ^ n < 1 := by
      simpa [div_pow, mul_div_assoc] using hn
    exact ((div_lt_one hrn).mp h2).le
  exact Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one hr0.le hr1)
    (Nat.cofinite_eq_atTop.symm ▸ hev)

/-- **UNCONDITIONAL EXACT GENERATING-FUNCTION IDENTITY (`liCoeff_eq_taylor_logDeriv_cayley`)**:
for EVERY `z : ℂ` with `‖z‖ < liMinRadius`,
`HasSum (fun n : ℕ => (liCoeff n : ℂ) * z ^ n) (liGenFun z)`. -/
theorem liCoeff_eq_taylor_logDeriv_cayley {z : ℂ} (hz : ‖z‖ < liMinRadius) :
    HasSum (fun n : ℕ => (liCoeff n : ℂ) * z ^ n) (liGenFun z) := by
  have hq0 : 0 ≤ ‖z‖ * liMinRadius⁻¹ := mul_nonneg (norm_nonneg z) (inv_nonneg.mpr liMinRadius_pos.le)
  have hq1 : ‖z‖ * liMinRadius⁻¹ < 1 := (mul_inv_lt_iff₀ liMinRadius_pos).mpr (by simpa using hz)
  have hsum_n : Summable (fun n : ℕ => (n : ℝ) ^ 2 * (‖z‖ * liMinRadius⁻¹) ^ n) :=
    summable_sq_mul_pow_of_lt_one hq0 hq1
  have hsum_prod : Summable (fun p : ℕ × ℕ => liPairTerm (xiZeroSeq p.1) p.2 * z ^ p.2) := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ =>
      (‖xiZeroSeq p.1‖ * ‖1 - xiZeroSeq p.1‖)⁻¹ *
      ((p.2 : ℝ) ^ 2 * (‖z‖ * liMinRadius⁻¹) ^ p.2))
      (summable_inv_mul_one_sub.mul_of_nonneg hsum_n (fun _ => by positivity) (fun _ => by positivity)) ?_
    rintro ⟨k, n⟩
    rw [norm_mul, norm_pow]
    calc ‖liPairTerm (xiZeroSeq k) n‖ * ‖z‖ ^ n
        ≤ ((n : ℝ) ^ 2 * liMinRadius⁻¹ ^ n * (‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹) * ‖z‖ ^ n :=
          mul_le_mul_of_nonneg_right (norm_liPairTerm_xiZeroSeq_le k n) (by positivity)
      _ = (‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹ * ((n : ℝ) ^ 2 * (‖z‖ * liMinRadius⁻¹) ^ n) := by
          rw [mul_pow]; ring
  have hcomm : (∑' k : ℕ, ∑' n : ℕ, liPairTerm (xiZeroSeq k) n * z ^ n) =
      ∑' n : ℕ, ∑' k : ℕ, liPairTerm (xiZeroSeq k) n * z ^ n := by
    rw [← hsum_prod.tsum_prod]
    have hswap := (Equiv.prodComm ℕ ℕ).tsum_eq
      (fun p : ℕ × ℕ => liPairTerm (xiZeroSeq p.1) p.2 * z ^ p.2)
    rw [← hswap]
    exact hsum_prod.prod_symm.tsum_prod
  have hsum_outer : Summable (fun n : ℕ => (liCoeff n : ℂ) * z ^ n) := by
    set C : ℝ := ∑' k : ℕ, (‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹
    refine Summable.of_norm_bounded (g := fun n : ℕ => ((1 / 2 : ℝ) * C) *
        ((n : ℝ) ^ 2 * (‖z‖ * liMinRadius⁻¹) ^ n)) (hsum_n.mul_left _) fun n => ?_
    rw [liCoeff_ofReal_eq_tsum n, norm_mul, norm_mul, norm_pow]
    have hhalf_norm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf_norm]
    have htsum_norm : ‖∑' k : ℕ, liPairTerm (xiZeroSeq k) n‖ ≤
        (n : ℝ) ^ 2 * liMinRadius⁻¹ ^ n * C := by
      calc ‖∑' k : ℕ, liPairTerm (xiZeroSeq k) n‖
          ≤ ∑' k : ℕ, ‖liPairTerm (xiZeroSeq k) n‖ :=
            norm_tsum_le_tsum_norm (summable_liPairTerm n).norm
        _ ≤ ∑' k : ℕ, ((n : ℝ) ^ 2 * liMinRadius⁻¹ ^ n) * (‖xiZeroSeq k‖ * ‖1 - xiZeroSeq k‖)⁻¹ :=
            (summable_liPairTerm n).norm.tsum_le_tsum (fun k => norm_liPairTerm_xiZeroSeq_le k n)
              (summable_inv_mul_one_sub.mul_left _)
        _ = (n : ℝ) ^ 2 * liMinRadius⁻¹ ^ n * C := by rw [tsum_mul_left]
    calc (1 / 2 : ℝ) * ‖∑' k : ℕ, liPairTerm (xiZeroSeq k) n‖ * ‖z‖ ^ n
        ≤ (1 / 2 : ℝ) * ((n : ℝ) ^ 2 * liMinRadius⁻¹ ^ n * C) * ‖z‖ ^ n := by gcongr
      _ = (1 / 2 : ℝ) * C * ((n : ℝ) ^ 2 * (‖z‖ * liMinRadius⁻¹) ^ n) := by rw [mul_pow]; ring
  have hsum_val : ∑' n : ℕ, (liCoeff n : ℂ) * z ^ n = liGenFun z := by
    calc ∑' n : ℕ, (liCoeff n : ℂ) * z ^ n
        = ∑' n : ℕ, (1 / 2 : ℂ) * ((∑' k : ℕ, liPairTerm (xiZeroSeq k) n) * z ^ n) := by
          refine tsum_congr fun n => ?_; rw [liCoeff_ofReal_eq_tsum n]; ring
      _ = (1 / 2 : ℂ) * ∑' n : ℕ, ∑' k : ℕ, liPairTerm (xiZeroSeq k) n * z ^ n := by
          rw [tsum_mul_left]
          congr 1; exact tsum_congr fun n => (tsum_mul_right).symm
      _ = (1 / 2 : ℂ) * ∑' k : ℕ, ∑' n : ℕ, liPairTerm (xiZeroSeq k) n * z ^ n := by
          rw [hcomm.symm]
      _ = (1 / 2 : ℂ) * ∑' k : ℕ,
            (z * ((1 / (1 - z) - 1 / (cayley (xiZeroSeq k) - z)) +
                  (1 / (1 - z) - 1 / (cayley (1 - xiZeroSeq k) - z)))) := by
          congr 1; exact tsum_congr fun k => (hasSum_liPairTerm_mul_pow k hz).tsum_eq
      _ = z * ((1 / 2 : ℂ) * ∑' k : ℕ,
            ((1 / (1 - z) - 1 / (cayley (xiZeroSeq k) - z)) +
             (1 / (1 - z) - 1 / (cayley (1 - xiZeroSeq k) - z)))) := by
          rw [tsum_mul_left]; ring
      _ = liGenFun z := by
          rw [← logDeriv_xiCayley_eq_paired_tsum hz, liGenFun]
  exact hsum_val ▸ hsum_outer.hasSum

theorem liGenFun_eq_tsum {z : ℂ} (hz : ‖z‖ < liMinRadius) :
    liGenFun z = ∑' n : ℕ, (liCoeff n : ℂ) * z ^ n :=
  (liCoeff_eq_taylor_logDeriv_cayley hz).tsum_eq.symm

/-! ### Termwise Iterated Differentiation of Complex Power Series -/

/-- Helper: `n ↦ (descFactorial (m + n) m : ℝ) * q ^ n` is summable for `0 ≤ q < 1`. -/
private lemma summable_descFactorial_mul_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    Summable (fun n : ℕ => (Nat.descFactorial (m + n) m : ℝ) * q ^ n) := by
  have hle : ∀ n : ℕ, (Nat.descFactorial (m + n) m : ℝ) ≤ ((m + n : ℕ) : ℝ) ^ m := fun n => by
    exact_mod_cast Nat.descFactorial_le_pow (m + n) m
  let r : ℝ := (q + 1) / 2
  have hr0 : 0 < r := by dsimp only [r]; linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hqr : q / r < 1 := (div_lt_one hr0).mpr (by dsimp only [r]; linarith)
  have htend : Tendsto (fun n : ℕ => ((m + n : ℕ) : ℝ) ^ m * (q / r) ^ n) atTop (𝓝 0) := by
    by_cases hq : q = 0
    · subst hq
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      simp [zero_div, zero_pow hn]
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      have hratio_gt : 1 < (q / r)⁻¹ := (one_lt_inv₀ (div_pos hqpos hr0)).mpr hqr
      have ht := (tendsto_pow_const_div_const_pow_of_one_lt m hratio_gt).comp (tendsto_add_atTop_nat m)
      have ht' := ht.mul_const (((q / r)⁻¹) ^ m)
      rw [zero_mul] at ht'
      refine ht'.congr fun n => ?_
      simp only [Function.comp_apply, add_comm n m]
      rw [inv_pow, inv_pow, div_inv_eq_mul, pow_add]
      have hqr_ne : (q / r) ^ m ≠ 0 := pow_ne_zero m (div_pos hqpos hr0).ne'
      field_simp [hqr_ne]
  have hev : ∀ᶠ n : ℕ in atTop, ‖(Nat.descFactorial (m + n) m : ℝ) * q ^ n‖ ≤ r ^ n := by
    refine (htend.eventually (Iio_mem_nhds zero_lt_one)).mono fun n hn => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have hrn : 0 < r ^ n := pow_pos hr0 n
    have h1 : ((m + n : ℕ) : ℝ) ^ m * q ^ n ≤ r ^ n := by
      have h2 : ((m + n : ℕ) : ℝ) ^ m * q ^ n / r ^ n < 1 := by
        simpa [div_pow, mul_div_assoc] using hn
      exact ((div_lt_one hrn).mp h2).le
    exact le_trans (mul_le_mul_of_nonneg_right (hle n) (pow_nonneg hq0 n)) h1
  exact Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one hr0.le hr1)
    (Nat.cofinite_eq_atTop.symm ▸ hev)

/-- **Termwise Iterated Derivative of a Complex Power Series** on its open disk of convergence:
if `HasSum (fun n => c n * z ^ n) (f z)` for all `z` with `‖z‖ < R`, then for every `m : ℕ`
and `z` with `‖z‖ < R`,
`iteratedDeriv m f z = ∑' k : ℕ, (Nat.descFactorial (m + k) m : ℂ) * c (m + k) * z ^ k`. -/
theorem iteratedDeriv_powerSeries_eq_tsum {c : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n : ℕ => c n * z ^ n) (f z)) :
    ∀ (m : ℕ) (z : ℂ), ‖z‖ < R →
      iteratedDeriv m f z =
        ∑' k : ℕ, (Nat.descFactorial (m + k) m : ℂ) * c (m + k) * z ^ k := by
  intro m
  induction m with
  | zero =>
    intro z hz
    simp only [iteratedDeriv_zero, zero_add, Nat.descFactorial_zero, Nat.cast_one, one_mul]
    exact (hf z hz).tsum_eq.symm
  | succ m ih =>
    intro z hz
    let r₂ : ℝ := (‖z‖ + R) / 2
    let r₁ : ℝ := (‖z‖ + r₂) / 2
    have hzr₁ : ‖z‖ < r₁ := by dsimp only [r₁, r₂]; linarith
    have hr₁r₂ : r₁ < r₂ := by dsimp only [r₁, r₂]; linarith
    have hr₂R : r₂ < R := by dsimp only [r₂]; linarith
    have hr₂_pos : 0 < r₂ := by dsimp only [r₂]; linarith [norm_nonneg z]
    have hr₁_pos : 0 < r₁ := by dsimp only [r₁, r₂]; linarith [norm_nonneg z]
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r₁ := by
      simpa [Metric.mem_ball, dist_zero_right] using hzr₁
    have hsum_r₂ : Summable (fun n : ℕ => c n * (r₂ : ℂ) ^ n) :=
      (hf (r₂ : ℂ) (by simpa [Complex.norm_real, abs_of_pos hr₂_pos] using hr₂R)).summable
    have hbd_tend : Tendsto (fun n : ℕ => ‖c n * (r₂ : ℂ) ^ n‖) atTop (𝓝 0) := by
      simpa using hsum_r₂.tendsto_atTop_zero.norm
    obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖c n‖ * r₂ ^ n ≤ M := by
      have hev : ∀ᶠ n : ℕ in atTop, ‖c n * (r₂ : ℂ) ^ n‖ ≤ 1 :=
        hbd_tend.eventually (Iic_mem_nhds zero_lt_one)
      rw [Filter.eventually_atTop] at hev
      obtain ⟨N, hN⟩ := hev
      let S : Finset ℝ := insert 1 ((Finset.range N).image fun n => ‖c n‖ * r₂ ^ n)
      refine ⟨S.max' (Finset.insert_nonempty _ _),
        le_trans zero_le_one (Finset.le_max' S 1 (Finset.mem_insert_self _ _)), fun n => ?_⟩
      by_cases hn : n < N
      · exact Finset.le_max' S _ (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hn)))
      · have h1 := hN n (not_lt.mp hn)
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr₂_pos.le] at h1
        exact le_trans h1 (Finset.le_max' S 1 (Finset.mem_insert_self _ _))
    let g : ℕ → ℂ → ℂ := fun k w => (Nat.descFactorial (m + k) m : ℂ) * c (m + k) * w ^ k
    let g' : ℕ → ℂ → ℂ := fun k w =>
      if k = 0 then 0 else (Nat.descFactorial (m + k) m : ℂ) * c (m + k) * ((k : ℂ) * w ^ (k - 1))
    have hderiv_g : ∀ k : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) r₁, HasDerivAt (g k) (g' k w) w := by
      intro k w _
      by_cases hk : k = 0
      · subst hk; simp [g, g', hasDerivAt_const]
      · simp only [g, g', hk, ↓reduceIte]
        exact (hasDerivAt_pow k w).const_mul _
    have hq0 : 0 ≤ r₁ / r₂ := div_nonneg hr₁_pos.le hr₂_pos.le
    have hq1 : r₁ / r₂ < 1 := (div_lt_one hr₂_pos).mpr hr₁r₂
    let u : ℕ → ℝ := fun k =>
      if k = 0 then 0
      else (M / r₂ ^ (m + 1)) * ((Nat.descFactorial (m + 1 + (k - 1)) (m + 1) : ℝ) * (r₁ / r₂) ^ (k - 1))
    have hu_sum : Summable u := by
      have hs := (summable_descFactorial_mul_pow hq0 hq1 (m + 1)).mul_left (M / r₂ ^ (m + 1))
      rw [← summable_nat_add_iff 1]
      refine hs.congr fun j => ?_
      simp [u]
    have hg'_bound : ∀ k : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) r₁, ‖g' k w‖ ≤ u k := by
      intro k w hw
      have hw_lt : ‖w‖ < r₁ := by simpa [Metric.mem_ball, dist_zero_right] using hw
      by_cases hk : k = 0
      · simp [g', u, hk]
      · simp only [g', u, hk, ↓reduceIte]
        have hdesc : (Nat.descFactorial (m + k) m : ℝ) * (k : ℝ) =
            (Nat.descFactorial (m + 1 + (k - 1)) (m + 1) : ℝ) := by
          have hnat : Nat.descFactorial (m + k) m * k = Nat.descFactorial (m + 1 + (k - 1)) (m + 1) := by
            have harg : m + k = m + 1 + (k - 1) := by omega
            rw [harg, Nat.descFactorial_succ]
            have hsub : m + 1 + (k - 1) - m = k := by omega
            rw [hsub, mul_comm]
          exact_mod_cast hnat
        rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
        have hcn : ‖c (m + k)‖ ≤ M / r₂ ^ (m + k) :=
          (le_div_iff₀ (pow_pos hr₂_pos (m + k))).mpr (hM (m + k))
        have hpow_le : ‖w‖ ^ (k - 1) ≤ r₁ ^ (k - 1) :=
          pow_le_pow_left₀ (norm_nonneg w) hw_lt.le (k - 1)
        have hmk : m + k = (m + 1) + (k - 1) := by omega
        calc (Nat.descFactorial (m + k) m : ℝ) * ‖c (m + k)‖ * ((k : ℝ) * ‖w‖ ^ (k - 1))
            ≤ (Nat.descFactorial (m + k) m : ℝ) * (M / r₂ ^ (m + k)) * ((k : ℝ) * r₁ ^ (k - 1)) := by
              have hnon1 : 0 ≤ (Nat.descFactorial (m + k) m : ℝ) * (M / r₂ ^ (m + k)) := by positivity
              gcongr
          _ = (M / r₂ ^ (m + 1)) * (((Nat.descFactorial (m + k) m : ℝ) * (k : ℝ)) * (r₁ / r₂) ^ (k - 1)) := by
              rw [hmk, pow_add, div_pow r₁ r₂]
              have hr2m : r₂ ^ (m + 1) ≠ 0 := (pow_pos hr₂_pos _).ne'
              have hr2k : r₂ ^ (k - 1) ≠ 0 := (pow_pos hr₂_pos _).ne'
              have halg : ∀ a x y z w : ℝ, y ≠ 0 → z ≠ 0 →
                  a * (x / (y * z)) * ((k : ℝ) * w) = x / y * ((a * (k : ℝ)) * (w / z)) :=
                fun a x y z w hy hz => by field_simp [hy, hz]
              exact halg _ M (r₂ ^ (m + 1)) (r₂ ^ (k - 1)) (r₁ ^ (k - 1)) hr2m hr2k
          _ = (M / r₂ ^ (m + 1)) *
                ((Nat.descFactorial (m + 1 + (k - 1)) (m + 1) : ℝ) * (r₁ / r₂) ^ (k - 1)) := by
              rw [hdesc]
    have hg0_sum : Summable (fun k : ℕ => g k 0) := by
      refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
      have hk0 : k ≠ 0 := by simpa using hk
      simp [g, zero_pow hk0]
    have hderiv_tsum : HasDerivAt (fun w : ℂ => ∑' k : ℕ, g k w) (∑' k : ℕ, g' k z) z :=
      hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball
        (convex_ball (0 : ℂ) r₁).isPreconnected hderiv_g hg'_bound
        (Metric.mem_ball_self hr₁_pos) hg0_sum hz_ball
    have hev_eq : iteratedDeriv m f =ᶠ[𝓝 z] fun w => ∑' k : ℕ, g k w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz_ball] with w hw
      have hwR : ‖w‖ < R := lt_trans (by simpa [Metric.mem_ball, dist_zero_right] using hw)
        (lt_trans hr₁r₂ hr₂R)
      exact ih w hwR
    rw [iteratedDeriv_succ, hev_eq.deriv_eq, hderiv_tsum.deriv]
    have hsum_g' : Summable (fun k : ℕ => g' k z) :=
      Summable.of_norm_bounded hu_sum fun k => hg'_bound k z hz_ball
    rw [hsum_g'.tsum_eq_zero_add]
    simp only [g', ↓reduceIte, zero_add]
    refine tsum_congr fun k => ?_
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    have hnat : Nat.descFactorial (m + (k + 1)) m * (k + 1) =
        Nat.descFactorial (m + 1 + k) (m + 1) := by
      have harg : m + (k + 1) = m + 1 + k := by omega
      rw [harg, Nat.descFactorial_succ]
      have hsub : m + 1 + k - m = k + 1 := by omega
      rw [hsub, mul_comm]
    have hcast : (Nat.descFactorial (m + (k + 1)) m : ℂ) * ((k + 1 : ℕ) : ℂ) =
        (Nat.descFactorial (m + 1 + k) (m + 1) : ℂ) := by
      exact_mod_cast hnat
    have harg : m + (k + 1) = m + 1 + k := by omega
    rw [harg]
    push_cast at hcast ⊢
    calc (Nat.descFactorial (m + 1 + k) m : ℂ) * c (m + 1 + k) * (((k : ℂ) + 1) * z ^ k)
        = ((Nat.descFactorial (m + (k + 1)) m : ℂ) * ((k : ℂ) + 1)) * c (m + 1 + k) * z ^ k := by
          rw [harg]; ring
      _ = (Nat.descFactorial (m + 1 + k) (m + 1) : ℂ) * c (m + 1 + k) * z ^ k := by
          rw [hcast]

/-- Exact Taylor-derivative representation of `liCoeff n` at `z = 0`:
`iteratedDeriv n liGenFun 0 = (n! : ℂ) * (liCoeff n : ℂ)`. -/
theorem iteratedDeriv_liGenFun_zero (n : ℕ) :
    iteratedDeriv n liGenFun 0 = (Nat.factorial n : ℂ) * (liCoeff n : ℂ) := by
  have h := iteratedDeriv_powerSeries_eq_tsum (R := liMinRadius)
    (fun z hz => liCoeff_eq_taylor_logDeriv_cayley hz) n 0 (by simpa using liMinRadius_pos)
  rw [h, tsum_eq_single 0]
  · simp [Nat.descFactorial_self]
  · intro k hk; simp [zero_pow hk]

/-- Exact real Taylor-derivative formula `liCoeff n = (n! : ℝ)⁻¹ * (iteratedDeriv n liGenFun 0).re`. -/
theorem liCoeff_eq_iteratedDeriv_genFun (n : ℕ) :
    liCoeff n = (Nat.factorial n : ℝ)⁻¹ * (iteratedDeriv n liGenFun 0).re := by
  rw [iteratedDeriv_liGenFun_zero n]
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  field_simp [hfac]

/-- Helper: extracting scalar Taylor series `HasSum (fun j => (j!)⁻¹ * iteratedDeriv j f x₀ * u^j) (f (x₀ + u))`
from any `HasFPowerSeriesOnBall f p x₀ r` with `ENNReal.ofReal R < r`. -/
private lemma hasSum_taylor_of_hasFPowerSeriesOnBall {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {x₀ : ℂ} {r : ENNReal} (hr : HasFPowerSeriesOnBall f p x₀ r)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt : ENNReal.ofReal R < r) :
    ∀ u : ℂ, ‖u‖ < R →
      HasSum (fun j : ℕ => ((Nat.factorial j : ℂ)⁻¹ * iteratedDeriv j f x₀) * u ^ j) (f (x₀ + u)) := by
  let c : ℕ → ℂ := fun j => p j (fun _ => 1)
  have hraw : ∀ u : ℂ, ‖u‖ < R → HasSum (fun j : ℕ => c j * u ^ j) (f (x₀ + u)) := by
    intro u hu
    have hu_eb : u ∈ Metric.eball (0 : ℂ) r := by
      simp only [Metric.mem_eball, edist_dist, dist_zero_right]
      exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff hR_pos).mpr hu) hR_lt
    refine (hr.hasSum hu_eb).congr_fun fun j => ?_
    have h1 := (p j).map_smul_univ (fun _ : Fin j => u) (fun _ : Fin j => (1 : ℂ))
    simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    change c j * u ^ j = (p j) (fun _ => u)
    rw [h1, mul_comm]
  have hcoeff : ∀ j : ℕ, c j = (Nat.factorial j : ℂ)⁻¹ * iteratedDeriv j f x₀ := by
    intro j
    have hd := iteratedDeriv_powerSeries_eq_tsum (R := R) hraw j 0 (by simpa using hR_pos)
    rw [tsum_eq_single 0] at hd
    · simp only [add_zero, Nat.descFactorial_self, pow_zero, mul_one] at hd
      have hshift : iteratedDeriv j (fun u : ℂ => f (x₀ + u)) 0 = iteratedDeriv j f x₀ := by
        simpa [add_zero] using congrFun (iteratedDeriv_comp_const_add j f x₀) (0 : ℂ)
      rw [hshift] at hd
      have hfac : (Nat.factorial j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      rw [hd]
      field_simp [hfac]
    · intro k hk; simp [zero_pow hk]
  intro u hu
  exact (hraw u hu).congr_fun fun j => by rw [hcoeff j]

/-! ### Keiper–Li Analytic Formula `((n - 1)!)⁻¹ * Re((d/ds)^n [s^{n - 1} log ξ(s)] |_{s = 1})` -/

/-- The classical Keiper–Li analytic definition of the `n`-th Li coefficient:
`liCoeffAnalytic n = ((n - 1)! : ℝ)⁻¹ * Re((d/ds)^n [s^(n - 1) * log (xi s)] |_{s = 1})`. -/
def liCoeffAnalytic (n : ℕ) : ℝ :=
  (Nat.factorial (n - 1) : ℝ)⁻¹ *
    (iteratedDeriv n (fun s : ℂ => s ^ (n - 1) * Complex.log (xi s)) 1).re

private lemma iteratedDeriv_pow_eq (j m : ℕ) (s : ℂ) :
    iteratedDeriv j (fun w : ℂ => w ^ m) s = (Nat.descFactorial m j : ℂ) * s ^ (m - j) := by
  induction j generalizing s with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv j (fun w : ℂ => w ^ m) =
        fun w : ℂ => (Nat.descFactorial m j : ℂ) * w ^ (m - j) := funext ih
    rw [hfun]
    have hd : HasDerivAt (fun w : ℂ => (Nat.descFactorial m j : ℂ) * w ^ (m - j))
        ((Nat.descFactorial m j : ℂ) * ((m - j : ℕ) : ℂ) * s ^ (m - j - 1)) s := by
      simpa [mul_assoc] using (hasDerivAt_pow (m - j) s).const_mul (Nat.descFactorial m j : ℂ)
    rw [hd.deriv, Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

private lemma iteratedDeriv_inv_one_sub_pow (m p : ℕ) {z : ℂ} (hz : z ≠ 1) :
    iteratedDeriv m (fun w : ℂ => ((1 - w) ^ p)⁻¹) z =
      (Nat.ascFactorial p m : ℂ) * ((1 - z) ^ (p + m))⁻¹ := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (fun w : ℂ => ((1 - w) ^ p)⁻¹) =ᶠ[𝓝 z]
        fun w : ℂ => (Nat.ascFactorial p m : ℂ) * ((1 - w) ^ (p + m))⁻¹ := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw using ih hw
    rw [hev.deriv_eq]
    have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
    have hsub : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
    have hpow : HasDerivAt (fun w : ℂ => (1 - w) ^ (p + m))
        (((p + m : ℕ) : ℂ) * (1 - z) ^ (p + m - 1) * (-1)) z :=
      (hasDerivAt_pow (p + m) (1 - z)).comp z hsub
    have hinv : HasDerivAt (fun w : ℂ => ((1 - w) ^ (p + m))⁻¹)
        (((p + m : ℕ) : ℂ) * ((1 - z) ^ (p + m + 1))⁻¹) z := by
      refine (hpow.inv (pow_ne_zero _ h1z)).congr_deriv ?_
      by_cases hpm : p + m = 0
      · simp [hpm]
      · have hpm1 : p + m - 1 + 1 = p + m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hpm)
        have h1 : (1 - z) ^ (p + m + 1) = (1 - z) ^ (p + m) * (1 - z) := pow_succ _ _
        have h2 : (1 - z) ^ (p + m) = (1 - z) ^ (p + m - 1) * (1 - z) := by
          rw [← pow_succ, hpm1]
        have hp1 : (1 - z) ^ (p + m) ≠ 0 := pow_ne_zero _ h1z
        have hp2 : (1 - z) ^ (p + m - 1) ≠ 0 := pow_ne_zero _ h1z
        field_simp [h1z, hp1, hp2]
        rw [h1, h2]
        ring
    have hmul := hinv.const_mul (Nat.ascFactorial p m : ℂ)
    rw [hmul.deriv, Nat.ascFactorial_succ]
    push_cast
    rw [add_assoc]
    ring

/-- **Exact Agreement of Paired Zero-Sum `liCoeff n` with Keiper–Li's Analytic Formula `liCoeffAnalytic n`**
for every `n ≥ 1`. -/
theorem liCoeff_eq_liCoeffAnalytic {n : ℕ} (hn : 1 ≤ n) :
    liCoeff n = liCoeffAnalytic n := by
  let F : ℂ → ℂ := fun s => Complex.log (xi s)
  let H : ℂ → ℂ := fun s => logDeriv xi s
  have hxi1_slit : xi 1 ∈ Complex.slitPlane := by
    rw [xi_one]; exact Or.inl zero_lt_one
  have hU_nhds : xi ⁻¹' Complex.slitPlane ∈ 𝓝 (1 : ℂ) :=
    continuous_xi.continuousAt.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hxi1_slit)
  have hF_deriv_ev : ∀ᶠ s in 𝓝 (1 : ℂ), HasDerivAt F (H s) s := by
    filter_upwards [hU_nhds] with s hs
    have hd : HasDerivAt (fun w => Complex.log (xi w)) (deriv xi s / xi s) s :=
      (differentiable_xi s).hasDerivAt.clog hs
    simpa [F, H, logDeriv_apply] using hd
  have hF_an : AnalyticAt ℂ F 1 := by
    have hdiff_on : DifferentiableOn ℂ F (xi ⁻¹' Complex.slitPlane) := fun s hs =>
      ((differentiable_xi s).hasDerivAt.clog hs).differentiableAt.differentiableWithinAt
    exact hdiff_on.analyticAt hU_nhds
  have hH_an : AnalyticAt ℂ H 1 := by
    have hne : xi 1 ≠ 0 := by simp
    have hne_nhds : {s : ℂ | xi s ≠ 0} ∈ 𝓝 (1 : ℂ) :=
      continuous_xi.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hne)
    have hdiff_on : DifferentiableOn ℂ H {s : ℂ | xi s ≠ 0} := fun s hs => by
      have hd1 : DifferentiableAt ℂ (deriv xi) s :=
        ((differentiable_xi.analyticAt s).deriv).differentiableAt
      exact (hd1.div (differentiable_xi s) hs).differentiableWithinAt
    exact hdiff_on.analyticAt hne_nhds
  have hiter_F_eq_H : ∀ j : ℕ, iteratedDeriv (j + 1) F 1 = iteratedDeriv j H 1 := fun j => by
    rw [iteratedDeriv_succ']
    have hev : deriv F =ᶠ[𝓝 (1 : ℂ)] H := hF_deriv_ev.mono fun s hs => hs.deriv
    exact hev.iteratedDeriv_eq j
  -- Step 1: Evaluate `((n - 1)!)⁻¹ * iteratedDeriv n (fun s => s^(n - 1) * F s) 1` via Leibniz rule
  have hLHS_complex :
      ((Nat.factorial (n - 1) : ℂ)⁻¹) * iteratedDeriv n (fun s : ℂ => s ^ (n - 1) * F s) 1 =
        ∑ j ∈ Finset.range n,
          (Nat.choose n (j + 1) : ℂ) * ((Nat.factorial j : ℂ)⁻¹) * iteratedDeriv j H 1 := by
    have hpow_cd : ContDiffAt ℂ n (fun s : ℂ => s ^ (n - 1)) 1 :=
      (contDiff_id.pow (n - 1)).contDiffAt
    have hF_cd : ContDiffAt ℂ n F 1 := hF_an.contDiffAt
    have hcomm_fun : (fun s : ℂ => s ^ (n - 1) * F s) = F * (fun s : ℂ => s ^ (n - 1)) :=
      funext fun s => mul_comm _ _
    rw [hcomm_fun, iteratedDeriv_mul hF_cd hpow_cd, Finset.sum_range_succ']
    have hzero_term : (Nat.choose n 0 : ℂ) * iteratedDeriv 0 F 1 *
        iteratedDeriv (n - 0) (fun s : ℂ => s ^ (n - 1)) 1 = 0 := by
      rw [Nat.sub_zero, iteratedDeriv_pow_eq]
      have hdesc0 : Nat.descFactorial (n - 1) n = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [hdesc0]
    rw [hzero_term, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < n := Finset.mem_range.mp hj
    rw [iteratedDeriv_pow_eq, one_pow, mul_one, hiter_F_eq_H j]
    have hfac_rel : (Nat.descFactorial (n - 1) (n - (j + 1)) : ℕ) * Nat.factorial j =
        Nat.factorial (n - 1) := by
      have hle : n - (j + 1) ≤ n - 1 := by omega
      have h := Nat.factorial_mul_descFactorial hle
      have hsub : n - 1 - (n - (j + 1)) = j := by omega
      rw [hsub, mul_comm] at h
      exact h
    have hfac_cast : (Nat.descFactorial (n - 1) (n - (j + 1)) : ℂ) * (Nat.factorial j : ℂ) =
        (Nat.factorial (n - 1) : ℂ) := by exact_mod_cast hfac_rel
    have hf1 : (Nat.factorial (n - 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf2 : (Nat.factorial j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hdiv : ((Nat.factorial (n - 1) : ℂ)⁻¹) * (Nat.descFactorial (n - 1) (n - (j + 1)) : ℂ) =
        (Nat.factorial j : ℂ)⁻¹ := by
      field_simp [hf1, hf2]
      exact hfac_cast
    calc (Nat.factorial (n - 1) : ℂ)⁻¹ *
          ((Nat.choose n (j + 1) : ℂ) * iteratedDeriv j H 1 *
            (Nat.descFactorial (n - 1) (n - (j + 1)) : ℂ))
        = (Nat.choose n (j + 1) : ℂ) *
            ((Nat.factorial (n - 1) : ℂ)⁻¹ * (Nat.descFactorial (n - 1) (n - (j + 1)) : ℂ)) *
            iteratedDeriv j H 1 := by ring
      _ = (Nat.choose n (j + 1) : ℂ) * (Nat.factorial j : ℂ)⁻¹ * iteratedDeriv j H 1 := by
          rw [hdiv]
  -- Step 2: Local Taylor expansion of `H` at `1`
  obtain ⟨rH, hrH_pos, hH_ps⟩ :
      ∃ rH : ℝ, 0 < rH ∧ ∀ u : ℂ, ‖u‖ < rH →
        HasSum (fun j : ℕ => ((Nat.factorial j : ℂ)⁻¹ * iteratedDeriv j H 1) * u ^ j) (H (1 + u)) := by
    obtain ⟨p, r, hr⟩ := hH_an
    have hr_pos : (0 : ENNReal) < r := hr.r_pos
    obtain ⟨r₀, hr₀_pos, hr₀_lt⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ ENNReal.ofReal r₀ < r := by
      rcases eq_or_ne r ⊤ with rfl | hr_top
      · exact ⟨1, zero_lt_one, ENNReal.ofReal_lt_top⟩
      · have hr_pos' : 0 < r.toReal := ENNReal.toReal_pos hr_pos.ne' hr_top
        refine ⟨r.toReal / 2, half_pos hr_pos', ?_⟩
        calc ENNReal.ofReal (r.toReal / 2)
            < ENNReal.ofReal r.toReal := (ENNReal.ofReal_lt_ofReal_iff hr_pos').mpr (half_lt_self hr_pos')
          _ = r := ENNReal.ofReal_toReal hr_top
    exact ⟨r₀, hr₀_pos, hasSum_taylor_of_hasFPowerSeriesOnBall hr hr₀_pos hr₀_lt⟩
  let b : ℕ → ℂ := fun j => (Nat.factorial j : ℂ)⁻¹ * iteratedDeriv j H 1
  let Rem : ℂ → ℂ := fun u => ∑' k : ℕ, b (n + k) * u ^ k
  have hRem_diff : DifferentiableOn ℂ Rem (Metric.ball (0 : ℂ) (rH / 2)) := by
    let r₁ : ℝ := rH / 2
    let r₂ : ℝ := (3 / 4 : ℝ) * rH
    have hr₁_pos : 0 < r₁ := by dsimp only [r₁]; linarith
    have hr₂_pos : 0 < r₂ := by dsimp only [r₂]; linarith
    have hr₁r₂ : r₁ < r₂ := by dsimp only [r₁, r₂]; linarith
    have hr₂rH : r₂ < rH := by dsimp only [r₂]; linarith
    have hsum_r₂ : Summable (fun j : ℕ => b j * (r₂ : ℂ) ^ j) :=
      (hH_ps (r₂ : ℂ) (by simpa [Complex.norm_real, abs_of_pos hr₂_pos] using hr₂rH)).summable
    have hbd_tend : Tendsto (fun j : ℕ => ‖b j * (r₂ : ℂ) ^ j‖) atTop (𝓝 0) := by
      simpa using hsum_r₂.tendsto_atTop_zero.norm
    obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, ‖b j‖ * r₂ ^ j ≤ M := by
      have hev : ∀ᶠ j : ℕ in atTop, ‖b j * (r₂ : ℂ) ^ j‖ ≤ 1 :=
        hbd_tend.eventually (Iic_mem_nhds zero_lt_one)
      rw [Filter.eventually_atTop] at hev
      obtain ⟨N, hN⟩ := hev
      let S : Finset ℝ := insert 1 ((Finset.range N).image fun j => ‖b j‖ * r₂ ^ j)
      refine ⟨S.max' (Finset.insert_nonempty _ _),
        le_trans zero_le_one (Finset.le_max' S 1 (Finset.mem_insert_self _ _)), fun j => ?_⟩
      by_cases hj : j < N
      · exact Finset.le_max' S _ (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hj)))
      · have h1 := hN j (not_lt.mp hj)
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr₂_pos.le] at h1
        exact le_trans h1 (Finset.le_max' S 1 (Finset.mem_insert_self _ _))
    intro u hu
    have hq0 : 0 ≤ r₁ / r₂ := div_nonneg hr₁_pos.le hr₂_pos.le
    have hq1 : r₁ / r₂ < 1 := (div_lt_one hr₂_pos).mpr hr₁r₂
    let ubound : ℕ → ℝ := fun k =>
      if k = 0 then 0 else (M / r₂ ^ (n + 1)) * ((k : ℝ) * (r₁ / r₂) ^ (k - 1))
    have hub_sum : Summable ubound := by
      have hs := (summable_descFactorial_mul_pow hq0 hq1 1).mul_left (M / r₂ ^ (n + 1))
      rw [← summable_nat_add_iff 1]
      refine hs.congr fun j => ?_
      simp [ubound, add_comm]
    have hderiv_each : ∀ k : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) r₁,
        HasDerivAt (fun x : ℂ => b (n + k) * x ^ k)
          (if k = 0 then 0 else b (n + k) * ((k : ℂ) * w ^ (k - 1))) w := fun k w _ => by
      by_cases hk : k = 0
      · subst hk; simp [hasDerivAt_const]
      · simp only [hk, ↓reduceIte]; exact (hasDerivAt_pow k w).const_mul _
    have hbound_each : ∀ k : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) r₁,
        ‖(if k = 0 then (0 : ℂ) else b (n + k) * ((k : ℂ) * w ^ (k - 1)))‖ ≤ ubound k := by
      intro k w hw
      have hw_lt : ‖w‖ < r₁ := by simpa [Metric.mem_ball, dist_zero_right] using hw
      by_cases hk : k = 0
      · simp [ubound, hk]
      · simp only [ubound, hk, ↓reduceIte, norm_mul, norm_pow, Complex.norm_natCast]
        have hbn : ‖b (n + k)‖ ≤ M / r₂ ^ (n + k) :=
          (le_div_iff₀ (pow_pos hr₂_pos (n + k))).mpr (hM (n + k))
        have hnk : n + k = (n + 1) + (k - 1) := by omega
        calc ‖b (n + k)‖ * ((k : ℝ) * ‖w‖ ^ (k - 1))
            ≤ (M / r₂ ^ (n + k)) * ((k : ℝ) * r₁ ^ (k - 1)) := by
              have hnon : 0 ≤ M / r₂ ^ (n + k) := by positivity
              gcongr
          _ = (M / r₂ ^ (n + 1)) * ((k : ℝ) * (r₁ / r₂) ^ (k - 1)) := by
              rw [hnk, pow_add, div_pow r₁ r₂]
              have hr2n : r₂ ^ (n + 1) ≠ 0 := (pow_pos hr₂_pos _).ne'
              have hr2k : r₂ ^ (k - 1) ≠ 0 := (pow_pos hr₂_pos _).ne'
              have halg : ∀ x y z w : ℝ, y ≠ 0 → z ≠ 0 →
                  x / (y * z) * ((k : ℝ) * w) = x / y * ((k : ℝ) * (w / z)) :=
                fun x y z w hy hz => by field_simp [hy, hz]
              exact halg M (r₂ ^ (n + 1)) (r₂ ^ (k - 1)) (r₁ ^ (k - 1)) hr2n hr2k
    have h0_sum : Summable (fun k : ℕ => b (n + k) * (0 : ℂ) ^ k) := by
      refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
      simp [zero_pow (by simpa using hk : k ≠ 0)]
    exact (hasDerivAt_tsum_of_isPreconnected hub_sum Metric.isOpen_ball
      (convex_ball (0 : ℂ) r₁).isPreconnected hderiv_each hbound_each
      (Metric.mem_ball_self hr₁_pos) h0_sum hu).differentiableAt.differentiableWithinAt
  have hRem_an : AnalyticAt ℂ Rem 0 :=
    hRem_diff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hrH_pos)))
  have hH_split : ∀ u : ℂ, ‖u‖ < rH →
      H (1 + u) = (∑ j ∈ Finset.range n, b j * u ^ j) + u ^ n * Rem u := by
    intro u hu
    have hhas := hH_ps u hu
    have htail : HasSum (fun k : ℕ => b (k + n) * u ^ (k + n))
        (H (1 + u) - ∑ j ∈ Finset.range n, b j * u ^ j) :=
      (hasSum_nat_add_iff' n).mpr hhas
    have htail' : HasSum (fun k : ℕ => b (n + k) * u ^ (n + k))
        (H (1 + u) - ∑ j ∈ Finset.range n, b j * u ^ j) :=
      htail.congr_fun fun k => by rw [add_comm n k]
    have htail2 : ∑' k : ℕ, b (n + k) * u ^ (n + k) = u ^ n * Rem u := by
      dsimp only [Rem]
      rw [← tsum_mul_left]
      exact tsum_congr fun k => by rw [pow_add]; ring
    linear_combination htail2 - htail'.tsum_eq
  -- Step 3: Local decomposition of `liGenFun` near `0`
  let Q : ℂ → ℂ := fun z => ((1 - z) ^ (n + 2))⁻¹ * Rem (z / (1 - z))
  have hQ_cd : ContDiffAt ℂ n Q 0 := by
    have h1 : ContDiffAt ℂ n (fun z : ℂ => ((1 - z) ^ (n + 2))⁻¹) 0 :=
      (((contDiffAt_const.sub contDiffAt_id).pow (n + 2)).inv (by norm_num))
    have h2 : ContDiffAt ℂ n (fun z : ℂ => z / (1 - z)) 0 :=
      contDiffAt_id.div (contDiffAt_const.sub contDiffAt_id) (by norm_num)
    have hRem0 : ContDiffAt ℂ n Rem ((0 : ℂ) / (1 - 0)) := by
      simpa using (hRem_an.contDiffAt : ContDiffAt ℂ n Rem 0)
    have h3 : ContDiffAt ℂ n (Rem ∘ fun z : ℂ => z / (1 - z)) 0 := hRem0.comp 0 h2
    exact h1.mul h3
  have hgen_ev : liGenFun =ᶠ[𝓝 (0 : ℂ)]
      fun z : ℂ => (∑ j ∈ Finset.range n, b j * (z ^ (j + 1) * ((1 - z) ^ (j + 2))⁻¹)) +
        z ^ (n + 1) * Q z := by
    set δ : ℝ := min (1 / 2) (rH / 4)
    have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ)] with z hz
    have hz_lt : ‖z‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hz_half : ‖z‖ < 1 / 2 := lt_of_lt_of_le hz_lt (min_le_left _ _)
    have hz1 : z ≠ 1 := by intro h; rw [h, norm_one] at hz_half; linarith
    have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
    have h1z_ge : 1 / 2 < ‖1 - z‖ := by
      have htri := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one] at htri; linarith
    have hu_lt : ‖z / (1 - z)‖ < rH := by
      rw [norm_div]
      calc ‖z‖ / ‖1 - z‖
          < (rH / 4) / (1 / 2) := by
            have hz_rH : ‖z‖ < rH / 4 := lt_of_lt_of_le hz_lt (min_le_right _ _)
            calc ‖z‖ / ‖1 - z‖
                ≤ ‖z‖ / (1 / 2) := div_le_div_of_nonneg_left (norm_nonneg z) (by norm_num) h1z_ge.le
              _ < (rH / 4) / (1 / 2) := div_lt_div_of_pos_right hz_rH (by norm_num)
        _ = rH / 2 := by ring
        _ < rH := by linarith
    have h1u : 1 + z / (1 - z) = 1 / (1 - z) := by field_simp [h1z]; ring
    rw [liGenFun, logDeriv_xiCayley_eq hz1]
    change z * (1 / (1 - z) ^ 2 * H (1 / (1 - z))) = _
    rw [← h1u, hH_split (z / (1 - z)) hu_lt]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow]
      have hp : (1 - z) ^ (j + 2) = (1 - z) ^ 2 * (1 - z) ^ j := by
        rw [← pow_add, add_comm]
      rw [hp]
      field_simp [h1z]
      ring
    · dsimp only [Q]
      rw [div_pow]
      have hp : (1 - z) ^ (n + 2) = (1 - z) ^ 2 * (1 - z) ^ n := by
        rw [← pow_add, add_comm]
      rw [hp]
      field_simp [h1z]
      ring
  -- Step 4: Compute `iteratedDeriv n` of each term at `z = 0`
  have hrem_zero : iteratedDeriv n (fun z : ℂ => z ^ (n + 1) * Q z) 0 = 0 := by
    have hpow_cd : ContDiffAt ℂ n (fun z : ℂ => z ^ (n + 1)) 0 :=
      (contDiff_id.pow (n + 1)).contDiffAt
    change iteratedDeriv n ((fun z : ℂ => z ^ (n + 1)) * Q) 0 = 0
    rw [iteratedDeriv_mul hpow_cd hQ_cd]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [iteratedDeriv_pow_eq]
    have hne0 : n + 1 - k ≠ 0 := by omega
    simp [zero_pow hne0]
  have hterm_val : ∀ j ∈ Finset.range n,
      iteratedDeriv n (fun z : ℂ => b j * (z ^ (j + 1) * ((1 - z) ^ (j + 2))⁻¹)) 0 =
        (Nat.factorial n : ℂ) * ((Nat.choose n (j + 1) : ℂ) * b j) := by
    intro j hj
    have hj_lt : j < n := Finset.mem_range.mp hj
    have hpow_cd : ContDiffAt ℂ n (fun z : ℂ => z ^ (j + 1)) 0 :=
      (contDiff_id.pow (j + 1)).contDiffAt
    have hinv_cd : ContDiffAt ℂ n (fun z : ℂ => ((1 - z) ^ (j + 2))⁻¹) 0 :=
      (((contDiffAt_const.sub contDiffAt_id).pow (j + 2)).inv (by norm_num))
    rw [iteratedDeriv_const_mul_field]
    change b j * iteratedDeriv n ((fun z : ℂ => z ^ (j + 1)) * fun z : ℂ => ((1 - z) ^ (j + 2))⁻¹) 0 = _
    rw [iteratedDeriv_mul hpow_cd hinv_cd, Finset.sum_eq_single (j + 1)]
    · rw [iteratedDeriv_pow_eq, Nat.sub_self, pow_zero, mul_one, Nat.descFactorial_self,
        iteratedDeriv_inv_one_sub_pow (n - (j + 1)) (j + 2) (by norm_num)]
      simp only [sub_zero, one_pow, inv_one, mul_one]
      have hasc : Nat.factorial (j + 1) * Nat.ascFactorial (j + 2) (n - (j + 1)) =
          Nat.factorial n := by
        have h := Nat.factorial_mul_ascFactorial (j + 1) (n - (j + 1))
        have harg : j + 1 + (n - (j + 1)) = n := by omega
        have harg2 : j + 1 + 1 = j + 2 := by omega
        rw [harg, harg2] at h
        exact h
      have hasc_c : (Nat.factorial (j + 1) : ℂ) * (Nat.ascFactorial (j + 2) (n - (j + 1)) : ℂ) =
          (Nat.factorial n : ℂ) := by exact_mod_cast hasc
      calc b j * ((Nat.choose n (j + 1) : ℂ) * (Nat.factorial (j + 1) : ℂ) *
            (Nat.ascFactorial (j + 2) (n - (j + 1)) : ℂ))
          = ((Nat.factorial (j + 1) : ℂ) * (Nat.ascFactorial (j + 2) (n - (j + 1)) : ℂ)) *
              ((Nat.choose n (j + 1) : ℂ) * b j) := by ring
        _ = (Nat.factorial n : ℂ) * ((Nat.choose n (j + 1) : ℂ) * b j) := by rw [hasc_c]
    · intro k hk hkne
      rw [iteratedDeriv_pow_eq]
      by_cases hlt : k < j + 1
      · have hne0 : j + 1 - k ≠ 0 := by omega
        simp [zero_pow hne0]
      · have hgt : j + 1 < k := lt_of_le_of_ne (not_lt.mp hlt) hkne.symm
        simp [Nat.descFactorial_eq_zero_iff_lt.mpr hgt]
    · intro hnot
      exfalso; exact hnot (Finset.mem_range.mpr (by omega))
  have hRHS_complex :
      ((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n liGenFun 0 =
        ∑ j ∈ Finset.range n, (Nat.choose n (j + 1) : ℂ) * b j := by
    rw [hgen_ev.iteratedDeriv_eq n]
    have hsum_cd : ContDiffAt ℂ n
        (fun z : ℂ => ∑ j ∈ Finset.range n, b j * (z ^ (j + 1) * ((1 - z) ^ (j + 2))⁻¹)) 0 :=
      ContDiffAt.sum fun j _ =>
        contDiffAt_const.mul ((contDiff_id.pow (j + 1)).contDiffAt.mul
          (((contDiffAt_const.sub contDiffAt_id).pow (j + 2)).inv (by norm_num)))
    have hrem_cd : ContDiffAt ℂ n (fun z : ℂ => z ^ (n + 1) * Q z) 0 :=
      (contDiff_id.pow (n + 1)).contDiffAt.mul hQ_cd
    change ((Nat.factorial n : ℂ)⁻¹) *
        iteratedDeriv n ((fun z : ℂ => ∑ j ∈ Finset.range n, b j * (z ^ (j + 1) * ((1 - z) ^ (j + 2))⁻¹)) +
          fun z : ℂ => z ^ (n + 1) * Q z) 0 = _
    rw [iteratedDeriv_add hsum_cd hrem_cd, hrem_zero, add_zero]
    rw [iteratedDeriv_fun_sum (fun j _ =>
      contDiffAt_const.mul ((contDiff_id.pow (j + 1)).contDiffAt.mul
        (((contDiffAt_const.sub contDiffAt_id).pow (j + 2)).inv (by norm_num))))]
    rw [Finset.sum_congr rfl hterm_val, ← Finset.mul_sum]
    have hfn : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp [hfn]
  -- Step 5: Match complex identities and take real parts
  have hmatch : ((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n liGenFun 0 =
      ((Nat.factorial (n - 1) : ℂ)⁻¹) *
        iteratedDeriv n (fun s : ℂ => s ^ (n - 1) * Complex.log (xi s)) 1 := by
    rw [hRHS_complex, hLHS_complex]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [b]; ring
  have hre_mul : ∀ (k : ℕ) (z : ℂ),
      ((Nat.factorial k : ℂ)⁻¹ * z).re = (Nat.factorial k : ℝ)⁻¹ * z.re := fun k z => by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  rw [liCoeff_eq_iteratedDeriv_genFun n, liCoeffAnalytic, ← hre_mul n, ← hre_mul (n - 1), hmatch]

/-! ## Section 4: Unconditional Proof of Li's 1997 Criterion (`0` Assumptions!) -/

/-- **Forward Direction of Li's Criterion (Strict Positivity)**:
Mathlib's `RiemannHypothesis` implies `0 < liCoeff n` for EVERY `n ≥ 1`. -/
theorem liCoeff_pos_of_RH (hRH : RiemannHypothesis) {n : ℕ} (hn : 1 ≤ n) :
    0 < liCoeff n := by
  have hall_half : ∀ k : ℕ, (xiZeroSeq k).re = 1 / 2 := fun k =>
    (riemannHypothesis_iff_xi_zeros_on_half_line.mp hRH) (xiZeroSeq k) (xiZeroSeq_zero k)
  have hnorm1 : ∀ k : ℕ, ‖cayley (xiZeroSeq k)‖ = 1 := fun k =>
    (norm_cayley_eq_one_iff (xiZeroSeq_ne_zero k)).mpr (hall_half k)
  have hnorm1_inv : ∀ k : ℕ, ‖cayley (1 - xiZeroSeq k)‖ = 1 := fun k => by
    rw [cayley_one_sub (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k), norm_inv, hnorm1 k, inv_one]
  have hterm_nonneg : ∀ k : ℕ, 0 ≤ (liPairTerm (xiZeroSeq k) n).re := fun k => by
    simp only [liPairTerm, Complex.add_re, Complex.sub_re, Complex.one_re]
    have h1 : (cayley (xiZeroSeq k) ^ n).re ≤ 1 := by
      calc (cayley (xiZeroSeq k) ^ n).re
          ≤ ‖cayley (xiZeroSeq k) ^ n‖ := Complex.re_le_norm _
        _ = ‖cayley (xiZeroSeq k)‖ ^ n := norm_pow _ _
        _ = 1 := by rw [hnorm1 k, one_pow]
    have h2 : (cayley (1 - xiZeroSeq k) ^ n).re ≤ 1 := by
      calc (cayley (1 - xiZeroSeq k) ^ n).re
          ≤ ‖cayley (1 - xiZeroSeq k) ^ n‖ := Complex.re_le_norm _
        _ = ‖cayley (1 - xiZeroSeq k)‖ ^ n := norm_pow _ _
        _ = 1 := by rw [hnorm1_inv k, one_pow]
    linarith
  have hex_ne : ∃ k₀ : ℕ, cayley (xiZeroSeq k₀) ^ n ≠ 1 := by
    by_contra hall
    push Not at hall
    have hfin_roots : {w : ℂ | w ^ n = 1}.Finite := by
      have hne0 : (Polynomial.X ^ n - 1 : Polynomial ℂ) ≠ 0 := by
        intro h
        have hdeg : (Polynomial.X ^ n - 1 : Polynomial ℂ).natDegree = n :=
          Polynomial.natDegree_X_pow_sub_C
        rw [h, Polynomial.natDegree_zero] at hdeg
        omega
      refine ((Polynomial.X ^ n - 1 : Polynomial ℂ).roots.toFinset.finite_toSet).subset fun w hw => ?_
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne0,
        Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one]
      exact sub_eq_zero.mpr hw
    have hinj : Set.InjOn cayley {s : ℂ | xi s = 0} := by
      intro s₁ hs₁ s₂ hs₂ heq
      change xi s₁ = 0 at hs₁
      change xi s₂ = 0 at hs₂
      have h10 : s₁ ≠ 0 := by intro h; rw [h, xi_zero] at hs₁; exact one_ne_zero hs₁
      have h20 : s₂ ≠ 0 := by intro h; rw [h, xi_zero] at hs₂; exact one_ne_zero hs₂
      rw [← inv_one_sub_cayley h10, ← inv_one_sub_cayley h20, heq]
    have himg_sub : cayley '' {s : ℂ | xi s = 0} ⊆ {w : ℂ | w ^ n = 1} := by
      rintro w ⟨s, hs, rfl⟩
      obtain ⟨k, hk⟩ := exists_xiZeroSeq_eq hs
      rw [← hk]
      exact hall k
    have hinf_img : (cayley '' {s : ℂ | xi s = 0}).Infinite :=
      infinite_xi_zeros.image hinj
    exact hinf_img (hfin_roots.subset himg_sub)
  obtain ⟨k₀, hk₀⟩ := hex_ne
  have hterm_pos : 0 < (liPairTerm (xiZeroSeq k₀) n).re := by
    have hre_lt : (cayley (xiZeroSeq k₀) ^ n).re < 1 := by
      have hle : (cayley (xiZeroSeq k₀) ^ n).re ≤ 1 := by
        calc (cayley (xiZeroSeq k₀) ^ n).re
            ≤ ‖cayley (xiZeroSeq k₀) ^ n‖ := Complex.re_le_norm _
          _ = 1 := by rw [norm_pow, hnorm1 k₀, one_pow]
      refine lt_of_le_of_ne hle fun heq => hk₀ ?_
      have hns : Complex.normSq (cayley (xiZeroSeq k₀) ^ n) = 1 := by
        rw [Complex.normSq_eq_norm_sq, norm_pow, hnorm1 k₀, one_pow, one_pow]
      rw [Complex.normSq_apply, heq] at hns
      have him : (cayley (xiZeroSeq k₀) ^ n).im = 0 := by nlinarith
      exact Complex.ext heq him
    have h2 : (cayley (1 - xiZeroSeq k₀) ^ n).re ≤ 1 := by
      calc (cayley (1 - xiZeroSeq k₀) ^ n).re
          ≤ ‖cayley (1 - xiZeroSeq k₀) ^ n‖ := Complex.re_le_norm _
        _ = 1 := by rw [norm_pow, hnorm1_inv k₀, one_pow]
    simp only [liPairTerm, Complex.add_re, Complex.sub_re, Complex.one_re]
    linarith
  have hsum_pos : 0 < ∑' k : ℕ, (liPairTerm (xiZeroSeq k) n).re :=
    lt_of_lt_of_le hterm_pos ((summable_liPairTerm_re n).le_tsum k₀ fun k _ => hterm_nonneg k)
  unfold liCoeff
  linarith

/-- **Forward Direction of Li's Criterion (Non-negativity)**:
Mathlib's `RiemannHypothesis` implies `0 ≤ liCoeff n` for EVERY `n ≥ 1`. -/
theorem liCoeff_nonneg_of_RH (hRH : RiemannHypothesis) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ liCoeff n :=
  (liCoeff_pos_of_RH hRH hn).le

/-- Finite binomial double-sum rearrangement:
`∑ n < N, a n * (r + h)^n = ∑ m < N, (∑ k < N - m, C(m + k, m) * a (m + k) * r^k) * h^m`. -/
private lemma finset_binomial_double_sum (a : ℕ → ℝ) (r h : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n * (r + h) ^ n =
      ∑ m ∈ Finset.range N,
        (∑ k ∈ Finset.range (N - m), (Nat.choose (m + k) m : ℝ) * a (m + k) * r ^ k) * h ^ m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hbin : a N * (r + h) ^ N =
        (∑ m ∈ Finset.range N, (Nat.choose N m : ℝ) * a N * r ^ (N - m) * h ^ m) +
        (Nat.choose N N : ℝ) * a N * h ^ N := by
      rw [add_comm r h, add_pow, Finset.mul_sum, Finset.sum_range_succ]
      simp only [Nat.sub_self, pow_zero, mul_one]
      congr 1
      · refine Finset.sum_congr rfl fun m _ => by ring
      · ring
    rw [hbin, ← add_assoc, ← Finset.sum_add_distrib]
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hm_lt : m < N := Finset.mem_range.mp hm
      have hsub : N + 1 - m = (N - m) + 1 := by omega
      have hmk : m + (N - m) = N := by omega
      rw [hsub, Finset.sum_range_succ, add_mul, hmk]
    · have h1 : N + 1 - N = 1 := by omega
      rw [h1, Finset.sum_range_one, add_zero, pow_zero, mul_one]

/-- Helper: if `0 ≤ a n` and `Summable (fun n => a n * r' ^ n)` with `0 < r < r'`, then
`Summable (fun k => (Nat.choose (m + k) m : ℝ) * a (m + k) * r ^ k)` for every `m : ℕ`. -/
private lemma summable_choose_mul_pow {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {r r' : ℝ} (hr : 0 < r) (hrr' : r < r')
    (hsr' : Summable (fun n : ℕ => a n * r' ^ n)) (m : ℕ) :
    Summable (fun k : ℕ => (Nat.choose (m + k) m : ℝ) * a (m + k) * r ^ k) := by
  have hr'_pos : 0 < r' := lt_trans hr hrr'
  have hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, a n * r' ^ n ≤ M := by
    have ht : Tendsto (fun n : ℕ => a n * r' ^ n) atTop (𝓝 0) := hsr'.tendsto_atTop_zero
    have hev : ∀ᶠ n : ℕ in atTop, a n * r' ^ n ≤ 1 := ht.eventually (Iic_mem_nhds zero_lt_one)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨K, hK⟩ := hev
    let S : Finset ℝ := insert 1 ((Finset.range K).image fun n => a n * r' ^ n)
    refine ⟨S.max' (Finset.insert_nonempty _ _),
      le_trans zero_le_one (Finset.le_max' S 1 (Finset.mem_insert_self _ _)), fun n => ?_⟩
    by_cases hn : n < K
    · exact Finset.le_max' S _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hn)))
    · exact le_trans (hK n (not_lt.mp hn)) (Finset.le_max' S 1 (Finset.mem_insert_self _ _))
  obtain ⟨M, hM0, hM⟩ := hbd
  have hs_desc := (summable_descFactorial_mul_pow (div_nonneg hr.le hr'_pos.le)
    ((div_lt_one hr'_pos).mpr hrr') m).mul_left (M / r' ^ m)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha (m + k))) (pow_nonneg hr.le k))
    (fun k => ?_) hs_desc
  have hch_le : (Nat.choose (m + k) m : ℝ) ≤ (Nat.descFactorial (m + k) m : ℝ) := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    exact_mod_cast Nat.div_le_self _ _
  have han : a (m + k) ≤ M / r' ^ (m + k) :=
    (le_div_iff₀ (pow_pos hr'_pos (m + k))).mpr (hM (m + k))
  have ha_non : 0 ≤ a (m + k) := ha (m + k)
  have hnon : 0 ≤ (Nat.descFactorial (m + k) m : ℝ) * (M / r' ^ (m + k)) := by positivity
  calc (Nat.choose (m + k) m : ℝ) * a (m + k) * r ^ k
      ≤ (Nat.descFactorial (m + k) m : ℝ) * (M / r' ^ (m + k)) * r ^ k := by gcongr
    _ = (M / r' ^ m) * ((Nat.descFactorial (m + k) m : ℝ) * (r / r') ^ k) := by
        rw [pow_add, div_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
        ring

/-- **Elementary Pringsheim Extension Lemma (for nonnegative power series)**:
if `∀ n, 0 ≤ a n`, `0 < R₀`, `HasSum (fun n => (a n : ℂ) * z ^ n) (φ z)` on `Metric.ball 0 R₀`,
and `φ` is complex-differentiable on `Metric.ball (R₀ : ℂ) δ` for some `δ > 0`,
then there exists `R₁ > R₀` with `Summable (fun n => a n * R₁ ^ n)`. -/
theorem pringsheim_radius_extend {a : ℕ → ℝ} (ha : ∀ n : ℕ, 0 ≤ a n)
    {φ : ℂ → ℂ} {R₀ δ : ℝ} (hR₀ : 0 < R₀) (hδ : 0 < δ)
    (hser : ∀ z : ℂ, ‖z‖ < R₀ → HasSum (fun n : ℕ => (a n : ℂ) * z ^ n) (φ z))
    (hdiff : DifferentiableOn ℂ φ (Metric.ball (R₀ : ℂ) δ)) :
    ∃ R₁ : ℝ, R₀ < R₁ ∧ Summable (fun n : ℕ => a n * R₁ ^ n) := by
  let ε : ℝ := min (δ / 4) (R₀ / 2)
  have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
  let r : ℝ := R₀ - ε
  have hr_pos : 0 < r := by
    have : ε ≤ R₀ / 2 := min_le_right _ _
    dsimp only [r]; linarith
  have hr_lt : r < R₀ := by dsimp only [r]; linarith
  have hball_sub : Metric.closedBall (r : ℂ) (2 * ε) ⊆ Metric.ball (R₀ : ℂ) δ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    have h4ε : 4 * ε ≤ δ := by
      have : ε ≤ δ / 4 := min_le_left _ _
      linarith
    have hdiff_r : ‖(r : ℂ) - (R₀ : ℂ)‖ = ε := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have : r - R₀ = -ε := by dsimp only [r]; ring
      rw [this, abs_neg, abs_of_pos hε_pos]
    calc ‖w - (R₀ : ℂ)‖
        = ‖(w - (r : ℂ)) + ((r : ℂ) - (R₀ : ℂ))‖ := by congr 1; ring
      _ ≤ ‖w - (r : ℂ)‖ + ‖(r : ℂ) - (R₀ : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * ε + ε := by rw [hdiff_r]; linarith
      _ < δ := by linarith
  let Rnn : NNReal := ⟨2 * ε, by positivity⟩
  have hRnn_pos : (0 : NNReal) < Rnn := by
    change (0 : ℝ) < 2 * ε
    linarith
  have hdiff_r : DifferentiableOn ℂ φ (Metric.closedBall (r : ℂ) (Rnn : ℝ)) :=
    hdiff.mono hball_sub
  have hfps : HasFPowerSeriesOnBall φ (cauchyPowerSeries φ (r : ℂ) (Rnn : ℝ)) (r : ℂ) (Rnn : ENNReal) :=
    hdiff_r.hasFPowerSeriesOnBall hRnn_pos
  let h : ℝ := (3 / 2 : ℝ) * ε
  have hh_pos : 0 < h := by dsimp only [h]; linarith
  have hh_lt : h < 2 * ε := by dsimp only [h]; linarith
  let h' : ℝ := (7 / 4 : ℝ) * ε
  have hh'_pos : 0 < h' := by dsimp only [h']; linarith
  have hh_lt_h' : h < h' := by dsimp only [h, h']; linarith
  have hh'_lt_2ε : h' < (Rnn : ℝ) := by
    change (7 / 4 : ℝ) * ε < 2 * ε
    linarith
  have hh'_lt_Rnn : ENNReal.ofReal h' < (Rnn : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hh'_lt_2ε
  have hhas_r : HasSum (fun m : ℕ =>
      ((Nat.factorial m : ℂ)⁻¹ * iteratedDeriv m φ (r : ℂ)) * (h : ℂ) ^ m)
      (φ ((r : ℂ) + (h : ℂ))) :=
    hasSum_taylor_of_hasFPowerSeriesOnBall hfps hh'_pos hh'_lt_Rnn
      (h : ℂ) (by simpa [Complex.norm_real, abs_of_pos hh_pos] using hh_lt_h')
  have hsum_re : Summable (fun m : ℕ =>
      (((Nat.factorial m : ℂ)⁻¹ * iteratedDeriv m φ (r : ℂ)).re) * h ^ m) := by
    have hs := Complex.reCLM.summable hhas_r.summable
    refine hs.congr fun m => ?_
    change (((Nat.factorial m : ℂ)⁻¹ * iteratedDeriv m φ (r : ℂ)) * (h : ℂ) ^ m).re = _
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  let r' : ℝ := (r + R₀) / 2
  have hrr' : r < r' := by dsimp only [r']; linarith
  have hr'R : r' < R₀ := by dsimp only [r']; linarith
  have hr'_pos : 0 < r' := lt_trans hr_pos hrr'
  have hsr' : Summable (fun n : ℕ => a n * r' ^ n) := by
    have hs := Complex.reCLM.summable
      (hser (r' : ℂ) (by simpa [Complex.norm_real, abs_of_pos hr'_pos] using hr'R)).summable
    refine hs.congr fun n => ?_
    change ((a n : ℂ) * (r' : ℂ) ^ n).re = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsum_k : ∀ m : ℕ, Summable (fun k : ℕ => (Nat.choose (m + k) m : ℝ) * a (m + k) * r ^ k) :=
    summable_choose_mul_pow ha hr_pos hrr' hsr'
  have hiter_re : ∀ m : ℕ,
      ((Nat.factorial m : ℂ)⁻¹ * iteratedDeriv m φ (r : ℂ)).re =
        ∑' k : ℕ, (Nat.choose (m + k) m : ℝ) * a (m + k) * r ^ k := by
    intro m
    have h1 := iteratedDeriv_powerSeries_eq_tsum hser m (r : ℂ)
      (by simpa [Complex.norm_real, abs_of_pos hr_pos] using hr_lt)
    rw [h1, ← tsum_mul_left]
    have hfac : (Nat.factorial m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have htsum_eq :
        ∑' k : ℕ, (Nat.factorial m : ℂ)⁻¹ *
          ((Nat.descFactorial (m + k) m : ℂ) * (a (m + k) : ℂ) * (r : ℂ) ^ k) =
        ∑' k : ℕ, (((Nat.choose (m + k) m : ℝ) * a (m + k) * r ^ k : ℝ) : ℂ) := by
      refine tsum_congr fun k => ?_
      have hdesc : (Nat.descFactorial (m + k) m : ℕ) = Nat.choose (m + k) m * Nat.factorial m := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
      have hdesc_c : (Nat.descFactorial (m + k) m : ℂ) =
          (Nat.choose (m + k) m : ℂ) * (Nat.factorial m : ℂ) := by exact_mod_cast hdesc
      rw [hdesc_c]
      push_cast
      field_simp [hfac]
    rw [htsum_eq, ← Complex.ofReal_tsum]
    exact Complex.ofReal_re _
  let R₁ : ℝ := r + h
  have hR₁_gt : R₀ < R₁ := by dsimp only [R₁, r, h]; linarith
  have hR₁_pos : 0 < R₁ := lt_trans hR₀ hR₁_gt
  refine ⟨R₁, hR₁_gt, summable_of_sum_range_le (c := ∑' m : ℕ,
      (((Nat.factorial m : ℂ)⁻¹ * iteratedDeriv m φ (r : ℂ)).re) * h ^ m)
      (fun n => mul_nonneg (ha n) (pow_nonneg hR₁_pos.le n)) fun N => ?_⟩
  have hterm_nonneg : ∀ m : ℕ,
      0 ≤ (((Nat.factorial m : ℂ)⁻¹ * iteratedDeriv m φ (r : ℂ)).re) * h ^ m := by
    intro m
    rw [hiter_re m]
    exact mul_nonneg
      (tsum_nonneg fun k => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha (m + k))) (pow_nonneg hr_pos.le k))
      (pow_nonneg hh_pos.le m)
  rw [finset_binomial_double_sum a r h N]
  have hle_inner : ∀ m ∈ Finset.range N,
      (∑ k ∈ Finset.range (N - m), (Nat.choose (m + k) m : ℝ) * a (m + k) * r ^ k) * h ^ m ≤
      (((Nat.factorial m : ℂ)⁻¹ * iteratedDeriv m φ (r : ℂ)).re) * h ^ m := fun m _ => by
    rw [hiter_re m]
    exact mul_le_mul_of_nonneg_right
      ((hsum_k m).sum_le_tsum (Finset.range (N - m)) fun k _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha (m + k))) (pow_nonneg hr_pos.le k))
      (pow_nonneg hh_pos.le m)
  exact le_trans (Finset.sum_le_sum hle_inner)
    (hsum_re.sum_le_tsum (Finset.range N) fun m _ => hterm_nonneg m)

/-- Simple-pole residue limit for `liGenFun` at any zero `z_* ≠ 0, 1` of `xiCayley`:
`(z - z_*) * liGenFun z → (m : ℂ) * z_* ≠ 0` along `𝓝[≠] z_*`, where `m = analyticOrderNatAt xiCayley z_* ≥ 1`. -/
private lemma tendsto_sub_mul_liGenFun_of_zero {z₀ : ℂ} (hz₀_ne0 : z₀ ≠ 0) (hz₀_ne1 : z₀ ≠ 1)
    (hzero : xiCayley z₀ = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun z : ℂ => (z - z₀) * liGenFun z) (𝓝[≠] z₀) (𝓝 c) := by
  have han : AnalyticOnNhd ℂ xiCayley ({1}ᶜ : Set ℂ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_xiCayley (by simpa using hz)).differentiableWithinAt) isOpen_compl_singleton
  have han0 : AnalyticAt ℂ xiCayley z₀ := han z₀ (by simpa using hz₀_ne1)
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num : (1 : Cardinal) < Module.rank ℝ ℂ) (1 : ℂ)).isPreconnected
  have hne_top : analyticOrderAt xiCayley z₀ ≠ ⊤ := by
    intro htop
    have hev0 : xiCayley =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.mp htop
    have h0eq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
      (by simpa using hz₀_ne1) hev0 (show (0 : ℂ) ∈ ({1}ᶜ : Set ℂ) by simp)
    rw [xiCayley_zero] at h0eq
    exact one_ne_zero h0eq
  set m : ℕ := analyticOrderNatAt xiCayley z₀
  have hm_pos : 0 < m := by
    have hne0 : analyticOrderAt xiCayley z₀ ≠ 0 := by
      intro h0
      exact (han0.analyticOrderAt_eq_zero.mp h0) hzero
    have hcast : (m : ENat) = analyticOrderAt xiCayley z₀ :=
      ENat.natCast_toNat hne_top
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    rw [this, Nat.cast_zero] at hcast
    exact hne0 hcast.symm
  obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := han0.analyticOrderAt_ne_top.mp hne_top
  refine ⟨(m : ℂ) * z₀, mul_ne_zero (Nat.cast_ne_zero.mpr hm_pos.ne') hz₀_ne0, ?_⟩
  have hh_diff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ h z :=
    hh_an.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hh_ne_ev : ∀ᶠ z in 𝓝 z₀, h z ≠ 0 :=
    hh_an.continuousAt.eventually_ne hh_ne
  have hlog_ev : ∀ᶠ z in 𝓝[≠] z₀,
      (z - z₀) * liGenFun z =
        z * ((m : ℂ) + (z - z₀) * (deriv h z / h z)) := by
    have hmem : ∀ᶠ z in 𝓝 z₀,
        (xiCayley =ᶠ[𝓝 z] fun w => (w - z₀) ^ m * h w) ∧ DifferentiableAt ℂ h z ∧ h z ≠ 0 := by
      have h1 : ∀ᶠ z in 𝓝 z₀, xiCayley =ᶠ[𝓝 z] fun w => (w - z₀) ^ m * h w :=
        eventually_eventually_nhds.mpr (hh_eq.mono fun w hw => by simpa [smul_eq_mul] using hw)
      exact h1.and (hh_diff.and hh_ne_ev)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with z ⟨hev_z, hdz, hhz⟩ (hz_ne : z ≠ z₀)
    have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
    have hval : xiCayley z = (z - z₀) ^ m * h z := hev_z.self_of_nhds
    have hderiv_pow : HasDerivAt (fun w : ℂ => (w - z₀) ^ m)
        ((m : ℂ) * (z - z₀) ^ (m - 1)) z := by
      have h1 : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
      have h2 := (hasDerivAt_pow m (z - z₀)).comp z h1
      simpa only [Function.comp_def, mul_one] using h2
    have hderiv_prod : HasDerivAt (fun w : ℂ => (w - z₀) ^ m * h w)
        (((m : ℂ) * (z - z₀) ^ (m - 1)) * h z + (z - z₀) ^ m * deriv h z) z :=
      hderiv_pow.mul hdz.hasDerivAt
    have hderiv_xi : deriv xiCayley z =
        ((m : ℂ) * (z - z₀) ^ (m - 1)) * h z + (z - z₀) ^ m * deriv h z := by
      rw [hev_z.deriv_eq, hderiv_prod.deriv]
    rw [liGenFun, logDeriv_apply, hderiv_xi, hval]
    have hpow_split : (z - z₀) ^ m = (z - z₀) ^ (m - 1) * (z - z₀) := by
      rw [← pow_succ, Nat.sub_add_cancel hm_pos]
    have hp1 : (z - z₀) ^ (m - 1) ≠ 0 := pow_ne_zero _ hzsub
    have hp2 : (z - z₀) ^ m ≠ 0 := pow_ne_zero _ hzsub
    field_simp [hzsub, hhz, hp1, hp2]
    rw [hpow_split]
    ring
  have hcont_dh : ContinuousAt (fun z : ℂ => deriv h z / h z) z₀ :=
    (hh_an.deriv.continuousAt).div hh_an.continuousAt hh_ne
  have htend_rhs : Tendsto (fun z : ℂ => z * ((m : ℂ) + (z - z₀) * (deriv h z / h z)))
      (𝓝[≠] z₀) (𝓝 ((m : ℂ) * z₀)) := by
    have h1 : Tendsto (fun z : ℂ => z * ((m : ℂ) + (z - z₀) * (deriv h z / h z)))
        (𝓝 z₀) (𝓝 (z₀ * ((m : ℂ) + (z₀ - z₀) * (deriv h z₀ / h z₀)))) :=
      continuousAt_id.mul (continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hcont_dh))
    simp only [sub_self, zero_mul, add_zero, mul_comm z₀ (m : ℂ)] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  exact htend_rhs.congr' (hlog_ev.mono fun _ h => h.symm)

/-- **UNCONDITIONAL CONVERSE OF LI'S 1997 CRITERION (`RH_of_liCoeff_nonneg`, `0` Assumptions!)**:
if `0 ≤ liCoeff n` for all `n ≥ 1`, then Mathlib's `RiemannHypothesis` holds! -/
theorem RH_of_liCoeff_nonneg (hnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff n) :
    RiemannHypothesis := by
  have hall_nonneg : ∀ n : ℕ, 0 ≤ liCoeff n := fun n => by
    by_cases hn : n = 0
    · subst hn; simp
    · exact hnonneg n (Nat.pos_of_ne_zero hn)
  rw [← liMinRadius_eq_one_iff_RH]
  by_contra hne1
  have hR_lt : liMinRadius < 1 := lt_of_le_of_ne liMinRadius_le_one hne1
  -- Step 1: `xiCayley (liMinRadius : ℂ) = xi (1 / (1 - liMinRadius)) ≠ 0` since `1 / (1 - R₀) > 1`!
  have hR_ne1 : (liMinRadius : ℂ) ≠ 1 := by exact_mod_cast hR_lt.ne
  have hxi_R_ne : xiCayley (liMinRadius : ℂ) ≠ 0 := by
    unfold xiCayley
    have hre_ge : (1 : ℝ) ≤ (1 / (1 - (liMinRadius : ℂ))).re := by
      have hsub : (1 : ℂ) - (liMinRadius : ℂ) = ((1 - liMinRadius : ℝ) : ℂ) := by simp
      rw [hsub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      have hpos : 0 < 1 - liMinRadius := by linarith
      rw [le_div_iff₀ hpos]
      linarith [liMinRadius_pos]
    exact xi_ne_zero_of_one_le_re hre_ge
  -- Step 2: `liGenFun` is differentiable on a small ball `Metric.ball (liMinRadius : ℂ) δ`!
  have hopen_good : IsOpen {z : ℂ | z ≠ 1 ∧ xiCayley z ≠ 0} := by
    have h1 : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hcont : ContinuousOn xiCayley ({1}ᶜ : Set ℂ) := fun z hz =>
      (differentiableAt_xiCayley (by simpa using hz)).continuousAt.continuousWithinAt
    have h2 : IsOpen ({z : ℂ | z ∈ ({1}ᶜ : Set ℂ) ∧ xiCayley z ≠ 0}) :=
      hcont.isOpen_inter_preimage h1 isOpen_ne
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using h2
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hopen_good (liMinRadius : ℂ) ⟨hR_ne1, hxi_R_ne⟩
  have hdiff_R : DifferentiableOn ℂ liGenFun (Metric.ball (liMinRadius : ℂ) δ) := by
    intro z hz
    obtain ⟨hz1, hxz⟩ := hδ_sub hz
    have han_xc : AnalyticAt ℂ xiCayley z :=
      (DifferentiableOn.analyticOnNhd (fun w hw =>
        (differentiableAt_xiCayley (by simpa using hw)).differentiableWithinAt)
        isOpen_compl_singleton) z (by simpa using hz1)
    have hdiff_ld : DifferentiableAt ℂ (logDeriv xiCayley) z := by
      change DifferentiableAt ℂ (fun w => deriv xiCayley w / xiCayley w) z
      exact han_xc.deriv.differentiableAt.div (differentiableAt_xiCayley hz1) hxz
    exact (differentiableAt_id.mul hdiff_ld).differentiableWithinAt
  -- Step 3: Apply Pringsheim extension to get `R₁ > liMinRadius` with `∑ liCoeff n * R₁^n < ∞`!
  obtain ⟨R₁, hR₁_gt, hR₁_sum⟩ := pringsheim_radius_extend hall_nonneg liMinRadius_pos hδ_pos
    (fun z hz => liCoeff_eq_taylor_logDeriv_cayley hz) hdiff_R
  -- Step 4: Pick a minimal-modulus zero `z₀ = cayley (xiZeroSeq k₀)` with `‖z₀‖ = liMinRadius < R₁`
  obtain ⟨k₀, hk₀⟩ := exists_min_cayley_of_lt_one hR_lt
  set z₀ : ℂ := cayley (xiZeroSeq k₀)
  have hz₀_norm : ‖z₀‖ = liMinRadius := hk₀
  have hz₀_ne0 : z₀ ≠ 0 := xiZeroSeq_cayley_ne_zero k₀
  have hz₀_ne1 : z₀ ≠ 1 := xiZeroSeq_cayley_ne_one k₀
  have hxc_zero : xiCayley z₀ = 0 := by
    unfold xiCayley
    rw [inv_one_sub_cayley (xiZeroSeq_ne_zero k₀)]
    exact xiZeroSeq_zero k₀
  -- Step 5: Approach `z₀` radially along `γ t = (t : ℂ) * z₀` as `t → 1⁻`
  let γ : ℝ → ℂ := fun t => (t : ℂ) * z₀
  have hγ_tend : Tendsto γ (𝓝[<] (1 : ℝ)) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto γ (𝓝 (1 : ℝ)) (𝓝 ((1 : ℂ) * z₀)) :=
        (Complex.continuous_ofReal.tendsto 1).mul tendsto_const_nhds
      rw [one_mul] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < 1)
      change (t : ℂ) * z₀ ≠ z₀
      intro heq
      have h1 : ((t : ℂ) - 1) * z₀ = 0 := by linear_combination heq
      have ht1 : (t : ℂ) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hz₀_ne0)
      have : t = 1 := by exact_mod_cast ht1
      linarith
  -- Limit 1: `‖liGenFun (γ t)‖ ≤ ∑' n, liCoeff n * R₁ ^ n` for `t ∈ (0, 1)`, so `(γ t - z₀) * liGenFun (γ t) → 0`!
  set C : ℝ := ∑' n : ℕ, liCoeff n * R₁ ^ n
  have hlim_zero : Tendsto (fun t : ℝ => (γ t - z₀) * liGenFun (γ t)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hsub_tend : Tendsto (fun t : ℝ => ‖γ t - z₀‖ * C) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => γ t - z₀) (𝓝[<] (1 : ℝ)) (𝓝 (z₀ - z₀)) :=
        (hγ_tend.mono_right nhdsWithin_le_nhds).sub (tendsto_const_nhds (x := z₀))
      rw [sub_self] at h1
      simpa using h1.norm.mul_const C
    refine squeeze_zero_norm' ?_ hsub_tend
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ⟨ht0, ht1⟩
    have hnorm_lt : ‖γ t‖ < liMinRadius := by
      simp only [γ, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le, hz₀_norm]
      nlinarith [liMinRadius_pos]
    have hbound : ‖liGenFun (γ t)‖ ≤ C := by
      rw [liGenFun_eq_tsum hnorm_lt]
      have hsum_t : Summable (fun n : ℕ => ‖(liCoeff n : ℂ) * (γ t) ^ n‖) := by
        refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hR₁_sum
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hall_nonneg n)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (le_trans hnorm_lt.le hR₁_gt.le) n) (hall_nonneg n)
      calc ‖∑' n : ℕ, (liCoeff n : ℂ) * (γ t) ^ n‖
          ≤ ∑' n : ℕ, ‖(liCoeff n : ℂ) * (γ t) ^ n‖ := norm_tsum_le_tsum_norm hsum_t
        _ ≤ C := hsum_t.tsum_le_tsum (fun n => by
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hall_nonneg n)]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) (le_trans hnorm_lt.le hR₁_gt.le) n) (hall_nonneg n))
            hR₁_sum
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  -- Limit 2: From simple-pole residue of `liGenFun` at `z₀`, `(γ t - z₀) * liGenFun (γ t) → c ≠ 0`!
  obtain ⟨c, hc_ne, hc_tend⟩ := tendsto_sub_mul_liGenFun_of_zero hz₀_ne0 hz₀_ne1 hxc_zero
  have hlim_c : Tendsto (fun t : ℝ => (γ t - z₀) * liGenFun (γ t)) (𝓝[<] (1 : ℝ)) (𝓝 c) :=
    hc_tend.comp hγ_tend
  exact hc_ne (tendsto_nhds_unique hlim_c hlim_zero)

/-- **UNCONDITIONAL LI'S 1997 CRITERION (NON-NEGATIVITY FORM, `0` ASSUMPTIONS!)**:
`RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff n`. -/
theorem riemannHypothesis_iff_liCoeff_nonneg :
    RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff n :=
  ⟨fun hRH _ hn => liCoeff_nonneg_of_RH hRH hn, RH_of_liCoeff_nonneg⟩

/-- **UNCONDITIONAL LI'S 1997 CRITERION (STRICT POSITIVITY FORM, `0` ASSUMPTIONS!)**:
`RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 < liCoeff n`. -/
theorem riemannHypothesis_iff_liCoeff_pos :
    RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 < liCoeff n :=
  ⟨fun hRH _ hn => liCoeff_pos_of_RH hRH hn,
   fun hpos => RH_of_liCoeff_nonneg fun n hn => (hpos n hn).le⟩

/-- **UNCONDITIONAL KEIPER–LI ANALYTIC CRITERION (`0` ASSUMPTIONS!)**:
`RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeffAnalytic n`. -/
theorem riemannHypothesis_iff_liCoeffAnalytic_nonneg :
    RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeffAnalytic n := by
  rw [riemannHypothesis_iff_liCoeff_nonneg]
  exact ⟨fun h n hn => liCoeff_eq_liCoeffAnalytic hn ▸ h n hn,
         fun h n hn => (liCoeff_eq_liCoeffAnalytic hn).symm ▸ h n hn⟩

/-! ## Section 5: Exact Evaluation of `λ₁` & the Hadamard Constant `xiHadamardB` -/

/-- Exact paired alternating harmonic sum:
`HasSum (fun n : ℕ => ((2 * n + 1 : ℝ)⁻¹ - (2 * n + 2 : ℝ)⁻¹)) (Real.log 2)`. -/
theorem hasSum_alternating_harmonic_pair :
    HasSum (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ)⁻¹ - ((2 * n + 2 : ℕ) : ℝ)⁻¹)) (Real.log 2) := by
  have hpartial : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, (((2 * n + 1 : ℕ) : ℝ)⁻¹ - ((2 * n + 2 : ℕ) : ℝ)⁻¹) =
        (harmonic (2 * N) : ℝ) - (harmonic N : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have h2N : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
      rw [h2N, harmonic_succ, harmonic_succ, harmonic_succ]
      have h1 : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (2 * (N : ℝ) + 2) ≠ 0 := by positivity
      have h3 : ((N : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp [h1, h2, h3]
      ring
  have htend : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (((2 * n + 1 : ℕ) : ℝ)⁻¹ - ((2 * n + 2 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 (Real.log 2)) := by
    simp_rw [hpartial]
    have h1 : Tendsto (fun N : ℕ => (harmonic (2 * N) : ℝ) - Real.log ((2 * N : ℕ) : ℝ))
        atTop (𝓝 Real.eulerMascheroniConstant) :=
      Real.tendsto_harmonic_sub_log.comp (tendsto_atTop_atTop_of_monotone
        (fun a b hab => Nat.mul_le_mul_left 2 hab) fun b => ⟨b, by omega⟩)
    have h2 : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log (N : ℝ))
        atTop (𝓝 Real.eulerMascheroniConstant) :=
      Real.tendsto_harmonic_sub_log
    have hdiff := (h1.sub h2).add_const (Real.log 2)
    rw [sub_self, zero_add] at hdiff
    refine hdiff.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hN_pos.ne']
    ring
  have hsum : Summable (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ)⁻¹ - ((2 * n + 2 : ℕ) : ℝ)⁻¹)) := by
    have hinv2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
      (Real.summable_nat_pow_inv.mpr (by norm_num : (1 : ℕ) < 2)).comp_injective
        (fun _ _ h => Nat.succ.inj h)
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hinv2
    · have hle : ((2 * n + 1 : ℕ) : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * n + 2)
      linarith [inv_anti₀ (by positivity : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ)) hle]
    · have h1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
      have h3 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have heq : (((2 * n + 1 : ℕ) : ℝ)⁻¹ - ((2 * n + 2 : ℕ) : ℝ)⁻¹) =
          ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))⁻¹ := by
        push_cast; field_simp [h1.ne', h2.ne']; ring
      rw [heq]
      refine inv_anti₀ h3 ?_
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hval : ∑' n : ℕ, (((2 * n + 1 : ℕ) : ℝ)⁻¹ - ((2 * n + 2 : ℕ) : ℝ)⁻¹) = Real.log 2 :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat htend
  exact hval ▸ hsum.hasSum

/-- Exact value of the digamma function at `1 / 2`:
`Complex.digamma (1 / 2 : ℂ) = -((Real.eulerMascheroniConstant + 2 * Real.log 2 : ℝ) : ℂ)`. -/
theorem digamma_half_eq :
    Complex.digamma (1 / 2 : ℂ) =
      -((Real.eulerMascheroniConstant + 2 * Real.log 2 : ℝ) : ℂ) := by
  have hre : 0 < (1 / 2 : ℂ).re := by norm_num
  rw [RHDirect.Stage7VonMangoldtExplicit.digamma_eq_neg_eulerMascheroni_add_tsum hre]
  have hhas_c : HasSum
      (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ)⁻¹ - ((2 * n + 2 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))
      (Real.log 2 : ℂ) :=
    Complex.ofRealCLM.hasSum hasSum_alternating_harmonic_pair
  have hhas_scaled := hhas_c.mul_left (-2 : ℂ)
  have hterm : ∀ n : ℕ,
      (((n + 1 : ℕ) : ℂ))⁻¹ - ((1 / 2 : ℂ) + (n : ℂ))⁻¹ =
        (-2 : ℂ) * ((((2 * n + 1 : ℕ) : ℝ)⁻¹ - ((2 * n + 2 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := fun n => by
    have h1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : (2 * n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * n + 1 ≠ 0)
    have h3 : (2 * n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * n + 2 ≠ 0)
    have h4 : (1 / 2 : ℂ) + (n : ℂ) ≠ 0 := by
      intro h
      have hre' := congrArg Complex.re h
      simp at hre'
      linarith [Nat.cast_nonneg (α := ℝ) n]
    push_cast
    field_simp [h1, h2, h3, h4]
    ring
  rw [tsum_congr hterm, hhas_scaled.tsum_eq]
  push_cast
  ring

/-- Exact derivative of `Complex.Gammaℝ` at `s = 1`:
`deriv Complex.Gammaℝ 1 = -((Real.eulerMascheroniConstant / 2 + Real.log (4 * Real.pi) / 2 : ℝ) : ℂ)`. -/
theorem deriv_Gammaℝ_one :
    deriv Complex.Gammaℝ 1 =
      -((Real.eulerMascheroniConstant / 2 + Real.log (4 * Real.pi) / 2 : ℝ) : ℂ) := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi_pos.ne'
  have hexp_d : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-(1 : ℂ) / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2 : ℂ)) 1 := by
    have hlin : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2 : ℂ) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).neg.div_const (2 : ℂ)
    have hc := hlin.const_cpow (Or.inl hpi_ne)
    refine hc.congr_deriv ?_; ring
  have hG_half_ne : Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero fun m h => by
      have hre := congrArg Complex.re h
      simp at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG_half_diff : DifferentiableAt ℂ Complex.Gamma (1 / 2 : ℂ) :=
    Complex.differentiableAt_Gamma (1 / 2 : ℂ) fun m h => by
      have hre := congrArg Complex.re h
      simp at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG_comp : HasDerivAt (fun s : ℂ => Complex.Gamma (s / 2))
      (deriv Complex.Gamma (1 / 2 : ℂ) * (1 / 2 : ℂ)) 1 := by
    have hlin : HasDerivAt (fun s : ℂ => s / 2) (1 / 2 : ℂ) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).div_const (2 : ℂ)
    exact hG_half_diff.hasDerivAt.comp 1 hlin
  have hprod : HasDerivAt Complex.Gammaℝ
      (((Real.pi : ℂ) ^ (-(1 : ℂ) / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2 : ℂ)) *
        Complex.Gamma (1 / 2 : ℂ) +
       (Real.pi : ℂ) ^ (-(1 : ℂ) / 2) * (deriv Complex.Gamma (1 / 2 : ℂ) * (1 / 2 : ℂ))) 1 := by
    refine (hexp_d.mul hG_comp).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    rfl
  rw [hprod.deriv]
  have hGℝ1 : (Real.pi : ℂ) ^ (-(1 : ℂ) / 2) * Complex.Gamma (1 / 2 : ℂ) = 1 := by
    simpa [Complex.Gammaℝ_def] using Complex.Gammaℝ_one
  have hderivG : deriv Complex.Gamma (1 / 2 : ℂ) =
      Complex.digamma (1 / 2 : ℂ) * Complex.Gamma (1 / 2 : ℂ) := by
    rw [Complex.digamma_def, logDeriv_apply, div_mul_cancel₀ _ hG_half_ne]
  have hlog_pi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log hpi_pos.le).symm
  have hlog_4pi : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [Real.log_mul (by norm_num) hpi_pos.ne', h4, Real.log_pow]
    ring
  calc ((Real.pi : ℂ) ^ (-(1 : ℂ) / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2 : ℂ)) *
        Complex.Gamma (1 / 2 : ℂ) +
       (Real.pi : ℂ) ^ (-(1 : ℂ) / 2) * (deriv Complex.Gamma (1 / 2 : ℂ) * (1 / 2 : ℂ))
      = ((Real.pi : ℂ) ^ (-(1 : ℂ) / 2) * Complex.Gamma (1 / 2 : ℂ)) *
          (Complex.log (Real.pi : ℂ) * (-1 / 2 : ℂ) + Complex.digamma (1 / 2 : ℂ) * (1 / 2 : ℂ)) := by
        rw [hderivG]; ring
    _ = (Real.log Real.pi : ℂ) * (-1 / 2 : ℂ) + Complex.digamma (1 / 2 : ℂ) * (1 / 2 : ℂ) := by
        rw [hGℝ1, one_mul, hlog_pi]
    _ = -((Real.eulerMascheroniConstant / 2 + Real.log (4 * Real.pi) / 2 : ℝ) : ℂ) := by
        rw [digamma_half_eq, hlog_4pi]
        push_cast
        ring

/-- Exact derivative of Mathlib's `xi` at `s = 1`:
`deriv xi 1 = ((1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 : ℝ) : ℂ)`. -/
theorem deriv_xi_one :
    deriv xi 1 = ((1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 : ℝ) : ℂ) := by
  let g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  have hg_ne : ∀ w : ℂ, w ≠ 1 → g w = (w - 1) * riemannZeta w := fun w hw => by simp [g, hw]
  have hg1 : g 1 = 1 := by simp [g]
  have hg_diff : Differentiable ℂ g := by
    rw [← differentiableOn_univ,
      ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
    refine ⟨fun z hz => ?_, by simpa only [g, continuousAt_update_same] using riemannZeta_residue_one⟩
    have hz1 : z ≠ 1 := by simpa using hz
    have hev : g =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw using hg_ne w hw
    exact ((DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hz1)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  have hg_deriv1 : deriv g 1 = (Real.eulerMascheroniConstant : ℂ) := by
    have hd := hasDerivAt_iff_tendsto_slope.mp (hg_diff 1).hasDerivAt
    refine tendsto_nhds_unique hd (tendsto_riemannZeta_sub_one_div.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [slope_def_field, hg_ne s hs, hg1]; field_simp
  have hxi_ev : xi =ᶠ[𝓝 (1 : ℂ)] fun s : ℂ => s * s.Gammaℝ * g s := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re)] with s (hs : 0 < s.re)
    by_cases h1 : s = 1
    · subst h1; simp [hg1, Complex.Gammaℝ_one]
    · have h0 : s ≠ 0 := by intro h; simp [h] at hs
      have hG : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
      rw [xi_eq_mul_Gammaℝ_mul_riemannZeta h0 h1 hG, hg_ne s h1]
      ring
  have hGℝ_diff : DifferentiableAt ℂ Complex.Gammaℝ 1 := by
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) 1 :=
      (((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hpi_ne))
    have hG_half_diff : DifferentiableAt ℂ Complex.Gamma (1 / 2 : ℂ) :=
      Complex.differentiableAt_Gamma (1 / 2 : ℂ) fun m h => by
        have hre := congrArg Complex.re h; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) m]
    have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) 1 :=
      hG_half_diff.comp 1 (differentiableAt_id.div_const 2)
    exact h1.mul h2
  have hprod : HasDerivAt (fun s : ℂ => s * s.Gammaℝ * g s)
      ((1 * (1 : ℂ).Gammaℝ + 1 * deriv Complex.Gammaℝ 1) * g 1 + (1 * (1 : ℂ).Gammaℝ) * deriv g 1) 1 :=
    ((hasDerivAt_id (1 : ℂ)).mul hGℝ_diff.hasDerivAt).mul (hg_diff 1).hasDerivAt
  rw [hxi_ev.deriv_eq, hprod.deriv, Complex.Gammaℝ_one, hg1, hg_deriv1, deriv_Gammaℝ_one]
  push_cast
  ring

/-- **Exact Closed-Form Value of the Hadamard Constant `xiHadamardB = deriv xi 0`**:
`xiHadamardB = ((-1 - γ / 2 + log (4 π) / 2 : ℝ) : ℂ)`. -/
theorem xiHadamardB_eq :
    xiHadamardB = ((-1 - Real.eulerMascheroniConstant / 2 + Real.log (4 * Real.pi) / 2 : ℝ) : ℂ) := by
  have h := logDeriv_xi_one_sub 0
  simp only [sub_zero, xi_one, xi_zero, div_one] at h
  have hB : xiHadamardB = -deriv xi 1 := by
    change deriv xi 0 = -deriv xi 1
    rw [h, neg_neg]
  rw [hB, deriv_xi_one]
  push_cast
  ring

/-- **EXACT CLOSED-FORM VALUE OF THE FIRST LI COEFFICIENT `λ₁`**:
`liCoeff 1 = 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2` (`≈ 0.0230957`). -/
theorem liCoeff_one_eq :
    liCoeff 1 = 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 := by
  have h1 := liCoeff_ofReal_eq_tsum 1
  have hterm : ∀ k : ℕ, liPairTerm (xiZeroSeq k) 1 = 1 / xiZeroSeq k + 1 / (1 - xiZeroSeq k) :=
    fun k => liPairTerm_one (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k)
  rw [tsum_congr hterm] at h1
  have hB : (liCoeff 1 : ℂ) = -xiHadamardB := by
    rw [h1, xiHadamardB_eq_neg_half_tsum]; ring
  have hre := congrArg Complex.re hB
  rw [Complex.ofReal_re, Complex.neg_re, xiHadamardB_eq, Complex.ofReal_re] at hre
  linarith

/-- **Unconditional Strict Positivity of `λ₁`** (`0 < liCoeff 1`), proved directly from
`liCoeff 1 = ∑'_k (1 / ρ_k).re` with every term strictly positive (`0 < Re(ρ_k) < 1`)! -/
theorem liCoeff_one_pos : 0 < liCoeff 1 := by
  have hterm : ∀ k : ℕ, (liPairTerm (xiZeroSeq k) 1).re =
      (1 / xiZeroSeq k).re + (1 / (1 - xiZeroSeq k)).re := fun k => by
    rw [liPairTerm_one (xiZeroSeq_ne_zero k) (xiZeroSeq_ne_one k), Complex.add_re]
  have hpos : ∀ k : ℕ, 0 < (liPairTerm (xiZeroSeq k) 1).re := fun k => by
    rw [hterm k]
    have h1 := RHDirect.Stage5JensenHadamard.re_inv_zero_pos (xiZeroSeq_strip k).1
    have h2 := RHDirect.Stage5JensenHadamard.re_inv_zero_pos
      (show 0 < (1 - xiZeroSeq k).re by simp; linarith [(xiZeroSeq_strip k).2])
    linarith
  have hsum_pos : 0 < ∑' k : ℕ, (liPairTerm (xiZeroSeq k) 1).re :=
    lt_of_lt_of_le (hpos 0) ((summable_liPairTerm_re 1).le_tsum 0 fun k _ => (hpos k).le)
  unfold liCoeff
  linarith

/-- Unconditional sharp transcendental inequality `log (4 π) < 2 + γ` as an immediate corollary
of `0 < liCoeff 1`. -/
theorem log_four_pi_lt : Real.log (4 * Real.pi) < 2 + Real.eulerMascheroniConstant := by
  have h := liCoeff_one_pos
  rw [liCoeff_one_eq] at h
  linarith

/-! ## Section 6: Master Bundled Stage 10 Theorem -/

/-- **MASTER UNCONDITIONAL STAGE 10 LI CRITERION THEOREM (`0` ASSUMPTIONS!)**:
bundles all core unconditional results for Li's 1997 criterion directly on Mathlib's
`RiemannHypothesis` and `xi(s)`. -/
theorem stage10_liCriterion_unconditional :
    (RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff n) ∧
    (RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 < liCoeff n) ∧
    (RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeffAnalytic n) ∧
    (∀ n : ℕ, 1 ≤ n → liCoeff n = liCoeffAnalytic n) ∧
    (∀ z : ℂ, ‖z‖ < liMinRadius → HasSum (fun n : ℕ => (liCoeff n : ℂ) * z ^ n) (liGenFun z)) ∧
    (liCoeff 1 = 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2) ∧
    (0 < liCoeff 1) :=
  ⟨riemannHypothesis_iff_liCoeff_nonneg,
   riemannHypothesis_iff_liCoeff_pos,
   riemannHypothesis_iff_liCoeffAnalytic_nonneg,
   fun _ hn => liCoeff_eq_liCoeffAnalytic hn,
   fun _ hz => liCoeff_eq_taylor_logDeriv_cayley hz,
   liCoeff_one_eq,
   liCoeff_one_pos⟩

end RHDirect.Stage10LiCriterion
