import RHDirect.Stage2DirichletAP
import RHDirect.Stage4ClassFieldTheory
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue

/-!
# RHDirect.Stage5DirichletDensity

Compact, self-contained, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of
**Analytic (Dirichlet) Prime Density, Dirichlet's Quantitative Density Theorem for Primes
in Arithmetic Progressions, the Exact Cyclotomic Chebotarev Density Theorem, Subfield
Splitting Density, and the Kronecker–Bauer Uniqueness Theorem for Cyclotomic Extensions**
directly on Mathlib's `CyclotomicField`, `riemannZeta`, and `DirichletCharacter.LFunction`
in pure Mathlib `v4.33.1` (0 external assumptions).

## Contents
1. **Analytic (Dirichlet) Prime Density `HasDirichletDensity S δ`**:
   - `primeDirichletSum S σ := ∑' p : {p : ℕ // p.Prime ∧ p ∈ S}, (p.1 : ℝ) ^ (-σ)` for `σ > 1`
     and `HasDirichletDensity S δ` as the limit as `σ → 1⁺` of
     `primeDirichletSum S σ / Real.log (1 / (σ - 1))`.
   - Unconditional basic laws: summability for `σ > 1`, uniqueness, nonnegativity, upper bound
     `δ ≤ 1`, `hasDirichletDensity_univ` (`δ = 1`), finite-set invariance
     (`hasDirichletDensity_of_symmDiff_finite`), disjoint additivity (binary and finite `Finset`
     unions), monotonicity, complement law (`1 - δ`), **density `> 0 ⇒ S.Infinite`**, and exact
     equivalence with the `Real.log (riemannZeta σ).re` normalization.
2. **Prime-Power Tail Bound & Analytic Residue-Class Asymptotics**:
   - Elementary telescoping bound `∑_{p prime, k ≥ 2} p^(-k σ) ≤ 1` for all `σ ≥ 1`.
   - Exact term-by-term differentiation via `LSeries_hasDerivAt` of the weighted prime-power
     series `residueClassWeight a`, combined with `Stage2DirichletAP.LFunctionResidueClassAux_continuous_and_eq`
     (which builds on `LFunction χ 1 ≠ 0` and `char_orthogonality_indicator_nat`) and the Mean Value
     Theorem on `[σ, 2]` to obtain the sharp uniform `O(1)` bound
     `|primeDirichletSum {p | p ≡ a [MOD m]} σ - (φ(m))⁻¹ log(1 / (σ - 1))| ≤ C` on `(1, 2)`.
3. **Dirichlet's Quantitative Analytic Density Theorem & Cyclotomic Chebotarev Density Theorem**:
   - `hasDirichletDensity_primes_modEq`: exact density `1 / φ(m)` for every `m ≥ 1` and
     `Nat.Coprime a m`.
   - `cyclotomic_chebotarev_density`: exact density `1 / |Gal(ℚ(ζ_m)/ℚ)|` for every Frobenius
     fiber `FrobPrimes m g` via `Stage4ClassFieldTheory.artinMap` and `frobPrime`.
   - `cyclotomic_chebotarev_density_subset` and `cyclotomic_chebotarev_density_subgroup`:
     exact density `|C| / |Gal(ℚ(ζ_m)/ℚ)|` for any subset `C` and `|H| / φ(m) = 1 / [G : H]`
     for any subgroup `H ≤ Gal(ℚ(ζ_m)/ℚ)`.
4. **Subfield Splitting Density & Kronecker–Bauer Uniqueness Theorem for Cyclotomic Extensions**:
   - For any intermediate field `K : IntermediateField ℚ (CycField m)`, define
     `SplitPrimes K := {p | ∃ hp hndvd, frobPrime m hp hndvd ∈ K.fixingSubgroup}`.
   - `hasDirichletDensity_splitPrimes_eq_inv_finrank`: exact splitting density `1 / [K : ℚ]`.
   - `bauer_le_of_splitPrimes_diff_finite`, `bauer_le_iff_splitPrimes_diff_finite`,
     `bauer_eq_iff_splitPrimes_symmDiff_finite`, and their stronger analytic density-zero
     equivalences (`HasDirichletDensity (SplitPrimes K₂ \ SplitPrimes K₁) 0 ↔ K₁ ≤ K₂`,
     `HasDirichletDensity (symmDiff (SplitPrimes K₁) (SplitPrimes K₂)) 0 ↔ K₁ = K₂`).

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex Filter Finset Topology
open RHDirect.Stage2DirichletAP RHDirect.Stage4ClassFieldTheory
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage5DirichletDensity

/-! ## Section 1: Analytic (Dirichlet) Prime Density `HasDirichletDensity` & Basic Laws -/

/-- The prime Dirichlet sum `∑_{p ∈ S, p prime} p^(-σ)` attached to a set `S : Set ℕ`
and a real parameter `σ`. -/
def primeDirichletSum (S : Set ℕ) (σ : ℝ) : ℝ :=
  ∑' p : {p : ℕ // p.Prime ∧ p ∈ S}, (p.1 : ℝ) ^ (-σ)

/-- **Analytic (Dirichlet) Prime Density**: a set `S : Set ℕ` has Dirichlet density `δ : ℝ`
if `primeDirichletSum S σ / Real.log (1 / (σ - 1)) → δ` as `σ → 1⁺`. -/
def HasDirichletDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun σ : ℝ => primeDirichletSum S σ / Real.log (1 / (σ - 1)))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds δ)

/-- Subtype-to-indicator rewrite for `primeDirichletSum`. -/
theorem primeDirichletSum_eq_tsum_indicator (S : Set ℕ) (σ : ℝ) :
    primeDirichletSum S σ =
      ∑' n : ℕ, ({p : ℕ | p.Prime ∧ p ∈ S}).indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n := by
  unfold primeDirichletSum
  exact tsum_subtype ({p : ℕ | p.Prime ∧ p ∈ S}) (fun n : ℕ => (n : ℝ) ^ (-σ))

/-- For `σ > 1`, `n ↦ (n : ℝ) ^ (-σ)` is summable over `ℕ`. -/
theorem summable_nat_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
  have h := Real.summable_nat_rpow_inv.mpr hσ
  refine h.congr fun n => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg n)]

/-- For `σ > 1`, the indicator prime series for any `S : Set ℕ` is summable. -/
theorem summable_primeIndicator (S : Set ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (({p : ℕ | p.Prime ∧ p ∈ S}).indicator (fun n : ℕ => (n : ℝ) ^ (-σ))) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_nat_rpow_neg hσ)
  · by_cases h : n ∈ {p : ℕ | p.Prime ∧ p ∈ S}
    · rw [Set.indicator_of_mem h]
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · rw [Set.indicator_of_notMem h]
  · by_cases h : n ∈ {p : ℕ | p.Prime ∧ p ∈ S}
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- For `σ > 1`, the subtype prime Dirichlet sum is summable for every `S : Set ℕ`. -/
theorem summable_primeDirichletSum (S : Set ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : {p : ℕ // p.Prime ∧ p ∈ S} => (p.1 : ℝ) ^ (-σ)) :=
  (summable_subtype_iff_indicator (s := {p : ℕ | p.Prime ∧ p ∈ S})
    (f := fun n : ℕ => (n : ℝ) ^ (-σ))).mpr (summable_primeIndicator S hσ)

/-- Every prime Dirichlet sum is nonnegative. -/
theorem primeDirichletSum_nonneg (S : Set ℕ) (σ : ℝ) : 0 ≤ primeDirichletSum S σ :=
  tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg p.1) _

/-- `primeDirichletSum ∅ σ = 0`. -/
theorem primeDirichletSum_empty (σ : ℝ) : primeDirichletSum ∅ σ = 0 := by
  rw [primeDirichletSum_eq_tsum_indicator]
  have h : {p : ℕ | p.Prime ∧ p ∈ (∅ : Set ℕ)} = ∅ := by ext; simp
  rw [h, Set.indicator_empty, tsum_zero]

/-- `primeDirichletSum S σ` depends only on the primes contained in `S`. -/
theorem primeDirichletSum_congr_primes {S₁ S₂ : Set ℕ}
    (h : ∀ p : ℕ, p.Prime → (p ∈ S₁ ↔ p ∈ S₂)) (σ : ℝ) :
    primeDirichletSum S₁ σ = primeDirichletSum S₂ σ := by
  rw [primeDirichletSum_eq_tsum_indicator, primeDirichletSum_eq_tsum_indicator]
  have hset : {p : ℕ | p.Prime ∧ p ∈ S₁} = {p : ℕ | p.Prime ∧ p ∈ S₂} := by
    ext p
    exact ⟨fun ⟨hp, h1⟩ => ⟨hp, (h p hp).mp h1⟩, fun ⟨hp, h2⟩ => ⟨hp, (h p hp).mpr h2⟩⟩
  rw [hset]

/-- Monotonicity of `primeDirichletSum` in the prime set `S` for `σ > 1`. -/
theorem primeDirichletSum_mono {S₁ S₂ : Set ℕ} (hsub : S₁ ⊆ S₂) {σ : ℝ} (hσ : 1 < σ) :
    primeDirichletSum S₁ σ ≤ primeDirichletSum S₂ σ := by
  rw [primeDirichletSum_eq_tsum_indicator, primeDirichletSum_eq_tsum_indicator]
  refine (summable_primeIndicator S₁ hσ).tsum_le_tsum (fun n => ?_) (summable_primeIndicator S₂ hσ)
  by_cases h1 : n ∈ {p : ℕ | p.Prime ∧ p ∈ S₁}
  · have h2 : n ∈ {p : ℕ | p.Prime ∧ p ∈ S₂} := ⟨h1.1, hsub h1.2⟩
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : n ∈ {p : ℕ | p.Prime ∧ p ∈ S₂}
    · rw [Set.indicator_of_mem h2]
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · rw [Set.indicator_of_notMem h2]

/-- Disjoint additivity of `primeDirichletSum` for `σ > 1`. -/
theorem primeDirichletSum_union_of_disjoint {S₁ S₂ : Set ℕ} (hdisj : Disjoint S₁ S₂)
    {σ : ℝ} (hσ : 1 < σ) :
    primeDirichletSum (S₁ ∪ S₂) σ = primeDirichletSum S₁ σ + primeDirichletSum S₂ σ := by
  rw [primeDirichletSum_eq_tsum_indicator, primeDirichletSum_eq_tsum_indicator,
    primeDirichletSum_eq_tsum_indicator,
    ← (summable_primeIndicator S₁ hσ).tsum_add (summable_primeIndicator S₂ hσ)]
  congr 1
  funext n
  by_cases hp : n.Prime
  · by_cases h1 : n ∈ S₁
    · have h2 : n ∉ S₂ := Set.disjoint_left.mp hdisj h1
      have hm1 : n ∈ {p : ℕ | p.Prime ∧ p ∈ S₁} := ⟨hp, h1⟩
      have hm2 : n ∉ {p : ℕ | p.Prime ∧ p ∈ S₂} := fun h => h2 h.2
      have hmu : n ∈ {p : ℕ | p.Prime ∧ p ∈ S₁ ∪ S₂} := ⟨hp, Or.inl h1⟩
      rw [Set.indicator_of_mem hmu, Set.indicator_of_mem hm1, Set.indicator_of_notMem hm2, add_zero]
    · by_cases h2 : n ∈ S₂
      · have hm1 : n ∉ {p : ℕ | p.Prime ∧ p ∈ S₁} := fun h => h1 h.2
        have hm2 : n ∈ {p : ℕ | p.Prime ∧ p ∈ S₂} := ⟨hp, h2⟩
        have hmu : n ∈ {p : ℕ | p.Prime ∧ p ∈ S₁ ∪ S₂} := ⟨hp, Or.inr h2⟩
        rw [Set.indicator_of_mem hmu, Set.indicator_of_notMem hm1, Set.indicator_of_mem hm2, zero_add]
      · have hm1 : n ∉ {p : ℕ | p.Prime ∧ p ∈ S₁} := fun h => h1 h.2
        have hm2 : n ∉ {p : ℕ | p.Prime ∧ p ∈ S₂} := fun h => h2 h.2
        have hmu : n ∉ {p : ℕ | p.Prime ∧ p ∈ S₁ ∪ S₂} := fun h => h.2.elim h1 h2
        rw [Set.indicator_of_notMem hmu, Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2,
          add_zero]
  · have hm1 : n ∉ {p : ℕ | p.Prime ∧ p ∈ S₁} := fun h => hp h.1
    have hm2 : n ∉ {p : ℕ | p.Prime ∧ p ∈ S₂} := fun h => hp h.1
    have hmu : n ∉ {p : ℕ | p.Prime ∧ p ∈ S₁ ∪ S₂} := fun h => hp h.1
    rw [Set.indicator_of_notMem hmu, Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2,
      add_zero]

/-- Set-difference additivity of `primeDirichletSum` when `S₁ ⊆ S₂` and `σ > 1`. -/
theorem primeDirichletSum_sdiff_of_subset {S₁ S₂ : Set ℕ} (hsub : S₁ ⊆ S₂) {σ : ℝ} (hσ : 1 < σ) :
    primeDirichletSum (S₂ \ S₁) σ = primeDirichletSum S₂ σ - primeDirichletSum S₁ σ := by
  have hunion : S₁ ∪ (S₂ \ S₁) = S₂ := Set.union_sdiff_cancel hsub
  have hdisj : Disjoint S₁ (S₂ \ S₁) := Set.disjoint_left.mpr fun _ hx h2 => h2.2 hx
  have hadd := primeDirichletSum_union_of_disjoint hdisj hσ
  rw [hunion] at hadd
  linarith

/-- Finite pairwise-disjoint union additivity of `primeDirichletSum` for `σ > 1`. -/
theorem primeDirichletSum_biUnion_finset {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (S : ι → Set ℕ) (hdisj : (I : Set ι).PairwiseDisjoint S) {σ : ℝ} (hσ : 1 < σ) :
    primeDirichletSum (⋃ i ∈ I, S i) σ = ∑ i ∈ I, primeDirichletSum (S i) σ := by
  induction I using Finset.induction_on with
  | empty =>
    simp [primeDirichletSum_empty]
  | insert a s ha ih =>
    have hdisj_s : (s : Set ι).PairwiseDisjoint S :=
      hdisj.subset (by intro x hx; exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx))
    have hdisj_a : Disjoint (S a) (⋃ i ∈ s, S i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_insert_self a s))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi)) hne
    have hunion : (⋃ i ∈ insert a s, S i) = S a ∪ ⋃ i ∈ s, S i := by
      ext n
      simp
    rw [hunion, primeDirichletSum_union_of_disjoint hdisj_a hσ, Finset.sum_insert ha, ih hdisj_s]

/-- For a finite set `S : Set ℕ` and `σ > 1`, `primeDirichletSum S σ ≤ |S|`. -/
theorem primeDirichletSum_le_card_of_finite {S : Set ℕ} (hS : S.Finite) {σ : ℝ} (hσ : 1 < σ) :
    primeDirichletSum S σ ≤ (hS.toFinset.card : ℝ) := by
  rw [primeDirichletSum_eq_tsum_indicator]
  have hsupp : ∀ n ∉ hS.toFinset,
      ({p : ℕ | p.Prime ∧ p ∈ S}).indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n = 0 := by
    intro n hn
    apply Set.indicator_of_notMem
    intro hmem
    exact hn (hS.mem_toFinset.mpr hmem.2)
  rw [tsum_eq_sum hsupp]
  calc ∑ n ∈ hS.toFinset, ({p : ℕ | p.Prime ∧ p ∈ S}).indicator (fun n : ℕ => (n : ℝ) ^ (-σ)) n
      ≤ ∑ _n ∈ hS.toFinset, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        by_cases hmem : n ∈ {p : ℕ | p.Prime ∧ p ∈ S}
        · rw [Set.indicator_of_mem hmem]
          have hge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmem.1.one_le
          exact Real.rpow_le_one_of_one_le_of_nonpos hge1 (by linarith)
        · rw [Set.indicator_of_notMem hmem]
          norm_num
    _ = (hS.toFinset.card : ℝ) := by simp

/-- As `σ → 1⁺`, `Real.log (1 / (σ - 1)) → +∞`. -/
theorem tendsto_log_inv_sub_one_atTop :
    Tendsto (fun σ : ℝ => Real.log (1 / (σ - 1))) (nhdsWithin 1 (Set.Ioi 1)) atTop := by
  have hsub : Tendsto (fun σ : ℝ => σ - 1) (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun σ : ℝ => σ - 1) 1 := (continuous_id.sub continuous_const).continuousAt
      have ht : Tendsto (fun σ : ℝ => σ - 1) (nhds (1 : ℝ)) (nhds (0 : ℝ)) := by
        simpa using hc.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_pos.mpr (Set.mem_Ioi.mp hσ)
  have hinv : Tendsto (fun σ : ℝ => (σ - 1)⁻¹) (nhdsWithin 1 (Set.Ioi 1)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  have hlog : Tendsto (fun σ : ℝ => Real.log ((σ - 1)⁻¹)) (nhdsWithin 1 (Set.Ioi 1)) atTop :=
    Real.tendsto_log_atTop.comp hinv
  simpa only [one_div] using hlog

/-- For every `σ ∈ (1, 2)`, `0 < Real.log (1 / (σ - 1))`. -/
theorem log_inv_sub_one_pos {σ : ℝ} (h1 : 1 < σ) (h2 : σ < 2) :
    0 < Real.log (1 / (σ - 1)) := by
  apply Real.log_pos
  rw [one_lt_div (sub_pos.mpr h1)]
  linarith

/-- Eventually as `σ → 1⁺`, `σ ∈ Set.Ioo 1 2`. -/
theorem eventually_mem_Ioo_one_two :
    ∀ᶠ σ : ℝ in nhdsWithin 1 (Set.Ioi 1), σ ∈ Set.Ioo (1 : ℝ) 2 := by
  have hlt : ∀ᶠ σ : ℝ in nhdsWithin 1 (Set.Ioi 1), σ < 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin, hlt] with σ h1 h2
  exact ⟨h1, h2⟩

/-- Eventually as `σ → 1⁺`, `0 < Real.log (1 / (σ - 1))`. -/
theorem eventually_log_inv_sub_one_pos :
    ∀ᶠ σ : ℝ in nhdsWithin 1 (Set.Ioi 1), 0 < Real.log (1 / (σ - 1)) := by
  filter_upwards [eventually_mem_Ioo_one_two] with σ hσ
  exact log_inv_sub_one_pos hσ.1 hσ.2

/-- For any constant `C : ℝ`, `C / Real.log (1 / (σ - 1)) → 0` as `σ → 1⁺`. -/
theorem tendsto_const_div_log_inv_sub_one (C : ℝ) :
    Tendsto (fun σ : ℝ => C / Real.log (1 / (σ - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
  tendsto_const_nhds.div_atTop tendsto_log_inv_sub_one_atTop

/-- Workhorse density criterion: if `|primeDirichletSum S σ - δ * log(1 / (σ - 1))| ≤ C`
uniformly on `(1, 2)`, then `HasDirichletDensity S δ`. -/
theorem hasDirichletDensity_of_bounded_sub {S : Set ℕ} {δ C : ℝ}
    (hbound : ∀ σ ∈ Set.Ioo (1 : ℝ) 2,
      |primeDirichletSum S σ - δ * Real.log (1 / (σ - 1))| ≤ C) :
    HasDirichletDensity S δ := by
  unfold HasDirichletDensity
  have h0 : Tendsto (fun σ : ℝ => primeDirichletSum S σ / Real.log (1 / (σ - 1)) - δ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_log_inv_sub_one C)
    filter_upwards [eventually_mem_Ioo_one_two] with σ hσ
    have hlog_pos : 0 < Real.log (1 / (σ - 1)) := log_inv_sub_one_pos hσ.1 hσ.2
    rw [Real.norm_eq_abs]
    have hrew : primeDirichletSum S σ / Real.log (1 / (σ - 1)) - δ =
        (primeDirichletSum S σ - δ * Real.log (1 / (σ - 1))) / Real.log (1 / (σ - 1)) := by
      field_simp [hlog_pos.ne']
    rw [hrew, abs_div, abs_of_pos hlog_pos]
    exact div_le_div_of_nonneg_right (hbound σ hσ) hlog_pos.le
  simpa using h0.add_const δ

/-- Uniqueness of analytic (Dirichlet) prime density. -/
theorem hasDirichletDensity_unique {S : Set ℕ} {δ₁ δ₂ : ℝ}
    (h₁ : HasDirichletDensity S δ₁) (h₂ : HasDirichletDensity S δ₂) :
    δ₁ = δ₂ := by
  have : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique h₁ h₂

/-- `HasDirichletDensity` depends only on the primes contained in `S`. -/
theorem hasDirichletDensity_congr_primes {S₁ S₂ : Set ℕ} {δ : ℝ}
    (h : ∀ p : ℕ, p.Prime → (p ∈ S₁ ↔ p ∈ S₂)) :
    HasDirichletDensity S₁ δ ↔ HasDirichletDensity S₂ δ := by
  unfold HasDirichletDensity
  have heq : (fun σ : ℝ => primeDirichletSum S₁ σ / Real.log (1 / (σ - 1))) =
      (fun σ : ℝ => primeDirichletSum S₂ σ / Real.log (1 / (σ - 1))) := by
    funext σ
    rw [primeDirichletSum_congr_primes h σ]
  rw [heq]

/-- The empty set has Dirichlet density `0`. -/
theorem hasDirichletDensity_empty : HasDirichletDensity ∅ 0 := by
  unfold HasDirichletDensity
  simp only [primeDirichletSum_empty, zero_div]
  exact tendsto_const_nhds

/-- Every finite set has Dirichlet density `0`. -/
theorem hasDirichletDensity_of_finite {S : Set ℕ} (hS : S.Finite) :
    HasDirichletDensity S 0 := by
  refine hasDirichletDensity_of_bounded_sub (C := (hS.toFinset.card : ℝ)) fun σ hσ => ?_
  rw [zero_mul, sub_zero, abs_of_nonneg (primeDirichletSum_nonneg S σ)]
  exact primeDirichletSum_le_card_of_finite hS hσ.1

/-- Every Dirichlet density is nonnegative. -/
theorem hasDirichletDensity_nonneg {S : Set ℕ} {δ : ℝ} (h : HasDirichletDensity S δ) :
    0 ≤ δ := by
  have : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  refine ge_of_tendsto h ?_
  filter_upwards [eventually_log_inv_sub_one_pos] with σ hlog
  exact div_nonneg (primeDirichletSum_nonneg S σ) hlog.le

/-- Monotonicity of Dirichlet density: `S₁ ⊆ S₂` implies `δ₁ ≤ δ₂`. -/
theorem hasDirichletDensity_mono {S₁ S₂ : Set ℕ} {δ₁ δ₂ : ℝ} (hsub : S₁ ⊆ S₂)
    (h₁ : HasDirichletDensity S₁ δ₁) (h₂ : HasDirichletDensity S₂ δ₂) :
    δ₁ ≤ δ₂ := by
  have : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  refine le_of_tendsto_of_tendsto h₁ h₂ ?_
  filter_upwards [self_mem_nhdsWithin, eventually_log_inv_sub_one_pos] with σ hσ hlog
  exact div_le_div_of_nonneg_right (primeDirichletSum_mono hsub hσ) hlog.le

/-- Disjoint additivity of Dirichlet density. -/
theorem hasDirichletDensity_union_of_disjoint {S₁ S₂ : Set ℕ} {δ₁ δ₂ : ℝ}
    (hdisj : Disjoint S₁ S₂)
    (h₁ : HasDirichletDensity S₁ δ₁) (h₂ : HasDirichletDensity S₂ δ₂) :
    HasDirichletDensity (S₁ ∪ S₂) (δ₁ + δ₂) := by
  unfold HasDirichletDensity at h₁ h₂ ⊢
  refine (h₁.add h₂).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [primeDirichletSum_union_of_disjoint hdisj hσ, add_div]

/-- Set-difference additivity of Dirichlet density when `S₁ ⊆ S₂`. -/
theorem hasDirichletDensity_sdiff_of_subset {S₁ S₂ : Set ℕ} {δ₁ δ₂ : ℝ}
    (hsub : S₁ ⊆ S₂)
    (h₁ : HasDirichletDensity S₁ δ₁) (h₂ : HasDirichletDensity S₂ δ₂) :
    HasDirichletDensity (S₂ \ S₁) (δ₂ - δ₁) := by
  unfold HasDirichletDensity at h₁ h₂ ⊢
  refine (h₂.sub h₁).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [primeDirichletSum_sdiff_of_subset hsub hσ, sub_div]

/-- Finite pairwise-disjoint union additivity of Dirichlet density. -/
theorem hasDirichletDensity_biUnion_finset {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (S : ι → Set ℕ) (δ : ι → ℝ) (hdisj : (I : Set ι).PairwiseDisjoint S)
    (h : ∀ i ∈ I, HasDirichletDensity (S i) (δ i)) :
    HasDirichletDensity (⋃ i ∈ I, S i) (∑ i ∈ I, δ i) := by
  unfold HasDirichletDensity
  have hsum : Tendsto (fun σ : ℝ => ∑ i ∈ I, primeDirichletSum (S i) σ / Real.log (1 / (σ - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (∑ i ∈ I, δ i)) :=
    tendsto_finsetSum I fun i hi => h i hi
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [← Finset.sum_div, primeDirichletSum_biUnion_finset I S hdisj hσ]

/-- **Finite-Set Invariance of Dirichlet Density**: if `symmDiff S₁ S₂` is finite, then
`HasDirichletDensity S₁ δ → HasDirichletDensity S₂ δ`. -/
theorem hasDirichletDensity_of_symmDiff_finite {S₁ S₂ : Set ℕ} {δ : ℝ}
    (hfin : (symmDiff S₁ S₂).Finite) (h₁ : HasDirichletDensity S₁ δ) :
    HasDirichletDensity S₂ δ := by
  have hfin12 : (S₁ \ S₂).Finite := hfin.subset Set.subset_union_left
  have hfin21 : (S₂ \ S₁).Finite := hfin.subset Set.subset_union_right
  have hinter : HasDirichletDensity (S₁ ∩ S₂) δ := by
    have heq : S₁ \ (S₁ \ S₂) = S₁ ∩ S₂ := Set.sdiff_sdiff_right_self S₁ S₂
    have hsub : S₁ \ S₂ ⊆ S₁ := Set.sdiff_subset
    have hd := hasDirichletDensity_sdiff_of_subset hsub (hasDirichletDensity_of_finite hfin12) h₁
    rwa [heq, sub_zero] at hd
  have hdisj : Disjoint (S₁ ∩ S₂) (S₂ \ S₁) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hx2.2 hx1.1
  have hunion : (S₁ ∩ S₂) ∪ (S₂ \ S₁) = S₂ := by
    ext x
    by_cases h : x ∈ S₁ <;> simp [h]
  have hres := hasDirichletDensity_union_of_disjoint hdisj hinter
    (hasDirichletDensity_of_finite hfin21)
  rwa [hunion, add_zero] at hres

/-- Cofinite equivalence of Dirichlet density. -/
theorem hasDirichletDensity_congr_cofinite {S₁ S₂ : Set ℕ} {δ : ℝ}
    (hfin : (symmDiff S₁ S₂).Finite) :
    HasDirichletDensity S₁ δ ↔ HasDirichletDensity S₂ δ :=
  ⟨hasDirichletDensity_of_symmDiff_finite hfin,
   hasDirichletDensity_of_symmDiff_finite (symmDiff_comm S₁ S₂ ▸ hfin)⟩

/-- Monotonicity up to a finite exception set: if `(S₁ \ S₂).Finite`, then `δ₁ ≤ δ₂`. -/
theorem hasDirichletDensity_le_of_diff_finite {S₁ S₂ : Set ℕ} {δ₁ δ₂ : ℝ}
    (hfin : (S₁ \ S₂).Finite)
    (h₁ : HasDirichletDensity S₁ δ₁) (h₂ : HasDirichletDensity S₂ δ₂) :
    δ₁ ≤ δ₂ := by
  have hsym : (symmDiff S₁ (S₁ ∩ S₂)).Finite := by
    have heq : symmDiff S₁ (S₁ ∩ S₂) = S₁ \ S₂ := by
      ext x; simp [symmDiff]; tauto
    rwa [heq]
  have hinter : HasDirichletDensity (S₁ ∩ S₂) δ₁ :=
    hasDirichletDensity_of_symmDiff_finite hsym h₁
  exact hasDirichletDensity_mono Set.inter_subset_right hinter h₂

/-- **Positive Dirichlet Density Implies Infinitude** (for the prime subset `{p ∈ S | p.Prime}`). -/
theorem infinite_primes_of_hasDirichletDensity_pos {S : Set ℕ} {δ : ℝ}
    (h : HasDirichletDensity S δ) (hδ : 0 < δ) :
    {p : ℕ | p.Prime ∧ p ∈ S}.Infinite := by
  intro hfin
  have h0 : HasDirichletDensity {p : ℕ | p.Prime ∧ p ∈ S} 0 := hasDirichletDensity_of_finite hfin
  have hδ' : HasDirichletDensity {p : ℕ | p.Prime ∧ p ∈ S} δ :=
    (hasDirichletDensity_congr_primes (fun p hp => by simp [hp])).mp h
  have heq : δ = 0 := hasDirichletDensity_unique hδ' h0
  linarith

/-- **Positive Dirichlet Density Implies `S.Infinite`**. -/
theorem infinite_of_hasDirichletDensity_pos {S : Set ℕ} {δ : ℝ}
    (h : HasDirichletDensity S δ) (hδ : 0 < δ) :
    S.Infinite :=
  (infinite_primes_of_hasDirichletDensity_pos h hδ).mono (fun _ hx => hx.2)

/-! ## Section 2: Prime-Power Tail Bound & Exact Analytic Residue-Class Asymptotics -/

/-- Prime-power weight `Λ(n) / log n`: equals `1` at primes `p`, `1/k` at prime powers `p^k`
(`k ≥ 1`), and `0` elsewhere. -/
def primePowWeight (n : ℕ) : ℝ :=
  Λ n / Real.log (n : ℝ)

theorem primePowWeight_zero : primePowWeight 0 = 0 := by
  simp [primePowWeight]

theorem primePowWeight_one : primePowWeight 1 = 0 := by
  simp [primePowWeight, ArithmeticFunction.vonMangoldt_apply_one]

theorem primePowWeight_prime {p : ℕ} (hp : p.Prime) : primePowWeight p = 1 := by
  unfold primePowWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  exact div_self hlog

theorem primePowWeight_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    primePowWeight (p ^ k) = (k : ℝ)⁻¹ := by
  unfold primePowWeight
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp,
    Nat.cast_pow, Real.log_pow]
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  field_simp [hlog, hkR]

theorem primePowWeight_of_not_isPrimePow {n : ℕ} (hn : ¬ IsPrimePow n) :
    primePowWeight n = 0 := by
  unfold primePowWeight
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]

theorem primePowWeight_nonneg (n : ℕ) : 0 ≤ primePowWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

theorem primePowWeight_le_one (n : ℕ) : primePowWeight n ≤ 1 := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [primePowWeight_prime_pow hp hkpos.ne']
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hkpos)
  · rw [primePowWeight_of_not_isPrimePow hpp]
    norm_num

theorem log_mul_primePowWeight (n : ℕ) :
    Real.log (n : ℝ) * primePowWeight n = Λ n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [primePowWeight_zero]
  · rcases eq_or_ne n 1 with rfl | hn1
    · simp [primePowWeight_one, ArithmeticFunction.vonMangoldt_apply_one]
    · have hge2 : (1 : ℝ) < (n : ℝ) := by
        have : 1 < n := by omega
        exact_mod_cast this
      have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hge2).ne'
      unfold primePowWeight
      exact mul_div_cancel₀ _ hlog

private lemma sum_biUnion_le_of_nonneg_real {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion :
        ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := t a ∩ s.biUnion t) (f := f) fun b _ => hf b]
    linarith

private lemma geom_Icc_two_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, r ^ k ≤ r ^ 2 / (1 - r) := by
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  rw [le_div_iff₀ h1r]
  induction N with
  | zero =>
    simp; positivity
  | succ m ih =>
    by_cases hm : m < 1
    · have hIcc : Finset.Icc 2 (m + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hIcc, Finset.sum_empty, zero_mul]
      positivity
    · by_cases hm1 : m = 1
      · subst hm1
        have hIcc : Finset.Icc 2 2 = {2} := by decide
        rw [hIcc, Finset.sum_singleton]
        nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hr0]
      · have hm2 : 2 ≤ m + 1 := by omega
        have hsum : ∑ k ∈ Finset.Icc 2 (m + 1), r ^ k =
            (∑ k ∈ Finset.Icc 2 m, r ^ k) + r ^ (m + 1) := by
          have hmem : m + 1 ∉ Finset.Icc 2 m := by simp
          have hset : insert (m + 1) (Finset.Icc 2 m) = Finset.Icc 2 (m + 1) := by
            ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
          rw [← hset, Finset.sum_insert hmem, add_comm]
        -- Direct telescoping: (∑_{k=2}^N r^k) * (1 - r) = r^2 - r^(N+1) ≤ r^2
        have htel : ∀ M : ℕ, 2 ≤ M →
            (∑ k ∈ Finset.Icc 2 M, r ^ k) * (1 - r) = r ^ 2 - r ^ (M + 1) := by
          intro M hM
          induction M, hM using Nat.le_induction with
          | base =>
            have h22 : Finset.Icc 2 2 = {2} := by decide
            rw [h22, Finset.sum_singleton]
            ring
          | succ n hn ihn =>
            have hmem' : n + 1 ∉ Finset.Icc 2 n := by simp
            have hset' : insert (n + 1) (Finset.Icc 2 n) = Finset.Icc 2 (n + 1) := by
              ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
            rw [← hset', Finset.sum_insert hmem', add_mul, ihn]
            ring
        rw [htel (m + 1) hm2]
        linarith [pow_nonneg hr0 (m + 2)]

private lemma telescoping_inv_Icc_le_one (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) ≤ 1 := by
  by_cases hN : N < 2
  · have hE : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hE, Finset.sum_empty]
    norm_num
  · push Not at hN
    have htel : ∀ M : ℕ, 2 ≤ M →
        ∑ n ∈ Finset.Icc 2 M, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) = 1 - 1 / (M : ℝ) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base =>
        have h22 : Finset.Icc 2 2 = {2} := by decide
        rw [h22, Finset.sum_singleton]
        norm_num
      | succ n hn ihn =>
        have hmem : n + 1 ∉ Finset.Icc 2 n := by simp
        have hset : insert (n + 1) (Finset.Icc 2 n) = Finset.Icc 2 (n + 1) := by
          ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
        rw [← hset, Finset.sum_insert hmem, ihn]
        push_cast
        ring
    rw [htel N hN]
    have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith

/-- **Unconditional Proper Prime-Power Tail Bound**:
for every real `σ ≥ 1`, `∑_{n = p^k, k ≥ 2} n^(-σ) ≤ 1`. -/
theorem properPrimePowTail_le_one {σ : ℝ} (hσ : 1 ≤ σ) :
    ∑' n : ℕ, (if IsPrimePow n ∧ ¬ n.Prime then (n : ℝ) ^ (-σ) else 0) ≤ 1 := by
  refine Real.tsum_le_of_sum_range_le (fun n => by
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact le_rfl) fun N => ?_
  rw [← Finset.sum_filter]
  set S := (Finset.range N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
  set P := (Finset.Icc 2 N).filter Nat.Prime
  have hsub : S ⊆ P.biUnion (fun p => (Finset.Icc 2 N).image (fun k => p ^ k)) := by
    intro n hn
    simp only [S, P, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc] at hn ⊢
    obtain ⟨hnN, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at hnp
      exact hnp hp
    have hpN : p ≤ N := by
      have hp_le_pk : p ≤ p ^ k := Nat.le_self_pow hkpos.ne' p
      omega
    have hkN : k ≤ N := by
      have h2k : k < 2 ^ k := Nat.lt_two_pow_self
      have h2pk : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      omega
    exact ⟨p, ⟨⟨hp.two_le, hpN⟩, hp⟩, k, ⟨hk2, hkN⟩, rfl⟩
  calc ∑ n ∈ S, (n : ℝ) ^ (-σ)
      ≤ ∑ n ∈ S, (n : ℝ)⁻¹ := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hpp : IsPrimePow n := (Finset.mem_filter.mp hn).2.1
        have hge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpp.one_lt.le
        have hpow : (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hge1 (by linarith)
        simpa [Real.rpow_neg_one] using hpow
    _ ≤ ∑ n ∈ P.biUnion (fun p => (Finset.Icc 2 N).image (fun k => p ^ k)), (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ ∑ p ∈ P, ∑ n ∈ (Finset.Icc 2 N).image (fun k => p ^ k), (n : ℝ)⁻¹ :=
        sum_biUnion_le_of_nonneg_real _ _ (fun n : ℕ => (n : ℝ)⁻¹)
          (fun n : ℕ => inv_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ ∑ p ∈ P, ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k := by
        refine Finset.sum_le_sum fun p _ => ?_
        calc ∑ n ∈ (Finset.Icc 2 N).image (fun k => p ^ k), (n : ℝ)⁻¹
            ≤ ∑ k ∈ Finset.Icc 2 N, ((p ^ k : ℕ) : ℝ)⁻¹ :=
              Finset.sum_image_le_of_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
          _ = ∑ k ∈ Finset.Icc 2 N, ((p : ℝ)⁻¹) ^ k := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Nat.cast_pow, inv_pow]
    _ ≤ ∑ p ∈ P, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
        have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
        have hgeom := geom_Icc_two_le hr0 hr1 N
        have halg : ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) = 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) := by
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp [hp0, hp1]
          ring
        linarith
    _ ≤ ∑ n ∈ Finset.Icc 2 N, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n hn _ => ?_
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hpos1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        have hle : 1 / (n : ℝ) ≤ 1 / ((n : ℝ) - 1) :=
          one_div_le_one_div_of_le hpos1 (by linarith)
        linarith
    _ ≤ 1 := telescoping_inv_Icc_le_one N

/-- Weighted residue-class prime-power arithmetic function:
`n ↦ if (n : ZMod m) = a then Λ(n) / log n else 0` (viewed in `ℂ`). -/
def residueClassWeight {m : ℕ} (a : ZMod m) (n : ℕ) : ℂ :=
  ((if (n : ZMod m) = a then primePowWeight n else 0 : ℝ) : ℂ)

theorem norm_residueClassWeight_le_one {m : ℕ} (a : ZMod m) (n : ℕ) :
    ‖residueClassWeight a n‖ ≤ 1 := by
  unfold residueClassWeight
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · rw [abs_of_nonneg (primePowWeight_nonneg n)]
    exact primePowWeight_le_one n
  · simp

theorem LSeriesSummable_residueClassWeight {m : ℕ} (a : ZMod m) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (residueClassWeight a) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_residueClassWeight_le_one a n) hs

theorem abscissaOfAbsConv_residueClassWeight_le_one {m : ℕ} (a : ZMod m) :
    LSeries.abscissaOfAbsConv (residueClassWeight a) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact LSeriesSummable_residueClassWeight a (by simpa using hy)

/-- Exact identity `LSeries.logMul (residueClassWeight a) n = (residueClass a n : ℂ)` for all `n`. -/
theorem logMul_residueClassWeight {m : ℕ} (a : ZMod m) (n : ℕ) :
    LSeries.logMul (residueClassWeight a) n =
      (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ) := by
  change Complex.log (n : ℂ) * residueClassWeight a n =
    (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)
  unfold residueClassWeight ArithmeticFunction.vonMangoldt.residueClass
  have hlogC : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlogC]
  by_cases hmod : (n : ZMod m) = a
  · have hmem : n ∈ {k : ℕ | (k : ZMod m) = a} := hmod
    rw [if_pos hmod, Set.indicator_of_mem hmem, ← Complex.ofReal_mul, log_mul_primePowWeight]
  · have hmem : n ∉ {k : ℕ | (k : ZMod m) = a} := hmod
    rw [if_neg hmod, Set.indicator_of_notMem hmem, Complex.ofReal_zero, mul_zero]

/-- Exact real derivative of `(LSeries (residueClassWeight a) σ).re` on `(1, ∞)`:
it equals `-(LSeries (residueClass a) σ).re`. -/
theorem hasDerivAt_re_LSeries_residueClassWeight {m : ℕ} (a : ZMod m) {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt (fun x : ℝ => (LSeries (residueClassWeight a) (x : ℂ)).re)
      (-(LSeries (fun n => (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) (σ : ℂ)).re) σ := by
  have habs : LSeries.abscissaOfAbsConv (residueClassWeight a) < ((σ : ℂ).re : EReal) := by
    refine lt_of_le_of_lt (abscissaOfAbsConv_residueClassWeight_le_one a) ?_
    rw [Complex.ofReal_re]
    exact EReal.coe_lt_coe_iff.mpr hσ
  have hC : HasDerivAt (LSeries (residueClassWeight a))
      (-LSeries (LSeries.logMul (residueClassWeight a)) (σ : ℂ)) (σ : ℂ) :=
    LSeries_hasDerivAt habs
  have hfun : LSeries.logMul (residueClassWeight a) =
      (fun n => (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) :=
    funext (logMul_residueClassWeight a)
  rw [hfun] at hC
  have hR : HasDerivAt (fun x : ℝ => LSeries (residueClassWeight a) (x : ℂ))
      (-LSeries (fun n => (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) (σ : ℂ)) σ :=
    hC.comp_ofReal
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt σ hR
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.neg_re] using hre

/-- Explicit real-series formula for `(LSeries (residueClassWeight a) (σ : ℂ)).re` when `σ > 1`. -/
theorem re_LSeries_residueClassWeight_eq_tsum {m : ℕ} (a : ZMod m) {σ : ℝ} (hσ : 1 < σ) :
    (LSeries (residueClassWeight a) (σ : ℂ)).re =
      ∑' n : ℕ, (if (n : ZMod m) = a then primePowWeight n else 0) * (n : ℝ) ^ (-σ) := by
  unfold LSeries
  have hsum : Summable (LSeries.term (residueClassWeight a) (σ : ℂ)) :=
    LSeriesSummable_residueClassWeight a (by simpa using hσ)
  rw [Complex.re_tsum hsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [LSeries.term_zero, primePowWeight_zero]
  · rw [LSeries.term_of_ne_zero hn0, residueClassWeight]
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re, div_eq_mul_inv,
      ← Real.rpow_neg (Nat.cast_nonneg n)]

/-- Comparison between `(LSeries (residueClassWeight a) σ).re` and `primeDirichletSum`:
their difference is the proper prime-power contribution, lying unconditionally in `[0, 1]`. -/
theorem re_LSeries_residueClassWeight_sub_primeDirichletSum_bounds {m a : ℕ} {σ : ℝ}
    (hσ : 1 < σ) :
    0 ≤ (LSeries (residueClassWeight (a : ZMod m)) (σ : ℂ)).re -
          primeDirichletSum {p : ℕ | p ≡ a [MOD m]} σ ∧
      (LSeries (residueClassWeight (a : ZMod m)) (σ : ℂ)).re -
          primeDirichletSum {p : ℕ | p ≡ a [MOD m]} σ ≤ 1 := by
  rw [re_LSeries_residueClassWeight_eq_tsum (a : ZMod m) hσ, primeDirichletSum_eq_tsum_indicator]
  have hsum_full :
      Summable (fun n : ℕ =>
        (if (n : ZMod m) = (a : ZMod m) then primePowWeight n else 0) * (n : ℝ) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_nat_rpow_neg hσ)
    · refine mul_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      split_ifs <;> [exact primePowWeight_nonneg n; exact le_rfl]
    · calc (if (n : ZMod m) = (a : ZMod m) then primePowWeight n else 0) * (n : ℝ) ^ (-σ)
          ≤ 1 * (n : ℝ) ^ (-σ) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
            split_ifs <;> [exact primePowWeight_le_one n; norm_num]
        _ = (n : ℝ) ^ (-σ) := one_mul _
  have hsum_prime :
      Summable (({p : ℕ | p.Prime ∧ p ∈ {p : ℕ | p ≡ a [MOD m]}}).indicator
        (fun n : ℕ => (n : ℝ) ^ (-σ))) :=
    summable_primeIndicator {p : ℕ | p ≡ a [MOD m]} hσ
  rw [← hsum_full.tsum_sub hsum_prime]
  have hsum_tail :
      Summable (fun n : ℕ => if IsPrimePow n ∧ ¬ n.Prime then (n : ℝ) ^ (-σ) else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_nat_rpow_neg hσ)
    · split_ifs <;> [exact Real.rpow_nonneg (Nat.cast_nonneg n) _; exact le_rfl]
    · split_ifs <;> [exact le_rfl; exact Real.rpow_nonneg (Nat.cast_nonneg n) _]
  have hterm_bounds : ∀ n : ℕ,
      0 ≤ (if (n : ZMod m) = (a : ZMod m) then primePowWeight n else 0) * (n : ℝ) ^ (-σ) -
            ({p : ℕ | p.Prime ∧ p ∈ {p : ℕ | p ≡ a [MOD m]}}).indicator
              (fun n : ℕ => (n : ℝ) ^ (-σ)) n ∧
        (if (n : ZMod m) = (a : ZMod m) then primePowWeight n else 0) * (n : ℝ) ^ (-σ) -
            ({p : ℕ | p.Prime ∧ p ∈ {p : ℕ | p ≡ a [MOD m]}}).indicator
              (fun n : ℕ => (n : ℝ) ^ (-σ)) n ≤
          (if IsPrimePow n ∧ ¬ n.Prime then (n : ℝ) ^ (-σ) else 0) := by
    intro n
    have hmod_iff : (n : ZMod m) = (a : ZMod m) ↔ n ≡ a [MOD m] := ZMod.natCast_eq_natCast_iff n a m
    by_cases hp : n.Prime
    · by_cases hmod : (n : ZMod m) = (a : ZMod m)
      · have hmem : n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | p ≡ a [MOD m]}} := ⟨hp, hmod_iff.mp hmod⟩
        rw [if_pos hmod, primePowWeight_prime hp, one_mul, Set.indicator_of_mem hmem, sub_self,
          if_neg (fun h => h.2 hp)]
        exact ⟨le_rfl, le_rfl⟩
      · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | p ≡ a [MOD m]}} :=
          fun h => hmod (hmod_iff.mpr h.2)
        rw [if_neg hmod, zero_mul, Set.indicator_of_notMem hmem, sub_self,
          if_neg (fun h => h.2 hp)]
        exact ⟨le_rfl, le_rfl⟩
    · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | p ≡ a [MOD m]}} := fun h => hp h.1
      rw [Set.indicator_of_notMem hmem, sub_zero]
      by_cases hpp : IsPrimePow n
      · have hite : (if IsPrimePow n ∧ ¬ n.Prime then (n : ℝ) ^ (-σ) else 0) = (n : ℝ) ^ (-σ) :=
          if_pos ⟨hpp, hp⟩
        rw [hite]
        constructor
        · refine mul_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          split_ifs <;> [exact primePowWeight_nonneg n; exact le_rfl]
        · calc (if (n : ZMod m) = (a : ZMod m) then primePowWeight n else 0) * (n : ℝ) ^ (-σ)
              ≤ 1 * (n : ℝ) ^ (-σ) := by
                refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
                split_ifs <;> [exact primePowWeight_le_one n; norm_num]
            _ = (n : ℝ) ^ (-σ) := one_mul _
      · have hite : (if IsPrimePow n ∧ ¬ n.Prime then (n : ℝ) ^ (-σ) else 0) = 0 :=
          if_neg (fun h => hpp h.1)
        rw [hite, primePowWeight_of_not_isPrimePow hpp]
        split_ifs <;> simp
  refine ⟨tsum_nonneg fun n => (hterm_bounds n).1, ?_⟩
  exact ((hsum_full.sub hsum_prime).tsum_le_tsum (fun n => (hterm_bounds n).2) hsum_tail).trans
    (properPrimePowTail_le_one hσ.le)

/-- **Uniform `O(1)` Analytic Asymptotic for `LSeries (residueClassWeight a)` on `(1, 2)`**:
proved unconditionally from `Stage2DirichletAP.LFunctionResidueClassAux_continuous_and_eq`
(encoding `LFunction χ 1 ≠ 0` and `char_orthogonality_indicator_nat`), `LSeries_hasDerivAt`,
and the Mean Value Theorem on `[σ, 2]`. -/
theorem exists_bound_re_LSeries_residueClassWeight_sub_log {m : ℕ} [NeZero m]
    {a : ZMod m} (ha : IsUnit a) :
    ∃ C : ℝ, ∀ σ ∈ Set.Ioo (1 : ℝ) 2,
      |(LSeries (residueClassWeight a) (σ : ℂ)).re -
          (m.totient : ℝ)⁻¹ * Real.log (1 / (σ - 1))| ≤ C := by
  obtain ⟨hcont, heqOn⟩ := LFunctionResidueClassAux_continuous_and_eq ha
  let g : ℝ → ℝ := fun x => -(ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux a (x : ℂ)).re
  have hg_cont : ContinuousOn g (Set.Icc (1 : ℝ) 2) := by
    have hmaps : Set.MapsTo (fun x : ℝ => (x : ℂ)) (Set.Icc (1 : ℝ) 2) {s : ℂ | 1 ≤ s.re} :=
      fun x hx => by simpa using hx.1
    have hcomp := hcont.comp Complex.continuous_ofReal.continuousOn hmaps
    exact (Complex.continuous_re.comp_continuousOn hcomp).neg
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg_cont
  let D : ℝ → ℝ := fun x =>
    (LSeries (residueClassWeight a) (x : ℂ)).re - (m.totient : ℝ)⁻¹ * Real.log (1 / (x - 1))
  have hD_deriv : ∀ x : ℝ, 1 < x → HasDerivAt D (g x) x := by
    intro x hx
    have h1 := hasDerivAt_re_LSeries_residueClassWeight a hx
    have hxsub : x - 1 ≠ 0 := (sub_pos.mpr hx).ne'
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 / (t - 1))) (-(x - 1)⁻¹) x := by
      have hlog_sub : HasDerivAt (fun t : ℝ => -Real.log (t - 1)) (-(x - 1)⁻¹) x := by
        have hsub : HasDerivAt (fun t : ℝ => t - 1) 1 x := (hasDerivAt_id x).sub_const 1
        have h1 : HasDerivAt (fun t : ℝ => Real.log (t - 1)) (x - 1)⁻¹ x := by
          have hcomp := (Real.hasDerivAt_log hxsub).comp x hsub
          rw [mul_one] at hcomp
          exact hcomp
        exact h1.neg
      refine hlog_sub.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with t ht
      rw [one_div, Real.log_inv]
    have h2 : HasDerivAt (fun t : ℝ => (m.totient : ℝ)⁻¹ * Real.log (1 / (t - 1)))
        (-((m.totient : ℝ)⁻¹ / (x - 1))) x := by
      have h := hlog.const_mul (m.totient : ℝ)⁻¹
      rwa [mul_neg, ← div_eq_mul_inv] at h
    have hsubD := h1.sub h2
    have haux := heqOn (show (1 : ℝ) < (x : ℂ).re by simpa using hx)
    have hval : -(LSeries (fun n => (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) (x : ℂ)).re -
        -((m.totient : ℝ)⁻¹ / (x - 1)) = g x := by
      dsimp only [g]
      rw [← haux, Complex.sub_re]
      have hpole : (((m.totient : ℂ)⁻¹ / ((x : ℂ) - 1)).re) = (m.totient : ℝ)⁻¹ / (x - 1) := by
        have hrew : (m.totient : ℂ)⁻¹ / ((x : ℂ) - 1) = (((m.totient : ℝ)⁻¹ / (x - 1) : ℝ) : ℂ) := by
          push_cast; rfl
        rw [hrew, Complex.ofReal_re]
      rw [hpole]
      ring
    rwa [hval] at hsubD
  refine ⟨|D 2| + max M 0, fun σ hσ => ?_⟩
  have hconv : Convex ℝ (Set.Icc σ 2) := convex_Icc σ 2
  have hderiv_on : ∀ x ∈ Set.Icc σ 2, HasDerivWithinAt D (g x) (Set.Icc σ 2) x :=
    fun x hx => (hD_deriv x (lt_of_lt_of_le hσ.1 hx.1)).hasDerivWithinAt
  have hbound_on : ∀ x ∈ Set.Icc σ 2, ‖g x‖ ≤ max M 0 :=
    fun x hx => (hM x ⟨(hσ.1.trans_le hx.1).le, hx.2⟩).trans (le_max_left M 0)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv_on hbound_on hconv
    (Set.left_mem_Icc.mpr hσ.2.le) (Set.right_mem_Icc.mpr hσ.2.le)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hdist : |2 - σ| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [hσ.2])]
    linarith [hσ.1]
  have hdiff : |D 2 - D σ| ≤ max M 0 :=
    hmvt.trans (by nlinarith [le_max_right M 0, hdist])
  have htri : |D σ| ≤ |D 2| + |D 2 - D σ| := by
    calc |D σ| = |D 2 - (D 2 - D σ)| := by ring_nf
      _ ≤ |D 2| + |D 2 - D σ| := abs_sub _ _
  linarith

/-- **Uniform `O(1)` Prime-Sum Asymptotic in Every Coprime Residue Class**:
for every `m ≥ 1` (`[NeZero m]`) and `Nat.Coprime a m`,
`|∑_{p ≡ a [MOD m]} p^(-σ) - φ(m)⁻¹ log(1 / (σ - 1))| ≤ C` on `(1, 2)`. -/
theorem exists_bound_primeDirichletSum_modEq {m a : ℕ} [NeZero m] (hcop : Nat.Coprime a m) :
    ∃ C : ℝ, ∀ σ ∈ Set.Ioo (1 : ℝ) 2,
      |primeDirichletSum {p : ℕ | p ≡ a [MOD m]} σ -
          (m.totient : ℝ)⁻¹ * Real.log (1 / (σ - 1))| ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_bound_re_LSeries_residueClassWeight_sub_log (isUnit_zmod_of_coprime hcop)
  refine ⟨C + 1, fun σ hσ => ?_⟩
  obtain ⟨hnn, hle1⟩ := re_LSeries_residueClassWeight_sub_primeDirichletSum_bounds (m := m) (a := a) hσ.1
  have h1 := hC σ hσ
  have hsplit :
      primeDirichletSum {p : ℕ | p ≡ a [MOD m]} σ - (m.totient : ℝ)⁻¹ * Real.log (1 / (σ - 1)) =
        ((LSeries (residueClassWeight (a : ZMod m)) (σ : ℂ)).re -
          (m.totient : ℝ)⁻¹ * Real.log (1 / (σ - 1))) -
        ((LSeries (residueClassWeight (a : ZMod m)) (σ : ℂ)).re -
          primeDirichletSum {p : ℕ | p ≡ a [MOD m]} σ) := by ring
  rw [hsplit]
  calc _ ≤ |(LSeries (residueClassWeight (a : ZMod m)) (σ : ℂ)).re -
              (m.totient : ℝ)⁻¹ * Real.log (1 / (σ - 1))| +
            |(LSeries (residueClassWeight (a : ZMod m)) (σ : ℂ)).re -
              primeDirichletSum {p : ℕ | p ≡ a [MOD m]} σ| := abs_sub _ _
    _ ≤ C + 1 := by
        rw [abs_of_nonneg hnn]
        linarith

/-! ## Section 3: Dirichlet's Quantitative Analytic Density Theorem & `riemannZeta` Normalization -/

/-- **Dirichlet's Quantitative Analytic Density Theorem** (congruence-set form):
for every `m ≥ 1` (`[NeZero m]`) and `Nat.Coprime a m`, `{p | p ≡ a [MOD m]}` has exact
Dirichlet density `1 / φ(m)`. -/
theorem hasDirichletDensity_modEq {m a : ℕ} [NeZero m] (hcop : Nat.Coprime a m) :
    HasDirichletDensity {p : ℕ | p ≡ a [MOD m]} (1 / (m.totient : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_bound_primeDirichletSum_modEq hcop
  refine hasDirichletDensity_of_bounded_sub (C := C) fun σ hσ => ?_
  simpa only [one_div] using hC σ hσ

/-- **Dirichlet's Quantitative Analytic Density Theorem** (prime-set form):
for every `m ≥ 1` (`[NeZero m]`) and `Nat.Coprime a m`, the prime set
`{p : ℕ | p.Prime ∧ p ≡ a [MOD m]}` has exact Dirichlet density `1 / φ(m)`. -/
theorem hasDirichletDensity_primes_modEq {m a : ℕ} [NeZero m] (hcop : Nat.Coprime a m) :
    HasDirichletDensity {p : ℕ | p.Prime ∧ p ≡ a [MOD m]} (1 / (m.totient : ℝ)) :=
  (hasDirichletDensity_congr_primes (fun p hp => by simp [hp])).mpr
    (hasDirichletDensity_modEq hcop)

/-- The set of all primes (`Set.univ`) has exact Dirichlet density `1`. -/
theorem hasDirichletDensity_univ : HasDirichletDensity Set.univ 1 := by
  have h1 := hasDirichletDensity_modEq (m := 1) (a := 1) (Nat.coprime_one_left 1)
  have hset : {p : ℕ | p ≡ 1 [MOD 1]} = Set.univ := by
    ext p; simp [Nat.ModEq, Nat.mod_one]
  rw [hset, Nat.totient_one, Nat.cast_one, div_one] at h1
  exact h1

/-- Every Dirichlet density satisfies `δ ≤ 1`. -/
theorem hasDirichletDensity_le_one {S : Set ℕ} {δ : ℝ} (h : HasDirichletDensity S δ) :
    δ ≤ 1 :=
  hasDirichletDensity_mono (Set.subset_univ S) h hasDirichletDensity_univ

/-- Complement law for Dirichlet density: if `S` has density `δ`, then `Sᶜ` has density `1 - δ`. -/
theorem hasDirichletDensity_compl {S : Set ℕ} {δ : ℝ} (h : HasDirichletDensity S δ) :
    HasDirichletDensity Sᶜ (1 - δ) := by
  have heq : Set.univ \ S = Sᶜ := (Set.compl_eq_univ_sdiff S).symm
  rw [← heq]
  exact hasDirichletDensity_sdiff_of_subset (Set.subset_univ S) h hasDirichletDensity_univ

/-- Quantitative Dirichlet infinitude derived directly from positive analytic density `1 / φ(m) > 0`. -/
theorem infinite_primes_modEq_of_density {m a : ℕ} [NeZero m] (hcop : Nat.Coprime a m) :
    {p : ℕ | p.Prime ∧ p ≡ a [MOD m]}.Infinite := by
  have hpos : (0 : ℝ) < 1 / (m.totient : ℝ) := by
    have htot : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
    positivity
  exact infinite_of_hasDirichletDensity_pos (hasDirichletDensity_primes_modEq hcop) hpos

/-- Asymptotic equivalence of `Real.log (riemannZeta σ).re` and `Real.log (1 / (σ - 1))`
as `σ → 1⁺`, proved directly from Mathlib's simple-pole theorem `riemannZeta_residue_one`. -/
theorem tendsto_log_riemannZeta_div_log_inv_sub_one :
    Tendsto (fun σ : ℝ => Real.log (riemannZeta (σ : ℂ)).re / Real.log (1 / (σ - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hmaps : Tendsto (fun σ : ℝ => (σ : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (nhds (1 : ℝ)) (nhds (1 : ℂ)) := by
        simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hEq
      have hR : σ = 1 := by exact_mod_cast hEq
      exact hσ.ne' hR
  have hresC : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℂ)) :=
    riemannZeta_residue_one.comp hmaps
  have hresR : Tendsto (fun σ : ℝ => (σ - 1) * (riemannZeta (σ : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) := by
    have h := (Complex.continuous_re.continuousAt.tendsto.comp hresC)
    refine h.congr fun σ => ?_
    change (((σ : ℂ) - 1) * riemannZeta (σ : ℂ)).re = (σ - 1) * (riemannZeta (σ : ℂ)).re
    have hsub : ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hsub, Complex.re_ofReal_mul]
  have hlog_res : Tendsto (fun σ : ℝ => Real.log ((σ - 1) * (riemannZeta (σ : ℂ)).re))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hresR
    simpa only [Function.comp_def, Real.log_one] using h
  have hdiv0 : Tendsto
      (fun σ : ℝ => Real.log ((σ - 1) * (riemannZeta (σ : ℂ)).re) / Real.log (1 / (σ - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    hlog_res.div_atTop tendsto_log_inv_sub_one_atTop
  have hpos_prod : ∀ᶠ σ : ℝ in nhdsWithin 1 (Set.Ioi 1),
      0 < (σ - 1) * (riemannZeta (σ : ℂ)).re :=
    hresR.eventually (Ioi_mem_nhds one_pos)
  have hsum : Tendsto
      (fun σ : ℝ => 1 + Real.log ((σ - 1) * (riemannZeta (σ : ℂ)).re) / Real.log (1 / (σ - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    simpa using tendsto_const_nhds.add hdiv0
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_log_inv_sub_one_pos, hpos_prod] with σ hσ hlog hprod
  have hsub_pos : 0 < σ - 1 := sub_pos.mpr hσ
  have hzeta_pos : 0 < (riemannZeta (σ : ℂ)).re := by
    by_contra hle
    push Not at hle
    nlinarith
  have hlog_eq : Real.log ((σ - 1) * (riemannZeta (σ : ℂ)).re) =
      Real.log (riemannZeta (σ : ℂ)).re - Real.log (1 / (σ - 1)) := by
    rw [Real.log_mul hsub_pos.ne' hzeta_pos.ne', one_div, Real.log_inv]
    ring
  rw [hlog_eq]
  field_simp [hlog.ne']
  ring

/-- **Equivalence with the `log ζ(σ)` Normalization of Dirichlet Density**:
`HasDirichletDensity S δ` holds if and only if
`primeDirichletSum S σ / Real.log (riemannZeta (σ : ℂ)).re → δ` as `σ → 1⁺`. -/
theorem hasDirichletDensity_iff_tendsto_div_log_riemannZeta {S : Set ℕ} {δ : ℝ} :
    HasDirichletDensity S δ ↔
      Tendsto (fun σ : ℝ => primeDirichletSum S σ / Real.log (riemannZeta (σ : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds δ) := by
  have hratio := tendsto_log_riemannZeta_div_log_inv_sub_one
  have hlog_zeta_pos : ∀ᶠ σ : ℝ in nhdsWithin 1 (Set.Ioi 1),
      0 < Real.log (riemannZeta (σ : ℂ)).re := by
    have hpos_r : ∀ᶠ σ : ℝ in nhdsWithin 1 (Set.Ioi 1),
        0 < Real.log (riemannZeta (σ : ℂ)).re / Real.log (1 / (σ - 1)) :=
      hratio.eventually (Ioi_mem_nhds one_pos)
    filter_upwards [eventually_log_inv_sub_one_pos, hpos_r] with σ h1 h2
    exact (div_pos_iff_of_pos_right h1).mp h2
  constructor
  · intro h
    have hdiv := h.div hratio one_ne_zero
    rw [div_one] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [eventually_log_inv_sub_one_pos, hlog_zeta_pos] with σ h1 h2
    dsimp only [Pi.div_apply]
    field_simp [h1.ne', h2.ne']
  · intro h
    have hmul := h.mul hratio
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_log_inv_sub_one_pos, hlog_zeta_pos] with σ h1 h2
    field_simp [h1.ne', h2.ne']

/-! ## Section 4: Exact Cyclotomic Chebotarev Density Theorem -/

/-- The Frobenius fiber of a Galois element `g ∈ Gal(ℚ(ζ_m)/ℚ)`:
the set of unramified primes `p ∤ m` with `frobPrime m hp hndvd = g`. -/
def FrobPrimes (m : ℕ) [NeZero m] (g : CycGal m) : Set ℕ :=
  {p : ℕ | ∃ (hp : p.Prime) (hndvd : ¬ p ∣ m), frobPrime m hp hndvd = g}

/-- The Frobenius preimage of a subset `C ⊆ Gal(ℚ(ζ_m)/ℚ)`:
the set of unramified primes `p ∤ m` with `frobPrime m hp hndvd ∈ C`. -/
def FrobPrimesSet (m : ℕ) [NeZero m] (C : Set (CycGal m)) : Set ℕ :=
  {p : ℕ | ∃ (hp : p.Prime) (hndvd : ¬ p ∣ m), frobPrime m hp hndvd ∈ C}

/-- Exact arithmetic identification of the Frobenius fiber `FrobPrimes m g` with the prime
residue class `p ≡ ((artinMap m)⁻¹ g : ZMod m).val [MOD m]`. -/
theorem frobPrimes_eq_primes_modEq (m : ℕ) [NeZero m] (g : CycGal m) :
    FrobPrimes m g =
      {p : ℕ | p.Prime ∧ p ≡ (((artinMap m).symm g : (ZMod m)ˣ) : ZMod m).val [MOD m]} := by
  set u : (ZMod m)ˣ := (artinMap m).symm g
  set a : ℕ := (u : ZMod m).val
  have ha_cast : (a : ZMod m) = (u : ZMod m) := ZMod.natCast_zmod_val (u : ZMod m)
  have ha_cop : Nat.Coprime a m :=
    (ZMod.isUnit_iff_coprime a m).mp (ha_cast.symm ▸ u.isUnit)
  ext p
  simp only [FrobPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hndvd, hEq⟩
    refine ⟨hp, ?_⟩
    have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
    have hu_eq : ZMod.unitOfCoprime p hcop = u := by
      apply (artinMap m).injective
      calc artinMap m (ZMod.unitOfCoprime p hcop)
          = frobPrime m hp hndvd := rfl
        _ = g := hEq
        _ = artinMap m u := ((artinMap m).apply_symm_apply g).symm
    have hval : (p : ZMod m) = (a : ZMod m) := by
      rw [ha_cast, ← hu_eq, ZMod.coe_unitOfCoprime]
    exact (ZMod.natCast_eq_natCast_iff p a m).mp hval
  · rintro ⟨hp, hmod⟩
    have hp_cop : p.Coprime m := by
      have hcast : (p : ZMod m) = (a : ZMod m) := (ZMod.natCast_eq_natCast_iff p a m).mpr hmod
      exact (ZMod.isUnit_iff_coprime p m).mp (hcast.symm ▸ isUnit_zmod_of_coprime ha_cop)
    have hndvd : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp).mp hp_cop
    refine ⟨hp, hndvd, ?_⟩
    have hu_eq : ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd) = u := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, ← ha_cast]
      exact (ZMod.natCast_eq_natCast_iff p a m).mpr hmod
    calc frobPrime m hp hndvd
        = artinMap m (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)) := rfl
      _ = artinMap m u := by rw [hu_eq]
      _ = g := (artinMap m).apply_symm_apply g

/-- **Exact Cyclotomic Chebotarev Density Theorem** (`φ(m)` form):
for every `m ≥ 1` (`[NeZero m]`) and every `g ∈ Gal(ℚ(ζ_m)/ℚ)`, the set of unramified primes
`p ∤ m` with `σ_p = g` has exact analytic density `1 / φ(m)`. -/
theorem cyclotomic_chebotarev_density_totient (m : ℕ) [NeZero m] (g : CycGal m) :
    HasDirichletDensity (FrobPrimes m g) (1 / (m.totient : ℝ)) := by
  rw [frobPrimes_eq_primes_modEq m g]
  set u : (ZMod m)ˣ := (artinMap m).symm g
  have ha_cop : Nat.Coprime ((u : ZMod m).val) m :=
    (ZMod.isUnit_iff_coprime _ m).mp ((ZMod.natCast_zmod_val (u : ZMod m)).symm ▸ u.isUnit)
  exact hasDirichletDensity_primes_modEq ha_cop

/-- **Exact Cyclotomic Chebotarev Density Theorem** (`|Gal|` form):
for every `m ≥ 1` (`[NeZero m]`) and every `g ∈ Gal(ℚ(ζ_m)/ℚ)`, the set of unramified primes
`p ∤ m` with `σ_p = g` has exact analytic density `1 / |Gal(ℚ(ζ_m)/ℚ)|`. -/
theorem cyclotomic_chebotarev_density (m : ℕ) [NeZero m] (g : CycGal m) :
    HasDirichletDensity (FrobPrimes m g) (1 / (Nat.card (CycGal m) : ℝ)) := by
  rw [card_cycGal_eq_totient m]
  exact cyclotomic_chebotarev_density_totient m g

/-- Unconditional infinitude of every Frobenius fiber `FrobPrimes m g`. -/
theorem cyclotomic_chebotarev_infinite (m : ℕ) [NeZero m] (g : CycGal m) :
    (FrobPrimes m g).Infinite := by
  have hpos : (0 : ℝ) < 1 / (m.totient : ℝ) := by
    have htot : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
    positivity
  exact infinite_of_hasDirichletDensity_pos (cyclotomic_chebotarev_density_totient m g) hpos

/-- Distinct Galois elements have disjoint Frobenius fibers. -/
theorem pairwiseDisjoint_frobPrimes (m : ℕ) [NeZero m] :
    (Set.univ : Set (CycGal m)).PairwiseDisjoint (FrobPrimes m) := by
  intro g₁ _ g₂ _ hne
  change Disjoint (FrobPrimes m g₁) (FrobPrimes m g₂)
  rw [Set.disjoint_left]
  rintro p ⟨hp1, hnd1, hEq1⟩ ⟨hp2, hnd2, hEq2⟩
  exact hne (hEq1.symm.trans hEq2)

/-- **Exact Cyclotomic Chebotarev Density Theorem for Arbitrary Subsets `C ⊆ Gal(ℚ(ζ_m)/ℚ)`**:
`HasDirichletDensity (FrobPrimesSet m C) (|C| / |Gal(ℚ(ζ_m)/ℚ)|)`. -/
theorem cyclotomic_chebotarev_density_subset (m : ℕ) [NeZero m] (C : Set (CycGal m)) :
    HasDirichletDensity (FrobPrimesSet m C)
      ((Nat.card C : ℝ) / (Nat.card (CycGal m) : ℝ)) := by
  classical
  have hC_fin : C.Finite := Set.toFinite C
  let I : Finset (CycGal m) := hC_fin.toFinset
  have hunion : FrobPrimesSet m C = ⋃ g ∈ I, FrobPrimes m g := by
    ext p
    simp only [FrobPrimesSet, FrobPrimes, Set.mem_ofPred_eq, Set.mem_iUnion, I, hC_fin.mem_toFinset]
    constructor
    · rintro ⟨hp, hndvd, hmem⟩
      exact ⟨frobPrime m hp hndvd, hmem, hp, hndvd, rfl⟩
    · rintro ⟨g, hg, hp, hndvd, rfl⟩
      exact ⟨hp, hndvd, hg⟩
  have hdisj : (I : Set (CycGal m)).PairwiseDisjoint (FrobPrimes m) :=
    (pairwiseDisjoint_frobPrimes m).subset (Set.subset_univ _)
  have hdens := hasDirichletDensity_biUnion_finset I (FrobPrimes m)
    (fun _ => 1 / (Nat.card (CycGal m) : ℝ)) hdisj
    (fun g _ => cyclotomic_chebotarev_density m g)
  rw [← hunion] at hdens
  have hcard : Nat.card C = I.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card C hC_fin]
  have hsum_eq : ∑ _g ∈ I, (1 / (Nat.card (CycGal m) : ℝ)) =
      (Nat.card C : ℝ) / (Nat.card (CycGal m) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_one_div]
  rwa [hsum_eq] at hdens

/-- **Cyclotomic Chebotarev Density for Subgroups `H ≤ Gal(ℚ(ζ_m)/ℚ)`** (`|H| / φ(m)` form). -/
theorem cyclotomic_chebotarev_density_subgroup (m : ℕ) [NeZero m] (H : Subgroup (CycGal m)) :
    HasDirichletDensity (FrobPrimesSet m (H : Set (CycGal m)))
      ((Nat.card H : ℝ) / (m.totient : ℝ)) := by
  have h := cyclotomic_chebotarev_density_subset m (H : Set (CycGal m))
  rwa [card_cycGal_eq_totient m] at h

/-- **Cyclotomic Chebotarev Density for Subgroups** (`1 / [G : H]` form via Lagrange's theorem). -/
theorem cyclotomic_chebotarev_density_subgroup_eq_inv_index (m : ℕ) [NeZero m]
    (H : Subgroup (CycGal m)) :
    HasDirichletDensity (FrobPrimesSet m (H : Set (CycGal m))) (1 / (H.index : ℝ)) := by
  have h := cyclotomic_chebotarev_density_subset m (H : Set (CycGal m))
  have hlag : (Nat.card H : ℝ) * (H.index : ℝ) = (Nat.card (CycGal m) : ℝ) := by
    exact_mod_cast Subgroup.card_mul_index H
  have hHpos : (Nat.card H : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hidx_pos : (H.index : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hlag
    have hGpos : (0 : ℝ) < (Nat.card (CycGal m) : ℝ) := by
      rw [card_cycGal_eq_totient m]
      exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
    linarith
  have hratio : (Nat.card H : ℝ) / (Nat.card (CycGal m) : ℝ) = 1 / (H.index : ℝ) := by
    rw [← hlag]
    field_simp [hHpos, hidx_pos]
  change HasDirichletDensity (FrobPrimesSet m (H : Set (CycGal m)))
    ((Nat.card H : ℝ) / (Nat.card (CycGal m) : ℝ)) at h
  rwa [hratio] at h

/-! ## Section 5: Subfield Splitting Density & Kronecker–Bauer Uniqueness Theorem -/

/-- The set of unramified primes `p ∤ m` that **split completely** in a cyclotomic subfield
`K : IntermediateField ℚ (CycField m)`: those with `frobPrime m hp hndvd ∈ K.fixingSubgroup`. -/
def SplitPrimes {m : ℕ} [NeZero m] (K : IntermediateField ℚ (CycField m)) : Set ℕ :=
  {p : ℕ | ∃ (hp : p.Prime) (hndvd : ¬ p ∣ m), frobPrime m hp hndvd ∈ K.fixingSubgroup}

/-- `SplitPrimes K` coincides literally with `FrobPrimesSet m K.fixingSubgroup`. -/
theorem splitPrimes_eq_frobPrimesSet {m : ℕ} [NeZero m]
    (K : IntermediateField ℚ (CycField m)) :
    SplitPrimes K = FrobPrimesSet m (K.fixingSubgroup : Set (CycGal m)) :=
  rfl

/-- Every unramified prime `p ∤ m` splits completely in `ℚ = ⊥`. -/
theorem splitPrimes_bot (m : ℕ) [NeZero m] :
    SplitPrimes (⊥ : IntermediateField ℚ (CycField m)) = {p : ℕ | p.Prime ∧ ¬ p ∣ m} := by
  ext p
  simp only [SplitPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hndvd, _⟩
    exact ⟨hp, hndvd⟩
  · rintro ⟨hp, hndvd⟩
    refine ⟨hp, hndvd, ?_⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact AlgEquiv.commutes _ r

/-- A prime splits completely in the full cyclotomic field `ℚ(ζ_m) = ⊤` iff `p ≡ 1 [MOD m]`. -/
theorem splitPrimes_top (m : ℕ) [NeZero m] :
    SplitPrimes (⊤ : IntermediateField ℚ (CycField m)) = {p : ℕ | p.Prime ∧ p ≡ 1 [MOD m]} := by
  have h1 : SplitPrimes (⊤ : IntermediateField ℚ (CycField m)) = FrobPrimes m 1 := by
    ext p
    simp only [SplitPrimes, FrobPrimes, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hp, hndvd, hmem⟩
      refine ⟨hp, hndvd, ?_⟩
      ext x
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hmem x trivial
    · rintro ⟨hp, hndvd, hEq⟩
      refine ⟨hp, hndvd, ?_⟩
      rw [hEq]
      exact Subgroup.one_mem _
  rw [h1, frobPrimes_eq_primes_modEq m 1]
  ext p
  simp only [Set.mem_ofPred_eq, map_one, Units.val_one]
  constructor
  · rintro ⟨hp, hmod⟩
    refine ⟨hp, ?_⟩
    have hcast : (p : ZMod m) = ((1 : ZMod m).val : ZMod m) :=
      (ZMod.natCast_eq_natCast_iff _ _ m).mpr hmod
    rw [ZMod.natCast_zmod_val, ← Nat.cast_one] at hcast
    exact (ZMod.natCast_eq_natCast_iff p 1 m).mp hcast
  · rintro ⟨hp, hmod⟩
    refine ⟨hp, ?_⟩
    have hcast : (p : ZMod m) = (1 : ZMod m) := by
      simpa using (ZMod.natCast_eq_natCast_iff p 1 m).mpr hmod
    rw [← ZMod.natCast_zmod_val (1 : ZMod m)] at hcast
    exact (ZMod.natCast_eq_natCast_iff _ _ m).mp hcast

/-- Prime splitting criterion for an Artin fixed field `ℚ(ζ_m)^H`:
`p ∈ SplitPrimes (cycFixedField m H)` iff `p` is prime, `p ∤ m`, and `(p : (ZMod m)ˣ) ∈ H`. -/
theorem mem_splitPrimes_cycFixedField_iff {m : ℕ} [NeZero m] (H : Subgroup (ZMod m)ˣ) (p : ℕ) :
    p ∈ SplitPrimes (cycFixedField m H) ↔
      ∃ (hp : p.Prime) (hndvd : ¬ p ∣ m),
        ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd) ∈ H := by
  simp only [SplitPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hndvd, hmem⟩
    refine ⟨hp, hndvd, ?_⟩
    have hfix : ∀ x : cycFixedField m H,
        frob m p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd) (x : CycField m) =
          (x : CycField m) :=
      fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hmem x.1 x.2
    exact (frob_fixes_cycFixedField_iff H ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)).mp hfix
  · rintro ⟨hp, hndvd, hu⟩
    refine ⟨hp, hndvd, ?_⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact ((frob_fixes_cycFixedField_iff H ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)).mpr hu)
      ⟨x, hx⟩

/-- Antitonicity of `SplitPrimes`: larger subfields have smaller sets of completely split primes. -/
theorem splitPrimes_antitone {m : ℕ} [NeZero m]
    {K₁ K₂ : IntermediateField ℚ (CycField m)} (hle : K₁ ≤ K₂) :
    SplitPrimes K₂ ⊆ SplitPrimes K₁ := by
  rintro p ⟨hp, hndvd, hmem⟩
  refine ⟨hp, hndvd, ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
  exact fun x hx => hmem x (hle hx)

private lemma cycGal_zpow_apply_eq_self {m : ℕ} [NeZero m] (g : CycGal m) {x : CycField m}
    (hx : g x = x) (k : ℤ) : (g ^ k) x = x := by
  have hinv : g⁻¹ x = x := by
    apply g.injective
    have h1 : g (g⁻¹ x) = (g * g⁻¹) x := rfl
    rw [h1, mul_inv_cancel, AlgEquiv.one_apply, hx]
  have hpow : ∀ n : ℕ, (g ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      exact (congrArg g ih).trans hx
  cases k with
  | ofNat n => simpa using hpow n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    have hinv_pow : ∀ r : ℕ, (g⁻¹ ^ r) x = x := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
        rw [pow_succ']
        exact (congrArg (fun y => g⁻¹ y) ih).trans hinv
    exact hinv_pow (n + 1)

/-- Compositum splitting law: a prime splits completely in `K₁ ⊔ K₂` iff it splits completely
in both `K₁` and `K₂`. -/
theorem splitPrimes_sup {m : ℕ} [NeZero m] (K₁ K₂ : IntermediateField ℚ (CycField m)) :
    SplitPrimes (K₁ ⊔ K₂) = SplitPrimes K₁ ∩ SplitPrimes K₂ := by
  ext p
  simp only [SplitPrimes, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hndvd, hmem⟩
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
    refine ⟨⟨hp, hndvd, ?_⟩, ⟨hp, hndvd, ?_⟩⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      exact fun x hx => hmem x (le_sup_left (a := K₁) (b := K₂) hx)
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      exact fun x hx => hmem x (le_sup_right (a := K₁) (b := K₂) hx)
  · rintro ⟨⟨hp, hndvd, h1⟩, ⟨_, _, h2⟩⟩
    refine ⟨hp, hndvd, ?_⟩
    have hfix : K₁ ⊔ K₂ ≤ IntermediateField.fixedField (Subgroup.zpowers (frobPrime m hp hndvd)) := by
      refine sup_le ?_ ?_
      · intro x hx ⟨σ, hσ⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
        exact cycGal_zpow_apply_eq_self _
          ((IntermediateField.mem_fixingSubgroup_iff _ _).mp h1 x hx) k
      · intro x hx ⟨σ, hσ⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
        exact cycGal_zpow_apply_eq_self _
          ((IntermediateField.mem_fixingSubgroup_iff _ _).mp h2 x hx) k
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hfix hx ⟨frobPrime m hp hndvd, Subgroup.mem_zpowers _⟩

/-- Exact degree-index identity for any cyclotomic subfield `K ⊆ ℚ(ζ_m)`:
`[K : ℚ] = [Gal(ℚ(ζ_m)/ℚ) : K.fixingSubgroup]`. -/
theorem finrank_cycIntermediateField_eq_index {m : ℕ} [NeZero m]
    (K : IntermediateField ℚ (CycField m)) :
    Module.finrank ℚ K = K.fixingSubgroup.index := by
  have hK : cycFixedField m (cycFixingSubgroup m K) = K := cycFixedField_fixingSubgroup m K
  have hdeg : Module.finrank ℚ K = (cycFixingSubgroup m K).index := by
    conv_lhs => rw [← hK]
    exact finrank_cycFixedField_eq_index m (cycFixingSubgroup m K)
  rw [hdeg]
  have hcard_eq : Nat.card (cycFixingSubgroup m K) = Nat.card K.fixingSubgroup := by
    let e : cycFixingSubgroup m K ≃ K.fixingSubgroup :=
      { toFun := fun u => ⟨artinMap m u.1, u.2⟩
        invFun := fun σ => ⟨(artinMap m).symm σ.1, by
          change artinMap m ((artinMap m).symm σ.1) ∈ K.fixingSubgroup
          rw [(artinMap m).apply_symm_apply]
          exact σ.2⟩
        left_inv := fun u => Subtype.ext ((artinMap m).symm_apply_apply u.1)
        right_inv := fun σ => Subtype.ext ((artinMap m).apply_symm_apply σ.1) }
    exact Nat.card_congr e
  have hlag1 := Subgroup.card_mul_index (cycFixingSubgroup m K)
  have hlag2 := Subgroup.card_mul_index K.fixingSubgroup
  have hcardG : Nat.card (ZMod m)ˣ = Nat.card (CycGal m) :=
    Nat.card_congr (artinMap m).toEquiv
  rw [hcard_eq, hcardG, ← hlag2] at hlag1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hlag1

/-- **Exact Splitting Density Theorem for Cyclotomic Subfields (0 Assumptions)**:
for every `m ≥ 1` (`[NeZero m]`) and every intermediate field
`K : IntermediateField ℚ (CycField m)`, the set of primes `SplitPrimes K` splitting completely
in `K` has exact analytic (Dirichlet) density `1 / [K : ℚ]`. -/
theorem hasDirichletDensity_splitPrimes_eq_inv_finrank {m : ℕ} [NeZero m]
    (K : IntermediateField ℚ (CycField m)) :
    HasDirichletDensity (SplitPrimes K) (1 / (Module.finrank ℚ K : ℝ)) := by
  rw [splitPrimes_eq_frobPrimesSet, finrank_cycIntermediateField_eq_index K]
  exact cyclotomic_chebotarev_density_subgroup_eq_inv_index m K.fixingSubgroup

/-- Exact splitting density for an Artin fixed field `ℚ(ζ_m)^H`: equals `1 / [(ZMod m)ˣ : H]`. -/
theorem hasDirichletDensity_splitPrimes_cycFixedField {m : ℕ} [NeZero m]
    (H : Subgroup (ZMod m)ˣ) :
    HasDirichletDensity (SplitPrimes (cycFixedField m H)) (1 / (H.index : ℝ)) := by
  have h := hasDirichletDensity_splitPrimes_eq_inv_finrank (cycFixedField m H)
  rwa [finrank_cycFixedField_eq_index m H] at h

/-- **Exact Compositum Splitting Density**:
the intersection `SplitPrimes K₁ ∩ SplitPrimes K₂` has exact Dirichlet density `1 / [K₁ ⊔ K₂ : ℚ]`. -/
theorem hasDirichletDensity_splitPrimes_inter_eq_inv_finrank_sup {m : ℕ} [NeZero m]
    (K₁ K₂ : IntermediateField ℚ (CycField m)) :
    HasDirichletDensity (SplitPrimes K₁ ∩ SplitPrimes K₂)
      (1 / (Module.finrank ℚ (K₁ ⊔ K₂ : IntermediateField ℚ (CycField m)) : ℝ)) := by
  rw [← splitPrimes_sup K₁ K₂]
  exact hasDirichletDensity_splitPrimes_eq_inv_finrank (K₁ ⊔ K₂)

/-- Helper: Galois inclusion characterization via `fixingSubgroup` for cyclotomic subfields. -/
private theorem cyc_le_iff_fixingSubgroup_le {m : ℕ} [NeZero m]
    (K₁ K₂ : IntermediateField ℚ (CycField m)) :
    K₁ ≤ K₂ ↔ K₂.fixingSubgroup ≤ K₁.fixingSubgroup := by
  have hord := (cycSubfieldEquivSubgroup m).map_rel_iff (a := K₁) (b := K₂)
  have hiff : cycFixingSubgroup m K₂ ≤ cycFixingSubgroup m K₁ ↔
      K₂.fixingSubgroup ≤ K₁.fixingSubgroup := by
    constructor
    · intro h σ hσ
      have hu : (artinMap m).symm σ ∈ cycFixingSubgroup m K₂ := by
        change artinMap m ((artinMap m).symm σ) ∈ K₂.fixingSubgroup
        rwa [(artinMap m).apply_symm_apply]
      have hu1 := h hu
      change artinMap m ((artinMap m).symm σ) ∈ K₁.fixingSubgroup at hu1
      rwa [(artinMap m).apply_symm_apply] at hu1
    · intro h u hu
      exact h hu
  exact hord.symm.trans hiff

/-- **Kronecker–Bauer Inclusion Theorem (Analytic Density-Zero Form, 0 Assumptions)**:
if `SplitPrimes K₂ \ SplitPrimes K₁` has Dirichlet density `0`, then `K₁ ≤ K₂`. -/
theorem bauer_le_of_splitPrimes_diff_density_zero {m : ℕ} [NeZero m]
    {K₁ K₂ : IntermediateField ℚ (CycField m)}
    (h0 : HasDirichletDensity (SplitPrimes K₂ \ SplitPrimes K₁) 0) :
    K₁ ≤ K₂ := by
  rw [cyc_le_iff_fixingSubgroup_le]
  intro g hg2
  by_contra hg1
  have hsub : FrobPrimes m g ⊆ SplitPrimes K₂ \ SplitPrimes K₁ := by
    rintro p ⟨hp, hndvd, hEq⟩
    refine ⟨⟨hp, hndvd, hEq.symm ▸ hg2⟩, ?_⟩
    rintro ⟨_, _, hmem1⟩
    exact hg1 (hEq ▸ hmem1)
  have hle : (1 / (m.totient : ℝ)) ≤ 0 :=
    hasDirichletDensity_mono hsub (cyclotomic_chebotarev_density_totient m g) h0
  have hpos : (0 : ℝ) < 1 / (m.totient : ℝ) := by
    have htot : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
    positivity
  linarith

/-- **Kronecker–Bauer Inclusion Theorem (Finite-Exception Form, 0 Assumptions)**:
if `(SplitPrimes K₂ \ SplitPrimes K₁).Finite`, then `K₁ ≤ K₂`. -/
theorem bauer_le_of_splitPrimes_diff_finite {m : ℕ} [NeZero m]
    {K₁ K₂ : IntermediateField ℚ (CycField m)}
    (hfin : (SplitPrimes K₂ \ SplitPrimes K₁).Finite) :
    K₁ ≤ K₂ :=
  bauer_le_of_splitPrimes_diff_density_zero (hasDirichletDensity_of_finite hfin)

/-- **Kronecker–Bauer Characterization of Subfield Inclusion (Finite-Exception Equivalence)**:
`(SplitPrimes K₂ \ SplitPrimes K₁).Finite ↔ K₁ ≤ K₂`. -/
theorem bauer_le_iff_splitPrimes_diff_finite {m : ℕ} [NeZero m]
    (K₁ K₂ : IntermediateField ℚ (CycField m)) :
    (SplitPrimes K₂ \ SplitPrimes K₁).Finite ↔ K₁ ≤ K₂ := by
  refine ⟨bauer_le_of_splitPrimes_diff_finite, fun hle => ?_⟩
  have hempty : SplitPrimes K₂ \ SplitPrimes K₁ = ∅ :=
    Set.sdiff_eq_empty.mpr (splitPrimes_antitone hle)
  rw [hempty]
  exact Set.finite_empty

/-- **Kronecker–Bauer Characterization of Subfield Inclusion (Density-Zero Equivalence)**:
`HasDirichletDensity (SplitPrimes K₂ \ SplitPrimes K₁) 0 ↔ K₁ ≤ K₂`. -/
theorem bauer_le_iff_splitPrimes_diff_density_zero {m : ℕ} [NeZero m]
    (K₁ K₂ : IntermediateField ℚ (CycField m)) :
    HasDirichletDensity (SplitPrimes K₂ \ SplitPrimes K₁) 0 ↔ K₁ ≤ K₂ := by
  refine ⟨bauer_le_of_splitPrimes_diff_density_zero, fun hle => ?_⟩
  have hempty : SplitPrimes K₂ \ SplitPrimes K₁ = ∅ :=
    Set.sdiff_eq_empty.mpr (splitPrimes_antitone hle)
  rw [hempty]
  exact hasDirichletDensity_empty

/-- **Kronecker–Bauer Uniqueness Theorem for Cyclotomic Subfields (Finite-Exception Form)**:
every subfield `K ⊆ ℚ(ζ_m)` is uniquely determined by its set of completely split primes
up to a finite set: `(symmDiff (SplitPrimes K₁) (SplitPrimes K₂)).Finite ↔ K₁ = K₂`. -/
theorem bauer_eq_iff_splitPrimes_symmDiff_finite {m : ℕ} [NeZero m]
    (K₁ K₂ : IntermediateField ℚ (CycField m)) :
    (symmDiff (SplitPrimes K₁) (SplitPrimes K₂)).Finite ↔ K₁ = K₂ := by
  constructor
  · intro hfin
    have h12 : K₂ ≤ K₁ :=
      bauer_le_of_splitPrimes_diff_finite (hfin.subset Set.subset_union_left)
    have h21 : K₁ ≤ K₂ :=
      bauer_le_of_splitPrimes_diff_finite (hfin.subset Set.subset_union_right)
    exact le_antisymm h21 h12
  · rintro rfl
    simp

/-- **Kronecker–Bauer Uniqueness Theorem for Cyclotomic Subfields (Density-Zero Form)**:
`HasDirichletDensity (symmDiff (SplitPrimes K₁) (SplitPrimes K₂)) 0 ↔ K₁ = K₂`. -/
theorem bauer_eq_iff_splitPrimes_symmDiff_density_zero {m : ℕ} [NeZero m]
    (K₁ K₂ : IntermediateField ℚ (CycField m)) :
    HasDirichletDensity (symmDiff (SplitPrimes K₁) (SplitPrimes K₂)) 0 ↔ K₁ = K₂ := by
  constructor
  · intro h0
    have h12_dens : HasDirichletDensity (SplitPrimes K₁ \ SplitPrimes K₂) 0 := by
      have hsub : SplitPrimes K₁ \ SplitPrimes K₂ ⊆ symmDiff (SplitPrimes K₁) (SplitPrimes K₂) :=
        Set.subset_union_left
      unfold HasDirichletDensity at h0 ⊢
      refine squeeze_zero' ?_ ?_ h0
      · filter_upwards [eventually_log_inv_sub_one_pos] with σ hlog
        exact div_nonneg (primeDirichletSum_nonneg _ σ) hlog.le
      · filter_upwards [self_mem_nhdsWithin, eventually_log_inv_sub_one_pos] with σ hσ hlog
        exact div_le_div_of_nonneg_right (primeDirichletSum_mono hsub hσ) hlog.le
    have h21_dens : HasDirichletDensity (SplitPrimes K₂ \ SplitPrimes K₁) 0 := by
      have hsub : SplitPrimes K₂ \ SplitPrimes K₁ ⊆ symmDiff (SplitPrimes K₁) (SplitPrimes K₂) :=
        Set.subset_union_right
      unfold HasDirichletDensity at h0 ⊢
      refine squeeze_zero' ?_ ?_ h0
      · filter_upwards [eventually_log_inv_sub_one_pos] with σ hlog
        exact div_nonneg (primeDirichletSum_nonneg _ σ) hlog.le
      · filter_upwards [self_mem_nhdsWithin, eventually_log_inv_sub_one_pos] with σ hσ hlog
        exact div_le_div_of_nonneg_right (primeDirichletSum_mono hsub hσ) hlog.le
    exact le_antisymm
      (bauer_le_of_splitPrimes_diff_density_zero h21_dens)
      (bauer_le_of_splitPrimes_diff_density_zero h12_dens)
  · rintro rfl
    simp [hasDirichletDensity_empty]

/-- **Quantitative Strict-Extension Splitting Gap**:
if `K₁ < K₂` are cyclotomic subfields of `ℚ(ζ_m)`, then the set of primes splitting completely
in `K₁` but NOT in `K₂` has exact strictly positive Dirichlet density
`1 / [K₁ : ℚ] - 1 / [K₂ : ℚ] > 0` (and is therefore infinite). -/
theorem hasDirichletDensity_splitPrimes_strictDiff {m : ℕ} [NeZero m]
    {K₁ K₂ : IntermediateField ℚ (CycField m)} (hlt : K₁ < K₂) :
    HasDirichletDensity (SplitPrimes K₁ \ SplitPrimes K₂)
        (1 / (Module.finrank ℚ K₁ : ℝ) - 1 / (Module.finrank ℚ K₂ : ℝ)) ∧
      0 < 1 / (Module.finrank ℚ K₁ : ℝ) - 1 / (Module.finrank ℚ K₂ : ℝ) := by
  have hsub : SplitPrimes K₂ ⊆ SplitPrimes K₁ := splitPrimes_antitone hlt.le
  have hdens : HasDirichletDensity (SplitPrimes K₁ \ SplitPrimes K₂)
      (1 / (Module.finrank ℚ K₁ : ℝ) - 1 / (Module.finrank ℚ K₂ : ℝ)) :=
    hasDirichletDensity_sdiff_of_subset hsub
      (hasDirichletDensity_splitPrimes_eq_inv_finrank K₂)
      (hasDirichletDensity_splitPrimes_eq_inv_finrank K₁)
  refine ⟨hdens, ?_⟩
  have hnotle : ¬ K₂ ≤ K₁ := not_le_of_gt hlt
  have hne0 : 1 / (Module.finrank ℚ K₁ : ℝ) - 1 / (Module.finrank ℚ K₂ : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hdens
    exact hnotle (bauer_le_of_splitPrimes_diff_density_zero hdens)
  have hnn : 0 ≤ 1 / (Module.finrank ℚ K₁ : ℝ) - 1 / (Module.finrank ℚ K₂ : ℝ) :=
    hasDirichletDensity_nonneg hdens
  exact lt_of_le_of_ne hnn hne0.symm

end RHDirect.Stage5DirichletDensity
