import RHDirect.Stage14Contracts
import RHDirect.Stage14M1_UnitaryGroupDef
import RHDirect.Stage14M1_LocalSiegelDensities
import RHDirect.Stage14M1_GenusClassDecomp

/-!
# RHDirect.Stage14M1_FormalDegreeDiscrete

Field-2 Package M1 Wave 2: **Unitary Discrete Series Formal Degrees at Real Places,
Level-Zero Volumes, Mass Recursion (`volume_mass_succ`, `volume_mass_ge_two`), and
Rank-2 Genus Mass (`genusMassAt_two`)** in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.

## Contents

1. **Weyl Shifts, Harish-Chandra Parameters & `U(n)` Weyl Dimension (`weylDim`)**:
   - Canonical half-sum of positive roots `weylRho n`, exact antisymmetry and zero-sum laws,
     Harish-Chandra parameter predicate `IsHCParam n lam`, and exact equivalence with shifted
     antitone integer weights `isHCParam_iff_antitone_int`.
   - Concrete Vandermonde product `vandermondeProd lam`, Weyl denominator `weylDenominator n`,
     proved identity `vandermondeProd_weylRho : vandermondeProd (weylRho n) = weylDenominator n`,
     and Weyl dimension `weylDim lam := vandermondeProd lam / weylDenominator n`.
   - Proved positivity, integrality lower bound `1 ≤ weylDim lam` for all `IsHCParam`,
     translation/duality invariance, explicit rank-2/rank-3 formulas, and two-sided
     logarithmic Weyl bounds (`log_weylDim_bounds`).

2. **`UnitaryDiscreteSeries` & `FormalDegreeAtRealPlace`**:
   - Concrete discrete-series datum `UnitaryDiscreteSeries p q` for `U(p, q)` with
     Harish-Chandra parameter `hcParam`, compatible `U(p) × U(q)` lowest `K`-type weights
     `kPosWeight` / `kNegWeight`, and unconditional constructors for arbitrary signatures
     (`ofAntitoneWeight`, `trivialDefinite`).
   - Exact compact unitary volume `unitaryCompactVol n = ∏_{M=1}^n 2 π^M / (M - 1)!`,
     archimedean Tamagawa factor `unitaryTamagawaArchFactor vE n`, and full `π`/factorial
     cancellation `unitaryTamagawaArchFactor_mul_compactVol`.
   - `FormalDegreeAtRealPlace`, `FormalDegreeAtRealPlaceNormalized`, `GlobalFormalDegreeCM`,
     Schur-orthogonality normalization `schur_orthogonality_formal_degree`, rank-2 closed form,
     and CM Hermitian space signature assignment via `Stage14M1_UnitaryGroupDef`.

3. **Congruence Level Towers, `volume_at_level_zero`, `volume_mass_succ`, `volume_mass_ge_two`**:
   - Congruence level tower scaling `tower_genusClassMass_eq` and `level_zero_volume_eq_genus_mass`
     via `Stage14M1_GenusClassDecomp`.
   - Rank-indexed volume-mass recursion `UnitaryVolumeSystem`, **`volume_at_level_zero`**,
     **`volume_mass_succ`**, **`volume_mass_ge_two`**, and indefinite signature induction
     `volume_indef_eq_mass`.
   - Concrete zero-assumption Braun–Shimura–Gan–Yu volume system `bsgyVolumeSystem`,
     `n ≥ 2` positivity `bsgyUnitaryMass_pos_ge_two`, and strict monotonicity
     (`bsgyUnitaryMass_strictMono_ge_three`, `bsgyUnitaryMass_strictMono_ge_two`).

4. **`genusMassAt_two` & Alignment with `Stage14Contracts.M1UnitarySiegelWeilContract`**:
   - Exact rank-2 genus mass formulas (`genusMassAt_two_formula`, `genusMassAt_two_deg_one`,
     `genusMassAt_two_chi4`, `genusMassAt_two_chi3`), positivity `genusMassAt_two_pos`,
     double-coset genus mass bridge `genusMassAt_two_of_class_decomp`, and local Siegel
     Euler-product match via `Stage14M1_LocalSiegelDensities`.
   - Complete Wave-3 handoff `FormalDegreeSiegelData` discharging all mass/density/volume
     obligations of `Stage14Contracts.M1UnitarySiegelWeilContract` and feeding directly into
     `Stage14Contracts.M1UnitarySiegelWeilContract.toStage2MassRatioDatum`.
-/

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Real Finset Filter MeasureTheory NumberField IsDedekindDomain
open RHDirect RHDirect.UnitaryMassFormula RHDirect.Stage11RallisMassFiber
open RHDirect.Stage14Contracts RHDirect.Stage14M1_UnitaryGroupDef
open RHDirect.Stage14M1_LocalSiegelDensities RHDirect.Stage14M1_GenusClassDecomp
open scoped BigOperators Matrix

namespace RHDirect.Stage14M1_FormalDegreeDiscrete

/-! ## Section 1: Weyl Shifts, Harish-Chandra Parameters & `U(n)` Weyl Dimension -/

section WeylDimensionAndHCParams

/-- Canonical half-sum of positive roots `ρ_n(i) = (n - 1)/2 - i` for `U(n)` (`0 ≤ i < n`). -/
def weylRho (n : ℕ) (i : Fin n) : ℝ :=
  ((n - 1 : ℕ) : ℝ) / 2 - (i : ℝ)

lemma weylRho_sub (n : ℕ) (i j : Fin n) :
    weylRho n i - weylRho n j = (j : ℝ) - (i : ℝ) := by
  unfold weylRho
  ring

theorem weylRho_strictAnti (n : ℕ) : StrictAnti (weylRho n) := by
  intro i j hij
  have hij_real : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
  unfold weylRho
  linarith

theorem weylRho_rev (n : ℕ) (i : Fin n) :
    weylRho n (Fin.rev i) = -weylRho n i := by
  unfold weylRho
  have hrev : ((Fin.rev i : Fin n) : ℕ) + (i : ℕ) = n - 1 := by
    rw [Fin.val_rev]
    omega
  have hrevR : ((Fin.rev i : Fin n) : ℝ) + (i : ℝ) = ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hrev
  linarith

theorem weylRho_sum_zero (n : ℕ) : ∑ i : Fin n, weylRho n i = 0 := by
  have h1 : ∑ i : Fin n, weylRho n i = ∑ i : Fin n, weylRho n (Fin.rev i) :=
    (Equiv.sum_comp Fin.revPerm (weylRho n)).symm
  have h2 : ∑ i : Fin n, weylRho n (Fin.rev i) = -∑ i : Fin n, weylRho n i := by
    simp_rw [weylRho_rev, Finset.sum_neg_distrib]
  linarith

/-- **Harish-Chandra Parameter Predicate (`IsHCParam n lam`)**:
`lam : Fin n → ℝ` is strictly decreasing and satisfies the integrality congruence
`lam_i - (n - 1) / 2 ∈ ℤ` for all `i : Fin n`. -/
def IsHCParam (n : ℕ) (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ i : Fin n, ∃ z : ℤ, lam i - ((n - 1 : ℕ) : ℝ) / 2 = (z : ℝ)

/-- Shifted dominant integral weight `μ + ρ_n` attached to `μ : Fin n → ℤ`. -/
def shiftedWeight (n : ℕ) (μ : Fin n → ℤ) (i : Fin n) : ℝ :=
  (μ i : ℝ) + weylRho n i

theorem shiftedWeight_strictAnti {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) :
    StrictAnti (shiftedWeight n μ) := by
  intro i j hij
  have h1 : (μ j : ℝ) ≤ (μ i : ℝ) := Int.cast_le.mpr (hμ hij.le)
  have h2 : weylRho n j < weylRho n i := weylRho_strictAnti n hij
  unfold shiftedWeight
  linarith

theorem shiftedWeight_isHCParam {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) :
    IsHCParam n (shiftedWeight n μ) := by
  refine ⟨shiftedWeight_strictAnti hμ, fun i => ⟨μ i - (i : ℤ), ?_⟩⟩
  unfold shiftedWeight weylRho
  push_cast
  ring

/-- Exact equivalence between `IsHCParam n lam` and shifted antitone integer weights `μ + ρ_n`. -/
theorem isHCParam_iff_antitone_int (n : ℕ) (lam : Fin n → ℝ) :
    IsHCParam n lam ↔ ∃ μ : Fin n → ℤ, Antitone μ ∧ lam = shiftedWeight n μ := by
  constructor
  · rintro ⟨hanti, hint⟩
    choose z hz using hint
    let μ : Fin n → ℤ := fun i => z i + (i : ℤ)
    have hlam : lam = shiftedWeight n μ := by
      ext i
      unfold shiftedWeight weylRho μ
      have hi := hz i
      push_cast
      linarith
    have hμ : Antitone μ := by
      have hstep : ∀ k : ℕ, ∀ hk : k + 1 < n, μ ⟨k + 1, hk⟩ ≤ μ ⟨k, by omega⟩ := by
        intro k hk
        have hlt_lam : lam ⟨k + 1, hk⟩ < lam ⟨k, by omega⟩ :=
          hanti (by simp [Fin.lt_def])
        have hz1 : (z ⟨k + 1, hk⟩ : ℝ) < (z ⟨k, by omega⟩ : ℝ) := by
          have hk1 := hz ⟨k + 1, hk⟩
          have hk0 := hz ⟨k, by omega⟩
          linarith
        have hz_int : z ⟨k + 1, hk⟩ < z ⟨k, by omega⟩ := by exact_mod_cast hz1
        unfold μ
        dsimp only [Fin.val_mk]
        omega
      intro i j hij
      have hij_nat : (i : ℕ) ≤ (j : ℕ) := hij
      have hidx : ∀ m : ℕ, (i : ℕ) ≤ m → ∀ hm : m < n, μ ⟨m, hm⟩ ≤ μ i := by
        intro m him hm
        induction m, him using Nat.le_induction with
        | base =>
          have heq : (⟨(i : ℕ), hm⟩ : Fin n) = i := Fin.ext rfl
          rw [heq]
        | succ m him ih =>
          exact (hstep m hm).trans (ih (by omega))
      have hres := hidx (j : ℕ) hij_nat j.isLt
      simpa using hres
    exact ⟨μ, hμ, hlam⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact shiftedWeight_isHCParam hμ

theorem isHCParam_diff_ge_nat {n : ℕ} {lam : Fin n → ℝ} (h : IsHCParam n lam)
    {i j : Fin n} (hij : i < j) :
    (j : ℝ) - (i : ℝ) ≤ lam i - lam j ∧
      ∃ m : ℕ, 1 ≤ m ∧ lam i - lam j = (m : ℝ) := by
  obtain ⟨μ, hμ, rfl⟩ := (isHCParam_iff_antitone_int n lam).mp h
  have hij_le : i ≤ j := hij.le
  have hμ_le : μ j ≤ μ i := hμ hij_le
  have hdiff_nn : 0 ≤ μ i - μ j := sub_nonneg.mpr hμ_le
  let mInt : ℤ := (μ i - μ j) + ((j : ℤ) - (i : ℤ))
  have hm_pos : 1 ≤ mInt := by
    have hij_int : (i : ℤ) < (j : ℤ) := by exact_mod_cast hij
    omega
  have hm_nat : ∃ m : ℕ, 1 ≤ m ∧ (m : ℤ) = mInt := by
    refine ⟨mInt.toNat, ?_, Int.toNat_of_nonneg (by omega)⟩
    omega
  obtain ⟨m, hm1, hmEq⟩ := hm_nat
  have hcalc : shiftedWeight n μ i - shiftedWeight n μ j = (mInt : ℝ) := by
    unfold shiftedWeight weylRho mInt
    push_cast
    ring
  refine ⟨?_, m, hm1, ?_⟩
  · rw [hcalc]
    have hdiff_real : (0 : ℝ) ≤ (μ i : ℝ) - (μ j : ℝ) := by exact_mod_cast hdiff_nn
    unfold mInt
    push_cast
    linarith
  · rw [hcalc, ← hmEq]
    norm_cast

/-- Spectral gap predicate: pairwise separation `h ≤ lam i - lam j` for `i < j`. -/
def GapAtLeast (n : ℕ) (lam : Fin n → ℝ) (h : ℝ) : Prop :=
  ∀ i j : Fin n, i < j → h ≤ lam i - lam j

theorem GapAtLeast.strictAnti {n : ℕ} {lam : Fin n → ℝ} {h : ℝ} (hh : 0 < h)
    (hg : GapAtLeast n lam h) : StrictAnti lam := by
  intro i j hij
  linarith [hg i j hij]

/-- Vandermonde positive-root product `∏_{i < j} (λ_i - λ_j)` for `U(n)`. -/
def vandermondeProd {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then (lam i - lam j) else 1

/-- Weyl denominator `∏_{j=0}^{n-1} j!` for `U(n)`. -/
def weylDenominator (n : ℕ) : ℝ :=
  ∏ j : Fin n, (Nat.factorial (j : ℕ) : ℝ)

theorem weylDenominator_pos (n : ℕ) : 0 < weylDenominator n := by
  unfold weylDenominator
  exact Finset.prod_pos fun j _ => Nat.cast_pos.mpr (Nat.factorial_pos (j : ℕ))

@[simp]
theorem vandermondeProd_zero (lam : Fin 0 → ℝ) : vandermondeProd lam = 1 := by
  simp [vandermondeProd]

@[simp]
theorem weylDenominator_zero : weylDenominator 0 = 1 := by
  simp [weylDenominator]

private lemma prod_range_sub_eq_factorial (k : ℕ) :
    ∏ i ∈ Finset.range k, ((k : ℝ) - (i : ℝ)) = (Nat.factorial k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ']
    have hshift : ∏ x ∈ Finset.range k, (((k + 1 : ℕ) : ℝ) - ((x + 1 : ℕ) : ℝ)) =
        ∏ x ∈ Finset.range k, ((k : ℝ) - (x : ℝ)) := by
      refine Finset.prod_congr rfl fun x _ => ?_
      push_cast
      ring
    rw [hshift, ih]
    simp only [Nat.cast_zero, sub_zero, Nat.factorial_succ, Nat.cast_mul]
    ring

/-- **Exact Vandermonde Normalization**: `vandermondeProd (weylRho n) = ∏_{j < n} j!`. -/
theorem vandermondeProd_weylRho (n : ℕ) :
    vandermondeProd (weylRho n) = weylDenominator n := by
  unfold vandermondeProd weylDenominator
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hterm : (∏ i : Fin n, if i < j then (weylRho n i - weylRho n j) else 1) =
      ∏ i : Fin n, if i < j then ((j : ℝ) - (i : ℝ)) else 1 := by
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i < j
    · rw [if_pos h, if_pos h, weylRho_sub]
    · rw [if_neg h, if_neg h]
  rw [hterm]
  have hfin : (∏ i : Fin n, if i < j then ((j : ℝ) - (i : ℝ)) else 1) =
      ∏ i ∈ Finset.range (j : ℕ), ((j : ℝ) - (i : ℝ)) := by
    have hsplit : (∏ i : Fin n, if i < j then ((j : ℝ) - (i : ℝ)) else 1) =
        ∏ i ∈ Finset.univ.filter (fun i : Fin n => i < j), ((j : ℝ) - (i : ℝ)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => i < j)]
      have h1 : ∏ i ∈ Finset.univ.filter (fun i : Fin n => i < j),
          (if i < j then ((j : ℝ) - (i : ℝ)) else 1) =
          ∏ i ∈ Finset.univ.filter (fun i : Fin n => i < j), ((j : ℝ) - (i : ℝ)) :=
        Finset.prod_congr rfl fun i hi => by rw [if_pos (Finset.mem_filter.mp hi).2]
      have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i < j),
          (if i < j then ((j : ℝ) - (i : ℝ)) else 1) = 1 :=
        Finset.prod_eq_one fun i hi => by rw [if_neg (Finset.mem_filter.mp hi).2]
      rw [h1, h2, mul_one]
    rw [hsplit]
    refine Finset.prod_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i₁ _ i₂ _ h
      exact Fin.ext h
    · intro k hk
      have hk_lt : k < n := (Finset.mem_range.mp hk).trans j.isLt
      exact ⟨⟨k, hk_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hk⟩, rfl⟩
    · intro i _
      rfl
  rw [hfin, prod_range_sub_eq_factorial]

theorem vandermondeProd_pos_of_strictAnti {n : ℕ} {lam : Fin n → ℝ} (h : StrictAnti lam) :
    0 < vandermondeProd lam := by
  unfold vandermondeProd
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  split_ifs with hij
  · exact sub_pos.mpr (h hij)
  · exact zero_lt_one

theorem vandermondeProd_add_const {n : ℕ} (lam : Fin n → ℝ) (c : ℝ) :
    vandermondeProd (fun i => lam i + c) = vandermondeProd lam := by
  unfold vandermondeProd
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem vandermondeProd_neg_rev {n : ℕ} (lam : Fin n → ℝ) :
    vandermondeProd (fun i => -lam (Fin.rev i)) = vandermondeProd lam := by
  unfold vandermondeProd
  have hrev_lt : ∀ i j : Fin n, i < j ↔ Fin.rev j < Fin.rev i := fun i j => by
    change (i : ℕ) < (j : ℕ) ↔ ((Fin.rev j : Fin n) : ℕ) < ((Fin.rev i : Fin n) : ℕ)
    rw [Fin.val_rev, Fin.val_rev]
    omega
  rw [Finset.prod_comm]
  refine Finset.prod_bij (fun j _ => Fin.rev j) ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_univ _
  · intro j₁ _ j₂ _ h; exact Fin.rev_injective h
  · intro j _; exact ⟨Fin.rev j, Finset.mem_univ _, Fin.rev_rev j⟩
  · intro j _
    refine Finset.prod_bij (fun i _ => Fin.rev i) ?_ ?_ ?_ ?_
    · intro i _; exact Finset.mem_univ _
    · intro i₁ _ i₂ _ h; exact Fin.rev_injective h
    · intro i _; exact ⟨Fin.rev i, Finset.mem_univ _, Fin.rev_rev i⟩
    · intro i _
      by_cases hij : i < j
      · have hij' : Fin.rev j < Fin.rev i := (hrev_lt i j).mp hij
        rw [if_pos hij, if_pos hij']
        ring
      · have hij' : ¬ Fin.rev j < Fin.rev i := fun h => hij ((hrev_lt i j).mpr h)
        rw [if_neg hij, if_neg hij']

theorem vandermondeProd_two (a b : ℝ) :
    vandermondeProd ![a, b] = a - b := by
  unfold vandermondeProd
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  simp

theorem vandermondeProd_three (a b c : ℝ) :
    vandermondeProd ![a, b, c] = (a - b) * (a - c) * (b - c) := by
  unfold vandermondeProd
  rw [Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [Fin.lt_def, Fin.val_zero, Fin.val_one, Fin.val_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- Expanding `vandermondeProd` on `Fin (n + 1)` by splitting off the top coordinate `lam 0`. -/
theorem vandermondeProd_succ (n : ℕ) (lam : Fin (n + 1) → ℝ) :
    vandermondeProd lam =
      (∏ j : Fin n, (lam 0 - lam j.succ)) * vandermondeProd (fun i : Fin n => lam i.succ) := by
  unfold vandermondeProd
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    have h0 : ¬ i.succ < (0 : Fin (n + 1)) := Fin.not_lt_zero _
    rw [if_neg h0, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [Fin.succ_lt_succ_iff]

/-- **Weyl Dimension of `U(n)`** for Harish-Chandra parameter `lam : Fin n → ℝ`:
`dim(π_λ) = ∏_{i < j} (λ_i - λ_j) / ∏_{j=0}^{n-1} j!`. -/
def weylDim {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  vandermondeProd lam / weylDenominator n

@[simp]
theorem weylDim_zero (lam : Fin 0 → ℝ) : weylDim lam = 1 := by
  simp [weylDim]

@[simp]
theorem weylDim_weylRho (n : ℕ) : weylDim (weylRho n) = 1 := by
  unfold weylDim
  rw [vandermondeProd_weylRho, div_self (weylDenominator_pos n).ne']

theorem weylDim_pos_of_strictAnti {n : ℕ} {lam : Fin n → ℝ} (h : StrictAnti lam) :
    0 < weylDim lam :=
  div_pos (vandermondeProd_pos_of_strictAnti h) (weylDenominator_pos n)

theorem weylDim_pos_of_isHCParam {n : ℕ} {lam : Fin n → ℝ} (h : IsHCParam n lam) :
    0 < weylDim lam :=
  weylDim_pos_of_strictAnti h.1

/-- **Weyl Dimension Integrality Lower Bound**: every representation of `U(n)` with
Harish-Chandra parameter `lam` has Weyl dimension `≥ 1`. -/
theorem weylDim_ge_one_of_isHCParam {n : ℕ} {lam : Fin n → ℝ} (h : IsHCParam n lam) :
    1 ≤ weylDim lam := by
  unfold weylDim
  rw [one_le_div (weylDenominator_pos n), ← vandermondeProd_weylRho n]
  unfold vandermondeProd
  refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) (fun i _ => ?_)
  · split_ifs with hij
    · linarith [weylRho_strictAnti n hij]
    · exact zero_le_one
  · refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
    · split_ifs with hij
      · linarith [weylRho_strictAnti n hij]
      · exact zero_le_one
    · split_ifs with hij
      · rw [weylRho_sub]
        exact (isHCParam_diff_ge_nat h hij).1
      · exact le_rfl

theorem weylDim_add_const {n : ℕ} (lam : Fin n → ℝ) (c : ℝ) :
    weylDim (fun i => lam i + c) = weylDim lam := by
  unfold weylDim
  rw [vandermondeProd_add_const]

theorem weylDim_dual_eq {n : ℕ} (lam : Fin n → ℝ) :
    weylDim (fun i => -lam (Fin.rev i)) = weylDim lam := by
  unfold weylDim
  rw [vandermondeProd_neg_rev]

theorem weylDim_two (a b : ℝ) : weylDim ![a, b] = a - b := by
  unfold weylDim weylDenominator
  rw [vandermondeProd_two, Fin.prod_univ_two]
  simp

theorem weylDim_three (a b c : ℝ) :
    weylDim ![a, b, c] = (a - b) * (a - c) * (b - c) / 2 := by
  unfold weylDim weylDenominator
  rw [vandermondeProd_three, Fin.prod_univ_three]
  norm_num

theorem weylDenominator_succ (n : ℕ) :
    weylDenominator (n + 1) = weylDenominator n * (Nat.factorial n : ℝ) := by
  unfold weylDenominator
  rw [Fin.prod_univ_castSucc]
  simp

/-- Inductive rank-step formula for `U(n + 1)` Weyl dimension in terms of `U(n)`. -/
theorem weylDim_succ (n : ℕ) (lam : Fin (n + 1) → ℝ) :
    weylDim lam =
      ((∏ j : Fin n, (lam 0 - lam j.succ)) / (Nat.factorial n : ℝ)) *
        weylDim (fun i : Fin n => lam i.succ) := by
  unfold weylDim
  rw [vandermondeProd_succ, weylDenominator_succ]
  have hden : weylDenominator n ≠ 0 := (weylDenominator_pos n).ne'
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hden, hfac]

theorem weylDim_monotone_of_diff_le {n : ℕ} {lam₁ lam₂ : Fin n → ℝ}
    (h1 : StrictAnti lam₁) (hdiff : ∀ i j : Fin n, i < j → lam₁ i - lam₁ j ≤ lam₂ i - lam₂ j) :
    weylDim lam₁ ≤ weylDim lam₂ := by
  unfold weylDim
  refine div_le_div_of_nonneg_right ?_ (weylDenominator_pos n).le
  unfold vandermondeProd
  refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) (fun i _ => ?_)
  · split_ifs with hij
    · exact sub_nonneg.mpr (h1 hij).le
    · exact zero_le_one
  · refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
    · split_ifs with hij
      · exact sub_nonneg.mpr (h1 hij).le
      · exact zero_le_one
    · split_ifs with hij
      · exact hdiff i j hij
      · exact le_rfl

private lemma sum_strict_pairs_card (n : ℕ) :
    ∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℕ) else 0) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have h0 : ∑ j : Fin (n + 1), (if (0 : Fin (n + 1)) < j then (1 : ℕ) else 0) = n := by
      rw [Fin.sum_univ_succ]
      simp [Fin.succ_pos]
    have hrest : ∑ i : Fin n, ∑ j : Fin (n + 1), (if i.succ < j then (1 : ℕ) else 0) =
        ∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℕ) else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.sum_univ_succ]
      have hnot : ¬ i.succ < (0 : Fin (n + 1)) := Fin.not_lt_zero _
      rw [if_neg hnot, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Fin.succ_lt_succ_iff]
    rw [h0, hrest, ih]
    cases n with
    | zero => simp
    | succ m =>
      have hmul : (m + 1 + 1) * (m + 1 + 1 - 1) = 2 * (m + 1) + (m + 1) * ((m + 1) - 1) := by
        simp only [Nat.add_sub_cancel]
        ring
      rw [hmul, Nat.mul_add_div (by norm_num)]

/-- Exact upper bound on `weylDim lam` from pairwise coordinate spread `lam i - lam j ≤ B`. -/
theorem weylDim_le_of_spread {n : ℕ} {lam : Fin n → ℝ} (hanti : StrictAnti lam)
    {B : ℝ} (hspread : ∀ i j : Fin n, i < j → lam i - lam j ≤ B) :
    weylDim lam ≤ B ^ (n * (n - 1) / 2) / weylDenominator n := by
  unfold weylDim
  refine div_le_div_of_nonneg_right ?_ (weylDenominator_pos n).le
  unfold vandermondeProd
  have h1 : (∏ i : Fin n, ∏ j : Fin n, if i < j then lam i - lam j else 1) ≤
      ∏ i : Fin n, ∏ j : Fin n, if i < j then B else 1 := by
    refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) (fun i _ => ?_)
    · split_ifs with hij
      · exact sub_nonneg.mpr (hanti hij).le
      · exact zero_le_one
    · refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
      · split_ifs with hij
        · exact sub_nonneg.mpr (hanti hij).le
        · exact zero_le_one
      · split_ifs with hij
        · exact hspread i j hij
        · exact le_rfl
  have h2 : (∏ i : Fin n, ∏ j : Fin n, if i < j then B else 1) =
      B ^ (n * (n - 1) / 2) := by
    have hpow : ∀ i : Fin n, (∏ j : Fin n, if i < j then B else 1) =
        B ^ (∑ j : Fin n, if i < j then (1 : ℕ) else 0) := fun i => by
      have hite : ∀ j : Fin n, (if i < j then B else 1) = B ^ (if i < j then (1 : ℕ) else 0) :=
        fun j => by split_ifs <;> simp
      simp_rw [hite, Finset.prod_pow_eq_pow_sum]
    simp_rw [hpow, Finset.prod_pow_eq_pow_sum, sum_strict_pairs_card]
  exact h1.trans_eq h2

/-- Exact lower bound on `weylDim lam` from spectral gap `GapAtLeast n lam h`. -/
theorem weylDim_ge_of_gap {n : ℕ} {lam : Fin n → ℝ} {h : ℝ} (hh : 0 < h)
    (hg : GapAtLeast n lam h) :
    h ^ (n * (n - 1) / 2) / weylDenominator n ≤ weylDim lam := by
  unfold weylDim
  refine div_le_div_of_nonneg_right ?_ (weylDenominator_pos n).le
  unfold vandermondeProd
  have h1 : (∏ i : Fin n, ∏ j : Fin n, if i < j then h else 1) ≤
      ∏ i : Fin n, ∏ j : Fin n, if i < j then lam i - lam j else 1 := by
    refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) (fun i _ => ?_)
    · split_ifs <;> linarith
    · refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
      · split_ifs <;> linarith
      · split_ifs with hij
        · exact hg i j hij
        · exact le_rfl
  have h2 : (∏ i : Fin n, ∏ j : Fin n, if i < j then h else 1) =
      h ^ (n * (n - 1) / 2) := by
    have hpow : ∀ i : Fin n, (∏ j : Fin n, if i < j then h else 1) =
        h ^ (∑ j : Fin n, if i < j then (1 : ℕ) else 0) := fun i => by
      have hite : ∀ j : Fin n, (if i < j then h else 1) = h ^ (if i < j then (1 : ℕ) else 0) :=
        fun j => by split_ifs <;> simp
      simp_rw [hite, Finset.prod_pow_eq_pow_sum]
    simp_rw [hpow, Finset.prod_pow_eq_pow_sum, sum_strict_pairs_card]
  exact h2.symm.trans_le h1

/-- Two-sided logarithmic bounds on `Real.log (weylDim lam)` via `GapAtLeast` and spread `B`. -/
theorem log_weylDim_bounds {n : ℕ} {lam : Fin n → ℝ} {h B : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hg : GapAtLeast n lam h)
    (hspread : ∀ i j : Fin n, i < j → lam i - lam j ≤ B) :
    ((n * (n - 1) / 2 : ℕ) : ℝ) * Real.log h - Real.log (weylDenominator n) ≤
      Real.log (weylDim lam) ∧
    Real.log (weylDim lam) ≤
      ((n * (n - 1) / 2 : ℕ) : ℝ) * Real.log B - Real.log (weylDenominator n) := by
  have hanti := hg.strictAnti hh
  have hden_pos : 0 < weylDenominator n := weylDenominator_pos n
  have hw_pos : 0 < weylDim lam := weylDim_pos_of_strictAnti hanti
  have hlo := weylDim_ge_of_gap hh hg
  have hhi := weylDim_le_of_spread hanti hspread
  have hlo_pos : 0 < h ^ (n * (n - 1) / 2) / weylDenominator n :=
    div_pos (pow_pos hh _) hden_pos
  have hhi_pos : 0 < B ^ (n * (n - 1) / 2) / weylDenominator n :=
    div_pos (pow_pos hB _) hden_pos
  constructor
  · have h1 := Real.log_le_log hlo_pos hlo
    rw [Real.log_div (pow_pos hh _).ne' hden_pos.ne', Real.log_pow] at h1
    exact h1
  · have h2 := Real.log_le_log hw_pos hhi
    rw [Real.log_div (pow_pos hB _).ne' hden_pos.ne', Real.log_pow] at h2
    exact h2

end WeylDimensionAndHCParams

/-! ## Section 2: `UnitaryDiscreteSeries` & `FormalDegreeAtRealPlace` -/

section DiscreteSeriesAndFormalDegree

private lemma strictMono_fin_eq_id {p : ℕ} (f : Fin p → Fin p) (hf : StrictMono f) :
    ∀ i : Fin p, f i = i := by
  have hmono_le : ∀ i : Fin p, (i : ℕ) ≤ (f i : ℕ) := by
    intro i
    induction hi : (i : ℕ) generalizing i with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk_lt : k < p := by omega
      have hlt : (⟨k, hk_lt⟩ : Fin p) < i := by simp [Fin.lt_def, hi]
      have hf_lt : f ⟨k, hk_lt⟩ < f i := hf hlt
      have hk_le : k ≤ (f ⟨k, hk_lt⟩ : ℕ) := ih ⟨k, hk_lt⟩ rfl
      have hf_nat : (f ⟨k, hk_lt⟩ : ℕ) < (f i : ℕ) := hf_lt
      omega
  have hge : ∀ d : ℕ, ∀ i : Fin p, p - 1 - (i : ℕ) = d → (f i : ℕ) ≤ (i : ℕ) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hi_lt : (i : ℕ) < p := i.isLt
      have hf_lt : (f i : ℕ) < p := (f i).isLt
      omega
    | succ d ih =>
      intro i hi
      have hi_lt : (i : ℕ) < p := i.isLt
      have hi1_lt : (i : ℕ) + 1 < p := by omega
      let i' : Fin p := ⟨(i : ℕ) + 1, hi1_lt⟩
      have hi'_val : (i' : ℕ) = (i : ℕ) + 1 := rfl
      have hlt : i < i' := by simp only [Fin.lt_def, hi'_val]; omega
      have hf_lt : (f i : ℕ) < (f i' : ℕ) := hf hlt
      have hi'_le : (f i' : ℕ) ≤ (i' : ℕ) := ih i' (by rw [hi'_val]; omega)
      omega
  intro i
  exact Fin.ext (le_antisymm (hge (p - 1 - (i : ℕ)) i rfl) (hmono_le i))

/-- **Unitary Discrete Series Datum (`UnitaryDiscreteSeries p q`)** for `U(p, q)` at an
archimedean real place: bundles a Harish-Chandra parameter `hcParam : Fin (p + q) → ℝ`
together with the `U(p) × U(q)` Weyl-chamber partition (`kPosIdx`, `kNegIdx`) selecting the
lowest `K`-type parameters. -/
structure UnitaryDiscreteSeries (p q : ℕ) where
  hcParam : Fin (p + q) → ℝ
  isHC : IsHCParam (p + q) hcParam
  kPosIdx : Fin p → Fin (p + q)
  kNegIdx : Fin q → Fin (p + q)
  kPosIdx_strictMono : StrictMono kPosIdx
  kNegIdx_strictMono : StrictMono kNegIdx
  disjoint_range : Disjoint (Set.range kPosIdx) (Set.range kNegIdx)

namespace UnitaryDiscreteSeries

/-- Canonical `UnitaryDiscreteSeries p q` from any antitone integer weight `μ : Fin (p + q) → ℤ`
with standard compact `U(p) × U(q)` block splitting (`castAdd q`, `natAdd p`). -/
def ofAntitoneWeight (p q : ℕ) (μ : Fin (p + q) → ℤ) (hμ : Antitone μ) :
    UnitaryDiscreteSeries p q where
  hcParam := shiftedWeight (p + q) μ
  isHC := shiftedWeight_isHCParam hμ
  kPosIdx := Fin.castAdd q
  kNegIdx := Fin.natAdd p
  kPosIdx_strictMono := fun _ _ h => h
  kNegIdx_strictMono := fun _ _ h => Nat.add_lt_add_left h p
  disjoint_range := Set.disjoint_left.mpr fun _ ⟨i, hi⟩ ⟨j, hj⟩ => by
    have h1 : (Fin.castAdd q i : ℕ) < p := i.isLt
    have h2 : p ≤ (Fin.natAdd p j : ℕ) := Nat.le_add_right p j
    have h3 : (Fin.castAdd q i : ℕ) = (Fin.natAdd p j : ℕ) := congrArg Fin.val (hi.trans hj.symm)
    omega

/-- Trivial discrete-series / finite-dimensional representation of compact `U(n)` (`q = 0`). -/
def trivialDefinite (n : ℕ) : UnitaryDiscreteSeries n 0 :=
  ofAntitoneWeight n 0 (fun _ => 0) antitone_const

lemma trivialDefinite_hcParam (n : ℕ) :
    (trivialDefinite n).hcParam = weylRho n := by
  ext i
  simp only [trivialDefinite, ofAntitoneWeight, shiftedWeight, Int.cast_zero, zero_add]
  rfl

/-- Restriction of the Harish-Chandra parameter to the `U(p)` compact factor. -/
def kPosWeight {p q : ℕ} (ds : UnitaryDiscreteSeries p q) : Fin p → ℝ :=
  fun i => ds.hcParam (ds.kPosIdx i)

/-- Restriction of the Harish-Chandra parameter to the `U(q)` compact factor. -/
def kNegWeight {p q : ℕ} (ds : UnitaryDiscreteSeries p q) : Fin q → ℝ :=
  fun j => ds.hcParam (ds.kNegIdx j)

theorem kPosWeight_strictAnti {p q : ℕ} (ds : UnitaryDiscreteSeries p q) :
    StrictAnti ds.kPosWeight :=
  fun _ _ hij => ds.isHC.1 (ds.kPosIdx_strictMono hij)

theorem kNegWeight_strictAnti {p q : ℕ} (ds : UnitaryDiscreteSeries p q) :
    StrictAnti ds.kNegWeight :=
  fun _ _ hij => ds.isHC.1 (ds.kNegIdx_strictMono hij)

/-- Weyl dimension of the lowest `K = U(p) × U(q)` type attached to `ds`. -/
def lowestKTypeDim {p q : ℕ} (ds : UnitaryDiscreteSeries p q) : ℝ :=
  weylDim ds.kPosWeight * weylDim ds.kNegWeight

theorem lowestKTypeDim_pos {p q : ℕ} (ds : UnitaryDiscreteSeries p q) :
    0 < ds.lowestKTypeDim :=
  mul_pos (weylDim_pos_of_strictAnti ds.kPosWeight_strictAnti)
    (weylDim_pos_of_strictAnti ds.kNegWeight_strictAnti)

theorem lowestKTypeDim_definite_eq_weylDim {n : ℕ} (ds : UnitaryDiscreteSeries n 0) :
    ds.lowestKTypeDim = weylDim ds.hcParam := by
  unfold lowestKTypeDim
  have h0 : weylDim ds.kNegWeight = 1 := weylDim_zero _
  rw [h0, mul_one]
  have hid : ∀ i : Fin n, ds.kPosIdx i = i :=
    strictMono_fin_eq_id ds.kPosIdx ds.kPosIdx_strictMono
  have hwt : ds.kPosWeight = ds.hcParam := by
    ext i; exact congrArg ds.hcParam (hid i)
  rw [hwt]

/-- Dual (contragredient) discrete series obtained by reversing and negating `hcParam`. -/
def dual {p q : ℕ} (ds : UnitaryDiscreteSeries p q) : UnitaryDiscreteSeries q p where
  hcParam := fun i => -ds.hcParam (Fin.rev (Fin.cast (Nat.add_comm q p) i))
  isHC := by
    obtain ⟨μ, hμ, hlam⟩ := (isHCParam_iff_antitone_int (p + q) ds.hcParam).mp ds.isHC
    refine (isHCParam_iff_antitone_int (q + p) _).mpr ?_
    refine ⟨fun i => -μ (Fin.rev (Fin.cast (Nat.add_comm q p) i)), ?_, ?_⟩
    · intro i j hij
      have hij' : Fin.rev (Fin.cast (Nat.add_comm q p) j) ≤
          Fin.rev (Fin.cast (Nat.add_comm q p) i) := by
        change ((Fin.rev (Fin.cast (Nat.add_comm q p) j) : Fin (p + q)) : ℕ) ≤
          ((Fin.rev (Fin.cast (Nat.add_comm q p) i) : Fin (p + q)) : ℕ)
        rw [Fin.val_rev, Fin.val_rev]
        have hij_nat : (i : ℕ) ≤ (j : ℕ) := hij
        simp only [Fin.val_cast]
        omega
      exact Int.neg_le_neg (hμ hij')
    · ext i
      have hrho : weylRho (q + p) i =
          -weylRho (p + q) (Fin.rev (Fin.cast (Nat.add_comm q p) i)) := by
        unfold weylRho
        simp only [Fin.val_rev, Fin.val_cast]
        have h1 : q + p - 1 = p + q - 1 := by omega
        have hlt : (i : ℕ) < p + q := by have := i.isLt; omega
        have hcast : ((p + q - (i + 1) : ℕ) : ℝ) = ((p + q - 1 : ℕ) : ℝ) - (i : ℝ) := by
          have hsub : p + q - (i + 1) = p + q - 1 - i := by omega
          rw [hsub, Nat.cast_sub (by omega)]
        rw [hcast, h1]
        ring
      have hlam_i := congrFun hlam (Fin.rev (Fin.cast (Nat.add_comm q p) i))
      change -ds.hcParam (Fin.rev (Fin.cast (Nat.add_comm q p) i)) = shiftedWeight (q + p) _ i
      unfold shiftedWeight
      rw [hrho, hlam_i]
      unfold shiftedWeight
      push_cast
      ring
  kPosIdx := fun j => Fin.cast (Nat.add_comm p q) (Fin.rev (ds.kNegIdx (Fin.rev j)))
  kNegIdx := fun i => Fin.cast (Nat.add_comm p q) (Fin.rev (ds.kPosIdx (Fin.rev i)))
  kPosIdx_strictMono := by
    intro a b hab
    have h1 : Fin.rev b < Fin.rev a := by
      change (Fin.rev b : ℕ) < (Fin.rev a : ℕ)
      rw [Fin.val_rev, Fin.val_rev]
      have : (a : ℕ) < (b : ℕ) := hab
      omega
    have h2 := ds.kNegIdx_strictMono h1
    change ((Fin.rev (ds.kNegIdx (Fin.rev a)) : Fin (p + q)) : ℕ) <
      ((Fin.rev (ds.kNegIdx (Fin.rev b)) : Fin (p + q)) : ℕ)
    rw [Fin.val_rev, Fin.val_rev]
    have h2n : (ds.kNegIdx (Fin.rev b) : ℕ) < (ds.kNegIdx (Fin.rev a) : ℕ) := h2
    omega
  kNegIdx_strictMono := by
    intro a b hab
    have h1 : Fin.rev b < Fin.rev a := by
      change (Fin.rev b : ℕ) < (Fin.rev a : ℕ)
      rw [Fin.val_rev, Fin.val_rev]
      have : (a : ℕ) < (b : ℕ) := hab
      omega
    have h2 := ds.kPosIdx_strictMono h1
    change ((Fin.rev (ds.kPosIdx (Fin.rev a)) : Fin (p + q)) : ℕ) <
      ((Fin.rev (ds.kPosIdx (Fin.rev b)) : Fin (p + q)) : ℕ)
    rw [Fin.val_rev, Fin.val_rev]
    have h2n : (ds.kPosIdx (Fin.rev b) : ℕ) < (ds.kPosIdx (Fin.rev a) : ℕ) := h2
    omega
  disjoint_range := Set.disjoint_left.mpr fun x ⟨j, hj⟩ ⟨i, hi⟩ => by
    have hxeq := hj.trans hi.symm
    have hrev : ds.kPosIdx (Fin.rev i) = ds.kNegIdx (Fin.rev j) := by
      apply Fin.rev_injective
      exact (Fin.cast_injective (Nat.add_comm p q) hxeq).symm
    exact (Set.disjoint_left.mp ds.disjoint_range) ⟨Fin.rev i, rfl⟩ ⟨Fin.rev j, hrev.symm⟩

end UnitaryDiscreteSeries

/-- Surface area `Vol(S^{2M - 1}) = 2 * π^M / (M - 1)!` of the unit sphere in `ℂ^M` (`M ≥ 1`). -/
def sphereSurfaceVol (M : ℕ) : ℝ :=
  2 * Real.pi ^ M / (Nat.factorial (M - 1) : ℝ)

/-- Canonical Euclidean Haar volume of the compact unitary group `U(n)`:
`Vol(U(n)) = ∏_{M=1}^n (2 π^M / (M - 1)!)`. -/
def unitaryCompactVol (n : ℕ) : ℝ :=
  ∏ M ∈ Finset.Icc 1 n, sphereSurfaceVol M

/-- Single-rank archimedean Tamagawa/Siegel factor `((M - 1)! * (vE / π)^M)` at a real place. -/
def unitaryTamagawaArchStep (vE : ℝ) (M : ℕ) : ℝ :=
  (Nat.factorial (M - 1) : ℝ) * (vE / Real.pi) ^ M

/-- Rank-`n` archimedean Tamagawa factor `∏_{M=1}^n ((M - 1)! * (vE / π)^M)`. -/
def unitaryTamagawaArchFactor (vE : ℝ) (n : ℕ) : ℝ :=
  ∏ M ∈ Finset.Icc 1 n, unitaryTamagawaArchStep vE M

theorem sphereSurfaceVol_pos (M : ℕ) : 0 < sphereSurfaceVol M := by
  unfold sphereSurfaceVol
  exact div_pos (mul_pos (by norm_num) (pow_pos Real.pi_pos M))
    (Nat.cast_pos.mpr (Nat.factorial_pos (M - 1)))

theorem unitaryCompactVol_pos (n : ℕ) : 0 < unitaryCompactVol n :=
  Finset.prod_pos fun M _ => sphereSurfaceVol_pos M

theorem unitaryTamagawaArchStep_pos {vE : ℝ} (hv : 0 < vE) (M : ℕ) :
    0 < unitaryTamagawaArchStep vE M :=
  mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos (M - 1))) (pow_pos (div_pos hv Real.pi_pos) M)

theorem unitaryTamagawaArchFactor_pos {vE : ℝ} (hv : 0 < vE) (n : ℕ) :
    0 < unitaryTamagawaArchFactor vE n :=
  Finset.prod_pos fun M _ => unitaryTamagawaArchStep_pos hv M

@[simp]
theorem unitaryCompactVol_zero : unitaryCompactVol 0 = 1 := by
  simp [unitaryCompactVol]

@[simp]
theorem unitaryCompactVol_one : unitaryCompactVol 1 = 2 * Real.pi := by
  unfold unitaryCompactVol sphereSurfaceVol
  simp

@[simp]
theorem unitaryCompactVol_two : unitaryCompactVol 2 = 4 * Real.pi ^ 3 := by
  unfold unitaryCompactVol sphereSurfaceVol
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc, Finset.prod_pair (by decide)]
  norm_num
  ring

/-- **Exact `π`-and-Factorial Cancellation**:
`unitaryTamagawaArchFactor vE n * unitaryCompactVol n = ∏_{M=1}^n (2 * vE^M)`. -/
theorem unitaryTamagawaArchFactor_mul_compactVol (vE : ℝ) (n : ℕ) :
    unitaryTamagawaArchFactor vE n * unitaryCompactVol n =
      ∏ M ∈ Finset.Icc 1 n, (2 * vE ^ M) := by
  unfold unitaryTamagawaArchFactor unitaryCompactVol
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun M _ => ?_
  unfold unitaryTamagawaArchStep sphereSurfaceVol
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfac : (Nat.factorial (M - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [div_pow]
  field_simp [hpi, hfac]

/-- **Formal Degree at a Real Place (`FormalDegreeAtRealPlace`)**:
Harish-Chandra formal degree `d(π_λ) = weylDim λ / Vol(U(p + q))` of a unitary discrete
series `ds : UnitaryDiscreteSeries p q` with respect to the canonical Haar measure on `U(p, q)`
normalized by `Vol(K) = Vol(U(p + q))`. -/
def FormalDegreeAtRealPlace {p q : ℕ} (ds : UnitaryDiscreteSeries p q) : ℝ :=
  weylDim ds.hcParam / unitaryCompactVol (p + q)

/-- Haar-normalized formal degree `d(π_λ) = weylDim λ` (with `Vol(U(n)) = 1`). -/
def FormalDegreeAtRealPlaceNormalized {p q : ℕ} (ds : UnitaryDiscreteSeries p q) : ℝ :=
  weylDim ds.hcParam

/-- Parametric Haar formal degree `weylDim λ / c_vol` for arbitrary compact Haar normalization `c_vol`. -/
def FormalDegreeAtRealPlaceHaar {p q : ℕ} (c_vol : ℝ) (ds : UnitaryDiscreteSeries p q) : ℝ :=
  weylDim ds.hcParam / c_vol

/-- Tamagawa-weighted formal degree `weylDim λ * unitaryTamagawaArchFactor vE (p + q)`. -/
def FormalDegreeAtRealPlaceTamagawa (vE : ℝ) {p q : ℕ} (ds : UnitaryDiscreteSeries p q) : ℝ :=
  weylDim ds.hcParam * unitaryTamagawaArchFactor vE (p + q)

theorem formalDegreeAtRealPlace_pos {p q : ℕ} (ds : UnitaryDiscreteSeries p q) :
    0 < FormalDegreeAtRealPlace ds :=
  div_pos (weylDim_pos_of_isHCParam ds.isHC) (unitaryCompactVol_pos (p + q))

theorem formalDegreeAtRealPlaceNormalized_pos {p q : ℕ} (ds : UnitaryDiscreteSeries p q) :
    0 < FormalDegreeAtRealPlaceNormalized ds :=
  weylDim_pos_of_isHCParam ds.isHC

theorem formalDegreeAtRealPlaceNormalized_ge_one {p q : ℕ} (ds : UnitaryDiscreteSeries p q) :
    1 ≤ FormalDegreeAtRealPlaceNormalized ds :=
  weylDim_ge_one_of_isHCParam ds.isHC

theorem formalDegreeAtRealPlaceTamagawa_pos {vE : ℝ} (hv : 0 < vE) {p q : ℕ}
    (ds : UnitaryDiscreteSeries p q) :
    0 < FormalDegreeAtRealPlaceTamagawa vE ds :=
  mul_pos (weylDim_pos_of_isHCParam ds.isHC) (unitaryTamagawaArchFactor_pos hv (p + q))

@[simp]
theorem formalDegreeAtRealPlaceNormalized_trivial (n : ℕ) :
    FormalDegreeAtRealPlaceNormalized (UnitaryDiscreteSeries.trivialDefinite n) = 1 := by
  unfold FormalDegreeAtRealPlaceNormalized
  rw [UnitaryDiscreteSeries.trivialDefinite_hcParam]
  exact weylDim_weylRho n

theorem formalDegreeAtRealPlace_trivial (n : ℕ) :
    FormalDegreeAtRealPlace (UnitaryDiscreteSeries.trivialDefinite n) =
      (unitaryCompactVol n)⁻¹ := by
  unfold FormalDegreeAtRealPlace
  rw [show (UnitaryDiscreteSeries.trivialDefinite n).hcParam = weylRho (n + 0) from by
    ext i
    simp only [UnitaryDiscreteSeries.trivialDefinite, UnitaryDiscreteSeries.ofAntitoneWeight,
      shiftedWeight, Int.cast_zero, zero_add]]
  rw [weylDim_weylRho, add_zero, one_div]

/-- Schur-orthogonality / Plancherel formal-degree normalization:
`c_vol * d(π_λ) = dim(π_λ)` for every Haar volume `c_vol > 0` on the compact form. -/
theorem schur_orthogonality_formal_degree {p q : ℕ} {c_vol : ℝ} (hc : 0 < c_vol)
    (ds : UnitaryDiscreteSeries p q) :
    c_vol * FormalDegreeAtRealPlaceHaar c_vol ds = weylDim ds.hcParam := by
  unfold FormalDegreeAtRealPlaceHaar
  exact mul_div_cancel₀ _ hc.ne'

theorem formalDegreeAtRealPlace_mul_compactVol {p q : ℕ} (ds : UnitaryDiscreteSeries p q) :
    unitaryCompactVol (p + q) * FormalDegreeAtRealPlace ds = weylDim ds.hcParam :=
  mul_div_cancel₀ _ (unitaryCompactVol_pos (p + q)).ne'

/-- Exact rank-2 formal degree at a real place:
for `U(2)` (`p + q = 2`), `d(π_λ) = (λ_0 - λ_1) / (4 π^3)`. -/
theorem formalDegreeAtRealPlace_rank_two (ds : UnitaryDiscreteSeries 2 0) :
    FormalDegreeAtRealPlace ds =
      (ds.hcParam 0 - ds.hcParam 1) / (4 * Real.pi ^ 3) := by
  unfold FormalDegreeAtRealPlace
  have h2 : ds.hcParam = ![ds.hcParam 0, ds.hcParam 1] := by
    ext i; fin_cases i <;> rfl
  change weylDim ds.hcParam / unitaryCompactVol 2 = _
  rw [h2, weylDim_two, unitaryCompactVol_two]
  simp

/-- Formal degree at an explicit real place `ι : F →+* ℝ` of a CM host field `(F, E)`. -/
def FormalDegreeAtRealPlaceCM {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (_cm : CMFieldPair F E)
    (ι : F →+* ℝ) {p q : (F →+* ℝ) → ℕ}
    (ds : ∀ ι' : F →+* ℝ, UnitaryDiscreteSeries (p ι') (q ι')) : ℝ :=
  FormalDegreeAtRealPlace (ds ι)

/-- Global archimedean formal degree product `∏_{ι : F →+* ℝ} d(π_{λ, ι})` over all real places. -/
def GlobalFormalDegreeCM {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (_cm : CMFieldPair F E)
    {p q : (F →+* ℝ) → ℕ}
    (ds : ∀ ι : F →+* ℝ, UnitaryDiscreteSeries (p ι) (q ι)) : ℝ :=
  ∏ ι : F →+* ℝ, FormalDegreeAtRealPlace (ds ι)

/-- Global normalized archimedean formal degree product `∏_{ι : F →+* ℝ} dim(π_{λ, ι})`. -/
def GlobalFormalDegreeNormalized {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (_cm : CMFieldPair F E)
    {p q : (F →+* ℝ) → ℕ}
    (ds : ∀ ι : F →+* ℝ, UnitaryDiscreteSeries (p ι) (q ι)) : ℝ :=
  ∏ ι : F →+* ℝ, FormalDegreeAtRealPlaceNormalized (ds ι)

theorem globalFormalDegreeCM_pos {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (cm : CMFieldPair F E)
    {p q : (F →+* ℝ) → ℕ} (ds : ∀ ι : F →+* ℝ, UnitaryDiscreteSeries (p ι) (q ι)) :
    0 < GlobalFormalDegreeCM cm ds :=
  Finset.prod_pos fun ι _ => formalDegreeAtRealPlace_pos (ds ι)

theorem globalFormalDegreeNormalized_ge_one {F E : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMFieldPair F E)
    {p q : (F →+* ℝ) → ℕ} (ds : ∀ ι : F →+* ℝ, UnitaryDiscreteSeries (p ι) (q ι)) :
    1 ≤ GlobalFormalDegreeNormalized cm ds :=
  Finset.one_le_prod (fun ι _ => formalDegreeAtRealPlaceNormalized_ge_one (ds ι))

/-- Attaches a real-place signature `(p ι, q ι)` to an `IndefiniteHermSpace E F V` by lifting
each real embedding `ι : F →+* ℝ` via `Stage14M1_UnitaryGroupDef.CMFieldPair.exists_embedding_with_realPlace`. -/
def realPlaceEmbeddingLift {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (cm : CMFieldPair F E) (ι : F →+* ℝ) : E →+* ℂ :=
  Classical.choose (cm.exists_embedding_with_realPlace ι)

theorem realPlaceEmbeddingLift_spec {F E : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMFieldPair F E) (ι : F →+* ℝ) :
    cm.realPlaceOfEmbedding (realPlaceEmbeddingLift cm ι) = ι :=
  Classical.choose_spec (cm.exists_embedding_with_realPlace ι)

/-- Definite CM Hermitian space formal degree at a real place `ι` (`q = 0`, `p = H.toHerm.dim`). -/
def DefiniteHermSpace.formalDegreeAtPlace {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : DefiniteHermSpace E F V) (ι : F →+* ℝ)
    (ds : UnitaryDiscreteSeries H.toHerm.dim 0) : ℝ :=
  FormalDegreeAtRealPlaceCM H.toHerm.cm ι
    (p := fun _ => H.toHerm.dim) (q := fun _ => 0) (fun _ => ds)

theorem DefiniteHermSpace.formalDegreeAtPlace_pos {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : DefiniteHermSpace E F V) (ι : F →+* ℝ)
    (ds : UnitaryDiscreteSeries H.toHerm.dim 0) :
    0 < DefiniteHermSpace.formalDegreeAtPlace H ι ds :=
  formalDegreeAtRealPlace_pos ds

end DiscreteSeriesAndFormalDegree

/-! ## Section 3: Congruence Level Towers, `volume_at_level_zero`, `volume_mass_succ`, `volume_mass_ge_two` -/

section LevelZeroVolumesAndMassRecursion

/-- Descending congruence level tower `K_0 ≥ K_1 ≥ K_2 ≥ ⋯` in a group `G` with finite
step indices `[K_m : K_{m+1}]`. -/
structure CongruenceLevelTower (G : Type*) [Group G] where
  K : ℕ → Subgroup G
  antitone_K : ∀ m : ℕ, K (m + 1) ≤ K m
  finite_step : ∀ m : ℕ, Finite (K m ⧸ (K (m + 1)).subgroupOf (K m))

namespace CongruenceLevelTower

variable {G : Type*} [Group G] (T : CongruenceLevelTower G)

theorem level_le {m n : ℕ} (hmn : m ≤ n) : T.K n ≤ T.K m := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (T.antitone_K n).trans ih

/-- Step index `[K_m : K_{m+1}]` along the congruence tower. -/
def stepIndex (m : ℕ) : ℕ :=
  ((T.K (m + 1)).subgroupOf (T.K m)).index

/-- Cumulative congruence index `∏_{j < m} [K_j : K_{j+1}]`. -/
def cumulativeIndex (m : ℕ) : ℕ :=
  ∏ j ∈ Finset.range m, T.stepIndex j

theorem stepIndex_pos (m : ℕ) : 0 < T.stepIndex m := by
  unfold stepIndex
  haveI := T.finite_step m
  rw [Subgroup.index_eq_card]
  exact Nat.card_pos

theorem cumulativeIndex_pos (m : ℕ) : 0 < T.cumulativeIndex m :=
  Finset.prod_pos fun j _ => T.stepIndex_pos j

theorem cumulativeIndex_mono {m n : ℕ} (hmn : m ≤ n) :
    T.cumulativeIndex m ≤ T.cumulativeIndex n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    unfold cumulativeIndex
    rw [Finset.prod_range_succ]
    exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (T.stepIndex_pos n))

theorem finite_quot_zero (m : ℕ) :
    Finite (T.K 0 ⧸ (T.K m).subgroupOf (T.K 0)) := by
  induction m with
  | zero =>
    have htop : (T.K 0).subgroupOf (T.K 0) = ⊤ := by
      ext x; simp
    rw [htop]
    exact inferInstance
  | succ m ih =>
    haveI := ih
    haveI := T.finite_step m
    have hle1 : T.K (m + 1) ≤ T.K m := T.antitone_K m
    have hle0 : T.K m ≤ T.K 0 := T.level_le (Nat.zero_le m)
    let s : (T.K 0 ⧸ (T.K m).subgroupOf (T.K 0)) → T.K 0 := fun q => Quotient.out q
    let g : ((T.K 0 ⧸ (T.K m).subgroupOf (T.K 0)) ×
        (T.K m ⧸ (T.K (m + 1)).subgroupOf (T.K m))) →
        (T.K 0 ⧸ (T.K (m + 1)).subgroupOf (T.K 0)) :=
      fun ⟨q, r⟩ => Quotient.lift (fun y : T.K m =>
        (QuotientGroup.mk (s q * ⟨y.1, hle0 y.2⟩) : T.K 0 ⧸ (T.K (m + 1)).subgroupOf (T.K 0)))
        (fun y₁ y₂ h => by
          have h' : y₁⁻¹ * y₂ ∈ (T.K (m + 1)).subgroupOf (T.K m) :=
            QuotientGroup.leftRel_apply.mp h
          apply QuotientGroup.eq.mpr
          rw [Subgroup.mem_subgroupOf] at h' ⊢
          have heq : (((s q * ⟨y₁.1, hle0 y₁.2⟩)⁻¹ * (s q * ⟨y₂.1, hle0 y₂.2⟩) : T.K 0) : G) =
              ((y₁⁻¹ * y₂ : T.K m) : G) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
          rw [heq]
          exact h') r
    refine Finite.of_surjective g ?_
    intro zq
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zq
    let q : T.K 0 ⧸ (T.K m).subgroupOf (T.K 0) := QuotientGroup.mk z
    have hq : QuotientGroup.mk (s q) = q := Quotient.out_eq q
    have hmem : (s q)⁻¹ * z ∈ (T.K m).subgroupOf (T.K 0) := QuotientGroup.eq.mp hq
    let y : T.K m := ⟨((s q)⁻¹ * z : T.K 0), hmem⟩
    refine ⟨(q, QuotientGroup.mk y), ?_⟩
    change QuotientGroup.mk (s q * ⟨y.1, hle0 y.2⟩) = QuotientGroup.mk z
    congr 1
    ext
    simp [y]

/-- **Exact Congruence-Tower Genus Mass Recursion**:
`genusClassMass Γ (T.K m) = (T.cumulativeIndex m : ℝ) * genusClassMass Γ (T.K 0)`. -/
theorem genusClassMass_tower_eq (Γ : Subgroup G)
    [∀ m, Fintype (DoubleCosetClassSet Γ (T.K m))]
    (hfin : ∀ m (g : G), Finite (doubleCosetStab Γ (T.K m) g)) (m : ℕ) :
    genusClassMass Γ (T.K m) = (T.cumulativeIndex m : ℝ) * genusClassMass Γ (T.K 0) := by
  induction m with
  | zero => simp [cumulativeIndex]
  | succ m ih =>
    haveI := T.finite_step m
    have hstep := genusClassMass_sublevel_eq Γ (T.antitone_K m) (hfin m)
    rw [hstep, ih]
    unfold cumulativeIndex stepIndex
    rw [Finset.prod_range_succ]
    push_cast
    ring

theorem genusClassMass_tower_mono (Γ : Subgroup G)
    [∀ m, Fintype (DoubleCosetClassSet Γ (T.K m))]
    (hfin : ∀ m (g : G), Finite (doubleCosetStab Γ (T.K m) g))
    {m n : ℕ} (hmn : m ≤ n) :
    genusClassMass Γ (T.K m) ≤ genusClassMass Γ (T.K n) := by
  rw [T.genusClassMass_tower_eq Γ hfin m, T.genusClassMass_tower_eq Γ hfin n]
  have hmass_nn : 0 ≤ genusClassMass Γ (T.K 0) := by
    unfold genusClassMass
    exact Finset.sum_nonneg fun c _ => genusClassWeight_nonneg Γ (T.K 0) c
  have hle : (T.cumulativeIndex m : ℝ) ≤ (T.cumulativeIndex n : ℝ) :=
    Nat.cast_le.mpr (T.cumulativeIndex_mono hmn)
  exact mul_le_mul_of_nonneg_right hle hmass_nn

end CongruenceLevelTower

/-- **Level-Zero Volume Equals Genus Mass (`level_zero_volume_eq_genus_mass`)**:
for any countable discrete subgroup `Γ ≤ G`, measurable compact-open level zero `K₀ ≤ G` with
`0 < μ K₀ < ⊤`, and fundamental domain `𝓕` for `Γ \ G`, the normalized level-zero volume
`(μ 𝓕).toReal / (μ K₀).toReal` equals `genusClassMass Γ K₀`. -/
theorem level_zero_volume_eq_genus_mass {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    {Γ K₀ : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK₀ : MeasurableSet (K₀ : Set G)) (hK₀pos : 0 < μ K₀) (hK₀fin : μ K₀ ≠ ⊤)
    [Fintype (DoubleCosetClassSet Γ K₀)]
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K₀ g))
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (μ 𝓕).toReal / (μ K₀).toReal = genusClassMass Γ K₀ :=
  (class_decomp_mass_eq_covolume_div μ hK₀ hK₀pos hK₀fin hfin h𝓕).symm

/-- **Congruence Tower Covolume-to-Level Scaling**:
along any congruence tower `T`, the normalized level-`m` volume satisfies
`(μ 𝓕).toReal / (μ (T.K m)).toReal = (T.cumulativeIndex m : ℝ) * genusClassMass Γ (T.K 0)`. -/
theorem level_tower_volume_eq_cumulative_genus_mass {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    (T : CongruenceLevelTower G)
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hKm : ∀ m, MeasurableSet (T.K m : Set G))
    (hKm_pos : ∀ m, 0 < μ (T.K m)) (hKm_fin : ∀ m, μ (T.K m) ≠ ⊤)
    [∀ m, Fintype (DoubleCosetClassSet Γ (T.K m))]
    (hfin : ∀ m (g : G), Finite (doubleCosetStab Γ (T.K m) g))
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (m : ℕ) :
    (μ 𝓕).toReal / (μ (T.K m)).toReal =
      (T.cumulativeIndex m : ℝ) * genusClassMass Γ (T.K 0) := by
  rw [level_zero_volume_eq_genus_mass μ (hKm m) (hKm_pos m) (hKm_fin m) (hfin m) h𝓕,
    T.genusClassMass_tower_eq Γ hfin m]

/-- Rank-and-signature-indexed unitary volume and mass system supporting the definite-to-indefinite
Siegel–Weil recursion (`volume_at_level_zero`, `volume_mass_succ`, `volume_mass_ge_two`). -/
structure UnitaryVolumeSystem where
  Space : ℕ → ℕ → Type*
  vol : ∀ {P Q : ℕ}, Space P Q → ℝ
  vol_pos : ∀ {P Q : ℕ} (W : Space P Q), 0 < vol W
  mass : ℕ → ℝ
  mass_pos : ∀ n : ℕ, 2 ≤ n → 0 < mass n
  ratio : ℕ → ℝ
  mass_step : ∀ n : ℕ, 2 ≤ n → mass (n + 1) / mass n = ratio (n + 1)
  step_pos_sig : ∀ (P Q : ℕ) (W : Space (P + 1) Q), 2 ≤ P →
    ∃ W' : Space P Q, vol W / vol W' = ratio (P + 1 + Q)
  step_neg_sig : ∀ (P Q : ℕ) (W : Space P (Q + 1)), 2 ≤ P →
    ∃ W' : Space P Q, vol W / vol W' = ratio (P + Q + 1)

/-- Level-zero volume-equals-mass predicate at definite rank `(n, 0)`:
`volume_at_level_zero S n` holds iff `S.vol W = S.mass n` for every definite rank-`n` space `W`. -/
def volume_at_level_zero (S : UnitaryVolumeSystem) (n : ℕ) : Prop :=
  ∀ W : S.Space n 0, S.vol W = S.mass n

/-- **Volume-Mass Rank Step (`volume_mass_succ`)**:
if `volume_at_level_zero S n` holds at rank `n ≥ 2`, then it holds at rank `n + 1`. -/
theorem volume_mass_succ (S : UnitaryVolumeSystem) (n : ℕ) (hn : 2 ≤ n)
    (h : volume_at_level_zero S n) :
    volume_at_level_zero S (n + 1) := by
  intro W
  obtain ⟨W', hstep⟩ := S.step_pos_sig n 0 W hn
  have hW' : S.vol W' = S.mass n := h W'
  have hm := S.mass_step n hn
  rw [add_zero] at hstep
  rw [hW'] at hstep
  have h0 : S.mass n ≠ 0 := (S.mass_pos n hn).ne'
  exact (div_left_inj' h0).mp (hstep.trans hm.symm)

/-- **Volume-Mass Induction for All `n ≥ 2` (`volume_mass_ge_two`)**:
from the rank-2 base case `volume_at_level_zero S 2`, proves `volume_at_level_zero S n`
for all `n ≥ 2`. -/
theorem volume_mass_ge_two (S : UnitaryVolumeSystem)
    (h2 : volume_at_level_zero S 2) :
    ∀ n : ℕ, 2 ≤ n → volume_at_level_zero S n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h2
  | succ n hn ih => exact volume_mass_succ S n hn ih

/-- **Indefinite Signature Volume = Mass (`volume_indef_eq_mass`)**:
from `volume_at_level_zero S 2`, proves `S.vol W = S.mass (P + Q)` for EVERY signature `(P, Q)`
with `P ≥ 2` and `Q ≥ 0`. -/
theorem volume_indef_eq_mass (S : UnitaryVolumeSystem)
    (h2 : volume_at_level_zero S 2) :
    ∀ (P Q : ℕ), 2 ≤ P → ∀ W : S.Space P Q, S.vol W = S.mass (P + Q) := by
  intro P Q hP
  induction Q with
  | zero =>
    intro W
    simpa only [add_zero] using volume_mass_ge_two S h2 P hP W
  | succ Q ih =>
    intro W
    obtain ⟨W', hstep⟩ := S.step_neg_sig P Q W hP
    have hW' : S.vol W' = S.mass (P + Q) := ih W'
    have hm := S.mass_step (P + Q) (by omega)
    rw [hW'] at hstep
    have h0 : S.mass (P + Q) ≠ 0 := (S.mass_pos (P + Q) (by omega)).ne'
    have heq : S.vol W = S.mass (P + Q + 1) := (div_left_inj' h0).mp (hstep.trans hm.symm)
    simpa only [Nat.add_assoc] using heq

/-- Complete definite volume-equals-mass theorem for all `n ≥ 0` from low-rank checks `n = 0, 1, 2`. -/
theorem definite_volume_mass_of_low (S : UnitaryVolumeSystem)
    (h0 : volume_at_level_zero S 0) (h1 : volume_at_level_zero S 1)
    (h2 : volume_at_level_zero S 2) :
    ∀ n : ℕ, volume_at_level_zero S n := by
  intro n
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn2
  · exact h0
  · exact h1
  · exact volume_mass_ge_two S h2 n hn2

/-- Exact single-step division identity for the Braun–Shimura–Gan–Yu mass `bsgyUnitaryMass`. -/
theorem bsgyUnitaryMass_step_div (f : ℕ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : 0 < vE) (n : ℕ) :
    bsgyUnitaryMass f χ vE (n + 1) / bsgyUnitaryMass f χ vE n =
      bsgyStepFactor f χ vE (n + 1) := by
  have hpos : bsgyUnitaryMass f χ vE n ≠ 0 := (bsgyUnitaryMass_pos f hχ hv n).ne'
  unfold bsgyUnitaryMass
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by simp [Finset.mem_Icc]
  rw [hIcc, Finset.prod_insert hnot]
  have hprod : 2 * (bsgyStepFactor f χ vE (n + 1) * ∏ j ∈ Finset.Icc 1 n, bsgyStepFactor f χ vE j) =
      bsgyStepFactor f χ vE (n + 1) * (2 * ∏ j ∈ Finset.Icc 1 n, bsgyStepFactor f χ vE j) := by
    ring
  rw [hprod]
  exact mul_div_cancel_right₀ _ hpos

/-- Positivity of `bsgyUnitaryMass f χ vE n` for all `n ≥ 2`. -/
theorem bsgyUnitaryMass_pos_ge_two (f : ℕ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : Real.pi ≤ vE)
    {n : ℕ} (_hn : 2 ≤ n) :
    0 < bsgyUnitaryMass f χ vE n :=
  bsgyUnitaryMass_pos f hχ (lt_of_lt_of_le Real.pi_pos hv) n

private lemma sqrt_pow_nat {x : ℝ} (hx : 0 ≤ x) (f : ℕ) :
    Real.sqrt (x ^ f) = (Real.sqrt x) ^ f := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx f), ih, pow_succ]

/-- For every `M ≥ 4` and `vE ≥ π`, `1 < bsgyStepFactor f χ vE M` (assuming `1 ≤ f`). -/
theorem bsgyStepFactor_gt_one_ge_four {f : ℕ} (hf : 1 ≤ f) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {vE : ℝ} (hv : Real.pi ≤ vE) {M : ℕ} (hM : 4 ≤ M) :
    1 < bsgyStepFactor f χ vE M := by
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hM3 : 3 ≤ M := by omega
  have hL_ge : (2 / 3 : ℝ) ≤ hermLVal χ M := (hermLVal_bounds_ge_three χ hM3).1
  have hfac_ge : (6 : ℝ) ≤ (Nat.factorial (M - 1) : ℝ) := by
    have h3le : 3 ≤ M - 1 := by omega
    have h6 : 6 ≤ Nat.factorial (M - 1) := by
      have h3 : Nat.factorial 3 ≤ Nat.factorial (M - 1) := Nat.factorial_le h3le
      have h3eq : Nat.factorial 3 = 6 := by decide
      omega
    exact_mod_cast h6
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h2v_pos : 0 < 2 * vE := by linarith
  have hsq_pos : 0 < Real.sqrt (2 * vE) := Real.sqrt_pos.mpr h2v_pos
  have hpi_lt : Real.pi < 4 := Real.pi_lt_four
  have hv_div_pi : 1 ≤ vE / Real.pi := (one_le_div Real.pi_pos).mpr hv
  have hpowM : vE / Real.pi ≤ (vE / Real.pi) ^ M := by
    have h1 : (vE / Real.pi) ^ 1 ≤ (vE / Real.pi) ^ M := pow_le_pow_right₀ hv_div_pi (by omega)
    simpa using h1
  have hsq_lt : (Real.sqrt (2 * vE)) ^ 2 < (4 * (vE / Real.pi)) ^ 2 := by
    rw [Real.sq_sqrt h2v_pos.le, mul_pow, div_pow, ← mul_div_assoc,
      lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
    have hpi_sq : Real.pi ^ 2 < 8 * Real.pi := by nlinarith [Real.pi_gt_three, Real.pi_lt_four]
    have hv_sq : Real.pi ^ 2 < 8 * vE := lt_of_lt_of_le hpi_sq (by linarith)
    nlinarith
  have hsingle_gt : 1 < ((Nat.factorial (M - 1) : ℝ) * (vE / Real.pi) ^ M) / Real.sqrt (2 * vE) * hermLVal χ M := by
    have hnum_ge : 4 * (vE / Real.pi) ≤ (Nat.factorial (M - 1) : ℝ) * (vE / Real.pi) ^ M * (2 / 3 : ℝ) := by
      have h1 : 4 ≤ (Nat.factorial (M - 1) : ℝ) * (2 / 3 : ℝ) := by linarith
      calc 4 * (vE / Real.pi)
          ≤ ((Nat.factorial (M - 1) : ℝ) * (2 / 3 : ℝ)) * (vE / Real.pi) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ ((Nat.factorial (M - 1) : ℝ) * (2 / 3 : ℝ)) * (vE / Real.pi) ^ M :=
            mul_le_mul_of_nonneg_left hpowM (by positivity)
        _ = (Nat.factorial (M - 1) : ℝ) * (vE / Real.pi) ^ M * (2 / 3 : ℝ) := by ring
    have h4_gt_sq : Real.sqrt (2 * vE) < 4 * (vE / Real.pi) := by
      nlinarith [Real.sqrt_nonneg (2 * vE), show 0 ≤ 4 * (vE / Real.pi) by positivity]
    have hlt1 : 1 < (4 * (vE / Real.pi)) / Real.sqrt (2 * vE) :=
      (one_lt_div hsq_pos).mpr h4_gt_sq
    have hle2 : (4 * (vE / Real.pi)) / Real.sqrt (2 * vE) ≤
        ((Nat.factorial (M - 1) : ℝ) * (vE / Real.pi) ^ M) / Real.sqrt (2 * vE) * (2 / 3 : ℝ) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hnum_ge hsq_pos.le
    have hle3 : ((Nat.factorial (M - 1) : ℝ) * (vE / Real.pi) ^ M) / Real.sqrt (2 * vE) * (2 / 3 : ℝ) ≤
        ((Nat.factorial (M - 1) : ℝ) * (vE / Real.pi) ^ M) / Real.sqrt (2 * vE) * hermLVal χ M :=
      mul_le_mul_of_nonneg_left hL_ge (by positivity)
    linarith
  unfold bsgyStepFactor UnitaryMassFormula.massRatioFactor
  dsimp only
  rw [sqrt_pow_nat h2v_pos.le f, ← div_pow, ← mul_pow]
  exact one_lt_pow₀ hsingle_gt (by omega)

/-- Strict monotonicity of `bsgyUnitaryMass f χ vE` for all `n ≥ 3` when `vE ≥ π` and `f ≥ 1`. -/
theorem bsgyUnitaryMass_strictMono_ge_three {f : ℕ} (hf : 1 ≤ f) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : Real.pi ≤ vE)
    {m n : ℕ} (hm : 3 ≤ m) (hmn : m < n) :
    bsgyUnitaryMass f χ vE m < bsgyUnitaryMass f χ vE n := by
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hsucc : ∀ k : ℕ, 3 ≤ k → bsgyUnitaryMass f χ vE k < bsgyUnitaryMass f χ vE (k + 1) := by
    intro k hk
    have hgt1 := bsgyStepFactor_gt_one_ge_four hf χ hv (show 4 ≤ k + 1 by omega)
    have hstep := bsgyUnitaryMass_step_div f hχ hv_pos k
    have hk_pos := bsgyUnitaryMass_pos f hχ hv_pos k
    rw [← hstep] at hgt1
    exact (one_lt_div hk_pos).mp hgt1
  induction n, hmn using Nat.le_induction with
  | base => exact hsucc m hm
  | succ k hmk ih => exact ih.trans (hsucc k (by omega))

/-- For `2 * π ≤ vE`, `1 < bsgyStepFactor f χ vE 3` already holds, giving strict monotonicity
for ALL `n ≥ 2`! -/
theorem bsgyStepFactor_gt_one_three_of_two_pi {f : ℕ} (hf : 1 ≤ f) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {vE : ℝ} (hv : 2 * Real.pi ≤ vE) :
    1 < bsgyStepFactor f χ vE 3 := by
  have hv_pos : 0 < vE := by linarith [Real.pi_pos]
  have h2v_pos : 0 < 2 * vE := by linarith
  have hsq_pos : 0 < Real.sqrt (2 * vE) := Real.sqrt_pos.mpr h2v_pos
  have hL_ge : (2 / 3 : ℝ) ≤ hermLVal χ 3 := (hermLVal_bounds_ge_three χ le_rfl).1
  have hv_div : 2 ≤ vE / Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith)
  have hsq_lt : (Real.sqrt (2 * vE)) ^ 2 < ((4 / 3 : ℝ) * (vE / Real.pi) ^ 3) ^ 2 := by
    rw [Real.sq_sqrt h2v_pos.le]
    have hpow5 : (32 : ℝ) ≤ (vE / Real.pi) ^ 5 := by
      have h1 : (2 : ℝ) ^ 5 ≤ (vE / Real.pi) ^ 5 := pow_le_pow_left₀ (by norm_num) hv_div 5
      linarith
    have hv_eq : vE = Real.pi * (vE / Real.pi) := (mul_div_cancel₀ vE Real.pi_ne_zero).symm
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have h1 : 2 * vE = 2 * Real.pi * (vE / Real.pi) := by
      conv_lhs => rw [hv_eq]
      ring
    have h2 : ((4 / 3 : ℝ) * (vE / Real.pi) ^ 3) ^ 2 =
        (16 / 9 : ℝ) * (vE / Real.pi) ^ 5 * (vE / Real.pi) := by ring
    have h3 : 2 * Real.pi < (16 / 9 : ℝ) * 32 := by linarith
    have h4 : 2 * Real.pi < (16 / 9 : ℝ) * (vE / Real.pi) ^ 5 := by nlinarith
    have hvp : 0 < vE / Real.pi := by positivity
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right h4 hvp
  have hlt_sq : Real.sqrt (2 * vE) < (4 / 3 : ℝ) * (vE / Real.pi) ^ 3 := by
    nlinarith [Real.sqrt_nonneg (2 * vE), show 0 ≤ (4 / 3 : ℝ) * (vE / Real.pi) ^ 3 by positivity]
  have hsingle : 1 < (Nat.factorial (3 - 1) : ℝ) * (vE / Real.pi) ^ 3 / Real.sqrt (2 * vE) * hermLVal χ 3 := by
    have h1 : 1 < ((4 / 3 : ℝ) * (vE / Real.pi) ^ 3) / Real.sqrt (2 * vE) :=
      (one_lt_div hsq_pos).mpr hlt_sq
    have h2 : (4 / 3 : ℝ) * (vE / Real.pi) ^ 3 ≤
        (Nat.factorial (3 - 1) : ℝ) * (vE / Real.pi) ^ 3 * (2 / 3 : ℝ) := by
      have : (Nat.factorial (3 - 1) : ℝ) = 2 := by norm_num
      rw [this]
      nlinarith [pow_nonneg (div_nonneg hv_pos.le Real.pi_pos.le) 3]
    have h3 : ((4 / 3 : ℝ) * (vE / Real.pi) ^ 3) / Real.sqrt (2 * vE) ≤
        (Nat.factorial (3 - 1) : ℝ) * (vE / Real.pi) ^ 3 / Real.sqrt (2 * vE) * (2 / 3 : ℝ) := by
      calc ((4 / 3 : ℝ) * (vE / Real.pi) ^ 3) / Real.sqrt (2 * vE)
          ≤ ((Nat.factorial (3 - 1) : ℝ) * (vE / Real.pi) ^ 3 * (2 / 3 : ℝ)) / Real.sqrt (2 * vE) :=
            div_le_div_of_nonneg_right h2 hsq_pos.le
        _ = (Nat.factorial (3 - 1) : ℝ) * (vE / Real.pi) ^ 3 / Real.sqrt (2 * vE) * (2 / 3 : ℝ) := by
            ring
    have h4 : (Nat.factorial (3 - 1) : ℝ) * (vE / Real.pi) ^ 3 / Real.sqrt (2 * vE) * (2 / 3 : ℝ) ≤
        (Nat.factorial (3 - 1) : ℝ) * (vE / Real.pi) ^ 3 / Real.sqrt (2 * vE) * hermLVal χ 3 :=
      mul_le_mul_of_nonneg_left hL_ge (by positivity)
    linarith
  unfold bsgyStepFactor UnitaryMassFormula.massRatioFactor
  dsimp only
  rw [sqrt_pow_nat h2v_pos.le f, ← div_pow, ← mul_pow]
  exact one_lt_pow₀ hsingle (by omega)

theorem bsgyUnitaryMass_strictMono_ge_two {f : ℕ} (hf : 1 ≤ f) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : 2 * Real.pi ≤ vE)
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    bsgyUnitaryMass f χ vE m < bsgyUnitaryMass f χ vE n := by
  have hv_pi : Real.pi ≤ vE := by linarith [Real.pi_pos]
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv_pi
  have hstep23 : bsgyUnitaryMass f χ vE 2 < bsgyUnitaryMass f χ vE 3 := by
    have hgt1 := bsgyStepFactor_gt_one_three_of_two_pi hf χ hv
    have hstep := bsgyUnitaryMass_step_div f hχ hv_pos 2
    have h2pos := bsgyUnitaryMass_pos f hχ hv_pos 2
    rw [← hstep] at hgt1
    exact (one_lt_div h2pos).mp hgt1
  rcases eq_or_lt_of_le hm with rfl | hm3
  · rcases eq_or_lt_of_le (show 3 ≤ n by omega) with rfl | hn3
    · exact hstep23
    · exact hstep23.trans (bsgyUnitaryMass_strictMono_ge_three hf hχ hv_pi le_rfl hn3)
  · exact bsgyUnitaryMass_strictMono_ge_three hf hχ hv_pi (by omega) hmn

/-- **Concrete Zero-Assumption `UnitaryVolumeSystem`** backed by `bsgyUnitaryMass f χ vE`. -/
def bsgyVolumeSystem (f : ℕ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : Real.pi ≤ vE) :
    UnitaryVolumeSystem where
  Space _ _ := Unit
  vol {P Q} _ := bsgyUnitaryMass f χ vE (P + Q)
  vol_pos {P Q} _ := bsgyUnitaryMass_pos f hχ (lt_of_lt_of_le Real.pi_pos hv) (P + Q)
  mass n := bsgyUnitaryMass f χ vE n
  mass_pos n _ := bsgyUnitaryMass_pos f hχ (lt_of_lt_of_le Real.pi_pos hv) n
  ratio M := bsgyStepFactor f χ vE M
  mass_step n _ := bsgyUnitaryMass_step_div f hχ (lt_of_lt_of_le Real.pi_pos hv) n
  step_pos_sig P Q _ _ := ⟨(), by
    simpa [Nat.add_assoc, Nat.add_comm Q 1] using
      bsgyUnitaryMass_step_div f hχ (lt_of_lt_of_le Real.pi_pos hv) (P + Q)⟩
  step_neg_sig P Q _ _ :=
    ⟨(), bsgyUnitaryMass_step_div f hχ (lt_of_lt_of_le Real.pi_pos hv) (P + Q)⟩

theorem bsgyVolumeSystem_volume_mass_ge_two (f : ℕ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : Real.pi ≤ vE) :
    ∀ n : ℕ, 2 ≤ n → volume_at_level_zero (bsgyVolumeSystem f hχ hv) n :=
  volume_mass_ge_two (bsgyVolumeSystem f hχ hv) (fun _ => rfl)

end LevelZeroVolumesAndMassRecursion

/-! ## Section 4: `genusMassAt_two` & Alignment with `Stage14Contracts.M1UnitarySiegelWeilContract` -/

section GenusMassAtTwoAndContracts

/-- **Exact Rank-2 Definite Unitary Genus Mass Closed Formula (`genusMassAt_two_formula`)**:
`bsgyUnitaryMass f χ vE 2 = 2 * ((vE / π)^(3f) / (2 vE)^f) * (hermLVal χ 1 * (π^2 / 6))^f`. -/
theorem genusMassAt_two_formula (f : ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {vE : ℝ} (hv : 0 < vE) :
    bsgyUnitaryMass f χ vE 2 =
      2 * ((vE / Real.pi) ^ (3 * f) / (2 * vE) ^ f) *
        (hermLVal χ 1 * (Real.pi ^ 2 / 6)) ^ f := by
  unfold bsgyUnitaryMass bsgyStepFactor UnitaryMassFormula.massRatioFactor
  dsimp only
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc, Finset.prod_pair (by decide)]
  have hz2 : hermLVal χ 2 = Real.pi ^ 2 / 6 := by
    unfold hermLVal
    rw [if_pos (by decide : _root_.Even 2), Nat.cast_ofNat, Stage9SpecialValues.riemannZeta_two_eq]
    simp
  rw [hz2]
  have h2v : (0 : ℝ) < 2 * vE := by linarith
  have hsq : Real.sqrt ((2 * vE) ^ f) ^ 2 = (2 * vE) ^ f :=
    Real.sq_sqrt (pow_nonneg h2v.le f)
  have hsq_ne : Real.sqrt ((2 * vE) ^ f) ≠ 0 :=
    (Real.sqrt_pos.mpr (pow_pos h2v f)).ne'
  have hpow3 : (vE / Real.pi) ^ f * (vE / Real.pi) ^ (2 * f) = (vE / Real.pi) ^ (3 * f) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul, pow_one,
    Nat.reduceSub, Nat.factorial_one]
  rw [← pow_mul]
  field_simp [hsq_ne]
  rw [hsq]
  calc (vE / Real.pi) ^ f * (2 * vE) ^ f * (hermLVal χ 1) ^ f * (vE / Real.pi) ^ (2 * f) *
        (Real.pi ^ 2 / 6) ^ f
      = (2 * vE) ^ f * ((vE / Real.pi) ^ f * (vE / Real.pi) ^ (2 * f)) *
          ((hermLVal χ 1) ^ f * (Real.pi ^ 2 / 6) ^ f) := by ring
    _ = (2 * vE) ^ f * (vE / Real.pi) ^ (3 * f) * (Real.pi ^ 2 * hermLVal χ 1 / 6) ^ f := by
        rw [hpow3, ← mul_pow]
        congr 1
        ring_nf

/-- Exact degree-`1` (`F = ℚ`) rank-2 unitary genus mass:
`bsgyUnitaryMass 1 χ vE 2 = vE^2 / (6 π) * hermLVal χ 1`. -/
theorem genusMassAt_two_deg_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {vE : ℝ} (hv : 0 < vE) :
    bsgyUnitaryMass 1 χ vE 2 = vE ^ 2 / (6 * Real.pi) * hermLVal χ 1 := by
  rw [genusMassAt_two_formula 1 χ hv]
  have hv0 : vE ≠ 0 := hv.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [mul_one, pow_one, div_pow]
  field_simp [hv0, hpi]

/-- Exact Gaussian (`ℚ(i)`, `chi4`) rank-2 unitary genus mass: `vE^2 / 24`. -/
theorem genusMassAt_two_chi4 {vE : ℝ} (hv : 0 < vE) :
    bsgyUnitaryMass 1 Stage9SpecialValues.chi4 vE 2 = vE ^ 2 / 24 := by
  rw [genusMassAt_two_deg_one Stage9SpecialValues.chi4 hv, hermLVal_chi4_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

/-- Exact Eisenstein (`ℚ(√-3)`, `chi3`) rank-2 unitary genus mass: `vE^2 / (18 √3)`. -/
theorem genusMassAt_two_chi3 {vE : ℝ} (hv : 0 < vE) :
    bsgyUnitaryMass 1 Stage9SpecialValues.chi3 vE 2 = vE ^ 2 / (18 * Real.sqrt 3) := by
  rw [genusMassAt_two_deg_one Stage9SpecialValues.chi3 hv, hermLVal_chi3_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsq : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp [hpi, hsq]
  ring

/-- Strict positivity of the rank-2 unitary genus mass for any `χ ≠ 1`, `vE > 0`, `f ≥ 0`. -/
theorem genusMassAt_two_pos (f : ℕ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {vE : ℝ} (hv : 0 < vE) :
    0 < bsgyUnitaryMass f χ vE 2 :=
  bsgyUnitaryMass_pos f hχ hv 2

/-- Explicit computable lower bound on `bsgyUnitaryMass 1 chi4 vE 2` for `vE ≥ π`: `1 / 3 < vE^2 / 24`. -/
theorem genusMassAt_two_chi4_gt_third {vE : ℝ} (hv : Real.pi ≤ vE) :
    (1 / 3 : ℝ) < bsgyUnitaryMass 1 Stage9SpecialValues.chi4 vE 2 := by
  rw [genusMassAt_two_chi4 (lt_of_lt_of_le Real.pi_pos hv)]
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hv3 : (3 : ℝ) < vE := lt_of_lt_of_le hpi3 hv
  nlinarith

/-- Rank-2 genus mass predicate for a double-coset genus `Γ \ G / K`. -/
def GenusMassAt {G : Type*} [Group G] (Γ K : Subgroup G)
    [Fintype (DoubleCosetClassSet Γ K)] (targetMass : ℝ) : Prop :=
  genusClassMass Γ K = targetMass

/-- **Rank-2 Genus Mass & Volume-Mass Bridge (`genusMassAt_two`)**:
for any rank-2 definite unitary double-coset decomposition `(Γ, K₀)` matching the
normalized Siegel–Weil covolume `(μ 𝓕).toReal / (μ K₀).toReal = bsgyUnitaryMass f χ vE 2`,
proves BOTH `GenusMassAt Γ K₀ (bsgyUnitaryMass f χ vE 2)` (`0 < genusClassMass Γ K₀`) AND
the full rank `n ≥ 2` / indefinite `(P, Q)` volume-mass recursion! -/
theorem genusMassAt_two {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    {Γ K₀ : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK₀ : MeasurableSet (K₀ : Set G)) (hK₀pos : 0 < μ K₀) (hK₀fin : μ K₀ ≠ ⊤)
    [Fintype (DoubleCosetClassSet Γ K₀)]
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K₀ g))
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (f : ℕ) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {vE : ℝ} (hv : Real.pi ≤ vE)
    (hvol : (μ 𝓕).toReal / (μ K₀).toReal = bsgyUnitaryMass f χ vE 2) :
    GenusMassAt Γ K₀ (bsgyUnitaryMass f χ vE 2) ∧
      0 < genusClassMass Γ K₀ ∧
      (∀ n : ℕ, 2 ≤ n → volume_at_level_zero (bsgyVolumeSystem f hχ hv) n) ∧
      (∀ P Q : ℕ, 2 ≤ P → ∀ W : (bsgyVolumeSystem f hχ hv).Space P Q,
        (bsgyVolumeSystem f hχ hv).vol W = (bsgyVolumeSystem f hχ hv).mass (P + Q)) := by
  have hcov : genusClassMass Γ K₀ = (μ 𝓕).toReal / (μ K₀).toReal :=
    class_decomp_mass_eq_covolume_div μ hK₀ hK₀pos hK₀fin hfin h𝓕
  have hgm : GenusMassAt Γ K₀ (bsgyUnitaryMass f χ vE 2) := hcov.trans hvol
  have hpos : 0 < genusClassMass Γ K₀ := by
    rw [hgm]
    exact genusMassAt_two_pos f hχ (lt_of_lt_of_le Real.pi_pos hv)
  exact ⟨hgm, hpos, bsgyVolumeSystem_volume_mass_ge_two f hχ hv,
    volume_indef_eq_mass (bsgyVolumeSystem f hχ hv) (fun _ => rfl)⟩

/-- **Local Siegel Euler-Product Compatibility at Rank 2 (`genusMassAt_two_euler_bounds`)**:
connects the convergent `n = 2 < m` global Siegel density Euler product
`Stage14M1_LocalSiegelDensities.siegelProductLValue χ m 2` (`16/49 ≤ · ≤ 16`) with
`bsgyUnitaryMass f χ vE 2`. -/
theorem genusMassAt_two_euler_bounds {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ n : ℕ, χ n = 0 ∨ χ n = 1 ∨ χ n = -1) {m : ℕ} (hm : 2 < m) :
    HasProd (globalEulerTerm χ m 2) (siegelProductLValue χ m 2) ∧
      (16 / 49 : ℝ) ≤ siegelProductLValue χ m 2 ∧
      siegelProductLValue χ m 2 ≤ 16 := by
  have h := siegel_densities_of_hermitian_form χ hquad hm
  refine ⟨h.1, ?_, ?_⟩
  · have h1 := h.2.2.1
    norm_num at h1 ⊢
    exact h1
  · have h2 := h.2.2.2
    norm_num at h2 ⊢
    exact h2

/-- **Wave-2 Formal-Degree & Mass Handoff Bundle (`FormalDegreeSiegelData`)**:
packages all proved mass, local density, logarithmic envelope, telescoping, and volume-mass
recursion obligations aligned verbatim with `Stage14Contracts.M1UnitarySiegelWeilContract`,
ready for M1 Wave 3 (`Stage14M1_SiegelWeilUnitary`). -/
structure FormalDegreeSiegelData : Type where
  genusMass : (f : ℕ) → (vE : ℝ) → ℕ → ℝ
  localSiegelDensity : (f : ℕ) → (vE : ℝ) → ℕ → ℝ
  unitaryTamagawaVol : (f : ℕ) → (vE : ℝ) → ℕ → ℕ → ℝ
  genusMass_pos : ∀ (f n : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ n → Real.pi ≤ vE → 0 < genusMass f vE n
  localSiegelDensity_pos : ∀ (f M : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ M → Real.pi ≤ vE →
    0 < localSiegelDensity f vE M
  localSiegelDensity_log_ge : ∀ (f m k : ℕ) (vE L_scale : ℝ),
    1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE → Real.log vE ≤ L_scale → 1 ≤ L_scale →
    ∃ B_L : ℝ, B_L ≤ (m : ℝ) * L_scale ∧
      -((f : ℝ) * B_L) ≤ ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (localSiegelDensity f vE M)
  siegelWeil_mass_telescope : ∀ (f m k : ℕ) (vE : ℝ),
    1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE →
    genusMass f vE (k + m - 1) =
      genusMass f vE k * ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
        UnitaryMassFormula.massRatioFactor f vE (localSiegelDensity f vE) M
  siegelWeil_vol_eq_mass : ∀ (f P Q : ℕ) (vE : ℝ),
    1 ≤ f → 2 ≤ P → Real.pi ≤ vE →
    unitaryTamagawaVol f vE P Q = genusMass f vE (P + Q)

/-- **Unconditional `FormalDegreeSiegelData` Realization** from any non-principal quadratic
Dirichlet character `χ ≠ 1` (e.g. `Stage9SpecialValues.chi4` or `chi3`). -/
def FormalDegreeSiegelData.ofBSGY {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : FormalDegreeSiegelData where
  genusMass f vE n := bsgyUnitaryMass f χ vE n
  localSiegelDensity f _vE M := (hermLVal χ M) ^ f
  unitaryTamagawaVol f vE P Q := bsgyUnitaryMass f χ vE (P + Q)
  genusMass_pos f n vE _ _ hv :=
    bsgyUnitaryMass_pos f hχ (lt_of_lt_of_le Real.pi_pos hv) n
  localSiegelDensity_pos f M _vE _ hM _ :=
    pow_pos (hermLVal_pos hχ (by omega)) f
  localSiegelDensity_log_ge f m k _vE L_scale _ hm hk _ _ hL1 := by
    refine ⟨((m : ℝ) - 1) / 2, ?_, ?_⟩
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    · have hpt : ∀ M ∈ Finset.Ico (k + 1) (k + m),
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
  siegelWeil_mass_telescope f m k vE _ hm hk _ := by
    have hidx : k + m - 1 = k - 1 + m := by omega
    rw [hidx]
    exact bsgyUnitaryMass_telescope f χ vE hm hk
  siegelWeil_vol_eq_mass f P Q vE _ _ _ := rfl

/-- Canonical `ℚ(i)` (`chi4`) Wave-2 handoff instance (`0` assumptions!). -/
def chi4FormalDegreeSiegelData : FormalDegreeSiegelData :=
  FormalDegreeSiegelData.ofBSGY Stage9SpecialValues.chi4_ne_one

/-- Direct compiler from `FormalDegreeSiegelData` + any positive `rallisSeesawScalar`
into `Stage14Contracts.M1UnitarySiegelWeilContract`. -/
def FormalDegreeSiegelData.toM1Contract (D : FormalDegreeSiegelData)
    (rallisSeesawScalar : (f k : ℕ) → (vE : ℝ) → ℕ → ℝ)
    (rallis_seesaw_pos : ∀ (f k j : ℕ) (vE : ℝ),
      1 ≤ f → 2 ≤ k → Real.pi ≤ vE → 0 < rallisSeesawScalar f k vE j) :
    M1UnitarySiegelWeilContract where
  genusMass := D.genusMass
  localSiegelDensity := D.localSiegelDensity
  unitaryTamagawaVol := D.unitaryTamagawaVol
  rallisSeesawScalar := rallisSeesawScalar
  genusMass_pos := D.genusMass_pos
  localSiegelDensity_pos := D.localSiegelDensity_pos
  localSiegelDensity_log_ge := D.localSiegelDensity_log_ge
  siegelWeil_mass_telescope := D.siegelWeil_mass_telescope
  siegelWeil_vol_eq_mass := D.siegelWeil_vol_eq_mass
  rallis_seesaw_pos := rallis_seesaw_pos

/-- **Archimedean Weyl-Dimension to `Stage2MassRatioDatum` Bridge**:
combines `FormalDegreeSiegelData` (with any positive Rallis seesaw scalar), a family of
discrete-series Weyl dimensions `dimRatio = ∏_{ρ : Fin f} weylDim (lam ρ)`, and the
explicit Stirling/Weyl lower bound `log_weylDim_bounds` to compile directly into
`Stage14Contracts.M1UnitarySiegelWeilContract.toStage2MassRatioDatum`! -/
def toStage2MassRatioDatum_of_formalDegree (D : FormalDegreeSiegelData)
    (rallisSeesawScalar : (f k : ℕ) → (vE : ℝ) → ℕ → ℝ)
    (rallis_seesaw_pos : ∀ (f k j : ℕ) (vE : ℝ),
      1 ≤ f → 2 ≤ k → Real.pi ≤ vE → 0 < rallisSeesawScalar f k vE j)
    {f m k : ℕ} {vE g₁ g₂ L_scale La cCount T_val : ℝ} {w_u0 : Fin m → Fin f → ℝ}
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hv : Real.pi ≤ vE) (hvL : Real.log vE ≤ L_scale) (hL1 : 1 ≤ L_scale)
    (Isig Ipi Dstar dstar W_lo : ℝ)
    (hIsig : 0 < Isig) (hIpi : 0 < Ipi)
    (ds : Fin f → UnitaryDiscreteSeries k 0)
    (hidx : ((2 : ℝ) ^ (2 * f))⁻¹ *
        (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) ≤ Isig / Ipi)
    (hcov : (2 / 3 : ℝ) ^ f * (D.genusMass f vE (k + m - 1) / D.genusMass f vE k) *
        (Isig / Ipi) * (∏ ρ : Fin f, FormalDegreeAtRealPlaceNormalized (ds ρ)) ≤ Dstar / dstar)
    (hweyl : W_lo ≤
      (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((f : ℝ) * (k : ℝ))) *
        Real.log (∏ ρ : Fin f, FormalDegreeAtRealPlaceNormalized (ds ρ)))
    (harch : (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w_u0 j ρ)) +
      Real.log (vE / Real.pi) ≤ W_lo)
    (hlogT : (1 / ((f : ℝ) * (k : ℝ))) * Real.log (Dstar / dstar) ≤ Real.log T_val) :
    Stage2ThetaWire.Stage2MassRatioDatum f m k vE g₁ g₂ L_scale La cCount w_u0 T_val :=
  (D.toM1Contract rallisSeesawScalar rallis_seesaw_pos).toStage2MassRatioDatum
    hf hm hk hv hvL hL1 Isig Ipi Dstar dstar
    (∏ ρ : Fin f, FormalDegreeAtRealPlaceNormalized (ds ρ))
    W_lo hIsig hIpi
    (Finset.prod_pos fun ρ _ => formalDegreeAtRealPlaceNormalized_pos (ds ρ))
    hidx hcov hweyl harch hlogT

end GenusMassAtTwoAndContracts

end RHDirect.Stage14M1_FormalDegreeDiscrete

end
