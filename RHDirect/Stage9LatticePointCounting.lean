import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# RHDirect.Stage9LatticePointCounting

Unconditional formalization of the **Gauss Circle Problem** (both the classical elementary `O(R)`
bound and the sub-linear **Sierpiński (1906) / Voronoï–Landau `O(R^{2/3})` Poisson-summation
breakthrough** with explicit constants and zero logarithmic loss), **`d`-dimensional Euclidean
sphere lattice-point counting** for all `d ≥ 1`, and **asymptotic averages of `r₂(n)`** in pure
Mathlib `v4.33.1` (0 `sorry`, 0 custom `axiom`s).

## Contents

1. **Concrete `d`-Dimensional Lattice Point Counting & `r₂(n)`**:
   - `latticeVec d v`, `latticeBallSet d R`, `latticeBallCount d R := (latticeBallSet d R).card`,
     `gaussCircleCount R := latticeBallCount 2 R`, `repTwoSquares n`.
   - Exact identity `gaussCircleCount_eq_sum_repTwoSquares`:
     `gaussCircleCount R = ∑ n ∈ Finset.Icc 0 ⌊R ^ 2⌋₊, repTwoSquares n`.
2. **Exact `d`-Dimensional Hypercube Tiling & Elementary Gauss Bounds (`d ≥ 1`)**:
   - Disjoint unit hypercubes `unitCube d v` of Lebesgue measure `1` satisfying
     `closedBall 0 (R - √d / 2) ⊆ ⋃_{v ∈ latticeBallSet d R} unitCube d v ⊆ closedBall 0 (R + √d / 2)`.
   - `latticeBallCount_volume_bounds`: for all `d ≥ 1` and `R ≥ √d / 2`,
     `ω_d * (R - √d / 2)^d ≤ latticeBallCount d R ≤ ω_d * (R + √d / 2)^d`.
   - Specializations `gauss_circle_classical_bound` (`d = 2`), `gauss_sphere_classical_bound`
     (`d = 3`), and universal asymptotic `latticeBallCount_asymptotic`:
     `latticeBallCount d R / R^d → ω_d` as `R → ∞`.
3. **Oscillatory-Integral Decay of the 2D Disk Fourier Transform**:
   - Elementary 2-IBP / endpoint-cap bound `|∫_0^1 √(1 - t²) cos(λ t) dt| ≤ 5 / λ^{3/2}` for all `λ > 0`.
   - Exact rotation reduction of `diskFourier R ξ₁ ξ₂` and unconditional decay
     `‖diskFourier R ξ₁ ξ₂‖ ≤ 2 * √R / (ξ₁² + ξ₂²)^{3/4}`.
4. **Compactly Supported 2D Tent Mollifier & Exact 2D Poisson Summation**:
   - `tent a`, `tentHat a` (`|tentHat a ξ| ≤ min 1 (1 / (2 π a ξ)²)`), `smoothedDisk R a`.
   - Exact pointwise sandwich `1_{B(0, R - 2√2 a)} * Φ_a ≤ 1_{B(0, R)} ≤ 1_{B(0, R + 2√2 a)} * Φ_a`.
   - Unconditional 2D Poisson summation via iterated 1D `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`.
5. **Dual Lattice Shell Bound & Unconditional Sierpiński `O(R^{2/3})` Breakthrough**:
   - Elementary `L^∞`-shell telescoping bound `dualSum a ≤ 37 / √a` for `0 < a ≤ 1`.
   - `gauss_circle_sierpinski_bound`: `∀ R ≥ 1, |(gaussCircleCount R : ℝ) - π R²| ≤ 300 * R^{2/3}`.
   - `sum_repTwoSquares_asymp`: `∀ N ≥ 1, |∑_{n=0}^N r₂(n) - π N| ≤ 300 * N^{1/3}`.
-/

open scoped BigOperators Topology ENNReal
open Filter Finset MeasureTheory Real

namespace RHDirect.Stage9LatticePointCounting

noncomputable section

/-! ## Section 1: Concrete `d`-Dimensional Lattice Point Counting & `r₂(n)` -/

section LatticeCountingDefs

/-- Canonical embedding of an integer lattice vector `v : Fin d → ℤ` into `EuclideanSpace ℝ (Fin d)`. -/
def latticeVec (d : ℕ) (v : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

@[simp]
lemma latticeVec_apply (d : ℕ) (v : Fin d → ℤ) (i : Fin d) :
    latticeVec d v i = (v i : ℝ) := rfl

lemma norm_sq_latticeVec (d : ℕ) (v : Fin d → ℤ) :
    ‖latticeVec d v‖ ^ 2 = ∑ i : Fin d, (v i : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [latticeVec, Real.norm_eq_abs, sq_abs]

lemma norm_latticeVec_le_iff {d : ℕ} {v : Fin d → ℤ} {R : ℝ} (hR : 0 ≤ R) :
    ‖latticeVec d v‖ ≤ R ↔ ∑ i : Fin d, (v i : ℝ) ^ 2 ≤ R ^ 2 := by
  rw [← norm_sq_latticeVec]
  exact (sq_le_sq₀ (norm_nonneg _) hR).symm

/-- Finite set of all integer lattice points in the closed Euclidean ball of radius `R` in `ℝ^d`. -/
def latticeBallSet (d : ℕ) (R : ℝ) : Finset (Fin d → ℤ) :=
  if 0 ≤ R then
    (Fintype.piFinset fun _ : Fin d => Finset.Icc (-⌈R⌉) ⌈R⌉).filter
      (fun v => ∑ i : Fin d, (v i : ℝ) ^ 2 ≤ R ^ 2)
  else
    ∅

lemma mem_latticeBallSet {d : ℕ} {R : ℝ} {v : Fin d → ℤ} :
    v ∈ latticeBallSet d R ↔ ‖latticeVec d v‖ ≤ R := by
  unfold latticeBallSet
  split_ifs with hR
  · simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
    rw [norm_latticeVec_le_iff hR]
    constructor
    · exact fun h => h.2
    · intro hsum
      refine ⟨fun i => ?_, hsum⟩
      have hi_sq : (v i : ℝ) ^ 2 ≤ R ^ 2 :=
        (Finset.single_le_sum (f := fun j : Fin d => (v j : ℝ) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans hsum
      have hi_abs : |(v i : ℝ)| ≤ R := by
        have h1 : |(v i : ℝ)| ^ 2 ≤ R ^ 2 := by simpa [sq_abs] using hi_sq
        exact (sq_le_sq₀ (abs_nonneg _) hR).mp h1
      have hle : (v i : ℝ) ≤ R := (abs_le.mp hi_abs).2
      have hge : -R ≤ (v i : ℝ) := (abs_le.mp hi_abs).1
      have hceil : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil R
      constructor
      · exact_mod_cast (by linarith : (-(⌈R⌉ : ℤ) : ℝ) ≤ (v i : ℝ))
      · exact_mod_cast (hle.trans hceil)
  · constructor
    · intro h; simp at h
    · intro h; exact absurd ((norm_nonneg _).trans h) hR

lemma mem_latticeBallSet_iff_sum_sq {d : ℕ} {R : ℝ} (hR : 0 ≤ R) {v : Fin d → ℤ} :
    v ∈ latticeBallSet d R ↔ ∑ i : Fin d, (v i : ℝ) ^ 2 ≤ R ^ 2 := by
  rw [mem_latticeBallSet, norm_latticeVec_le_iff hR]

/-- Number of integer lattice points `v ∈ ℤ^d` with `‖v‖ ≤ R`. -/
def latticeBallCount (d : ℕ) (R : ℝ) : ℕ :=
  (latticeBallSet d R).card

/-- Classical Gauss circle counting function `N₂(R) = #{ (a, b) ∈ ℤ² | a² + b² ≤ R² }`. -/
def gaussCircleCount (R : ℝ) : ℕ :=
  latticeBallCount 2 R

lemma latticeBallCount_mono {d : ℕ} {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    latticeBallCount d R₁ ≤ latticeBallCount d R₂ := by
  unfold latticeBallCount
  refine Finset.card_le_card fun v hv => ?_
  rw [mem_latticeBallSet] at hv ⊢
  exact hv.trans h

/-- Finite set of all representations `(a, b) ∈ ℤ²` with `a² + b² = n`. -/
def repTwoSquaresSet (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)).filter
    (fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))

lemma mem_repTwoSquaresSet {n : ℕ} {p : ℤ × ℤ} :
    p ∈ repTwoSquaresSet n ↔ p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
  unfold repTwoSquaresSet
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro hp
    refine ⟨⟨?_, ?_⟩, hp⟩
    · have h1 : p.1 ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg p.2]
      have habs : |p.1| ≤ (n : ℤ) := by
        by_contra hlt
        push Not at hlt
        have h2 : ((n : ℤ) + 1) ≤ |p.1| := by omega
        have h3 : ((n : ℤ) + 1) ^ 2 ≤ |p.1| ^ 2 := by nlinarith
        rw [sq_abs] at h3
        nlinarith
      exact abs_le.mp habs
    · have h1 : p.2 ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg p.1]
      have habs : |p.2| ≤ (n : ℤ) := by
        by_contra hlt
        push Not at hlt
        have h2 : ((n : ℤ) + 1) ≤ |p.2| := by omega
        have h3 : ((n : ℤ) + 1) ^ 2 ≤ |p.2| ^ 2 := by nlinarith
        rw [sq_abs] at h3
        nlinarith
      exact abs_le.mp habs

/-- Number of representations `r₂(n) = #{ (a, b) ∈ ℤ² | a² + b² = n }`. -/
def repTwoSquares (n : ℕ) : ℕ :=
  (repTwoSquaresSet n).card

lemma repTwoSquares_zero : repTwoSquares 0 = 1 := by
  unfold repTwoSquares
  have h : repTwoSquaresSet 0 = {(0, 0)} := by
    ext ⟨a, b⟩
    simp only [mem_repTwoSquaresSet, Finset.mem_singleton, Prod.mk.injEq, Nat.cast_zero]
    constructor
    · intro hab
      have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      exact ⟨sq_eq_zero_iff.mp ha, sq_eq_zero_iff.mp hb⟩
    · rintro ⟨rfl, rfl⟩; norm_num
  rw [h, Finset.card_singleton]

lemma repTwoSquares_one : repTwoSquares 1 = 4 := by
  unfold repTwoSquares
  have h : repTwoSquaresSet 1 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
    ext ⟨a, b⟩
    simp only [mem_repTwoSquaresSet, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
      Nat.cast_one]
    constructor
    · intro hab
      have ha_le : -1 ≤ a ∧ a ≤ 1 := by
        constructor <;> by_contra hc <;> push Not at hc <;> nlinarith [sq_nonneg b]
      have hb_le : -1 ≤ b ∧ b ≤ 1 := by
        constructor <;> by_contra hc <;> push Not at hc <;> nlinarith [sq_nonneg a]
      have ha' : a = -1 ∨ a = 0 ∨ a = 1 := by omega
      have hb' : b = -1 ∨ b = 0 ∨ b = 1 := by omega
      rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  rw [h]
  decide

/-- Exact bridge between the 2D Gauss circle count `N₂(R)` and the summatory function of `r₂(n)`:
`gaussCircleCount R = ∑ n ∈ Finset.Icc 0 ⌊R²⌋₊, repTwoSquares n`. -/
theorem gaussCircleCount_eq_sum_repTwoSquares {R : ℝ} (hR : 0 ≤ R) :
    gaussCircleCount R = ∑ n ∈ Finset.Icc 0 ⌊R ^ 2⌋₊, repTwoSquares n := by
  unfold gaussCircleCount latticeBallCount repTwoSquares
  let S : Finset (ℤ × ℤ) :=
    (Finset.Icc 0 ⌊R ^ 2⌋₊).biUnion repTwoSquaresSet
  have hdisj : Set.PairwiseDisjoint (Finset.Icc 0 ⌊R ^ 2⌋₊ : Set ℕ) repTwoSquaresSet := by
    intro m _ n _ hmn
    show Disjoint (repTwoSquaresSet m) (repTwoSquaresSet n)
    rw [Finset.disjoint_left]
    intro p hpm hpn
    rw [mem_repTwoSquaresSet] at hpm hpn
    exact hmn (by omega)
  have hcardS : S.card = ∑ n ∈ Finset.Icc 0 ⌊R ^ 2⌋₊, (repTwoSquaresSet n).card :=
    Finset.card_biUnion hdisj
  rw [← hcardS]
  refine Finset.card_bij (fun (v : Fin 2 → ℤ) _ => (v 0, v 1)) ?_ ?_ ?_
  · intro v hv
    rw [mem_latticeBallSet_iff_sum_sq hR] at hv
    have hsum2 : (v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 ≤ R ^ 2 := by
      simpa [Fin.sum_univ_two] using hv
    have hnn : (0 : ℤ) ≤ v 0 ^ 2 + v 1 ^ 2 := by positivity
    let n : ℕ := (v 0 ^ 2 + v 1 ^ 2).toNat
    have hn_cast : (n : ℤ) = v 0 ^ 2 + v 1 ^ 2 := Int.toNat_of_nonneg hnn
    have hn_le : n ≤ ⌊R ^ 2⌋₊ := by
      rw [Nat.le_floor_iff (sq_nonneg R)]
      have hreal : (n : ℝ) = (v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 := by exact_mod_cast hn_cast
      linarith
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hn_le⟩,
      mem_repTwoSquaresSet.mpr hn_cast.symm⟩
  · intro u _ v _ huv
    ext i
    fin_cases i
    · exact (Prod.mk.inj huv).1
    · exact (Prod.mk.inj huv).2
  · intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨n, hn, hpn⟩
    rw [Finset.mem_Icc] at hn
    rw [mem_repTwoSquaresSet] at hpn
    refine ⟨![p.1, p.2], ?_, by simp⟩
    rw [mem_latticeBallSet_iff_sum_sq hR, Fin.sum_univ_two]
    have h1 : (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 = (n : ℝ) := by exact_mod_cast hpn
    have h2 : (n : ℝ) ≤ R ^ 2 := (Nat.le_floor_iff (sq_nonneg R)).mp hn.2
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using h1.le.trans h2

/-- Specialization at `R = √N`: `gaussCircleCount (√N) = ∑ n ∈ Finset.Icc 0 N, r₂(n)`. -/
theorem gaussCircleCount_sqrt_nat (N : ℕ) :
    gaussCircleCount (Real.sqrt N) = ∑ n ∈ Finset.Icc 0 N, repTwoSquares n := by
  rw [gaussCircleCount_eq_sum_repTwoSquares (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg N), Nat.floor_natCast]

end LatticeCountingDefs

/-! ## Section 2: Exact `d`-Dimensional Hypercube Tiling & Elementary Gauss Bounds -/

section ElementaryGaussBounds

/-- Volume `ω_d = vol(B_d(0, 1))` of the unit Euclidean ball in `ℝ^d`. -/
def unitBallVolume (d : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

lemma unitBallVolume_eq_sqrt_pi_div_gamma {d : ℕ} (hd : 1 ≤ d) :
    unitBallVolume d = Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  unfold unitBallVolume
  rw [EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  refine ENNReal.toReal_ofReal ?_
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (Real.Gamma_pos_of_pos (by positivity)).le

lemma unitBallVolume_eq_rpow {d : ℕ} (hd : 1 ≤ d) :
    unitBallVolume d = Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) := by
  rw [unitBallVolume_eq_sqrt_pi_div_gamma hd]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  congr 1
  ring

lemma unitBallVolume_pos {d : ℕ} (hd : 1 ≤ d) : 0 < unitBallVolume d := by
  rw [unitBallVolume_eq_sqrt_pi_div_gamma hd]
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by positivity))

lemma volume_closedBall_eq_unitBallVolume {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) r)).toReal =
      unitBallVolume d * r ^ d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  have hω : (ENNReal.ofReal (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1))).toReal =
      unitBallVolume d := by
    rw [unitBallVolume_eq_sqrt_pi_div_gamma hd]
    exact ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (Real.Gamma_pos_of_pos (by positivity)).le)
  rw [hω, mul_comm]

lemma volume_closedBall_ne_top (d : ℕ) (r : ℝ) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) r) ≠ ⊤ :=
  measure_closedBall_lt_top.ne

lemma unitBallVolume_one : unitBallVolume 1 = 2 := by
  rw [unitBallVolume_eq_sqrt_pi_div_gamma (by norm_num)]
  have hG : Real.Gamma ((1 : ℝ) / 2 + 1) = (1 / 2) * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  rw [pow_one, Nat.cast_one, hG]
  have hne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp [hne]

lemma unitBallVolume_two : unitBallVolume 2 = Real.pi := by
  rw [unitBallVolume_eq_sqrt_pi_div_gamma (by norm_num)]
  have h2 : ((2 : ℕ) : ℝ) / 2 + 1 = (1 : ℕ) + 1 := by norm_num
  rw [h2, Real.Gamma_nat_eq_factorial, Nat.factorial_one, Nat.cast_one, div_one,
    Real.sq_sqrt Real.pi_pos.le]

lemma unitBallVolume_three : unitBallVolume 3 = (4 / 3) * Real.pi := by
  rw [unitBallVolume_eq_sqrt_pi_div_gamma (by norm_num)]
  have h3 : ((3 : ℕ) : ℝ) / 2 + 1 = (3 / 2 : ℝ) + 1 := by norm_num
  have hG1 : Real.Gamma ((3 / 2 : ℝ) + 1) = (3 / 2 : ℝ) * Real.Gamma (3 / 2) :=
    Real.Gamma_add_one (by norm_num)
  have hG2 : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    have : (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 := by norm_num
    rw [this, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  rw [h3, hG1, hG2]
  have hsq : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    rw [pow_succ, Real.sq_sqrt Real.pi_pos.le]
  rw [hsq]
  have hne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp [hne]
  ring

/-- Half-open unit hypercube centered at the integer lattice point `v ∈ ℤ^d`:
`Q_v = ∏ᵢ [vᵢ - 1/2, vᵢ + 1/2)` in `EuclideanSpace ℝ (Fin d)`. -/
def unitCube (d : ℕ) (v : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun i => Set.Ico ((v i : ℝ) - 1 / 2) ((v i : ℝ) + 1 / 2))

lemma mem_unitCube_iff {d : ℕ} {v : Fin d → ℤ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ unitCube d v ↔ ∀ i : Fin d, (v i : ℝ) - 1 / 2 ≤ x i ∧ x i < (v i : ℝ) + 1 / 2 := by
  simp [unitCube, Set.mem_pi, Set.mem_Ico]

lemma unitCube_measurableSet (d : ℕ) (v : Fin d → ℤ) :
    MeasurableSet (unitCube d v) := by
  unfold unitCube
  refine MeasurableSet.preimage ?_ (PiLp.volume_preserving_ofLp (Fin d)).measurable
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma volume_unitCube (d : ℕ) (v : Fin d → ℤ) :
    volume (unitCube d v) = 1 := by
  unfold unitCube
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet]
  rw [MeasureTheory.volume_pi_pi]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Real.volume_Ico]
  have hsub : ((v i : ℝ) + 1 / 2) - ((v i : ℝ) - 1 / 2) = 1 := by ring
  rw [hsub, ENNReal.ofReal_one]

lemma unitCube_pairwiseDisjoint (d : ℕ) :
    Pairwise fun u v : Fin d → ℤ => Disjoint (unitCube d u) (unitCube d v) := by
  intro u v huv
  rw [Set.disjoint_left]
  intro x hxu hxv
  rw [mem_unitCube_iff] at hxu hxv
  have hne : ∃ i : Fin d, u i ≠ v i := by
    by_contra hall
    push Not at hall
    exact huv (funext hall)
  rcases hne with ⟨i, hi⟩
  have hu := hxu i
  have hv := hxv i
  have hlt1 : (u i : ℝ) < (v i : ℝ) + 1 := by linarith
  have hlt2 : (v i : ℝ) < (u i : ℝ) + 1 := by linarith
  have hint1 : u i < v i + 1 := by exact_mod_cast hlt1
  have hint2 : v i < u i + 1 := by exact_mod_cast hlt2
  exact hi (by omega)

lemma unitCube_norm_sub_le {d : ℕ} {v : Fin d → ℤ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ unitCube d v) :
    ‖x - latticeVec d v‖ ≤ Real.sqrt d / 2 := by
  rw [mem_unitCube_iff] at hx
  have hsq : ‖x - latticeVec d v‖ ^ 2 ≤ (Real.sqrt d / 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ i : Fin d, ‖(x - latticeVec d v) i‖ ^ 2
          ≤ ∑ _i : Fin d, ((1 : ℝ) / 2) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hxi := hx i
            have habs : |x i - (v i : ℝ)| ≤ 1 / 2 := by
              rw [abs_le]; constructor <;> linarith
            have hnorm : ‖(x - latticeVec d v) i‖ = |x i - (v i : ℝ)| := by
              simp [Real.norm_eq_abs, latticeVec]
            rw [hnorm]
            exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr habs
      _ = (d : ℝ) * ((1 : ℝ) / 2) ^ 2 := by simp
      _ = (Real.sqrt d / 2) ^ 2 := by
            rw [show (Real.sqrt d / 2) ^ 2 = Real.sqrt d ^ 2 / 4 by ring,
              Real.sq_sqrt (Nat.cast_nonneg d)]
            ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

lemma exists_mem_unitCube (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ v : Fin d → ℤ, x ∈ unitCube d v := by
  refine ⟨fun i => ⌊x i + 1 / 2⌋, ?_⟩
  rw [mem_unitCube_iff]
  intro i
  have h1 : (⌊x i + 1 / 2⌋ : ℝ) ≤ x i + 1 / 2 := Int.floor_le _
  have h2 : x i + 1 / 2 < (⌊x i + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  constructor <;> linarith

lemma biUnion_unitCube_subset_closedBall {d : ℕ} {R : ℝ} :
    (⋃ v ∈ latticeBallSet d R, unitCube d v) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + Real.sqrt d / 2) := by
  intro x hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨v, hv, hxv⟩
  rw [mem_latticeBallSet] at hv
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖x‖ = ‖(x - latticeVec d v) + latticeVec d v‖ := by abel_nf
    _ ≤ ‖x - latticeVec d v‖ + ‖latticeVec d v‖ := norm_add_le _ _
    _ ≤ Real.sqrt d / 2 + R := add_le_add (unitCube_norm_sub_le hxv) hv
    _ = R + Real.sqrt d / 2 := add_comm _ _

lemma closedBall_subset_biUnion_unitCube {d : ℕ} {R : ℝ} :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R - Real.sqrt d / 2) ⊆
      ⋃ v ∈ latticeBallSet d R, unitCube d v := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  obtain ⟨v, hxv⟩ := exists_mem_unitCube d x
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨v, ?_, hxv⟩
  rw [mem_latticeBallSet]
  calc
    ‖latticeVec d v‖ = ‖x - (x - latticeVec d v)‖ := by abel_nf
    _ ≤ ‖x‖ + ‖x - latticeVec d v‖ := norm_sub_le _ _
    _ ≤ (R - Real.sqrt d / 2) + Real.sqrt d / 2 := add_le_add hx (unitCube_norm_sub_le hxv)
    _ = R := by ring

lemma volume_biUnion_unitCube (d : ℕ) (S : Finset (Fin d → ℤ)) :
    volume (⋃ v ∈ S, unitCube d v) = (S.card : ℝ≥0∞) := by
  rw [measure_biUnion_finset]
  · simp [volume_unitCube]
  · intro u _ v _ huv
    exact unitCube_pairwiseDisjoint d huv
  · intro v _
    exact unitCube_measurableSet d v

/-- **Exact `d`-Dimensional Gauss Lattice-Ball Volume Bounds** (ALL `d ≥ 1`, ALL `R ≥ √d / 2`):
`ω_d * (R - √d / 2)^d ≤ latticeBallCount d R ≤ ω_d * (R + √d / 2)^d`. -/
theorem latticeBallCount_volume_bounds {d : ℕ} (hd : 1 ≤ d) {R : ℝ}
    (hR : Real.sqrt d / 2 ≤ R) :
    unitBallVolume d * (R - Real.sqrt d / 2) ^ d ≤ (latticeBallCount d R : ℝ) ∧
    (latticeBallCount d R : ℝ) ≤ unitBallVolume d * (R + Real.sqrt d / 2) ^ d := by
  have hR0 : 0 ≤ R := (by positivity : (0 : ℝ) ≤ Real.sqrt d / 2).trans hR
  have hsub1 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R - Real.sqrt d / 2)) ≤
      volume (⋃ v ∈ latticeBallSet d R, unitCube d v) :=
    measure_mono closedBall_subset_biUnion_unitCube
  have hsub2 : volume (⋃ v ∈ latticeBallSet d R, unitCube d v) ≤
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + Real.sqrt d / 2)) :=
    measure_mono biUnion_unitCube_subset_closedBall
  rw [volume_biUnion_unitCube] at hsub1 hsub2
  have h1 := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hsub1
  have h2 := ENNReal.toReal_mono (volume_closedBall_ne_top d _) hsub2
  rw [ENNReal.toReal_natCast, volume_closedBall_eq_unitBallVolume hd (by linarith)] at h1
  rw [ENNReal.toReal_natCast, volume_closedBall_eq_unitBallVolume hd (by positivity)] at h2
  exact ⟨h1, h2⟩

/-- **Classical Gauss Circle Bound (1834), Sharp Form**:
for all `R ≥ 1`, `|N₂(R) - π R²| ≤ √2 π R + π / 2`. -/
theorem gauss_circle_classical_bound_sharp {R : ℝ} (hR : 1 ≤ R) :
    |(gaussCircleCount R : ℝ) - Real.pi * R ^ 2| ≤ Real.sqrt 2 * Real.pi * R + Real.pi / 2 := by
  have hsqrt2_le : Real.sqrt 2 / 2 ≤ R := by
    have : Real.sqrt 2 ≤ 2 := by
      have hsq : Real.sqrt 2 ^ 2 ≤ 2 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hsq
    linarith
  have ⟨hlo, hhi⟩ := latticeBallCount_volume_bounds (d := 2) (by norm_num) hsqrt2_le
  rw [unitBallVolume_two] at hlo hhi
  change Real.pi * (R - Real.sqrt 2 / 2) ^ 2 ≤ (gaussCircleCount R : ℝ) at hlo
  change (gaussCircleCount R : ℝ) ≤ Real.pi * (R + Real.sqrt 2 / 2) ^ 2 at hhi
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [abs_le]
  constructor
  · nlinarith [hlo, hsq2, hpi]
  · nlinarith [hhi, hsq2, hpi]

/-- **Classical Gauss Circle Bound (1834)**:
for all `R ≥ 2`, `|N₂(R) - π R²| ≤ 2 π R`. -/
theorem gauss_circle_classical_bound {R : ℝ} (hR : 2 ≤ R) :
    |(gaussCircleCount R : ℝ) - Real.pi * R ^ 2| ≤ 2 * Real.pi * R := by
  have h1 := gauss_circle_classical_bound_sharp (by linarith : (1 : ℝ) ≤ R)
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    have hsq : Real.sqrt 2 ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hsq
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : Real.sqrt 2 * Real.pi * R ≤ (3 / 2) * Real.pi * R := by
    have hpiR : 0 ≤ Real.pi * R := by positivity
    nlinarith
  have h3 : Real.pi / 2 ≤ (1 / 2) * Real.pi * R := by nlinarith
  linarith

/-- **Classical Gauss 3D Sphere Bound**:
for all `R ≥ 1`, `|N₃(R) - (4/3) π R³| ≤ 2 √3 π R² + 3 π R + (√3 / 2) π`. -/
theorem gauss_sphere_classical_bound {R : ℝ} (hR : 1 ≤ R) :
    |(latticeBallCount 3 R : ℝ) - (4 / 3) * Real.pi * R ^ 3| ≤
      2 * Real.sqrt 3 * Real.pi * R ^ 2 + 3 * Real.pi * R + (Real.sqrt 3 / 2) * Real.pi := by
  have hsqrt3_le : Real.sqrt 3 / 2 ≤ R := by
    have : Real.sqrt 3 ≤ 2 := by
      have hsq : Real.sqrt 3 ^ 2 ≤ 2 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hsq
    linarith
  have ⟨hlo, hhi⟩ := latticeBallCount_volume_bounds (d := 3) (by norm_num) hsqrt3_le
  rw [unitBallVolume_three] at hlo hhi
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcube3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, hsq3]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp_hi : (4 / 3) * Real.pi * (R + Real.sqrt 3 / 2) ^ 3 - (4 / 3) * Real.pi * R ^ 3 =
      2 * Real.sqrt 3 * Real.pi * R ^ 2 + 3 * Real.pi * R + (Real.sqrt 3 / 2) * Real.pi := by
    calc
      (4 / 3) * Real.pi * (R + Real.sqrt 3 / 2) ^ 3 - (4 / 3) * Real.pi * R ^ 3
          = (4 / 3) * Real.pi * (3 / 2 * Real.sqrt 3 * R ^ 2 + 3 / 4 * Real.sqrt 3 ^ 2 * R +
              1 / 8 * Real.sqrt 3 ^ 3) := by ring
      _ = (4 / 3) * Real.pi * (3 / 2 * Real.sqrt 3 * R ^ 2 + 3 / 4 * 3 * R +
              1 / 8 * (3 * Real.sqrt 3)) := by rw [hsq3, hcube3]
      _ = 2 * Real.sqrt 3 * Real.pi * R ^ 2 + 3 * Real.pi * R + (Real.sqrt 3 / 2) * Real.pi := by ring
  have hexp_lo : (4 / 3) * Real.pi * R ^ 3 - (4 / 3) * Real.pi * (R - Real.sqrt 3 / 2) ^ 3 =
      2 * Real.sqrt 3 * Real.pi * R ^ 2 - 3 * Real.pi * R + (Real.sqrt 3 / 2) * Real.pi := by
    calc
      (4 / 3) * Real.pi * R ^ 3 - (4 / 3) * Real.pi * (R - Real.sqrt 3 / 2) ^ 3
          = (4 / 3) * Real.pi * (3 / 2 * Real.sqrt 3 * R ^ 2 - 3 / 4 * Real.sqrt 3 ^ 2 * R +
              1 / 8 * Real.sqrt 3 ^ 3) := by ring
      _ = (4 / 3) * Real.pi * (3 / 2 * Real.sqrt 3 * R ^ 2 - 3 / 4 * 3 * R +
              1 / 8 * (3 * Real.sqrt 3)) := by rw [hsq3, hcube3]
      _ = 2 * Real.sqrt 3 * Real.pi * R ^ 2 - 3 * Real.pi * R + (Real.sqrt 3 / 2) * Real.pi := by ring
  rw [abs_le]
  constructor
  · nlinarith [hlo, hexp_lo, hpi]
  · linarith [hhi, hexp_hi]

/-- **Universal `d`-Dimensional Lattice-Point Asymptotic** (ALL `d ≥ 1`):
`(latticeBallCount d R : ℝ) / R^d → ω_d` as `R → ∞`. -/
theorem latticeBallCount_asymptotic {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun R : ℝ => (latticeBallCount d R : ℝ) / R ^ d) atTop (nhds (unitBallVolume d)) := by
  have hlow_lim : Tendsto (fun R : ℝ => unitBallVolume d * (1 - (Real.sqrt d / 2) / R) ^ d)
      atTop (nhds (unitBallVolume d)) := by
    have h0 : Tendsto (fun R : ℝ => (Real.sqrt d / 2) / R) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h1 : Tendsto (fun R : ℝ => (1 - (Real.sqrt d / 2) / R) ^ d) atTop (nhds ((1 - 0) ^ d)) :=
      (tendsto_const_nhds.sub h0).pow d
    simpa using tendsto_const_nhds.mul h1
  have hhigh_lim : Tendsto (fun R : ℝ => unitBallVolume d * (1 + (Real.sqrt d / 2) / R) ^ d)
      atTop (nhds (unitBallVolume d)) := by
    have h0 : Tendsto (fun R : ℝ => (Real.sqrt d / 2) / R) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h1 : Tendsto (fun R : ℝ => (1 + (Real.sqrt d / 2) / R) ^ d) atTop (nhds ((1 + 0) ^ d)) :=
      (tendsto_const_nhds.add h0).pow d
    simpa using tendsto_const_nhds.mul h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hhigh_lim ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max (Real.sqrt d / 2) 1)] with R hR
    have hRd : Real.sqrt d / 2 ≤ R := (le_max_left _ _).trans hR
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hR)
    have hlo := (latticeBallCount_volume_bounds hd hRd).1
    have hpow : 0 < R ^ d := pow_pos hRpos d
    rw [le_div_iff₀ hpow]
    calc
      unitBallVolume d * (1 - (Real.sqrt d / 2) / R) ^ d * R ^ d
          = unitBallVolume d * ((1 - (Real.sqrt d / 2) / R) * R) ^ d := by
              rw [mul_assoc, mul_pow]
      _ = unitBallVolume d * (R - Real.sqrt d / 2) ^ d := by
              congr 2; field_simp [hRpos.ne']
      _ ≤ (latticeBallCount d R : ℝ) := hlo
  · filter_upwards [Filter.eventually_ge_atTop (max (Real.sqrt d / 2) 1)] with R hR
    have hRd : Real.sqrt d / 2 ≤ R := (le_max_left _ _).trans hR
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hR)
    have hhi := (latticeBallCount_volume_bounds hd hRd).2
    have hpow : 0 < R ^ d := pow_pos hRpos d
    rw [div_le_iff₀ hpow]
    calc
      (latticeBallCount d R : ℝ)
          ≤ unitBallVolume d * (R + Real.sqrt d / 2) ^ d := hhi
      _ = unitBallVolume d * ((1 + (Real.sqrt d / 2) / R) * R) ^ d := by
              congr 2; field_simp [hRpos.ne']
      _ = unitBallVolume d * (1 + (Real.sqrt d / 2) / R) ^ d * R ^ d := by
              rw [mul_assoc, mul_pow]

end ElementaryGaussBounds

/-! ## Section 3: Oscillatory-Integral Decay of the 2D Disk Fourier Transform -/

section DiskFourierDecay

/-- Half-circle cosine oscillatory integral `I(λ) = ∫₀¹ √(1 - t²) cos(λ t) dt`. -/
def halfCircleCosIntegral (lam : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)

private lemma rpow_three_halves_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rcases hx.eq_or_lt with rfl | hpos
  · simp
  · rw [show ((3 : ℝ) / 2) = (1 : ℝ) + (1 / 2 : ℝ) by norm_num,
      Real.rpow_add hpos, Real.rpow_one, Real.sqrt_eq_rpow]

private lemma hasDerivAt_sqrt_one_sub_sq {t : ℝ} (ht : 0 < 1 - t ^ 2) :
    HasDerivAt (fun u => Real.sqrt (1 - u ^ 2)) (-t / Real.sqrt (1 - t ^ 2)) t := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (0 - 2 * t ^ (2 - 1)) t :=
    (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_pow 2 t)
  have h2 := h1.sqrt ht.ne'
  refine h2.congr_deriv ?_
  have hsq : Real.sqrt (1 - t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  field_simp [hsq]
  ring

private lemma hasDerivAt_div_sqrt_one_sub_sq {t : ℝ} (ht : 0 < 1 - t ^ 2) :
    HasDerivAt (fun u => u / Real.sqrt (1 - u ^ 2))
      (1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2))) t := by
  have hsq : Real.sqrt (1 - t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have h := (hasDerivAt_id t).div (hasDerivAt_sqrt_one_sub_sq ht) hsq
  refine h.congr_deriv ?_
  dsimp only [id_eq]
  have hsq2 : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt ht.le
  field_simp [hsq, ht.ne']
  nlinarith [hsq2]

private lemma hasDerivAt_ibp_prim {lam t : ℝ} (hlam : lam ≠ 0) (ht : 0 < 1 - t ^ 2) :
    HasDerivAt
      (fun u => Real.sqrt (1 - u ^ 2) * Real.sin (lam * u) / lam -
        (u / Real.sqrt (1 - u ^ 2)) * Real.cos (lam * u) / lam ^ 2)
      (Real.sqrt (1 - t ^ 2) * Real.cos (lam * t) -
        (1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2))) * Real.cos (lam * t) / lam ^ 2) t := by
  have hlin : HasDerivAt (fun u : ℝ => lam * u) lam t := by
    simpa using (hasDerivAt_id t).const_mul lam
  have hsin : HasDerivAt (fun u => Real.sin (lam * u)) (Real.cos (lam * t) * lam) t :=
    hlin.sin
  have hcos : HasDerivAt (fun u => Real.cos (lam * u)) (-Real.sin (lam * t) * lam) t :=
    hlin.cos
  have hterm1 : HasDerivAt (fun u => Real.sqrt (1 - u ^ 2) * Real.sin (lam * u) / lam)
      (((-t / Real.sqrt (1 - t ^ 2)) * Real.sin (lam * t) +
        Real.sqrt (1 - t ^ 2) * (Real.cos (lam * t) * lam)) / lam) t :=
    ((hasDerivAt_sqrt_one_sub_sq ht).mul hsin).div_const lam
  have hterm2 : HasDerivAt (fun u => (u / Real.sqrt (1 - u ^ 2)) * Real.cos (lam * u) / lam ^ 2)
      (((1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2))) * Real.cos (lam * t) +
        (t / Real.sqrt (1 - t ^ 2)) * (-Real.sin (lam * t) * lam)) / lam ^ 2) t :=
    ((hasDerivAt_div_sqrt_one_sub_sq ht).mul hcos).div_const (lam ^ 2)
  refine (hterm1.sub hterm2).congr_deriv ?_
  have hsq : Real.sqrt (1 - t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  field_simp [hlam, hsq, ht.ne']
  ring

/-- **Elementary Stationary-Phase / 2-IBP Decay Bound**:
for every `λ > 0`, `|∫₀¹ √(1 - t²) cos(λ t) dt| ≤ 5 / λ^{3/2}`. -/
theorem abs_halfCircleCosIntegral_le {lam : ℝ} (hlam : 0 < lam) :
    |halfCircleCosIntegral lam| ≤ 5 / lam ^ ((3 : ℝ) / 2) := by
  rw [rpow_three_halves_eq hlam.le]
  by_cases hsmall : lam ≤ 2
  · have hbound : |halfCircleCosIntegral lam| ≤ 1 := by
      unfold halfCircleCosIntegral
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (f := fun t => Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)) (C := 1) fun t ht => by
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
          rw [Real.norm_eq_abs, abs_mul]
          have hs1 : Real.sqrt (1 - t ^ 2) ≤ 1 := by
            refine Real.sqrt_le_one.mpr ?_
            nlinarith [sq_nonneg t]
          have hs2 : |Real.sqrt (1 - t ^ 2)| ≤ 1 := by
            rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hs1
          calc
            |Real.sqrt (1 - t ^ 2)| * |Real.cos (lam * t)| ≤ 1 * 1 :=
              mul_le_mul hs2 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      simpa [Real.norm_eq_abs] using h1
    have hlam_sq : lam * Real.sqrt lam ≤ 5 := by
      have hsr : Real.sqrt lam ≤ 2 := by
        have : Real.sqrt lam ^ 2 ≤ 2 ^ 2 := by rw [Real.sq_sqrt hlam.le]; linarith
        exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp this
      nlinarith [Real.sqrt_nonneg lam]
    have hpos : 0 < lam * Real.sqrt lam := mul_pos hlam (Real.sqrt_pos.mpr hlam)
    rw [le_div_iff₀ hpos]
    nlinarith
  · push Not at hsmall
    set δ : ℝ := 1 / lam
    set c : ℝ := 1 - δ
    have hδ_pos : 0 < δ := one_div_pos.mpr hlam
    have hδ_lt_half : δ < 1 / 2 := by
      dsimp [δ]
      exact (one_div_lt_one_div hlam (by norm_num)).mpr hsmall
    have hc_pos : 0 < c := by linarith
    have hc_lt_one : c < 1 := by linarith
    -- Split integral into `[0, c]` and `[c, 1]`
    have hcont : Continuous (fun t : ℝ => Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)) := by
      fun_prop
    have hsplit : halfCircleCosIntegral lam =
        (∫ t in (0 : ℝ)..c, Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)) +
        (∫ t in c..1, Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 c) (hcont.intervalIntegrable c 1)).symm
    -- Cap `[c, 1]` bound: `≤ √(2 δ) * δ = √2 / (lam * √lam)`
    have hcap : |∫ t in c..1, Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)| ≤
        Real.sqrt (2 * δ) * δ := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := 1)
        (f := fun t => Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)) (C := Real.sqrt (2 * δ))
        fun t ht => by
          rw [Set.uIoc_of_le hc_lt_one.le] at ht
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have hsub : 1 - t ^ 2 ≤ 2 * δ := by
            have h1t : 1 - t ≤ δ := by linarith [ht.1]
            have h2t : 1 + t ≤ 2 := by linarith [ht.2]
            have hnn : 0 ≤ 1 - t := by linarith [ht.2]
            nlinarith
          calc
            Real.sqrt (1 - t ^ 2) * |Real.cos (lam * t)|
                ≤ Real.sqrt (2 * δ) * 1 :=
                  mul_le_mul (Real.sqrt_le_sqrt hsub) (Real.abs_cos_le_one _) (abs_nonneg _)
                    (Real.sqrt_nonneg _)
            _ = Real.sqrt (2 * δ) := mul_one _
      have heq : |1 - c| = δ := by rw [abs_of_pos (by linarith : 0 < 1 - c)]; ring
      simpa [Real.norm_eq_abs, heq] using h1
    -- Interior `[0, c]` via FTC
    have hpos_on : ∀ t ∈ Set.uIcc (0 : ℝ) c, 0 < 1 - t ^ 2 := by
      intro t ht
      rw [Set.uIcc_of_le hc_pos.le] at ht
      nlinarith [ht.1, ht.2]
    let g2 : ℝ → ℝ := fun t => (1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2))) / lam ^ 2
    let g2cos : ℝ → ℝ := fun t =>
      (1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2))) * Real.cos (lam * t) / lam ^ 2
    have hg2_cont : ContinuousOn g2 (Set.uIcc 0 c) := by
      have hden_cont : Continuous (fun t : ℝ => (1 - t ^ 2) * Real.sqrt (1 - t ^ 2)) := by
        fun_prop
      have hinv : ContinuousOn (fun t : ℝ => 1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2)))
          (Set.uIcc 0 c) :=
        continuousOn_const.div hden_cont.continuousOn fun t ht =>
          mul_ne_zero (hpos_on t ht).ne' (Real.sqrt_pos.mpr (hpos_on t ht)).ne'
      exact hinv.div_const (lam ^ 2)
    have hg2cos_cont : ContinuousOn g2cos (Set.uIcc 0 c) := by
      have hden_cont : Continuous (fun t : ℝ => (1 - t ^ 2) * Real.sqrt (1 - t ^ 2)) := by
        fun_prop
      have hinv : ContinuousOn (fun t : ℝ => 1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2)))
          (Set.uIcc 0 c) :=
        continuousOn_const.div hden_cont.continuousOn fun t ht =>
          mul_ne_zero (hpos_on t ht).ne' (Real.sqrt_pos.mpr (hpos_on t ht)).ne'
      have hcos_cont : Continuous (fun t : ℝ => Real.cos (lam * t)) := by fun_prop
      exact (hinv.mul hcos_cont.continuousOn).div_const (lam ^ 2)
    have hg2_int : IntervalIntegrable g2 volume 0 c :=
      hg2_cont.intervalIntegrable
    have hg2cos_int : IntervalIntegrable g2cos volume 0 c :=
      hg2cos_cont.intervalIntegrable
    let H : ℝ → ℝ := fun u =>
      Real.sqrt (1 - u ^ 2) * Real.sin (lam * u) / lam -
        (u / Real.sqrt (1 - u ^ 2)) * Real.cos (lam * u) / lam ^ 2
    have hftc1 :
        ∫ t in (0 : ℝ)..c, (Real.sqrt (1 - t ^ 2) * Real.cos (lam * t) - g2cos t) =
          H c - H 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_
      · exact hasDerivAt_ibp_prim hlam.ne' (hpos_on t ht)
      · exact (hcont.intervalIntegrable 0 c).sub hg2cos_int
    have hH0 : H 0 = 0 := by simp [H]
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable 0 c) hg2cos_int, hH0,
      sub_zero] at hftc1
    have hint_eq :
        ∫ t in (0 : ℝ)..c, Real.sqrt (1 - t ^ 2) * Real.cos (lam * t) =
          H c + ∫ t in (0 : ℝ)..c, g2cos t := by linarith
    have hftc2 : ∫ t in (0 : ℝ)..c, g2 t = (c / Real.sqrt (1 - c ^ 2)) / lam ^ 2 := by
      have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) c,
          HasDerivAt (fun u => (u / Real.sqrt (1 - u ^ 2)) / lam ^ 2) (g2 t) t := by
        intro t ht
        exact (hasDerivAt_div_sqrt_one_sub_sq (hpos_on t ht)).div_const (lam ^ 2)
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hg2_int
      simpa using h
    have hg2cos_le : |∫ t in (0 : ℝ)..c, g2cos t| ≤ (c / Real.sqrt (1 - c ^ 2)) / lam ^ 2 := by
      rw [← hftc2]
      have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) hc_pos.le
        (f := g2cos)
      refine h1.trans (intervalIntegral.integral_mono_on hc_pos.le hg2cos_int.abs hg2_int ?_)
      intro t ht
      have htp : 0 < 1 - t ^ 2 := hpos_on t (by rw [Set.uIcc_of_le hc_pos.le]; exact ht)
      have hden_pos : 0 < (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) :=
        mul_pos htp (Real.sqrt_pos.mpr htp)
      dsimp [g2cos, g2]
      rw [abs_div, abs_mul, abs_of_pos (one_div_pos.mpr hden_pos), abs_of_pos (sq_pos_of_pos hlam)]
      have hcos : |Real.cos (lam * t)| ≤ 1 := Real.abs_cos_le_one _
      have hnum : 1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2)) * |Real.cos (lam * t)| ≤
          1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2)) := by
        nlinarith [one_div_pos.mpr hden_pos]
      exact div_le_div_of_nonneg_right hnum (sq_nonneg lam)
    -- Elementary bounds at `c = 1 - δ`
    have h1mc2_ge : δ ≤ 1 - c ^ 2 := by
      have : 1 - c ^ 2 = δ * (2 - δ) := by dsimp [c]; ring
      nlinarith
    have h1mc2_le : 1 - c ^ 2 ≤ 2 * δ := by
      have : 1 - c ^ 2 = δ * (2 - δ) := by dsimp [c]; ring
      nlinarith
    have hsqrt_ge : Real.sqrt δ ≤ Real.sqrt (1 - c ^ 2) := Real.sqrt_le_sqrt h1mc2_ge
    have hsqrt_le : Real.sqrt (1 - c ^ 2) ≤ Real.sqrt (2 * δ) := Real.sqrt_le_sqrt h1mc2_le
    have hc_div_le : c / Real.sqrt (1 - c ^ 2) ≤ 1 / Real.sqrt δ := by
      have hpos1 : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ_pos
      have hpos2 : 0 < Real.sqrt (1 - c ^ 2) := lt_of_lt_of_le hpos1 hsqrt_ge
      rw [div_le_div_iff₀ hpos2 hpos1]
      nlinarith [hsqrt_ge, hc_lt_one]
    have hHc_le : |H c| ≤ Real.sqrt (2 * δ) / lam + (1 / Real.sqrt δ) / lam ^ 2 := by
      dsimp [H]
      have htri : |Real.sqrt (1 - c ^ 2) * Real.sin (lam * c) / lam -
          (c / Real.sqrt (1 - c ^ 2)) * Real.cos (lam * c) / lam ^ 2| ≤
          |Real.sqrt (1 - c ^ 2) * Real.sin (lam * c) / lam| +
          |(c / Real.sqrt (1 - c ^ 2)) * Real.cos (lam * c) / lam ^ 2| := abs_sub _ _
      refine htri.trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hlam]
        refine div_le_div_of_nonneg_right ?_ hlam.le
        calc
          Real.sqrt (1 - c ^ 2) * |Real.sin (lam * c)| ≤ Real.sqrt (2 * δ) * 1 :=
            mul_le_mul hsqrt_le (Real.abs_sin_le_one _) (abs_nonneg _) (Real.sqrt_nonneg _)
          _ = Real.sqrt (2 * δ) := mul_one _
      · rw [abs_div, abs_mul, abs_of_pos (div_pos hc_pos (Real.sqrt_pos.mpr (by linarith))),
          abs_of_pos (sq_pos_of_pos hlam)]
        refine div_le_div_of_nonneg_right ?_ (sq_nonneg lam)
        calc
          c / Real.sqrt (1 - c ^ 2) * |Real.cos (lam * c)| ≤ (1 / Real.sqrt δ) * 1 :=
            mul_le_mul hc_div_le (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
          _ = 1 / Real.sqrt δ := mul_one _
    -- Convert all terms to `1 / (lam * √lam)`
    have hsqrt_δ : Real.sqrt δ = 1 / Real.sqrt lam := by
      dsimp [δ]
      rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
    have hsqrt_2δ : Real.sqrt (2 * δ) = Real.sqrt 2 / Real.sqrt lam := by
      rw [Real.sqrt_mul (by norm_num), hsqrt_δ]; ring
    have htermA : Real.sqrt (2 * δ) * δ = Real.sqrt 2 / (lam * Real.sqrt lam) := by
      rw [hsqrt_2δ]; dsimp [δ]; ring
    have htermB : Real.sqrt (2 * δ) / lam = Real.sqrt 2 / (lam * Real.sqrt lam) := by
      rw [hsqrt_2δ]; ring
    have htermC : (1 / Real.sqrt δ) / lam ^ 2 = 1 / (lam * Real.sqrt lam) := by
      rw [hsqrt_δ]
      have hsr : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
      have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
      field_simp [hlam.ne', hsr]
      nlinarith [hsq]
    have hg2cos_le' : |∫ t in (0 : ℝ)..c, g2cos t| ≤ 1 / (lam * Real.sqrt lam) := by
      rw [← htermC]
      exact hg2cos_le.trans (div_le_div_of_nonneg_right hc_div_le (sq_nonneg lam))
    have htotal : |halfCircleCosIntegral lam| ≤
        (2 * Real.sqrt 2 + 2) / (lam * Real.sqrt lam) := by
      rw [hsplit, hint_eq]
      calc
        |H c + (∫ t in (0 : ℝ)..c, g2cos t) +
            ∫ t in c..1, Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)|
            ≤ |H c| + |∫ t in (0 : ℝ)..c, g2cos t| +
              |∫ t in c..1, Real.sqrt (1 - t ^ 2) * Real.cos (lam * t)| := by
                have h1 := abs_add_le (H c + ∫ t in (0 : ℝ)..c, g2cos t)
                  (∫ t in c..1, Real.sqrt (1 - t ^ 2) * Real.cos (lam * t))
                have h2 := abs_add_le (H c) (∫ t in (0 : ℝ)..c, g2cos t)
                linarith
        _ ≤ (Real.sqrt (2 * δ) / lam + (1 / Real.sqrt δ) / lam ^ 2) +
              1 / (lam * Real.sqrt lam) + Real.sqrt (2 * δ) * δ :=
                add_le_add (add_le_add hHc_le hg2cos_le') hcap
        _ = (2 * Real.sqrt 2 + 2) / (lam * Real.sqrt lam) := by
              rw [htermA, htermB, htermC]; ring
    have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
      have : Real.sqrt 2 ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp this
    exact htotal.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-- Indicator function of the closed 2D disk `x² + y² ≤ R²`. -/
def diskInd (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 then 1 else 0

lemma diskInd_nonneg (R : ℝ) (p : ℝ × ℝ) : 0 ≤ diskInd R p := by
  unfold diskInd; split_ifs <;> norm_num

lemma diskInd_le_one (R : ℝ) (p : ℝ × ℝ) : diskInd R p ≤ 1 := by
  unfold diskInd; split_ifs <;> norm_num

lemma measurable_diskInd (R : ℝ) : Measurable (diskInd R) := by
  unfold diskInd
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
    measurable_const

/-- 2D Fourier transform of the disk indicator `1_{B(0, R)}` at frequency `(ξ₁, ξ₂)`:
`diskFourier R ξ₁ ξ₂ = ∫∫_{x² + y² ≤ R²} exp(-2π i (ξ₁ x + ξ₂ y)) dx dy`. -/
def diskFourier (R ξ₁ ξ₂ : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ,
    Complex.exp (-(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2) : ℝ) * Complex.I) * (diskInd R p : ℂ)

/-- Canonical measure-preserving equivalence between `ℝ × ℝ` and `EuclideanSpace ℝ (Fin 2)`. -/
def prodToE2 : (ℝ × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma volume_preserving_prodToE2 : MeasurePreserving prodToE2 volume volume := by
  unfold prodToE2
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm

/-- Planar rotation `LinearIsometryEquiv` on `EuclideanSpace ℝ (Fin 2)` for `(c, s)` with `c² + s² = 1`. -/
def rotE2 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  { toFun := fun x => WithLp.toLp 2 ![c * x 0 - s * x 1, s * x 0 + c * x 1]
    invFun := fun y => WithLp.toLp 2 ![c * y 0 + s * y 1, -s * y 0 + c * y 1]
    map_add' := fun x y => by
      ext i; fin_cases i <;> simp <;> ring
    map_smul' := fun r x => by
      ext i; fin_cases i <;> simp <;> ring
    left_inv := fun x => by
      ext i; fin_cases i
      · simp; linear_combination (x 0) * hcs
      · simp; linear_combination (x 1) * hcs
    right_inv := fun y => by
      ext i; fin_cases i
      · simp; linear_combination (y 0) * hcs
      · simp; linear_combination (y 1) * hcs
    norm_map' := fun x => by
      have hsq : ‖WithLp.toLp 2 ![c * x 0 - s * x 1, s * x 0 + c * x 1]‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
        simp only [Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one]
        change (c * x 0 - s * x 1) ^ 2 + (s * x 0 + c * x 1) ^ 2 = (x 0) ^ 2 + (x 1) ^ 2
        linear_combination ((x 0) ^ 2 + (x 1) ^ 2) * hcs
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }

/-- Measure-preserving planar rotation on `ℝ × ℝ`: `(u, v) ↦ (c u - s v, s u + c v)`. -/
def rotProd (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (prodToE2.trans (rotE2 c s hcs).toHomeomorph.toMeasurableEquiv).trans prodToE2.symm

lemma rotProd_apply (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (p : ℝ × ℝ) :
    rotProd c s hcs p = (c * p.1 - s * p.2, s * p.1 + c * p.2) := by
  simp [rotProd, prodToE2, rotE2]

lemma volume_preserving_rotProd (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    MeasurePreserving (rotProd c s hcs) volume volume := by
  unfold rotProd
  exact volume_preserving_prodToE2.symm.comp
    ((rotE2 c s hcs).measurePreserving.comp volume_preserving_prodToE2)

lemma integrable_diskInd (R : ℝ) : Integrable (diskInd R) (volume : Measure (ℝ × ℝ)) := by
  have hle : ∀ p : ℝ × ℝ, ‖diskInd R p‖ ≤
      (Set.Icc (-|R|) |R| ×ˢ Set.Icc (-|R|) |R|).indicator (fun _ => (1 : ℝ)) p := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (diskInd_nonneg R p)]
    unfold diskInd
    split_ifs with h
    · have h1 : |p.1| ≤ |R| := by
        have hsq : |p.1| ^ 2 ≤ |R| ^ 2 := by
          rw [sq_abs, sq_abs]; nlinarith [sq_nonneg p.2]
        exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp hsq
      have h2 : |p.2| ≤ |R| := by
        have hsq : |p.2| ^ 2 ≤ |R| ^ 2 := by
          rw [sq_abs, sq_abs]; nlinarith [sq_nonneg p.1]
        exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp hsq
      have hmem : p ∈ Set.Icc (-|R|) |R| ×ˢ Set.Icc (-|R|) |R| :=
        ⟨abs_le.mp h1, abs_le.mp h2⟩
      rw [Set.indicator_of_mem hmem]
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) p
  have hbox : Integrable
      ((Set.Icc (-|R|) |R| ×ˢ Set.Icc (-|R|) |R|).indicator (fun _ => (1 : ℝ)))
      (volume : Measure (ℝ × ℝ)) := by
    refine integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc) |>.mpr ?_
    refine integrableOn_const ?_
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  exact hbox.mono' (measurable_diskInd R).aestronglyMeasurable (Filter.Eventually.of_forall hle)

private lemma integral_complex_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) :
    ∫ x, (f x : ℂ) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) :=
  Complex.ofRealCLM.integral_comp_comm' Complex.isometry_ofReal.antilipschitz f

lemma integral_diskInd {R : ℝ} (hR : 0 ≤ R) :
    ∫ p : ℝ × ℝ, diskInd R p = Real.pi * R ^ 2 := by
  have heq : (fun p : ℝ × ℝ => diskInd R p) =
      (prodToE2 ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R).indicator
        (fun _ => (1 : ℝ)) := by
    funext p
    unfold diskInd
    have hmem : p ∈ prodToE2 ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ↔
        p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 := by
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      have hsq : ‖prodToE2 p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
        simp [prodToE2, Real.norm_eq_abs, sq_abs]
      rw [← hsq]
      exact (sq_le_sq₀ (norm_nonneg _) hR).symm
    by_cases h : p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2
    · rw [if_pos h, Set.indicator_of_mem (hmem.mpr h)]
    · rw [if_neg h, Set.indicator_of_notMem (mt hmem.mp h)]
  rw [heq, integral_indicator (measurableSet_closedBall.preimage prodToE2.measurable)]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
  rw [volume_preserving_prodToE2.measure_preimage measurableSet_closedBall.nullMeasurableSet,
    volume_closedBall_eq_unitBallVolume (d := 2) (by norm_num) hR, unitBallVolume_two]

/-- Zero-frequency value of the disk Fourier transform: `diskFourier R 0 0 = π R²`. -/
theorem diskFourier_zero {R : ℝ} (hR : 0 ≤ R) :
    diskFourier R 0 0 = (Real.pi * R ^ 2 : ℂ) := by
  unfold diskFourier
  simp only [zero_mul, add_zero, mul_zero, neg_zero, Complex.ofReal_zero, Complex.exp_zero,
    one_mul]
  rw [integral_complex_ofReal, integral_diskInd hR]
  push_cast
  rfl

/-- Exact 1D reduction of `diskFourier R ξ₁ ξ₂` for `(ξ₁, ξ₂) ≠ (0, 0)` by orthogonal rotation. -/
theorem diskFourier_eq_halfCircleCosIntegral {R ξ₁ ξ₂ : ℝ} (hR : 0 < R)
    (hξ : ξ₁ ^ 2 + ξ₂ ^ 2 ≠ 0) :
    diskFourier R ξ₁ ξ₂ =
      ((4 * R ^ 2 * halfCircleCosIntegral (2 * Real.pi * Real.sqrt (ξ₁ ^ 2 + ξ₂ ^ 2) * R) : ℝ) :
        ℂ) := by
  set r : ℝ := Real.sqrt (ξ₁ ^ 2 + ξ₂ ^ 2)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (lt_of_le_of_ne (by positivity) hξ.symm)
  set c : ℝ := ξ₁ / r
  set s : ℝ := ξ₂ / r
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    have hr2 : r ^ 2 = ξ₁ ^ 2 + ξ₂ ^ 2 := Real.sq_sqrt (by positivity)
    field_simp [hr_pos.ne']
    linarith [hr2]
  -- Rotate integration variables by `rotProd c s hcs`
  have hrot : diskFourier R ξ₁ ξ₂ =
      ∫ p : ℝ × ℝ,
        Complex.exp (-(2 * Real.pi * r * p.1 : ℝ) * Complex.I) * (diskInd R p : ℂ) := by
    unfold diskFourier
    rw [← (volume_preserving_rotProd c s hcs).integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    rw [rotProd_apply]
    have hnorm : (c * p.1 - s * p.2) ^ 2 + (s * p.1 + c * p.2) ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      linear_combination (p.1 ^ 2 + p.2 ^ 2) * hcs
    have hdot : ξ₁ * (c * p.1 - s * p.2) + ξ₂ * (s * p.1 + c * p.2) = r * p.1 := by
      dsimp [c, s]
      have hr2 : r ^ 2 = ξ₁ ^ 2 + ξ₂ ^ 2 := Real.sq_sqrt (by positivity)
      field_simp [hr_pos.ne']
      rw [hr2]
      ring
    have hind : diskInd R (c * p.1 - s * p.2, s * p.1 + c * p.2) = diskInd R p := by
      unfold diskInd; simp [hnorm]
    rw [hdot, hind]
    congr 2
    ring_nf
  rw [hrot]
  -- Fubini on `ℝ × ℝ`
  have hint_prod : Integrable
      (fun p : ℝ × ℝ => Complex.exp (-(2 * Real.pi * r * p.1 : ℝ) * Complex.I) *
        (diskInd R p : ℂ)) (volume.prod volume) := by
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Complex.exp (-(2 * Real.pi * r * p.1 : ℝ) * Complex.I) *
          (diskInd R p : ℂ)) (volume.prod volume) := by
      refine Measurable.aestronglyMeasurable ?_
      refine Measurable.mul ?_ (Complex.continuous_ofReal.measurable.comp (measurable_diskInd R))
      fun_prop
    refine (integrable_diskInd R).mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul,
      show -(2 * Real.pi * r * p.1 : ℝ) * Complex.I = ((-(2 * Real.pi * r * p.1) : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (diskInd_nonneg R p)]
  rw [Measure.volume_eq_prod, MeasureTheory.integral_prod _ hint_prod]
  -- Evaluate the inner `v`-integral for each fixed `u`
  have hinner : ∀ u : ℝ,
      (∫ v : ℝ, Complex.exp (-(2 * Real.pi * r * u : ℝ) * Complex.I) *
        (diskInd R (u, v) : ℂ)) =
        if |u| ≤ R then
          Complex.exp (-(2 * Real.pi * r * u : ℝ) * Complex.I) *
            ((2 * Real.sqrt (R ^ 2 - u ^ 2) : ℝ) : ℂ)
        else 0 := by
    intro u
    rw [integral_const_mul]
    split_ifs with hu
    · congr 1
      rw [integral_complex_ofReal]
      congr 1
      set s_u : ℝ := Real.sqrt (R ^ 2 - u ^ 2)
      have hu2 : u ^ 2 ≤ R ^ 2 := by
        have := (sq_le_sq₀ (abs_nonneg u) hR.le).mpr hu
        simpa [sq_abs] using this
      have hind_eq : (fun v : ℝ => diskInd R (u, v)) =
          (Set.Icc (-s_u) s_u).indicator (fun _ => (1 : ℝ)) := by
        funext v
        unfold diskInd
        have hiff : u ^ 2 + v ^ 2 ≤ R ^ 2 ↔ v ∈ Set.Icc (-s_u) s_u := by
          rw [Set.mem_Icc, ← abs_le]
          have hs_nn : 0 ≤ s_u := Real.sqrt_nonneg _
          have hs_sq : s_u ^ 2 = R ^ 2 - u ^ 2 := Real.sq_sqrt (by linarith)
          constructor
          · intro h
            have hv2 : |v| ^ 2 ≤ s_u ^ 2 := by rw [sq_abs, hs_sq]; linarith
            exact (sq_le_sq₀ (abs_nonneg v) hs_nn).mp hv2
          · intro h
            have hv2 : |v| ^ 2 ≤ s_u ^ 2 := (sq_le_sq₀ (abs_nonneg v) hs_nn).mpr h
            rw [sq_abs, hs_sq] at hv2
            linarith
        by_cases h : u ^ 2 + v ^ 2 ≤ R ^ 2
        · rw [if_pos h, Set.indicator_of_mem (hiff.mp h)]
        · rw [if_neg h, Set.indicator_of_notMem (mt hiff.mpr h)]
      rw [hind_eq, integral_indicator measurableSet_Icc]
      simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith [Real.sqrt_nonneg (R ^ 2 - u ^ 2)])]
      ring
    · have hzero : ∀ v : ℝ, diskInd R (u, v) = 0 := by
        intro v
        unfold diskInd
        rw [if_neg]
        push Not at hu ⊢
        have hu2 : R ^ 2 < u ^ 2 := by
          have := (sq_lt_sq₀ hR.le (abs_nonneg u)).mpr hu
          simpa [sq_abs] using this
        nlinarith [sq_nonneg v]
      simp [hzero]
  simp_rw [hinner]
  -- Convert `∫ u, if |u| ≤ R then ... else 0` to `∫ u in (-R)..R, ...`
  have hIcc :
      (∫ u : ℝ, if |u| ≤ R then
        Complex.exp (-(2 * Real.pi * r * u : ℝ) * Complex.I) *
          ((2 * Real.sqrt (R ^ 2 - u ^ 2) : ℝ) : ℂ)
        else 0) =
      ∫ u in (-R)..R,
        Complex.exp (-(2 * Real.pi * r * u : ℝ) * Complex.I) *
          ((2 * Real.sqrt (R ^ 2 - u ^ 2) : ℝ) : ℂ) := by
    have heq_ind :
        (fun u : ℝ => if |u| ≤ R then
          Complex.exp (-(2 * Real.pi * r * u : ℝ) * Complex.I) *
            ((2 * Real.sqrt (R ^ 2 - u ^ 2) : ℝ) : ℂ)
          else 0) =
        (Set.Icc (-R) R).indicator (fun u =>
          Complex.exp (-(2 * Real.pi * r * u : ℝ) * Complex.I) *
            ((2 * Real.sqrt (R ^ 2 - u ^ 2) : ℝ) : ℂ)) := by
      funext u
      by_cases h : |u| ≤ R
      · rw [if_pos h, Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp h))]
      · rw [if_neg h, Set.indicator_of_notMem (by rwa [Set.mem_Icc, ← abs_le])]
    rw [heq_ind, integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
  rw [hIcc]
  -- Split `exp(-i θ) = cos θ - i sin θ`: odd `sin` integral vanishes, even `cos` doubles
  have hcont_c : Continuous (fun u : ℝ =>
      2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u)) := by fun_prop
  have hcont_s : Continuous (fun u : ℝ =>
      2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.sin (2 * Real.pi * r * u)) := by fun_prop
  have hexp_split : ∀ u : ℝ,
      Complex.exp (-(2 * Real.pi * r * u : ℝ) * Complex.I) *
        ((2 * Real.sqrt (R ^ 2 - u ^ 2) : ℝ) : ℂ) =
      ((2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u) : ℝ) : ℂ) -
      Complex.I * ((2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.sin (2 * Real.pi * r * u) : ℝ) : ℂ) := by
    intro u
    rw [show -(2 * Real.pi * r * u : ℝ) * Complex.I = ((-(2 * Real.pi * r * u) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I]
    simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
      Complex.ofReal_sin, Complex.ofReal_mul]
    ring
  simp_rw [hexp_split]
  have hint_c : IntervalIntegrable
      (fun u : ℝ => ((2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u) : ℝ) : ℂ))
      volume (-R) R :=
    (Complex.continuous_ofReal.comp hcont_c).intervalIntegrable (-R) R
  have hint_s : IntervalIntegrable
      (fun u : ℝ => Complex.I * ((2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.sin (2 * Real.pi * r * u) : ℝ) : ℂ))
      volume (-R) R :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hcont_s)).intervalIntegrable (-R) R
  rw [intervalIntegral.integral_sub hint_c hint_s,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  -- Odd integral `∫_{-R}^R ... sin(...) = 0`
  have hodd : ∫ u in (-R)..R, 2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.sin (2 * Real.pi * r * u) = 0 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun u => 2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.sin (2 * Real.pi * r * u))
      (a := -R) (b := R)
    simp only [neg_neg, neg_sq, mul_neg, Real.sin_neg, mul_neg, intervalIntegral.integral_neg] at hcomp
    linarith
  -- Even integral `∫_{-R}^R ... cos(...) = 2 ∫_0^R ... cos(...)`
  have heven : ∫ u in (-R)..R, 2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u) =
      4 * ∫ u in (0 : ℝ)..R, Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u) := by
    have hsp := (intervalIntegral.integral_add_adjacent_intervals
      (hcont_c.intervalIntegrable (μ := volume) (-R) 0)
      (hcont_c.intervalIntegrable (μ := volume) 0 R)).symm
    have hneg := intervalIntegral.integral_comp_neg
      (f := fun u => 2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u))
      (a := -R) (b := 0)
    simp only [neg_zero, neg_neg, neg_sq, mul_neg, Real.cos_neg] at hneg
    rw [hsp, hneg]
    have hpull : ∫ u in (0 : ℝ)..R, 2 * Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u) =
        2 * ∫ u in (0 : ℝ)..R, Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u _ => by ring
    linarith
  -- Change of variable `u = R * t` on `[0, 1]`
  have hscale :
      ∫ u in (0 : ℝ)..R, Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u) =
        R ^ 2 * halfCircleCosIntegral (2 * Real.pi * r * R) := by
    unfold halfCircleCosIntegral
    have hcomp := intervalIntegral.integral_comp_mul_left
      (f := fun u => Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u))
      (a := (0 : ℝ)) (b := 1) hR.ne'
    simp only [mul_zero, mul_one, smul_eq_mul] at hcomp
    have hpull : ∫ t in (0 : ℝ)..1,
        Real.sqrt (R ^ 2 - (R * t) ^ 2) * Real.cos (2 * Real.pi * r * (R * t)) =
      R * ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t ^ 2) * Real.cos (2 * Real.pi * r * R * t) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have hsq : R ^ 2 - (R * t) ^ 2 = R ^ 2 * (1 - t ^ 2) := by ring
      rw [hsq, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]
      rw [show 2 * Real.pi * r * (R * t) = 2 * Real.pi * r * R * t by ring]
      ring
    calc
      ∫ u in (0 : ℝ)..R, Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u)
          = R * (R⁻¹ * ∫ u in (0 : ℝ)..R, Real.sqrt (R ^ 2 - u ^ 2) * Real.cos (2 * Real.pi * r * u)) := by
              rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
      _ = R * ∫ t in (0 : ℝ)..1,
            Real.sqrt (R ^ 2 - (R * t) ^ 2) * Real.cos (2 * Real.pi * r * (R * t)) := by
              rw [← hcomp]
      _ = R * (R * ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t ^ 2) * Real.cos (2 * Real.pi * r * R * t)) := by
              rw [hpull]
      _ = R ^ 2 * ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t ^ 2) * Real.cos (2 * Real.pi * r * R * t) := by
              ring
  rw [hodd, Complex.ofReal_zero, mul_zero, sub_zero, heven, hscale]
  congr 1
  ring

/-- **Unconditional `O(√R / ‖ξ‖^{3/2})` Decay of the 2D Disk Fourier Transform**:
for all `R > 0` and `(ξ₁, ξ₂) ≠ (0, 0)`,
`‖diskFourier R ξ₁ ξ₂‖ ≤ 2 * √R / (ξ₁² + ξ₂²)^{3/4}`. -/
theorem norm_diskFourier_le {R ξ₁ ξ₂ : ℝ} (hR : 0 < R) (hξ : ξ₁ ^ 2 + ξ₂ ^ 2 ≠ 0) :
    ‖diskFourier R ξ₁ ξ₂‖ ≤ 2 * Real.sqrt R / (ξ₁ ^ 2 + ξ₂ ^ 2) ^ ((3 : ℝ) / 4) := by
  rw [diskFourier_eq_halfCircleCosIntegral hR hξ, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : 0 < 4 * R ^ 2)]
  set r : ℝ := Real.sqrt (ξ₁ ^ 2 + ξ₂ ^ 2)
  have hξ_pos : 0 < ξ₁ ^ 2 + ξ₂ ^ 2 := lt_of_le_of_ne (by positivity) hξ.symm
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hξ_pos
  have hlam_pos : 0 < 2 * Real.pi * r * R := by positivity
  have hbound := abs_halfCircleCosIntegral_le hlam_pos
  have h1 : 4 * R ^ 2 * |halfCircleCosIntegral (2 * Real.pi * r * R)| ≤
      4 * R ^ 2 * (5 / (2 * Real.pi * r * R) ^ ((3 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  refine h1.trans ?_
  have hr_rpow : r ^ ((3 : ℝ) / 2) = (ξ₁ ^ 2 + ξ₂ ^ 2) ^ ((3 : ℝ) / 4) := by
    dsimp [r]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hξ_pos.le]
    congr 1; norm_num
  have hfactor : (2 * Real.pi * r * R) ^ ((3 : ℝ) / 2) =
      (2 * Real.pi) ^ ((3 : ℝ) / 2) * r ^ ((3 : ℝ) / 2) * R ^ ((3 : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) hR.le, Real.mul_rpow (by positivity) hr_pos.le]
  rw [hfactor, hr_rpow, rpow_three_halves_eq hR.le]
  have hpi3 : 10 ≤ (2 * Real.pi) ^ ((3 : ℝ) / 2) := by
    rw [rpow_three_halves_eq (by positivity)]
    have h2pi : 6 < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hsr : 2 ≤ Real.sqrt (2 * Real.pi) := by
      have : (2 : ℝ) ^ 2 ≤ Real.sqrt (2 * Real.pi) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]; linarith
      exact (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp this
    nlinarith
  have hden_pos : 0 < (ξ₁ ^ 2 + ξ₂ ^ 2) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hξ_pos _
  have hRsq : R ^ 2 = R * (Real.sqrt R * Real.sqrt R) := by
    rw [Real.mul_self_sqrt hR.le]; ring
  have hsr_pos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have h2pi_pos : 0 < (2 * Real.pi) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hden_pos]
  calc
    4 * R ^ 2 * 5 * (ξ₁ ^ 2 + ξ₂ ^ 2) ^ ((3 : ℝ) / 4)
        = 20 * (R * Real.sqrt R) * Real.sqrt R * (ξ₁ ^ 2 + ξ₂ ^ 2) ^ ((3 : ℝ) / 4) := by
          rw [hRsq]; ring
    _ ≤ 2 * (2 * Real.pi) ^ ((3 : ℝ) / 2) * (R * Real.sqrt R) * Real.sqrt R *
          (ξ₁ ^ 2 + ξ₂ ^ 2) ^ ((3 : ℝ) / 4) := by
          have hnn : 0 ≤ (R * Real.sqrt R) * Real.sqrt R * (ξ₁ ^ 2 + ξ₂ ^ 2) ^ ((3 : ℝ) / 4) := by
            positivity
          nlinarith
    _ = 2 * Real.sqrt R *
          ((2 * Real.pi) ^ ((3 : ℝ) / 2) * (ξ₁ ^ 2 + ξ₂ ^ 2) ^ ((3 : ℝ) / 4) *
            (R * Real.sqrt R)) := by ring

end DiskFourierDecay

/-! ## Section 4: Compactly Supported 2D Tent Mollifier & Exact 2D Poisson Summation -/

section TentMollifierAndPoisson

/-- 1D compactly supported continuous tent mollifier of half-width `2 a`:
`tent a t = max 0 (2 a - |t|) / (4 a²)`, with `tent a ≥ 0`, `supp(tent a) ⊆ [-2a, 2a]`,
`∫ tent a = 1`, and Fourier transform `tentHat a ξ = sinc(2 π a ξ)²`. -/
def tent (a t : ℝ) : ℝ :=
  max 0 (2 * a - |t|) / (4 * a ^ 2)

lemma tent_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ tent a t := by
  unfold tent
  exact div_nonneg (le_max_left _ _) (by positivity)

lemma tent_le {a : ℝ} (ha : 0 < a) (t : ℝ) : tent a t ≤ 1 / (2 * a) := by
  unfold tent
  have h1 : max 0 (2 * a - |t|) ≤ 2 * a := by
    refine max_le (by positivity) ?_
    linarith [abs_nonneg t]
  calc
    max 0 (2 * a - |t|) / (4 * a ^ 2) ≤ (2 * a) / (4 * a ^ 2) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    _ = 1 / (2 * a) := by field_simp [ha.ne']; norm_num

lemma tent_eq_zero_of_abs_ge {a t : ℝ} (h : 2 * a ≤ |t|) : tent a t = 0 := by
  unfold tent
  rw [max_eq_left (by linarith), zero_div]

lemma tent_even (a t : ℝ) : tent a (-t) = tent a t := by
  simp [tent]

lemma continuous_tent (a : ℝ) : Continuous (tent a) := by
  unfold tent
  fun_prop

lemma integrable_tent {a : ℝ} (ha : 0 < a) : Integrable (tent a) := by
  have hle : ∀ t : ℝ, ‖tent a t‖ ≤ (Set.Icc (-2 * a) (2 * a)).indicator (fun _ => 1 / (2 * a)) t := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg ha t)]
    by_cases ht : |t| ≤ 2 * a
    · have hmem : t ∈ Set.Icc (-2 * a) (2 * a) := by
        rw [Set.mem_Icc]
        have := abs_le.mp ht
        constructor <;> linarith
      rw [Set.indicator_of_mem hmem]
      exact tent_le ha t
    · push Not at ht
      rw [tent_eq_zero_of_abs_ge ht.le]
      exact Set.indicator_nonneg (fun _ _ => by positivity) t
  have hbox : Integrable ((Set.Icc (-2 * a) (2 * a)).indicator (fun _ => 1 / (2 * a))) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    refine integrableOn_const ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact hbox.mono' (continuous_tent a).aestronglyMeasurable (Filter.Eventually.of_forall hle)

lemma integral_tent {a : ℝ} (ha : 0 < a) : ∫ t : ℝ, tent a t = 1 := by
  have heq : (fun t : ℝ => tent a t) = (Set.Icc (-2 * a) (2 * a)).indicator (tent a) := by
    funext t
    by_cases ht : |t| ≤ 2 * a
    · have hmem : t ∈ Set.Icc (-2 * a) (2 * a) := by
        rw [Set.mem_Icc]; have := abs_le.mp ht; constructor <;> linarith
      rw [Set.indicator_of_mem hmem]
    · push Not at ht
      have hnot : t ∉ Set.Icc (-2 * a) (2 * a) := by
        rw [Set.mem_Icc]; intro h; exact ht.not_ge (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [Set.indicator_of_notMem hnot, tent_eq_zero_of_abs_ge ht.le]
  rw [heq, integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals
    ((continuous_tent a).intervalIntegrable (μ := volume) (-2 * a) 0)
    ((continuous_tent a).intervalIntegrable (μ := volume) 0 (2 * a))).symm
  have hneg := intervalIntegral.integral_comp_neg (f := tent a) (a := -2 * a) (b := 0)
  simp only [neg_zero, neg_mul, neg_neg, tent_even] at hneg
  rw [show -(2 * a) = -2 * a by ring] at hneg
  rw [hsplit, hneg]
  have hon : ∫ t in (0 : ℝ)..(2 * a), tent a t =
      ∫ t in (0 : ℝ)..(2 * a), (2 * a - t) / (4 * a ^ 2) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    unfold tent
    rw [abs_of_nonneg ht.1, max_eq_right (by linarith [ht.2])]
  rw [hon]
  have hftc : ∫ t in (0 : ℝ)..(2 * a), (2 * a - t) / (4 * a ^ 2) =
      ((2 * a * (2 * a) - (2 * a) ^ 2 / 2) / (4 * a ^ 2)) -
      ((2 * a * 0 - 0 ^ 2 / 2) / (4 * a ^ 2)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => (2 * a * u - u ^ 2 / 2) / (4 * a ^ 2)) (fun t _ => ?_)
      ((by fun_prop : Continuous fun t : ℝ => (2 * a - t) / (4 * a ^ 2)).intervalIntegrable 0 (2 * a))
    have h1 : HasDerivAt (fun u : ℝ => 2 * a * u - u ^ 2 / 2) (2 * a - t) t := by
      have hA : HasDerivAt (fun u : ℝ => 2 * a * u) (2 * a) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * a)
      have hB : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
        simpa using ((hasDerivAt_pow 2 t).div_const 2)
      exact hA.sub hB
    exact h1.div_const (4 * a ^ 2)
  rw [hftc]
  field_simp [ha.ne']
  ring

/-- 1D Fourier transform of the tent mollifier `tent a`. -/
def tentHat (a ξ : ℝ) : ℂ :=
  FourierTransform.fourier (fun t : ℝ => (tent a t : ℂ)) ξ

lemma tentHat_eq_integral (a ξ : ℝ) :
    tentHat a ξ = ∫ t : ℝ, Complex.exp (-(2 * Real.pi * t * ξ : ℝ) * Complex.I) * (tent a t : ℂ) := by
  unfold tentHat
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  change (Real.fourierChar (-inner ℝ t ξ) : ℂ) * (tent a t : ℂ) = _
  rw [Real.fourierChar_apply, RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast
  ring

lemma tentHat_zero {a : ℝ} (ha : 0 < a) : tentHat a 0 = 1 := by
  rw [tentHat_eq_integral]
  simp only [mul_zero, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [integral_complex_ofReal, integral_tent ha, Complex.ofReal_one]

lemma norm_tentHat_le_one {a : ℝ} (ha : 0 < a) (ξ : ℝ) : ‖tentHat a ξ‖ ≤ 1 := by
  rw [tentHat_eq_integral]
  calc
    ‖∫ t : ℝ, Complex.exp (-(2 * Real.pi * t * ξ : ℝ) * Complex.I) * (tent a t : ℂ)‖
        ≤ ∫ t : ℝ, ‖Complex.exp (-(2 * Real.pi * t * ξ : ℝ) * Complex.I) * (tent a t : ℂ)‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, tent a t := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          dsimp only
          rw [norm_mul,
            show -(2 * Real.pi * t * ξ : ℝ) * Complex.I =
              ((-(2 * Real.pi * t * ξ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (tent_nonneg ha t)]
    _ = 1 := integral_tent ha

/-- Exact Fourier decay of the tent mollifier: for `a > 0` and `ξ ≠ 0`,
`‖tentHat a ξ‖ ≤ 1 / (2 π a ξ)²`. -/
lemma norm_tentHat_le_inv_sq {a ξ : ℝ} (ha : 0 < a) (hξ : ξ ≠ 0) :
    ‖tentHat a ξ‖ ≤ 1 / (2 * Real.pi * a * ξ) ^ 2 := by
  set ω : ℝ := 2 * Real.pi * ξ
  have hω : ω ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hξ
  rw [tentHat_eq_integral]
  -- Restrict from `ℝ` to `[-2a, 2a]`
  have hIcc :
      (∫ t : ℝ, Complex.exp (-(2 * Real.pi * t * ξ : ℝ) * Complex.I) * (tent a t : ℂ)) =
      ∫ t in (-2 * a)..(2 * a),
        Complex.exp (-(ω * t : ℝ) * Complex.I) * (tent a t : ℂ) := by
    have heq :
        (fun t : ℝ => Complex.exp (-(2 * Real.pi * t * ξ : ℝ) * Complex.I) * (tent a t : ℂ)) =
        (Set.Icc (-2 * a) (2 * a)).indicator
          (fun t => Complex.exp (-(ω * t : ℝ) * Complex.I) * (tent a t : ℂ)) := by
      funext t
      by_cases ht : |t| ≤ 2 * a
      · have hmem : t ∈ Set.Icc (-2 * a) (2 * a) := by
          rw [Set.mem_Icc]; have := abs_le.mp ht; constructor <;> linarith
        rw [Set.indicator_of_mem hmem]
        rw [show 2 * Real.pi * t * ξ = ω * t by dsimp [ω]; ring]
      · push Not at ht
        have hnot : t ∉ Set.Icc (-2 * a) (2 * a) := by
          rw [Set.mem_Icc]; intro h; exact ht.not_ge (abs_le.mpr ⟨by linarith, by linarith⟩)
        rw [Set.indicator_of_notMem hnot, tent_eq_zero_of_abs_ge ht.le, Complex.ofReal_zero,
          mul_zero]
    rw [heq, integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
  rw [hIcc]
  have hcont_c : Continuous (fun t : ℝ => tent a t * Real.cos (ω * t)) :=
    (continuous_tent a).mul (by fun_prop)
  have hcont_s : Continuous (fun t : ℝ => tent a t * Real.sin (ω * t)) :=
    (continuous_tent a).mul (by fun_prop)
  have hexp : ∀ t : ℝ,
      Complex.exp (-(ω * t : ℝ) * Complex.I) * (tent a t : ℂ) =
        ((tent a t * Real.cos (ω * t) : ℝ) : ℂ) -
        Complex.I * ((tent a t * Real.sin (ω * t) : ℝ) : ℂ) := by
    intro t
    rw [show -(ω * t : ℝ) * Complex.I = ((-(ω * t) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
      Complex.ofReal_sin, Complex.ofReal_mul]
    ring
  simp_rw [hexp]
  have hint_c : IntervalIntegrable (fun t : ℝ => ((tent a t * Real.cos (ω * t) : ℝ) : ℂ))
      volume (-2 * a) (2 * a) :=
    (Complex.continuous_ofReal.comp hcont_c).intervalIntegrable _ _
  have hint_s : IntervalIntegrable (fun t : ℝ => Complex.I * ((tent a t * Real.sin (ω * t) : ℝ) : ℂ))
      volume (-2 * a) (2 * a) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hcont_s)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hint_c hint_s, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hodd : ∫ t in (-2 * a)..(2 * a), tent a t * Real.sin (ω * t) = 0 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun t => tent a t * Real.sin (ω * t)) (a := -2 * a) (b := 2 * a)
    simp only [neg_mul, neg_neg, tent_even, mul_neg, Real.sin_neg, intervalIntegral.integral_neg]
      at hcomp
    rw [show -(2 * a) = -2 * a by ring] at hcomp
    linarith
  have heven : ∫ t in (-2 * a)..(2 * a), tent a t * Real.cos (ω * t) =
      2 * ∫ t in (0 : ℝ)..(2 * a), ((2 * a - t) * Real.cos (ω * t)) / (4 * a ^ 2) := by
    have hsp := (intervalIntegral.integral_add_adjacent_intervals
      (hcont_c.intervalIntegrable (μ := volume) (-2 * a) 0)
      (hcont_c.intervalIntegrable (μ := volume) 0 (2 * a))).symm
    have hneg := intervalIntegral.integral_comp_neg
      (f := fun t => tent a t * Real.cos (ω * t)) (a := -2 * a) (b := 0)
    simp only [neg_zero, neg_mul, neg_neg, tent_even, mul_neg, Real.cos_neg] at hneg
    rw [show -(2 * a) = -2 * a by ring] at hneg
    rw [hsp, hneg]
    have hon : ∫ t in (0 : ℝ)..(2 * a), tent a t * Real.cos (ω * t) =
        ∫ t in (0 : ℝ)..(2 * a), ((2 * a - t) * Real.cos (ω * t)) / (4 * a ^ 2) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      unfold tent
      rw [abs_of_nonneg ht.1, max_eq_right (by linarith [ht.2])]
      ring
    linarith
  -- FTC for `∫_0^{2a} ((2a - t) cos(ω t)) / (4 a²) dt`
  have hftc :
      ∫ t in (0 : ℝ)..(2 * a), ((2 * a - t) * Real.cos (ω * t)) / (4 * a ^ 2) =
        (1 - Real.cos (ω * (2 * a))) / (4 * a ^ 2 * ω ^ 2) := by
    let F : ℝ → ℝ := fun t =>
      ((2 * a - t) * Real.sin (ω * t) / ω - Real.cos (ω * t) / ω ^ 2) / (4 * a ^ 2)
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * a),
        HasDerivAt F (((2 * a - t) * Real.cos (ω * t)) / (4 * a ^ 2)) t := by
      intro t _
      have hlin : HasDerivAt (fun u : ℝ => ω * u) ω t := by
        simpa using (hasDerivAt_id t).const_mul ω
      have h1 : HasDerivAt (fun u : ℝ => 2 * a - u) (-1) t :=
        (hasDerivAt_id t).const_sub (2 * a)
      have hA : HasDerivAt (fun u : ℝ => (2 * a - u) * Real.sin (ω * u) / ω)
          (((-1) * Real.sin (ω * t) + (2 * a - t) * (Real.cos (ω * t) * ω)) / ω) t :=
        (h1.mul hlin.sin).div_const ω
      have hB : HasDerivAt (fun u : ℝ => Real.cos (ω * u) / ω ^ 2)
          ((-Real.sin (ω * t) * ω) / ω ^ 2) t :=
        hlin.cos.div_const (ω ^ 2)
      refine ((hA.sub hB).div_const (4 * a ^ 2)).congr_deriv ?_
      field_simp [hω, ha.ne']
      ring
    have hcontF' : Continuous (fun t : ℝ => ((2 * a - t) * Real.cos (ω * t)) / (4 * a ^ 2)) := by
      fun_prop
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcontF'.intervalIntegrable 0 (2 * a))
    rw [hval]
    dsimp [F]
    simp only [sub_self, zero_mul, zero_div, zero_sub, mul_zero, Real.sin_zero, Real.cos_zero]
    field_simp [hω, ha.ne']
    ring
  rw [hodd, Complex.ofReal_zero, mul_zero, sub_zero, heven, hftc, Complex.norm_real,
    Real.norm_eq_abs]
  have hcos : -1 ≤ Real.cos (ω * (2 * a)) ∧ Real.cos (ω * (2 * a)) ≤ 1 :=
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hnum_nn : 0 ≤ 2 * ((1 - Real.cos (ω * (2 * a))) / (4 * a ^ 2 * ω ^ 2)) := by
    have h1 : 0 ≤ 1 - Real.cos (ω * (2 * a)) := by linarith
    positivity
  rw [abs_of_nonneg hnum_nn]
  have hnum_le : 1 - Real.cos (ω * (2 * a)) ≤ 2 := by linarith
  calc
    2 * ((1 - Real.cos (ω * (2 * a))) / (4 * a ^ 2 * ω ^ 2))
        ≤ 2 * (2 / (4 * a ^ 2 * ω ^ 2)) := by
          gcongr
    _ = 1 / (2 * Real.pi * a * ξ) ^ 2 := by
          dsimp [ω]
          field_simp [ha.ne', hξ, Real.pi_ne_zero]
          ring

lemma norm_tentHat_le_quarter {a ξ : ℝ} (ha : 0 < a) (hξ : ξ ≠ 0) :
    ‖tentHat a ξ‖ ≤ 1 / (4 * a ^ 2 * ξ ^ 2) := by
  refine (norm_tentHat_le_inv_sq ha hξ).trans ?_
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hden1 : 0 < 4 * a ^ 2 * ξ ^ 2 := by positivity
  have hden2 : 0 < (2 * Real.pi * a * ξ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden2 hden1]
  have hfac : (2 * Real.pi * a * ξ) ^ 2 = Real.pi ^ 2 * (4 * a ^ 2 * ξ ^ 2) := by ring
  nlinarith

lemma summable_norm_tentHat {a : ℝ} (ha : 0 < a) :
    Summable (fun m : ℤ => ‖tentHat a (m : ℝ)‖) := by
  have hnat : Summable (fun n : ℕ => (1 / (4 * a ^ 2)) * ((n : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).mul_left (1 / (4 * a ^ 2))
  have hint_pos : Summable (fun n : ℕ => ‖tentHat a (n : ℝ)‖) := by
    have hmaj : Summable (fun n : ℕ =>
        if n = 0 then (1 : ℝ) else (1 / (4 * a ^ 2)) * ((n : ℝ) ^ 2)⁻¹) := by
      refine hnat.congr_cofinite ?_
      filter_upwards [(Set.finite_singleton (0 : ℕ)).compl_mem_cofinite] with n hn
      have hn0 : n ≠ 0 := hn
      simp [hn0]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hmaj
    by_cases hn : n = 0
    · subst hn; simp [norm_tentHat_le_one ha]
    · simp only [hn, ↓reduceIte]
      have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      refine (norm_tentHat_le_quarter ha hne).trans_eq ?_
      field_simp [ha.ne', hne]
  have hint_neg : Summable (fun n : ℕ => ‖tentHat a (-(n : ℤ) : ℤ)‖) := by
    have hmaj : Summable (fun n : ℕ =>
        if n = 0 then (1 : ℝ) else (1 / (4 * a ^ 2)) * ((n : ℝ) ^ 2)⁻¹) := by
      refine hnat.congr_cofinite ?_
      filter_upwards [(Set.finite_singleton (0 : ℕ)).compl_mem_cofinite] with n hn
      have hn0 : n ≠ 0 := hn
      simp [hn0]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hmaj
    by_cases hn : n = 0
    · subst hn; simp [norm_tentHat_le_one ha]
    · simp only [hn, ↓reduceIte]
      have hne : ((-(n : ℤ) : ℤ) : ℝ) ≠ 0 := by
        simp [Nat.cast_ne_zero.mpr hn]
      refine (norm_tentHat_le_quarter ha hne).trans_eq ?_
      simp only [Int.cast_neg, Int.cast_natCast, neg_sq]
      have hne' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      field_simp [ha.ne', hne']
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨hint_pos, hint_neg⟩

/-- 2D tent-mollified disk indicator:
`smoothedDisk R a x y = ∫∫ diskInd R (u, v) * tent a (x - u) * tent a (y - v) du dv`. -/
def smoothedDisk (R a x y : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, diskInd R p * tent a (x - p.1) * tent a (y - p.2)

lemma integral_tent_sub {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∫ u : ℝ, tent a (x - u) = 1 := by
  rw [MeasureTheory.integral_sub_left_eq_self (tent a) volume x, integral_tent ha]

lemma integral_prod_tent_sub {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    ∫ p : ℝ × ℝ, tent a (x - p.1) * tent a (y - p.2) = 1 := by
  rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (fun u => tent a (x - u))
    (fun v => tent a (y - v)), integral_tent_sub ha x, integral_tent_sub ha y, mul_one]

lemma integrable_prod_tent_sub {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    Integrable (fun p : ℝ × ℝ => tent a (x - p.1) * tent a (y - p.2))
      (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  have h1 : Integrable (fun u : ℝ => tent a (x - u)) volume :=
    (integrable_tent ha).comp_sub_left x
  have h2 : Integrable (fun v : ℝ => tent a (y - v)) volume :=
    (integrable_tent ha).comp_sub_left y
  exact h1.mul_prod h2

lemma smoothedDisk_nonneg {R a : ℝ} (ha : 0 < a) (x y : ℝ) :
    0 ≤ smoothedDisk R a x y := by
  unfold smoothedDisk
  refine integral_nonneg fun p => ?_
  exact mul_nonneg (mul_nonneg (diskInd_nonneg R p) (tent_nonneg ha _)) (tent_nonneg ha _)

lemma smoothedDisk_le_one {R a : ℝ} (ha : 0 < a) (x y : ℝ) :
    smoothedDisk R a x y ≤ 1 := by
  unfold smoothedDisk
  have hint : Integrable (fun p : ℝ × ℝ => diskInd R p * tent a (x - p.1) * tent a (y - p.2))
      (volume : Measure (ℝ × ℝ)) := by
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => diskInd R p * tent a (x - p.1) * tent a (y - p.2)) volume := by
      refine Measurable.aestronglyMeasurable ?_
      exact ((measurable_diskInd R).mul
        ((continuous_tent a).measurable.comp (measurable_const.sub measurable_fst))).mul
        ((continuous_tent a).measurable.comp (measurable_const.sub measurable_snd))
    refine (integrable_prod_tent_sub ha x y).mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (diskInd_nonneg R p) (tent_nonneg ha _)) (tent_nonneg ha _))]
    have h1 := diskInd_le_one R p
    have h2 : 0 ≤ tent a (x - p.1) * tent a (y - p.2) :=
      mul_nonneg (tent_nonneg ha _) (tent_nonneg ha _)
    nlinarith
  calc
    ∫ p : ℝ × ℝ, diskInd R p * tent a (x - p.1) * tent a (y - p.2)
        ≤ ∫ p : ℝ × ℝ, tent a (x - p.1) * tent a (y - p.2) := by
          refine integral_mono hint (integrable_prod_tent_sub ha x y) fun p => ?_
          have h1 := diskInd_le_one R p
          have h2 : 0 ≤ tent a (x - p.1) * tent a (y - p.2) :=
            mul_nonneg (tent_nonneg ha _) (tent_nonneg ha _)
          nlinarith
    _ = 1 := integral_prod_tent_sub ha x y

lemma smoothedDisk_eq_zero_of_abs_x_gt {R a x y : ℝ} (hR : 0 ≤ R) (hx : R + 2 * a < |x|) :
    smoothedDisk R a x y = 0 := by
  unfold smoothedDisk
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only [Pi.zero_apply]
  by_cases hp : p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2
  · have hp1 : |p.1| ≤ R := by
      have hsq : |p.1| ^ 2 ≤ R ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg p.2]
      exact (sq_le_sq₀ (abs_nonneg _) hR).mp hsq
    have hdiff : 2 * a ≤ |x - p.1| := by
      have htri : |x| ≤ |x - p.1| + |p.1| := by
        simpa [sub_add_cancel] using abs_add_le (x - p.1) p.1
      linarith
    rw [tent_eq_zero_of_abs_ge hdiff, mul_zero, zero_mul]
  · simp [diskInd, hp]

lemma smoothedDisk_eq_zero_of_abs_y_gt {R a x y : ℝ} (hR : 0 ≤ R) (hy : R + 2 * a < |y|) :
    smoothedDisk R a x y = 0 := by
  unfold smoothedDisk
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only [Pi.zero_apply]
  by_cases hp : p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2
  · have hp2 : |p.2| ≤ R := by
      have hsq : |p.2| ^ 2 ≤ R ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg p.1]
      exact (sq_le_sq₀ (abs_nonneg _) hR).mp hsq
    have hdiff : 2 * a ≤ |y - p.2| := by
      have htri : |y| ≤ |y - p.2| + |p.2| := by
        simpa [sub_add_cancel] using abs_add_le (y - p.2) p.2
      linarith
    rw [tent_eq_zero_of_abs_ge hdiff, mul_zero]
  · simp [diskInd, hp]

/-- **Exact Upper Sandwich** (ZERO tail error!):
for all `R ≥ 0`, `a > 0`, and `(x, y) ∈ ℝ²`,
`diskInd R (x, y) ≤ smoothedDisk (R + 2 √2 a) a x y`. -/
theorem diskInd_le_smoothedDisk {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (x y : ℝ) :
    diskInd R (x, y) ≤ smoothedDisk (R + 2 * Real.sqrt 2 * a) a x y := by
  by_cases hxy : x ^ 2 + y ^ 2 ≤ R ^ 2
  · have hind1 : diskInd R (x, y) = 1 := by simp [diskInd, hxy]
    rw [hind1]
    have hEq1 : smoothedDisk (R + 2 * Real.sqrt 2 * a) a x y = 1 := by
      unfold smoothedDisk
      rw [← integral_prod_tent_sub ha x y]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      by_cases hdx : 2 * a ≤ |x - p.1|
      · simp [tent_eq_zero_of_abs_ge hdx]
      · by_cases hdy : 2 * a ≤ |y - p.2|
        · simp [tent_eq_zero_of_abs_ge hdy]
        · push Not at hdx hdy
          have hd_sq : (x - p.1) ^ 2 + (y - p.2) ^ 2 ≤ (2 * Real.sqrt 2 * a) ^ 2 := by
            have h1 : (x - p.1) ^ 2 ≤ (2 * a) ^ 2 := by
              rw [← sq_abs (x - p.1)]
              exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdx.le
            have h2 : (y - p.2) ^ 2 ≤ (2 * a) ^ 2 := by
              rw [← sq_abs (y - p.2)]
              exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdy.le
            have hsq2 : (2 * Real.sqrt 2 * a) ^ 2 = 8 * a ^ 2 := by
              calc
                (2 * Real.sqrt 2 * a) ^ 2 = 4 * Real.sqrt 2 ^ 2 * a ^ 2 := by ring
                _ = 4 * 2 * a ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
                _ = 8 * a ^ 2 := by ring
            nlinarith
          have hp_in : p.1 ^ 2 + p.2 ^ 2 ≤ (R + 2 * Real.sqrt 2 * a) ^ 2 := by
            have hnorm_p : ‖prodToE2 p‖ ≤ R + 2 * Real.sqrt 2 * a := by
              have hxy_norm : ‖prodToE2 (x, y)‖ ≤ R := by
                have hsq : ‖prodToE2 (x, y)‖ ^ 2 ≤ R ^ 2 := by
                  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
                  simpa [prodToE2, Real.norm_eq_abs, sq_abs] using hxy
                exact (sq_le_sq₀ (norm_nonneg _) hR).mp hsq
              have hdiff_norm : ‖prodToE2 (x, y) - prodToE2 p‖ ≤ 2 * Real.sqrt 2 * a := by
                have hsq : ‖prodToE2 (x, y) - prodToE2 p‖ ^ 2 ≤ (2 * Real.sqrt 2 * a) ^ 2 := by
                  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
                  simpa [prodToE2, Real.norm_eq_abs, sq_abs] using hd_sq
                exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
              calc
                ‖prodToE2 p‖ = ‖prodToE2 (x, y) - (prodToE2 (x, y) - prodToE2 p)‖ := by abel_nf
                _ ≤ ‖prodToE2 (x, y)‖ + ‖prodToE2 (x, y) - prodToE2 p‖ := norm_sub_le _ _
                _ ≤ R + 2 * Real.sqrt 2 * a := add_le_add hxy_norm hdiff_norm
            have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm_p
            rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two] at hsq
            simpa [prodToE2, Real.norm_eq_abs, sq_abs] using hsq
          simp [diskInd, hp_in]
    linarith
  · have hind0 : diskInd R (x, y) = 0 := by simp [diskInd, hxy]
    rw [hind0]
    exact smoothedDisk_nonneg ha x y

/-- **Exact Lower Sandwich** (ZERO tail error!):
for all `a > 0`, `2 √2 a ≤ R`, and `(x, y) ∈ ℝ²`,
`smoothedDisk (R - 2 √2 a) a x y ≤ diskInd R (x, y)`. -/
theorem smoothedDisk_le_diskInd {R a : ℝ} (ha : 0 < a) (hRa : 2 * Real.sqrt 2 * a ≤ R)
    (x y : ℝ) :
    smoothedDisk (R - 2 * Real.sqrt 2 * a) a x y ≤ diskInd R (x, y) := by
  by_cases hxy : x ^ 2 + y ^ 2 ≤ R ^ 2
  · have hind1 : diskInd R (x, y) = 1 := by simp [diskInd, hxy]
    rw [hind1]
    exact smoothedDisk_le_one ha x y
  · have hind0 : diskInd R (x, y) = 0 := by simp [diskInd, hxy]
    rw [hind0]
    have hEq0 : smoothedDisk (R - 2 * Real.sqrt 2 * a) a x y = 0 := by
      unfold smoothedDisk
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun p => ?_)
      by_cases hdx : 2 * a ≤ |x - p.1|
      · simp [tent_eq_zero_of_abs_ge hdx]
      · by_cases hdy : 2 * a ≤ |y - p.2|
        · simp [tent_eq_zero_of_abs_ge hdy]
        · push Not at hdx hdy hxy
          have hd_sq : (x - p.1) ^ 2 + (y - p.2) ^ 2 < (2 * Real.sqrt 2 * a) ^ 2 := by
            have h1 : (x - p.1) ^ 2 < (2 * a) ^ 2 := by
              rw [← sq_abs (x - p.1)]
              exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr hdx
            have h2 : (y - p.2) ^ 2 < (2 * a) ^ 2 := by
              rw [← sq_abs (y - p.2)]
              exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr hdy
            have hsq2 : (2 * Real.sqrt 2 * a) ^ 2 = 8 * a ^ 2 := by
              calc
                (2 * Real.sqrt 2 * a) ^ 2 = 4 * Real.sqrt 2 ^ 2 * a ^ 2 := by ring
                _ = 4 * 2 * a ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
                _ = 8 * a ^ 2 := by ring
            nlinarith
          have hp_out : ¬ (p.1 ^ 2 + p.2 ^ 2 ≤ (R - 2 * Real.sqrt 2 * a) ^ 2) := by
            intro hp_in
            have hR0 : 0 ≤ R := (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 2 * a).trans hRa
            have hp_norm : ‖prodToE2 p‖ ≤ R - 2 * Real.sqrt 2 * a := by
              have hsq : ‖prodToE2 p‖ ^ 2 ≤ (R - 2 * Real.sqrt 2 * a) ^ 2 := by
                rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
                simpa [prodToE2, Real.norm_eq_abs, sq_abs] using hp_in
              exact (sq_le_sq₀ (norm_nonneg _) (by linarith)).mp hsq
            have hdiff_norm : ‖prodToE2 (x, y) - prodToE2 p‖ < 2 * Real.sqrt 2 * a := by
              have hsq : ‖prodToE2 (x, y) - prodToE2 p‖ ^ 2 < (2 * Real.sqrt 2 * a) ^ 2 := by
                rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
                simpa [prodToE2, Real.norm_eq_abs, sq_abs] using hd_sq
              exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp hsq
            have hxy_norm : ‖prodToE2 (x, y)‖ < R := by
              calc
                ‖prodToE2 (x, y)‖ = ‖(prodToE2 (x, y) - prodToE2 p) + prodToE2 p‖ := by abel_nf
                _ ≤ ‖prodToE2 (x, y) - prodToE2 p‖ + ‖prodToE2 p‖ := norm_add_le _ _
                _ < 2 * Real.sqrt 2 * a + (R - 2 * Real.sqrt 2 * a) :=
                    add_lt_add_of_lt_of_le hdiff_norm hp_norm
                _ = R := by ring
            have hsq := (sq_lt_sq₀ (norm_nonneg _) hR0).mpr hxy_norm
            rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two] at hsq
            have : x ^ 2 + y ^ 2 < R ^ 2 := by
              simpa [prodToE2, Real.norm_eq_abs, sq_abs] using hsq
            linarith
          simp [diskInd, hp_out]
    linarith

/-- Partial `x`-Fourier transform of `smoothedDisk R a`:
`xFourierDisk R a ξ₁ y = tentHat a ξ₁ * ∫∫ e^{-2π i ξ₁ u} diskInd R (u, v) tent a (y - v) du dv`. -/
def xFourierDisk (R a ξ₁ y : ℝ) : ℂ :=
  tentHat a ξ₁ *
    ∫ p : ℝ × ℝ,
      Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
        (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)

lemma xFourierDisk_eq_zero_of_abs_gt {R a ξ₁ y : ℝ} (hR : 0 ≤ R) (hy : R + 2 * a < |y|) :
    xFourierDisk R a ξ₁ y = 0 := by
  unfold xFourierDisk
  have hz :
      (∫ p : ℝ × ℝ,
        Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
          (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)) = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only [Pi.zero_apply]
    by_cases hp : p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2
    · have hp2 : |p.2| ≤ R := by
        have hsq : |p.2| ^ 2 ≤ R ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg p.1]
        exact (sq_le_sq₀ (abs_nonneg _) hR).mp hsq
      have hdiff : 2 * a ≤ |y - p.2| := by
        have htri : |y| ≤ |y - p.2| + |p.2| := by
          simpa [sub_add_cancel] using abs_add_le (y - p.2) p.2
        linarith
      rw [tent_eq_zero_of_abs_ge hdiff, Complex.ofReal_zero, mul_zero]
    · simp [diskInd, hp]
  rw [hz, mul_zero]

lemma continuous_smoothedDisk_x {R a : ℝ} (ha : 0 < a) (y : ℝ) :
    Continuous (fun x : ℝ => (smoothedDisk R a x y : ℂ)) := by
  refine Complex.continuous_ofReal.comp ?_
  unfold smoothedDisk
  refine MeasureTheory.continuous_of_dominated
    (bound := fun p : ℝ × ℝ => (1 / (2 * a)) ^ 2 * diskInd R p) ?_ ?_ ?_ ?_
  · intro x
    refine Measurable.aestronglyMeasurable ?_
    exact ((measurable_diskInd R).mul
      ((continuous_tent a).measurable.comp (measurable_const.sub measurable_fst))).mul
      ((continuous_tent a).measurable.comp (measurable_const.sub measurable_snd))
  · intro x
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (diskInd_nonneg R p) (tent_nonneg ha _)) (tent_nonneg ha _))]
    have ht1 : tent a (x - p.1) ≤ 1 / (2 * a) := tent_le ha _
    have ht2 : tent a (y - p.2) ≤ 1 / (2 * a) := tent_le ha _
    have hnn1 : 0 ≤ tent a (x - p.1) := tent_nonneg ha _
    have hnn2 : 0 ≤ tent a (y - p.2) := tent_nonneg ha _
    have hd : 0 ≤ diskInd R p := diskInd_nonneg R p
    calc
      diskInd R p * tent a (x - p.1) * tent a (y - p.2)
          ≤ diskInd R p * (1 / (2 * a)) * (1 / (2 * a)) := by gcongr
      _ = (1 / (2 * a)) ^ 2 * diskInd R p := by ring
  · exact (integrable_diskInd R).const_mul ((1 / (2 * a)) ^ 2)
  · refine Filter.Eventually.of_forall fun p => ?_
    exact (continuous_const.mul ((continuous_tent a).comp (continuous_id.sub continuous_const))).mul
      continuous_const

lemma continuous_xFourierDisk_y {R a : ℝ} (ha : 0 < a) (ξ₁ : ℝ) :
    Continuous (fun y : ℝ => xFourierDisk R a ξ₁ y) := by
  unfold xFourierDisk
  refine continuous_const.mul ?_
  refine MeasureTheory.continuous_of_dominated
    (bound := fun p : ℝ × ℝ => (1 / (2 * a)) * diskInd R p) ?_ ?_ ?_ ?_
  · intro y
    refine Measurable.aestronglyMeasurable ?_
    refine (Measurable.mul ?_ (Complex.continuous_ofReal.measurable.comp (measurable_diskInd R))).mul
      (Complex.continuous_ofReal.measurable.comp
        ((continuous_tent a).measurable.comp (measurable_const.sub measurable_snd)))
    fun_prop
  · intro y
    refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul, norm_mul,
      show -(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I =
        ((-(2 * Real.pi * (ξ₁ * p.1)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (diskInd_nonneg R p),
      abs_of_nonneg (tent_nonneg ha _)]
    have ht := tent_le ha (y - p.2)
    have hd := diskInd_nonneg R p
    nlinarith
  · exact (integrable_diskInd R).const_mul (1 / (2 * a))
  · refine Filter.Eventually.of_forall fun p => ?_
    exact continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_tent a).comp (continuous_id.sub continuous_const)))

lemma fourier_smoothedDisk_x {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (ξ₁ y : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (smoothedDisk R a x y : ℂ)) ξ₁ =
      xFourierDisk R a ξ₁ y := by
  rw [Real.fourier_eq]
  have hchar : ∀ x : ℝ,
      Real.fourierChar (-inner ℝ x ξ₁) • (smoothedDisk R a x y : ℂ) =
      ∫ p : ℝ × ℝ,
        Complex.exp (-(2 * Real.pi * x * ξ₁ : ℝ) * Complex.I) *
          ((diskInd R p : ℂ) * (tent a (x - p.1) : ℂ) * (tent a (y - p.2) : ℂ)) := by
    intro x
    change (Real.fourierChar (-inner ℝ x ξ₁) : ℂ) * (smoothedDisk R a x y : ℂ) = _
    rw [Real.fourierChar_apply, RCLike.inner_apply, conj_trivial]
    unfold smoothedDisk
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    push_cast
    congr 2
    ring
  simp_rw [hchar]
  -- Fubini on `ℝ × (ℝ × ℝ)`
  have hint_prod : Integrable
      (Function.uncurry fun (x : ℝ) (p : ℝ × ℝ) =>
        Complex.exp (-(2 * Real.pi * x * ξ₁ : ℝ) * Complex.I) *
          ((diskInd R p : ℂ) * (tent a (x - p.1) : ℂ) * (tent a (y - p.2) : ℂ)))
      (volume.prod (volume : Measure (ℝ × ℝ))) := by
    have hmeas : AEStronglyMeasurable
        (Function.uncurry fun (x : ℝ) (p : ℝ × ℝ) =>
          Complex.exp (-(2 * Real.pi * x * ξ₁ : ℝ) * Complex.I) *
            ((diskInd R p : ℂ) * (tent a (x - p.1) : ℂ) * (tent a (y - p.2) : ℂ)))
        (volume.prod (volume : Measure (ℝ × ℝ))) := by
      refine Measurable.aestronglyMeasurable ?_
      change Measurable fun z : ℝ × (ℝ × ℝ) =>
        Complex.exp (-(2 * Real.pi * z.1 * ξ₁ : ℝ) * Complex.I) *
          ((diskInd R z.2 : ℂ) * (tent a (z.1 - z.2.1) : ℂ) * (tent a (y - z.2.2) : ℂ))
      refine Measurable.mul ?_ ?_
      · fun_prop
      · refine (Measurable.mul ?_ ?_).mul ?_
        · exact Complex.continuous_ofReal.measurable.comp ((measurable_diskInd R).comp measurable_snd)
        · exact Complex.continuous_ofReal.measurable.comp
            ((continuous_tent a).measurable.comp (measurable_fst.sub (measurable_fst.comp measurable_snd)))
        · exact Complex.continuous_ofReal.measurable.comp
            ((continuous_tent a).measurable.comp (measurable_const.sub (measurable_snd.comp measurable_snd)))
    let bound : ℝ × (ℝ × ℝ) → ℝ := fun z =>
      (Set.Icc (-(R + 2 * a)) (R + 2 * a)).indicator (fun _ => 1 / (2 * a)) z.1 *
        ((1 / (2 * a)) * diskInd R z.2)
    have hbound_int : Integrable bound (volume.prod (volume : Measure (ℝ × ℝ))) := by
      have h1 : Integrable ((Set.Icc (-(R + 2 * a)) (R + 2 * a)).indicator (fun _ => 1 / (2 * a)))
          volume := by
        rw [integrable_indicator_iff measurableSet_Icc]
        exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      have h2 : Integrable (fun p : ℝ × ℝ => (1 / (2 * a)) * diskInd R p) volume :=
        (integrable_diskInd R).const_mul (1 / (2 * a))
      exact h1.mul_prod h2
    refine hbound_int.mono' hmeas (Filter.Eventually.of_forall fun z => ?_)
    dsimp only [Function.uncurry, bound]
    rw [norm_mul,
      show -(2 * Real.pi * z.1 * ξ₁ : ℝ) * Complex.I =
        ((-(2 * Real.pi * z.1 * ξ₁) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (diskInd_nonneg R z.2), abs_of_nonneg (tent_nonneg ha _),
      abs_of_nonneg (tent_nonneg ha _)]
    by_cases hz2 : z.2.1 ^ 2 + z.2.2 ^ 2 ≤ R ^ 2
    · by_cases hdx : 2 * a ≤ |z.1 - z.2.1|
      · rw [tent_eq_zero_of_abs_ge hdx, mul_zero, zero_mul]
        exact mul_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _)
          (mul_nonneg (by positivity) (diskInd_nonneg R z.2))
      · push Not at hdx
        have hz21 : |z.2.1| ≤ R := by
          have hsq : |z.2.1| ^ 2 ≤ R ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg z.2.2]
          exact (sq_le_sq₀ (abs_nonneg _) hR).mp hsq
        have hz1 : |z.1| ≤ R + 2 * a := by
          have htri : |z.1| ≤ |z.1 - z.2.1| + |z.2.1| := by
            simpa [sub_add_cancel] using abs_add_le (z.1 - z.2.1) z.2.1
          linarith
        have hmem : z.1 ∈ Set.Icc (-(R + 2 * a)) (R + 2 * a) := Set.mem_Icc.mpr (abs_le.mp hz1)
        rw [Set.indicator_of_mem hmem]
        have ht1 := tent_le ha (z.1 - z.2.1)
        have ht2 := tent_le ha (y - z.2.2)
        have hnn1 := tent_nonneg ha (z.1 - z.2.1)
        have hnn2 := tent_nonneg ha (y - z.2.2)
        have hd := diskInd_nonneg R z.2
        calc
          diskInd R z.2 * tent a (z.1 - z.2.1) * tent a (y - z.2.2)
              ≤ diskInd R z.2 * (1 / (2 * a)) * (1 / (2 * a)) := by gcongr
          _ = 1 / (2 * a) * (1 / (2 * a) * diskInd R z.2) := by ring
    · simp only [diskInd, hz2, ↓reduceIte, zero_mul, mul_zero, le_refl]
  rw [MeasureTheory.integral_integral_swap hint_prod]
  -- Evaluate inner `x`-integral by translation `x = u + p.1`
  unfold xFourierDisk
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have hinner :
      (∫ x : ℝ, Complex.exp (-(2 * Real.pi * x * ξ₁ : ℝ) * Complex.I) *
        ((diskInd R p : ℂ) * (tent a (x - p.1) : ℂ) * (tent a (y - p.2) : ℂ))) =
      tentHat a ξ₁ * (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
        (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)) := by
    rw [← MeasureTheory.integral_add_right_eq_self _ p.1]
    have hrew : ∀ u : ℝ,
        Complex.exp (-(2 * Real.pi * (u + p.1) * ξ₁ : ℝ) * Complex.I) *
          ((diskInd R p : ℂ) * (tent a (u + p.1 - p.1) : ℂ) * (tent a (y - p.2) : ℂ)) =
        (Complex.exp (-(2 * Real.pi * u * ξ₁ : ℝ) * Complex.I) * (tent a u : ℂ)) *
          (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
            (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)) := by
      intro u
      rw [add_sub_cancel_right]
      have hexp :
          Complex.exp (-(2 * Real.pi * (u + p.1) * ξ₁ : ℝ) * Complex.I) =
          Complex.exp (-(2 * Real.pi * u * ξ₁ : ℝ) * Complex.I) *
            Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1; push_cast; ring
      rw [hexp]; ring
    simp_rw [hrew]
    rw [integral_mul_const, tentHat_eq_integral]
  exact hinner

lemma fourier_xFourierDisk_y {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (ξ₁ ξ₂ : ℝ) :
    FourierTransform.fourier (fun y : ℝ => xFourierDisk R a ξ₁ y) ξ₂ =
      tentHat a ξ₁ * tentHat a ξ₂ * diskFourier R ξ₁ ξ₂ := by
  rw [Real.fourier_eq]
  have hchar : ∀ y : ℝ,
      Real.fourierChar (-inner ℝ y ξ₂) • xFourierDisk R a ξ₁ y =
      tentHat a ξ₁ *
        ∫ p : ℝ × ℝ,
          Complex.exp (-(2 * Real.pi * y * ξ₂ : ℝ) * Complex.I) *
            (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
              (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)) := by
    intro y
    change (Real.fourierChar (-inner ℝ y ξ₂) : ℂ) * xFourierDisk R a ξ₁ y = _
    rw [Real.fourierChar_apply, RCLike.inner_apply, conj_trivial]
    unfold xFourierDisk
    rw [show Complex.exp (((2 * Real.pi * -(ξ₂ * y) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-(2 * Real.pi * y * ξ₂ : ℝ) * Complex.I) by
          congr 1; push_cast; ring]
    rw [← mul_assoc, mul_comm (Complex.exp _) (tentHat a ξ₁), mul_assoc, ← integral_const_mul]
  simp_rw [hchar]
  rw [integral_const_mul]
  -- Fubini on `ℝ × (ℝ × ℝ)`
  have hint_prod : Integrable
      (Function.uncurry fun (y : ℝ) (p : ℝ × ℝ) =>
        Complex.exp (-(2 * Real.pi * y * ξ₂ : ℝ) * Complex.I) *
          (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
            (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)))
      (volume.prod (volume : Measure (ℝ × ℝ))) := by
    have hmeas : AEStronglyMeasurable
        (Function.uncurry fun (y : ℝ) (p : ℝ × ℝ) =>
          Complex.exp (-(2 * Real.pi * y * ξ₂ : ℝ) * Complex.I) *
            (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
              (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)))
        (volume.prod (volume : Measure (ℝ × ℝ))) := by
      refine Measurable.aestronglyMeasurable ?_
      change Measurable fun z : ℝ × (ℝ × ℝ) =>
        Complex.exp (-(2 * Real.pi * z.1 * ξ₂ : ℝ) * Complex.I) *
          (Complex.exp (-(2 * Real.pi * (ξ₁ * z.2.1) : ℝ) * Complex.I) *
            (diskInd R z.2 : ℂ) * (tent a (z.1 - z.2.2) : ℂ))
      refine Measurable.mul ?_ ?_
      · fun_prop
      · refine (Measurable.mul ?_ ?_).mul ?_
        · fun_prop
        · exact Complex.continuous_ofReal.measurable.comp ((measurable_diskInd R).comp measurable_snd)
        · exact Complex.continuous_ofReal.measurable.comp
            ((continuous_tent a).measurable.comp (measurable_fst.sub (measurable_snd.comp measurable_snd)))
    let bound : ℝ × (ℝ × ℝ) → ℝ := fun z =>
      (Set.Icc (-(R + 2 * a)) (R + 2 * a)).indicator (fun _ => 1 / (2 * a)) z.1 * diskInd R z.2
    have hbound_int : Integrable bound (volume.prod (volume : Measure (ℝ × ℝ))) := by
      have h1 : Integrable ((Set.Icc (-(R + 2 * a)) (R + 2 * a)).indicator (fun _ => 1 / (2 * a)))
          volume := by
        rw [integrable_indicator_iff measurableSet_Icc]
        exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      exact h1.mul_prod (integrable_diskInd R)
    refine hbound_int.mono' hmeas (Filter.Eventually.of_forall fun z => ?_)
    dsimp only [Function.uncurry, bound]
    rw [norm_mul, norm_mul, norm_mul,
      show -(2 * Real.pi * z.1 * ξ₂ : ℝ) * Complex.I =
        ((-(2 * Real.pi * z.1 * ξ₂) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      show -(2 * Real.pi * (ξ₁ * z.2.1) : ℝ) * Complex.I =
        ((-(2 * Real.pi * (ξ₁ * z.2.1)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, one_mul, one_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (diskInd_nonneg R z.2), abs_of_nonneg (tent_nonneg ha _)]
    by_cases hz2 : z.2.1 ^ 2 + z.2.2 ^ 2 ≤ R ^ 2
    · by_cases hdy : 2 * a ≤ |z.1 - z.2.2|
      · rw [tent_eq_zero_of_abs_ge hdy, mul_zero]
        exact mul_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _) (diskInd_nonneg R z.2)
      · push Not at hdy
        have hz22 : |z.2.2| ≤ R := by
          have hsq : |z.2.2| ^ 2 ≤ R ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg z.2.1]
          exact (sq_le_sq₀ (abs_nonneg _) hR).mp hsq
        have hz1 : |z.1| ≤ R + 2 * a := by
          have htri : |z.1| ≤ |z.1 - z.2.2| + |z.2.2| := by
            simpa [sub_add_cancel] using abs_add_le (z.1 - z.2.2) z.2.2
          linarith
        have hmem : z.1 ∈ Set.Icc (-(R + 2 * a)) (R + 2 * a) := Set.mem_Icc.mpr (abs_le.mp hz1)
        rw [Set.indicator_of_mem hmem]
        have ht := tent_le ha (z.1 - z.2.2)
        have hd := diskInd_nonneg R z.2
        nlinarith
    · simp only [diskInd, hz2, ↓reduceIte, zero_mul, mul_zero, le_refl]
  rw [MeasureTheory.integral_integral_swap hint_prod, mul_assoc]
  congr 1
  unfold diskFourier
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  rw [← MeasureTheory.integral_add_right_eq_self _ p.2]
  have hrew : ∀ v : ℝ,
      Complex.exp (-(2 * Real.pi * (v + p.2) * ξ₂ : ℝ) * Complex.I) *
        (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
          (diskInd R p : ℂ) * (tent a (v + p.2 - p.2) : ℂ)) =
      (Complex.exp (-(2 * Real.pi * v * ξ₂ : ℝ) * Complex.I) * (tent a v : ℂ)) *
        (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2) : ℝ) * Complex.I) *
          (diskInd R p : ℂ)) := by
    intro v
    rw [add_sub_cancel_right]
    have hexp :
        Complex.exp (-(2 * Real.pi * (v + p.2) * ξ₂ : ℝ) * Complex.I) *
          Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) =
        Complex.exp (-(2 * Real.pi * v * ξ₂ : ℝ) * Complex.I) *
          Complex.exp (-(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2) : ℝ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    calc
      Complex.exp (-(2 * Real.pi * (v + p.2) * ξ₂ : ℝ) * Complex.I) *
          (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I) *
            (diskInd R p : ℂ) * (tent a v : ℂ))
          = (Complex.exp (-(2 * Real.pi * (v + p.2) * ξ₂ : ℝ) * Complex.I) *
              Complex.exp (-(2 * Real.pi * (ξ₁ * p.1) : ℝ) * Complex.I)) *
              ((diskInd R p : ℂ) * (tent a v : ℂ)) := by ring
      _ = (Complex.exp (-(2 * Real.pi * v * ξ₂ : ℝ) * Complex.I) *
            Complex.exp (-(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2) : ℝ) * Complex.I)) *
            ((diskInd R p : ℂ) * (tent a v : ℂ)) := by rw [hexp]
      _ = (Complex.exp (-(2 * Real.pi * v * ξ₂ : ℝ) * Complex.I) * (tent a v : ℂ)) *
            (Complex.exp (-(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2) : ℝ) * Complex.I) *
              (diskInd R p : ℂ)) := by ring
  simp_rw [hrew]
  rw [integral_mul_const, tentHat_eq_integral]

/-- 1D Poisson summation specialized to compactly supported continuous functions `f : ℝ → ℂ`. -/
lemma poisson_summation_compact_support {f : ℝ → ℂ} {B : ℝ}
    (hcont : Continuous f) (hsupp : ∀ x : ℝ, B < |x| → f x = 0)
    (hsum : Summable (fun m : ℤ => FourierTransform.fourier f (m : ℝ))) :
    ∑' n : ℤ, f (n : ℝ) = ∑' m : ℤ, FourierTransform.fourier f (m : ℝ) := by
  have hdecay : f =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    have hmem : {x : ℝ | B < |x|} ∈ Filter.cocompact ℝ := by
      rw [Filter.mem_cocompact]
      refine ⟨Set.Icc (-B) B, isCompact_Icc, fun x hx => ?_⟩
      change B < |x|
      by_contra hle
      push Not at hle
      exact hx (Set.mem_Icc.mpr (abs_le.mp hle))
    filter_upwards [hmem] with x hx
    rw [hsupp x hx, norm_zero, one_mul]
    exact norm_nonneg _
  have h0 := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont (b := 2) (by norm_num)
    hdecay hsum 0
  simpa only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] using h0

lemma norm_diskFourier_trivial {R : ℝ} (hR : 0 ≤ R) (ξ₁ ξ₂ : ℝ) :
    ‖diskFourier R ξ₁ ξ₂‖ ≤ Real.pi * R ^ 2 := by
  unfold diskFourier
  calc
    ‖∫ p : ℝ × ℝ, Complex.exp (-(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2) : ℝ) * Complex.I) *
        (diskInd R p : ℂ)‖
        ≤ ∫ p : ℝ × ℝ, ‖Complex.exp (-(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2) : ℝ) * Complex.I) *
            (diskInd R p : ℂ)‖ := norm_integral_le_integral_norm _
    _ = ∫ p : ℝ × ℝ, diskInd R p := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          dsimp only
          rw [norm_mul,
            show -(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2) : ℝ) * Complex.I =
              ((-(2 * Real.pi * (ξ₁ * p.1 + ξ₂ * p.2)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (diskInd_nonneg R p)]
    _ = Real.pi * R ^ 2 := integral_diskInd hR

lemma summable_dual_fourier {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    Summable (fun m : ℤ × ℤ => tentHat a m.1 * tentHat a m.2 * diskFourier R m.1 m.2) := by
  have hprod : Summable (fun m : ℤ × ℤ =>
      (Real.pi * R ^ 2) * (‖tentHat a m.1‖ * ‖tentHat a m.2‖)) :=
    ((summable_norm_tentHat ha).mul_of_nonneg (summable_norm_tentHat ha)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left (Real.pi * R ^ 2)
  refine Summable.of_norm_bounded hprod fun m => ?_
  rw [norm_mul, norm_mul]
  have h1 := norm_diskFourier_trivial hR m.1 m.2
  have hnn : 0 ≤ ‖tentHat a m.1‖ * ‖tentHat a m.2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- **Exact Unconditional 2D Poisson Summation Identity for the Tent-Smoothed Disk**:
for every `R ≥ 0` and `a > 0`,
`∑' n : ℤ × ℤ, smoothedDisk R a n.1 n.2 = ∑' m : ℤ × ℤ, tentHat a m.1 * tentHat a m.2 * diskFourier R m.1 m.2`. -/
theorem poisson_summation_smoothedDisk {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    (∑' n : ℤ × ℤ, (smoothedDisk R a n.1 n.2 : ℂ)) =
      ∑' m : ℤ × ℤ, tentHat a m.1 * tentHat a m.2 * diskFourier R m.1 m.2 := by
  set M : ℤ := ⌈R + 2 * a⌉ + 1
  let S : Finset ℤ := Finset.Icc (-M) M
  have hM_gt : R + 2 * a < (M : ℝ) := by
    have : R + 2 * a ≤ (⌈R + 2 * a⌉ : ℝ) := Int.le_ceil _
    dsimp [M]; push_cast; linarith
  have hsupp_S : ∀ k : ℤ, k ∉ S → R + 2 * a < |(k : ℝ)| := by
    intro k hk
    simp only [S, Finset.mem_Icc, not_and_or, not_le] at hk
    rcases hk with hlt | hgt
    · have : (k : ℝ) < -(M : ℝ) := by exact_mod_cast hlt
      have : (M : ℝ) < |(k : ℝ)| := by rw [lt_abs]; right; linarith
      linarith
    · have : (M : ℝ) < (k : ℝ) := by exact_mod_cast hgt
      have : (M : ℝ) < |(k : ℝ)| := by rw [lt_abs]; left; linarith
      linarith
  -- Spatial sum is finite on `S ×ˢ S`
  have hspatial_eq :
      (∑' n : ℤ × ℤ, (smoothedDisk R a n.1 n.2 : ℂ)) =
      ∑ n₂ ∈ S, ∑' n₁ : ℤ, (smoothedDisk R a n₁ n₂ : ℂ) := by
    have hfin : (∑' n : ℤ × ℤ, (smoothedDisk R a n.1 n.2 : ℂ)) =
        ∑ n ∈ S ×ˢ S, (smoothedDisk R a n.1 n.2 : ℂ) := by
      refine tsum_eq_sum fun n hn => ?_
      rw [Finset.mem_product, not_and_or] at hn
      rcases hn with h1 | h2
      · rw [smoothedDisk_eq_zero_of_abs_x_gt hR (hsupp_S n.1 h1), Complex.ofReal_zero]
      · rw [smoothedDisk_eq_zero_of_abs_y_gt hR (hsupp_S n.2 h2), Complex.ofReal_zero]
    rw [hfin, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun n₂ _ => ?_
    refine (tsum_eq_sum fun n₁ hn₁ => ?_).symm
    rw [smoothedDisk_eq_zero_of_abs_x_gt hR (hsupp_S n₁ hn₁), Complex.ofReal_zero]
  rw [hspatial_eq]
  -- Summability of `xFourierDisk R a m₁ y` in `m₁ : ℤ`
  have hsum_x : ∀ y : ℝ, Summable (fun m₁ : ℤ => xFourierDisk R a m₁ y) := by
    intro y
    have hbound : ∀ m₁ : ℤ, ‖xFourierDisk R a m₁ y‖ ≤
        ((1 / (2 * a)) * (Real.pi * R ^ 2)) * ‖tentHat a m₁‖ := by
      intro m₁
      unfold xFourierDisk
      rw [norm_mul]
      have hint_le :
          ‖∫ p : ℝ × ℝ, Complex.exp (-(2 * Real.pi * (m₁ * p.1) : ℝ) * Complex.I) *
              (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)‖ ≤
            (1 / (2 * a)) * (Real.pi * R ^ 2) := by
        calc
          ‖∫ p : ℝ × ℝ, Complex.exp (-(2 * Real.pi * (m₁ * p.1) : ℝ) * Complex.I) *
              (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)‖
              ≤ ∫ p : ℝ × ℝ, ‖Complex.exp (-(2 * Real.pi * (m₁ * p.1) : ℝ) * Complex.I) *
                  (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ p : ℝ × ℝ, (1 / (2 * a)) * diskInd R p := by
                refine integral_mono ?_ ((integrable_diskInd R).const_mul _) fun p => ?_
                · have hmeas : AEStronglyMeasurable
                      (fun p : ℝ × ℝ => Complex.exp (-(2 * Real.pi * (m₁ * p.1) : ℝ) * Complex.I) *
                        (diskInd R p : ℂ) * (tent a (y - p.2) : ℂ)) volume := by
                    refine Measurable.aestronglyMeasurable ?_
                    refine (Measurable.mul ?_
                      (Complex.continuous_ofReal.measurable.comp (measurable_diskInd R))).mul
                      (Complex.continuous_ofReal.measurable.comp
                        ((continuous_tent a).measurable.comp (measurable_const.sub measurable_snd)))
                    fun_prop
                  refine (((integrable_diskInd R).const_mul (1 / (2 * a))).mono' hmeas
                    (Filter.Eventually.of_forall fun p => ?_)).norm
                  rw [norm_mul, norm_mul,
                    show -(2 * Real.pi * (m₁ * p.1) : ℝ) * Complex.I =
                      ((-(2 * Real.pi * (m₁ * p.1)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                    Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Complex.norm_real,
                    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (diskInd_nonneg R p),
                    abs_of_nonneg (tent_nonneg ha _)]
                  nlinarith [tent_le ha (y - p.2), diskInd_nonneg R p]
                · rw [norm_mul, norm_mul,
                    show -(2 * Real.pi * (m₁ * p.1) : ℝ) * Complex.I =
                      ((-(2 * Real.pi * (m₁ * p.1)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                    Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Complex.norm_real,
                    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (diskInd_nonneg R p),
                    abs_of_nonneg (tent_nonneg ha _)]
                  nlinarith [tent_le ha (y - p.2), diskInd_nonneg R p]
          _ = (1 / (2 * a)) * (Real.pi * R ^ 2) := by
                rw [integral_const_mul, integral_diskInd hR]
      nlinarith [norm_nonneg (tentHat a m₁)]
    exact Summable.of_norm_bounded
      ((summable_norm_tentHat ha).mul_left ((1 / (2 * a)) * (Real.pi * R ^ 2))) hbound
  -- Step 1: 1D Poisson in `n₁` for each `n₂ ∈ S`
  have hstep1 :
      (∑ n₂ ∈ S, ∑' n₁ : ℤ, (smoothedDisk R a n₁ n₂ : ℂ)) =
      ∑ n₂ ∈ S, ∑' m₁ : ℤ, xFourierDisk R a m₁ n₂ := by
    refine Finset.sum_congr rfl fun n₂ _ => ?_
    have hf := poisson_summation_compact_support (B := R + 2 * a)
      (continuous_smoothedDisk_x ha n₂)
      (fun x hx => by rw [smoothedDisk_eq_zero_of_abs_x_gt hR hx, Complex.ofReal_zero])
      (by
        simpa only [fourier_smoothedDisk_x hR ha] using hsum_x n₂)
    simpa only [fourier_smoothedDisk_x hR ha] using hf
  rw [hstep1]
  -- Swap finite sum over `n₂ ∈ S` with infinite sum over `m₁ : ℤ`
  rw [← Summable.tsum_finsetSum (f := fun (n₂ : ℤ) (m₁ : ℤ) => xFourierDisk R a m₁ n₂)
    (fun n₂ _ => hsum_x n₂)]
  -- Step 2: 1D Poisson in `n₂` for each `m₁ : ℤ`
  have hstep2 : ∀ m₁ : ℤ,
      (∑ n₂ ∈ S, xFourierDisk R a m₁ n₂) =
      ∑' m₂ : ℤ, tentHat a m₁ * tentHat a m₂ * diskFourier R m₁ m₂ := by
    intro m₁
    have hfin_y : (∑ n₂ ∈ S, xFourierDisk R a m₁ n₂) = ∑' n₂ : ℤ, xFourierDisk R a m₁ n₂ := by
      refine (tsum_eq_sum fun n₂ hn₂ => ?_).symm
      exact xFourierDisk_eq_zero_of_abs_gt hR (hsupp_S n₂ hn₂)
    rw [hfin_y]
    have hsum_y : Summable (fun m₂ : ℤ =>
        FourierTransform.fourier (fun y : ℝ => xFourierDisk R a m₁ y) (m₂ : ℝ)) := by
      simp_rw [fourier_xFourierDisk_y hR ha]
      have hbound : ∀ m₂ : ℤ, ‖tentHat a m₁ * tentHat a m₂ * diskFourier R m₁ m₂‖ ≤
          (‖tentHat a m₁‖ * (Real.pi * R ^ 2)) * ‖tentHat a m₂‖ := by
        intro m₂
        rw [norm_mul, norm_mul]
        have h1 := norm_diskFourier_trivial hR m₁ m₂
        have hnn : 0 ≤ ‖tentHat a m₁‖ * ‖tentHat a m₂‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        nlinarith
      exact Summable.of_norm_bounded
        ((summable_norm_tentHat ha).mul_left (‖tentHat a m₁‖ * (Real.pi * R ^ 2))) hbound
    have hf := poisson_summation_compact_support (B := R + 2 * a)
      (continuous_xFourierDisk_y ha m₁)
      (fun y hy => xFourierDisk_eq_zero_of_abs_gt hR hy)
      hsum_y
    simpa only [fourier_xFourierDisk_y hR ha] using hf
  simp_rw [hstep2]
  exact (summable_dual_fourier hR ha).tsum_prod.symm

end TentMollifierAndPoisson

/-! ## Section 5: Dual Lattice Shell Bound & Unconditional Sierpiński `O(R^{2/3})` Breakthrough -/

section SierpinskiBreakthrough

/-- Nonnegative dual summand `‖tentHat a m₁‖ * ‖tentHat a m₂‖ / (m₁² + m₂²)^{3/4}` for `m ≠ (0, 0)`. -/
def dualTerm (a : ℝ) (m : ℤ × ℤ) : ℝ :=
  if m = (0, 0) then 0
  else ‖tentHat a m.1‖ * ‖tentHat a m.2‖ / ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4)

lemma dualTerm_nonneg (a : ℝ) (m : ℤ × ℤ) : 0 ≤ dualTerm a m := by
  unfold dualTerm
  split_ifs
  · exact le_refl 0
  · positivity

/-- `L^∞`-shell `{ m ∈ ℤ² | max |m₁| |m₂| = k }`. -/
def shellSet (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(k : ℤ)) (k : ℤ) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
    (fun m => max m.1.natAbs m.2.natAbs = k)

lemma mem_shellSet {k : ℕ} {m : ℤ × ℤ} :
    m ∈ shellSet k ↔ max m.1.natAbs m.2.natAbs = k := by
  unfold shellSet
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · have h1 : m.1.natAbs ≤ k := by omega
      constructor <;> omega
    · have h2 : m.2.natAbs ≤ k := by omega
      constructor <;> omega

lemma card_shellSet_le {k : ℕ} (hk : 1 ≤ k) : (shellSet k).card ≤ 12 * k := by
  let I : Finset ℤ := Finset.Icc (-(k : ℤ)) (k : ℤ)
  let edge1 : Finset (ℤ × ℤ) := ({(k : ℤ), -(k : ℤ)} : Finset ℤ) ×ˢ I
  let edge2 : Finset (ℤ × ℤ) := I ×ˢ ({(k : ℤ), -(k : ℤ)} : Finset ℤ)
  have hsub : shellSet k ⊆ edge1 ∪ edge2 := by
    intro m hm
    rw [mem_shellSet] at hm
    have h1 : m.1.natAbs ≤ k := by omega
    have h2 : m.2.natAbs ≤ k := by omega
    have hm1I : m.1 ∈ I := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hm2I : m.2 ∈ I := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [Finset.mem_union]
    by_cases heq1 : m.1.natAbs = k
    · left
      refine Finset.mem_product.mpr ⟨?_, hm2I⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · right
      have heq2 : m.2.natAbs = k := by omega
      refine Finset.mem_product.mpr ⟨hm1I, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  have hcardI : I.card = 2 * k + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  have hcard2 : ({(k : ℤ), -(k : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  calc
    (shellSet k).card ≤ (edge1 ∪ edge2).card := Finset.card_le_card hsub
    _ ≤ edge1.card + edge2.card := Finset.card_union_le _ _
    _ = ({(k : ℤ), -(k : ℤ)} : Finset ℤ).card * I.card +
        I.card * ({(k : ℤ), -(k : ℤ)} : Finset ℤ).card := by
          simp [edge1, edge2, Finset.card_product]
    _ ≤ 2 * (2 * k + 1) + (2 * k + 1) * 2 := by
          rw [hcardI]; nlinarith [hcard2]
    _ ≤ 12 * k := by omega

private lemma sum_inv_sqrt_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt k ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hstep : (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
      have hpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hdiff : (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) = 1 := by
        have h1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 := by
          rw [Real.sq_sqrt (by positivity)]; push_cast; ring
        have h2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
        nlinarith
      have hsum_le : Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) ≤
          2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
        have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by push_cast; linarith)
        linarith
      rw [div_le_iff₀ hpos]
      have hnn : 0 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ) :=
        sub_nonneg.mpr (Real.sqrt_le_sqrt (by push_cast; linarith))
      nlinarith
    linarith

private lemma sum_inv_sq_sqrt_tail_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ k ∈ Finset.Icc (N + 1) M, (1 : ℝ) / ((k : ℝ) ^ 2 * Real.sqrt k) ≤
      1 / ((N : ℝ) * Real.sqrt N) - if N ≤ M then 1 / ((M : ℝ) * Real.sqrt M) else 0 := by
  induction M with
  | zero =>
    have hnot : ¬ N ≤ 0 := by omega
    simp only [hnot, ↓reduceIte, sub_zero, Finset.Icc_eq_empty (by omega : ¬ N + 1 ≤ 0),
      Finset.sum_empty]
    positivity
  | succ m ih =>
    by_cases hm : m < N
    · have hemp : Finset.Icc (N + 1) (m + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]
      split_ifs with hle
      · have heq : N = m + 1 := by omega
        subst heq; simp
      · simp only [sub_zero]; positivity
    · push Not at hm
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hmp_pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
      have hIcc : Finset.Icc (N + 1) (m + 1) = insert (m + 1) (Finset.Icc (N + 1) m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      rw [if_pos hm] at ih
      rw [if_pos (by omega : N ≤ m + 1)]
      have hstep :
          (1 : ℝ) / (((m + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤
            1 / ((m : ℝ) * Real.sqrt m) - 1 / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
        set a : ℝ := (m : ℝ)
        set b : ℝ := ((m + 1 : ℕ) : ℝ)
        have hb_eq : b = a + 1 := by dsimp [a, b]; push_cast; ring
        have ha_pos : 0 < a := hm_pos
        have hb_pos : 0 < b := hmp_pos
        have hsa_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha_pos
        have hsb_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb_pos
        have hsr_le : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
        have hnum : Real.sqrt b ≤ b * Real.sqrt b - a * Real.sqrt a := by
          nlinarith [hsr_le, ha_pos]
        have hden : a * Real.sqrt a ≤ b * Real.sqrt b := by nlinarith [hsr_le, ha_pos, hsb_pos]
        rw [div_sub_div _ _ (mul_pos ha_pos hsa_pos).ne' (mul_pos hb_pos hsb_pos).ne',
          one_mul, mul_one,
          div_le_div_iff₀ (by positivity) (by positivity)]
        have hsub_le : a * Real.sqrt a * (b * Real.sqrt b) ≤ b ^ 2 * Real.sqrt b * Real.sqrt b := by
          have : a * Real.sqrt a ≤ b * Real.sqrt b := hden
          have h1 : a * Real.sqrt a * (b * Real.sqrt b) ≤ b * Real.sqrt b * (b * Real.sqrt b) := by
            nlinarith [mul_pos hb_pos hsb_pos]
          nlinarith [h1]
        have hleft : a * Real.sqrt a * (b * Real.sqrt b) ≤
            (b * Real.sqrt b - a * Real.sqrt a) * (b ^ 2 * Real.sqrt b) := by
          have h1 : b ^ 2 * Real.sqrt b * Real.sqrt b ≤
              (b * Real.sqrt b - a * Real.sqrt a) * (b ^ 2 * Real.sqrt b) := by
            have hnn : 0 ≤ b ^ 2 * Real.sqrt b := by positivity
            nlinarith [hnum]
          linarith
        nlinarith [hleft]
      linarith

lemma sum_shell_dualTerm_le {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    ∑ m ∈ shellSet k, dualTerm a m ≤
      min (12 / Real.sqrt k) (3 / (a ^ 2 * (k : ℝ) ^ 2 * Real.sqrt k)) := by
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk_pos
  have hpoint : ∀ m ∈ shellSet k,
      dualTerm a m ≤
        min (1 / ((k : ℝ) * Real.sqrt k)) (1 / (4 * a ^ 2 * (k : ℝ) ^ 3 * Real.sqrt k)) := by
    intro m hm
    rw [mem_shellSet] at hm
    have hm_ne : m ≠ (0, 0) := by
      intro h0; subst h0; simp at hm; omega
    unfold dualTerm
    rw [if_neg hm_ne]
    have hsq_ge : (k : ℝ) ^ 2 ≤ (m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2 := by
      have hmax : (k : ℤ) = max |m.1| |m.2| := by
        have h1 : (m.1.natAbs : ℤ) = |m.1| := Int.natCast_natAbs m.1
        have h2 : (m.2.natAbs : ℤ) = |m.2| := Int.natCast_natAbs m.2
        have h3 : ((max m.1.natAbs m.2.natAbs : ℕ) : ℤ) =
            max (m.1.natAbs : ℤ) (m.2.natAbs : ℤ) := Nat.cast_max _ _
        rw [← hm, h3, h1, h2]
      have hmaxR : (k : ℝ) = max |(m.1 : ℝ)| |(m.2 : ℝ)| := by exact_mod_cast hmax
      rcases le_total |(m.1 : ℝ)| |(m.2 : ℝ)| with hle | hle
      · rw [max_eq_right hle] at hmaxR
        have : (k : ℝ) ^ 2 = (m.2 : ℝ) ^ 2 := by rw [hmaxR, sq_abs]
        nlinarith [sq_nonneg (m.1 : ℝ)]
      · rw [max_eq_left hle] at hmaxR
        have : (k : ℝ) ^ 2 = (m.1 : ℝ) ^ 2 := by rw [hmaxR, sq_abs]
        nlinarith [sq_nonneg (m.2 : ℝ)]
    have hden_ge : (k : ℝ) * Real.sqrt k ≤ ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4) := by
      have h1 : ((k : ℝ) ^ 2) ^ ((3 : ℝ) / 4) ≤ ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow (sq_nonneg _) hsq_ge (by norm_num)
      have h2 : ((k : ℝ) ^ 2) ^ ((3 : ℝ) / 4) = (k : ℝ) * Real.sqrt k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hk_pos.le]
        have : (2 : ℝ) * ((3 : ℝ) / 4) = (3 : ℝ) / 2 := by norm_num
        rw [Nat.cast_ofNat, this, rpow_three_halves_eq hk_pos.le]
      linarith
    have hden_pos : 0 < ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4) :=
      lt_of_lt_of_le (mul_pos hk_pos hsk_pos) hden_ge
    refine le_min ?_ ?_
    · have hnum : ‖tentHat a m.1‖ * ‖tentHat a m.2‖ ≤ 1 := by
        calc
          ‖tentHat a m.1‖ * ‖tentHat a m.2‖ ≤ 1 * 1 :=
            mul_le_mul (norm_tentHat_le_one ha _) (norm_tentHat_le_one ha _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc
        ‖tentHat a m.1‖ * ‖tentHat a m.2‖ / ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4)
            ≤ 1 / ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4) :=
              div_le_div_of_nonneg_right hnum hden_pos.le
        _ ≤ 1 / ((k : ℝ) * Real.sqrt k) :=
              one_div_le_one_div_of_le (mul_pos hk_pos hsk_pos) hden_ge
    · have hnum : ‖tentHat a m.1‖ * ‖tentHat a m.2‖ ≤ 1 / (4 * a ^ 2 * (k : ℝ) ^ 2) := by
        by_cases heq1 : m.1.natAbs = k
        · have hm1_sq : (m.1 : ℝ) ^ 2 = (k : ℝ) ^ 2 := by
            have habs : |(m.1 : ℝ)| = (k : ℝ) := by
              rw [← Int.cast_abs, ← Int.natCast_natAbs, heq1, Int.cast_natCast]
            rw [← sq_abs, habs]
          have hm1_ne : (m.1 : ℝ) ≠ 0 := by
            intro h0; rw [h0, zero_pow two_ne_zero] at hm1_sq; nlinarith [sq_pos_of_pos hk_pos]
          have hA := norm_tentHat_le_quarter ha hm1_ne
          rw [hm1_sq] at hA
          calc
            ‖tentHat a m.1‖ * ‖tentHat a m.2‖ ≤ (1 / (4 * a ^ 2 * (k : ℝ) ^ 2)) * 1 :=
              mul_le_mul hA (norm_tentHat_le_one ha _) (norm_nonneg _) (by positivity)
            _ = 1 / (4 * a ^ 2 * (k : ℝ) ^ 2) := mul_one _
        · have heq2 : m.2.natAbs = k := by omega
          have hm2_sq : (m.2 : ℝ) ^ 2 = (k : ℝ) ^ 2 := by
            have habs : |(m.2 : ℝ)| = (k : ℝ) := by
              rw [← Int.cast_abs, ← Int.natCast_natAbs, heq2, Int.cast_natCast]
            rw [← sq_abs, habs]
          have hm2_ne : (m.2 : ℝ) ≠ 0 := by
            intro h0; rw [h0, zero_pow two_ne_zero] at hm2_sq; nlinarith [sq_pos_of_pos hk_pos]
          have hB := norm_tentHat_le_quarter ha hm2_ne
          rw [hm2_sq] at hB
          calc
            ‖tentHat a m.1‖ * ‖tentHat a m.2‖ ≤ 1 * (1 / (4 * a ^ 2 * (k : ℝ) ^ 2)) :=
              mul_le_mul (norm_tentHat_le_one ha _) hB (norm_nonneg _) zero_le_one
            _ = 1 / (4 * a ^ 2 * (k : ℝ) ^ 2) := one_mul _
      calc
        ‖tentHat a m.1‖ * ‖tentHat a m.2‖ / ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4)
            ≤ (1 / (4 * a ^ 2 * (k : ℝ) ^ 2)) / ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4) :=
              div_le_div_of_nonneg_right hnum hden_pos.le
        _ ≤ (1 / (4 * a ^ 2 * (k : ℝ) ^ 2)) / ((k : ℝ) * Real.sqrt k) :=
              div_le_div_of_nonneg_left (by positivity) (mul_pos hk_pos hsk_pos) hden_ge
        _ = 1 / (4 * a ^ 2 * (k : ℝ) ^ 3 * Real.sqrt k) := by
              field_simp [ha.ne', hk_pos.ne', hsk_pos.ne']
  have hcard : ((shellSet k).card : ℝ) ≤ 12 * (k : ℝ) := by exact_mod_cast card_shellSet_le hk
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  refine le_min ?_ ?_
  · calc
      ((shellSet k).card : ℝ) *
          min (1 / ((k : ℝ) * Real.sqrt k)) (1 / (4 * a ^ 2 * (k : ℝ) ^ 3 * Real.sqrt k))
          ≤ (12 * (k : ℝ)) * (1 / ((k : ℝ) * Real.sqrt k)) :=
            mul_le_mul hcard (min_le_left _ _) (le_min (by positivity) (by positivity)) (by positivity)
      _ = 12 / Real.sqrt k := by field_simp [hk_pos.ne', hsk_pos.ne']
  · calc
      ((shellSet k).card : ℝ) *
          min (1 / ((k : ℝ) * Real.sqrt k)) (1 / (4 * a ^ 2 * (k : ℝ) ^ 3 * Real.sqrt k))
          ≤ (12 * (k : ℝ)) * (1 / (4 * a ^ 2 * (k : ℝ) ^ 3 * Real.sqrt k)) :=
            mul_le_mul hcard (min_le_right _ _) (le_min (by positivity) (by positivity)) (by positivity)
      _ = 3 / (a ^ 2 * (k : ℝ) ^ 2 * Real.sqrt k) := by
            field_simp [ha.ne', hk_pos.ne', hsk_pos.ne']
            ring

/-- **Uniform Finite-Sum Bound on the 2D Dual Lattice Sum**:
for all `0 < a ≤ 1` and every `F : Finset (ℤ × ℤ)`, `∑ m ∈ F, dualTerm a m ≤ 37 / √a`. -/
lemma sum_finset_dualTerm_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (F : Finset (ℤ × ℤ)) :
    ∑ m ∈ F, dualTerm a m ≤ 37 / Real.sqrt a := by
  let M : ℕ := F.sup (fun m => max m.1.natAbs m.2.natAbs)
  let N : ℕ := Nat.ceil (1 / a)
  have hN_ge : (1 / a : ℝ) ≤ (N : ℝ) := Nat.le_ceil (1 / a)
  have hN_pos : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ 1 / a := (one_le_div ha).mpr ha1
    have h2 : (1 : ℝ) ≤ (N : ℝ) := h1.trans hN_ge
    exact_mod_cast h2
  have hN_le : (N : ℝ) ≤ 2 / a := by
    have h1 : (N : ℝ) < 1 / a + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ 1 / a := (one_le_div ha).mpr ha1
    have h3 : (2 : ℝ) / a = 1 / a + 1 / a := by ring
    linarith
  let K : ℕ := max M N
  have hsub : F ⊆ insert (0, 0) ((Finset.Icc 1 K).biUnion shellSet) := by
    intro m hm
    by_cases h0 : m = (0, 0)
    · rw [h0]; exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ?_)
      let k := max m.1.natAbs m.2.natAbs
      refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, mem_shellSet.mpr rfl⟩
      · by_contra hk0
        have hk0' : k = 0 := by omega
        have h1 : m.1 = 0 := by omega
        have h2 : m.2 = 0 := by omega
        exact h0 (Prod.ext h1 h2)
      · exact (Finset.le_sup (f := fun p : ℤ × ℤ => max p.1.natAbs p.2.natAbs) hm).trans
          (le_max_left M N)
  have hdisj : Set.PairwiseDisjoint (Finset.Icc 1 K : Set ℕ) shellSet := by
    intro i _ j _ hij
    show Disjoint (shellSet i) (shellSet j)
    rw [Finset.disjoint_left]
    intro m hmi hmj
    rw [mem_shellSet] at hmi hmj
    exact hij (by omega)
  have h0_notmem : ((0 : ℤ), (0 : ℤ)) ∉ (Finset.Icc 1 K).biUnion shellSet := by
    simp only [Finset.mem_biUnion, Finset.mem_Icc, mem_shellSet, not_exists, not_and]
    intro k hk hmax
    have : max (0 : ℤ).natAbs (0 : ℤ).natAbs = 0 := rfl
    omega
  have hsum_le : ∑ m ∈ F, dualTerm a m ≤ ∑ k ∈ Finset.Icc 1 K, ∑ m ∈ shellSet k, dualTerm a m := by
    calc
      ∑ m ∈ F, dualTerm a m
          ≤ ∑ m ∈ insert (0, 0) ((Finset.Icc 1 K).biUnion shellSet), dualTerm a m :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => dualTerm_nonneg a m)
      _ = dualTerm a (0, 0) + ∑ m ∈ (Finset.Icc 1 K).biUnion shellSet, dualTerm a m :=
            Finset.sum_insert h0_notmem
      _ = ∑ k ∈ Finset.Icc 1 K, ∑ m ∈ shellSet k, dualTerm a m := by
            rw [Finset.sum_biUnion hdisj]
            simp [dualTerm]
  -- Split `Icc 1 K` into `Icc 1 N` and `Icc (N + 1) K`
  have hIcc_split : Finset.Icc 1 K = Finset.Icc 1 N ∪ Finset.Icc (N + 1) K := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hIcc_disj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) K) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega
  rw [hIcc_split, Finset.sum_union hIcc_disj] at hsum_le
  -- Head bound (`1 ≤ k ≤ N`): `≤ 24 √N ≤ 24 √(2 / a) ≤ 34 / √a`
  have hhead : ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ shellSet k, dualTerm a m ≤ 34 / Real.sqrt a := by
    calc
      ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ shellSet k, dualTerm a m
          ≤ ∑ k ∈ Finset.Icc 1 N, (12 : ℝ) * (1 / Real.sqrt k) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
            exact ((sum_shell_dualTerm_le ha hk1).trans (min_le_left _ _)).trans_eq (by ring)
      _ = 12 * ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt k := by rw [Finset.mul_sum]
      _ ≤ 12 * (2 * Real.sqrt N) :=
            mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by norm_num)
      _ ≤ 24 * Real.sqrt (2 / a) := by
            have := Real.sqrt_le_sqrt hN_le
            linarith
      _ = (24 * Real.sqrt 2) / Real.sqrt a := by
            rw [Real.sqrt_div (by norm_num)]; ring
      _ ≤ 34 / Real.sqrt a := by
            have hsqrt2 : Real.sqrt 2 ≤ 17 / 12 := by
              have hsq : Real.sqrt 2 ^ 2 ≤ (17 / 12 : ℝ) ^ 2 := by
                rw [Real.sq_sqrt (by norm_num)]; norm_num
              exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hsq
            refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
            linarith
  -- Tail bound (`N + 1 ≤ k ≤ K`): `≤ (3 / a²) * (1 / (N √N)) ≤ 3 / √a`
  have htail : ∑ k ∈ Finset.Icc (N + 1) K, ∑ m ∈ shellSet k, dualTerm a m ≤ 3 / Real.sqrt a := by
    calc
      ∑ k ∈ Finset.Icc (N + 1) K, ∑ m ∈ shellSet k, dualTerm a m
          ≤ ∑ k ∈ Finset.Icc (N + 1) K, (3 / a ^ 2) * (1 / ((k : ℝ) ^ 2 * Real.sqrt k)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
            refine ((sum_shell_dualTerm_le ha hk1).trans (min_le_right _ _)).trans_eq ?_
            ring
      _ = (3 / a ^ 2) * ∑ k ∈ Finset.Icc (N + 1) K, (1 : ℝ) / ((k : ℝ) ^ 2 * Real.sqrt k) := by
            rw [Finset.mul_sum]
      _ ≤ (3 / a ^ 2) * (1 / ((N : ℝ) * Real.sqrt N)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h1 := sum_inv_sq_sqrt_tail_le hN_pos K
            have h2 : (0 : ℝ) ≤ if N ≤ K then 1 / ((K : ℝ) * Real.sqrt K) else 0 := by
              split_ifs <;> positivity
            linarith
      _ ≤ (3 / a ^ 2) * (1 / ((1 / a) * Real.sqrt (1 / a))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hsr : Real.sqrt (1 / a) ≤ Real.sqrt N := Real.sqrt_le_sqrt hN_ge
            have hprod : (1 / a) * Real.sqrt (1 / a) ≤ (N : ℝ) * Real.sqrt N :=
              mul_le_mul hN_ge hsr (Real.sqrt_nonneg _) (by positivity)
            exact one_div_le_one_div_of_le (mul_pos (by positivity) (Real.sqrt_pos.mpr (by positivity)))
              hprod
      _ = 3 / Real.sqrt a := by
            rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
            have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
            have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
            field_simp [ha.ne', hsa]
            nlinarith [hsq]
  have h37 : (34 : ℝ) / Real.sqrt a + 3 / Real.sqrt a = 37 / Real.sqrt a := by ring
  linarith

lemma summable_dualTerm {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Summable (dualTerm a) :=
  summable_of_sum_le (dualTerm_nonneg a) (sum_finset_dualTerm_le ha ha1)

lemma tsum_dualTerm_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∑' m : ℤ × ℤ, dualTerm a m ≤ 37 / Real.sqrt a :=
  (summable_dualTerm ha ha1).tsum_le_of_sum_le (sum_finset_dualTerm_le ha ha1)

/-- **Master Smoothed-Disk Poisson Error Bound**:
for every `R > 0` and `0 < a ≤ 1`,
`|∑' n : ℤ × ℤ, smoothedDisk R a n.1 n.2 - π R²| ≤ 74 √R / √a`. -/
theorem abs_tsum_smoothedDisk_sub_pi_sq_le {R a : ℝ} (hR : 0 < R) (ha : 0 < a) (ha1 : a ≤ 1) :
    |(∑' n : ℤ × ℤ, smoothedDisk R a n.1 n.2) - Real.pi * R ^ 2| ≤
      74 * Real.sqrt R / Real.sqrt a := by
  have hpois := poisson_summation_smoothedDisk hR.le ha
  have hreal_lhs :
      (((∑' n : ℤ × ℤ, smoothedDisk R a n.1 n.2) - Real.pi * R ^ 2 : ℝ) : ℂ) =
      (∑' m : ℤ × ℤ, tentHat a m.1 * tentHat a m.2 * diskFourier R m.1 m.2) -
        (Real.pi * R ^ 2 : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_tsum, hpois]
    push_cast
    rfl
  -- Extract the `(0, 0)` term from the dual sum
  let g : ℤ × ℤ → ℂ := fun m => tentHat a m.1 * tentHat a m.2 * diskFourier R m.1 m.2
  have hg0 : g (0, 0) = (Real.pi * R ^ 2 : ℂ) := by
    dsimp [g]
    rw [Int.cast_zero, tentHat_zero ha, one_mul, one_mul, diskFourier_zero hR.le]
  have hsum_g : Summable g := summable_dual_fourier hR.le ha
  let g' : ℤ × ℤ → ℂ := fun m => if m = (0, 0) then 0 else g m
  have hdiff : (∑' m : ℤ × ℤ, g m) - (Real.pi * R ^ 2 : ℂ) = ∑' m : ℤ × ℤ, g' m := by
    have hsplit : ∑' m : ℤ × ℤ, g m = g (0, 0) + ∑' m : ℤ × ℤ, g' m := by
      have h1 := hsum_g.tsum_eq_add_tsum_ite (0, 0)
      simpa [g'] using h1
    rw [hsplit, hg0]
    ring
  have hsum_norm_g' : Summable (fun m : ℤ × ℤ => ‖g' m‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((summable_dualTerm ha ha1).mul_left (2 * Real.sqrt R))
    by_cases hm : m = (0, 0)
    · simp [g', dualTerm, hm]
    · simp only [g', dualTerm, hm, ↓reduceIte, g]
      rw [norm_mul, norm_mul]
      have hξ : (m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2 ≠ 0 := by
        intro h0
        have h1 : (m.1 : ℝ) = 0 := by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2 : ℝ)]
        have h2 : (m.2 : ℝ) = 0 := by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2 : ℝ)]
        exact hm (Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2))
      have hF := norm_diskFourier_le hR hξ
      have hnn : 0 ≤ ‖tentHat a m.1‖ * ‖tentHat a m.2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc
        ‖tentHat a m.1‖ * ‖tentHat a m.2‖ * ‖diskFourier R m.1 m.2‖
            ≤ ‖tentHat a m.1‖ * ‖tentHat a m.2‖ *
                (2 * Real.sqrt R / ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4)) :=
              mul_le_mul_of_nonneg_left hF hnn
        _ = 2 * Real.sqrt R *
              (‖tentHat a m.1‖ * ‖tentHat a m.2‖ /
                ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4)) := by ring
  calc
    |(∑' n : ℤ × ℤ, smoothedDisk R a n.1 n.2) - Real.pi * R ^ 2|
        = ‖(((∑' n : ℤ × ℤ, smoothedDisk R a n.1 n.2) - Real.pi * R ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑' m : ℤ × ℤ, g' m‖ := by rw [hreal_lhs, hdiff]
    _ ≤ ∑' m : ℤ × ℤ, ‖g' m‖ := norm_tsum_le_tsum_norm hsum_norm_g'
    _ ≤ ∑' m : ℤ × ℤ, (2 * Real.sqrt R) * dualTerm a m := by
          refine hsum_norm_g'.tsum_le_tsum (fun m => ?_)
            ((summable_dualTerm ha ha1).mul_left (2 * Real.sqrt R))
          by_cases hm : m = (0, 0)
          · simp [g', dualTerm, hm]
          · simp only [g', dualTerm, hm, ↓reduceIte, g]
            rw [norm_mul, norm_mul]
            have hξ : (m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2 ≠ 0 := by
              intro h0
              have h1 : (m.1 : ℝ) = 0 := by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2 : ℝ)]
              have h2 : (m.2 : ℝ) = 0 := by nlinarith [sq_nonneg (m.1 : ℝ), sq_nonneg (m.2 : ℝ)]
              exact hm (Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2))
            have hF := norm_diskFourier_le hR hξ
            have hnn : 0 ≤ ‖tentHat a m.1‖ * ‖tentHat a m.2‖ :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            calc
              ‖tentHat a m.1‖ * ‖tentHat a m.2‖ * ‖diskFourier R m.1 m.2‖
                  ≤ ‖tentHat a m.1‖ * ‖tentHat a m.2‖ *
                      (2 * Real.sqrt R / ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4)) :=
                    mul_le_mul_of_nonneg_left hF hnn
              _ = 2 * Real.sqrt R *
                    (‖tentHat a m.1‖ * ‖tentHat a m.2‖ /
                      ((m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2) ^ ((3 : ℝ) / 4)) := by ring
    _ = 2 * Real.sqrt R * ∑' m : ℤ × ℤ, dualTerm a m := tsum_mul_left
    _ ≤ 2 * Real.sqrt R * (37 / Real.sqrt a) :=
          mul_le_mul_of_nonneg_left (tsum_dualTerm_le ha ha1) (by positivity)
    _ = 74 * Real.sqrt R / Real.sqrt a := by ring

lemma gaussCircleCount_eq_tsum_diskInd {R : ℝ} (hR : 0 ≤ R) :
    (gaussCircleCount R : ℝ) = ∑' n : ℤ × ℤ, diskInd R (n.1, n.2) := by
  let S : Finset (ℤ × ℤ) := (latticeBallSet 2 R).image (fun v => (v 0, v 1))
  have hinj : Set.InjOn (fun v : Fin 2 → ℤ => (v 0, v 1)) (latticeBallSet 2 R : Set (Fin 2 → ℤ)) := by
    intro u _ v _ huv
    ext i; fin_cases i
    · exact (Prod.mk.inj huv).1
    · exact (Prod.mk.inj huv).2
  have hcard : gaussCircleCount R = S.card := by
    unfold gaussCircleCount latticeBallCount
    exact (Finset.card_image_of_injOn hinj).symm
  have hmemS : ∀ n : ℤ × ℤ, n ∈ S ↔ (n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2 ≤ R ^ 2 := by
    intro n
    simp only [S, Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_latticeBallSet_iff_sum_sq hR, Fin.sum_univ_two] at hv
      exact hv
    · intro hn
      refine ⟨![n.1, n.2], ?_, by simp⟩
      rw [mem_latticeBallSet_iff_sum_sq hR, Fin.sum_univ_two]
      simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using hn
  rw [hcard, tsum_eq_sum (s := S) (fun n hn => by
    unfold diskInd
    rw [if_neg (mt (hmemS n).mpr hn)])]
  have h1 : ∀ n ∈ S, diskInd R (n.1, n.2) = 1 := fun n hn => by
    unfold diskInd
    rw [if_pos ((hmemS n).mp hn)]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma summable_smoothedDisk {R a : ℝ} (hR : 0 ≤ R) :
    Summable (fun n : ℤ × ℤ => smoothedDisk R a n.1 n.2) := by
  set M : ℤ := ⌈R + 2 * a⌉ + 1
  let S : Finset (ℤ × ℤ) := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M
  refine summable_of_ne_finset_zero (s := S) fun n hn => ?_
  have hM_gt : R + 2 * a < (M : ℝ) := by
    have : R + 2 * a ≤ (⌈R + 2 * a⌉ : ℝ) := Int.le_ceil _
    dsimp [M]; push_cast; linarith
  have hsupp : ∀ k : ℤ, k ∉ Finset.Icc (-M) M → R + 2 * a < |(k : ℝ)| := by
    intro k hk
    simp only [Finset.mem_Icc, not_and_or, not_le] at hk
    rcases hk with hlt | hgt
    · have : (k : ℝ) < -(M : ℝ) := by exact_mod_cast hlt
      have : (M : ℝ) < |(k : ℝ)| := by rw [lt_abs]; right; linarith
      linarith
    · have : (M : ℝ) < (k : ℝ) := by exact_mod_cast hgt
      have : (M : ℝ) < |(k : ℝ)| := by rw [lt_abs]; left; linarith
      linarith
  rw [Finset.mem_product, not_and_or] at hn
  rcases hn with h1 | h2
  · exact smoothedDisk_eq_zero_of_abs_x_gt hR (hsupp n.1 h1)
  · exact smoothedDisk_eq_zero_of_abs_y_gt hR (hsupp n.2 h2)

lemma summable_diskInd_int {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun n : ℤ × ℤ => diskInd R (n.1, n.2)) := by
  set M : ℤ := ⌈R⌉ + 1
  let S : Finset (ℤ × ℤ) := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M
  refine summable_of_ne_finset_zero (s := S) fun n hn => ?_
  have hM_gt : R < (M : ℝ) := by
    have : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil _
    dsimp [M]; push_cast; linarith
  unfold diskInd
  rw [if_neg]
  intro hle
  have h1 : |(n.1 : ℝ)| ≤ R := by
    have hsq : |(n.1 : ℝ)| ^ 2 ≤ R ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg (n.2 : ℝ)]
    exact (sq_le_sq₀ (abs_nonneg _) hR).mp hsq
  have h2 : |(n.2 : ℝ)| ≤ R := by
    have hsq : |(n.2 : ℝ)| ^ 2 ≤ R ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg (n.1 : ℝ)]
    exact (sq_le_sq₀ (abs_nonneg _) hR).mp hsq
  have hmem : n ∈ S := by
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_, Finset.mem_Icc.mpr ?_⟩
    · have := abs_le.mp h1
      exact ⟨by exact_mod_cast (by linarith : -(M : ℝ) ≤ (n.1 : ℝ)),
        by exact_mod_cast (by linarith : (n.1 : ℝ) ≤ (M : ℝ))⟩
    · have := abs_le.mp h2
      exact ⟨by exact_mod_cast (by linarith : -(M : ℝ) ≤ (n.2 : ℝ)),
        by exact_mod_cast (by linarith : (n.2 : ℝ) ≤ (M : ℝ))⟩
  exact hn hmem

/-- **UNCONDITIONAL SIERPIŃSKI (1906) / VORONOÏ–LANDAU `O(R^{2/3})` GAUSS CIRCLE THEOREM**
(Explicit Constant, ZERO Logarithmic Loss, ZERO Assumptions!):
for every `R ≥ 1`,
`|(gaussCircleCount R : ℝ) - π R²| ≤ 300 * R^{2/3}`. -/
theorem gauss_circle_sierpinski_bound {R : ℝ} (hR : 1 ≤ R) :
    |(gaussCircleCount R : ℝ) - Real.pi * R ^ 2| ≤ 300 * R ^ ((2 : ℝ) / 3) := by
  have hR_pos : 0 < R := by linarith
  set a : ℝ := (1 / 8 : ℝ) * R ^ (-(1 : ℝ) / 3)
  have ha_pos : 0 < a := by positivity
  have hR_neg13_le : R ^ (-(1 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)
  have ha_le_eighth : a ≤ 1 / 8 := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by linarith
  have hsqrt2_le : Real.sqrt 2 ≤ 3 / 2 := by
    have : Real.sqrt 2 ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp this
  set h : ℝ := 2 * Real.sqrt 2 * a
  have hh_pos : 0 < h := by positivity
  have hh_le_half : h ≤ 1 / 2 := by dsimp [h]; nlinarith
  have hR_sub_pos : 0 < R - h := by linarith
  have hR_add_le : R + h ≤ 2 * R := by linarith
  have hR_sub_le : R - h ≤ 2 * R := by linarith
  -- Key `rpow` identities
  have hR_two_thirds : R * R ^ (-(1 : ℝ) / 3) = R ^ ((2 : ℝ) / 3) := by
    calc
      R * R ^ (-(1 : ℝ) / 3) = R ^ (1 : ℝ) * R ^ (-(1 : ℝ) / 3) := by rw [Real.rpow_one]
      _ = R ^ ((1 : ℝ) + -(1 : ℝ) / 3) := (Real.rpow_add hR_pos _ _).symm
      _ = R ^ ((2 : ℝ) / 3) := by congr 1; norm_num
  have hsqrt_div : Real.sqrt (2 * R) / Real.sqrt a = 4 * R ^ ((2 : ℝ) / 3) := by
    have hsqrt_a : Real.sqrt a = (1 / Real.sqrt 8) * R ^ (-(1 : ℝ) / 6) := by
      dsimp [a]
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_div zero_le_one, Real.sqrt_one]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR_pos.le]
      congr 1; norm_num
    have hsqrt_2R : Real.sqrt (2 * R) = Real.sqrt 2 * R ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_mul (by norm_num)]
      congr 1
      exact Real.sqrt_eq_rpow R
    have hsqrt28 : Real.sqrt 2 * Real.sqrt 8 = 4 := by
      rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ) * 8 = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [hsqrt_2R, hsqrt_a]
    have hne8 : Real.sqrt 8 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hneR : R ^ (-(1 : ℝ) / 6) ≠ 0 := (Real.rpow_pos_of_pos hR_pos _).ne'
    calc
      Real.sqrt 2 * R ^ ((1 : ℝ) / 2) / (1 / Real.sqrt 8 * R ^ (-(1 : ℝ) / 6))
          = (Real.sqrt 2 * Real.sqrt 8) * (R ^ ((1 : ℝ) / 2) / R ^ (-(1 : ℝ) / 6)) := by
            field_simp [hne8, hneR]
      _ = 4 * R ^ ((1 : ℝ) / 2 - (-(1 : ℝ) / 6)) := by
            rw [hsqrt28, ← Real.rpow_sub hR_pos]
      _ = 4 * R ^ ((2 : ℝ) / 3) := by congr 2; norm_num
  -- Dual error bound for `R' ∈ {R + h, R - h}`: `74 √R' / √a ≤ 296 R^{2/3}`
  have hdual_hi : 74 * Real.sqrt (R + h) / Real.sqrt a ≤ 296 * R ^ ((2 : ℝ) / 3) := by
    calc
      74 * Real.sqrt (R + h) / Real.sqrt a
          ≤ 74 * Real.sqrt (2 * R) / Real.sqrt a := by
            gcongr
      _ = 74 * (Real.sqrt (2 * R) / Real.sqrt a) := by ring
      _ = 296 * R ^ ((2 : ℝ) / 3) := by rw [hsqrt_div]; ring
  have hdual_lo : 74 * Real.sqrt (R - h) / Real.sqrt a ≤ 296 * R ^ ((2 : ℝ) / 3) := by
    calc
      74 * Real.sqrt (R - h) / Real.sqrt a
          ≤ 74 * Real.sqrt (2 * R) / Real.sqrt a := by
            gcongr
      _ = 74 * (Real.sqrt (2 * R) / Real.sqrt a) := by ring
      _ = 296 * R ^ ((2 : ℝ) / 3) := by rw [hsqrt_div]; ring
  -- Main term difference bound: `≤ 4 * R^{2/3}`
  have hpi_lt : Real.pi < 4 := Real.pi_lt_four
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hmain_hi : Real.pi * (R + h) ^ 2 - Real.pi * R ^ 2 ≤ 4 * R ^ ((2 : ℝ) / 3) := by
    have hRh : R * h ≤ (3 / 8) * R ^ ((2 : ℝ) / 3) := by
      dsimp [h, a]
      have : R * (2 * Real.sqrt 2 * (1 / 8 * R ^ (-(1 : ℝ) / 3))) =
          (Real.sqrt 2 / 4) * (R * R ^ (-(1 : ℝ) / 3)) := by ring
      rw [this, hR_two_thirds]
      have hnn : 0 ≤ R ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hR_pos.le _
      nlinarith
    have hh2 : h ^ 2 ≤ (1 / 4) * R ^ ((2 : ℝ) / 3) := by
      have h1 : h ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith [hh_pos, hh_le_half]
      have h2 : (1 : ℝ) ≤ R ^ ((2 : ℝ) / 3) := Real.one_le_rpow hR (by norm_num)
      linarith
    have hdiff : Real.pi * (R + h) ^ 2 - Real.pi * R ^ 2 = Real.pi * (2 * (R * h) + h ^ 2) := by
      ring
    rw [hdiff]
    have hsum : 2 * (R * h) + h ^ 2 ≤ R ^ ((2 : ℝ) / 3) := by linarith
    have hnn : 0 ≤ 2 * (R * h) + h ^ 2 := by positivity
    nlinarith
  have hmain_lo : Real.pi * R ^ 2 - Real.pi * (R - h) ^ 2 ≤ 4 * R ^ ((2 : ℝ) / 3) := by
    have hRh : R * h ≤ (3 / 8) * R ^ ((2 : ℝ) / 3) := by
      dsimp [h, a]
      have : R * (2 * Real.sqrt 2 * (1 / 8 * R ^ (-(1 : ℝ) / 3))) =
          (Real.sqrt 2 / 4) * (R * R ^ (-(1 : ℝ) / 3)) := by ring
      rw [this, hR_two_thirds]
      have hnn : 0 ≤ R ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hR_pos.le _
      nlinarith
    have hdiff : Real.pi * R ^ 2 - Real.pi * (R - h) ^ 2 = Real.pi * (2 * (R * h) - h ^ 2) := by
      ring
    rw [hdiff]
    have hbound : 2 * (R * h) - h ^ 2 ≤ R ^ ((2 : ℝ) / 3) := by
      have hnn : 0 ≤ h ^ 2 := sq_nonneg h
      have hR23 : 0 ≤ R ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hR_pos.le _
      linarith
    have hpos_rhs : 0 ≤ R ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hR_pos.le _
    nlinarith
  -- Sandwich the Gauss circle count between the two smoothed Poisson sums
  have hcount_le : (gaussCircleCount R : ℝ) ≤ ∑' n : ℤ × ℤ, smoothedDisk (R + h) a n.1 n.2 := by
    rw [gaussCircleCount_eq_tsum_diskInd hR_pos.le]
    exact (summable_diskInd_int hR_pos.le).tsum_le_tsum
      (fun n => diskInd_le_smoothedDisk hR_pos.le ha_pos n.1 n.2)
      (summable_smoothedDisk (by linarith))
  have hcount_ge : ∑' n : ℤ × ℤ, smoothedDisk (R - h) a n.1 n.2 ≤ (gaussCircleCount R : ℝ) := by
    rw [gaussCircleCount_eq_tsum_diskInd hR_pos.le]
    exact (summable_smoothedDisk hR_sub_pos.le).tsum_le_tsum
      (fun n => smoothedDisk_le_diskInd ha_pos (by linarith) n.1 n.2)
      (summable_diskInd_int hR_pos.le)
  have herr_hi := abs_tsum_smoothedDisk_sub_pi_sq_le (by linarith : 0 < R + h) ha_pos ha1
  have herr_lo := abs_tsum_smoothedDisk_sub_pi_sq_le hR_sub_pos ha_pos ha1
  rw [abs_le] at herr_hi herr_lo ⊢
  constructor
  · linarith [hcount_ge, herr_lo.1, hdual_lo, hmain_lo]
  · linarith [hcount_le, herr_hi.2, hdual_hi, hmain_hi]

/-- **Unconditional Sierpiński (1906) / Voronoï–Landau Poisson-Summation Bound** (`∃ C > 0`, `O(R^{2/3})`). -/
theorem gauss_circle_sierpinski_poisson_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      |(gaussCircleCount R : ℝ) - Real.pi * R ^ 2| ≤ C * R ^ ((2 : ℝ) / 3) :=
  ⟨300, by norm_num, fun _ hR => gauss_circle_sierpinski_bound (by linarith)⟩

/-- **Unconditional Sub-Linear Gauss Circle Bound** (also implying `O(R^{2/3} log R)` for `R ≥ 2`). -/
theorem gauss_circle_sublinear_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      |(gaussCircleCount R : ℝ) - Real.pi * R ^ 2| ≤ C * R ^ ((2 : ℝ) / 3) * Real.log R := by
  refine ⟨600, by norm_num, fun R hR => ?_⟩
  have h1 := gauss_circle_sierpinski_bound (by linarith : (1 : ℝ) ≤ R)
  have hlog : (1 / 2 : ℝ) ≤ Real.log R := by
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
        have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
          have := Real.add_one_le_exp (-(1 / 2 : ℝ))
          linarith
        rw [Real.exp_neg] at h1
        have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
        have hmul : (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) ≤ 1 := by
          have := mul_le_mul_of_nonneg_right h1 hpos.le
          rwa [inv_mul_cancel₀ hpos.ne'] at this
        linarith
      have := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at this
    exact h2.trans (Real.log_le_log (by norm_num) hR)
  have hnn : 0 ≤ R ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- **Unconditional Sub-Square-Root Average of `r₂(n)` (Explicit Constant, ZERO Log Loss)**:
for every `N ≥ 1`,
`|∑ n ∈ Finset.Icc 0 N, r₂(n) - π N| ≤ 300 * N^{1/3}`
(improving Gauss's elementary `O(√N)` all the way to Sierpiński's `O(N^{1/3})`). -/
theorem sum_repTwoSquares_asymp_explicit {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 0 N, (repTwoSquares n : ℝ)) - Real.pi * (N : ℝ)| ≤
      300 * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  have hN_ge : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt_ge : 1 ≤ Real.sqrt N := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hN_ge
  have hbound := gauss_circle_sierpinski_bound hsqrt_ge
  rw [gaussCircleCount_sqrt_nat N, Nat.cast_sum, Real.sq_sqrt (Nat.cast_nonneg N)] at hbound
  have hrpow : (Real.sqrt N) ^ ((2 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1; norm_num
  rwa [hrpow] at hbound

/-- **Unconditional Sub-Square-Root Average of `r₂(n)` (`∃ C > 0`, exact `O(N^{1/3})`)**. -/
theorem sum_repTwoSquares_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 0 N, (repTwoSquares n : ℝ)) - Real.pi * (N : ℝ)| ≤
        C * (N : ℝ) ^ ((1 : ℝ) / 3) :=
  ⟨300, by norm_num, fun _ hN => sum_repTwoSquares_asymp_explicit hN⟩

end SierpinskiBreakthrough

end

end RHDirect.Stage9LatticePointCounting
