import RHDirect.Interfaces
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# RHDirect.BesselWaveGrid

Compact, self-contained, 0-`sorry`, 0-`axiom` Lean 4 rebuild of the **Bessel / Whittaker
Wave-Grid Evaluation, Test-Vector Assembly, Local-Factor Matching & Orbit/Frame Norm Core**,
compressing the duplicated `ThetaBesselIsometries` (`143f / 10,415L`) ↔ `JetHarmonics`
(`1,415f / 129,062L`) and `BesselWaveGrids` / `BesselOrbitBounds` / `BesselModels` cluster
into one direct, idiomatic module.

## Contents
1. **Interlacing Wave-Grid Geometry & Cut-Interval Separation** (`progY`, `gridY`, `gridΛ`):
   - Spacing-5 arithmetic grids with exact cardinality, pairwise 5-separation, simultaneous
     cut-interval inclusion (`lo + 2 ≤ -y, -(y+1) ≤ hi - 2`), and wave-grid scale threshold
     `gridΛ` bounded by `b ^ ((6 + CT) * (2*r + 2))`.
2. **Letter-Word Rational Shift Factors & `ℓ¹`-Ball Jet Shifts** (`Letter`, `letterFac`,
   `wordFactor`, `wordEval`, `shiftBall`):
   - Exact rational shift factor bounds `3/4 ≤ letterFac l y ≤ 4/3` away from poles
     (`4 ≤ |y - l.pt|`), word-length product envelopes `(3/4)^|w| ≤ wordFactor w y ≤ (4/3)^|w|`,
     nonvanishing on separated evaluation grids, and `ℓ¹` ball radius control for jet shifts.
3. **Discrete Bessel Wave-Grid Evaluation Operator, Vandermonde Separation & Test-Vector
   Assembly** (`waveEval`, `waveGram`, `lagrangeTestVector`, `bessel_finrank_le_one`):
   - Finite wave-grid evaluation linear map with exact Parseval/Gram identity, Lagrange
     delta test-vector construction on any separated grid (including `progY`), Vandermonde
     injectivity, quantitative grid-point lower bound (`∃ y ∈ Y, c * ‖v‖ / √|Y| ≤ ‖eval v y‖`),
     and Bessel multiplicity-one (`finrank ≤ 1`) from invariant-line proportionality.
4. **Local-Factor Multiplicativity & Tower-Stage Norm Factorization** (`LocalFactorSystem`,
   `global_norm_prod_local_factors`, `local_factor_ratio_matching`, `tower_stage_norm_prod`):
   - Exact Euler/place factorization of global theta/Bessel norms across finite places,
     cancellation of unramified local factors in twin-lift ratios, and telescoping norm
     factorization along an `m`-step Witt/theta tower.
5. **Orbit-Word Growth, Gap-Size Envelopes, Grid-Frame Gram/Schur Inequalities & `nWv`
   Coupling** (`prod_norm_le`, `orbit_word_norm_bound`, `gap_sizes_ineq`, `gapY_bounds`,
   `grid_frame_lower_bound`, `grid_frame_upper_bound`, `grid_frame_linearIndependent`,
   `gram_frobenius_frame_bound`, `nWv_bounds`, `rankVal_wave_grid_bounds`):
   - Lie-word conjugation growth bounds, discrete-series gap-size margins (`120 N^3`,
     `125 m^2 N^3`, `(2r+2)^(9/2)`), diagonally-dominant and Frobenius-defect Bessel-frame
     norm inequalities feeding `LatticeFrame.lean`, and exact bounds on `RHDirect.nWv`,
     `RHDirect.TOv`, `RHDirect.ChainRanks.chainRank`, and `RHDirect.RankVal` feeding
     `ThetaSlopeEngine.lean`.

Zero `sorry`, zero custom `axiom`s.
-/

open Real Finset Matrix RHDirect
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace RHDirect.BesselWaveGrid

noncomputable section

/-! ## Section 1: Interlacing Wave-Grid Geometry & Scale Threshold (`progY`, `gridY`, `gridΛ`) -/

/-- Spacing-5 arithmetic progression `y₀, y₀ + 5, ..., y₀ + 5(M - 1)` forming an
interlacing evaluation grid for Bessel/Whittaker wave packets. -/
def progY (y0 : ℝ) (M : ℕ) : Finset ℝ :=
  (Finset.range M).image fun i : ℕ => y0 + 5 * (i : ℝ)

theorem progY_injective (y0 : ℝ) : Function.Injective fun i : ℕ => y0 + 5 * (i : ℝ) := by
  intro i j h
  have h' : (i : ℝ) = j := by linarith
  exact_mod_cast h'

theorem progY_card (y0 : ℝ) (M : ℕ) : (progY y0 M).card = M := by
  unfold progY
  rw [Finset.card_image_of_injective _ (progY_injective y0), Finset.card_range]

theorem progY_sep (y0 : ℝ) (M : ℕ) :
    ∀ y ∈ progY y0 M, ∀ y' ∈ progY y0 M, y ≠ y' → 5 ≤ |y - y'| := by
  intro y hy y' hy' hne
  simp only [progY, Finset.mem_image, Finset.mem_range] at hy hy'
  obtain ⟨i, -, rfl⟩ := hy
  obtain ⟨j, -, rfl⟩ := hy'
  have hij : i ≠ j := fun h => hne (by rw [h])
  have hsub : y0 + 5 * (i : ℝ) - (y0 + 5 * (j : ℝ)) = 5 * (((i : ℤ) - (j : ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [hsub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
  have h1 : (1 : ℝ) ≤ |(((i : ℤ) - (j : ℤ) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    have hZ : (1 : ℤ) ≤ |(i : ℤ) - (j : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hij))
    exact_mod_cast hZ
  linarith

/-- Every point `y` of `progY (2 - hi) M` places both `-y` and `-(y + 1)` strictly inside the
cut interval `[lo + 2, hi - 2]` whenever `5 * M ≤ hi - lo`. -/
theorem progY_cut (lo hi : ℝ) (M : ℕ) (hlen : 5 * (M : ℝ) ≤ hi - lo) :
    ∀ y ∈ progY (2 - hi) M,
      (lo + 2 ≤ -y ∧ -y ≤ hi - 2) ∧ (lo + 2 ≤ -(y + 1) ∧ -(y + 1) ≤ hi - 2) := by
  intro y hy
  simp only [progY, Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨i, hi', rfl⟩ := hy
  have hiM : (i : ℝ) + 1 ≤ M := by exact_mod_cast hi'
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- Wave-grid evaluation set attached to spectral shifts `(u, u')` at index `l`, rank `r`,
and depth `N`. -/
def gridY (u u' : ℕ → ℝ) (r l N : ℕ) : Finset ℝ :=
  progY (2 - max (u l) (u' l)) (N * (2 * r + 1))

theorem gridY_card (u u' : ℕ → ℝ) (r l N : ℕ) :
    (gridY u u' r l N).card = N * (2 * r + 1) :=
  progY_card _ _

theorem gridY_sep (u u' : ℕ → ℝ) (r l N : ℕ) :
    ∀ y ∈ gridY u u' r l N, ∀ y' ∈ gridY u u' r l N, y ≠ y' → 5 ≤ |y - y'| :=
  progY_sep _ _

/-- Simultaneous cut-interval inclusion for `gridY` when the spectral gap
`|u l - u' l|` accommodates `5 * N * (2 * r + 1)`. -/
theorem gridY_onCut (u u' : ℕ → ℝ) (r l N : ℕ)
    (hlen : 5 * ((N * (2 * r + 1) : ℕ) : ℝ) ≤ |u l - u' l|) :
    ∀ y ∈ gridY u u' r l N,
      (min (u l) (u' l) + 2 ≤ -y ∧ -y ≤ max (u l) (u' l) - 2) ∧
      (min (u l) (u' l) + 2 ≤ -(y + 1) ∧ -(y + 1) ≤ max (u l) (u' l) - 2) := by
  have hdiff : max (u l) (u' l) - min (u l) (u' l) = |u l - u' l| := by
    rcases le_total (u l) (u' l) with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  exact progY_cut (min (u l) (u' l)) (max (u l) (u' l)) (N * (2 * r + 1)) (by rwa [hdiff])

/-- Wave-grid amplitude threshold `Λ(r, b, T, T', N) = max 1 √((4/3)^N * b^(8r+20) / (T * T'))`. -/
def gridΛ (r : ℕ) (b T T' : ℝ) (N : ℕ) : ℝ :=
  max 1 (Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T'))))

theorem one_le_gridΛ (r : ℕ) (b T T' : ℝ) (N : ℕ) : 1 ≤ gridΛ r b T T' N :=
  le_max_left _ _

theorem gridΛ_sq_ge (r : ℕ) (b T T' : ℝ) (N : ℕ) (hb : 0 ≤ b) (hTT : 0 < T * T') :
    (4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T')) ≤ gridΛ r b T T' N ^ 2 := by
  unfold gridΛ
  have hX : 0 ≤ (4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T')) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (div_nonneg (pow_nonneg hb _) hTT.le)
  calc (4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T'))
      = Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T'))) ^ 2 := (Real.sq_sqrt hX).symm
    _ ≤ max 1 (Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T')))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2

/-- Polynomial-in-`b` upper bound `gridΛ ≤ b ^ ((6 + CT) * (2*r + 2))` for `N ≤ 3(r + 1)`
and lower-bounded period product `T * T' ≥ b ^ (-CT * (2r + 2))`. -/
theorem gridΛ_le (r : ℕ) (b T T' CT : ℝ) (N : ℕ) (hN : N ≤ 3 * (r + 1)) (hb : 3 ≤ b)
    (hCT : 0 ≤ CT) (hTT0 : 0 < T * T')
    (hTT : b ^ (-(CT * ((2 * r + 2 : ℕ) : ℝ))) ≤ T * T') :
    gridΛ r b T T' N ≤ b ^ ((6 + CT) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  set m : ℝ := ((2 * r + 2 : ℕ) : ℝ)
  have hm' : m = 2 * (r : ℝ) + 2 := by unfold m; push_cast; ring
  have hm0 : 0 ≤ m := by rw [hm']; linarith
  have hinv : (T * T')⁻¹ ≤ b ^ (CT * m) := by
    have h1 : 0 < b ^ (CT * m) := Real.rpow_pos_of_pos hb0 _
    rw [Real.rpow_neg hb0.le] at hTT
    exact (inv_le_comm₀ h1 hTT0).mp hTT
  have h43 : (4 / 3 : ℝ) ^ N ≤ b ^ (3 * (r + 1)) :=
    le_trans (pow_le_pow_left₀ (by norm_num) (by linarith) N) (pow_le_pow_right₀ hb1 hN)
  have hpow : b ^ (3 * (r + 1)) * b ^ (8 * r + 20) ≤ b ^ (12 * m) := by
    rw [← pow_add, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb1
    rw [hm']; push_cast; linarith
  have hX : (4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T')) ≤ b ^ (12 * m) * b ^ (CT * m) := by
    rw [div_eq_mul_inv]
    calc (4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) * (T * T')⁻¹)
        ≤ b ^ (3 * (r + 1)) * (b ^ (8 * r + 20) * b ^ (CT * m)) :=
          mul_le_mul h43 (mul_le_mul_of_nonneg_left hinv (pow_nonneg hb0.le _))
            (mul_nonneg (pow_nonneg hb0.le _) (inv_nonneg.mpr hTT0.le)) (pow_nonneg hb0.le _)
      _ = (b ^ (3 * (r + 1)) * b ^ (8 * r + 20)) * b ^ (CT * m) := by ring
      _ ≤ b ^ (12 * m) * b ^ (CT * m) := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hb0.le _)
  have hy : (b ^ ((6 + CT) * m)) ^ 2 = b ^ (12 * m) * b ^ (2 * (CT * m)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
    congr 1; push_cast; ring
  have hX' : (4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T')) ≤ (b ^ ((6 + CT) * m)) ^ 2 := by
    rw [hy]
    refine le_trans hX (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hb0.le _))
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by nlinarith)
  unfold gridΛ
  refine max_le (Real.one_le_rpow hb1 (mul_nonneg (by linarith) hm0)) ?_
  calc Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * r + 20) / (T * T')))
      ≤ Real.sqrt ((b ^ ((6 + CT) * m)) ^ 2) := Real.sqrt_le_sqrt hX'
    _ = b ^ ((6 + CT) * m) := Real.sqrt_sq (Real.rpow_nonneg hb0.le _)

/-! ## Section 2: Rational Letter-Word Shift Factors & `ℓ¹`-Ball Jet Shifts -/

/-- A signed shift letter `(plus, pt)` representing a rational Bessel-shift factor on the grid. -/
structure Letter where
  plus : Bool
  pt : ℝ

/-- Rational shift factor attached to a single letter `l` evaluated at `y : ℝ`. -/
def letterFac (l : Letter) (y : ℝ) : ℝ :=
  if l.plus then (y - l.pt + 1) / (y - l.pt) else (l.pt - y) / (l.pt - y - 1)

/-- Product of rational shift factors along a word `w : List Letter`. -/
def wordFactor (w : List Letter) (y : ℝ) : ℝ :=
  (w.map fun l => letterFac l y).prod

/-- Complex rational wave-word evaluation `q(y) * ∏_{l ∈ w} letterFac l y`. -/
def wordEval (q : ℝ → ℂ) (w : List Letter) (y : ℝ) : ℂ :=
  q y * ((wordFactor w y : ℝ) : ℂ)

theorem letterFac_ge (l : Letter) (y : ℝ) (h : 4 ≤ |y - l.pt|) :
    (3 : ℝ) / 4 ≤ letterFac l y := by
  unfold letterFac
  split_ifs
  · rcases le_abs'.1 h with h' | h'
    · have hneg : y - l.pt < 0 := by linarith
      rw [le_div_iff_of_neg hneg]; linarith
    · have hpos : 0 < y - l.pt := by linarith
      rw [le_div_iff₀ hpos]; linarith
  · rcases le_abs'.1 h with h' | h'
    · have hpos : 0 < l.pt - y - 1 := by linarith
      rw [le_div_iff₀ hpos]; linarith
    · have hneg : l.pt - y - 1 < 0 := by linarith
      rw [le_div_iff_of_neg hneg]; linarith

theorem letterFac_le (l : Letter) (y : ℝ) (h : 4 ≤ |y - l.pt|) :
    letterFac l y ≤ (4 : ℝ) / 3 := by
  unfold letterFac
  split_ifs
  · rcases le_abs'.1 h with h' | h'
    · have hneg : y - l.pt < 0 := by linarith
      rw [div_le_iff_of_neg hneg]; linarith
    · have hpos : 0 < y - l.pt := by linarith
      rw [div_le_iff₀ hpos]; linarith
  · rcases le_abs'.1 h with h' | h'
    · have hpos : 0 < l.pt - y - 1 := by linarith
      rw [div_le_iff₀ hpos]; linarith
    · have hneg : l.pt - y - 1 < 0 := by linarith
      rw [div_le_iff_of_neg hneg]; linarith

theorem wordFactor_ge (w : List Letter) (y : ℝ) (h : ∀ l ∈ w, 4 ≤ |y - l.pt|) :
    ((3 : ℝ) / 4) ^ w.length ≤ wordFactor w y := by
  induction w with
  | nil => simp [wordFactor]
  | cons l w ih =>
    simp only [wordFactor, List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    have h1 := letterFac_ge l y (h l List.mem_cons_self)
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    rw [mul_comm]
    exact mul_le_mul h1 h2 (by positivity) (by linarith)

theorem wordFactor_le (w : List Letter) (y : ℝ) (h : ∀ l ∈ w, 4 ≤ |y - l.pt|) :
    wordFactor w y ≤ ((4 : ℝ) / 3) ^ w.length := by
  induction w with
  | nil => simp [wordFactor]
  | cons l w ih =>
    simp only [wordFactor, List.length_cons, List.map_cons, List.prod_cons, pow_succ']
    have h1 := letterFac_le l y (h l List.mem_cons_self)
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have h2pos : 0 ≤ wordFactor w y :=
      le_trans (by positivity) (wordFactor_ge w y fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    exact mul_le_mul h1 h2 h2pos (by norm_num)

/-- Nonvanishing & explicit lower bound for rational Bessel word evaluation away from poles. -/
theorem norm_wordEval_ge (q : ℝ → ℂ) (w : List Letter) (y : ℝ)
    (h : ∀ l ∈ w, 4 ≤ |y - l.pt|) :
    ((3 : ℝ) / 4) ^ w.length * ‖q y‖ ≤ ‖wordEval q w y‖ := by
  have hwf : ((3 : ℝ) / 4) ^ w.length ≤ wordFactor w y := wordFactor_ge w y h
  have hwf0 : 0 ≤ wordFactor w y := le_trans (by positivity) hwf
  have hn : ‖((wordFactor w y : ℝ) : ℂ)‖ = wordFactor w y := by
    rw [Complex.norm_real, Real.norm_of_nonneg hwf0]
  rw [wordEval, norm_mul, hn, mul_comm (‖q y‖)]
  exact mul_le_mul_of_nonneg_right hwf (norm_nonneg (q y))

theorem wordEval_ne_zero (q : ℝ → ℂ) (w : List Letter) (y : ℝ)
    (hq : q y ≠ 0) (h : ∀ l ∈ w, 4 ≤ |y - l.pt|) :
    wordEval q w y ≠ 0 := by
  have hpos : 0 < ((3 : ℝ) / 4) ^ w.length * ‖q y‖ :=
    mul_pos (by positivity) (norm_pos_iff.mpr hq)
  exact norm_pos_iff.mp (lt_of_lt_of_le hpos (norm_wordEval_ge q w y h))

/-- Unit `ℓ¹` shift vectors in `ℤ^n` (`0` and `±e_i`) generating discrete jet/Whittaker balls. -/
def unitShifts (n : ℕ) : Finset (Fin n → ℤ) :=
  insert 0 ((Finset.univ.image fun i : Fin n => Pi.single i (1 : ℤ)) ∪
            (Finset.univ.image fun i : Fin n => Pi.single i (-1 : ℤ)))

/-- Discrete `ℓ¹` shift ball of radius `e` in `ℤ^n` built by iterated Minkowski sum. -/
def shiftBall (n : ℕ) : ℕ → Finset (Fin n → ℤ)
  | 0 => {0}
  | e + 1 => Finset.image₂ (· + ·) (shiftBall n e) (unitShifts n)

theorem sum_natAbs_le_one_of_mem_unitShifts {n : ℕ} {s : Fin n → ℤ} (hs : s ∈ unitShifts n) :
    ∑ i : Fin n, (s i).natAbs ≤ 1 := by
  simp only [unitShifts, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hs
  rcases hs with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; simp [Pi.single_eq_of_ne hbj]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; simp [Pi.single_eq_of_ne hbj]
    · intro h; exact absurd (Finset.mem_univ j) h

theorem sum_natAbs_le_of_mem_shiftBall {n : ℕ} :
    ∀ e : ℕ, ∀ ν ∈ shiftBall n e, ∑ i : Fin n, (ν i).natAbs ≤ e
  | 0, ν, h => by
    rw [shiftBall, Finset.mem_singleton] at h
    simp [h]
  | e + 1, ν, h => by
    obtain ⟨x, hx, s, hs, rfl⟩ := Finset.mem_image₂.1 h
    have h1 := sum_natAbs_le_of_mem_shiftBall e x hx
    have h2 := sum_natAbs_le_one_of_mem_unitShifts hs
    have h3 : ∑ i : Fin n, ((x + s) i).natAbs ≤
        ∑ i : Fin n, (x i).natAbs + ∑ i : Fin n, (s i).natAbs := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le (x i) (s i)
    omega

/-! ## Section 3: Discrete Bessel Wave-Grid Evaluation Operator, Separation & Test-Vector Assembly -/

/-- Discrete Bessel wave-grid evaluation linear map attached to an evaluation kernel matrix
`K : Matrix ι (Fin d) ℂ` mapping test-vector coefficients `v : Fin d → ℂ` to grid values
`(K *ᵥ v) : ι → ℂ`. -/
def waveEval {ι : Type*} {d : ℕ} (K : Matrix ι (Fin d) ℂ) : (Fin d → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  Matrix.mulVecLin K

/-- Gram / Bessel-frame operator `Kᴴ * K` associated to a finite evaluation grid `ι`. -/
def waveGram {ι : Type*} [Fintype ι] {d : ℕ} (K : Matrix ι (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Kᴴ * K

/-- Exact Parseval / Gram identity: the `ℓ²`-energy of a test vector `v` on the wave grid
equals the Hermitian Gram quadratic form `vᴴ (Kᴴ K) v`. -/
theorem waveEval_energy_eq_gram {ι : Type*} [Fintype ι] {d : ℕ}
    (K : Matrix ι (Fin d) ℂ) (v : Fin d → ℂ) :
    ∑ y : ι, ‖waveEval K v y‖ ^ 2 = (dotProduct (star v) (waveGram K *ᵥ v)).re := by
  have h1 : ∀ y : ι, ((‖(K *ᵥ v) y‖ ^ 2 : ℝ) : ℂ) = star ((K *ᵥ v) y) * (K *ᵥ v) y := by
    intro y
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hC : ((∑ y : ι, ‖(K *ᵥ v) y‖ ^ 2 : ℝ) : ℂ) =
      dotProduct (star v) ((Kᴴ * K) *ᵥ v) := by
    calc ((∑ y : ι, ‖(K *ᵥ v) y‖ ^ 2 : ℝ) : ℂ)
        = ∑ y : ι, ((‖(K *ᵥ v) y‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      _ = ∑ y : ι, star ((K *ᵥ v) y) * (K *ᵥ v) y := Finset.sum_congr rfl fun y _ => h1 y
      _ = dotProduct (star (K *ᵥ v)) (K *ᵥ v) := rfl
      _ = dotProduct (star v ᵥ* Kᴴ) (K *ᵥ v) := by rw [Matrix.star_mulVec]
      _ = dotProduct (star v) (Kᴴ *ᵥ (K *ᵥ v)) := (Matrix.dotProduct_mulVec (star v) Kᴴ (K *ᵥ v)).symm
      _ = dotProduct (star v) ((Kᴴ * K) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
  have hre := congrArg Complex.re hC
  rw [Complex.ofReal_re] at hre
  simpa [waveEval, waveGram, Matrix.mulVecLin_apply] using hre

/-- Every nonzero test vector with positive grid energy attains an explicit quantitative
lower bound at some grid evaluation point `y ∈ Y`. -/
theorem exists_grid_point_lower_bound {ι : Type*} (Y : Finset ι) (f : ι → ℂ) {c : ℝ}
    (hY : Y.Nonempty) (hc : 0 ≤ c) (hen : c ≤ ∑ y ∈ Y, ‖f y‖ ^ 2) :
    ∃ y ∈ Y, Real.sqrt (c / (Y.card : ℝ)) ≤ ‖f y‖ := by
  have hcard : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  by_contra h
  push Not at h
  have hlt : ∑ y ∈ Y, ‖f y‖ ^ 2 < ∑ _y ∈ Y, (c / (Y.card : ℝ)) := by
    apply Finset.sum_lt_sum_of_nonempty hY
    intro y hy
    have hlt' : ‖f y‖ < Real.sqrt (c / (Y.card : ℝ)) := h y hy
    calc ‖f y‖ ^ 2
        < Real.sqrt (c / (Y.card : ℝ)) ^ 2 :=
          pow_lt_pow_left₀ hlt' (norm_nonneg _) (by norm_num)
      _ = c / (Y.card : ℝ) := Real.sq_sqrt (div_nonneg hc hcard.le)
  rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hcard.ne'] at hlt
  linarith

/-- Vandermonde evaluation kernel on `d` grid nodes `nodes : Fin d → ℝ` (cast to `ℂ`). -/
def vandermondeKernel {d : ℕ} (nodes : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vandermonde fun i => (nodes i : ℂ)

/-- On any `d` pairwise distinct real evaluation nodes (in particular, any `d`-point `progY`
grid), the Vandermonde evaluation matrix has nonzero determinant. -/
theorem vandermondeKernel_det_ne_zero {d : ℕ} {nodes : Fin d → ℝ}
    (hinj : Function.Injective nodes) :
    (vandermondeKernel nodes).det ≠ 0 := by
  rw [vandermondeKernel, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [Finset.mem_Ioi] at hj
  intro hsub
  have heq : (nodes j : ℂ) = (nodes i : ℂ) := sub_eq_zero.mp hsub
  exact (ne_of_gt hj) (hinj (Complex.ofReal_injective heq))

/-- Point separation on a `d`-point grid: polynomial/jet test vectors of degree `< d` are
uniquely determined by their values on any `d` distinct evaluation nodes. -/
theorem vandermonde_waveEval_injective {d : ℕ} {nodes : Fin d → ℝ}
    (hinj : Function.Injective nodes) :
    Function.Injective (waveEval (vandermondeKernel nodes)) := by
  have hunit : IsUnit (vandermondeKernel nodes).det :=
    isUnit_iff_ne_zero.mpr (vandermondeKernel_det_ne_zero hinj)
  intro u v huv
  have h0 : vandermondeKernel nodes *ᵥ (u - v) = 0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr huv
  have hinv := congrArg (fun w => (vandermondeKernel nodes)⁻¹ *ᵥ w) h0
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
    Matrix.mulVec_zero] at hinv
  exact sub_eq_zero.mp hinv

/-- **Test-Vector Assembly (Lagrange Delta Test Vector)**: on any `d` distinct evaluation nodes
(e.g. `progY y0 d`), for every target point `i₀` and desired value `α : ℂ`, there exists an
explicit test vector `v : Fin d → ℂ` taking value `α` at `i₀` and `0` at all other grid nodes. -/
theorem exists_delta_test_vector {d : ℕ} {nodes : Fin d → ℝ}
    (hinj : Function.Injective nodes) (i₀ : Fin d) (α : ℂ) :
    ∃ v : Fin d → ℂ, ∀ i : Fin d, waveEval (vandermondeKernel nodes) v i = if i = i₀ then α else 0 := by
  have hunit : IsUnit (vandermondeKernel nodes).det :=
    isUnit_iff_ne_zero.mpr (vandermondeKernel_det_ne_zero hinj)
  let target : Fin d → ℂ := fun i => if i = i₀ then α else 0
  refine ⟨(vandermondeKernel nodes)⁻¹ *ᵥ target, fun i => ?_⟩
  show (vandermondeKernel nodes *ᵥ ((vandermondeKernel nodes)⁻¹ *ᵥ target)) i = target i
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]

/-- Specialization of test-vector assembly to the spacing-5 interlacing grid `progY y0 d`. -/
theorem exists_delta_test_vector_progY (y0 : ℝ) (d : ℕ) (i₀ : Fin d) (α : ℂ) :
    ∃ v : Fin d → ℂ, ∀ i : Fin d,
      waveEval (vandermondeKernel (fun k : Fin d => y0 + 5 * (k : ℝ))) v i =
        if i = i₀ then α else 0 := by
  apply exists_delta_test_vector
  intro i j h
  have h' : (i : ℕ) = (j : ℕ) := progY_injective y0 h
  exact Fin.ext h'

/-- **Bessel Multiplicity-One (Rank ≤ 1)**: if every functional in a subspace `S` of linear
maps/forms is a scalar multiple of a single reference Bessel functional `l`, then
`Module.finrank ℂ S ≤ 1`. -/
theorem bessel_finrank_le_one {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ (V →ₗ[ℂ] W))
    (l : V →ₗ[ℂ] W) (hmult : ∀ B ∈ S, ∃ c : ℂ, B = c • l) :
    Module.finrank ℂ S ≤ 1 := by
  by_cases hl : l = 0
  · have hbot : S = ⊥ := eq_bot_iff.mpr fun B hB => by
      obtain ⟨c, rfl⟩ := hmult B hB
      simp [hl]
    rw [hbot, finrank_bot]
    exact Nat.zero_le 1
  · have hle : S ≤ Submodule.span ℂ {l} := by
      intro B hB
      obtain ⟨c, rfl⟩ := hmult B hB
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton l))
    have hspan : Module.finrank ℂ (Submodule.span ℂ ({l} : Set (V →ₗ[ℂ] W))) = 1 :=
      finrank_span_singleton hl
    exact (Submodule.finrank_mono hle).trans hspan.le

/-- **Multiplicity-One Scalar Comparison**: if two Bessel functionals `B₁, B₂` both lie in
the multiplicity-one line `ℂ • l` and `B₁ v₀ ≠ 0` on a test vector `v₀`, then `B₂` is an
explicit scalar multiple of `B₁` everywhere. -/
theorem bessel_scalar_ratio_of_test_vector {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {l B₁ B₂ : V →ₗ[ℂ] W}
    (h1 : ∃ c₁ : ℂ, B₁ = c₁ • l) (h2 : ∃ c₂ : ℂ, B₂ = c₂ • l)
    {v₀ : V} (hv : B₁ v₀ ≠ 0) :
    ∃ c : ℂ, ∀ v : V, B₂ v = c • B₁ v := by
  obtain ⟨c₁, rfl⟩ := h1
  obtain ⟨c₂, rfl⟩ := h2
  have hc₁ : c₁ ≠ 0 := by
    intro h0
    apply hv
    simp [h0]
  refine ⟨c₂ / c₁, fun v => ?_⟩
  simp only [LinearMap.smul_apply, smul_smul, div_mul_cancel₀ _ hc₁]

/-! ## Section 4: Local-Factor Multiplicativity & Tower-Stage Norm Factorization -/

/-- A finite-place local-factor system for a theta/Bessel inner product over a finite set of
places `places : Finset ι`, separating the archimedean factor `archFactor` from the product
of finite-place local factors `localFactor v`. -/
structure LocalFactorSystem (ι : Type*) where
  places : Finset ι
  archFactor : ℂ
  localFactor : ι → ℂ
  globalValue : ℂ
  factorizes : globalValue = archFactor * ∏ v ∈ places, localFactor v

/-- Exact nonvanishing of a global theta/Bessel value from archimedean and local-factor
nonvanishing at every place in `places`. -/
theorem LocalFactorSystem.globalValue_ne_zero {ι : Type*} (L : LocalFactorSystem ι)
    (harch : L.archFactor ≠ 0) (hloc : ∀ v ∈ L.places, L.localFactor v ≠ 0) :
    L.globalValue ≠ 0 := by
  rw [L.factorizes]
  exact mul_ne_zero harch (Finset.prod_ne_zero_iff.mpr hloc)

/-- Exact norm multiplicativity across finite places:
`‖globalValue‖ = ‖archFactor‖ * ∏ v ∈ places, ‖localFactor v‖`. -/
theorem LocalFactorSystem.norm_globalValue_eq_prod {ι : Type*} (L : LocalFactorSystem ι) :
    ‖L.globalValue‖ = ‖L.archFactor‖ * ∏ v ∈ L.places, ‖L.localFactor v‖ := by
  rw [L.factorizes, norm_mul, norm_prod]

/-- **Twin Theta-Lift Local-Factor Ratio Cancellation**:
If two local-factor systems `L₁, L₂` share the same finite place set `S`, agree at the
archimedean place (`arch₁ = c_∞ * arch₂`) and agree at every unramified place `v ∉ S₀`,
while matching at each bad place `v ∈ S₀` via `local₁ v = c_v * local₂ v`, then the global
value ratio collapses to `c_∞ * ∏ v ∈ S₀, c_v` (all unramified local factors cancel!). -/
theorem local_factor_ratio_matching {ι : Type*} [DecidableEq ι]
    (L₁ L₂ : LocalFactorSystem ι) (S₀ : Finset ι)
    (hS : L₁.places = L₂.places) (hS₀ : S₀ ⊆ L₁.places)
    (cArch : ℂ) (cLoc : ι → ℂ)
    (hArch : L₁.archFactor = cArch * L₂.archFactor)
    (hBad : ∀ v ∈ S₀, L₁.localFactor v = cLoc v * L₂.localFactor v)
    (hUnram : ∀ v ∈ L₁.places \ S₀, L₁.localFactor v = L₂.localFactor v) :
    L₁.globalValue = (cArch * ∏ v ∈ S₀, cLoc v) * L₂.globalValue := by
  rw [L₁.factorizes, L₂.factorizes, ← hS, hArch]
  have hsplit₁ : ∏ v ∈ L₁.places, L₁.localFactor v =
      (∏ v ∈ S₀, L₁.localFactor v) * ∏ v ∈ L₁.places \ S₀, L₁.localFactor v := by
    rw [← Finset.prod_union disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hS₀]
  have hsplit₂ : ∏ v ∈ L₁.places, L₂.localFactor v =
      (∏ v ∈ S₀, L₂.localFactor v) * ∏ v ∈ L₁.places \ S₀, L₂.localFactor v := by
    rw [← Finset.prod_union disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hS₀]
  have hbadProd : ∏ v ∈ S₀, L₁.localFactor v =
      (∏ v ∈ S₀, cLoc v) * ∏ v ∈ S₀, L₂.localFactor v := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hBad
  have hunramProd : ∏ v ∈ L₁.places \ S₀, L₁.localFactor v =
      ∏ v ∈ L₁.places \ S₀, L₂.localFactor v :=
    Finset.prod_congr rfl hUnram
  rw [hsplit₁, hsplit₂, hbadProd, hunramProd]
  ring

/-- **Witt/Theta Tower-Stage Norm Factorization**:
Along an `m`-step tower with positive stage norms `N(0), ..., N(m)` and step multipliers
`N(j + 1) = ρ(j) * N(j)`, the top-to-bottom norm equals `N(0) * ∏_{j < m} ρ(j)`. -/
theorem tower_stage_norm_prod (N ρ : ℕ → ℝ) (hstep : ∀ j, N (j + 1) = ρ j * N j) :
    ∀ m : ℕ, N m = N 0 * ∏ j ∈ Finset.range m, ρ j
  | 0 => by simp
  | m + 1 => by
    rw [hstep m, tower_stage_norm_prod N ρ hstep m, Finset.prod_range_succ]
    ring

/-! ## Section 5: Orbit-Word Bounds, Gap-Size Margins, Grid-Frame Inequalities & `nWv` Coupling -/

/-- Exact product-of-norms upper bound along a list of matrices/operators (`ProdNormLe.lean`). -/
theorem prod_norm_le {α : Type*} [SeminormedAddCommGroup α] (W : List α) {a : ℝ}
    (h : ∀ X ∈ W, ‖X‖ ≤ a) :
    (W.map fun X => ‖X‖).prod ≤ a ^ W.length := by
  induction W with
  | nil => simp
  | cons X W ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    have h0 : 0 ≤ (W.map fun X => ‖X‖).prod := List.prod_nonneg fun x hx => by
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    exact mul_le_mul (h X List.mem_cons_self)
      (ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)) h0
      ((norm_nonneg X).trans (h X List.mem_cons_self))

/-- **Orbit Conjugation Word Bound** (`ProdNormLe.lean`):
For a conjugated operator word `P'` of length `≤ m` (with conjugation growth `≤ A * M^c`)
followed by a fixed word `R` of length `≤ c * m` (with norm `≤ A`), the concatenated word
norm product is bounded by `A ^ (m + c * m) * M ^ (c * m)`. -/
theorem orbit_word_norm_bound {α : Type*} [SeminormedAddCommGroup α]
    (P' R : List α) {A M : ℝ} {m c : ℕ}
    (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hPlen : P'.length ≤ m) (hRlen : R.length ≤ c * m)
    (hP : ∀ X ∈ P', ‖X‖ ≤ A * M ^ c) (hR : ∀ X ∈ R, ‖X‖ ≤ A) :
    ((P' ++ R).map fun X => ‖X‖).prod ≤ A ^ (m + c * m) * M ^ (c * m) := by
  rw [List.map_append, List.prod_append]
  have hMc : 1 ≤ M ^ c := one_le_pow₀ hM
  have b1 : (P'.map fun X => ‖X‖).prod ≤ (A * M ^ c) ^ m :=
    (prod_norm_le P' hP).trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hA hMc) hPlen)
  have b2 : (R.map fun X => ‖X‖).prod ≤ A ^ (c * m) :=
    (prod_norm_le R hR).trans (pow_le_pow_right₀ hA hRlen)
  have hR0 : 0 ≤ (R.map fun X => ‖X‖).prod := List.prod_nonneg fun x hx => by
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
  calc (P'.map fun X => ‖X‖).prod * (R.map fun X => ‖X‖).prod
      ≤ (A * M ^ c) ^ m * A ^ (c * m) := mul_le_mul b1 b2 hR0 (by positivity)
    _ = A ^ (m + c * m) * M ^ (c * m) := by rw [mul_pow, ← pow_mul, pow_add]; ring

/-- **Discrete-Series Gap-Size Inequalities** (`GapSizes.lean`):
Exact threshold margins `120 * N^3 ≤ Cg * (m^4 * s) * P / 4` and
`125 * m^2 * N^3 ≤ Cg * m^4 * P / 32` for Bessel multiplicity-one and wave-grid decay. -/
theorem gap_sizes_ineq {Cg m N P s : ℝ} (hCg : 1000 ≤ Cg) (hm2 : 2 ≤ m)
    (hmN : m ≤ N) (hPN : N ^ 3 ≤ P) (hs : 1 ≤ s) :
    120 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P / 4 ∧
    125 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P / 32 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hm4e : m ^ 4 = m ^ 2 * m ^ 2 := by ring
  have hm4 : (16 : ℝ) ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hm4' : 4 * m ^ 2 ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hCg0 : (0 : ℝ) ≤ Cg := by linarith
  constructor
  · have a : (16 : ℝ) ≤ m ^ 4 * s := le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)
    have b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s) := by nlinarith
    have c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
  · have b : 4000 * m ^ 2 ≤ Cg * m ^ 4 := by nlinarith
    have c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith

/-- Discrete-series spectral gap threshold `gapY k r` (`PowFourLeRpowNineHalves.lean`). -/
def gapY (k r : ℕ) : ℝ :=
  ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)

theorem pow_four_le_rpow_nine_halves (r : ℕ) :
    ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)) (by norm_num)

theorem gapY_dominates_prod (k r : ℕ) :
    ((2 * r + 2 : ℕ) : ℝ) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  mul_le_mul (pow_four_le_rpow_nine_halves r) (le_add_of_nonneg_left (by positivity))
    (by positivity) (by positivity)

/-! ### Grid-Frame Gram & Schur-Complement Norm Inequalities (feeding `LatticeFrame.lean`) -/

/-- Exact expansion of `‖∑ i, c i • φ i‖²` in any complex inner product space into its
diagonal and off-diagonal Gram contributions. -/
theorem norm_sq_sum_smul_eq_gram {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → H) (c : ι → ℂ) :
    ‖∑ i : ι, c i • φ i‖ ^ 2 =
      (∑ i : ι, ‖c i‖ ^ 2 * ‖φ i‖ ^ 2) +
      (∑ i : ι, ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re) := by
  have hsq : (‖∑ i : ι, c i • φ i‖ ^ 2 : ℝ) =
      (⟪∑ i : ι, c i • φ i, ∑ j : ι, c j • φ j⟫_ℂ).re := by
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  rw [hsq, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, Complex.re_sum]
  have hsplit : ∀ i : ι,
      ∑ j : ι, ((starRingEnd ℂ (c i)) * (c j * ⟪φ i, φ j⟫_ℂ)).re =
        ‖c i‖ ^ 2 * ‖φ i‖ ^ 2 +
        ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · rw [inner_self_eq_norm_sq_to_K, ← mul_assoc, RCLike.conj_mul]
      simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_assoc]
  simp_rw [hsplit, Finset.sum_add_distrib]

/-- **Gershgorin / Schur Off-Diagonal Quadratic Defect Bound**:
If every row's off-diagonal Gram sum satisfies `∑_{j ≠ i} ‖⟪φ i, φ j⟫‖ ≤ ρ`, then the
off-diagonal quadratic contribution is bounded in absolute value by `ρ * ∑_i ‖c i‖²`. -/
theorem gram_offDiag_abs_le_rowSum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → H) (c : ι → ℂ) {ρ : ℝ}
    (hrow : ∀ i : ι, ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ ≤ ρ) :
    |∑ i : ι, ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re| ≤
      ρ * ∑ i : ι, ‖c i‖ ^ 2 := by
  have h1 : |∑ i : ι, ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re| ≤
      ∑ i : ι, ∑ j ∈ Finset.univ.erase i, ‖c i‖ * ‖c j‖ * ‖⟪φ i, φ j⟫_ℂ‖ := by
    calc |∑ i : ι, ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re|
        ≤ ∑ i : ι, |∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : ι, ∑ j ∈ Finset.univ.erase i, |(star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : ι, ∑ j ∈ Finset.univ.erase i, ‖c i‖ * ‖c j‖ * ‖⟪φ i, φ j⟫_ℂ‖ := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          calc |(star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re|
              ≤ ‖star (c i) * c j * ⟪φ i, φ j⟫_ℂ‖ := Complex.abs_re_le_norm _
            _ = ‖c i‖ * ‖c j‖ * ‖⟪φ i, φ j⟫_ℂ‖ := by rw [norm_mul, norm_mul, norm_star]
  have hAM : ∑ i : ι, ∑ j ∈ Finset.univ.erase i, ‖c i‖ * ‖c j‖ * ‖⟪φ i, φ j⟫_ℂ‖ ≤
      ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
        ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * ‖⟪φ i, φ j⟫_ℂ‖ := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
  have hsymm :
      ∑ i : ι, ∑ j ∈ Finset.univ.erase i, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * ‖⟪φ i, φ j⟫_ℂ‖ =
      ∑ i : ι, ‖c i‖ ^ 2 * ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ := by
    have hsplit :
        ∑ i : ι, ∑ j ∈ Finset.univ.erase i, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * ‖⟪φ i, φ j⟫_ℂ‖ =
        (∑ i : ι, ∑ j ∈ Finset.univ.erase i, (‖c i‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖) +
        (∑ i : ι, ∑ j ∈ Finset.univ.erase i, (‖c j‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hswap :
        ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (‖c j‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖ =
        ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (‖c i‖ ^ 2 / 2) * ‖⟪φ i, φ j⟫_ℂ‖ := by
      have hite : ∀ f : ι → ι → ℝ,
          ∑ i : ι, ∑ j ∈ Finset.univ.erase i, f i j =
          ∑ i : ι, ∑ j : ι, if j = i then 0 else f i j := by
        intro f
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext j; simp
      rw [hite, hite, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hji : i = j
      · subst hji; simp
      · have hij : j ≠ i := Ne.symm hji
        simp only [hji, hij, ↓reduceIte]
        rw [← norm_inner_symm (φ i) (φ j)]
    rw [hsplit, hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  calc |∑ i : ι, ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re|
      ≤ ∑ i : ι, ‖c i‖ ^ 2 * ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ :=
        h1.trans (hAM.trans hsymm.le)
    _ ≤ ∑ i : ι, ‖c i‖ ^ 2 * ρ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
    _ = ρ * ∑ i : ι, ‖c i‖ ^ 2 := by rw [← Finset.sum_mul, mul_comm]

/-- **Grid-Frame Lower Norm Inequality**:
Near-orthogonal wave-grid test vectors (`dMin ≤ ‖φ i‖²` and off-diagonal Gram row sum `≤ ρ`)
satisfy the Bessel frame lower bound `(dMin - ρ) * ∑_i ‖c i‖² ≤ ‖∑_i c i • φ i‖²`. -/
theorem grid_frame_lower_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → H) (c : ι → ℂ) {dMin ρ : ℝ}
    (hdiag : ∀ i : ι, dMin ≤ ‖φ i‖ ^ 2)
    (hrow : ∀ i : ι, ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ ≤ ρ) :
    (dMin - ρ) * ∑ i : ι, ‖c i‖ ^ 2 ≤ ‖∑ i : ι, c i • φ i‖ ^ 2 := by
  rw [norm_sq_sum_smul_eq_gram]
  have h1 : dMin * ∑ i : ι, ‖c i‖ ^ 2 ≤ ∑ i : ι, ‖c i‖ ^ 2 * ‖φ i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg _)
  have h2 := (abs_le.mp (gram_offDiag_abs_le_rowSum φ c hrow)).1
  linarith

/-- **Grid-Frame Upper Norm Inequality**:
Wave-grid test vectors with `‖φ i‖² ≤ dMax` and off-diagonal Gram row sum `≤ ρ`
satisfy the Bessel frame upper bound `‖∑_i c i • φ i‖² ≤ (dMax + ρ) * ∑_i ‖c i‖²`. -/
theorem grid_frame_upper_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → H) (c : ι → ℂ) {dMax ρ : ℝ}
    (hdiag : ∀ i : ι, ‖φ i‖ ^ 2 ≤ dMax)
    (hrow : ∀ i : ι, ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ ≤ ρ) :
    ‖∑ i : ι, c i • φ i‖ ^ 2 ≤ (dMax + ρ) * ∑ i : ι, ‖c i‖ ^ 2 := by
  rw [norm_sq_sum_smul_eq_gram]
  have h1 : ∑ i : ι, ‖c i‖ ^ 2 * ‖φ i‖ ^ 2 ≤ dMax * ∑ i : ι, ‖c i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg _)
  have h2 := (abs_le.mp (gram_offDiag_abs_le_rowSum φ c hrow)).2
  linarith

/-- **Linear Independence & Rank Saturation of Diagonally-Dominant Wave-Grid Frames**:
Whenever the off-diagonal Gram row sum `ρ < dMin`, the wave-grid test-vector family `φ`
is linearly independent over `ℂ`. -/
theorem grid_frame_linearIndependent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → H) {dMin ρ : ℝ}
    (hgap : ρ < dMin)
    (hdiag : ∀ i : ι, dMin ≤ ‖φ i‖ ^ 2)
    (hrow : ∀ i : ι, ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ ≤ ρ) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hlow := grid_frame_lower_bound φ c hdiag hrow
  rw [hc, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hlow
  have hpos : 0 < dMin - ρ := sub_pos.mpr hgap
  have hsum0 : ∑ i : ι, ‖c i‖ ^ 2 ≤ 0 := by nlinarith
  have hsum_eq : ∑ i : ι, ‖c i‖ ^ 2 = 0 :=
    le_antisymm hsum0 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  intro i
  have hi0 : ‖c i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖c j‖)).mp hsum_eq i (Finset.mem_univ i)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi0)

/-- **Frobenius-Defect Gram Frame Bound** (directly feeding `LatticeFrame.lean` and
`SlopeInequality.lean`): if the off-diagonal Frobenius energy satisfies
`∑_i ∑_{j ≠ i} ‖⟪φ i, φ j⟫‖² ≤ η²` (`η ≥ 0`), then every linear combination satisfies
`(dMin - η) * ∑_i ‖c i‖² ≤ ‖∑_i c i • φ i‖² ≤ (dMax + η) * ∑_i ‖c i‖²`. -/
theorem gram_frobenius_frame_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → H) (c : ι → ℂ) {dMin dMax η : ℝ}
    (hη : 0 ≤ η)
    (hdiag_lo : ∀ i : ι, dMin ≤ ‖φ i‖ ^ 2) (hdiag_hi : ∀ i : ι, ‖φ i‖ ^ 2 ≤ dMax)
    (hfrob : ∑ i : ι, ∑ j ∈ Finset.univ.erase i, ‖⟪φ i, φ j⟫_ℂ‖ ^ 2 ≤ η ^ 2) :
    (dMin - η) * ∑ i : ι, ‖c i‖ ^ 2 ≤ ‖∑ i : ι, c i • φ i‖ ^ 2 ∧
    ‖∑ i : ι, c i • φ i‖ ^ 2 ≤ (dMax + η) * ∑ i : ι, ‖c i‖ ^ 2 := by
  have hoff :
      |∑ i : ι, ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re| ≤
        η * ∑ i : ι, ‖c i‖ ^ 2 := by
    have hstep1 :
        |∑ i : ι, ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re| ≤
          ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (‖c i‖ * ‖c j‖) * ‖⟪φ i, φ j⟫_ℂ‖ := by
      calc |∑ i : ι, ∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re|
          ≤ ∑ i : ι, |∑ j ∈ Finset.univ.erase i, (star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : ι, ∑ j ∈ Finset.univ.erase i, |(star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re| :=
            Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (‖c i‖ * ‖c j‖) * ‖⟪φ i, φ j⟫_ℂ‖ := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            calc |(star (c i) * c j * ⟪φ i, φ j⟫_ℂ).re|
                ≤ ‖star (c i) * c j * ⟪φ i, φ j⟫_ℂ‖ := Complex.abs_re_le_norm _
              _ = (‖c i‖ * ‖c j‖) * ‖⟪φ i, φ j⟫_ℂ‖ := by rw [norm_mul, norm_mul, norm_star]
    -- Cauchy-Schwarz over the product set `S = {(i, j) | j ≠ i}`
    let S : Finset (ι × ι) := Finset.univ.filter fun p => p.2 ≠ p.1
    have hsum_eq : ∀ f : ι → ι → ℝ,
        ∑ i : ι, ∑ j ∈ Finset.univ.erase i, f i j = ∑ p ∈ S, f p.1 p.2 := by
      intro f
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j; simp
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S
      (fun p => ‖c p.1‖ * ‖c p.2‖) (fun p => ‖⟪φ p.1, φ p.2⟫_ℂ‖)
    have hCsq : ∑ p ∈ S, (‖c p.1‖ * ‖c p.2‖) ^ 2 ≤ (∑ i : ι, ‖c i‖ ^ 2) ^ 2 := by
      calc ∑ p ∈ S, (‖c p.1‖ * ‖c p.2‖) ^ 2
          ≤ ∑ p : ι × ι, (‖c p.1‖ * ‖c p.2‖) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg fun p => sq_nonneg _
        _ = ∑ i : ι, ∑ j : ι, ‖c i‖ ^ 2 * ‖c j‖ ^ 2 := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_pow _ _ 2
        _ = (∑ i : ι, ‖c i‖ ^ 2) ^ 2 := by
            rw [sq, Finset.sum_mul_sum]
    have hFsq : ∑ p ∈ S, ‖⟪φ p.1, φ p.2⟫_ℂ‖ ^ 2 ≤ η ^ 2 := by
      rwa [← hsum_eq (fun i j => ‖⟪φ i, φ j⟫_ℂ‖ ^ 2)]
    have hprod_sq :
        (∑ p ∈ S, (‖c p.1‖ * ‖c p.2‖) * ‖⟪φ p.1, φ p.2⟫_ℂ‖) ^ 2 ≤
          (η * ∑ i : ι, ‖c i‖ ^ 2) ^ 2 := by
      calc (∑ p ∈ S, (‖c p.1‖ * ‖c p.2‖) * ‖⟪φ p.1, φ p.2⟫_ℂ‖) ^ 2
          ≤ (∑ p ∈ S, (‖c p.1‖ * ‖c p.2‖) ^ 2) * (∑ p ∈ S, ‖⟪φ p.1, φ p.2⟫_ℂ‖ ^ 2) := hcs
        _ ≤ (∑ i : ι, ‖c i‖ ^ 2) ^ 2 * η ^ 2 :=
            mul_le_mul hCsq hFsq (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
        _ = (η * ∑ i : ι, ‖c i‖ ^ 2) ^ 2 := by ring
    have hnonneg : 0 ≤ η * ∑ i : ι, ‖c i‖ ^ 2 :=
      mul_nonneg hη (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hstep2 : ∑ p ∈ S, (‖c p.1‖ * ‖c p.2‖) * ‖⟪φ p.1, φ p.2⟫_ℂ‖ ≤
        η * ∑ i : ι, ‖c i‖ ^ 2 :=
      le_of_sq_le_sq hprod_sq hnonneg
    rw [hsum_eq (fun i j => (‖c i‖ * ‖c j‖) * ‖⟪φ i, φ j⟫_ℂ‖)] at hstep1
    exact hstep1.trans hstep2
  rw [norm_sq_sum_smul_eq_gram]
  have hlo : dMin * ∑ i : ι, ‖c i‖ ^ 2 ≤ ∑ i : ι, ‖c i‖ ^ 2 * ‖φ i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hdiag_lo i) (sq_nonneg _)
  have hhi : ∑ i : ι, ‖c i‖ ^ 2 * ‖φ i‖ ^ 2 ≤ dMax * ∑ i : ι, ‖c i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hdiag_hi i) (sq_nonneg _)
  obtain ⟨hoff_lo, hoff_hi⟩ := abs_le.mp hoff
  exact ⟨by linarith, by linarith⟩

/-! ### Wave-Grid Multiplicity `nWv` & Chain-Rank Coupling (feeding `ThetaSlopeEngine.lean`) -/

/-- Exact divisibility of the wave-grid multiplicity `RHDirect.nWv R s` by `8`. -/
theorem eight_dvd_nWv (R : ChainRanks) (s : ScaleParams) : 8 ∣ nWv R s :=
  ⟨⌈10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8⌉₊, rfl⟩

/-- Exact two-sided envelope for the wave-grid multiplicity `RHDirect.nWv R s` in terms of
the rank/chain-length ratio `(R.f + R.f² * (R.k - 1)³ * s.L² / R.m)`. -/
theorem nWv_bounds (R : ChainRanks) (s : ScaleParams) (hk : 1 ≤ R.k) :
    10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) ≤
      (nWv R s : ℝ) ∧
    (nWv R s : ℝ) <
      10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) + 8 := by
  set X : ℝ := 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m)
  have hX0 : 0 ≤ X := by
    have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hk)
    unfold X
    positivity
  have hcast : (nWv R s : ℝ) = 8 * (⌈X / 8⌉₊ : ℝ) := by
    unfold nWv; push_cast; rfl
  rw [hcast]
  constructor
  · have hle : X / 8 ≤ (⌈X / 8⌉₊ : ℝ) := Nat.le_ceil (X / 8)
    linarith
  · have hlt : (⌈X / 8⌉₊ : ℝ) < X / 8 + 1 := Nat.ceil_lt_add_one (div_nonneg hX0 (by norm_num))
    linarith

/-- Chain-rank monotonicity and exact step increment along the `m`-step theta-lift chain. -/
theorem chainRank_mono (R : ChainRanks) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂) :
    R.chainRank j₁ ≤ R.chainRank j₂ := by
  unfold ChainRanks.chainRank
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) R.k

theorem chainRank_diff (R : ChainRanks) (j : ℕ) :
    R.chainRank j - R.chainRank 0 = j * (R.t + 1) := by
  simp [ChainRanks.chainRank]

/-- Exact wave-grid rank balance extracted from `RHDirect.RankVal s R`. -/
theorem rankVal_wave_grid_bounds {s : ScaleParams} {R : ChainRanks} (hR : RankVal s R) :
    TOv s * nWv R s ≤ R.r + R.t ∧
    R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s ∧
    s.x ^ (377 : ℝ) ≤ (TOv s : ℝ) := by
  have hbal := hR.2.2.2
  refine ⟨by omega, by omega, Nat.le_ceil _⟩

end

end RHDirect.BesselWaveGrid
