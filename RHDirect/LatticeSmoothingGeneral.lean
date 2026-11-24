/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# P4 lattice-crypto campaign, wave 2a: general-ε smoothing bounds

Builds on the wave-1 dual smoothing bound (`RHDirect.LatticeSmoothing`) and the verified
Banaszczyk / Poisson machinery of `RHDirect.Stage12BanaszczykTransference`.

Main results (Micciancio–Regev, SICOMP 2007, Lemma 3.2 corollary; GPV08 §2.3;
Peikert, *A Decade of Lattice Cryptography*, Thm 2.3.1 dual form):
* `rhoPunct_scale_le` : for `0 < s₀ ≤ s`,
  `ρ_{1/s}(Λ*\{0}) ≤ exp(−π(s²−s₀²)·λ₁(Λ*)²) · ρ_{1/s₀}(Λ*\{0})`;
* `eta_le_sqrt_n_add_log_div_lambda1` : for `0 < ε ≤ 1`,
  `η_ε(Λ) ≤ √(n + ln(1/ε)/π) / λ₁(Λ*)`.

All statements are on Mathlib's native `Submodule ℤ (EuclideanSpace ℝ (Fin n))` with
`[DiscreteTopology Λ] [IsZLattice ℝ Λ]`, unconditionally.
-/
import RHDirect.LatticeSmoothing
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace RHDirect.LatticeSmoothingGeneral

open RHDirect.LatticeSmoothing RHDirect.Stage12BanaszczykTransference
  RHDirect.Stage10GeometryOfNumbers
open MeasureTheory
open scoped Real

variable {n : ℕ} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))}

/-! ### Nonnegativity of the shortest norm (all dimensions, no lattice hypotheses) -/

/-- `shortestNorm Λ ≥ 0` for every `Λ` (it is an infimum of norms; `sInf ∅ = 0`). -/
theorem shortestNorm_nonneg (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    0 ≤ shortestNorm Λ := by
  unfold shortestNorm
  by_cases hne : {r : ℝ | ∃ v ∈ Λ, v ≠ 0 ∧ ‖(v : EuclideanSpace ℝ (Fin n))‖ = r}.Nonempty
  · refine le_csInf hne ?_
    rintro _ ⟨v, _, _, rfl⟩
    exact norm_nonneg _
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sInf_empty]

/-! ### Gaussian-width scaling of the punctured dual mass -/

/-- Termwise Gaussian scaling identity:
`exp(−π s² x) = exp(−π(s²−s₀²)x) · exp(−π s₀² x)`. -/
private theorem exp_scale_split {s₀ s : ℝ} (x : ℝ) :
    Real.exp (-Real.pi * s ^ 2 * x) =
      Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * x) *
        Real.exp (-Real.pi * s₀ ^ 2 * x) := by
  rw [← Real.exp_add]; congr 1; ring

/-- **Punctured-mass scaling inequality.** For `0 < s₀ ≤ s`,
`ρ_{1/s}(Λ*\{0}) ≤ exp(−π(s²−s₀²)·λ₁(Λ*)²) · ρ_{1/s₀}(Λ*\{0})`.
Every nonzero dual vector has norm `≥ λ₁(Λ*)`, so widening the Gaussian from `s₀` to `s`
costs at least the factor `exp(−π(s²−s₀²)λ₁²)` on each term. -/
theorem rhoPunct_scale_le {s₀ s : ℝ} (hs₀ : 0 < s₀) (hle : s₀ ≤ s)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    rhoPunct Λ s ≤
      Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) *
        shortestNorm (dualLattice Λ) ^ 2) * rhoPunct Λ s₀ := by
  have hs : 0 < s := lt_of_lt_of_le hs₀ hle
  have hlam_nn : 0 ≤ shortestNorm (dualLattice Λ) := shortestNorm_nonneg _
  have hterm : ∀ v : {v : dualLattice Λ // (v.1 : EuclideanSpace ℝ (Fin n)) ≠ 0},
      Real.exp (-Real.pi * s ^ 2 * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * shortestNorm (dualLattice Λ) ^ 2) *
          Real.exp (-Real.pi * s₀ ^ 2 * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    intro v
    rw [exp_scale_split]
    have hnorm : shortestNorm (dualLattice Λ) ≤ ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ :=
      shortestNorm_le_norm (dualLattice Λ) v.1.2 v.2
    have hsq : shortestNorm (dualLattice Λ) ^ 2 ≤ ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      pow_le_pow_left₀ hlam_nn hnorm 2
    have hdiff : 0 ≤ s ^ 2 - s₀ ^ 2 := by
      have : s₀ ^ 2 ≤ s ^ 2 := by gcongr
      linarith
    have hexp : Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * shortestNorm (dualLattice Λ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hcoef : 0 ≤ Real.pi * (s ^ 2 - s₀ ^ 2) := by positivity
      linarith [mul_le_mul_of_nonneg_left hsq hcoef]
    exact mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)
  have hsum₁ : Summable fun v : {v : dualLattice Λ // (v.1 : EuclideanSpace ℝ (Fin n)) ≠ 0} =>
      Real.exp (-Real.pi * s ^ 2 * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) :=
    summable_rhoPunct hs
  have hsum₂ : Summable fun v : {v : dualLattice Λ // (v.1 : EuclideanSpace ℝ (Fin n)) ≠ 0} =>
      Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * shortestNorm (dualLattice Λ) ^ 2) *
        Real.exp (-Real.pi * s₀ ^ 2 * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) :=
    (summable_rhoPunct hs₀).mul_left _
  calc rhoPunct Λ s
      ≤ ∑' v : {v : dualLattice Λ // (v.1 : EuclideanSpace ℝ (Fin n)) ≠ 0},
          Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * shortestNorm (dualLattice Λ) ^ 2) *
            Real.exp (-Real.pi * s₀ ^ 2 * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) :=
        hsum₁.tsum_le_tsum hterm hsum₂
    _ = Real.exp (-Real.pi * (s ^ 2 - s₀ ^ 2) * shortestNorm (dualLattice Λ) ^ 2) *
        rhoPunct Λ s₀ := by
        rw [tsum_mul_left]; rfl

/-! ### Antitonicity of the punctured mass -/

/-- **A1.** The punctured dual Gaussian mass is antitone in the width:
`0 < s₁ ≤ s₂ → ρ_{1/s₂}(Λ*\{0}) ≤ ρ_{1/s₁}(Λ*\{0})`. -/
theorem rhoPunct_antitone {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (h : s₁ ≤ s₂)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    rhoPunct Λ s₂ ≤ rhoPunct Λ s₁ := by
  have hscale := rhoPunct_scale_le (Λ := Λ) hs₁ h
  have hsq : s₁ ^ 2 ≤ s₂ ^ 2 := by gcongr
  have hnn : 0 ≤ Real.pi * (s₂ ^ 2 - s₁ ^ 2) * shortestNorm (dualLattice Λ) ^ 2 :=
    mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (by linarith)) (sq_nonneg _)
  have hexp : Real.exp (-Real.pi * (s₂ ^ 2 - s₁ ^ 2) * shortestNorm (dualLattice Λ) ^ 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith
  calc rhoPunct Λ s₂
      ≤ Real.exp (-Real.pi * (s₂ ^ 2 - s₁ ^ 2) * shortestNorm (dualLattice Λ) ^ 2) *
          rhoPunct Λ s₁ := hscale
    _ ≤ 1 * rhoPunct Λ s₁ :=
        mul_le_mul_of_nonneg_right hexp rhoPunct_nonneg
    _ = rhoPunct Λ s₁ := one_mul _

/-! ### General-ε dual smoothing bound -/

/-- **A3. General-ε dual smoothing bound** (Micciancio–Regev Lemma 3.2 corollary).
For `0 < ε < 1/(2ⁿ−1)`,
`η_ε(Λ) ≤ √(n + ln(1/(ε(2ⁿ−1)))/π) / λ₁(Λ*)`.

Proof: scale the wave-1 core bound `ρ_{1/s₀}(Λ*\{0}) ≤ 1/(2ⁿ−1)` (valid for `s₀ > √n/λ₁`)
up to `s = S + δ` using `rhoPunct_scale_le`, choosing `s₀` just above `√n/λ₁` so that the
Gaussian decay factor supplies exactly `ε`; then let `δ → 0`. -/
theorem eta_le_sqrt_scaling (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ε : ℝ} (hε : 0 < ε) (hεlt : ε < 1 / ((2 : ℝ) ^ n - 1)) :
    eta Λ ε ≤
      Real.sqrt ((n : ℝ) + Real.log (1 / (ε * ((2 : ℝ) ^ n - 1))) / Real.pi) /
        shortestNorm (dualLattice Λ) := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  set L := shortestNorm (dualLattice Λ) with hLdef
  have hL : 0 < L := shortestNorm_pos hn (dualLattice Λ)
  have h2n : (1 : ℝ) < (2 : ℝ) ^ n := by
    have := pow_lt_pow_left₀ (show (1 : ℝ) < 2 by norm_num) zero_le_one
      (Nat.pos_iff_ne_zero.mp hn)
    simpa using this
  have hden : 0 < (2 : ℝ) ^ n - 1 := by linarith
  set a := Real.log (1 / (ε * ((2 : ℝ) ^ n - 1))) with hadef
  have hprod : ε * ((2 : ℝ) ^ n - 1) < 1 := by
    rwa [lt_div_iff₀ hden] at hεlt
  have ha_pos : 0 < a := by
    apply Real.log_pos
    rw [lt_div_iff₀ (mul_pos hε hden)]
    linarith
  set S := Real.sqrt ((n : ℝ) + a / Real.pi) / L with hSdef
  have hS_pos : 0 < S := by
    apply div_pos (Real.sqrt_pos.mpr _) hL
    positivity
  apply le_of_forall_pos_le_add
  intro δ hδ
  set s' := S + δ with hs'def
  have hs' : 0 < s' := by positivity
  apply eta_le_of_rhoPunct_le hs'
  set slack := Real.pi * (s' ^ 2 - S ^ 2) * L ^ 2 with hslackdef
  have hslack : 0 < slack := by
    have hSlt : S < s' := by dsimp [s']; linarith
    have hSsq : S ^ 2 < s' ^ 2 := pow_lt_pow_left₀ hSlt (le_of_lt hS_pos) (by norm_num)
    have : 0 < s' ^ 2 - S ^ 2 := by linarith
    positivity
  set s₀ := Real.sqrt ((n : ℝ) + slack / (2 * Real.pi)) / L with hs₀def
  have hs₀_pos : 0 < s₀ := by
    apply div_pos (Real.sqrt_pos.mpr _) hL
    positivity
  -- exact square identities (all square-root arguments are nonnegative)
  have hS2 : S ^ 2 * L ^ 2 = (n : ℝ) + a / Real.pi := by
    have hnn : 0 ≤ (n : ℝ) + a / Real.pi := by positivity
    dsimp [S]; rw [div_pow, Real.sq_sqrt hnn]; field_simp
  have h1 : s₀ ^ 2 * L ^ 2 = (n : ℝ) + slack / (2 * Real.pi) := by
    have hnn : 0 ≤ (n : ℝ) + slack / (2 * Real.pi) := by positivity
    dsimp [s₀]; rw [div_pow, Real.sq_sqrt hnn]; field_simp
  have hslackπ : slack / Real.pi = (s' ^ 2 - S ^ 2) * L ^ 2 := by
    dsimp [slack]; field_simp
  have h2 : s' ^ 2 * L ^ 2 = (n : ℝ) + a / Real.pi + slack / Real.pi := by
    calc s' ^ 2 * L ^ 2 = S ^ 2 * L ^ 2 + (s' ^ 2 - S ^ 2) * L ^ 2 := by ring
      _ = (n : ℝ) + a / Real.pi + slack / Real.pi := by rw [hS2, hslackπ]
  have hs₀_gt : Real.sqrt (n : ℝ) / s₀ < L := by
    rw [div_lt_iff₀ hs₀_pos]
    have hLs₀ : L * s₀ = Real.sqrt ((n : ℝ) + slack / (2 * Real.pi)) := by
      dsimp [s₀]; field_simp
    rw [hLs₀]
    apply Real.sqrt_lt_sqrt (by positivity)
    have : 0 < slack / (2 * Real.pi) := by positivity
    linarith
  have hs₀_le_s' : s₀ ≤ s' := by
    have hsq : s₀ ^ 2 ≤ s' ^ 2 := by
      have : s₀ ^ 2 * L ^ 2 ≤ s' ^ 2 * L ^ 2 := by
        rw [h1, h2]
        have haπ : 0 ≤ a / Real.pi := by positivity
        have hfrac : slack / (2 * Real.pi) ≤ slack / Real.pi := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hπ : Real.pi ≤ 2 * Real.pi := by linarith [Real.pi_pos]
          exact mul_le_mul_of_nonneg_left hπ (le_of_lt hslack)
        nlinarith
      exact le_of_mul_le_mul_right this (pow_pos hL 2)
    by_contra hnot
    push Not at hnot
    have : s' ^ 2 < s₀ ^ 2 := pow_lt_pow_left₀ hnot (le_of_lt hs') (by norm_num)
    linarith
  have hcore := rhoPunct_le_of_sqrt_n_div_lt (Λ := Λ) hn hs₀_pos hs₀_gt
  have hscale := rhoPunct_scale_le (Λ := Λ) hs₀_pos hs₀_le_s'
  have hkey : Real.pi * (s' ^ 2 - s₀ ^ 2) * L ^ 2 = a + slack / 2 := by
    have : Real.pi * (s' ^ 2 - s₀ ^ 2) * L ^ 2 =
        Real.pi * (s' ^ 2 * L ^ 2 - s₀ ^ 2 * L ^ 2) := by ring
    rw [this, h2, h1]
    field_simp; ring
  calc rhoPunct Λ s'
      ≤ Real.exp (-Real.pi * (s' ^ 2 - s₀ ^ 2) * L ^ 2) * rhoPunct Λ s₀ := hscale
    _ ≤ Real.exp (-Real.pi * (s' ^ 2 - s₀ ^ 2) * L ^ 2) * (1 / ((2 : ℝ) ^ n - 1)) :=
        mul_le_mul_of_nonneg_left hcore (Real.exp_nonneg _)
    _ = Real.exp (-(a + slack / 2)) * Real.exp (-Real.log ((2 : ℝ) ^ n - 1)) := by
        have hneg : -Real.pi * (s' ^ 2 - s₀ ^ 2) * L ^ 2 = -(a + slack / 2) := by
          rw [show -Real.pi * (s' ^ 2 - s₀ ^ 2) * L ^ 2 =
            -(Real.pi * (s' ^ 2 - s₀ ^ 2) * L ^ 2) by ring]
          rw [hkey]
        rw [hneg]
        have hinv : 1 / ((2 : ℝ) ^ n - 1) = Real.exp (-Real.log ((2 : ℝ) ^ n - 1)) := by
          rw [Real.exp_neg, Real.exp_log hden]; field_simp
        rw [hinv]
    _ = Real.exp (-(a + slack / 2) - Real.log ((2 : ℝ) ^ n - 1)) := by
        have hsub : -(a + slack / 2) - Real.log ((2 : ℝ) ^ n - 1) =
            -(a + slack / 2) + -Real.log ((2 : ℝ) ^ n - 1) := by ring
        rw [hsub, ← Real.exp_add]
    _ ≤ ε := by
        have haε : a + Real.log ((2 : ℝ) ^ n - 1) = -Real.log ε := by
          dsimp [a]
          have hmul := (Real.log_mul (x := 1 / (ε * ((2 : ℝ) ^ n - 1)))
            (y := ((2 : ℝ) ^ n - 1)) (ne_of_gt (by positivity)) (ne_of_gt hden)).symm
          rw [hmul]
          have hsimp : (1 / (ε * ((2 : ℝ) ^ n - 1))) * ((2 : ℝ) ^ n - 1) = 1 / ε := by
            field_simp
          rw [hsimp, one_div, Real.log_inv]
        have hlog : -(a + slack / 2) - Real.log ((2 : ℝ) ^ n - 1) ≤ Real.log ε := by
          have hslack2 : 0 ≤ slack / 2 := by positivity
          linarith [haε]
        calc Real.exp (-(a + slack / 2) - Real.log ((2 : ℝ) ^ n - 1))
            ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr hlog
          _ = ε := Real.exp_log hε

/-! ### The nonzero dual Fourier error term and the GPV shift-mass sandwich -/

/-- The nonzero dual Fourier error term
`E_s(u) = ∑_{0≠w∈Λ*} cos(2π⟪w,u⟫)·exp(−πs²‖w‖²)`. -/
def dualErr {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (s : ℝ)
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑' w : {w : dualLattice Λ // (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0},
    Real.cos (2 * Real.pi * inner ℝ (w.1 : EuclideanSpace ℝ (Fin n)) u) *
      Real.exp (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)

/-- Summability of the dual error term. -/
theorem summable_dualErr {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (u : EuclideanSpace ℝ (Fin n)) :
    Summable fun w : {w : dualLattice Λ // (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0} =>
      Real.cos (2 * Real.pi * inner ℝ (w.1 : EuclideanSpace ℝ (Fin n)) u) *
        Real.exp (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
  refine Summable.of_norm_bounded (summable_rhoPunct (Λ := Λ) hs) (fun w => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  nlinarith [Real.abs_cos_le_one (2 * Real.pi * inner ℝ (w.1 : EuclideanSpace ℝ (Fin n)) u),
    Real.exp_nonneg (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)]

/-- The error term is bounded by the punctured dual mass: `|E_s(u)| ≤ ρ_{1/s}(Λ*\{0})`. -/
theorem abs_dualErr_le_rhoPunct {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (u : EuclideanSpace ℝ (Fin n)) :
    |dualErr Λ s u| ≤ rhoPunct Λ s := by
  have h1 : |dualErr Λ s u| ≤
      ∑' w : {w : dualLattice Λ // (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0},
        |Real.cos (2 * Real.pi * inner ℝ (w.1 : EuclideanSpace ℝ (Fin n)) u) *
          Real.exp (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)| := by
    have := norm_tsum_le_tsum_norm (summable_dualErr (Λ := Λ) hs u).norm
    simpa only [dualErr, Real.norm_eq_abs] using this
  have h2 : ∑' w : {w : dualLattice Λ // (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0},
        |Real.cos (2 * Real.pi * inner ℝ (w.1 : EuclideanSpace ℝ (Fin n)) u) *
          Real.exp (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)| ≤
      rhoPunct Λ s := by
    have hterm : ∀ w : {w : dualLattice Λ // (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0},
        |Real.cos (2 * Real.pi * inner ℝ (w.1 : EuclideanSpace ℝ (Fin n)) u) *
          Real.exp (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)| ≤
        Real.exp (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
      intro w
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      nlinarith [Real.abs_cos_le_one (2 * Real.pi * inner ℝ (w.1 : EuclideanSpace ℝ (Fin n)) u),
        Real.exp_nonneg (-Real.pi * s ^ 2 * ‖(w.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)]
    exact (summable_dualErr (Λ := Λ) hs u).abs.tsum_le_tsum hterm
      (summable_rhoPunct (Λ := Λ) hs)
  linarith

/-- Poisson rewrite of the shifted mass: `ρ_s(Λ−u) = (sⁿ/covol Λ)·(1 + E_s(u))`. -/
theorem rhoShift_eq_one_add_dualErr {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (u : EuclideanSpace ℝ (Fin n)) :
    rhoShift s Λ u =
      (s ^ n / ZLattice.covolume Λ volume) * (1 + dualErr Λ s u) := by
  rw [rhoShift_poisson_summation Λ hs u]
  congr 1
  let f : dualLattice Λ → ℝ :=
    fun w => Real.cos (2 * Real.pi * inner ℝ (w : EuclideanSpace ℝ (Fin n)) u) *
      Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hsum_exp : Summable fun w : dualLattice Λ =>
      Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    have hsum := summable_rho (one_div_pos.mpr hs) (dualLattice Λ)
    have heq : (fun w : dualLattice Λ =>
        Real.exp (-Real.pi * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (1 / s) ^ 2)) =
        (fun w : dualLattice Λ =>
          Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
      funext w; congr 1; field_simp [hs.ne']
    rwa [← heq]
  have hf_sum : Summable f := by
    refine Summable.of_norm_bounded hsum_exp (fun w => ?_)
    dsimp only [f]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    nlinarith [Real.abs_cos_le_one (2 * Real.pi * inner ℝ (w : EuclideanSpace ℝ (Fin n)) u),
      Real.exp_nonneg (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2)]
  have hf0 : f 0 = 1 := by simp [f]
  have hh0 : ∑' w : dualLattice Λ, (if w = 0 then 0 else f w) = dualErr Λ s u := by
    dsimp only [dualErr]
    have hind : (fun w : dualLattice Λ => if w = 0 then 0 else f w) =
        ({w : dualLattice Λ | (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0}.indicator f) := by
      funext w; simp only [Set.indicator_apply]; by_cases hw : w = 0 <;> simp [hw]
    rw [hind, ← tsum_subtype]
    dsimp only [f]
    rfl
  have hsplit : ∑' w : dualLattice Λ, f w = 1 + dualErr Λ s u := by
    rw [hf_sum.tsum_eq_add_tsum_ite 0, hh0, hf0]
  exact hsplit

/-- Poisson rewrite of the centered mass: `ρ_s(Λ) = (sⁿ/covol Λ)·(1 + ρ_{1/s}(Λ*\{0}))`. -/
theorem rho_eq_one_add_rhoPunct {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    rho s Λ = (s ^ n / ZLattice.covolume Λ volume) * (1 + rhoPunct Λ s) := by
  rw [rho_poisson_summation Λ hs]
  congr 1
  have := rhoPunct_eq_rho_sub_one (Λ := Λ) hs
  linarith

/-- **A6. GPV08 Lemma 2.6 (lower ratio).** If `ρ_{1/s}(Λ*\{0}) ≤ ε` with `0 < ε < 1`, then for
every shift `u`, `(1−ε)/(1+ε)·ρ_s(Λ) ≤ ρ_s(Λ−u)`. (The upper ratio `ρ_s(Λ−u) ≤ ρ_s(Λ)` is
Stage12's `rhoShift_le_rho`.) -/
theorem rhoShift_ge_ratio_mul_rho (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (hε1 : ε < 1)
    (hsmooth : rhoPunct Λ s ≤ ε) (u : EuclideanSpace ℝ (Fin n)) :
    (1 - ε) / (1 + ε) * rho s Λ ≤ rhoShift s Λ u := by
  have hE : |dualErr Λ s u| ≤ ε :=
    (abs_dualErr_le_rhoPunct (Λ := Λ) hs u).trans hsmooth
  have hEge : -ε ≤ dualErr Λ s u := (abs_le.mp hE).1
  have hshift := rhoShift_eq_one_add_dualErr (Λ := Λ) hs u
  have hcenter := rho_eq_one_add_rhoPunct (Λ := Λ) hs
  rw [hshift, hcenter]
  set F := s ^ n / ZLattice.covolume Λ volume with hFdef
  have hF : 0 < F := by
    dsimp [F]; apply div_pos (pow_pos hs n) (ZLattice.covolume_pos Λ volume)
  have h1ε : 0 < 1 + ε := by linarith
  have hrat : (1 + rhoPunct Λ s) / (1 + ε) ≤ 1 := by
    apply (div_le_iff₀ h1ε).mpr
    nlinarith [rhoPunct_nonneg (Λ := Λ) (s := s)]
  calc (1 - ε) / (1 + ε) * (F * (1 + rhoPunct Λ s))
      = F * (1 - ε) * ((1 + rhoPunct Λ s) / (1 + ε)) := by ring
    _ ≤ F * (1 - ε) * 1 := by
        apply mul_le_mul_of_nonneg_left hrat
        positivity
    _ = F * (1 - ε) := by ring
    _ ≤ F * (1 + dualErr Λ s u) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hF)
        linarith

/-- **A7. GPV08 Lemma 2.8 (discrete-Gaussian tail, tsum form).** If `ρ_{1/s}(Λ*\{0}) ≤ ε`
with `0 < ε < 1`, then for every center `c`,
`∑_{v∈Λ, √n·s < ‖v−c‖} exp(−π‖v−c‖²/s²) ≤ ((1+ε)/(1−ε))·2⁻ⁿ·ρ_s(Λ−c)`. -/
theorem discreteGaussian_tail_le (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (hε1 : ε < 1)
    (hsmooth : rhoPunct Λ s ≤ ε) (c : EuclideanSpace ℝ (Fin n)) :
    ∑' v : {v : Λ // Real.sqrt (n : ℝ) * s < ‖(v.1 : EuclideanSpace ℝ (Fin n)) - c‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - c‖ ^ 2 / s ^ 2) ≤
      (1 + ε) / (1 - ε) * (2 : ℝ) ^ (-(n : ℝ)) * rhoShift s Λ c := by
  have htail := banaszczyk_tail_bound_scale Λ hs c
  have hA6 := rhoShift_ge_ratio_mul_rho (Λ := Λ) hn hs hε hε1 hsmooth c
  have hrho_le : rho s Λ ≤ (1 + ε) / (1 - ε) * rhoShift s Λ c := by
    have hcoef : 0 < (1 - ε) / (1 + ε) := by apply div_pos <;> linarith
    have hdiv : (1 + ε) / (1 - ε) * rhoShift s Λ c =
        rhoShift s Λ c / ((1 - ε) / (1 + ε)) := by field_simp
    rw [hdiv]
    apply (le_div_iff₀ hcoef).mpr
    linarith
  calc ∑' v : {v : Λ // Real.sqrt (n : ℝ) * s < ‖(v.1 : EuclideanSpace ℝ (Fin n)) - c‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - c‖ ^ 2 / s ^ 2)
      ≤ (2 : ℝ) ^ (-(n : ℝ)) * rho s Λ := htail
    _ ≤ (2 : ℝ) ^ (-(n : ℝ)) * ((1 + ε) / (1 - ε) * rhoShift s Λ c) := by
        gcongr
    _ = (1 + ε) / (1 - ε) * (2 : ℝ) ^ (-(n : ℝ)) * rhoShift s Λ c := by ring

/-! ### The discrete Gaussian distribution (probability mass function) on a lattice -/

/-- The **discrete Gaussian probability mass function** on `Λ` with width `s > 0` and center `c`:
`D_{Λ,s,c}(v) = exp(−π‖v−c‖²/s²) / ρ_s(Λ−c)`. This is the native Mathlib formulation of the
discrete Gaussian distribution used in lattice cryptography (GPV08 / Micciancio–Regev). -/
def dGaussian {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (s : ℝ)
    (c : EuclideanSpace ℝ (Fin n)) (v : Λ) : ℝ :=
  Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - c‖ ^ 2 / s ^ 2) / rhoShift s Λ c

/-- The discrete Gaussian mass function is nonnegative. -/
theorem dGaussian_nonneg {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ]
    (c : EuclideanSpace ℝ (Fin n)) (v : Λ) : 0 ≤ dGaussian Λ s c v :=
  div_nonneg (Real.exp_nonneg _) (le_of_lt (rhoShift_pos hs Λ c))

/-- The discrete Gaussian mass function sums to `1` (it is a probability distribution on `Λ`). -/
theorem tsum_dGaussian {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ]
    (c : EuclideanSpace ℝ (Fin n)) :
    ∑' v : Λ, dGaussian Λ s c v = 1 := by
  have hne : rhoShift s Λ c ≠ 0 := ne_of_gt (rhoShift_pos hs Λ c)
  have h : (fun v : Λ => dGaussian Λ s c v) =
      (fun v : Λ => (rhoShift s Λ c)⁻¹ *
        Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - c‖ ^ 2 / s ^ 2)) := by
    funext v; dsimp [dGaussian]; ring
  rw [h, tsum_mul_left]
  have hrho : (∑' v : Λ,
      Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - c‖ ^ 2 / s ^ 2)) =
      rhoShift s Λ c := rfl
  rw [hrho]
  field_simp

/-- Each discrete Gaussian probability is at most `1`. -/
theorem dGaussian_le_one {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ]
    (c : EuclideanSpace ℝ (Fin n)) (v : Λ) : dGaussian Λ s c v ≤ 1 := by
  have hsum := summable_rhoShift hs Λ c
  have hle : Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - c‖ ^ 2 / s ^ 2) ≤
      rhoShift s Λ c :=
    hsum.le_tsum v (fun _ _ => (Real.exp_pos _).le)
  exact (div_le_one (rhoShift_pos hs Λ c)).mpr hle

end RHDirect.LatticeSmoothingGeneral
