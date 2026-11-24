/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# P3 lattice-crypto campaign, wave 1: the discrete-Gaussian smoothing parameter

This file defines the Micciancio–Regev **smoothing parameter** `η_ε(Λ)` of a full-rank Euclidean
lattice and proves the Banaszczyk / Micciancio–Regev dual upper bound, entirely unconditionally on
Mathlib's native `Submodule ℤ (EuclideanSpace ℝ (Fin n))` and the already-verified Banaszczyk
tail-bound machinery of `RHDirect.Stage12BanaszczykTransference`.

Main results (cf. Micciancio–Regev, *Worst-case to Average-case Reductions based on Gaussian
Measures*, SICOMP 2007, Lemma 3.2; Peikert, *A Decade of Lattice Cryptography*, Thm 2.3.1):
* `rhoPunct_le_of_sqrt_n_div_lt` : if `√n / s < λ₁(Λ*)` then `ρ_{1/s}(Λ* \ {0}) ≤ 1/(2ⁿ−1)`;
* `eta_le_sqrt_n_div_lambda1` : `η_{1/(2ⁿ−1)}(Λ) ≤ √n / λ₁(Λ*)`.

Here `ρ_t(L) = ∑_{v∈L} exp(−π‖v‖²/t²)` is the discrete Gaussian mass (`Stage12.rho`), and
`η_ε(Λ) = inf { s > 0 : ρ_{1/s}(Λ* \ {0}) ≤ ε }`.
-/
import RHDirect.Stage12BanaszczykTransference
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

namespace RHDirect.LatticeSmoothing

open RHDirect.Stage12BanaszczykTransference RHDirect.Stage10GeometryOfNumbers
open scoped Real

/-! ### Definitions -/

/-- The punctured dual Gaussian mass `ρ_{1/s}(Λ* \ {0}) = ∑_{0≠w∈Λ*} exp(−π s²‖w‖²)`. -/
def rhoPunct {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (s : ℝ) : ℝ :=
  ∑' v : {v : dualLattice Λ // (v.1 : EuclideanSpace ℝ (Fin n)) ≠ 0},
    Real.exp (-Real.pi * s ^ 2 * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2)

/-- The smoothing parameter `η_ε(Λ) = inf { s > 0 : ρ_{1/s}(Λ* \ {0}) ≤ ε }`. -/
def eta {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (ε : ℝ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ rhoPunct Λ s ≤ ε}

/-! ### Elementary properties of the punctured mass -/

variable {n : ℕ} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))}

/-- The Gaussian-width rewrite `−π x / (1/s)² = −π s² x`. -/
private theorem exp_width_rewrite {s : ℝ} (hs : 0 < s) (x : ℝ) :
    -Real.pi * x / (1 / s) ^ 2 = -Real.pi * s ^ 2 * x := by
  field_simp [hs.ne']

theorem summable_rhoPunct {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Summable fun v : {v : dualLattice Λ // (v.1 : EuclideanSpace ℝ (Fin n)) ≠ 0} =>
      Real.exp (-Real.pi * s ^ 2 * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  have h := summable_rho (one_div_pos.mpr hs) (dualLattice Λ)
  have heq : (fun v : dualLattice Λ =>
      Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (1 / s) ^ 2)) =
      (fun v : dualLattice Λ =>
        Real.exp (-Real.pi * s ^ 2 * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
    funext v; congr 1; exact exp_width_rewrite hs _
  rw [heq] at h
  exact h.comp_injective Subtype.coe_injective

theorem rhoPunct_nonneg {s : ℝ} : 0 ≤ rhoPunct Λ s :=
  tsum_nonneg (fun v => Real.exp_nonneg _)

/-- The punctured mass is the full dual mass minus the zero term: `ρ_{1/s}(Λ*\{0}) = ρ_{1/s}(Λ*) − 1`. -/
theorem rhoPunct_eq_rho_sub_one {s : ℝ} (hs : 0 < s) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    rhoPunct Λ s = rho (1 / s) (dualLattice Λ) - 1 := by
  let f : dualLattice Λ → ℝ :=
    fun w => Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hf_sum : Summable f := by
    have h := summable_rho (one_div_pos.mpr hs) (dualLattice Λ)
    have heq : (fun v : dualLattice Λ =>
        Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (1 / s) ^ 2)) = f := by
      funext v; congr 1; exact exp_width_rewrite hs _
    rwa [← heq]
  have hf0 : f 0 = 1 := by simp [f]
  have hrho : rho (1 / s) (dualLattice Λ) = ∑' w : dualLattice Λ, f w := by
    unfold rho; congr 1; funext w; congr 1; exact exp_width_rewrite hs _
  have hsplit : ∑' w : dualLattice Λ, f w = f 0 + rhoPunct Λ s := by
    let g : dualLattice Λ → ℝ := fun w => if w = 0 then f w else 0
    let h : dualLattice Λ → ℝ := fun w => if w = 0 then 0 else f w
    have hg : Summable g :=
      Summable.of_nonneg_of_le
        (fun w => by dsimp [g, f]; split <;> positivity)
        (fun w => by
          dsimp [g, f]
          split
          · exact le_rfl
          · exact Real.exp_nonneg _) hf_sum
    have hh : Summable h :=
      Summable.of_nonneg_of_le
        (fun w => by dsimp [h, f]; split <;> positivity)
        (fun w => by
          dsimp [h, f]
          split
          · exact Real.exp_nonneg _
          · exact le_rfl) hf_sum
    have hgh : ∑' w, f w = ∑' w, g w + ∑' w, h w := by
      rw [← Summable.tsum_add hg hh]; congr 1; funext w; dsimp [g, h]; split <;> simp
    have hg0 : ∑' w : dualLattice Λ, g w = f 0 := by
      dsimp [g]; rw [tsum_ite_eq]
    have hh0 : ∑' w : dualLattice Λ, h w = rhoPunct Λ s := by
      dsimp only [h, rhoPunct]
      have hind : (fun w : dualLattice Λ => if w = 0 then 0 else f w) =
          ({w : dualLattice Λ | (w.1 : EuclideanSpace ℝ (Fin n)) ≠ 0}.indicator f) := by
        funext w; simp only [Set.indicator_apply]; by_cases hw : w = 0 <;> simp [hw]
      rw [hind, ← tsum_subtype]; dsimp only [f]; rfl
    rw [hgh, hg0, hh0]
  rw [hrho, hsplit, hf0]; ring

/-! ### The Banaszczyk tail bound in punctured-mass form -/

/-- If `√n / s < λ₁(Λ*)`, every nonzero dual vector lies outside the ball of radius `√n/s`,
so the Banaszczyk tail bound controls the *whole* punctured mass. -/
theorem rhoPunct_le_of_sqrt_n_div_lt (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hlam : Real.sqrt (n : ℝ) / s < shortestNorm (dualLattice Λ)) :
    rhoPunct Λ s ≤ 1 / ((2 : ℝ) ^ n - 1) := by
  haveI : DiscreteTopology (dualLattice Λ) := instDiscreteTopologyDualLattice Λ
  haveI : IsZLattice ℝ (dualLattice Λ) := instIsZLatticeDualLattice Λ
  have htail := banaszczyk_tail_bound_scale (dualLattice Λ) (one_div_pos.mpr hs) 0
  have hpred : ∀ v : dualLattice Λ,
      (Real.sqrt (n : ℝ) * (1 / s) < ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖) ↔
      (v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro v
    simp only [sub_zero, mul_one_div]
    constructor
    · intro h
      exact norm_pos_iff.mp (lt_of_le_of_lt (div_nonneg (Real.sqrt_nonneg _) hs.le) h)
    · intro hv
      have hle : shortestNorm (dualLattice Λ) ≤ ‖(v : EuclideanSpace ℝ (Fin n))‖ :=
        shortestNorm_le_norm (dualLattice Λ) v.2 hv
      linarith
  have hLHS : ∑' v : {v : dualLattice Λ //
      Real.sqrt (n : ℝ) * (1 / s) < ‖(v.1 : EuclideanSpace ℝ (Fin n)) - 0‖},
      Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - 0‖ ^ 2 / (1 / s) ^ 2) =
      rhoPunct Λ s := by
    let f : dualLattice Λ → ℝ :=
      fun v => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖ ^ 2 / (1 / s) ^ 2)
    let g : dualLattice Λ → ℝ :=
      fun v => Real.exp (-Real.pi * s ^ 2 * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2)
    have hfg : ∀ v, f v = g v := by
      intro v; dsimp [f, g]; congr 1
      have : ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖ = ‖(v : EuclideanSpace ℝ (Fin n))‖ := by simp
      rw [this]; exact exp_width_rewrite hs _
    have h1 : ∑' v : {v : dualLattice Λ //
        Real.sqrt (n : ℝ) * (1 / s) < ‖(v.1 : EuclideanSpace ℝ (Fin n)) - 0‖}, f v.1 =
        ∑' v : dualLattice Λ,
          {v : dualLattice Λ | Real.sqrt (n : ℝ) * (1 / s) <
            ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖}.indicator f v := by
      have heq : ∑' v : {v : dualLattice Λ //
          Real.sqrt (n : ℝ) * (1 / s) < ‖(v.1 : EuclideanSpace ℝ (Fin n)) - 0‖}, f v.1 =
          ∑' v : ({v : dualLattice Λ | Real.sqrt (n : ℝ) * (1 / s) <
            ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖} : Set (dualLattice Λ)), f v.1 :=
        (Equiv.subtypeEquivRight fun _ => Iff.rfl).tsum_eq
          (fun v : ({v : dualLattice Λ | Real.sqrt (n : ℝ) * (1 / s) <
            ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖} : Set (dualLattice Λ)) => f v.1)
      rw [heq, tsum_subtype
        ({v : dualLattice Λ | Real.sqrt (n : ℝ) * (1 / s) <
          ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖}) f]
    have h2 : rhoPunct Λ s =
        ∑' v : dualLattice Λ,
          {v : dualLattice Λ | (v : EuclideanSpace ℝ (Fin n)) ≠ 0}.indicator g v := by
      dsimp [rhoPunct]
      have heq : ∑' v : {v : dualLattice Λ // (v.1 : EuclideanSpace ℝ (Fin n)) ≠ 0},
          Real.exp (-Real.pi * s ^ 2 * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) =
          ∑' v : ({v : dualLattice Λ | (v : EuclideanSpace ℝ (Fin n)) ≠ 0} :
            Set (dualLattice Λ)), g v.1 :=
        (Equiv.subtypeEquivRight fun _ => Iff.rfl).tsum_eq
          (fun v : ({v : dualLattice Λ | (v : EuclideanSpace ℝ (Fin n)) ≠ 0} :
            Set (dualLattice Λ)) => g v.1)
      rw [heq, tsum_subtype
        ({v : dualLattice Λ | (v : EuclideanSpace ℝ (Fin n)) ≠ 0}) g]
    rw [h1, h2]
    congr 1; funext v
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hpred v, hfg v]
  have hRHS : rho (1 / s) (dualLattice Λ) = rhoPunct Λ s + 1 := by
    have := rhoPunct_eq_rho_sub_one hs (Λ := Λ)
    linarith
  rw [hLHS, hRHS] at htail
  have h2n : (1 : ℝ) < (2 : ℝ) ^ n := by
    have h := pow_lt_pow_left₀ (show (1 : ℝ) < 2 by norm_num) zero_le_one
      (Nat.pos_iff_ne_zero.mp hn)
    simpa using h
  have hclt1 : (2 : ℝ) ^ (-(n : ℝ)) < 1 := by
    rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)), Real.rpow_natCast]
    exact inv_lt_one_iff₀.mpr (Or.inr h2n)
  have hkey : rhoPunct Λ s * (1 - (2 : ℝ) ^ (-(n : ℝ))) ≤ (2 : ℝ) ^ (-(n : ℝ)) := by
    linarith
  have hden : 0 < 1 - (2 : ℝ) ^ (-(n : ℝ)) := by linarith
  have hdiv : rhoPunct Λ s ≤ (2 : ℝ) ^ (-(n : ℝ)) / (1 - (2 : ℝ) ^ (-(n : ℝ))) :=
    (le_div_iff₀ hden).mpr hkey
  have heq : (2 : ℝ) ^ (-(n : ℝ)) / (1 - (2 : ℝ) ^ (-(n : ℝ))) = 1 / ((2 : ℝ) ^ n - 1) := by
    rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)), Real.rpow_natCast]
    field_simp [show (2 : ℝ) ^ n ≠ 1 by linarith]
  rw [heq] at hdiv
  exact hdiv

/-! ### The smoothing parameter bound -/

theorem eta_le_of_rhoPunct_le {ε s : ℝ} (hs : 0 < s) (hε : rhoPunct Λ s ≤ ε) :
    eta Λ ε ≤ s := by
  have hmem : s ∈ {s : ℝ | 0 < s ∧ rhoPunct Λ s ≤ ε} := ⟨hs, hε⟩
  have hbdd : BddBelow {s : ℝ | 0 < s ∧ rhoPunct Λ s ≤ ε} := by
    use 0; intro y hy; exact le_of_lt hy.1
  exact csInf_le hbdd hmem

/-- **Banaszczyk–Micciancio–Regev smoothing bound (dual form).**
`η_{1/(2ⁿ−1)}(Λ) ≤ √n / λ₁(Λ*)`. -/
theorem eta_le_sqrt_n_div_lambda1 (hn : 0 < n) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    eta Λ (1 / ((2 : ℝ) ^ n - 1)) ≤ Real.sqrt (n : ℝ) / shortestNorm (dualLattice Λ) := by
  have hlampos : 0 < shortestNorm (dualLattice Λ) := shortestNorm_pos hn (dualLattice Λ)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hs : 0 < Real.sqrt (n : ℝ) / shortestNorm (dualLattice Λ) + δ := by positivity
  have hlam : Real.sqrt (n : ℝ) / (Real.sqrt (n : ℝ) / shortestNorm (dualLattice Λ) + δ) <
      shortestNorm (dualLattice Λ) := by
    have hgt : Real.sqrt (n : ℝ) / shortestNorm (dualLattice Λ) + δ >
        Real.sqrt (n : ℝ) / shortestNorm (dualLattice Λ) := by linarith
    calc Real.sqrt (n : ℝ) / (Real.sqrt (n : ℝ) / shortestNorm (dualLattice Λ) + δ)
        < Real.sqrt (n : ℝ) / (Real.sqrt (n : ℝ) / shortestNorm (dualLattice Λ)) := by
          gcongr
      _ = shortestNorm (dualLattice Λ) := by
          field_simp [hsqrt.ne', hlampos.ne']
  have hbound := rhoPunct_le_of_sqrt_n_div_lt hn hs hlam
  exact eta_le_of_rhoPunct_le hs hbound

end RHDirect.LatticeSmoothing
