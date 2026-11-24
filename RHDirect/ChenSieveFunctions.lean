import RHDirect.ChenDefs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# RHDirect.ChenSieveFunctions

Existence and exact properties of the normalized linear-sieve (`β = 2`) limit functions
`(chenF, chenf)` satisfying `RHDirect.Chen.LinearSievePair chenF chenf`, together with
Chen's exact positive numerical margin theorem `chen_margin_pos`.

## Construction overview (no `e^γ`, no Laplace transforms)
1. Define unnormalized functions `(chenF₀, chenf₀)` by structural recursion on `n : ℕ`
   via `pairAux n` (stabilized on `(-∞, n + 2]`):
   - Base `n = 0`: `F₀(s) = 1 / s` on `(0, 2]` (`0` for `s ≤ 0`), `f₀(s) = 0`.
   - Step `n → n + 1` (`k = n + 2`): for `s > k`,
     `F(s) = (k * F(k) + ∫ u in k..s, f(u - 1)) / s`,
     `f(s) = (k * f(k) + ∫ u in k..s, F(u - 1)) / s`.
2. Prove continuity on `Set.Ioi 0`, global Buchstab integral equations on `[2, ∞)`, and
   closed forms `chenF₀ s = 1 / s` on `(0, 3]` and `chenf₀ s = Real.log (s - 1) / s` on `[2, 4]`.
3. Prove the exact adjoint invariant `s * (s - 1) * (chenF₀ s - chenf₀ s) = ∫ t in (s - 1)..s, t * (chenF₀ t - chenf₀ t)`
   for `s ≥ 2`, which immediately implies `chenf₀ s < chenF₀ s` for all `s > 0`, and from
   the ODE derivatives implies `chenF₀` is antitone and `chenf₀` is monotone on `Set.Ioi 0`.
4. Normalize by `chenL₀ := sInf (chenF₀ '' Set.Ioi 0) ∈ [Real.log 3 / 4, 1 / 3]` to obtain
   `chenF s = chenF₀ s / chenL₀` and `chenf s = chenf₀ s / chenL₀` satisfying `LinearSievePair`.
5. Prove `chenIB < 37 / 100` (via the Padé upper bound `log(1 + y) ≤ y(6 + y)/(6 + 4y)` and
   closed-form partial-fraction integration), `40 / 100 < log (3 / 2)`, `chen_T2_integral_eq`,
   and `chen_margin_pos`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

open scoped Topology
open Filter Set MeasureTheory intervalIntegral

namespace RHDirect.Chen

/-! ### Section 1: Auxiliary Calculus & Gluing Helpers -/

private lemma continuousOn_ite_le {k : ℝ} (hk : 0 < k) {g₁ g₂ : ℝ → ℝ}
    (h₁ : ContinuousOn g₁ (Set.Ioi 0)) (h₂ : ContinuousOn g₂ (Set.Ici k))
    (heq : g₁ k = g₂ k) :
    ContinuousOn (fun s => if s ≤ k then g₁ s else g₂ s) (Set.Ioi 0) := by
  intro x hx
  have hcontAt : ContinuousAt (fun s => if s ≤ k then g₁ s else g₂ s) x := by
    rcases lt_trichotomy x k with hlt | hxeq | hgt
    · have h1x : ContinuousAt g₁ x := h₁.continuousAt (isOpen_Ioi.mem_nhds hx)
      refine h1x.congr ?_
      filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
      simp [le_of_lt (Set.mem_Iio.mp hs)]
    · subst hxeq
      rw [Metric.continuousAt_iff]
      intro ε hε
      have h1k : ContinuousAt g₁ x := h₁.continuousAt (isOpen_Ioi.mem_nhds hk)
      obtain ⟨δ₁, hδ₁, h1⟩ := Metric.continuousAt_iff.mp h1k ε hε
      obtain ⟨δ₂, hδ₂, h2⟩ := Metric.continuousWithinAt_iff.mp (h₂ x (Set.mem_Ici.mpr le_rfl)) ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs => ?_⟩
      simp only [le_rfl, ↓reduceIte]
      by_cases hsk : s ≤ x
      · simp only [hsk, ↓reduceIte]
        exact h1 (lt_of_lt_of_le hs (min_le_left _ _))
      · simp only [hsk, ↓reduceIte]
        rw [heq]
        exact h2 (Set.mem_Ici.mpr (le_of_lt (not_le.mp hsk))) (lt_of_lt_of_le hs (min_le_right _ _))
    · have h2x : ContinuousAt g₂ x := h₂.continuousAt (Ici_mem_nhds hgt)
      refine h2x.congr ?_
      filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
      simp [not_le.mpr (Set.mem_Ioi.mp hs)]
  exact hcontAt.continuousWithinAt

private lemma hasDerivAt_integral_shift {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0))
    {a x : ℝ} (ha : 1 < a) (hx : 1 < x) :
    HasDerivAt (fun s => ∫ u in a..s, g (u - 1)) (g (x - 1)) x := by
  have hcomp : ContinuousOn (fun u => g (u - 1)) (Set.Ioi 1) :=
    hg.comp (continuous_id.sub continuous_const).continuousOn
      (fun u hu => by simp only [Set.mem_Ioi] at hu ⊢; linarith)
  have huIcc : Set.uIcc a x ⊆ Set.Ioi 1 := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    simp only [Set.mem_Ioi]
    rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hint : IntervalIntegrable (fun u => g (u - 1)) volume a x :=
    (hcomp.mono huIcc).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (fun u => g (u - 1)) (nhds x) volume :=
    hcomp.stronglyMeasurableAtFilter isOpen_Ioi x hx
  have hcont : ContinuousAt (fun u => g (u - 1)) x :=
    hcomp.continuousAt (isOpen_Ioi.mem_nhds hx)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

private lemma continuousOn_integral_shift {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0))
    {a : ℝ} (ha : 1 < a) :
    ContinuousOn (fun s => ∫ u in a..s, g (u - 1)) (Set.Ioi 1) := by
  intro x hx
  exact (hasDerivAt_integral_shift hg ha hx).continuousAt.continuousWithinAt

/-! ### Section 2: Recursive Construction of `(chenF₀, chenf₀)` -/

/-- Recursive pair `(Fₙ, fₙ)` agreeing with `(chenF₀, chenf₀)` on `(-∞, n + 2]`. -/
def pairAux : ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (fun s => if 0 < s then 1 / s else 0, fun _ => 0)
  | n + 1 =>
      let prev := pairAux n
      let k : ℝ := (n : ℝ) + 2
      (fun s => if s ≤ k then prev.1 s else (k * prev.1 k + ∫ u in k..s, prev.2 (u - 1)) / s,
       fun s => if s ≤ k then prev.2 s else (k * prev.2 k + ∫ u in k..s, prev.1 (u - 1)) / s)

private lemma pairAux_continuousOn (n : ℕ) :
    ContinuousOn (pairAux n).1 (Set.Ioi 0) ∧ ContinuousOn (pairAux n).2 (Set.Ioi 0) := by
  induction n with
  | zero =>
    constructor
    · refine ((continuousOn_const (c := (1 : ℝ))).div continuousOn_id
        (fun x hx => ne_of_gt (Set.mem_Ioi.mp hx))).congr ?_
      intro x hx
      simp [pairAux, Set.mem_Ioi.mp hx]
    · exact continuousOn_const
  | succ n ih =>
    rcases ih with ⟨hF, hf⟩
    set k : ℝ := (n : ℝ) + 2 with hk_def
    have hk_pos : 0 < k := by positivity
    have hk_gt1 : 1 < k := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hIci_sub_Ioi1 : Set.Ici k ⊆ Set.Ioi 1 := fun s hs => lt_of_lt_of_le hk_gt1 hs
    have hIci_sub_ne0 : ∀ s ∈ Set.Ici k, s ≠ 0 := fun s hs => ne_of_gt (lt_of_lt_of_le hk_pos hs)
    constructor
    · refine continuousOn_ite_le hk_pos hF ?_ ?_
      · exact (continuousOn_const.add ((continuousOn_integral_shift hf hk_gt1).mono hIci_sub_Ioi1)).div
          continuousOn_id hIci_sub_ne0
      · rw [← hk_def, intervalIntegral.integral_same, add_zero, mul_div_cancel_left₀ _ (ne_of_gt hk_pos)]
    · refine continuousOn_ite_le hk_pos hf ?_ ?_
      · exact (continuousOn_const.add ((continuousOn_integral_shift hF hk_gt1).mono hIci_sub_Ioi1)).div
          continuousOn_id hIci_sub_ne0
      · rw [← hk_def, intervalIntegral.integral_same, add_zero, mul_div_cancel_left₀ _ (ne_of_gt hk_pos)]

private lemma pairAux_eq_of_le {m n : ℕ} (hmn : m ≤ n) {s : ℝ} (hs : s ≤ (m : ℝ) + 2) :
    (pairAux n).1 s = (pairAux m).1 s ∧ (pairAux n).2 s = (pairAux m).2 s := by
  induction hmn with
  | refl => exact ⟨rfl, rfl⟩
  | @step n' hmn' ih =>
    have hs' : s ≤ (n' : ℝ) + 2 := by
      have : (m : ℝ) ≤ (n' : ℝ) := Nat.cast_le.mpr hmn'
      linarith
    simp only [pairAux, hs', ↓reduceIte]
    exact ih

/-- Unnormalized upper linear-sieve limit function `chenF₀`. -/
def chenF₀ (s : ℝ) : ℝ := (pairAux ⌊s⌋₊).1 s

/-- Unnormalized lower linear-sieve limit function `chenf₀`. -/
def chenf₀ (s : ℝ) : ℝ := (pairAux ⌊s⌋₊).2 s

private lemma le_floor_add_two (s : ℝ) : s ≤ (⌊s⌋₊ : ℝ) + 2 := by
  by_cases hs : 0 ≤ s
  · linarith [Nat.lt_floor_add_one s]
  · have : (0 : ℝ) ≤ (⌊s⌋₊ : ℝ) := Nat.cast_nonneg _
    linarith

lemma chenF₀_eq_pairAux {n : ℕ} {s : ℝ} (hs : s ≤ (n : ℝ) + 2) :
    chenF₀ s = (pairAux n).1 s := by
  unfold chenF₀
  rcases le_total ⌊s⌋₊ n with h | h
  · exact (pairAux_eq_of_le h (le_floor_add_two s)).1.symm
  · exact (pairAux_eq_of_le h hs).1

lemma chenf₀_eq_pairAux {n : ℕ} {s : ℝ} (hs : s ≤ (n : ℝ) + 2) :
    chenf₀ s = (pairAux n).2 s := by
  unfold chenf₀
  rcases le_total ⌊s⌋₊ n with h | h
  · exact (pairAux_eq_of_le h (le_floor_add_two s)).2.symm
  · exact (pairAux_eq_of_le h hs).2

lemma chenF₀_continuousOn : ContinuousOn chenF₀ (Set.Ioi 0) := by
  intro x hx
  set n : ℕ := ⌊x⌋₊
  have hlt : x < (n : ℝ) + 2 := by
    have : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  have hcont : ContinuousAt (pairAux n).1 x :=
    (pairAux_continuousOn n).1.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hcont' : ContinuousAt chenF₀ x := by
    refine hcont.congr ?_
    filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
    exact (chenF₀_eq_pairAux (le_of_lt (Set.mem_Iio.mp hs))).symm
  exact hcont'.continuousWithinAt

lemma chenf₀_continuousOn : ContinuousOn chenf₀ (Set.Ioi 0) := by
  intro x hx
  set n : ℕ := ⌊x⌋₊
  have hlt : x < (n : ℝ) + 2 := by
    have : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  have hcont : ContinuousAt (pairAux n).2 x :=
    (pairAux_continuousOn n).2.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hcont' : ContinuousAt chenf₀ x := by
    refine hcont.congr ?_
    filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
    exact (chenf₀_eq_pairAux (le_of_lt (Set.mem_Iio.mp hs))).symm
  exact hcont'.continuousWithinAt

lemma chenF₀_eq_of_Ioc_two {s : ℝ} (hs0 : 0 < s) (hs2 : s ≤ 2) :
    chenF₀ s = 1 / s := by
  rw [chenF₀_eq_pairAux (n := 0) (by simpa using hs2)]
  simp [pairAux, hs0]

lemma chenf₀_eq_zero_of_le_two {s : ℝ} (hs2 : s ≤ 2) :
    chenf₀ s = 0 := by
  rw [chenf₀_eq_pairAux (n := 0) (by simpa using hs2)]
  rfl

/-! ### Section 3: Global Buchstab Integral Equations & Explicit Closed Forms -/

private lemma chenF₀_step_integral (n : ℕ) {s : ℝ}
    (hs1 : (n : ℝ) + 2 ≤ s) (hs2 : s ≤ (n : ℝ) + 3) :
    s * chenF₀ s - ((n : ℝ) + 2) * chenF₀ ((n : ℝ) + 2) =
      ∫ u in ((n : ℝ) + 2)..s, chenf₀ (u - 1) := by
  have hs_le : s ≤ ((n + 1 : ℕ) : ℝ) + 2 := by push_cast; linarith
  by_cases hsk : s = (n : ℝ) + 2
  · subst hsk; simp
  · have hnotle : ¬ s ≤ (n : ℝ) + 2 := by
      intro hle; exact hsk (le_antisymm hle hs1)
    have hs_pos : 0 < s := by linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [chenF₀_eq_pairAux hs_le, chenF₀_eq_pairAux (n := n) le_rfl]
    simp only [pairAux, hnotle, ↓reduceIte]
    rw [mul_div_cancel₀ _ (ne_of_gt hs_pos), add_sub_cancel_left]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hs1] at hu
    exact (chenf₀_eq_pairAux (n := n) (by linarith [hu.2])).symm

private lemma chenf₀_step_integral (n : ℕ) {s : ℝ}
    (hs1 : (n : ℝ) + 2 ≤ s) (hs2 : s ≤ (n : ℝ) + 3) :
    s * chenf₀ s - ((n : ℝ) + 2) * chenf₀ ((n : ℝ) + 2) =
      ∫ u in ((n : ℝ) + 2)..s, chenF₀ (u - 1) := by
  have hs_le : s ≤ ((n + 1 : ℕ) : ℝ) + 2 := by push_cast; linarith
  by_cases hsk : s = (n : ℝ) + 2
  · subst hsk; simp
  · have hnotle : ¬ s ≤ (n : ℝ) + 2 := by
      intro hle; exact hsk (le_antisymm hle hs1)
    have hs_pos : 0 < s := by linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [chenf₀_eq_pairAux hs_le, chenf₀_eq_pairAux (n := n) le_rfl]
    simp only [pairAux, hnotle, ↓reduceIte]
    rw [mul_div_cancel₀ _ (ne_of_gt hs_pos), add_sub_cancel_left]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hs1] at hu
    exact (chenF₀_eq_pairAux (n := n) (by linarith [hu.2])).symm

private lemma intervalIntegrable_shift {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0))
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun u => g (u - 1)) volume a b := by
  have hcomp : ContinuousOn (fun u => g (u - 1)) (Set.Ioi 1) :=
    hg.comp (continuous_id.sub continuous_const).continuousOn
      (fun u hu => by simp only [Set.mem_Ioi] at hu ⊢; linarith)
  refine (hcomp.mono ?_).intervalIntegrable
  intro u hu
  rw [Set.mem_uIcc] at hu
  simp only [Set.mem_Ioi]
  rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

private lemma chenF₀_nat_integral (n : ℕ) :
    ((n : ℝ) + 2) * chenF₀ ((n : ℝ) + 2) - 2 * chenF₀ 2 =
      ∫ u in (2 : ℝ)..((n : ℝ) + 2), chenf₀ (u - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := chenF₀_step_integral n (s := (n : ℝ) + 3) (by linarith) le_rfl
    have hadd : (∫ u in (2 : ℝ)..((n : ℝ) + 2), chenf₀ (u - 1)) +
        (∫ u in ((n : ℝ) + 2)..((n : ℝ) + 3), chenf₀ (u - 1)) =
        ∫ u in (2 : ℝ)..((n : ℝ) + 3), chenf₀ (u - 1) :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_shift chenf₀_continuousOn (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n]))
        (intervalIntegrable_shift chenf₀_continuousOn (by linarith [Nat.cast_nonneg (α := ℝ) n])
          (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    have h3 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
    rw [h3]
    linarith

private lemma chenf₀_nat_integral (n : ℕ) :
    ((n : ℝ) + 2) * chenf₀ ((n : ℝ) + 2) - 2 * chenf₀ 2 =
      ∫ u in (2 : ℝ)..((n : ℝ) + 2), chenF₀ (u - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := chenf₀_step_integral n (s := (n : ℝ) + 3) (by linarith) le_rfl
    have hadd : (∫ u in (2 : ℝ)..((n : ℝ) + 2), chenF₀ (u - 1)) +
        (∫ u in ((n : ℝ) + 2)..((n : ℝ) + 3), chenF₀ (u - 1)) =
        ∫ u in (2 : ℝ)..((n : ℝ) + 3), chenF₀ (u - 1) :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_shift chenF₀_continuousOn (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n]))
        (intervalIntegrable_shift chenF₀_continuousOn (by linarith [Nat.cast_nonneg (α := ℝ) n])
          (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    have h3 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
    rw [h3]
    linarith

private lemma chenF₀_integral_from_two {s : ℝ} (hs : 2 ≤ s) :
    s * chenF₀ s - 2 * chenF₀ 2 = ∫ u in (2 : ℝ)..s, chenf₀ (u - 1) := by
  set m : ℕ := ⌊s - 2⌋₊
  have hm_nonneg : 0 ≤ s - 2 := by linarith
  have hm1 : (m : ℝ) + 2 ≤ s := by
    have := Nat.floor_le hm_nonneg
    linarith
  have hm2 : s ≤ (m : ℝ) + 3 := by
    have := Nat.lt_floor_add_one (s - 2)
    linarith
  have h1 := chenF₀_nat_integral m
  have h2 := chenF₀_step_integral m hm1 hm2
  have hadd : (∫ u in (2 : ℝ)..((m : ℝ) + 2), chenf₀ (u - 1)) +
      (∫ u in ((m : ℝ) + 2)..s, chenf₀ (u - 1)) =
      ∫ u in (2 : ℝ)..s, chenf₀ (u - 1) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_shift chenf₀_continuousOn (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m]))
      (intervalIntegrable_shift chenf₀_continuousOn (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by linarith))
  linarith

private lemma chenf₀_integral_from_two {s : ℝ} (hs : 2 ≤ s) :
    s * chenf₀ s - 2 * chenf₀ 2 = ∫ u in (2 : ℝ)..s, chenF₀ (u - 1) := by
  set m : ℕ := ⌊s - 2⌋₊
  have hm_nonneg : 0 ≤ s - 2 := by linarith
  have hm1 : (m : ℝ) + 2 ≤ s := by
    have := Nat.floor_le hm_nonneg
    linarith
  have hm2 : s ≤ (m : ℝ) + 3 := by
    have := Nat.lt_floor_add_one (s - 2)
    linarith
  have h1 := chenf₀_nat_integral m
  have h2 := chenf₀_step_integral m hm1 hm2
  have hadd : (∫ u in (2 : ℝ)..((m : ℝ) + 2), chenF₀ (u - 1)) +
      (∫ u in ((m : ℝ) + 2)..s, chenF₀ (u - 1)) =
      ∫ u in (2 : ℝ)..s, chenF₀ (u - 1) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_shift chenF₀_continuousOn (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m]))
      (intervalIntegrable_shift chenF₀_continuousOn (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by linarith))
  linarith

lemma chenF₀_buchstab {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    b * chenF₀ b - a * chenF₀ a = ∫ u in a..b, chenf₀ (u - 1) := by
  have hb : 2 ≤ b := le_trans ha hab
  have h1 := chenF₀_integral_from_two ha
  have h2 := chenF₀_integral_from_two hb
  have hadd : (∫ u in (2 : ℝ)..a, chenf₀ (u - 1)) + (∫ u in a..b, chenf₀ (u - 1)) =
      ∫ u in (2 : ℝ)..b, chenf₀ (u - 1) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_shift chenf₀_continuousOn (by norm_num) (by linarith))
      (intervalIntegrable_shift chenf₀_continuousOn (by linarith) (by linarith))
  linarith

lemma chenf₀_buchstab {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    b * chenf₀ b - a * chenf₀ a = ∫ u in a..b, chenF₀ (u - 1) := by
  have hb : 2 ≤ b := le_trans ha hab
  have h1 := chenf₀_integral_from_two ha
  have h2 := chenf₀_integral_from_two hb
  have hadd : (∫ u in (2 : ℝ)..a, chenF₀ (u - 1)) + (∫ u in a..b, chenF₀ (u - 1)) =
      ∫ u in (2 : ℝ)..b, chenF₀ (u - 1) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_shift chenF₀_continuousOn (by norm_num) (by linarith))
      (intervalIntegrable_shift chenF₀_continuousOn (by linarith) (by linarith))
  linarith

lemma chenF₀_eq_of_Ioc_three {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) :
    chenF₀ s = 1 / s := by
  by_cases hs2 : s ≤ 2
  · exact chenF₀_eq_of_Ioc_two hs0 hs2
  · push Not at hs2
    have h := chenF₀_integral_from_two (le_of_lt hs2)
    have hint : ∫ u in (2 : ℝ)..s, chenf₀ (u - 1) = 0 := by
      have hcongr : ∫ u in (2 : ℝ)..s, chenf₀ (u - 1) = ∫ _ in (2 : ℝ)..s, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [Set.uIcc_of_le (le_of_lt hs2)] at hu
        exact chenf₀_eq_zero_of_le_two (by linarith [hu.2])
      rw [hcongr, intervalIntegral.integral_zero]
    rw [hint, chenF₀_eq_of_Ioc_two (by norm_num) le_rfl] at h
    have hs_ne : s ≠ 0 := ne_of_gt hs0
    have hmul : s * chenF₀ s = 1 := by linarith
    field_simp [hs_ne]
    linarith

lemma chenf₀_eq_of_Icc {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    chenf₀ s = Real.log (s - 1) / s := by
  have h := chenf₀_integral_from_two hs2
  rw [chenf₀_eq_zero_of_le_two le_rfl] at h
  have hcongr : ∫ u in (2 : ℝ)..s, chenF₀ (u - 1) = ∫ u in (2 : ℝ)..s, (u - 1)⁻¹ := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hs2] at hu
    rw [chenF₀_eq_of_Ioc_three (by linarith [hu.1]) (by linarith [hu.2]), one_div]
  have hftc : ∫ u in (2 : ℝ)..s, (u - 1)⁻¹ = Real.log (s - 1) - Real.log (2 - 1) := by
    have hint : IntervalIntegrable (fun u : ℝ => (u - 1)⁻¹) volume 2 s := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ((continuousOn_id (s := Set.uIcc (2 : ℝ) s)).sub continuousOn_const).inv₀ ?_
      intro u hu
      rw [Set.uIcc_of_le hs2] at hu
      simp only [Pi.sub_apply, id_eq]
      linarith [hu.1]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => Real.log (u - 1)) ?_ hint
    intro u hu
    rw [Set.uIcc_of_le hs2] at hu
    have hne : u - 1 ≠ 0 := by linarith [hu.1]
    simpa [one_div] using ((hasDerivAt_id' u).sub_const 1).log hne
  rw [hcongr, hftc] at h
  have hlog1 : Real.log ((2 : ℝ) - 1) = 0 := by norm_num
  rw [hlog1] at h
  have hs_ne : s ≠ 0 := by linarith
  field_simp [hs_ne]
  linarith

/-! ### Section 4: Derivatives, Adjoint Invariant, Positivity, and Monotonicity -/

private lemma hasDerivAt_mul_chenF₀ {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * chenF₀ x) (chenf₀ (s - 1)) s := by
  have h := hasDerivAt_integral_shift chenf₀_continuousOn (a := 2) (by norm_num) (by linarith)
  have h2 := h.const_add (2 * chenF₀ 2)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
  have := chenF₀_integral_from_two (le_of_lt (Set.mem_Ioi.mp hx))
  linarith

private lemma hasDerivAt_mul_chenf₀ {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * chenf₀ x) (chenF₀ (s - 1)) s := by
  have h := hasDerivAt_integral_shift chenF₀_continuousOn (a := 2) (by norm_num) (by linarith)
  have h2 := h.const_add (2 * chenf₀ 2)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
  have := chenf₀_integral_from_two (le_of_lt (Set.mem_Ioi.mp hx))
  linarith

private lemma hasDerivAt_chenF₀ {s : ℝ} (hs : 2 < s) :
    HasDerivAt chenF₀ ((chenf₀ (s - 1) - chenF₀ s) / s) s := by
  have hs_ne : s ≠ 0 := by linarith
  have hdiv := (hasDerivAt_mul_chenF₀ hs).fun_div (hasDerivAt_id' s) hs_ne
  have hval : (chenf₀ (s - 1) * s - s * chenF₀ s * 1) / s ^ 2 = (chenf₀ (s - 1) - chenF₀ s) / s := by
    field_simp [hs_ne]
  rw [hval] at hdiv
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
  have hx_ne : x ≠ 0 := by linarith [Set.mem_Ioi.mp hx]
  simp [mul_div_cancel_left₀ _ hx_ne]

private lemma hasDerivAt_chenf₀ {s : ℝ} (hs : 2 < s) :
    HasDerivAt chenf₀ ((chenF₀ (s - 1) - chenf₀ s) / s) s := by
  have hs_ne : s ≠ 0 := by linarith
  have hdiv := (hasDerivAt_mul_chenf₀ hs).fun_div (hasDerivAt_id' s) hs_ne
  have hval : (chenF₀ (s - 1) * s - s * chenf₀ s * 1) / s ^ 2 = (chenF₀ (s - 1) - chenf₀ s) / s := by
    field_simp [hs_ne]
  rw [hval] at hdiv
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
  have hx_ne : x ≠ 0 := by linarith [Set.mem_Ioi.mp hx]
  simp [mul_div_cancel_left₀ _ hx_ne]

/-- The difference function `chenD₀ s = chenF₀ s - chenf₀ s`. -/
private def chenD₀ (s : ℝ) : ℝ := chenF₀ s - chenf₀ s

private lemma chenD₀_continuousOn : ContinuousOn chenD₀ (Set.Ioi 0) :=
  chenF₀_continuousOn.sub chenf₀_continuousOn

private lemma hasDerivAt_mul_chenD₀ {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * chenD₀ x) (-chenD₀ (s - 1)) s := by
  have h := (hasDerivAt_mul_chenF₀ hs).fun_sub (hasDerivAt_mul_chenf₀ hs)
  have hval : chenf₀ (s - 1) - chenF₀ (s - 1) = -chenD₀ (s - 1) := by
    simp [chenD₀]
  rw [hval] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp only [chenD₀]; ring

private lemma hasDerivAt_integral_one {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0))
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun s => ∫ t in (1 : ℝ)..s, g t) (g x) x := by
  have huIcc : Set.uIcc (1 : ℝ) x ⊆ Set.Ioi 0 := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    simp only [Set.mem_Ioi]
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  exact intervalIntegral.integral_hasDerivAt_right (hg.mono huIcc).intervalIntegrable
    (hg.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hg.continuousAt (isOpen_Ioi.mem_nhds hx))

/-- Exact adjoint invariant of the linear sieve: for all `s ≥ 2`,
`s * (s - 1) * (chenF₀ s - chenf₀ s) = ∫ t in (s - 1)..s, t * (chenF₀ t - chenf₀ t)`. -/
private lemma chenD₀_adjoint_invariant {s : ℝ} (hs : 2 ≤ s) :
    s * (s - 1) * chenD₀ s = ∫ t in (s - 1)..s, t * chenD₀ t := by
  set g : ℝ → ℝ := fun t => t * chenD₀ t
  have hg_cont : ContinuousOn g (Set.Ioi 0) := continuousOn_id.mul chenD₀_continuousOn
  set Φ : ℝ → ℝ := fun x =>
    (x - 1) * (x * chenD₀ x) - ((∫ t in (1 : ℝ)..x, g t) - (∫ t in (1 : ℝ)..(x - 1), g t))
  have hΦ_deriv : ∀ x ∈ Set.Ioi (2 : ℝ), HasDerivAt Φ 0 x := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have h1 : HasDerivAt (fun u => (u - 1) * (u * chenD₀ u))
        (1 * (x * chenD₀ x) + (x - 1) * (-chenD₀ (x - 1))) x :=
      ((hasDerivAt_id x).sub_const 1).fun_mul (hasDerivAt_mul_chenD₀ hx)
    have h2 : HasDerivAt (fun u => ∫ t in (1 : ℝ)..u, g t) (g x) x :=
      hasDerivAt_integral_one hg_cont (by linarith)
    have h3 : HasDerivAt (fun u => ∫ t in (1 : ℝ)..(u - 1), g t) (g (x - 1) * 1) x :=
      (hasDerivAt_integral_one hg_cont (by linarith)).comp x ((hasDerivAt_id x).sub_const 1)
    have hsub := h1.fun_sub (h2.fun_sub h3)
    have hzero : 1 * (x * chenD₀ x) + (x - 1) * -chenD₀ (x - 1) - (g x - g (x - 1) * 1) = 0 := by
      simp only [g]; ring
    rwa [hzero] at hsub
  have hΦ_cont : ContinuousOn Φ (Set.Ici 2) := by
    have hIci_pos : Set.Ici (2 : ℝ) ⊆ Set.Ioi 0 :=
      fun x hx => Set.mem_Ioi.mpr (by linarith [Set.mem_Ici.mp hx])
    have hIci_sub1 : Set.MapsTo (fun x : ℝ => x - 1) (Set.Ici 2) (Set.Ioi 0) :=
      fun x hx => Set.mem_Ioi.mpr (by linarith [Set.mem_Ici.mp hx])
    have hint_cont : ContinuousOn (fun u => ∫ t in (1 : ℝ)..u, g t) (Set.Ioi 0) :=
      fun x hx => (hasDerivAt_integral_one hg_cont hx).continuousAt.continuousWithinAt
    exact ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_id.mul (chenD₀_continuousOn.mono hIci_pos))).sub
      ((hint_cont.mono hIci_pos).sub
        (hint_cont.comp (continuousOn_id.sub continuousOn_const) hIci_sub1))
  have hΦ_diff : DifferentiableOn ℝ Φ (interior (Set.Ici (2 : ℝ))) := by
    rw [interior_Ici]
    exact fun x hx => (hΦ_deriv x hx).differentiableAt.differentiableWithinAt
  have hΦ_mono : MonotoneOn Φ (Set.Ici 2) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 2) hΦ_cont hΦ_diff (fun x hx => by
      rw [interior_Ici] at hx; rw [(hΦ_deriv x hx).deriv])
  have hΦ_anti : AntitoneOn Φ (Set.Ici 2) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 2) hΦ_cont hΦ_diff (fun x hx => by
      rw [interior_Ici] at hx; rw [(hΦ_deriv x hx).deriv])
  have hΦ_eq : Φ s = Φ 2 :=
    le_antisymm (hΦ_anti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs)
      (hΦ_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs)
  have hΦ2 : Φ 2 = 0 := by
    have hD2 : chenD₀ 2 = 1 / 2 := by
      simp [chenD₀, chenF₀_eq_of_Ioc_two (by norm_num) le_rfl, chenf₀_eq_zero_of_le_two le_rfl]
    have hint12 : ∫ t in (1 : ℝ)..2, g t = 1 := by
      have hcongr : ∫ t in (1 : ℝ)..2, g t = ∫ _ in (1 : ℝ)..2, (1 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le (by norm_num)] at ht
        have ht0 : 0 < t := by linarith [ht.1]
        simp only [g, chenD₀, chenF₀_eq_of_Ioc_two ht0 ht.2, chenf₀_eq_zero_of_le_two ht.2, sub_zero]
        field_simp [ne_of_gt ht0]
      rw [hcongr]
      norm_num
    simp only [Φ, show (2 : ℝ) - 1 = 1 by norm_num, intervalIntegral.integral_same, sub_zero,
      hD2, hint12]
    norm_num
  have hadd : (∫ t in (1 : ℝ)..(s - 1), g t) + (∫ t in (s - 1)..s, g t) =
      ∫ t in (1 : ℝ)..s, g t := by
    refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
    · refine (hg_cont.mono ?_).intervalIntegrable
      intro t ht; rw [Set.uIcc_of_le (by linarith)] at ht; simp only [Set.mem_Ioi]; linarith [ht.1]
    · refine (hg_cont.mono ?_).intervalIntegrable
      intro t ht; rw [Set.uIcc_of_le (by linarith)] at ht; simp only [Set.mem_Ioi]; linarith [ht.1]
  have hΦs : Φ s = 0 := hΦ_eq.trans hΦ2
  simp only [Φ] at hΦs
  linarith

lemma chenf₀_lt_chenF₀ {s : ℝ} (hs : 0 < s) : chenf₀ s < chenF₀ s := by
  suffices h : 0 < chenD₀ s by
    simp only [chenD₀] at h; linarith
  by_contra hnot
  push Not at hnot
  set Z : Set ℝ := {x : ℝ | 2 ≤ x ∧ chenD₀ x ≤ 0}
  have hZ_ne : Z.Nonempty := by
    refine ⟨s, ?_, hnot⟩
    by_contra hs2
    push Not at hs2
    have hD : chenD₀ s = 1 / s := by
      simp [chenD₀, chenF₀_eq_of_Ioc_two hs (le_of_lt hs2), chenf₀_eq_zero_of_le_two (le_of_lt hs2)]
    rw [hD] at hnot
    have : 0 < 1 / s := one_div_pos.mpr hs
    linarith
  have hZ_bdd : BddBelow Z := ⟨2, fun x hx => hx.1⟩
  have hZ_closed : IsClosed Z := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    have hx2 : 2 ≤ x := isClosed_Ici.closure_subset (closure_mono (fun y hy => hy.1) hx)
    refine ⟨hx2, ?_⟩
    by_contra hpos
    push Not at hpos
    have hcont : ContinuousAt chenD₀ x :=
      chenD₀_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))
    have hopen : {y | 0 < chenD₀ y} ∈ nhds x := hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    obtain ⟨y, hy_pos, hyZ⟩ := mem_closure_iff_nhds.mp hx _ hopen
    exact not_lt_of_ge hyZ.2 hy_pos
  set s₀ : ℝ := sInf Z
  have hs₀_mem : s₀ ∈ Z := hZ_closed.csInf_mem hZ_ne hZ_bdd
  have hs₀_gt2 : 2 < s₀ := by
    refine lt_of_le_of_ne hs₀_mem.1 ?_
    intro heq
    have hD2 : chenD₀ 2 = 1 / 2 := by
      simp [chenD₀, chenF₀_eq_of_Ioc_two (by norm_num) le_rfl, chenf₀_eq_zero_of_le_two le_rfl]
    have := hs₀_mem.2
    rw [← heq, hD2] at this
    linarith
  have hlt_pos : ∀ t, 0 < t → t < s₀ → 0 < chenD₀ t := by
    intro t ht0 hts₀
    by_cases ht2 : t < 2
    · have hDt : chenD₀ t = 1 / t := by
        simp [chenD₀, chenF₀_eq_of_Ioc_two ht0 (le_of_lt ht2), chenf₀_eq_zero_of_le_two (le_of_lt ht2)]
      rw [hDt]; exact one_div_pos.mpr ht0
    · push Not at ht2
      by_contra hle
      push Not at hle
      have hmem : t ∈ Z := ⟨ht2, hle⟩
      exact not_lt_of_ge (csInf_le hZ_bdd hmem) hts₀
  have hs₀_ge0 : 0 ≤ chenD₀ s₀ := by
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousAt chenD₀ s₀ :=
      chenD₀_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont (-chenD₀ s₀) (by linarith)
    set t : ℝ := max (s₀ / 2) (s₀ - δ / 2)
    have ht0 : 0 < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hts₀ : t < s₀ := max_lt (by linarith) (by linarith)
    have hdist : |t - s₀| < δ := by
      rw [abs_of_neg (by linarith)]
      have : s₀ - δ / 2 ≤ t := le_max_right _ _
      linarith
    have h1 := hball hdist
    rw [Real.dist_eq] at h1
    have h2 := hlt_pos t ht0 hts₀
    linarith [abs_lt.mp h1]
  have hint_pos : 0 < ∫ t in (s₀ - 1)..s₀, t * chenD₀ t := by
    refine intervalIntegral.integral_pos (by linarith) ?_ ?_ ?_
    · refine (continuousOn_id.mul chenD₀_continuousOn).mono ?_
      intro t ht; simp only [Set.mem_Ioi]; linarith [ht.1]
    · intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      rcases eq_or_lt_of_le ht.2 with rfl | hlt
      · exact mul_nonneg (le_of_lt ht0) hs₀_ge0
      · exact mul_nonneg (le_of_lt ht0) (le_of_lt (hlt_pos t ht0 hlt))
    · refine ⟨s₀ - 1, ⟨le_rfl, by linarith⟩, ?_⟩
      exact mul_pos (by linarith) (hlt_pos (s₀ - 1) (by linarith) (by linarith))
  have hinv := chenD₀_adjoint_invariant hs₀_mem.1
  have hnonpos : s₀ * (s₀ - 1) * chenD₀ s₀ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) hs₀_mem.2
  linarith

private lemma chenF₀_antitone_and_chenf₀_monotone :
    AntitoneOn chenF₀ (Set.Ioi 0) ∧ MonotoneOn chenf₀ (Set.Ioi 0) := by
  set E : Set ℝ :=
    {x : ℝ | 2 ≤ x ∧ (chenF₀ x ≤ chenf₀ (x - 1) ∨ chenF₀ (x - 1) ≤ chenf₀ x)}
  have hE_empty : E = ∅ := by
    by_contra hE_ne
    have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_ne
    have hE_bdd : BddBelow E := ⟨2, fun x hx => hx.1⟩
    have hE_closed : IsClosed E := by
      rw [← closure_subset_iff_isClosed]
      intro x hx
      have hx2 : 2 ≤ x := isClosed_Ici.closure_subset (closure_mono (fun y hy => hy.1) hx)
      refine ⟨hx2, ?_⟩
      by_contra hnot
      push Not at hnot
      rcases hnot with ⟨h1, h2⟩
      have hFc : ContinuousAt chenF₀ x :=
        chenF₀_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))
      have hfc : ContinuousAt chenf₀ x :=
        chenf₀_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))
      have hFsc : ContinuousAt (fun y => chenF₀ (y - 1)) x :=
        (chenF₀_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))).comp
          (continuousAt_id.sub continuousAt_const)
      have hfsc : ContinuousAt (fun y => chenf₀ (y - 1)) x :=
        (chenf₀_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))).comp
          (continuousAt_id.sub continuousAt_const)
      have hopen1 : {y | 0 < chenF₀ y - chenf₀ (y - 1)} ∈ nhds x :=
        (hFc.sub hfsc).preimage_mem_nhds (isOpen_Ioi.mem_nhds (sub_pos.mpr h1))
      have hopen2 : {y | 0 < chenF₀ (y - 1) - chenf₀ y} ∈ nhds x :=
        (hFsc.sub hfc).preimage_mem_nhds (isOpen_Ioi.mem_nhds (sub_pos.mpr h2))
      obtain ⟨y, ⟨hy1, hy2⟩, hyE⟩ :=
        mem_closure_iff_nhds.mp hx _ (Filter.inter_mem hopen1 hopen2)
      rcases hyE.2 with hbad | hbad
      · exact not_lt_of_ge hbad (sub_pos.mp hy1)
      · exact not_lt_of_ge hbad (sub_pos.mp hy2)
    set s₀ : ℝ := sInf E
    have hs₀_mem : s₀ ∈ E := hE_closed.csInf_mem hE_nonempty hE_bdd
    have hs₀_gt2 : 2 < s₀ := by
      refine lt_of_le_of_ne hs₀_mem.1 ?_
      intro heq
      have hF2 : chenF₀ 2 = 1 / 2 := chenF₀_eq_of_Ioc_two (by norm_num) le_rfl
      have hF1 : chenF₀ 1 = 1 := by simpa using chenF₀_eq_of_Ioc_two (s := 1) (by norm_num) (by norm_num)
      have hf2 : chenf₀ 2 = 0 := chenf₀_eq_zero_of_le_two le_rfl
      have hf1 : chenf₀ 1 = 0 := chenf₀_eq_zero_of_le_two (by norm_num)
      have := hs₀_mem.2
      rw [← heq] at this
      norm_num [hF2, hF1, hf2, hf1] at this
    have hF_anti_Icc : AntitoneOn chenF₀ (Set.Icc 2 s₀) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 2 s₀)
        (chenF₀_continuousOn.mono fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1])) ?_ ?_
      · rw [interior_Icc]
        exact fun x hx => (hasDerivAt_chenF₀ hx.1).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_chenF₀ hx.1).deriv]
        have hnotE : x ∉ E := fun h => not_lt_of_ge (csInf_le hE_bdd h) hx.2
        have hlt : chenf₀ (x - 1) < chenF₀ x := by
          by_contra hge; push Not at hge; exact hnotE ⟨le_of_lt hx.1, Or.inl hge⟩
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hx.1])
    have hf_mono_Icc : MonotoneOn chenf₀ (Set.Icc 2 s₀) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 2 s₀)
        (chenf₀_continuousOn.mono fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1])) ?_ ?_
      · rw [interior_Icc]
        exact fun x hx => (hasDerivAt_chenf₀ hx.1).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_chenf₀ hx.1).deriv]
        have hnotE : x ∉ E := fun h => not_lt_of_ge (csInf_le hE_bdd h) hx.2
        have hlt : chenf₀ x < chenF₀ (x - 1) := by
          by_contra hge; push Not at hge; exact hnotE ⟨le_of_lt hx.1, Or.inr hge⟩
        exact div_nonneg (by linarith) (by linarith [hx.1])
    have hF_anti_Ioc : AntitoneOn chenF₀ (Set.Ioc 0 s₀) := by
      intro x hx y hy hxy
      rcases le_or_gt y 2 with hy2 | hy2
      · rw [chenF₀_eq_of_Ioc_two hx.1 (le_trans hxy hy2), chenF₀_eq_of_Ioc_two hy.1 hy2]
        exact one_div_le_one_div_of_le hx.1 hxy
      · rcases le_or_gt x 2 with hx2 | hx2
        · calc chenF₀ y ≤ chenF₀ 2 := hF_anti_Icc ⟨le_rfl, le_of_lt hs₀_gt2⟩ ⟨le_of_lt hy2, hy.2⟩ (le_of_lt hy2)
            _ ≤ chenF₀ x := by
              rw [chenF₀_eq_of_Ioc_two hx.1 hx2, chenF₀_eq_of_Ioc_two (by norm_num) le_rfl]
              exact one_div_le_one_div_of_le hx.1 hx2
        · exact hF_anti_Icc ⟨le_of_lt hx2, hx.2⟩ ⟨le_of_lt hy2, hy.2⟩ hxy
    have hf_mono_Ioc : MonotoneOn chenf₀ (Set.Ioc 0 s₀) := by
      intro x hx y hy hxy
      rcases le_or_gt y 2 with hy2 | hy2
      · rw [chenf₀_eq_zero_of_le_two (le_trans hxy hy2), chenf₀_eq_zero_of_le_two hy2]
      · rcases le_or_gt x 2 with hx2 | hx2
        · calc chenf₀ x = chenf₀ 2 := by rw [chenf₀_eq_zero_of_le_two hx2, chenf₀_eq_zero_of_le_two le_rfl]
            _ ≤ chenf₀ y := hf_mono_Icc ⟨le_rfl, le_of_lt hs₀_gt2⟩ ⟨le_of_lt hy2, hy.2⟩ (le_of_lt hy2)
        · exact hf_mono_Icc ⟨le_of_lt hx2, hx.2⟩ ⟨le_of_lt hy2, hy.2⟩ hxy
    have h1 : chenf₀ (s₀ - 1) ≤ chenf₀ s₀ :=
      hf_mono_Ioc ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    have h2 : chenF₀ s₀ ≤ chenF₀ (s₀ - 1) :=
      hF_anti_Ioc ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    have h3 : chenf₀ s₀ < chenF₀ s₀ := chenf₀_lt_chenF₀ (by linarith)
    rcases hs₀_mem.2 with hbad | hbad <;> linarith
  have hF_anti_Ici : AntitoneOn chenF₀ (Set.Ici 2) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 2)
      (chenF₀_continuousOn.mono fun x hx => Set.mem_Ioi.mpr (by linarith [Set.mem_Ici.mp hx])) ?_ ?_
    · rw [interior_Ici]
      exact fun x hx => (hasDerivAt_chenF₀ hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_chenF₀ hx).deriv]
      have hnotE : x ∉ E := by rw [hE_empty]; simp
      have hlt : chenf₀ (x - 1) < chenF₀ x := by
        by_contra hge; push Not at hge; exact hnotE ⟨le_of_lt hx, Or.inl hge⟩
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [Set.mem_Ioi.mp hx])
  have hf_mono_Ici : MonotoneOn chenf₀ (Set.Ici 2) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 2)
      (chenf₀_continuousOn.mono fun x hx => Set.mem_Ioi.mpr (by linarith [Set.mem_Ici.mp hx])) ?_ ?_
    · rw [interior_Ici]
      exact fun x hx => (hasDerivAt_chenf₀ hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_chenf₀ hx).deriv]
      have hnotE : x ∉ E := by rw [hE_empty]; simp
      have hlt : chenf₀ x < chenF₀ (x - 1) := by
        by_contra hge; push Not at hge; exact hnotE ⟨le_of_lt hx, Or.inr hge⟩
      exact div_nonneg (by linarith) (by linarith [Set.mem_Ioi.mp hx])
  constructor
  · intro x hx y hy hxy
    rcases le_or_gt y 2 with hy2 | hy2
    · rw [chenF₀_eq_of_Ioc_two hx (le_trans hxy hy2), chenF₀_eq_of_Ioc_two hy hy2]
      exact one_div_le_one_div_of_le hx hxy
    · rcases le_or_gt x 2 with hx2 | hx2
      · calc chenF₀ y ≤ chenF₀ 2 := hF_anti_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt hy2)) (le_of_lt hy2)
          _ ≤ chenF₀ x := by
            rw [chenF₀_eq_of_Ioc_two hx hx2, chenF₀_eq_of_Ioc_two (by norm_num) le_rfl]
            exact one_div_le_one_div_of_le hx hx2
      · exact hF_anti_Ici (Set.mem_Ici.mpr (le_of_lt hx2)) (Set.mem_Ici.mpr (le_of_lt hy2)) hxy
  · intro x hx y hy hxy
    rcases le_or_gt y 2 with hy2 | hy2
    · rw [chenf₀_eq_zero_of_le_two (le_trans hxy hy2), chenf₀_eq_zero_of_le_two hy2]
    · rcases le_or_gt x 2 with hx2 | hx2
      · calc chenf₀ x = chenf₀ 2 := by rw [chenf₀_eq_zero_of_le_two hx2, chenf₀_eq_zero_of_le_two le_rfl]
          _ ≤ chenf₀ y := hf_mono_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt hy2)) (le_of_lt hy2)
      · exact hf_mono_Ici (Set.mem_Ici.mpr (le_of_lt hx2)) (Set.mem_Ici.mpr (le_of_lt hy2)) hxy

lemma chenF₀_antitoneOn : AntitoneOn chenF₀ (Set.Ioi 0) :=
  chenF₀_antitone_and_chenf₀_monotone.1

lemma chenf₀_monotoneOn : MonotoneOn chenf₀ (Set.Ioi 0) :=
  chenF₀_antitone_and_chenf₀_monotone.2

lemma chenf₀_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ chenf₀ s := by
  rcases le_or_gt s 2 with hs2 | hs2
  · rw [chenf₀_eq_zero_of_le_two hs2]
  · rw [← chenf₀_eq_zero_of_le_two (s := 2) le_rfl]
    exact chenf₀_monotoneOn (by norm_num) hs (le_of_lt hs2)

lemma chenF₀_sub_chenf₀_le_one_div {s : ℝ} (hs : 2 ≤ s) :
    chenF₀ s - chenf₀ s ≤ 1 / s := by
  have hF := chenF₀_integral_from_two hs
  have hf := chenf₀_integral_from_two hs
  have hsub : s * (chenF₀ s - chenf₀ s) - 2 * (chenF₀ 2 - chenf₀ 2) =
      -(∫ u in (2 : ℝ)..s, chenD₀ (u - 1)) := by
    have hint : (∫ u in (2 : ℝ)..s, chenf₀ (u - 1)) - (∫ u in (2 : ℝ)..s, chenF₀ (u - 1)) =
        -(∫ u in (2 : ℝ)..s, chenD₀ (u - 1)) := by
      rw [← intervalIntegral.integral_sub
        (intervalIntegrable_shift chenf₀_continuousOn (by norm_num) (by linarith))
        (intervalIntegrable_shift chenF₀_continuousOn (by norm_num) (by linarith)),
        ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp [chenD₀]
    linarith
  have hint_nonneg : 0 ≤ ∫ u in (2 : ℝ)..s, chenD₀ (u - 1) := by
    refine intervalIntegral.integral_nonneg hs fun u hu => ?_
    exact le_of_lt (sub_pos.mpr (chenf₀_lt_chenF₀ (by linarith [hu.1])))
  have h2val : 2 * (chenF₀ 2 - chenf₀ 2) = 1 := by
    rw [chenF₀_eq_of_Ioc_two (by norm_num) le_rfl, chenf₀_eq_zero_of_le_two le_rfl]
    norm_num
  have hmul : s * (chenF₀ s - chenf₀ s) ≤ 1 := by linarith
  have hs0 : 0 < s := by linarith
  rw [le_div_iff₀ hs0]
  linarith

/-! ### Section 5: The Common Limit `chenL₀` and Normalized Pair `(chenF, chenf)` -/

/-- The common limit `L₀ = lim_{s → ∞} chenF₀(s) = lim_{s → ∞} chenf₀(s)` (`= e^{-γ} / 2`). -/
def chenL₀ : ℝ := sInf (chenF₀ '' Set.Ioi 0)

private lemma chenF₀_image_nonempty : (chenF₀ '' Set.Ioi 0).Nonempty :=
  ⟨chenF₀ 1, 1, by norm_num, rfl⟩

private lemma chenf₀_le_chenF₀_any {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    chenf₀ s ≤ chenF₀ t := by
  set M : ℝ := max s t
  have hM : 0 < M := lt_of_lt_of_le hs (le_max_left _ _)
  calc chenf₀ s ≤ chenf₀ M := chenf₀_monotoneOn hs hM (le_max_left _ _)
    _ ≤ chenF₀ M := le_of_lt (chenf₀_lt_chenF₀ hM)
    _ ≤ chenF₀ t := chenF₀_antitoneOn ht hM (le_max_right _ _)

private lemma chenF₀_image_bddBelow : BddBelow (chenF₀ '' Set.Ioi 0) :=
  ⟨0, by rintro _ ⟨s, hs, rfl⟩; exact le_trans (chenf₀_nonneg hs) (le_of_lt (chenf₀_lt_chenF₀ hs))⟩

lemma chenL₀_le_chenF₀ {s : ℝ} (hs : 0 < s) : chenL₀ ≤ chenF₀ s :=
  csInf_le chenF₀_image_bddBelow ⟨s, hs, rfl⟩

lemma chenf₀_le_chenL₀ {s : ℝ} (hs : 0 < s) : chenf₀ s ≤ chenL₀ := by
  refine le_csInf chenF₀_image_nonempty ?_
  rintro _ ⟨t, ht, rfl⟩
  exact chenf₀_le_chenF₀_any hs ht

lemma log_three_div_four_le_chenL₀ : Real.log 3 / 4 ≤ chenL₀ := by
  have h4 : chenf₀ 4 = Real.log 3 / 4 := by
    have := chenf₀_eq_of_Icc (s := 4) (by norm_num) le_rfl
    norm_num at this
    exact this
  rw [← h4]
  exact chenf₀_le_chenL₀ (by norm_num)

lemma chenL₀_pos : 0 < chenL₀ := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith [log_three_div_four_le_chenL₀]

lemma chenL₀_le_one_third : chenL₀ ≤ 1 / 3 := by
  have h3 : chenF₀ 3 = 1 / 3 := chenF₀_eq_of_Ioc_three (by norm_num) le_rfl
  rw [← h3]
  exact chenL₀_le_chenF₀ (by norm_num)

lemma chenF₀_tendsto_chenL₀ : Filter.Tendsto chenF₀ Filter.atTop (nhds chenL₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, ⟨s₀, hs₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt chenF₀_image_nonempty (lt_add_of_pos_right chenL₀ hε)
  refine ⟨s₀, fun s hs => ?_⟩
  have hs_pos : 0 < s := lt_of_lt_of_le hs₀ hs
  have hlo : chenL₀ ≤ chenF₀ s := chenL₀_le_chenF₀ hs_pos
  have hhi : chenF₀ s ≤ chenF₀ s₀ := chenF₀_antitoneOn hs₀ hs_pos hs
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

lemma chenf₀_tendsto_chenL₀ : Filter.Tendsto chenf₀ Filter.atTop (nhds chenL₀) := by
  have hinv : Filter.Tendsto (fun s : ℝ => 1 / s) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlo : Filter.Tendsto (fun s : ℝ => chenF₀ s - 1 / s) Filter.atTop (nhds chenL₀) := by
    simpa using chenF₀_tendsto_chenL₀.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo chenF₀_tendsto_chenL₀ ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with s hs
    linarith [chenF₀_sub_chenf₀_le_one_div hs]
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with s hs
    exact le_of_lt (chenf₀_lt_chenF₀ hs)

/-- Normalized upper linear-sieve limit function `F(s) = chenF₀ s / chenL₀`. -/
def chenF (s : ℝ) : ℝ := chenF₀ s / chenL₀

/-- Normalized lower linear-sieve limit function `f(s) = chenf₀ s / chenL₀`. -/
def chenf (s : ℝ) : ℝ := chenf₀ s / chenL₀

theorem chenF_eq_of_le_three {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) :
    chenF s = 1 / (chenL₀ * s) := by
  unfold chenF
  rw [chenF₀_eq_of_Ioc_three hs0 hs3]
  field_simp [ne_of_gt chenL₀_pos, ne_of_gt hs0]

theorem chenf_eq_of_Icc {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    chenf s = Real.log (s - 1) / (chenL₀ * s) := by
  unfold chenf
  rw [chenf₀_eq_of_Icc hs2 hs4]
  have hs0 : s ≠ 0 := by linarith
  field_simp [ne_of_gt chenL₀_pos, hs0]

theorem chenSievePair : LinearSievePair chenF chenf where
  F_cont := chenF₀_continuousOn.div_const chenL₀
  f_cont := chenf₀_continuousOn.div_const chenL₀
  F_antitone := fun _ hx _ hy hxy => div_le_div_of_nonneg_right (chenF₀_antitoneOn hx hy hxy) (le_of_lt chenL₀_pos)
  f_monotone := fun _ hx _ hy hxy => div_le_div_of_nonneg_right (chenf₀_monotoneOn hx hy hxy) (le_of_lt chenL₀_pos)
  f_nonneg := fun s hs => div_nonneg (chenf₀_nonneg hs) (le_of_lt chenL₀_pos)
  f_le_one := fun s hs => (div_le_one chenL₀_pos).mpr (chenf₀_le_chenL₀ hs)
  one_le_F := fun s hs => (one_le_div chenL₀_pos).mpr (chenL₀_le_chenF₀ hs)
  F_tendsto_one := by
    show Filter.Tendsto (fun s => chenF₀ s / chenL₀) Filter.atTop (nhds 1)
    simpa [div_self (ne_of_gt chenL₀_pos)] using chenF₀_tendsto_chenL₀.div_const chenL₀
  f_tendsto_one := by
    show Filter.Tendsto (fun s => chenf₀ s / chenL₀) Filter.atTop (nhds 1)
    simpa [div_self (ne_of_gt chenL₀_pos)] using chenf₀_tendsto_chenL₀.div_const chenL₀
  F_const_le_three := fun s hs0 hs3 => by
    rw [chenF_eq_of_le_three hs0 hs3, chenF_eq_of_le_three (by norm_num) le_rfl]
    field_simp [ne_of_gt hs0, ne_of_gt chenL₀_pos]
  f_zero_le_two := fun s _ hs2 => by
    simp [chenf, chenf₀_eq_zero_of_le_two hs2]
  F_buchstab := fun a b ha hab => by
    have h0 := chenF₀_buchstab (by linarith) hab
    unfold chenF chenf
    rw [intervalIntegral.integral_div, ← mul_div_assoc, ← mul_div_assoc, ← sub_div, h0]
  f_buchstab := fun a b ha hab => by
    have h0 := chenf₀_buchstab ha hab
    unfold chenf chenF
    rw [intervalIntegral.integral_div, ← mul_div_assoc, ← mul_div_assoc, ← sub_div, h0]

/-! ### Section 6: Elementary Padé Bounds for `Real.log` and `chen_margin_pos` -/

/-- Padé upper bound: `log(1 + y) ≤ y * (6 + y) / (6 + 4 * y)` for all `y ≥ 0`. -/
private lemma log_one_add_le_pade {y : ℝ} (hy : 0 ≤ y) :
    Real.log (1 + y) ≤ y * (6 + y) / (6 + 4 * y) := by
  set φ : ℝ → ℝ := fun t => t * (6 + t) / (6 + 4 * t) - Real.log (1 + t)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt φ (4 * t ^ 3 / ((6 + 4 * t) ^ 2 * (1 + t))) t := by
    intro t ht
    have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
    have hden1 : 6 + 4 * t ≠ 0 := by linarith
    have hden2 : 1 + t ≠ 0 := by linarith
    have hnum : HasDerivAt (fun u : ℝ => u * (6 + u)) (6 + 2 * t) t := by
      have h1 := (hasDerivAt_id' t).fun_mul ((hasDerivAt_id' t).const_add 6)
      exact h1.congr_deriv (by ring)
    have hden : HasDerivAt (fun u : ℝ => 6 + 4 * u) 4 t := by
      have h1 := ((hasDerivAt_id' t).const_mul 4).const_add 6
      exact h1.congr_deriv (by ring)
    have hq := hnum.fun_div hden hden1
    have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t :=
      (((hasDerivAt_id' t).const_add 1).log hden2).congr_deriv (by ring)
    exact (hq.fun_sub hlog).congr_deriv (by field_simp [hden1, hden2]; ring)
  have hcont : ContinuousOn φ (Set.Ici 0) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (interior (Set.Ici (0 : ℝ))) := by
    rw [interior_Ici]
    exact fun t ht => (hderiv t (Set.mem_Ici.mpr (le_of_lt ht))).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn φ (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff fun t ht => by
      rw [interior_Ici] at ht
      rw [(hderiv t (Set.mem_Ici.mpr (le_of_lt ht))).deriv]
      have ht0 : 0 ≤ t := le_of_lt ht
      positivity
  have h0 : φ 0 ≤ φ y := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  have hφ0 : φ 0 = 0 := by simp [φ]
  linarith

/-- Padé lower bound: `2 * y / (2 + y) ≤ log(1 + y)` for all `y ≥ 0`. -/
private lemma pade_le_log_one_add {y : ℝ} (hy : 0 ≤ y) :
    2 * y / (2 + y) ≤ Real.log (1 + y) := by
  set ψ : ℝ → ℝ := fun t => Real.log (1 + t) - 2 * t / (2 + t)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt ψ (t ^ 2 / ((1 + t) * (2 + t) ^ 2)) t := by
    intro t ht
    have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
    have hden1 : 1 + t ≠ 0 := by linarith
    have hden2 : 2 + t ≠ 0 := by linarith
    have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t :=
      (((hasDerivAt_id' t).const_add 1).log hden1).congr_deriv (by ring)
    have hnum : HasDerivAt (fun u : ℝ => 2 * u) 2 t :=
      ((hasDerivAt_id' t).const_mul 2).congr_deriv (by ring)
    have hden : HasDerivAt (fun u : ℝ => 2 + u) 1 t :=
      (hasDerivAt_id' t).const_add 2
    have hq := hnum.fun_div hden hden2
    exact (hlog.fun_sub hq).congr_deriv (by field_simp [hden1, hden2]; ring)
  have hcont : ContinuousOn ψ (Set.Ici 0) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ ψ (interior (Set.Ici (0 : ℝ))) := by
    rw [interior_Ici]
    exact fun t ht => (hderiv t (Set.mem_Ici.mpr (le_of_lt ht))).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn ψ (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff fun t ht => by
      rw [interior_Ici] at ht
      rw [(hderiv t (Set.mem_Ici.mpr (le_of_lt ht))).deriv]
      have ht0 : 0 ≤ t := le_of_lt ht
      positivity
  have h0 : ψ 0 ≤ ψ y := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  linarith

theorem log_three_halves_gt : (40 / 100 : ℝ) < Real.log (3 / 2) := by
  have hsplit : Real.log (3 / 2 : ℝ) = Real.log (1 + 1 / 4) + Real.log (1 + 1 / 5) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h1 := pade_le_log_one_add (y := 1 / 4) (by norm_num)
  have h2 := pade_le_log_one_add (y := 1 / 5) (by norm_num)
  rw [hsplit]
  norm_num at h1 h2
  linarith

theorem chenIB_lt : chenIB < 37 / 100 := by
  unfold chenIB
  have hab : (1 / 8 : ℝ) ≤ 1 / 3 := by norm_num
  set f : ℝ → ℝ := fun u => Real.log (2 - 3 * u) / (u * (1 - u))
  set g : ℝ → ℝ := fun u => ((1 - 3 * u) * (7 - 3 * u)) / ((10 - 12 * u) * u * (1 - u))
  have hf_int : IntervalIntegrable f volume (1 / 8 : ℝ) (1 / 3 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    have hlog : ContinuousOn (fun u => Real.log (2 - 3 * u)) (Set.Icc (1 / 8) (1 / 3)) :=
      ContinuousOn.log (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
        (fun u hu => by linarith [hu.1, hu.2])
    exact hlog.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun u hu => by nlinarith [hu.1, hu.2])
  have hg_int : IntervalIntegrable g volume (1 / 8 : ℝ) (1 / 3 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))).div
      (((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul continuousOn_id).mul
        (continuousOn_const.sub continuousOn_id))
      (fun u hu => by
        have h1 : 0 < 10 - 12 * u := by linarith [hu.2]
        have h2 : 0 < u := by linarith [hu.1]
        have h3 : 0 < 1 - u := by linarith [hu.2]
        positivity)
  have hle_int : ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), f u ≤ ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), g u := by
    refine intervalIntegral.integral_mono_on hab hf_int hg_int fun u hu => ?_
    have hy : 0 ≤ 1 - 3 * u := by linarith [hu.2]
    have hpade := log_one_add_le_pade hy
    have h1 : 1 + (1 - 3 * u) = 2 - 3 * u := by ring
    have h2 : (1 - 3 * u) * (6 + (1 - 3 * u)) / (6 + 4 * (1 - 3 * u)) =
        ((1 - 3 * u) * (7 - 3 * u)) / (10 - 12 * u) := by ring
    rw [h1, h2] at hpade
    have hden : 0 < u * (1 - u) := mul_pos (by linarith [hu.1]) (by linarith [hu.2])
    calc f u = Real.log (2 - 3 * u) / (u * (1 - u)) := rfl
      _ ≤ (((1 - 3 * u) * (7 - 3 * u)) / (10 - 12 * u)) / (u * (1 - u)) :=
        div_le_div_of_nonneg_right hpade (le_of_lt hden)
      _ = g u := by simp only [g, div_div, mul_assoc]
  set H : ℝ → ℝ := fun u =>
    (7 / 10 : ℝ) * Real.log u - 4 * Real.log (1 - u) + (81 / 20 : ℝ) * Real.log (5 - 6 * u)
  have hg_eval : ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), g u = H (1 / 3) - H (1 / 8) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hg_int
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have h1u : 1 - u ≠ 0 := by linarith [hu.2]
    have h56 : 5 - 6 * u ≠ 0 := by linarith [hu.2]
    have hd1 : HasDerivAt (fun x => (7 / 10 : ℝ) * Real.log x) ((7 / 10 : ℝ) * (1 / u)) u :=
      (((hasDerivAt_id' u).log hu0).const_mul (7 / 10 : ℝ)).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun x => (4 : ℝ) * Real.log (1 - x)) ((4 : ℝ) * (-1 / (1 - u))) u :=
      ((((hasDerivAt_id' u).const_sub 1).log h1u).const_mul (4 : ℝ)).congr_deriv (by ring)
    have hd3 : HasDerivAt (fun x => (81 / 20 : ℝ) * Real.log (5 - 6 * x))
        ((81 / 20 : ℝ) * (-6 / (5 - 6 * u))) u :=
      (((((hasDerivAt_id' u).const_mul 6).const_sub 5).log h56).const_mul (81 / 20 : ℝ)).congr_deriv (by ring)
    refine ((hd1.fun_sub hd2).fun_add hd3).congr_deriv ?_
    simp only [g]
    have h10 : 10 - 12 * u ≠ 0 := by linarith [hu.2]
    have hden_ne : (10 - 12 * u) * u * (1 - u) ≠ 0 := mul_ne_zero (mul_ne_zero h10 hu0) h1u
    apply mul_right_cancel₀ hden_ne
    rw [div_mul_cancel₀ _ hden_ne]
    have h56_mul : (10 - 12 * u) = 2 * (5 - 6 * u) := by ring
    have ha1 : (7 / 10 : ℝ) * (1 / u) * ((10 - 12 * u) * u * (1 - u)) =
        (7 / 10 : ℝ) * (10 - 12 * u) * (1 - u) := by
      have : (1 / u) * u = 1 := one_div_mul_cancel hu0
      linear_combination (7 / 10 : ℝ) * (10 - 12 * u) * (1 - u) * this
    have ha2 : (4 : ℝ) * (-1 / (1 - u)) * ((10 - 12 * u) * u * (1 - u)) =
        -4 * (10 - 12 * u) * u := by
      have : (1 / (1 - u)) * (1 - u) = 1 := one_div_mul_cancel h1u
      linear_combination -4 * (10 - 12 * u) * u * this
    have ha3 : (81 / 20 : ℝ) * (-6 / (5 - 6 * u)) * ((10 - 12 * u) * u * (1 - u)) =
        -(243 / 5 : ℝ) * u * (1 - u) := by
      rw [h56_mul]
      have : (1 / (5 - 6 * u)) * (5 - 6 * u) = 1 := one_div_mul_cancel h56
      linear_combination -(243 / 5 : ℝ) * u * (1 - u) * this
    linear_combination ha1 - ha2 + ha3
  have hHbHa : H (1 / 3) - H (1 / 8) =
      (7 / 10 : ℝ) * Real.log (8 / 3) + 4 * Real.log (21 / 16) - (81 / 20 : ℝ) * Real.log (17 / 12) := by
    have h1 : Real.log (1 / 3 : ℝ) - Real.log (1 / 8 : ℝ) = Real.log (8 / 3 : ℝ) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    have h2 : Real.log (1 - (1 / 8 : ℝ)) - Real.log (1 - (1 / 3 : ℝ)) = Real.log (21 / 16 : ℝ) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    have h3 : Real.log (5 - 6 * (1 / 8 : ℝ)) - Real.log (5 - 6 * (1 / 3 : ℝ)) = Real.log (17 / 12 : ℝ) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    simp only [H]
    linarith
  have hl83 : Real.log (8 / 3 : ℝ) ≤ 2 * ((1 / 3 : ℝ) * (6 + 1 / 3) / (6 + 4 * (1 / 3))) +
      ((1 / 2 : ℝ) * (6 + 1 / 2) / (6 + 4 * (1 / 2))) := by
    have hsplit : Real.log (8 / 3 : ℝ) =
        2 * Real.log (1 + 1 / 3) + Real.log (1 + 1 / 2) := by
      have hmul1 : Real.log ((1 + 1 / 3 : ℝ) * (1 + 1 / 3)) =
          Real.log (1 + 1 / 3) + Real.log (1 + 1 / 3) :=
        Real.log_mul (by norm_num) (by norm_num)
      have hmul2 : Real.log (((1 + 1 / 3 : ℝ) * (1 + 1 / 3)) * (1 + 1 / 2)) =
          Real.log ((1 + 1 / 3 : ℝ) * (1 + 1 / 3)) + Real.log (1 + 1 / 2) :=
        Real.log_mul (by norm_num) (by norm_num)
      have heq : ((1 + 1 / 3 : ℝ) * (1 + 1 / 3)) * (1 + 1 / 2) = 8 / 3 := by norm_num
      rw [← heq, hmul2, hmul1]; ring
    rw [hsplit]
    linarith [log_one_add_le_pade (y := 1 / 3) (by norm_num),
      log_one_add_le_pade (y := 1 / 2) (by norm_num)]
  have hl2116 : Real.log (21 / 16 : ℝ) ≤ (5 / 16 : ℝ) * (6 + 5 / 16) / (6 + 4 * (5 / 16)) := by
    have h := log_one_add_le_pade (y := 5 / 16) (by norm_num)
    norm_num at h ⊢
    exact h
  have hl1712 : 2 * (1 / 5 : ℝ) / (2 + 1 / 5) + 2 * (13 / 72 : ℝ) / (2 + 13 / 72) ≤
      Real.log (17 / 12 : ℝ) := by
    have hsplit : Real.log (17 / 12 : ℝ) =
        Real.log (1 + 1 / 5) + Real.log (1 + 13 / 72) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hsplit]
    linarith [pade_le_log_one_add (y := 1 / 5) (by norm_num),
      pade_le_log_one_add (y := 13 / 72) (by norm_num)]
  rw [hg_eval, hHbHa] at hle_int
  norm_num at hl83 hl2116 hl1712
  linarith

theorem chen_T2_integral_eq :
    (1 / 2 : ℝ) * (∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), chenF (4 - 8 * u) / u) =
      Real.log 6 / (8 * chenL₀) := by
  have hab : (1 / 8 : ℝ) ≤ 1 / 3 := by norm_num
  have hcongr : ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), chenF (4 - 8 * u) / u =
      ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), 1 / (chenL₀ * u * (4 - 8 * u)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [chenF_eq_of_le_three (by linarith [hu.2]) (by linarith [hu.1]), div_div]
    ring_nf
  set G : ℝ → ℝ := fun u => (Real.log u - Real.log (1 - 2 * u)) / (4 * chenL₀)
  have hint : IntervalIntegrable (fun u => 1 / (chenL₀ * u * (4 - 8 * u))) volume (1 / 8 : ℝ) (1 / 3 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.div
      ((continuousOn_const.mul continuousOn_id).mul
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
      (fun u hu => ?_)
    have hL : 0 < chenL₀ := chenL₀_pos
    have hu0 : 0 < u := by linarith [hu.1]
    have h48 : 0 < 4 - 8 * u := by linarith [hu.2]
    positivity
  have hftc : ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), 1 / (chenL₀ * u * (4 - 8 * u)) = G (1 / 3) - G (1 / 8) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hint
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have h12 : 1 - 2 * u ≠ 0 := by linarith [hu.2]
    have hL : chenL₀ ≠ 0 := ne_of_gt chenL₀_pos
    have hd1 : HasDerivAt (fun x => Real.log x) (1 / u) u :=
      ((hasDerivAt_id' u).log hu0).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun x => Real.log (1 - 2 * x)) (-2 / (1 - 2 * u)) u :=
      ((((hasDerivAt_id' u).const_mul 2).const_sub 1).log h12).congr_deriv (by ring)
    refine ((hd1.fun_sub hd2).div_const (4 * chenL₀)).congr_deriv ?_
    have h48 : 4 - 8 * u = 4 * (1 - 2 * u) := by ring
    rw [h48]
    have hkey : 1 / u - -2 / (1 - 2 * u) = 1 / (u * (1 - 2 * u)) := by
      apply mul_right_cancel₀ (mul_ne_zero hu0 h12)
      rw [one_div_mul_cancel (mul_ne_zero hu0 h12)]
      have h1 : (1 / u) * u = 1 := one_div_mul_cancel hu0
      have h2 : (1 / (1 - 2 * u)) * (1 - 2 * u) = 1 := one_div_mul_cancel h12
      linear_combination (1 - 2 * u) * h1 + 2 * u * h2
    rw [hkey, div_div]
    congr 1
    ring
  have hGbGa : G (1 / 3) - G (1 / 8) = Real.log 6 / (4 * chenL₀) := by
    have hGb : G (1 / 3) = 0 := by
      simp only [G]
      norm_num
    have hGa : G (1 / 8) = -Real.log 6 / (4 * chenL₀) := by
      simp only [G]
      have hsub : Real.log (1 / 8 : ℝ) - Real.log (1 - 2 * (1 / 8 : ℝ)) = -Real.log 6 := by
        rw [← Real.log_div (by norm_num) (by norm_num)]
        have : (1 / 8 : ℝ) / (1 - 2 * (1 / 8 : ℝ)) = (6 : ℝ)⁻¹ := by norm_num
        rw [this, Real.log_inv]
      rw [hsub]
    rw [hGb, hGa]
    ring
  rw [hcongr, hftc, hGbGa]
  ring

theorem chen_margin_pos :
    (1 / 50 : ℝ) / (8 * chenL₀) ≤
      chenf 4 - (1 / 2 : ℝ) * (∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), chenF (4 - 8 * u) / u)
        - (1 / 4 : ℝ) * chenIB * chenF 2 := by
  have hf4 : chenf 4 = Real.log 3 / (4 * chenL₀) := by
    have := chenf_eq_of_Icc (s := 4) (by norm_num) le_rfl
    norm_num at this
    rw [this]; ring
  have hF2 : chenF 2 = 1 / (2 * chenL₀) := by
    have := chenF_eq_of_le_three (s := 2) (by norm_num) (by norm_num)
    rw [this]; ring
  have hlog_id : 2 * Real.log 3 - Real.log 6 = Real.log (3 / 2) := by
    have h3 : (2 : ℝ) * Real.log 3 = Real.log (3 ^ 2 : ℝ) := by
      rw [Real.log_pow]; norm_num
    rw [h3, ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hnum : (1 / 50 : ℝ) ≤ 2 * Real.log 3 - Real.log 6 - chenIB := by
    rw [hlog_id]
    linarith [log_three_halves_gt, chenIB_lt]
  have hden : 0 < 8 * chenL₀ := by linarith [chenL₀_pos]
  rw [hf4, chen_T2_integral_eq, hF2]
  have hrhs : Real.log 3 / (4 * chenL₀) - Real.log 6 / (8 * chenL₀) -
      (1 / 4 : ℝ) * chenIB * (1 / (2 * chenL₀)) =
      (2 * Real.log 3 - Real.log 6 - chenIB) / (8 * chenL₀) := by
    field_simp [ne_of_gt chenL₀_pos]
    ring
  rw [hrhs]
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden)

end RHDirect.Chen
