import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# PPL 134 (Kimberling #2 — Expulsion Sequence A007063): Partial Structural Milestone

**Scope Notice (Partial Milestone — NOT the full open conjecture):**
The full Kimberling expulsion conjecture (`A007063`, asking whether every positive integer
eventually appears in the main diagonal) remains OPEN. This file formalizes the unconditional
structural theorems proved in `scripts/ppl134_findings.md`:

1. **Entry & Active-Zone Dynamics (`pre_entry_outside_active`, `entry_in_active_zone`,
   `activePosStep_invariant`):**
   Every `x ≥ 1` enters the active zone `1 ≤ p ≤ 2s - 1` at `s₀ = (x + 4) / 3` with
   `p_{s₀} = x + 1 - s₀`, and never leaves the active zone prior to expulsion (`p = s`).
2. **Exact `(n, m)` Active-Zone Bijection (`activeF_mem_target`, `activeFinv_mem_source`,
   `activeFinv_left_inv`, `activeF_right_inv`):**
   With `n = s + 3` and `m = 2s + 3 - p`, the active step maps `[4, 2n - 4] \ {n}` bijectively
   onto `[7, 2(n + 1) - 4]`, with explicit inverse `activeFinv`.
3. **Single-Equation Branchless Collapse (`branchless_collapse`, `YCoord_mod_four`):**
   Setting `Y(s, p) = 4 * (s - p) + 1`, expulsion is `Y = 1`, `Y % 4 = 1` is preserved,
   and both active branches collapse into `Y_{s+1} = 4s + 7 - 2 * |Y_s|`.
4. **No Ultimately Periodic Branch Sequence (`no_ultimately_periodic_branches`):**
   No trajectory remaining in the active zone can have an ultimately periodic L/R branch sequence.
5. **Universal Backward Lifting Theorem (`universal_backward_lifting`):**
   Every valid backward-word path `u 0^k` ending at an entry point `(n₀, m₀)` with
   `m₀ ∈ {4, 5, 6}` lifts unconditionally to an infinite closed-form family
   `s_t = (m₀ * 2^(r + k + t * d) - B) / A - 3` expelling `3 * (s_t - s) + x - 3 * t * d`.
-/

namespace PPL134

section ActiveZoneAndCollapse

/-- Active-zone row-position step for Kimberling's `RILI` array (`1 ≤ p ≤ 2s - 1`, `p ≠ s`). -/
def activePosStep (s p : ℤ) : ℤ :=
  if p < s then 2 * (s - p) else 2 * (p - s) - 1

/-- Full Kimberling step starting from `p ≥ 1` (`none` when expelled at `p = s`). -/
def kimberlingStep (s p : ℤ) : Option ℤ :=
  if p = s then none
  else if p ≤ 2 * s - 1 then some (activePosStep s p)
  else some (p - 1)

/-- `Y`-coordinate for the single-equation branchless collapse. -/
def YCoord (s p : ℤ) : ℤ :=
  4 * (s - p) + 1

/-- Entry stage `s₀ = ⌈(x + 2) / 3⌉ = (x + 4) / 3` for initial value `x ≥ 1`. -/
def entryStage (x : ℤ) : ℤ :=
  (x + 4) / 3

/-- Prior to `entryStage x`, `p_s = x + 1 - s` remains outside the active zone (`p_s ≥ 2s`)
and decrements by `1` per stage. -/
theorem pre_entry_outside_active (x s : ℤ) (_hx : 1 ≤ x) (_hs : 1 ≤ s)
    (hlt : s < entryStage x) :
    2 * s ≤ x + 1 - s ∧ kimberlingStep s (x + 1 - s) = some (x + 1 - (s + 1)) := by
  have h1 : 3 * s ≤ x + 1 := by
    have : s + 1 ≤ (x + 4) / 3 := hlt
    omega
  have hge : 2 * s ≤ x + 1 - s := by omega
  refine ⟨hge, ?_⟩
  unfold kimberlingStep
  have hne : x + 1 - s ≠ s := by omega
  have hnotle : ¬ x + 1 - s ≤ 2 * s - 1 := by omega
  simp [hne, hnotle]
  ring

/-- At `s₀ = entryStage x`, `p_{s₀} = x + 1 - s₀` lies in the active zone `[1, 2s₀ - 1]`
and satisfies `2s₀ - 3 ≤ p_{s₀} ≤ 2s₀ - 1`. -/
theorem entry_in_active_zone (x : ℤ) (hx : 1 ≤ x) :
    let s₀ := entryStage x
    let p₀ := x + 1 - s₀
    1 ≤ s₀ ∧ 1 ≤ p₀ ∧ p₀ ≤ 2 * s₀ - 1 ∧ 2 * s₀ - 3 ≤ p₀ := by
  dsimp only [entryStage]
  omega

/-- The active zone `1 ≤ p ≤ 2s - 1` is invariant under `activePosStep`. -/
theorem activePosStep_invariant (s p : ℤ) (_hs : 1 ≤ s) (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * s - 1)
    (hne : p ≠ s) :
    1 ≤ activePosStep s p ∧ activePosStep s p ≤ 2 * (s + 1) - 1 := by
  unfold activePosStep
  split_ifs <;> omega

/-- Theorem 1B (Invariant): `YCoord s p % 4 = 1`, and expulsion `p = s` iff `YCoord s p = 1`. -/
theorem YCoord_mod_four (s p : ℤ) : YCoord s p % 4 = 1 := by
  unfold YCoord
  omega

theorem YCoord_eq_one_iff (s p : ℤ) : YCoord s p = 1 ↔ p = s := by
  unfold YCoord
  omega

/-- Theorem 1B (Single-Equation Branchless Collapse):
For every `1 ≤ p ≤ 2s - 1` with `p ≠ s`, both branches collapse into
`Y_{s+1} = 4s + 7 - 2 |Y_s|`. -/
theorem branchless_collapse (s p : ℤ) (_hs : 1 ≤ s) (_hp1 : 1 ≤ p) (_hp2 : p ≤ 2 * s - 1)
    (hne : p ≠ s) :
    YCoord (s + 1) (activePosStep s p) = 4 * s + 7 - 2 * |YCoord s p| := by
  unfold YCoord activePosStep
  rcases lt_trichotomy p s with hlt | rfl | hgt
  · have habs : |4 * (s - p) + 1| = 4 * (s - p) + 1 := abs_of_nonneg (by omega)
    simp [hlt, habs]
    ring
  · exact (hne rfl).elim
  · have hnot : ¬ p < s := by omega
    have habs : |4 * (s - p) + 1| = -(4 * (s - p) + 1) := abs_of_neg (by omega)
    simp [hnot, habs]
    ring

end ActiveZoneAndCollapse

section BijectionNM

/-- Forward map in `(n, m)` coordinates (`n = s + 3`, `m = 2s + 3 - p`). -/
def activeF (n m : ℤ) : ℤ :=
  if m < n then 2 * m else 4 * n - 1 - 2 * m

/-- Explicit backward inverse `F⁻¹(n', m')` at stage `n' = n + 1`. -/
def activeFinv (n' m' : ℤ) : ℤ :=
  if m' % 2 = 0 then m' / 2 else 2 * n' - (m' + 5) / 2

/-- Conjugacy between `activePosStep` and `activeF` under `n = s + 3`, `m = 2s + 3 - p`
(for `p ≠ s`). -/
theorem activePosStep_eq_activeF (s p : ℤ) (hne : p ≠ s) :
    2 * (s + 1) + 3 - activePosStep s p = activeF (s + 3) (2 * s + 3 - p) := by
  unfold activePosStep activeF
  split_ifs <;> omega

/-- Theorem 1A (Exact `(n, m)` Active-Zone Bijection):
For any `n ≥ 4`, `activeF n` maps `{m | 4 ≤ m ∧ m ≤ 2*n - 4 ∧ m ≠ n}` bijectively onto
`{m' | 7 ≤ m' ∧ m' ≤ 2*(n+1) - 4}` with inverse `activeFinv (n + 1)`. -/
theorem activeF_mem_target (n m : ℤ) (_hn : 4 ≤ n) (hm1 : 4 ≤ m) (hm2 : m ≤ 2 * n - 4)
    (hne : m ≠ n) :
    7 ≤ activeF n m ∧ activeF n m ≤ 2 * (n + 1) - 4 := by
  unfold activeF
  split_ifs <;> omega

theorem activeFinv_mem_source (n m' : ℤ) (hn : 4 ≤ n) (hm1 : 7 ≤ m')
    (hm2 : m' ≤ 2 * (n + 1) - 4) :
    4 ≤ activeFinv (n + 1) m' ∧ activeFinv (n + 1) m' ≤ 2 * n - 4 ∧
      activeFinv (n + 1) m' ≠ n := by
  unfold activeFinv
  split_ifs <;> omega

theorem activeFinv_left_inv (n m : ℤ) (_hn : 4 ≤ n) (_hm1 : 4 ≤ m) (_hm2 : m ≤ 2 * n - 4)
    (_hne : m ≠ n) :
    activeFinv (n + 1) (activeF n m) = m := by
  unfold activeF activeFinv
  split_ifs <;> omega

theorem activeF_right_inv (n m' : ℤ) (_hn : 4 ≤ n) (_hm1 : 7 ≤ m')
    (_hm2 : m' ≤ 2 * (n + 1) - 4) :
    activeF n (activeFinv (n + 1) m') = m' := by
  unfold activeF activeFinv
  split_ifs <;> omega

end BijectionNM

section NoPeriodicBranches

/-- Step parameterized by explicit branch `br : Bool` (`true` = L branch, `false` = R branch). -/
def branchStep (br : Bool) (s p : ℤ) : ℤ :=
  if br then 2 * (s - p) else 2 * (p - s) - 1

/-- Iterated branch step over `t` consecutive stages starting at `s` with branch schedule `w`. -/
def iterBranch (w : ℕ → Bool) (s : ℤ) : ℕ → ℤ → ℤ
  | 0, p => p
  | t + 1, p => branchStep (w (s.toNat + t)) (s + t) (iterBranch w s t p)

/-- Affine decomposition of `t` steps starting at `(s, p)`:
`iterBranch w s t p = e * p + a * s + b`, where `|e| = 2^t` and `a, b : ℤ`
depend only on the length-`t` window `(w(off), ..., w(off + t - 1))`. -/
def blockAffine (w : ℕ → Bool) (off : ℕ) : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 0, 0)
  | t + 1 =>
    let (e, a, b) := blockAffine w off t
    if w (off + t) then
      (-2 * e, 2 - 2 * a, -2 * b + 2 * (t : ℤ))
    else
      (2 * e, 2 * a - 2, 2 * b - 2 * (t : ℤ) - 1)

private lemma blockAffine_sign_abs (w : ℕ → Bool) (off t : ℕ) :
    |(blockAffine w off t).1| = (2 : ℤ) ^ t := by
  induction t with
  | zero => simp [blockAffine]
  | succ t ih =>
    simp only [blockAffine]
    split_ifs <;> simp [abs_mul, ih, pow_succ']

private lemma iterBranch_eq_blockAffine (w : ℕ → Bool) (s : ℤ) (_hs : 0 ≤ s) (t : ℕ) (p : ℤ) :
    iterBranch w s t p =
      let (e, a, b) := blockAffine w s.toNat t
      e * p + a * s + b := by
  induction t with
  | zero => simp [iterBranch, blockAffine]
  | succ t ih =>
    simp only [iterBranch, blockAffine, ih, branchStep]
    split_ifs <;> ring

private lemma w_add_mul_period (w : ℕ → Bool) (T : ℕ) (hper : ∀ k, w (k + T) = w k)
    (m n : ℕ) : w (n + m * T) = w n := by
  induction m with
  | zero => simp
  | succ m ihm =>
    have h1 : n + (m + 1) * T = (n + m * T) + T := by ring
    rw [h1, hper, ihm]

private lemma blockAffine_periodic (w : ℕ → Bool) (T : ℕ)
    (hper : ∀ k, w (k + T) = w k) (off t k : ℕ) :
    blockAffine w (off + k * T) t = blockAffine w off t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [blockAffine, ih]
    have hw : w (off + k * T + t) = w (off + t) := by
      have h1 : off + k * T + t = (off + t) + k * T := by ring
      rw [h1]
      exact w_add_mul_period w T hper k (off + t)
    simp [hw]

/-- Tent map on `ℚ`: `tentQ r = 2 * |r - 1|`. -/
def tentQ (r : ℚ) : ℚ :=
  2 * |r - 1|

private lemma tentQ_of_le {r : ℚ} (hr : r ≤ 1) : tentQ r = 2 * (1 - r) := by
  unfold tentQ
  rw [abs_of_nonpos (sub_nonpos.mpr hr)]
  ring

private lemma tentQ_of_ge {r : ℚ} (hr : 1 ≤ r) : tentQ r = 2 * (r - 1) := by
  unfold tentQ
  rw [abs_of_nonneg (sub_nonneg.mpr hr)]

private lemma sq_lt_pow_two (m : ℕ) (hm : 5 ≤ m) : m ^ 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1) ^ 2 < 2 * k ^ 2 := by nlinarith
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

private lemma pow_two_gt_linear (C₀ C₁ : ℚ) :
    ∃ k : ℕ, C₀ + C₁ * (k : ℚ) < (2 : ℚ) ^ k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|C₀| + |C₁| + 5)
  refine ⟨N + 5, ?_⟩
  have hm : 5 ≤ N + 5 := by omega
  have hsq : ((N + 5 : ℕ) : ℚ) ^ 2 < (2 : ℚ) ^ (N + 5) := by
    exact_mod_cast sq_lt_pow_two (N + 5) hm
  have hC : C₀ + C₁ * ((N + 5 : ℕ) : ℚ) ≤ (|C₀| + |C₁|) * ((N + 5 : ℕ) : ℚ) := by
    have hnn : (1 : ℚ) ≤ ((N + 5 : ℕ) : ℚ) := by norm_cast; omega
    nlinarith [le_abs_self C₀, le_abs_self C₁, abs_nonneg C₀, abs_nonneg C₁]
  have hlt : (|C₀| + |C₁|) * ((N + 5 : ℕ) : ℚ) < ((N + 5 : ℕ) : ℚ) ^ 2 := by
    have hpos : (0 : ℚ) < ((N + 5 : ℕ) : ℚ) := by positivity
    have h1 : |C₀| + |C₁| < ((N + 5 : ℕ) : ℚ) := by push_cast; linarith
    nlinarith
  linarith

private lemma tentQ_iter_form {d : ℕ} (_hd_gt : 1 < d) (_hd_odd : Odd d)
    {u : ℕ} (hu1 : 0 < u) (hu2 : u < 2 * d) (hud : u ≠ d) (hcop : Nat.Coprime u d) :
    ∃ b : ℕ, 1 ≤ b ∧ b < d ∧ Nat.Coprime b d ∧
      tentQ ((u : ℚ) / (d : ℚ)) = (2 * (b : ℚ)) / (d : ℚ) := by
  let b : ℕ := if u < d then d - u else u - d
  have hb1 : 1 ≤ b := by dsimp [b]; split_ifs <;> omega
  have hb2 : b < d := by dsimp [b]; split_ifs <;> omega
  have hbcop : Nat.Coprime b d := by
    dsimp [b]
    split_ifs with h
    · refine Nat.coprime_of_dvd fun p hp hpb hpd => ?_
      have hpu : p ∣ u := by
        have hu_eq : u = d - (d - u) := by omega
        rw [hu_eq]
        exact Nat.dvd_sub hpd hpb
      exact hp.not_dvd_one (hcop.symm ▸ Nat.dvd_gcd hpd hpu)
    · exact (Nat.coprime_sub_self_left (by omega)).mpr hcop
  refine ⟨b, hb1, hb2, hbcop, ?_⟩
  have hd_pos : (0 : ℚ) < (d : ℚ) := by positivity
  dsimp [b]
  split_ifs with h
  · have hr : (u : ℚ) / (d : ℚ) ≤ 1 := by rw [div_le_one hd_pos]; exact_mod_cast le_of_lt h
    rw [tentQ_of_le hr]
    have hsub : ((d - u : ℕ) : ℚ) = (d : ℚ) - (u : ℚ) := by exact_mod_cast Int.ofNat_sub (le_of_lt h)
    rw [hsub]
    field_simp
  · have hle : d ≤ u := by omega
    have hr : 1 ≤ (u : ℚ) / (d : ℚ) := by rw [one_le_div hd_pos]; exact_mod_cast hle
    rw [tentQ_of_ge hr]
    have hsub : ((u - d : ℕ) : ℚ) = (u : ℚ) - (d : ℚ) := by exact_mod_cast Int.ofNat_sub hle
    rw [hsub]
    field_simp

private lemma tentQ_iter_mem {d : ℕ} (hd_gt : 1 < d) (hd_odd : Odd d)
    {r₀ : ℚ} (h0 : 0 < r₀) (h2 : r₀ < 2) (hne1 : r₀ ≠ 1)
    (hden : r₀.den = d)
    (hiter : ∀ n : ℕ, 0 < tentQ^[n] r₀ ∧ tentQ^[n] r₀ < 2 ∧ tentQ^[n] r₀ ≠ 1) :
    ∀ n : ℕ, 1 ≤ n → ∃ b : ℕ, 1 ≤ b ∧ b < d ∧ Nat.Coprime b d ∧
      tentQ^[n] r₀ = (2 * (b : ℚ)) / (d : ℚ) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have hd_pos : (0 : ℚ) < (d : ℚ) := by positivity
    have hr_pos_num : 0 < r₀.num := Rat.num_pos.mpr h0
    let u : ℕ := r₀.num.natAbs
    have hu_z : (u : ℤ) = r₀.num := Int.natAbs_of_nonneg (le_of_lt hr_pos_num)
    have hu_eq : (u : ℚ) = (r₀.num : ℚ) := by exact_mod_cast hu_z
    have hr_eq : r₀ = (u : ℚ) / (d : ℚ) := by
      rw [hu_eq, ← hden]
      exact (Rat.num_div_den r₀).symm
    have hu1 : 0 < u := by
      have : (0 : ℚ) < (u : ℚ) := by rw [hu_eq]; exact_mod_cast hr_pos_num
      exact_mod_cast this
    have hu2 : u < 2 * d := by
      have : (u : ℚ) / (d : ℚ) < 2 := by rw [← hr_eq]; exact h2
      have : (u : ℚ) < 2 * (d : ℚ) := (div_lt_iff₀ hd_pos).mp this
      exact_mod_cast this
    have hud : u ≠ d := by
      intro heq
      apply hne1
      rw [hr_eq, heq]
      field_simp
    have hcop : Nat.Coprime u d := by rw [← hden]; exact r₀.reduced
    obtain ⟨b, hb1, hb2, hbcop, hform⟩ := tentQ_iter_form hd_gt hd_odd hu1 hu2 hud hcop
    rw [Function.iterate_one, hr_eq]
    exact ⟨b, hb1, hb2, hbcop, hform⟩
  | succ k hk ih =>
    obtain ⟨b, hb1, hb2, hbcop, hk_eq⟩ := ih
    have hk_props := hiter k
    have hcop2 : Nat.Coprime (2 * b) d :=
      Nat.Coprime.mul_left (Nat.coprime_two_left.mpr hd_odd) hbcop
    have h2b1 : 0 < 2 * b := by omega
    have h2b2 : 2 * b < 2 * d := by omega
    have h2bd : 2 * b ≠ d := by
      intro heq
      have hne : tentQ^[k] r₀ = 1 := by
        rw [hk_eq]
        have hq : (2 : ℚ) * (b : ℚ) = (d : ℚ) := by exact_mod_cast heq
        have hd0 : (d : ℚ) ≠ 0 := by positivity
        rw [hq, div_self hd0]
      exact hk_props.2.2 hne
    obtain ⟨b', hb'1, hb'2, hb'cop, hform⟩ :=
      tentQ_iter_form hd_gt hd_odd h2b1 h2b2 h2bd hcop2
    refine ⟨b', hb'1, hb'2, hb'cop, ?_⟩
    rw [Function.iterate_succ_apply', hk_eq]
    have hcast : ((2 * b : ℕ) : ℚ) / (d : ℚ) = (2 * (b : ℚ)) / (d : ℚ) := by
      push_cast; ring
    rw [← hcast]
    exact hform

private lemma linear_bound_contradicts_exp (T : ℕ) (hT : 1 ≤ T) (δ : ℕ → ℚ)
    (A₀ A₁ : ℚ) (habs : ∀ m, |δ m| = (2 : ℚ) ^ (m * T) * |δ 0|)
    (hbnd : ∀ m, |δ m| ≤ A₀ + A₁ * (m : ℚ)) :
    δ 0 = 0 := by
  by_contra hne
  have hpos : 0 < |δ 0| := abs_pos.mpr hne
  obtain ⟨m, hm⟩ := pow_two_gt_linear (A₀ / |δ 0|) (A₁ / |δ 0|)
  have h2m : (2 : ℚ) ^ m ≤ (2 : ℚ) ^ (m * T) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right m hT)
  have h1 : (2 : ℚ) ^ m * |δ 0| ≤ |δ m| := by
    rw [habs m]; exact mul_le_mul_of_nonneg_right h2m (abs_nonneg _)
  have h2 : |δ m| ≤ (A₀ / |δ 0| + A₁ / |δ 0| * (m : ℚ)) * |δ 0| := by
    have hle := hbnd m
    have heq : (A₀ / |δ 0| + A₁ / |δ 0| * (m : ℚ)) * |δ 0| = A₀ + A₁ * (m : ℚ) := by field_simp
    linarith
  have h3 : (A₀ / |δ 0| + A₁ / |δ 0| * (m : ℚ)) * |δ 0| < (2 : ℚ) ^ m * |δ 0| :=
    mul_lt_mul_of_pos_right hm hpos
  linarith

private lemma slope_le_of_forall (a b c : ℚ) (s₀ T : ℕ) (hT : 1 ≤ T)
    (hc : ∀ k : ℕ, a * ((s₀ : ℚ) + (k : ℚ) * (T : ℚ)) + b ≤
      c * ((s₀ : ℚ) + (k : ℚ) * (T : ℚ))) :
    a ≤ c := by
  by_contra hgt
  have hlt : c < a := lt_of_not_ge hgt
  have hT_pos : (0 : ℚ) < (T : ℚ) := by positivity
  have hdiff_pos : 0 < (a - c) * (T : ℚ) := mul_pos (sub_pos.mpr hlt) hT_pos
  obtain ⟨k, hk⟩ := exists_nat_gt ((|b| + |a - c| * (s₀ : ℚ) + 1) / ((a - c) * (T : ℚ)))
  have hk' := hc k
  have hmul : |b| + |a - c| * (s₀ : ℚ) + 1 < (a - c) * (T : ℚ) * (k : ℚ) := by
    have h1 := (div_lt_iff₀ hdiff_pos).mp hk
    linarith [show (k : ℚ) * ((a - c) * (T : ℚ)) = (a - c) * (T : ℚ) * (k : ℚ) by ring]
  have hge0 : (a - c) * (s₀ : ℚ) ≥ -(|a - c| * (s₀ : ℚ)) := by nlinarith [neg_abs_le (a - c)]
  have hgeB : b ≥ -|b| := neg_abs_le _
  nlinarith

private lemma slope_ge_of_forall (a b c : ℚ) (s₀ T : ℕ) (hT : 1 ≤ T)
    (hc : ∀ k : ℕ, c * ((s₀ : ℚ) + (k : ℚ) * (T : ℚ)) ≤
      a * ((s₀ : ℚ) + (k : ℚ) * (T : ℚ)) + b) :
    c ≤ a := by
  have h := slope_le_of_forall (-a) (-b) (-c) s₀ T hT (fun k => by linarith [hc k])
  linarith

private lemma all_two_R_branch_absurd (p : ℕ → ℤ) (s₀ T : ℕ) (hT : 1 ≤ T)
    (hp_hi : ∀ s ≥ s₀, p s ≤ 2 * (s : ℤ) - 1)
    (w : ℕ → Bool)
    (hstep_w : ∀ k : ℕ, p (s₀ + k + 1) = branchStep (w k) ((s₀ + k : ℕ) : ℤ) (p (s₀ + k)))
    (α β : ℕ → ℚ)
    (hp_exact : ∀ j k : ℕ, (p (s₀ + j + k * T) : ℚ) = α j * ((s₀ + j + k * T : ℕ) : ℚ) + β j)
    (hall2 : ∀ i : ℕ, α i = 2)
    (hall_false : ∀ i : ℕ, w i = false) :
    False := by
  have hR_step : ∀ k : ℕ, p (s₀ + k + 1) - (2 * ((s₀ + k + 1 : ℕ) : ℤ) + 3) =
      2 * (p (s₀ + k) - (2 * ((s₀ + k : ℕ) : ℤ) + 3)) := by
    intro k
    have hs := hstep_w k
    rw [hall_false k] at hs
    simp only [branchStep, Bool.false_eq_true, ↓reduceIte] at hs
    push_cast
    omega
  have hR_iter : ∀ m : ℕ, p (s₀ + m) - (2 * ((s₀ + m : ℕ) : ℤ) + 3) =
      (2 : ℤ) ^ m * (p s₀ - (2 * (s₀ : ℤ) + 3)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      have h1 : s₀ + (m + 1) = s₀ + m + 1 := by ring
      rw [h1]
      have hs := hR_step m
      have h3 : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by ring
      rw [h3, hs]
      linarith [ihm]
  have hp0_eq : (p s₀ : ℚ) = 2 * (s₀ : ℚ) + β 0 := by simpa [hall2 0] using hp_exact 0 0
  have hpT_eq : (p (s₀ + T) : ℚ) = 2 * ((s₀ + T : ℕ) : ℚ) + β 0 := by
    simpa [hall2 0] using hp_exact 0 1
  have hRT : ((p (s₀ + T) : ℚ) - (2 * ((s₀ + T : ℕ) : ℚ) + 3)) =
      (2 : ℚ) ^ T * ((p s₀ : ℚ) - (2 * (s₀ : ℚ) + 3)) := by
    exact_mod_cast hR_iter T
  have hβ3 : β 0 = 3 := by
    rw [hp0_eq, hpT_eq] at hRT
    have h2ne1 : (2 : ℚ) ^ T - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ (2 : ℚ) ^ T := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hT
      linarith
    have hmul : ((2 : ℚ) ^ T - 1) * (β 0 - 3) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h
    · exact (h2ne1 h).elim
    · linarith
  have hp0_hi : (p s₀ : ℚ) ≤ 2 * (s₀ : ℚ) - 1 := by exact_mod_cast hp_hi s₀ (le_refl s₀)
  linarith [hp0_eq, hβ3, hp0_hi]

/-- Theorem 2 (No Ultimately Periodic Branch Sequence):
Suppose `p : ℕ → ℤ` remains in the active zone `[1, 2s - 1] \ {s}` under `activePosStep`
for all `s ≥ s₀` (`1 ≤ s₀`). Then its L/R branch sequence `s ↦ decide (p s < (s : ℤ))`
cannot be periodic on `[s₀, ∞)` for any period `T ≥ 1`. -/
theorem no_ultimately_periodic_branches (p : ℕ → ℤ) (s₀ : ℕ) (_hs₀ : 1 ≤ s₀)
    (hp_lo : ∀ s ≥ s₀, 1 ≤ p s)
    (hp_hi : ∀ s ≥ s₀, p s ≤ 2 * (s : ℤ) - 1)
    (_hp_ne : ∀ s ≥ s₀, p s ≠ (s : ℤ))
    (hp_step : ∀ s ≥ s₀, p (s + 1) = activePosStep (s : ℤ) (p s))
    (T₀ : ℕ) (hT₀ : 1 ≤ T₀)
    (hper₀ : ∀ s ≥ s₀, decide (p (s + T₀) < (s + T₀ : ℤ)) = decide (p s < (s : ℤ))) :
    False := by
  classical
  let w : ℕ → Bool := fun j => decide (p (s₀ + j) < ((s₀ + j : ℕ) : ℤ))
  have hex_per : ∃ T, 1 ≤ T ∧ ∀ j, w (j + T) = w j := by
    refine ⟨T₀, hT₀, fun j => ?_⟩
    have h := hper₀ (s₀ + j) (by omega)
    dsimp only [w]
    have h1 : s₀ + j + T₀ = s₀ + (j + T₀) := by ring
    have h2 : ((s₀ + j : ℕ) : ℤ) + (T₀ : ℤ) = ((s₀ + (j + T₀) : ℕ) : ℤ) := by push_cast; ring
    have h3 : ((s₀ + j : ℕ) : ℤ) = (s₀ + j : ℤ) := by push_cast; ring
    rw [h1, h2] at h
    rw [h3]
    exact h
  let T : ℕ := Nat.find hex_per
  have hT_spec : 1 ≤ T ∧ ∀ j, w (j + T) = w j := Nat.find_spec hex_per
  have hT : 1 ≤ T := hT_spec.1
  have hper : ∀ j, w (j + T) = w j := hT_spec.2
  have hT_min : ∀ T', 1 ≤ T' → T' < T → ∃ j, w (j + T') ≠ w j := by
    intro T' hT'1 hT'lt
    have hnot := Nat.find_min hex_per hT'lt
    push Not at hnot
    exact hnot hT'1
  have hstep_w : ∀ k : ℕ, p (s₀ + k + 1) = branchStep (w k) ((s₀ + k : ℕ) : ℤ) (p (s₀ + k)) := by
    intro k
    have h1 := hp_step (s₀ + k) (by omega)
    dsimp only [w]
    unfold activePosStep at h1
    unfold branchStep
    by_cases hlt : p (s₀ + k) < ((s₀ + k : ℕ) : ℤ)
    · have hlt' : p (s₀ + k) < (s₀ + k : ℤ) := by push_cast at hlt; exact hlt
      simp [hlt'] at h1 ⊢; exact h1
    · have hlt' : ¬ p (s₀ + k) < (s₀ + k : ℤ) := by push_cast at hlt; exact hlt
      simp [hlt'] at h1 ⊢; exact h1
  let w0 : ℕ → Bool := fun s => if s₀ ≤ s then w (s - s₀) else false
  have hw0_shift : ∀ m : ℕ, w0 (s₀ + m) = w m := fun m => by simp [w0]
  have hiter_p : ∀ j t : ℕ,
      p (s₀ + j + t) = iterBranch w0 ((s₀ + j : ℕ) : ℤ) t (p (s₀ + j)) := by
    intro j t
    induction t with
    | zero => simp [iterBranch]
    | succ t ih =>
      have h1 : s₀ + j + (t + 1) = s₀ + (j + t) + 1 := by ring
      rw [h1, hstep_w (j + t)]
      simp only [iterBranch]
      have hto : ((s₀ + j : ℕ) : ℤ).toNat + t = s₀ + j + t := by omega
      rw [hto, Nat.add_assoc, hw0_shift (j + t)]
      have hcast : ((s₀ + j : ℕ) : ℤ) + (t : ℤ) = ((s₀ + (j + t) : ℕ) : ℤ) := by push_cast; ring
      have ih' : p (s₀ + (j + t)) = iterBranch w0 ((s₀ + j : ℕ) : ℤ) t (p (s₀ + j)) := by
        simpa [Nat.add_assoc] using ih
      rw [hcast, ih']
  let E : ℕ → ℤ := fun j => (blockAffine w j T).1
  let A : ℕ → ℤ := fun j => (blockAffine w j T).2.1
  let B : ℕ → ℤ := fun j => (blockAffine w j T).2.2
  have hblock_shift : ∀ j : ℕ, blockAffine w0 (s₀ + j) T = blockAffine w j T := by
    intro j
    have gen : ∀ t : ℕ, blockAffine w0 (s₀ + j) t = blockAffine w j t := by
      intro t
      induction t with
      | zero => rfl
      | succ t iht =>
        simp only [blockAffine, iht]
        have hw : w0 (s₀ + j + t) = w (j + t) := by
          rw [Nat.add_assoc]; exact hw0_shift (j + t)
        simp [hw]
    exact gen T
  have hE_abs : ∀ j, |E j| = (2 : ℤ) ^ T := fun j => blockAffine_sign_abs w j T
  have hE_ne1 : ∀ j, (1 : ℚ) - (E j : ℚ) ≠ 0 := by
    intro j heq
    have h1 : E j = 1 := by exact_mod_cast (sub_eq_zero.mp heq).symm
    have h2 : |E j| = 1 := by rw [h1]; norm_num
    rw [hE_abs j] at h2
    have hpow : (2 : ℤ) ≤ (2 : ℤ) ^ T := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hT
    omega
  let α : ℕ → ℚ := fun j => (A j : ℚ) / (1 - (E j : ℚ))
  let β : ℕ → ℚ := fun j => ((B j : ℚ) - α j * (T : ℚ)) / (1 - (E j : ℚ))
  have hstep_affine : ∀ j k : ℕ,
      p (s₀ + j + (k + 1) * T) =
        E j * p (s₀ + j + k * T) + A j * ((s₀ + j + k * T : ℕ) : ℤ) + B j := by
    intro j k
    have h1 : s₀ + j + (k + 1) * T = s₀ + (j + k * T) + T := by ring
    rw [h1, hiter_p (j + k * T) T]
    have hs_nn : (0 : ℤ) ≤ ((s₀ + (j + k * T) : ℕ) : ℤ) := by positivity
    have hiter := iterBranch_eq_blockAffine w0 ((s₀ + (j + k * T) : ℕ) : ℤ) hs_nn T (p (s₀ + (j + k * T)))
    have hto : ((s₀ + (j + k * T) : ℕ) : ℤ).toNat = s₀ + (j + k * T) := Int.toNat_natCast _
    rw [hto] at hiter
    have hba : blockAffine w0 (s₀ + (j + k * T)) T = blockAffine w j T := by
      rw [hblock_shift, blockAffine_periodic w T hper]
    rw [hba] at hiter
    dsimp only at hiter
    rw [hiter]
    have heq : s₀ + (j + k * T) = s₀ + j + k * T := by ring
    rw [heq]
  have hp_exact : ∀ j k : ℕ,
      (p (s₀ + j + k * T) : ℚ) = α j * ((s₀ + j + k * T : ℕ) : ℚ) + β j := by
    intro j k
    let pstar : ℕ → ℚ := fun s => α j * (s : ℚ) + β j
    have hpstar_step : ∀ s : ℚ,
        (E j : ℚ) * (α j * s + β j) + (A j : ℚ) * s + (B j : ℚ) =
          α j * (s + (T : ℚ)) + β j := by
      intro s
      have hD : (1 : ℚ) - (E j : ℚ) ≠ 0 := hE_ne1 j
      dsimp only [α, β]
      field_simp
      ring
    let δ : ℕ → ℚ := fun m => (p (s₀ + j + m * T) : ℚ) - pstar (s₀ + j + m * T)
    have hδ_step : ∀ m : ℕ, δ (m + 1) = (E j : ℚ) * δ m := by
      intro m
      dsimp only [δ, pstar]
      have hst : (p (s₀ + j + (m + 1) * T) : ℚ) =
          (E j : ℚ) * (p (s₀ + j + m * T) : ℚ) +
            (A j : ℚ) * ((s₀ + j + m * T : ℕ) : ℚ) + (B j : ℚ) := by
        exact_mod_cast hstep_affine j m
      have hs_cast : ((s₀ + j + (m + 1) * T : ℕ) : ℚ) =
          ((s₀ + j + m * T : ℕ) : ℚ) + (T : ℚ) := by push_cast; ring
      have hs_eq := hpstar_step ((s₀ + j + m * T : ℕ) : ℚ)
      rw [hst, hs_cast]
      linarith
    have hδ_abs : ∀ m : ℕ, |δ m| = (2 : ℚ) ^ (m * T) * |δ 0| := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [hδ_step m, abs_mul, ihm]
        have hEabs : |(E j : ℚ)| = (2 : ℚ) ^ T := by exact_mod_cast hE_abs j
        rw [hEabs]
        have hpow : (2 : ℚ) ^ ((m + 1) * T) = (2 : ℚ) ^ T * (2 : ℚ) ^ (m * T) := by
          rw [Nat.add_mul, Nat.one_mul, pow_add, mul_comm]
        rw [hpow]
        ring
    have hδ0 : δ 0 = 0 := by
      apply linear_bound_contradicts_exp T hT δ
        (2 * ((s₀ + j : ℕ) : ℚ) + |α j| * ((s₀ + j : ℕ) : ℚ) + |β j|)
        (2 * (T : ℚ) + |α j| * (T : ℚ))
        hδ_abs
      intro m
      have hp1 : (1 : ℚ) ≤ (p (s₀ + j + m * T) : ℚ) := by exact_mod_cast hp_lo _ (by omega)
      have hp2 : (p (s₀ + j + m * T) : ℚ) ≤ 2 * ((s₀ + j + m * T : ℕ) : ℚ) - 1 := by
        exact_mod_cast hp_hi _ (by omega)
      have hpabs : |(p (s₀ + j + m * T) : ℚ)| ≤ 2 * ((s₀ + j + m * T : ℕ) : ℚ) := by
        rw [abs_of_nonneg (by linarith)]; linarith
      have hps : |pstar (s₀ + j + m * T)| ≤ |α j| * ((s₀ + j + m * T : ℕ) : ℚ) + |β j| := by
        dsimp only [pstar]
        calc
          |α j * ((s₀ + j + m * T : ℕ) : ℚ) + β j|
              ≤ |α j * ((s₀ + j + m * T : ℕ) : ℚ)| + |β j| := abs_add_le _ _
          _ = |α j| * ((s₀ + j + m * T : ℕ) : ℚ) + |β j| := by
              have hnn : (0 : ℚ) ≤ ((s₀ + j + m * T : ℕ) : ℚ) := Nat.cast_nonneg _
              rw [abs_mul, abs_of_nonneg hnn]
      have htri : |δ m| ≤ |(p (s₀ + j + m * T) : ℚ)| + |pstar (s₀ + j + m * T)| := abs_sub _ _
      have hcast : ((s₀ + j + m * T : ℕ) : ℚ) = ((s₀ + j : ℕ) : ℚ) + (T : ℚ) * (m : ℚ) := by
        push_cast; ring
      rw [hcast] at hpabs hps
      linarith
    have hδk : δ k = 0 := abs_eq_zero.mp (by rw [hδ_abs k, hδ0, abs_zero, mul_zero])
    dsimp only [δ, pstar] at hδk
    linarith
  have hα_per : ∀ j, α (j + T) = α j := by
    intro j
    have h0 := hp_exact (j + T) 0
    have h1 := hp_exact (j + T) 1
    have h0' := hp_exact j 1
    have h1' := hp_exact j 2
    have e0 : s₀ + (j + T) + 0 * T = s₀ + j + 1 * T := by ring
    have e1 : s₀ + (j + T) + 1 * T = s₀ + j + 2 * T := by ring
    rw [e0] at h0; rw [e1] at h1
    push_cast at h0 h1 h0' h1'
    have hT_ne : (T : ℚ) ≠ 0 := by positivity
    apply mul_right_cancel₀ hT_ne
    linarith
  have hα_mul_per : ∀ i m, α (i + m * T) = α i := by
    intro i m
    induction m with
    | zero => simp
    | succ m ihm =>
      have : i + (m + 1) * T = (i + m * T) + T := by ring
      rw [this, hα_per, ihm]
  have hα_bounds : ∀ j, 0 ≤ α j ∧ α j ≤ 2 ∧
      (w j = true → α j ≤ 1) ∧ (w j = false → 1 ≤ α j) := by
    intro j
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply slope_ge_of_forall (α j) (β j) 0 (s₀ + j) T hT
      intro k
      have h1 : (1 : ℚ) ≤ (p (s₀ + j + k * T) : ℚ) := by exact_mod_cast hp_lo _ (by omega)
      have h2 := hp_exact j k
      have hcast : ((s₀ + j + k * T : ℕ) : ℚ) = ((s₀ + j : ℕ) : ℚ) + (k : ℚ) * (T : ℚ) := by
        push_cast; ring
      rw [hcast] at h2
      linarith
    · apply slope_le_of_forall (α j) (β j) 2 (s₀ + j) T hT
      intro k
      have h1 : (p (s₀ + j + k * T) : ℚ) ≤ 2 * ((s₀ + j + k * T : ℕ) : ℚ) - 1 := by
        exact_mod_cast hp_hi _ (by omega)
      have h2 := hp_exact j k
      have hcast : ((s₀ + j + k * T : ℕ) : ℚ) = ((s₀ + j : ℕ) : ℚ) + (k : ℚ) * (T : ℚ) := by
        push_cast; ring
      rw [hcast] at h1 h2
      linarith
    · intro hw
      apply slope_le_of_forall (α j) (β j) 1 (s₀ + j) T hT
      intro k
      have hwk : w (j + k * T) = true := by rw [w_add_mul_period w T hper]; exact hw
      have hlt : p (s₀ + j + k * T) < ((s₀ + j + k * T : ℕ) : ℤ) := by
        have := decide_eq_true_iff.mp hwk
        simpa [Nat.add_assoc] using this
      have h1 : (p (s₀ + j + k * T) : ℚ) ≤ ((s₀ + j + k * T : ℕ) : ℚ) := by
        exact_mod_cast le_of_lt hlt
      have h2 := hp_exact j k
      have hcast : ((s₀ + j + k * T : ℕ) : ℚ) = ((s₀ + j : ℕ) : ℚ) + (k : ℚ) * (T : ℚ) := by
        push_cast; ring
      rw [hcast] at h1 h2
      linarith
    · intro hw
      apply slope_ge_of_forall (α j) (β j) 1 (s₀ + j) T hT
      intro k
      have hwk : w (j + k * T) = false := by rw [w_add_mul_period w T hper]; exact hw
      have hge : ((s₀ + j + k * T : ℕ) : ℤ) ≤ p (s₀ + j + k * T) := by
        have := decide_eq_false_iff_not.mp hwk
        have hlt : ¬ p (s₀ + j + k * T) < ((s₀ + j + k * T : ℕ) : ℤ) := by
          simpa [Nat.add_assoc] using this
        omega
      have h1 : ((s₀ + j + k * T : ℕ) : ℚ) ≤ (p (s₀ + j + k * T) : ℚ) := by exact_mod_cast hge
      have h2 := hp_exact j k
      have hcast : ((s₀ + j + k * T : ℕ) : ℚ) = ((s₀ + j : ℕ) : ℚ) + (k : ℚ) * (T : ℚ) := by
        push_cast; ring
      rw [hcast] at h1 h2
      linarith
  have hα_tent : ∀ j, α (j + 1) = tentQ (α j) := by
    intro j
    have heq_step : ∀ k : ℕ,
        (p (s₀ + (j + 1) + k * T) : ℚ) =
          if w j then 2 * (((s₀ + j + k * T : ℕ) : ℚ) - (p (s₀ + j + k * T) : ℚ))
          else 2 * ((p (s₀ + j + k * T) : ℚ) - ((s₀ + j + k * T : ℕ) : ℚ)) - 1 := by
      intro k
      have hwk : w (j + k * T) = w j := w_add_mul_period w T hper k j
      have hs := hstep_w (j + k * T)
      have heq1 : s₀ + (j + k * T) + 1 = s₀ + (j + 1) + k * T := by ring
      have heq2 : s₀ + (j + k * T) = s₀ + j + k * T := by ring
      rw [heq1, heq2, hwk] at hs
      dsimp only [branchStep] at hs
      cases hwb : w j
      · simp only [hwb, Bool.false_eq_true, ↓reduceIte] at hs ⊢; exact_mod_cast hs
      · simp only [hwb, ↓reduceIte] at hs ⊢; exact_mod_cast hs
    have h0 := heq_step 0
    have h1 := heq_step 1
    have hp0 := hp_exact j 0
    have hp1 := hp_exact j 1
    have hq0 := hp_exact (j + 1) 0
    have hq1 := hp_exact (j + 1) 1
    push_cast at h0 h1 hp0 hp1 hq0 hq1
    have hT_ne : (T : ℚ) ≠ 0 := by positivity
    have hlin : α (j + 1) = if w j then 2 * (1 - α j) else 2 * (α j - 1) := by
      cases hwb : w j
      · simp only [hwb, Bool.false_eq_true, ↓reduceIte] at h0 h1 ⊢
        apply mul_right_cancel₀ hT_ne; linarith
      · simp only [hwb, ↓reduceIte] at h0 h1 ⊢
        apply mul_right_cancel₀ hT_ne; linarith
    rw [hlin]
    cases hwb : w j
    · simp [tentQ_of_ge ((hα_bounds j).2.2.2 hwb)]
    · simp [tentQ_of_le ((hα_bounds j).2.2.1 hwb)]
  have hall_two_false : ∀ j₀ : ℕ, (∀ m : ℕ, α (j₀ + m) = 2) → False := by
    intro j₀ hconst
    have hall2 : ∀ i : ℕ, α i = 2 := by
      intro i
      have hle : j₀ ≤ i + j₀ * T := by
        have : j₀ ≤ j₀ * T := Nat.le_mul_of_pos_right j₀ hT
        omega
      let m := i + j₀ * T - j₀
      have hm : i + j₀ * T = j₀ + m := by omega
      rw [← hα_mul_per i j₀, hm, hconst m]
    have hall_false : ∀ i, w i = false := by
      intro i
      cases hwi : w i with
      | false => rfl
      | true =>
        have hle1 := (hα_bounds i).2.2.1 hwi
        rw [hall2 i] at hle1
        norm_num at hle1
    exact all_two_R_branch_absurd p s₀ T hT hp_hi w hstep_w α β hp_exact hall2 hall_false
  have hconst_from_two : ∀ j₀, α j₀ = 2 → ∀ m : ℕ, α (j₀ + m) = 2 := by
    intro j₀ hj₀ m
    induction m with
    | zero => simpa using hj₀
    | succ m ihm =>
      have : j₀ + (m + 1) = j₀ + m + 1 := by ring
      rw [this, hα_tent, ihm]; norm_num [tentQ]
  have hα_interior : ∀ j, 0 < α j ∧ α j < 2 ∧ α j ≠ 1 := by
    intro j
    have hb := hα_bounds j
    refine ⟨?_, ?_, ?_⟩
    · by_contra hle
      have hj0 : α j = 0 := le_antisymm (by linarith) hb.1
      have hj1 : α (j + 1) = 2 := by rw [hα_tent, hj0]; norm_num [tentQ]
      exact hall_two_false (j + 1) (hconst_from_two (j + 1) hj1)
    · by_contra hge
      have hj2 : α j = 2 := le_antisymm hb.2.1 (by linarith)
      exact hall_two_false j (hconst_from_two j hj2)
    · intro hj1
      have hj2 : α (j + 1) = 0 := by rw [hα_tent, hj1]; norm_num [tentQ]
      have hj3 : α (j + 2) = 2 := by rw [hα_tent, hj2]; norm_num [tentQ]
      exact hall_two_false (j + 2) (hconst_from_two (j + 2) hj3)
  have hw_eq_dec : ∀ j, w j = decide (α j < 1) := by
    intro j
    cases hwb : w j with
    | true =>
      have hle := (hα_bounds j).2.2.1 hwb
      have hne := (hα_interior j).2.2
      simp [lt_of_le_of_ne hle hne]
    | false =>
      have hge := (hα_bounds j).2.2.2 hwb
      have hnot : ¬ α j < 1 := by linarith
      simp [hnot]
  have hα_iter : ∀ n : ℕ, α n = tentQ^[n] (α 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ihn => rw [Function.iterate_succ_apply', ← ihn, hα_tent]
  have hα_inj : Function.Injective (fun j : Fin T => α j.1) := by
    have hcontra : ∀ a b : Fin T, a.1 < b.1 → α a.1 = α b.1 → False := by
      intro a b hlt hab
      let T' : ℕ := b.1 - a.1
      have hT'1 : 1 ≤ T' := by omega
      have hT'lt : T' < T := by omega
      have hiter_add : ∀ x y, tentQ^[x + y] (α 0) = tentQ^[y] (tentQ^[x] (α 0)) := by
        intro x y; rw [Nat.add_comm x y, Function.iterate_add_apply]
      have hper_tail : ∀ m : ℕ, α (a.1 + m + T') = α (a.1 + m) := by
        intro m
        have h1 : a.1 + m + T' = b.1 + m := by omega
        have hL := hα_iter (b.1 + m)
        have hR := hα_iter (a.1 + m)
        rw [h1, hL, hR, hiter_add b.1 m, hiter_add a.1 m]
        have hab' : tentQ^[a.1] (α 0) = tentQ^[b.1] (α 0) := by
          rw [← hα_iter, ← hα_iter]; exact hab
        rw [hab']
      have hper_α_all : ∀ n : ℕ, α (n + T') = α n := by
        intro n
        have hle : a.1 ≤ n + a.1 * T := by
          have : a.1 ≤ a.1 * T := Nat.le_mul_of_pos_right a.1 hT
          omega
        let m := n + a.1 * T - a.1
        have hm1 : n + a.1 * T = a.1 + m := by omega
        have hm2 : (n + T') + a.1 * T = a.1 + m + T' := by omega
        rw [← hα_mul_per (n + T') a.1, ← hα_mul_per n a.1, hm2, hm1, hper_tail m]
      have hper_w_all : ∀ n : ℕ, w (n + T') = w n := by
        intro n
        rw [hw_eq_dec, hw_eq_dec, hper_α_all n]
      obtain ⟨n₀, hn₀⟩ := hT_min T' hT'1 hT'lt
      exact hn₀ (hper_w_all n₀)
    intro i j hij
    rcases Nat.lt_trichotomy i.1 j.1 with hlt | heq | hgt
    · exact (hcontra i j hlt hij).elim
    · exact Fin.ext heq
    · exact (hcontra j i hgt hij.symm).elim
  let r₀ : ℚ := α 0
  let d : ℕ := r₀.den
  have hd_gt1 : 1 < d := by
    by_contra hle
    have hd_nz : 0 < d := Nat.pos_of_ne_zero r₀.den_nz
    have hd1 : d = 1 := by omega
    have hr_int : r₀ = (r₀.num : ℚ) := by
      have := Rat.num_div_den r₀
      rw [show (r₀.den : ℚ) = 1 from by exact_mod_cast hd1, div_one] at this
      exact this.symm
    have h0 := (hα_interior 0).1
    have h2 := (hα_interior 0).2.1
    have hne1 : r₀ ≠ 1 := (hα_interior 0).2.2
    have hnum_gt : (0 : ℤ) < r₀.num := Rat.num_pos.mpr h0
    have hnum_lt : r₀.num < 2 := by
      have : (r₀.num : ℚ) < 2 := by rw [← hr_int]; exact h2
      exact_mod_cast this
    have hnum1 : r₀.num = 1 := by omega
    apply hne1
    rw [hr_int, hnum1]
    norm_num
  have hrel0 : (1 - E 0) * r₀.num = A 0 * (d : ℤ) := by
    have hD : (1 : ℚ) - (E 0 : ℚ) ≠ 0 := hE_ne1 0
    have hα0 : r₀ * (1 - (E 0 : ℚ)) = (A 0 : ℚ) := by
      dsimp only [r₀, α]
      exact div_mul_cancel₀ _ hD
    have hden : r₀ = (r₀.num : ℚ) / (d : ℚ) := (Rat.num_div_den r₀).symm
    have hd0 : (d : ℚ) ≠ 0 := by positivity
    have hq : ((1 - E 0 : ℤ) : ℚ) * (r₀.num : ℚ) = (A 0 : ℚ) * (d : ℚ) := by
      rw [hden] at hα0
      field_simp at hα0
      push_cast
      linarith
    exact_mod_cast hq
  have hd_dvd_1mE : d ∣ (1 - E 0).natAbs := by
    have hd_dvd : (d : ℤ) ∣ (1 - E 0) * r₀.num := ⟨A 0, by linarith⟩
    have hnat : d ∣ (1 - E 0).natAbs * r₀.num.natAbs := by
      rw [← Int.natAbs_mul]
      exact Int.natCast_dvd.mp hd_dvd
    have hcop : Nat.Coprime d r₀.num.natAbs := r₀.reduced.symm
    exact hcop.dvd_of_dvd_mul_right hnat
  have hd_odd : Odd d := by
    have h2E : Even (E 0) := by
      have habs := hE_abs 0
      obtain ⟨T1, hT1⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
      rcases abs_eq (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ T) |>.mp habs with h | h
      · rw [h, hT1, pow_succ']; exact ⟨(2 : ℤ) ^ T1, by ring⟩
      · rw [h, hT1, pow_succ']; exact ⟨-((2 : ℤ) ^ T1), by ring⟩
    have h1mE_odd : Odd (1 - E 0) := by
      rcases h2E with ⟨m, hm⟩
      refine ⟨-m, by omega⟩
    refine Nat.not_even_iff_odd.mp fun heven => ?_
    rcases heven with ⟨q, hq⟩
    have h2_dvd : 2 ∣ (1 - E 0).natAbs := dvd_trans ⟨q, by omega⟩ hd_dvd_1mE
    have h2_dvdz : (2 : ℤ) ∣ (1 - E 0) := Int.ofNat_dvd_left.mpr h2_dvd
    rcases h2_dvdz with ⟨k, hk⟩
    rcases h1mE_odd with ⟨m, hm⟩
    omega
  have hα_interior_iter : ∀ n : ℕ, 0 < tentQ^[n] r₀ ∧ tentQ^[n] r₀ < 2 ∧ tentQ^[n] r₀ ≠ 1 := by
    intro n; rw [← hα_iter n]; exact hα_interior n
  have hT_le_tot : T ≤ Nat.totient d := by
    let S : Finset ℕ := (Finset.Ico 1 d).filter (fun b => Nat.Coprime b d)
    have hS_card : S.card = Nat.totient d := by
      rw [Nat.totient_eq_card_coprime]
      congr 1
      ext b
      simp only [S, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
      constructor
      · rintro ⟨⟨_, hb⟩, h⟩; exact ⟨hb, h.symm⟩
      · rintro ⟨hb, h⟩
        refine ⟨⟨?_, hb⟩, h.symm⟩
        by_contra hb0
        have hz : b = 0 := by omega
        rw [hz, Nat.coprime_zero_right] at h
        omega
    let f : ℕ → ℚ := fun b => (2 * (b : ℚ)) / (d : ℚ)
    let imgJ : Finset ℚ := Finset.univ.image (fun j : Fin T => α j.1)
    have himg_sub : imgJ ⊆ S.image f := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨j, _, rfl⟩
      have hper_j : α j.1 = α (j.1 + T) := (hα_per j.1).symm
      rw [hper_j, hα_iter]
      obtain ⟨b, hb1, hb2, hbcop, hbeq⟩ :=
        tentQ_iter_mem hd_gt1 hd_odd (hα_interior 0).1 (hα_interior 0).2.1 (hα_interior 0).2.2
          rfl hα_interior_iter (j.1 + T) (by omega)
      exact Finset.mem_image.mpr
        ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hb1, hb2⟩, hbcop⟩, hbeq.symm⟩
    calc
      T = (Finset.univ : Finset (Fin T)).card := (Finset.card_fin T).symm
      _ = imgJ.card := (Finset.card_image_of_injective _ hα_inj).symm
      _ ≤ (S.image f).card := Finset.card_le_card himg_sub
      _ ≤ S.card := Finset.card_image_le
      _ = Nat.totient d := hS_card
  have hd_dvd_T : d ∣ T := by
    have hp0 := hp_exact 0 0
    have hpT := hp_exact 0 1
    have hdiff : ((p (s₀ + T) - p s₀ : ℤ) : ℚ) = r₀ * (T : ℚ) := by
      rw [Int.cast_sub]
      simp only [add_zero, zero_mul, one_mul] at hp0 hpT
      push_cast at hp0 hpT
      dsimp only [r₀]
      rw [hp0, hpT]
      ring
    have hden : r₀ = (r₀.num : ℚ) / (d : ℚ) := (Rat.num_div_den r₀).symm
    have hd0 : (d : ℚ) ≠ 0 := by positivity
    have hq : (d : ℚ) * ((p (s₀ + T) - p s₀ : ℤ) : ℚ) = (r₀.num : ℚ) * (T : ℚ) := by
      rw [hden] at hdiff
      field_simp at hdiff ⊢
      linarith
    have hint : (d : ℤ) * (p (s₀ + T) - p s₀) = r₀.num * (T : ℤ) := by exact_mod_cast hq
    have hd_dvd_z : (d : ℤ) ∣ r₀.num * (T : ℤ) := ⟨p (s₀ + T) - p s₀, hint.symm⟩
    have hnat : d ∣ r₀.num.natAbs * T := by
      have h1 : d ∣ (r₀.num * (T : ℤ)).natAbs := Int.natCast_dvd.mp hd_dvd_z
      simpa [Int.natAbs_mul] using h1
    have hcop : Nat.Coprime r₀.num.natAbs d := r₀.reduced
    exact hcop.symm.dvd_of_dvd_mul_left hnat
  have hd_le_T : d ≤ T := Nat.le_of_dvd hT hd_dvd_T
  have htot_lt : Nat.totient d < d := Nat.totient_lt d hd_gt1
  omega

end NoPeriodicBranches

section UniversalBackwardLifting

/-- Affine coefficients `(A, B)` accumulated along a backward word `u : List Bool`
starting at step index `j` from `(n, n)`: `m_j(n) = (A * n + B) / 2^j`.
Here `false` corresponds to the even backward step `m ↦ m / 2` and `true` to the odd
backward step `m ↦ 2 * (n - j) - (m + 5) / 2`. -/
def backCoeffAux : ℕ → ℕ → ℤ → List Bool → ℕ × ℤ
  | _, A, B, [] => (A, B)
  | j, A, B, false :: rest => backCoeffAux (j + 1) A B rest
  | j, A, B, true :: rest =>
    backCoeffAux (j + 1) (2 ^ (j + 2) - A) (-B - (4 * (j : ℤ) + 5) * (2 : ℤ) ^ j) rest

/-- Backward word coefficient pair `(A(u), B(u))` starting from `(1, 0)` at `j = 0`. -/
def backCoeff (u : List Bool) : ℕ × ℤ :=
  backCoeffAux 0 1 0 u

private lemma backCoeffAux_invariant (j A : ℕ) (B : ℤ) (u : List Bool)
    (hodd : Odd A) (hpos : 0 < A) (hlt : A < 2 ^ (j + 1)) :
    let A' := (backCoeffAux j A B u).1
    Odd A' ∧ 0 < A' ∧ A' < 2 ^ (j + u.length + 1) := by
  induction u generalizing j A B with
  | nil => simpa [backCoeffAux] using ⟨hodd, hpos, hlt⟩
  | cons c rest ih =>
    cases c with
    | false =>
      simp only [backCoeffAux, List.length_cons]
      have hlt2 : A < 2 ^ (j + 1 + 1) := by
        have : 2 ^ (j + 1) < 2 ^ (j + 1 + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
        omega
      have hres := ih (j + 1) A B hodd hpos hlt2
      have heq : j + 1 + rest.length + 1 = j + (rest.length + 1) + 1 := by ring
      simpa [heq] using hres
    | true =>
      simp only [backCoeffAux, List.length_cons]
      have h2j2 : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      have hA'_pos : 0 < 2 ^ (j + 2) - A := by omega
      have hA'_lt : 2 ^ (j + 2) - A < 2 ^ (j + 1 + 1) := by omega
      have h2_even : Even (2 ^ (j + 2)) := by rw [h2j2]; exact even_two_mul _
      have hA'_odd : Odd (2 ^ (j + 2) - A) := by
        rcases h2_even with ⟨k, hk⟩
        rcases hodd with ⟨m, hm⟩
        refine ⟨k - m - 1, by omega⟩
      have hres := ih (j + 1) (2 ^ (j + 2) - A)
        (-B - (4 * (j : ℤ) + 5) * (2 : ℤ) ^ j) hA'_odd hA'_pos hA'_lt
      have heq : j + 1 + rest.length + 1 = j + (rest.length + 1) + 1 := by ring
      simpa [heq] using hres

theorem backCoeff_odd_bounds (u : List Bool) :
    Odd (backCoeff u).1 ∧ 0 < (backCoeff u).1 ∧ (backCoeff u).1 < 2 ^ (u.length + 1) := by
  simpa [backCoeff] using backCoeffAux_invariant 0 1 0 u odd_one (by norm_num) (by norm_num)

private lemma backCoeffAux_last_true (j A : ℕ) (B : ℤ) (u : List Bool)
    (hodd : Odd A) (hpos : 0 < A) (hlt : A < 2 ^ (j + 1))
    (hlast : u.getLast? = some true) :
    2 ^ (j + u.length) < (backCoeffAux j A B u).1 := by
  induction u generalizing j A B with
  | nil => simp at hlast
  | cons c rest ih =>
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp only [backCoeffAux, List.length_singleton]
      have h2 : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      omega
    | cons c2 rest2 =>
      have hlast' : (c2 :: rest2).getLast? = some true := by
        simpa [List.getLast?_cons_cons] using hlast
      cases c with
      | false =>
        simp only [backCoeffAux, List.length_cons]
        have hlt2 : A < 2 ^ (j + 1 + 1) := by
          have : 2 ^ (j + 1) < 2 ^ (j + 1 + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
          omega
        have hres := ih (j + 1) A B hodd hpos hlt2 hlast'
        have heq : j + 1 + (rest2.length + 1) = j + (rest2.length + 1 + 1) := by ring
        simpa [heq] using hres
      | true =>
        simp only [backCoeffAux, List.length_cons]
        have h2j2 : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
        have hA'_pos : 0 < 2 ^ (j + 2) - A := by omega
        have hA'_lt : 2 ^ (j + 2) - A < 2 ^ (j + 1 + 1) := by omega
        have h2_even : Even (2 ^ (j + 2)) := by rw [h2j2]; exact even_two_mul _
        have hA'_odd : Odd (2 ^ (j + 2) - A) := by
          rcases h2_even with ⟨k, hk⟩
          rcases hodd with ⟨m, hm⟩
          refine ⟨k - m - 1, by omega⟩
        have hres := ih (j + 1) (2 ^ (j + 2) - A)
          (-B - (4 * (j : ℤ) + 5) * (2 : ℤ) ^ j) hA'_odd hA'_pos hA'_lt hlast'
        have heq : j + 1 + (rest2.length + 1) = j + (rest2.length + 1 + 1) := by ring
        simpa [heq] using hres

theorem backCoeff_last_true_gt (u : List Bool) (hlast : u.getLast? = some true) :
    2 ^ u.length < (backCoeff u).1 := by
  simpa [backCoeff] using backCoeffAux_last_true 0 1 0 u odd_one (by norm_num) (by norm_num) hlast

private lemma backCoeffAux_append_zeros (j A : ℕ) (B : ℤ) (u : List Bool) (k : ℕ) :
    backCoeffAux j A B (u ++ List.replicate k false) = backCoeffAux j A B u := by
  induction u generalizing j A B with
  | nil =>
    simp only [List.nil_append]
    induction k generalizing j with
    | zero => rfl
    | succ k ihk => simp only [List.replicate_succ, backCoeffAux, ihk]
  | cons c rest ih =>
    cases c <;> simp only [List.cons_append, backCoeffAux, ih]

theorem backCoeff_append_zeros (u : List Bool) (k : ℕ) :
    backCoeff (u ++ List.replicate k false) = backCoeff u :=
  backCoeffAux_append_zeros 0 1 0 u k

private lemma backCoeffAux_snoc (j A : ℕ) (B : ℤ) (u : List Bool) (c : Bool) :
    backCoeffAux j A B (u ++ [c]) =
      let (A', B') := backCoeffAux j A B u
      let j' := j + u.length
      if c then (2 ^ (j' + 2) - A', -B' - (4 * (j' : ℤ) + 5) * (2 : ℤ) ^ j')
      else (A', B') := by
  induction u generalizing j A B with
  | nil => cases c <;> simp [backCoeffAux]
  | cons c0 rest ih =>
    cases c0 <;>
    · simp only [List.cons_append, backCoeffAux, List.length_cons, ih]
      have : j + (rest.length + 1) = j + 1 + rest.length := by ring
      simp [this]

private lemma list_take_succ_eq_append (w : List Bool) (j : ℕ) (hj : j < w.length) :
    w.take (j + 1) = w.take j ++ [w[j]] := by
  induction w generalizing j with
  | nil => simp at hj
  | cons a rest ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.length_cons] at hj
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
      exact congrArg (a :: ·) (ih j (by omega))

private lemma backCoeff_take_succ (w : List Bool) (j : ℕ) (hj : j < w.length) :
    backCoeff (w.take (j + 1)) =
      let (A', B') := backCoeff (w.take j)
      if w[j] then (2 ^ (j + 2) - A', -B' - (4 * (j : ℤ) + 5) * (2 : ℤ) ^ j)
      else (A', B') := by
  have htake : w.take (j + 1) = w.take j ++ [w[j]] := list_take_succ_eq_append w j hj
  have hlen : (w.take j).length = j := List.length_take_of_le (le_of_lt hj)
  rw [htake, backCoeff, backCoeffAux_snoc, hlen]
  simp [backCoeff]

/-- Forward active iteration starting at `(n₀, m₀)` for `i` steps. -/
def iterActiveF (n₀ m₀ : ℤ) : ℕ → ℤ
  | 0 => m₀
  | i + 1 => activeF (n₀ + (i : ℤ)) (iterActiveF n₀ m₀ i)

private lemma iterActiveF_add (n₀ m₀ : ℤ) (a b : ℕ) :
    iterActiveF n₀ m₀ (a + b) = iterActiveF (n₀ + (a : ℤ)) (iterActiveF n₀ m₀ a) b := by
  induction b with
  | zero => simp [iterActiveF]
  | succ b ih =>
    have h1 : a + (b + 1) = a + b + 1 := by ring
    rw [h1, iterActiveF, iterActiveF, ih]
    have h2 : n₀ + (a : ℤ) + (b : ℤ) = n₀ + ((a + b : ℕ) : ℤ) := by push_cast; ring
    rw [h2]

private lemma iterActiveF_double_run (n₀ m₀ : ℤ) (hm0 : 4 ≤ m₀) (M : ℕ)
    (hbound : ∀ i : ℕ, i < M → m₀ * (2 : ℤ) ^ i < n₀ + (i : ℤ)) :
    ∀ i : ℕ, i ≤ M →
      iterActiveF n₀ m₀ i = m₀ * (2 : ℤ) ^ i ∧
        (∀ l < i, 4 ≤ iterActiveF n₀ m₀ l ∧ iterActiveF n₀ m₀ l < n₀ + (l : ℤ)) := by
  intro i hi
  induction i with
  | zero => simp [iterActiveF]
  | succ i ih =>
    obtain ⟨ih_eq, ih_bnd⟩ := ih (by omega)
    have hlt : m₀ * (2 : ℤ) ^ i < n₀ + (i : ℤ) := hbound i (by omega)
    have heq : iterActiveF n₀ m₀ (i + 1) = m₀ * (2 : ℤ) ^ (i + 1) := by
      rw [iterActiveF, ih_eq, activeF, if_pos hlt]
      ring
    refine ⟨heq, fun l hl => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
    · exact ih_bnd l hl'
    · rw [ih_eq]
      have hpow : (1 : ℤ) ≤ (2 : ℤ) ^ l := one_le_pow₀ (by norm_num)
      exact ⟨by nlinarith, hlt⟩

/-- Existence of a valid lifting period `d ≥ 1` with `(A / gcd m₀ A) ∣ (2^d - 1)`
whenever `Odd A` (`d = φ(A / gcd m₀ A)` works). -/
theorem exists_lifting_period (m₀ A : ℕ) (_hm₀ : 1 ≤ m₀) (hodd : Odd A) :
    ∃ d : ℕ, 1 ≤ d ∧ (A / Nat.gcd m₀ A) ∣ (2 ^ d - 1) := by
  let g := Nat.gcd m₀ A
  let q := A / g
  have hg_dvd : g ∣ A := Nat.gcd_dvd_right m₀ A
  have hq_odd : Odd q := by
    have hmul : g * q = A := Nat.mul_div_cancel' hg_dvd
    have : Odd (g * q) := by rw [hmul]; exact hodd
    exact (Nat.odd_mul.mp this).2
  have hq_pos : 0 < q := by rcases hq_odd with ⟨k, hk⟩; omega
  let d := Nat.totient q
  have hd_pos : 1 ≤ d := Nat.totient_pos.mpr hq_pos
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hq_odd
  have hmod : 2 ^ d ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop
  have hdvd : q ∣ 2 ^ d - 1 := by
    have hle : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
    exact (Nat.modEq_iff_dvd' hle).mp hmod.symm
  exact ⟨d, hd_pos, hdvd⟩

private lemma lifting_doubling_step_bound (A L M : ℕ) (n₀ m₀ nt n : ℤ)
    (hA_pos : 0 < A) (hA_ltL : A < 2 ^ (L + 1))
    (hm₀ : m₀ = 4 ∨ m₀ = 5 ∨ m₀ = 6)
    (hn₀_lo : 4 ≤ n₀) (hn₀_56 : (m₀ = 5 ∨ m₀ = 6) → 5 ≤ n₀)
    (hnt_diff : (A : ℤ) * (nt - n) = m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1))
    (h_n0 : n₀ = n - (L : ℤ)) :
    ∀ i : ℕ, i < M → m₀ * (2 : ℤ) ^ i < (nt - ((L + M : ℕ) : ℤ)) + (i : ℤ) := by
  intro i hi
  let l : ℕ := M - i
  have hl1 : 1 ≤ l := by omega
  have hlM : l ≤ M := Nat.sub_le M i
  have hm₀_ge4 : 4 ≤ m₀ := by rcases hm₀ with rfl | rfl | rfl <;> omega
  have hA_z : (0 : ℤ) < (A : ℤ) := by exact_mod_cast hA_pos
  have hA_ub : (A : ℤ) + 1 ≤ 2 * (2 : ℤ) ^ L := by
    have h1 : (A : ℤ) < (2 : ℤ) ^ (L + 1) := by exact_mod_cast hA_ltL
    have h2 : (2 : ℤ) ^ (L + 1) = 2 * (2 : ℤ) ^ L := by ring
    omega
  have hid : (A : ℤ) * ((nt - ((L + M : ℕ) : ℤ)) + (i : ℤ) - m₀ * (2 : ℤ) ^ i) =
      (A : ℤ) * (n₀ - (l : ℤ)) +
        (m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1) - (A : ℤ) * m₀ * (2 : ℤ) ^ i) := by
    have hcast : ((L + M : ℕ) : ℤ) - (i : ℤ) = (L : ℤ) + (l : ℤ) := by
      have : L + M = L + i + l := by omega
      push_cast [this]; ring
    have h1 : (nt - ((L + M : ℕ) : ℤ)) + (i : ℤ) = (n₀ - (l : ℤ)) + (nt - n) := by
      rw [h_n0]; linarith [hcast]
    rw [h1, mul_sub, mul_add]
    linarith [hnt_diff]
  have hpos_prod : 0 < (A : ℤ) * ((nt - ((L + M : ℕ) : ℤ)) + (i : ℤ) - m₀ * (2 : ℤ) ^ i) := by
    rw [hid]
    have h2M_ge1 : (1 : ℤ) ≤ (2 : ℤ) ^ M := one_le_pow₀ (by norm_num)
    have hbase : 2 * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1) ≥ ((A : ℤ) + 1) * ((2 : ℤ) ^ M - 1) :=
      mul_le_mul_of_nonneg_right hA_ub (by linarith)
    have hbase_m₀ : m₀ * (2 * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1)) ≥
        m₀ * (((A : ℤ) + 1) * ((2 : ℤ) ^ M - 1)) :=
      mul_le_mul_of_nonneg_left hbase (by omega)
    rcases Nat.eq_or_lt_of_le hl1 with hl_eq1 | hl_ge2
    · have hiM : i + 1 = M := by omega
      have h2M : (2 : ℤ) ^ M = 2 * (2 : ℤ) ^ i := by rw [← hiM]; ring
      have hmain : 2 * (m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1) - (A : ℤ) * m₀ * (2 : ℤ) ^ i) ≥
          m₀ * ((2 : ℤ) ^ M - 1 - (A : ℤ)) := by
        calc
          2 * (m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1) - (A : ℤ) * m₀ * (2 : ℤ) ^ i)
              = m₀ * (2 * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1)) - (A : ℤ) * m₀ * (2 * (2 : ℤ) ^ i) := by ring
          _ ≥ m₀ * (((A : ℤ) + 1) * ((2 : ℤ) ^ M - 1)) - (A : ℤ) * m₀ * (2 : ℤ) ^ M := by
              rw [← h2M]; linarith [hbase_m₀]
          _ = m₀ * ((2 : ℤ) ^ M - 1 - (A : ℤ)) := by ring
      have hn0_1 : (A : ℤ) * (2 * (n₀ - (l : ℤ)) - m₀) ≥ 0 := by
        have hdiff : 2 * (n₀ - (l : ℤ)) - m₀ ≥ 0 := by
          rw [← hl_eq1]
          rcases hm₀ with rfl | rfl | rfl
          · omega
          · have := hn₀_56 (Or.inl rfl); omega
          · have := hn₀_56 (Or.inr rfl); omega
        exact mul_nonneg (by omega) hdiff
      have hm₀_pos : 0 < m₀ * ((2 : ℤ) ^ M - 1) := by
        have : 1 ≤ (2 : ℤ) ^ M - 1 := by
          have : (2 : ℤ) ≤ (2 : ℤ) ^ M := by
            simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : 1 ≤ M)
          omega
        nlinarith
      linarith
    · have h2i_le : 2 * (2 : ℤ) ^ i ≤ (2 : ℤ) ^ (M - 1) := by
        have : 2 * (2 : ℤ) ^ i = (2 : ℤ) ^ (i + 1) := by ring
        rw [this]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h2M : (2 : ℤ) ^ M = 2 * (2 : ℤ) ^ (M - 1) := by
        obtain ⟨M1, hM1⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
        rw [hM1]; simp [pow_succ']
      have hmul_i : (A : ℤ) * m₀ * (2 * (2 : ℤ) ^ i) ≤ (A : ℤ) * m₀ * (2 : ℤ) ^ (M - 1) :=
        mul_le_mul_of_nonneg_left h2i_le (by positivity)
      have hmain : 2 * (m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1) - (A : ℤ) * m₀ * (2 : ℤ) ^ i) ≥
          (A : ℤ) * (m₀ * ((2 : ℤ) ^ (M - 1) - 1)) + m₀ * ((2 : ℤ) ^ M - 1) := by
        have hstep1 : m₀ * (2 * (2 : ℤ) ^ L * ((2 : ℤ) ^ M - 1)) - (A : ℤ) * m₀ * (2 * (2 : ℤ) ^ i) ≥
            m₀ * (((A : ℤ) + 1) * ((2 : ℤ) ^ M - 1)) - (A : ℤ) * m₀ * (2 : ℤ) ^ (M - 1) := by
          linarith [hbase_m₀, hmul_i]
        have heq_rhs : m₀ * (((A : ℤ) + 1) * ((2 : ℤ) ^ M - 1)) - (A : ℤ) * m₀ * (2 : ℤ) ^ (M - 1) =
            (A : ℤ) * (m₀ * ((2 : ℤ) ^ (M - 1) - 1)) + m₀ * ((2 : ℤ) ^ M - 1) := by
          rw [h2M]; ring
        linarith
      have hpow_lin : (l : ℤ) ≤ (2 : ℤ) ^ M - 2 := by
        have hgen : ∀ m : ℕ, 2 ≤ m → (m : ℤ) ≤ (2 : ℤ) ^ m - 2 := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base => norm_num
          | succ r hr ihr =>
            have h2r : (2 : ℤ) ^ (r + 1) = 2 * (2 : ℤ) ^ r := by ring
            omega
        have hlm : (l : ℤ) ≤ (M : ℤ) := by exact_mod_cast hlM
        have hM2 : (M : ℤ) ≤ (2 : ℤ) ^ M - 2 := hgen M (by omega)
        omega
      have h4pow : 2 * (l : ℤ) ≤ m₀ * ((2 : ℤ) ^ (M - 1) - 1) := by
        have hpos_m1 : 0 ≤ (2 : ℤ) ^ (M - 1) - 1 := by
          have : (1 : ℤ) ≤ (2 : ℤ) ^ (M - 1) := one_le_pow₀ (by norm_num)
          omega
        have h4le : 4 * ((2 : ℤ) ^ (M - 1) - 1) ≤ m₀ * ((2 : ℤ) ^ (M - 1) - 1) :=
          mul_le_mul_of_nonneg_right hm₀_ge4 hpos_m1
        linarith
      have h8 : 8 ≤ 2 * (n₀ - (l : ℤ)) + m₀ * ((2 : ℤ) ^ (M - 1) - 1) := by linarith
      have hA_term : 8 * (A : ℤ) ≤ (A : ℤ) * (2 * (n₀ - (l : ℤ)) + m₀ * ((2 : ℤ) ^ (M - 1) - 1)) := by
        nlinarith
      have hm_nonneg : 0 ≤ m₀ * ((2 : ℤ) ^ M - 1) := by positivity
      linarith
  exact sub_pos.mp (pos_of_mul_pos_right hpos_prod (by positivity))

private lemma lifting_prefix_div (w : List Bool) (L : ℕ) (hw_len : w.length = L)
    (nt m₀ : ℤ) (M : ℕ)
    (hL_eq : ((backCoeff w).1 : ℤ) * nt + (backCoeff w).2 = m₀ * (2 : ℤ) ^ (L + M)) :
    ∀ step : ℕ, step ≤ L →
      (2 : ℤ) ^ (L - step) ∣
        ((backCoeff (w.take (L - step))).1 : ℤ) * nt + (backCoeff (w.take (L - step))).2 := by
  intro step
  induction step with
  | zero =>
    intro _
    have htakeL : w.take L = w := List.take_of_length_le (by rw [hw_len])
    simp only [Nat.sub_zero, htakeL, hL_eq]
    refine ⟨m₀ * (2 : ℤ) ^ M, by rw [pow_add]; ring⟩
  | succ step ih =>
    intro hle
    have ih' := ih (by omega)
    have hidx'_eq : L - step = (L - (step + 1)) + 1 := by omega
    have hidx_lt : L - (step + 1) < w.length := by rw [hw_len]; omega
    have htake := backCoeff_take_succ w (L - (step + 1)) hidx_lt
    rw [← hidx'_eq] at htake
    cases hc : w[L - (step + 1)]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at htake
      have hAeq : (backCoeff (w.take (L - step))).1 = (backCoeff (w.take (L - (step + 1)))).1 := by
        rw [htake]
      have hBeq : (backCoeff (w.take (L - step))).2 = (backCoeff (w.take (L - (step + 1)))).2 := by
        rw [htake]
      rw [← hAeq, ← hBeq]
      have hpow : (2 : ℤ) ^ (L - (step + 1)) ∣ (2 : ℤ) ^ (L - step) := by
        rw [hidx'_eq, pow_succ]; exact dvd_mul_right _ _
      exact dvd_trans hpow ih'
    · simp only [hc, ↓reduceIte] at htake
      have hAeq : (backCoeff (w.take (L - step))).1 =
          2 ^ ((L - (step + 1)) + 2) - (backCoeff (w.take (L - (step + 1)))).1 := by rw [htake]
      have hBeq : (backCoeff (w.take (L - step))).2 =
          -(backCoeff (w.take (L - (step + 1)))).2 -
            (4 * ((L - (step + 1) : ℕ) : ℤ) + 5) * (2 : ℤ) ^ (L - (step + 1)) := by rw [htake]
      have hAi_lt : (backCoeff (w.take (L - (step + 1)))).1 < 2 ^ ((L - (step + 1)) + 1) := by
        have hp := backCoeff_odd_bounds (w.take (L - (step + 1)))
        have hln : (w.take (L - (step + 1))).length = L - (step + 1) :=
          List.length_take_of_le (by rw [hw_len]; omega)
        rw [hln] at hp; exact hp.2.2
      have hAi_cast : ((2 ^ ((L - (step + 1)) + 2) - (backCoeff (w.take (L - (step + 1)))).1 : ℕ) : ℤ) =
          (2 : ℤ) ^ ((L - (step + 1)) + 2) - ((backCoeff (w.take (L - (step + 1)))).1 : ℤ) := by
        have hle2 : (backCoeff (w.take (L - (step + 1)))).1 ≤ 2 ^ ((L - (step + 1)) + 2) := by
          have : 2 ^ ((L - (step + 1)) + 1) ≤ 2 ^ ((L - (step + 1)) + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          omega
        exact_mod_cast Int.ofNat_sub hle2
      rw [hAeq, hBeq, hAi_cast, hidx'_eq] at ih'
      rcases ih' with ⟨q, hq⟩
      have hp1 : (2 : ℤ) ^ ((L - (step + 1)) + 1) = 2 * (2 : ℤ) ^ (L - (step + 1)) := by ring
      have hp2 : (2 : ℤ) ^ ((L - (step + 1)) + 2) = 4 * (2 : ℤ) ^ (L - (step + 1)) := by ring
      rw [hp1, hp2] at hq
      refine ⟨4 * (nt - ((L - (step + 1) : ℕ) : ℤ) - 1) - 1 - 2 * q, ?_⟩
      linarith

/-- Theorem 4 (Universal Backward Lifting Theorem):
Given any backward path `w = u ++ 0^k` of length `L = r + k` reaching an entry point
`(n₀, m₀)` (`n₀ = n - L`, `n = s + 3`, `m₀ ∈ {4, 5, 6}`) from `(n, n)` with valid active
intermediate steps, let `(A, B) = backCoeff u`, `g = gcd(m₀, A)`, and `d ≥ 1` satisfy
`(A / g) ∣ (2^d - 1)`. Then for every `t : ℕ`:
1. `A ∣ m₀ * 2^(L + t * d) - B`, so `s_t := (m₀ * 2^(L + t * d) - B) / A - 3` is an integer `≥ s`;
2. Starting from `(n_t - (L + t * d), m₀)` (corresponding to initial integer
   `x_t = 3 * (s_t - s) + x - 3 * t * d`), all `L + t * d` forward active steps remain strictly
   inside the active zone `[4, 2*n' - 4] \ {n'}` and reach `(n_t, n_t)` (expelling `x_t` at `s_t`). -/
theorem universal_backward_lifting (u : List Bool) (k : ℕ) (s m₀ : ℤ)
    (_hs : 1 ≤ s) (hm₀ : m₀ = 4 ∨ m₀ = 5 ∨ m₀ = 6)
    (d : ℕ) (_hd : 1 ≤ d)
    (hdvd : ((backCoeff u).1 / Nat.gcd m₀.toNat (backCoeff u).1) ∣ (2 ^ d - 1))
    (hn₀_lo : 4 ≤ (s + 3) - ((u.length + k : ℕ) : ℤ))
    (hn₀_56 : (m₀ = 5 ∨ m₀ = 6) → 5 ≤ (s + 3) - ((u.length + k : ℕ) : ℤ))
    (hback_end : ((backCoeff u).1 : ℤ) * (s + 3) + (backCoeff u).2 =
      m₀ * (2 : ℤ) ^ (u.length + k))
    (hback_valid : ∀ j : ℕ, j ≤ u.length + k →
      let w := u ++ List.replicate k false
      let (Aj, Bj) := backCoeff (w.take j)
      ((2 : ℤ) ^ j ∣ (Aj : ℤ) * (s + 3) + Bj) ∧
        let mj := ((Aj : ℤ) * (s + 3) + Bj) / (2 : ℤ) ^ j
        mj ≤ 2 * ((s + 3) - (j : ℤ)) - 4 ∧
          (j < u.length + k → 7 ≤ mj) ∧
          (1 ≤ j →
            match w[j - 1]? with
            | some false => mj < (s + 3) - (j : ℤ)
            | some true => (s + 3) - (j : ℤ) < mj
            | none => True)) :
    ∀ t : ℕ,
      let A := (backCoeff u).1
      let B := (backCoeff u).2
      let L := u.length + k
      let n := s + 3
      let x := 3 * (n - (L : ℤ)) - 7 - m₀
      ((A : ℤ) ∣ m₀ * (2 : ℤ) ^ (L + t * d) - B) ∧
        let nt := (m₀ * (2 : ℤ) ^ (L + t * d) - B) / (A : ℤ)
        let st := nt - 3
        let n₀t := nt - ((L + t * d : ℕ) : ℤ)
        let xt := 3 * n₀t - 7 - m₀
        s ≤ st ∧ xt = 3 * (st - s) + x - 3 * ((t * d : ℕ) : ℤ) ∧
          iterActiveF n₀t m₀ (L + t * d) = nt ∧
          (∀ i < L + t * d,
            4 ≤ iterActiveF n₀t m₀ i ∧
              iterActiveF n₀t m₀ i ≤ 2 * (n₀t + (i : ℤ)) - 4 ∧
              iterActiveF n₀t m₀ i ≠ n₀t + (i : ℤ)) := by
  intro t
  set A := (backCoeff u).1
  set B := (backCoeff u).2
  set L := u.length + k
  set n := s + 3
  set w := u ++ List.replicate k false
  have hw_len : w.length = L := by simp [w, L]
  have hA_props := backCoeff_odd_bounds u
  have hA_pos : 0 < A := hA_props.2.1
  have hA_lt : A < 2 ^ (u.length + 1) := hA_props.2.2
  have hA_ltL : A < 2 ^ (L + 1) := by
    have hpow : 2 ^ (u.length + 1) ≤ 2 ^ (L + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  have hm₀_ge4 : 4 ≤ m₀ := by rcases hm₀ with rfl | rfl | rfl <;> omega
  have hdvd_td : (A / Nat.gcd m₀.toNat A) ∣ (2 ^ (t * d) - 1) := by
    let q := A / Nat.gcd m₀.toNat A
    have h1 : 2 ^ d ≡ 1 [MOD q] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow d 2 (by norm_num))).mpr hdvd).symm
    have ht : (2 ^ d) ^ t ≡ 1 ^ t [MOD q] := h1.pow t
    rw [← pow_mul, mul_comm d t, one_pow] at ht
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow (t * d) 2 (by norm_num))).mp ht.symm
  have hA_dvd_diff : (A : ℤ) ∣ m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ (t * d) - 1) := by
    let g := Nat.gcd m₀.toNat A
    let q := A / g
    rcases Nat.gcd_dvd_left m₀.toNat A with ⟨q₁, hq₁⟩
    have hg2 : g ∣ A := Nat.gcd_dvd_right m₀.toNat A
    rcases hdvd_td with ⟨q₂, hq₂⟩
    have hAg : A = g * q := (Nat.mul_div_cancel' hg2).symm
    have hm_eq : m₀ = (g : ℤ) * (q₁ : ℤ) := by
      have hm₀_nn : (m₀.toNat : ℤ) = m₀ := Int.toNat_of_nonneg (by omega)
      rw [← hm₀_nn, hq₁]; push_cast; ring
    have h2_eq : (2 : ℤ) ^ (t * d) - 1 = (q : ℤ) * (q₂ : ℤ) := by
      have hle : 1 ≤ 2 ^ (t * d) := Nat.one_le_pow _ _ (by norm_num)
      have hz : ((2 ^ (t * d) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (t * d) - 1 := by
        exact_mod_cast Int.ofNat_sub hle
      rw [← hz, hq₂, Nat.cast_mul]
    refine ⟨(q₁ : ℤ) * (q₂ : ℤ) * (2 : ℤ) ^ L, ?_⟩
    have hAgz : (A : ℤ) = (g : ℤ) * (q : ℤ) := by exact_mod_cast hAg
    rw [hm_eq, h2_eq, hAgz]
    ring
  have hA_dvd_target : (A : ℤ) ∣ m₀ * (2 : ℤ) ^ (L + t * d) - B := by
    have hbe : (A : ℤ) * n + B = m₀ * (2 : ℤ) ^ L := hback_end
    have heq : m₀ * (2 : ℤ) ^ (L + t * d) - B =
        (A : ℤ) * n + m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ (t * d) - 1) := by
      rw [pow_add, ← mul_assoc, ← hbe]; ring
    rw [heq]
    exact dvd_add (dvd_mul_right _ _) hA_dvd_diff
  refine ⟨hA_dvd_target, ?_⟩
  let nt := (m₀ * (2 : ℤ) ^ (L + t * d) - B) / (A : ℤ)
  let st := nt - 3
  let n₀t := nt - ((L + t * d : ℕ) : ℤ)
  let xt := 3 * n₀t - 7 - m₀
  have hnt_rel : (A : ℤ) * nt + B = m₀ * (2 : ℤ) ^ (L + t * d) := by
    have hmul := Int.mul_ediv_cancel' hA_dvd_target
    linarith
  have hnt_diff : (A : ℤ) * (nt - n) = m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ (t * d) - 1) := by
    have hbe : (A : ℤ) * n + B = m₀ * (2 : ℤ) ^ L := hback_end
    have hpow : (2 : ℤ) ^ (L + t * d) = (2 : ℤ) ^ L * (2 : ℤ) ^ (t * d) := pow_add 2 L (t * d)
    rw [hpow] at hnt_rel
    linarith
  have hnt_ge_n : n ≤ nt := by
    have hpow : (1 : ℤ) ≤ (2 : ℤ) ^ (t * d) := one_le_pow₀ (by norm_num)
    have hprod : 0 ≤ m₀ * (2 : ℤ) ^ L * ((2 : ℤ) ^ (t * d) - 1) := by positivity
    have hA_z : (0 : ℤ) < (A : ℤ) := by exact_mod_cast hA_pos
    nlinarith
  have hst_ge : s ≤ st := by dsimp [st, n] at *; omega
  have hxt_eq : xt = 3 * (st - s) + (3 * (n - (L : ℤ)) - 7 - m₀) - 3 * ((t * d : ℕ) : ℤ) := by
    dsimp [xt, n₀t, st, n]; rw [Nat.cast_add]; ring
  refine ⟨hst_ge, hxt_eq, ?_⟩
  let M : ℕ := t * d
  have hM_bound : ∀ i : ℕ, i < M → m₀ * (2 : ℤ) ^ i < n₀t + (i : ℤ) :=
    lifting_doubling_step_bound A L M (n - (L : ℤ)) m₀ nt n hA_pos hA_ltL hm₀ hn₀_lo hn₀_56
      hnt_diff rfl
  obtain ⟨hM_eq, hM_bnd⟩ := iterActiveF_double_run n₀t m₀ hm₀_ge4 M hM_bound M (le_refl M)
  have hbw : backCoeff w = (A, B) := backCoeff_append_zeros u k
  have hL_eq : ((backCoeff w).1 : ℤ) * nt + (backCoeff w).2 = m₀ * (2 : ℤ) ^ (L + M) := by
    rw [hbw]; exact hnt_rel
  have hdvd_all := lifting_prefix_div w L hw_len nt m₀ M hL_eq
  have hprefix_inv : ∀ j : ℕ, j ≤ L →
      let Aj := (backCoeff (w.take j)).1
      let Bj := (backCoeff (w.take j)).2
      ((2 : ℤ) ^ j ∣ (Aj : ℤ) * nt + Bj) ∧
        let mj := ((Aj : ℤ) * nt + Bj) / (2 : ℤ) ^ j
        mj ≤ 2 * (nt - (j : ℤ)) - 4 ∧
          (j < L → 7 ≤ mj) ∧
          (1 ≤ j →
            match w[j - 1]? with
            | some false => mj < nt - (j : ℤ)
            | some true => nt - (j : ℤ) < mj
            | none => True) := by
    intro j hj
    have hdvd_nt : (2 : ℤ) ^ j ∣ ((backCoeff (w.take j)).1 : ℤ) * nt + (backCoeff (w.take j)).2 := by
      have h1 := hdvd_all (L - j) (Nat.sub_le L j)
      have h2 : L - (L - j) = j := Nat.sub_sub_self hj
      simpa [h2] using h1
    refine ⟨hdvd_nt, ?_⟩
    obtain ⟨hdvd_n, hhi_n, hlo_n, hdir_n⟩ := hback_valid j hj
    have hAj_props := backCoeff_odd_bounds (w.take j)
    have hAj_len : (w.take j).length = j := List.length_take_of_le (by rw [hw_len]; exact hj)
    have hAj_lt : (backCoeff (w.take j)).1 < 2 ^ (j + 1) := by
      have h := hAj_props.2.2
      rw [hAj_len] at h
      exact h
    rcases hdvd_n with ⟨mn, hmn⟩
    rcases hdvd_nt with ⟨mt, hmt⟩
    have hmn' : ((backCoeff (w.take j)).1 : ℤ) * (s + 3) + (backCoeff (w.take j)).2 =
        (2 : ℤ) ^ j * mn := hmn
    have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ j := by positivity
    have hmn_div : (((backCoeff (w.take j)).1 : ℤ) * (s + 3) + (backCoeff (w.take j)).2) /
        (2 : ℤ) ^ j = mn := by
      rw [hmn', mul_comm, Int.mul_ediv_cancel _ (ne_of_gt hpow_pos)]
    have hmn_div_aux : (((backCoeffAux 0 1 0 (w.take j)).1 : ℤ) * n +
        (backCoeffAux 0 1 0 (w.take j)).2) / (2 : ℤ) ^ j = mn := hmn_div
    have hmt_div : (((backCoeff (w.take j)).1 : ℤ) * nt + (backCoeff (w.take j)).2) / (2 : ℤ) ^ j = mt := by
      rw [hmt, mul_comm, Int.mul_ediv_cancel _ (ne_of_gt hpow_pos)]
    rw [hmn_div_aux] at hhi_n hlo_n hdir_n
    rw [hmt_div]
    have hdiff_m : (2 : ℤ) ^ j * (mt - mn) = ((backCoeff (w.take j)).1 : ℤ) * (nt - n) := by linarith
    have hAj_zpos : (0 : ℤ) < ((backCoeff (w.take j)).1 : ℤ) := by exact_mod_cast hAj_props.2.1
    have hmt_ge_mn : mn ≤ mt := by nlinarith
    have hhi_t : mt ≤ 2 * (nt - (j : ℤ)) - 4 := by
      have hAj_ub : ((backCoeff (w.take j)).1 : ℤ) ≤ 2 * (2 : ℤ) ^ j - 1 := by
        have : ((backCoeff (w.take j)).1 : ℤ) < (2 : ℤ) ^ (j + 1) := by exact_mod_cast hAj_lt
        have : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by ring
        omega
      nlinarith
    refine ⟨hhi_t, fun hjL => by linarith [hlo_n hjL], fun hj1 => ?_⟩
    have hj_lt : j - 1 < w.length := by rw [hw_len]; omega
    rw [List.getElem?_eq_getElem hj_lt] at hdir_n ⊢
    cases hwb : w[j - 1]
    · simp only [hwb] at hdir_n ⊢
      have htake := backCoeff_take_succ w (j - 1) hj_lt
      have hjm : j - 1 + 1 = j := by omega
      rw [hjm, hwb] at htake
      simp only [Bool.false_eq_true, ↓reduceIte] at htake
      have hAeq : (backCoeff (w.take j)).1 = (backCoeff (w.take (j - 1))).1 := by rw [htake]
      have hp := backCoeff_odd_bounds (w.take (j - 1))
      have hln : (w.take (j - 1)).length = j - 1 := List.length_take_of_le (by rw [hw_len]; omega)
      rw [hln] at hp
      have hAj_zlt : ((backCoeff (w.take j)).1 : ℤ) < (2 : ℤ) ^ j := by
        have : (backCoeff (w.take j)).1 < 2 ^ j := by rw [hAeq, ← hjm]; exact hp.2.2
        exact_mod_cast this
      have hmul : ((backCoeff (w.take j)).1 : ℤ) * (nt - n) ≤ (2 : ℤ) ^ j * (nt - n) :=
        mul_le_mul_of_nonneg_right (le_of_lt hAj_zlt) (by linarith [hnt_ge_n])
      have hmn_lt := hdir_n hj1
      nlinarith
    · simp only [hwb] at hdir_n ⊢
      have htake := backCoeff_take_succ w (j - 1) hj_lt
      have hjm : j - 1 + 1 = j := by omega
      rw [hjm, hwb] at htake
      simp only [↓reduceIte] at htake
      have hAeq : (backCoeff (w.take j)).1 = 2 ^ (j - 1 + 2) - (backCoeff (w.take (j - 1))).1 := by
        rw [htake]
      have hp := backCoeff_odd_bounds (w.take (j - 1))
      have hln : (w.take (j - 1)).length = j - 1 := List.length_take_of_le (by rw [hw_len]; omega)
      rw [hln] at hp
      have hp2 : (backCoeff (w.take (j - 1))).1 < 2 ^ j := by rw [← hjm]; exact hp.2.2
      have h2j2 : 2 ^ (j - 1 + 2) = 2 * 2 ^ j := by
        rw [show j - 1 + 2 = j + 1 by omega, pow_succ']
      have hAj_zgt : (2 : ℤ) ^ j < ((backCoeff (w.take j)).1 : ℤ) := by
        have : 2 ^ j < (backCoeff (w.take j)).1 := by omega
        exact_mod_cast this
      have hmul : (2 : ℤ) ^ j * (nt - n) ≤ ((backCoeff (w.take j)).1 : ℤ) * (nt - n) :=
        mul_le_mul_of_nonneg_right (le_of_lt hAj_zgt) (by linarith [hnt_ge_n])
      have hmn_gt := hdir_n hj1
      nlinarith
  have hL_run : ∀ l : ℕ, l ≤ L →
      iterActiveF (nt - (L : ℤ)) (m₀ * (2 : ℤ) ^ M) l =
        (((backCoeff (w.take (L - l))).1 : ℤ) * nt + (backCoeff (w.take (L - l))).2) /
          (2 : ℤ) ^ (L - l) := by
    intro l hl
    induction l with
    | zero =>
      have htakeL : w.take L = w := List.take_of_length_le (by rw [hw_len])
      simp only [Nat.sub_zero, iterActiveF, htakeL, hbw, hnt_rel]
      have hpow : (2 : ℤ) ^ (L + M) = (2 : ℤ) ^ L * (2 : ℤ) ^ M := pow_add 2 L M
      have h2L : (2 : ℤ) ^ L ≠ 0 := by positivity
      rw [hpow, show m₀ * ((2 : ℤ) ^ L * (2 : ℤ) ^ M) = (m₀ * (2 : ℤ) ^ M) * (2 : ℤ) ^ L by ring]
      exact (Int.mul_ediv_cancel _ h2L).symm
    | succ l ih =>
      have ih' := ih (by omega)
      have hj'_eq : L - l = (L - (l + 1)) + 1 := by omega
      have hj_lt : L - (l + 1) < w.length := by rw [hw_len]; omega
      obtain ⟨hdvd_j', _, _, hdir_j'⟩ := hprefix_inv (L - l) (by omega)
      have htake := backCoeff_take_succ w (L - (l + 1)) hj_lt
      rw [← hj'_eq] at htake
      have hdir := hdir_j' (by omega : 1 ≤ L - l)
      have hj'_m1 : L - l - 1 = L - (l + 1) := by omega
      rw [hj'_m1, List.getElem?_eq_getElem hj_lt] at hdir
      rw [iterActiveF, ih']
      have hstage : nt - (L : ℤ) + (l : ℤ) = nt - ((L - l : ℕ) : ℤ) := by
        have hjl : (L - l) + l = L := by omega
        have hLcast : (L : ℤ) = ((L - l : ℕ) : ℤ) + (l : ℤ) := by exact_mod_cast hjl.symm
        rw [hLcast]; ring
      rw [hstage]
      rcases hdvd_j' with ⟨mj', hmj'⟩
      have h2j'_pos : (2 : ℤ) ^ (L - l) ≠ 0 := by positivity
      have hm_val : (((backCoeff (w.take (L - l))).1 : ℤ) * nt + (backCoeff (w.take (L - l))).2) /
          (2 : ℤ) ^ (L - l) = mj' := by
        rw [hmj', mul_comm]; exact Int.mul_ediv_cancel _ h2j'_pos
      rw [hm_val] at hdir ⊢
      cases hc : w[L - (l + 1)]
      · simp only [hc] at hdir
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at htake
        have hAeq : (backCoeff (w.take (L - l))).1 = (backCoeff (w.take (L - (l + 1)))).1 := by
          rw [htake]
        have hBeq : (backCoeff (w.take (L - l))).2 = (backCoeff (w.take (L - (l + 1)))).2 := by
          rw [htake]
        rw [← hAeq, ← hBeq, activeF, if_pos hdir]
        have h2j_pos : (2 : ℤ) ^ (L - (l + 1)) ≠ 0 := by positivity
        rw [hmj', hj'_eq, pow_succ]
        rw [show (2 : ℤ) ^ (L - (l + 1)) * 2 * mj' = (2 * mj') * (2 : ℤ) ^ (L - (l + 1)) by ring]
        rw [Int.mul_ediv_cancel _ h2j_pos]
      · simp only [hc] at hdir
        simp only [hc, ↓reduceIte] at htake
        have hnot : ¬ mj' < nt - ((L - l : ℕ) : ℤ) := by omega
        rw [activeF, if_neg hnot]
        have hAj_lt : (backCoeff (w.take (L - (l + 1)))).1 < 2 ^ ((L - (l + 1)) + 1) := by
          have hp := backCoeff_odd_bounds (w.take (L - (l + 1)))
          have hln : (w.take (L - (l + 1))).length = L - (l + 1) :=
            List.length_take_of_le (by rw [hw_len]; omega)
          rw [hln] at hp; exact hp.2.2
        have hAeq : (backCoeff (w.take (L - l))).1 =
            2 ^ ((L - (l + 1)) + 2) - (backCoeff (w.take (L - (l + 1)))).1 := by rw [htake]
        have hBeq : (backCoeff (w.take (L - l))).2 =
            -(backCoeff (w.take (L - (l + 1)))).2 -
              (4 * ((L - (l + 1) : ℕ) : ℤ) + 5) * (2 : ℤ) ^ (L - (l + 1)) := by rw [htake]
        have hAj_cast : ((2 ^ ((L - (l + 1)) + 2) - (backCoeff (w.take (L - (l + 1)))).1 : ℕ) : ℤ) =
            (2 : ℤ) ^ ((L - (l + 1)) + 2) - ((backCoeff (w.take (L - (l + 1)))).1 : ℤ) := by
          have : (backCoeff (w.take (L - (l + 1)))).1 ≤ 2 ^ ((L - (l + 1)) + 2) := by
            have : 2 ^ ((L - (l + 1)) + 1) ≤ 2 ^ ((L - (l + 1)) + 2) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            omega
          exact_mod_cast Int.ofNat_sub this
        rw [hAeq, hBeq, hAj_cast] at hmj'
        have h2j_pos : (2 : ℤ) ^ (L - (l + 1)) ≠ 0 := by positivity
        have hsub : ((backCoeff (w.take (L - (l + 1)))).1 : ℤ) * nt +
              (backCoeff (w.take (L - (l + 1)))).2 =
            (4 * (nt - ((L - l : ℕ) : ℤ)) - 1 - 2 * mj') * (2 : ℤ) ^ (L - (l + 1)) := by
          have hp1 : (2 : ℤ) ^ (L - l) = 2 * (2 : ℤ) ^ (L - (l + 1)) := by rw [hj'_eq, pow_succ']
          have hp2 : (2 : ℤ) ^ ((L - (l + 1)) + 2) = 4 * (2 : ℤ) ^ (L - (l + 1)) := by ring
          have hjc : ((L - l : ℕ) : ℤ) = ((L - (l + 1) : ℕ) : ℤ) + 1 := by exact_mod_cast hj'_eq
          rw [hp1, hp2] at hmj'
          rw [hjc]
          have hlin : (4 * (nt - (((L - (l + 1) : ℕ) : ℤ) + 1)) - 1 - 2 * mj') *
              (2 : ℤ) ^ (L - (l + 1)) =
              (4 * (2 : ℤ) ^ (L - (l + 1)) * nt -
                (4 * ((L - (l + 1) : ℕ) : ℤ) + 5) * (2 : ℤ) ^ (L - (l + 1))) -
                2 * (2 : ℤ) ^ (L - (l + 1)) * mj' := by ring
          rw [hlin]
          linarith [hmj']
        rw [hsub, Int.mul_ediv_cancel _ h2j_pos]
  have hstage_M : n₀t + (M : ℤ) = nt - (L : ℤ) := by
    dsimp [n₀t, M]; rw [Nat.cast_add]; ring
  refine ⟨?_, ?_⟩
  · rw [add_comm L M, iterActiveF_add]
    have hst_M' : (m₀ * (2 : ℤ) ^ (M + L) - B) / (A : ℤ) - ((M + L : ℕ) : ℤ) + (M : ℤ) =
        nt - (L : ℤ) := by
      have : M + L = L + M := add_comm M L
      dsimp only [nt]; rw [this]; push_cast; ring
    have hm₀_arg : iterActiveF ((m₀ * (2 : ℤ) ^ (M + L) - B) / (A : ℤ) - ((M + L : ℕ) : ℤ)) m₀ M =
        m₀ * (2 : ℤ) ^ M := by
      have : M + L = L + M := add_comm M L
      simpa [this, n₀t, M] using hM_eq
    rw [hst_M', hm₀_arg]
    have hL := hL_run L (le_refl L)
    simp only [Nat.sub_self, List.take_zero, backCoeff, backCoeffAux, Nat.cast_one, one_mul,
      add_zero, pow_zero, Int.ediv_one] at hL
    exact hL.trans (by dsimp only [nt, M]; rw [add_comm L (t * d)])
  · intro i hi
    rcases lt_or_ge i M with hiM | hiM
    · obtain ⟨h4, hlt⟩ := hM_bnd i hiM
      have hne : iterActiveF n₀t m₀ i ≠ n₀t + (i : ℤ) := ne_of_lt hlt
      exact ⟨h4, by linarith, hne⟩
    · let l := i - M
      have hl_lt : l < L := by omega
      have hi_eq : M + l = i := Nat.add_sub_of_le hiM
      rw [← hi_eq, iterActiveF_add, hstage_M, hM_eq, hL_run l (le_of_lt hl_lt)]
      have hj1 : 1 ≤ L - l := by omega
      obtain ⟨_, hhi, hlo7, hdir⟩ := hprefix_inv (L - l) (by omega)
      have hstage_j : n₀t + ((M + l : ℕ) : ℤ) = nt - ((L - l : ℕ) : ℤ) := by
        have hjl : (L - l) + l = L := by omega
        have hLcast : (L : ℤ) = ((L - l : ℕ) : ℤ) + (l : ℤ) := by exact_mod_cast hjl.symm
        dsimp only [n₀t, M]
        have hcastML : ((L + M : ℕ) : ℤ) = (L : ℤ) + (M : ℤ) := by push_cast; ring
        have hcastMl : ((M + l : ℕ) : ℤ) = (M : ℤ) + (l : ℤ) := by push_cast; ring
        rw [hcastML, hcastMl, hLcast]; ring
      rw [hstage_j]
      have h4 : 4 ≤ (((backCoeff (w.take (L - l))).1 : ℤ) * nt + (backCoeff (w.take (L - l))).2) /
          (2 : ℤ) ^ (L - l) := by
        by_cases hjL : L - l = L
        · have htakeL : w.take L = w := List.take_of_length_le (by rw [hw_len])
          rw [hjL, htakeL, hbw, hnt_rel, pow_add]
          have h2L : (2 : ℤ) ^ L ≠ 0 := by positivity
          rw [show m₀ * ((2 : ℤ) ^ L * (2 : ℤ) ^ M) = (m₀ * (2 : ℤ) ^ M) * (2 : ℤ) ^ L by ring]
          rw [Int.mul_ediv_cancel _ h2L]
          have hpow : (1 : ℤ) ≤ (2 : ℤ) ^ M := one_le_pow₀ (by norm_num)
          nlinarith
        · have := hlo7 (by omega); omega
      have hne : (((backCoeff (w.take (L - l))).1 : ℤ) * nt + (backCoeff (w.take (L - l))).2) /
          (2 : ℤ) ^ (L - l) ≠ nt - ((L - l : ℕ) : ℤ) := by
        have hd := hdir hj1
        have hj_lt : (L - l) - 1 < w.length := by rw [hw_len]; omega
        rw [List.getElem?_eq_getElem hj_lt] at hd
        cases hc : w[(L - l) - 1] <;> simp only [hc] at hd <;> omega
      exact ⟨h4, hhi, hne⟩

end UniversalBackwardLifting

end PPL134
