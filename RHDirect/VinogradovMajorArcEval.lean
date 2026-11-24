import RHDirect.VinogradovMajorArc
import RHDirect.VinogradovSingularSeriesBound
import RHDirect.Stage10SiegelWalfiszFull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Vinogradov — Unconditional Major-Arc Asymptotic Evaluation

This module proves the unconditional major-arc lower bound for Vinogradov's three-primes
circle integral:
for every `B ≥ 1`, there exists `N₀ ≥ 16` such that for all odd `n ≥ N₀` and
`Q = (Real.log n) ^ B`:
`(1 / 4) * (2 * (2 - π² / 6)) * n² ≤ (∫ α in majorArcs n Q, (S n α)³ * e (-n α)).re`.

## Architecture
1. **Major-Arc Definitions, Measurability, Disjointness & Periodicity Decomposition:**
   Defines `majorArc` and `majorArcs`, proves pairwise disjointness for `2 * Q^3 < N`,
   and reduces `∫_{majorArcs N Q} F` for any continuous 1-periodic `F` to the exact
   sum of symmetric integrals `∑_{1 ≤ q ≤ ⌊Q⌋₊} ∑_{a < q, (a,q)=1} ∫_{-Q/N}^{Q/N} F(a/q + β) dβ`.
2. **Uniform Single-Arc Approximation via Unconditional Full Siegel–Walfisz:**
   Applies `Stage10SiegelWalfiszFull.siegel_walfisz_theta` to `VinogradovMajorArc.S_single_arc_approx`
   to bound `‖S N (a/q + β) - (μ(q)/φ(q)) * v N β‖ ≤ N / (log N)^D` uniformly for any `D ≥ 0`.
3. **Exact Singular Integral & Geometric Tail Bound:**
   Evaluates `∫_{-1/2}^{1/2} (v n β)^3 e(-n β) dβ = (n + 1)(n + 2) / 2` exactly by
   integer orthogonality, and proves `‖v N β‖ ≤ 1 / (2 |β|)` on `0 < |β| ≤ 1/2` to bound
   the tail `|∫_{-Q/N}^{Q/N} - ∫_{-1/2}^{1/2}| ≤ N^2 / (8 Q^2)`.
4. **Truncated Singular Series Lower & Upper Bounds:**
   Proves the Möbius divisor formula, reality, and multiplicativity of `ramanujanSum q n`,
   the elementary totient bound `q^3 ≤ 16 * φ(q)^4`, telescoping `1 / (q √q)` tail decay,
   and combines with `VinogradovSingularSeriesBound.singularPartialProd_lower_bound` to get
   `2*(2 - π²/6) - 8/√M ≤ ∑_{q=1}^M (μ(q)/φ(q))^3 c_q(n)` and `|∑| ≤ 12`.
5. **Major-Arc Master Lower Bound (`major_arc_integral_lower_bound`).**

Pure targeted Mathlib; zero `sorry`, zero custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral Filter Topology

namespace RHDirect.Vinogradov

noncomputable section

/-! ## Section 1: Major-Arc Definitions, Measurability, Disjointness & Decomposition -/

/-- A single major arc centered at `a / q` of half-width `Q / N`. -/
def majorArc (N : ℕ) (Q : ℝ) (q a : ℕ) : Set ℝ :=
  {α : ℝ | |α - (a : ℝ) / (q : ℝ)| ≤ Q / (N : ℝ)}

/-- The union of major arcs inside `[0, 1]` with modulus `1 ≤ q ≤ ⌊Q⌋₊` and `0 ≤ a ≤ q, (a,q)=1`. -/
def majorArcs (N : ℕ) (Q : ℝ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩
    ⋃ q ∈ Finset.Icc 1 ⌊Q⌋₊,
      ⋃ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
        majorArc N Q q a

lemma majorArc_eq_Icc (N : ℕ) (Q : ℝ) (q a : ℕ) :
    majorArc N Q q a = Set.Icc ((a : ℝ) / (q : ℝ) - Q / (N : ℝ)) ((a : ℝ) / (q : ℝ) + Q / (N : ℝ)) := by
  ext α
  simp only [majorArc, Set.mem_Icc, abs_le]
  constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma measurableSet_majorArc (N : ℕ) (Q : ℝ) (q a : ℕ) :
    MeasurableSet (majorArc N Q q a) := by
  rw [majorArc_eq_Icc]
  exact measurableSet_Icc

theorem measurableSet_majorArcs (N : ℕ) (Q : ℝ) :
    MeasurableSet (majorArcs N Q) := by
  refine measurableSet_Icc.inter ?_
  refine Finset.measurableSet_biUnion _ fun q _ => ?_
  exact Finset.measurableSet_biUnion _ fun a _ => measurableSet_majorArc N Q q a

lemma majorArcs_subset_Icc (N : ℕ) (Q : ℝ) : majorArcs N Q ⊆ Set.Icc (0 : ℝ) 1 :=
  Set.inter_subset_left

/-- Distinct reduced pairs `(q₁, a₁) ≠ (q₂, a₂)` have distinct rationals `a₁ / q₁ ≠ a₂ / q₂`. -/
private lemma div_ne_of_coprime_ne {q₁ a₁ q₂ a₂ : ℕ}
    (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (hc₁ : Nat.Coprime a₁ q₁) (hc₂ : Nat.Coprime a₂ q₂)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    (a₁ : ℝ) / (q₁ : ℝ) ≠ (a₂ : ℝ) / (q₂ : ℝ) := by
  intro heq
  have hq₁0 : (q₁ : ℝ) ≠ 0 := by positivity
  have hq₂0 : (q₂ : ℝ) ≠ 0 := by positivity
  have hmulR : (a₁ : ℝ) * (q₂ : ℝ) = (a₂ : ℝ) * (q₁ : ℝ) := by
    have := (div_eq_div_iff hq₁0 hq₂0).mp heq
    exact this
  have hmul : a₁ * q₂ = a₂ * q₁ := by exact_mod_cast hmulR
  have hdvd1 : q₁ ∣ q₂ := by
    have h1 : q₁ ∣ a₁ * q₂ := ⟨a₂, by linarith⟩
    exact hc₁.symm.dvd_of_dvd_mul_left h1
  have hdvd2 : q₂ ∣ q₁ := by
    have h2 : q₂ ∣ a₂ * q₁ := ⟨a₁, by linarith⟩
    exact hc₂.symm.dvd_of_dvd_mul_left h2
  have hqeq : q₁ = q₂ := Nat.dvd_antisymm hdvd1 hdvd2
  subst hqeq
  have haeq : a₁ = a₂ := Nat.eq_of_mul_eq_mul_right (by omega : 0 < q₁) hmul
  exact hne (Prod.ext rfl haeq)

/-- Minimum separation `1 / (q₁ * q₂)` between distinct rationals `a₁/q₁` and `a₂/q₂`. -/
private lemma abs_sub_div_ge {q₁ a₁ q₂ a₂ : ℕ}
    (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (hc₁ : Nat.Coprime a₁ q₁) (hc₂ : Nat.Coprime a₂ q₂)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |(a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)| := by
  have hq₁pos : (0 : ℝ) < (q₁ : ℝ) := by positivity
  have hq₂pos : (0 : ℝ) < (q₂ : ℝ) := by positivity
  have hne_div := div_ne_of_coprime_ne hq₁ hq₂ hc₁ hc₂ hne
  have hsub : (a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ) =
      (((a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) : ℤ) : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    push_cast
    field_simp [hq₁pos.ne', hq₂pos.ne']
  rw [hsub, abs_div, abs_of_pos (mul_pos hq₁pos hq₂pos)]
  have hnum_ne : (a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) ≠ 0 := by
    intro h0
    apply hne_div
    rw [div_eq_div_iff hq₁pos.ne' hq₂pos.ne']
    have h0R : ((a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    push_cast at h0R
    linarith
  have hnum_ge : (1 : ℝ) ≤ |(((a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) : ℤ) : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |(a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ)| :=
      Int.one_le_abs hnum_ne
    exact_mod_cast h1
  exact div_le_div_of_nonneg_right hnum_ge (mul_pos hq₁pos hq₂pos).le

/-- Pairwise disjointness of major arcs whenever `2 * Q^3 < N` and `1 ≤ Q`. -/
theorem majorArc_disjoint {N : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) (hQN : 2 * Q ^ 3 < (N : ℝ))
    {q₁ a₁ q₂ a₂ : ℕ}
    (hq₁ : q₁ ∈ Finset.Icc 1 ⌊Q⌋₊) (hq₂ : q₂ ∈ Finset.Icc 1 ⌊Q⌋₊)
    (hc₁ : Nat.Coprime a₁ q₁) (hc₂ : Nat.Coprime a₂ q₂)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Disjoint (majorArc N Q q₁ a₁) (majorArc N Q q₂ a₂) := by
  rw [Set.disjoint_left]
  intro α hα₁ hα₂
  have hq₁_1 : 1 ≤ q₁ := (Finset.mem_Icc.mp hq₁).1
  have hq₂_1 : 1 ≤ q₂ := (Finset.mem_Icc.mp hq₂).1
  have hq₁_Q : (q₁ : ℝ) ≤ Q :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hq₁).2).trans (Nat.floor_le (by linarith))
  have hq₂_Q : (q₂ : ℝ) ≤ Q :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hq₂).2).trans (Nat.floor_le (by linarith))
  have hNpos : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by linarith : 0 < Q) 3]
  have hsep := abs_sub_div_ge hq₁_1 hq₂_1 hc₁ hc₂ hne
  have htri : |(a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)| ≤ 2 * Q / (N : ℝ) := by
    have h1 : |α - (a₁ : ℝ) / (q₁ : ℝ)| ≤ Q / (N : ℝ) := hα₁
    have h2 : |α - (a₂ : ℝ) / (q₂ : ℝ)| ≤ Q / (N : ℝ) := hα₂
    have heq : (a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ) =
        -((α - (a₁ : ℝ) / (q₁ : ℝ)) - (α - (a₂ : ℝ) / (q₂ : ℝ))) := by ring
    rw [heq, abs_neg]
    calc |(α - (a₁ : ℝ) / (q₁ : ℝ)) - (α - (a₂ : ℝ) / (q₂ : ℝ))|
        ≤ |α - (a₁ : ℝ) / (q₁ : ℝ)| + |α - (a₂ : ℝ) / (q₂ : ℝ)| := abs_sub _ _
      _ ≤ Q / (N : ℝ) + Q / (N : ℝ) := add_le_add h1 h2
      _ = 2 * Q / (N : ℝ) := by ring
  have hprod_le : (q₁ : ℝ) * (q₂ : ℝ) ≤ Q ^ 2 := by nlinarith
  have hsepQ : 1 / Q ^ 2 ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) hprod_le
  have hlt : 2 * Q / (N : ℝ) < 1 / Q ^ 2 := by
    rw [div_lt_div_iff₀ hNpos (by positivity)]
    nlinarith
  linarith

/-- For `q ≥ 2` and `a ∈ (range (q + 1)).filter (Coprime · q)`, we have `1 ≤ a ≤ q - 1`,
and `majorArc N Q q a ⊆ Set.Icc 0 1` whenever `2 * Q^3 < N` and `1 ≤ Q`. -/
private lemma majorArc_subset_Icc_of_two_le {N : ℕ} {Q : ℝ} (hQ : 1 ≤ Q)
    (hQN : 2 * Q ^ 3 < (N : ℝ)) {q a : ℕ} (hq2 : 2 ≤ q) (hqQ : q ≤ ⌊Q⌋₊)
    (ha : a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)) :
    majorArc N Q q a ⊆ Set.Icc (0 : ℝ) 1 := by
  have ha_le : a ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
  have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
  have ha_ne0 : a ≠ 0 := by
    intro h0; subst h0; rw [Nat.coprime_zero_left] at hcop; omega
  have ha_neq : a ≠ q := by
    intro hq; subst hq; rw [Nat.coprime_self] at hcop; omega
  have ha1 : 1 ≤ a := by omega
  have ha_lt : a + 1 ≤ q := by omega
  have hqR : (q : ℝ) ≤ Q := (Nat.cast_le.mpr hqQ).trans (Nat.floor_le (by linarith))
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by linarith : 0 < Q) 3]
  have hQN_le : Q / (N : ℝ) ≤ 1 / (q : ℝ) := by
    rw [div_le_div_iff₀ hNpos hqpos]
    have hQ2 : Q ^ 2 ≤ Q ^ 3 := by nlinarith
    nlinarith
  intro α hα
  rw [majorArc_eq_Icc, Set.mem_Icc] at hα
  refine ⟨?_, ?_⟩
  · have h1 : 1 / (q : ℝ) ≤ (a : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast ha1) hqpos.le
    linarith [hα.1]
  · have h2 : (a : ℝ) / (q : ℝ) + 1 / (q : ℝ) ≤ 1 := by
      rw [← add_div, div_le_one hqpos]
      exact_mod_cast ha_lt
    linarith [hα.2]

/-- For `q ≥ 2`, filtering `range (q + 1)` by `Coprime · q` equals filtering `range q`. -/
private lemma filter_coprime_range_succ_eq {q : ℕ} (hq2 : 2 ≤ q) :
    (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q) =
      (Finset.range q).filter (fun a => Nat.Coprime a q) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hcop⟩
    refine ⟨?_, hcop⟩
    by_contra hge
    have haq : a = q := by omega
    subst haq
    rw [Nat.coprime_self] at hcop
    omega
  · rintro ⟨hlt, hcop⟩
    exact ⟨Nat.lt_succ_of_lt hlt, hcop⟩

/-- **Grand Major-Arc Integral Decomposition**: for `1 ≤ Q`, `2 * Q^3 < N`, and any
continuous 1-periodic `F : ℝ → ℂ`, the integral over `majorArcs N Q` equals the exact
double sum of symmetric integrals over `[-Q/N, Q/N]` around `a/q` (`1 ≤ q ≤ ⌊Q⌋₊`, `a < q`, `(a,q)=1`). -/
theorem integral_majorArcs_eq_sum {N : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) (hQN : 2 * Q ^ 3 < (N : ℝ))
    {F : ℝ → ℂ} (hFcont : Continuous F) (hFper : ∀ α : ℝ, F (α + 1) = F α) :
    ∫ α in majorArcs N Q, F α =
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ∫ β in (-(Q / (N : ℝ)))..(Q / (N : ℝ)), F ((a : ℝ) / (q : ℝ) + β) := by
  set M := ⌊Q⌋₊
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hQ)
  have hNpos : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by linarith : 0 < Q) 3]
  set δ : ℝ := Q / (N : ℝ)
  have hδ_pos : 0 < δ := div_pos (by linarith) hNpos
  have hδ_le_half : δ ≤ 1 / 2 := by
    dsimp only [δ]
    rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 2)]
    have hQ2 : Q ≤ Q ^ 2 := by nlinarith
    have hQ3 : Q ≤ Q ^ 3 := by nlinarith
    nlinarith
  have hIcc_int : IntegrableOn F (Set.Icc (0 : ℝ) 1) := hFcont.integrableOn_Icc
  -- Step 1: distribute `Icc 0 1 ∩ ⋃ q, ⋃ a, ...`
  have hrew : majorArcs N Q =
      ⋃ q ∈ Finset.Icc 1 M,
        ⋃ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
          (Set.Icc (0 : ℝ) 1 ∩ majorArc N Q q a) := by
    ext α
    simp only [majorArcs, Set.mem_inter_iff, Set.mem_iUnion, exists_prop, M]
    constructor
    · rintro ⟨hI, q, hq, a, ha, hα⟩
      exact ⟨q, hq, a, ha, hI, hα⟩
    · rintro ⟨q, hq, a, ha, hI, hα⟩
      exact ⟨hI, q, hq, a, ha, hα⟩
  rw [hrew]
  -- Outer biUnion over `q`
  have hdisj_q : (Finset.Icc 1 M : Set ℕ).PairwiseDisjoint
      (fun q => ⋃ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
        (Set.Icc (0 : ℝ) 1 ∩ majorArc N Q q a)) := by
    intro q₁ hq₁ q₂ hq₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro α h₁ h₂
    simp only [Set.mem_iUnion, exists_prop] at h₁ h₂
    obtain ⟨a₁, ha₁, _, hm₁⟩ := h₁
    obtain ⟨a₂, ha₂, _, hm₂⟩ := h₂
    have hdisj := majorArc_disjoint hQ hQN hq₁ hq₂
      (Finset.mem_filter.mp ha₁).2 (Finset.mem_filter.mp ha₂).2
      (fun h => hne (congrArg Prod.fst h))
    exact Set.disjoint_left.mp hdisj hm₁ hm₂
  have hmeas_q : ∀ q ∈ Finset.Icc 1 M,
      MeasurableSet (⋃ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
        (Set.Icc (0 : ℝ) 1 ∩ majorArc N Q q a)) := fun q _ =>
    Finset.measurableSet_biUnion _ fun a _ => measurableSet_Icc.inter (measurableSet_majorArc N Q q a)
  have hint_q : ∀ q ∈ Finset.Icc 1 M,
      IntegrableOn F (⋃ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
        (Set.Icc (0 : ℝ) 1 ∩ majorArc N Q q a)) := fun q _ =>
    hIcc_int.mono_set (Set.iUnion₂_subset fun _ _ => Set.inter_subset_left)
  rw [MeasureTheory.integral_biUnion_finset (Finset.Icc 1 M) hmeas_q hdisj_q hint_q]
  -- Evaluate each `q ∈ Icc 1 M`
  refine Finset.sum_congr rfl fun q hq => ?_
  -- Inner biUnion over `a`
  have hdisj_a : ((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q) : Set ℕ).PairwiseDisjoint
      (fun a => Set.Icc (0 : ℝ) 1 ∩ majorArc N Q q a) := by
    intro a₁ ha₁ a₂ ha₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro α h₁ h₂
    have hdisj := majorArc_disjoint hQ hQN hq hq
      (Finset.mem_filter.mp ha₁).2 (Finset.mem_filter.mp ha₂).2
      (fun h => hne (congrArg Prod.snd h))
    exact Set.disjoint_left.mp hdisj h₁.2 h₂.2
  have hmeas_a : ∀ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
      MeasurableSet (Set.Icc (0 : ℝ) 1 ∩ majorArc N Q q a) := fun a _ =>
    measurableSet_Icc.inter (measurableSet_majorArc N Q q a)
  have hint_a : ∀ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
      IntegrableOn F (Set.Icc (0 : ℝ) 1 ∩ majorArc N Q q a) := fun a _ =>
    hIcc_int.mono_set Set.inter_subset_left
  rw [MeasureTheory.integral_biUnion_finset _ hmeas_a hdisj_a hint_a]
  by_cases hq1 : q = 1
  · -- Case `q = 1`: recombine `[0, δ]` and `[1 - δ, 1]` via 1-periodicity!
    subst hq1
    have hset1 : (Finset.range (1 + 1)).filter (fun a => Nat.Coprime a 1) = {0, 1} := by decide
    have hset0 : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
    rw [hset1, hset0, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), Finset.sum_singleton]
    have hI0 : Set.Icc (0 : ℝ) 1 ∩ majorArc N Q 1 0 = Set.Icc 0 δ := by
      rw [majorArc_eq_Icc]
      ext α; simp only [Set.mem_inter_iff, Set.mem_Icc, Nat.cast_zero, Nat.cast_one, zero_div,
        zero_sub, zero_add]
      constructor
      · rintro ⟨⟨h1, _⟩, ⟨_, h4⟩⟩; exact ⟨h1, h4⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, ⟨by linarith, h2⟩⟩
    have hI1 : Set.Icc (0 : ℝ) 1 ∩ majorArc N Q 1 1 = Set.Icc (1 - δ) 1 := by
      rw [majorArc_eq_Icc]
      ext α; simp only [Set.mem_inter_iff, Set.mem_Icc, Nat.cast_one, div_one]
      constructor
      · rintro ⟨⟨_, h2⟩, ⟨h3, _⟩⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, ⟨h1, by linarith⟩⟩
    rw [hI0, hI1, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hδ_pos.le,
      ← intervalIntegral.integral_of_le (by linarith : 1 - δ ≤ 1)]
    have hshift : (∫ α in (1 - δ)..1, F α) = ∫ β in (-δ)..0, F β := by
      have h1 := intervalIntegral.integral_comp_add_right F (1 : ℝ) (a := -δ) (b := 0)
      have h2 : (∫ β in (-δ)..0, F (β + 1)) = ∫ β in (-δ)..0, F β :=
        intervalIntegral.integral_congr fun β _ => hFper β
      rw [h2] at h1
      have ha : -δ + 1 = 1 - δ := by ring
      have hb : (0 : ℝ) + 1 = 1 := by ring
      rw [ha, hb] at h1
      exact h1.symm
    rw [hshift, add_comm, intervalIntegral.integral_add_adjacent_intervals
      (hFcont.intervalIntegrable _ _) (hFcont.intervalIntegrable _ _)]
    simp only [Nat.cast_zero, Nat.cast_one, zero_div, zero_add]
  · -- Case `q ≥ 2`: every arc lies strictly inside `[0, 1]`!
    have hq2 : 2 ≤ q := by have := (Finset.mem_Icc.mp hq).1; omega
    have hqQ : q ≤ ⌊Q⌋₊ := (Finset.mem_Icc.mp hq).2
    rw [filter_coprime_range_succ_eq hq2]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q) := by
      rw [filter_coprime_range_succ_eq hq2]; exact ha
    have hsub : majorArc N Q q a ⊆ Set.Icc (0 : ℝ) 1 :=
      majorArc_subset_Icc_of_two_le hQ hQN hq2 hqQ ha'
    rw [Set.inter_eq_right.mpr hsub, majorArc_eq_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (a : ℝ) / q - δ ≤ (a : ℝ) / q + δ)]
    have hshift := intervalIntegral.integral_comp_add_left F ((a : ℝ) / (q : ℝ)) (a := -δ) (b := δ)
    have ha_eq : (a : ℝ) / (q : ℝ) + -δ = (a : ℝ) / (q : ℝ) - δ := by ring
    rw [ha_eq] at hshift
    exact hshift.symm

/-! ## Section 2: Uniform Single-Arc Approximation via Unconditional Full Siegel–Walfisz -/

/-- Exact norm of `e(β) - 1`: `‖e β - 1‖ = 2 * |sin (π * β)|`. -/
theorem norm_e_sub_one (β : ℝ) : ‖e β - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
  set θ : ℝ := Real.pi * β
  have h1 : e β - 1 = Complex.exp ((θ : ℂ) * Complex.I) *
      (Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp (-((θ : ℂ) * Complex.I))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    congr 1
    simp only [e, θ]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp (-((θ : ℂ) * Complex.I)) =
      2 * (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]
    ring
  rw [h1, h2, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs]

/-- Lipschitz bound on `e`: `‖e β - 1‖ ≤ 2 * π * |β|`. -/
theorem norm_e_sub_one_le (β : ℝ) : ‖e β - 1‖ ≤ 2 * Real.pi * |β| := by
  rw [norm_e_sub_one]
  have hsin : |Real.sin (Real.pi * β)| ≤ |Real.pi * β| := Real.abs_sin_le_abs
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  linarith

/-- Lower bound on `‖e β - 1‖` for `|β| ≤ 1 / 2`: `4 * |β| ≤ ‖e β - 1‖`. -/
theorem four_mul_abs_le_norm_e_sub_one {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    4 * |β| ≤ ‖e β - 1‖ := by
  rw [norm_e_sub_one]
  have hsin_abs : |Real.sin (Real.pi * β)| = Real.sin (Real.pi * |β|) := by
    by_cases h : 0 ≤ β
    · rw [abs_of_nonneg h, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le h)
        (by nlinarith [Real.pi_pos, abs_of_nonneg h])
    · push Not at h
      rw [abs_of_neg h]
      have hpos : 0 ≤ Real.pi * (-β) := by nlinarith [Real.pi_pos]
      have hle_pi : Real.pi * (-β) ≤ Real.pi := by
        have : -β ≤ 1 / 2 := by rw [abs_of_neg h] at hβ; exact hβ
        nlinarith [Real.pi_pos]
      have hsin_nn : 0 ≤ Real.sin (Real.pi * (-β)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hpos hle_pi
      have hneg_eq : Real.sin (Real.pi * β) = -Real.sin (Real.pi * (-β)) := by
        rw [mul_neg, Real.sin_neg, neg_neg]
      rw [hneg_eq, abs_neg, abs_of_nonneg hsin_nn]
  rw [hsin_abs]
  have hle : Real.pi * |β| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hmul := Real.mul_le_sin (mul_nonneg Real.pi_pos.le (abs_nonneg β)) hle
  have hsimp : 2 / Real.pi * (Real.pi * |β|) = 2 * |β| := by
    field_simp [Real.pi_ne_zero]
  linarith

/-- Step difference bound: `‖e ((n + 1) * β) - e (n * β)‖ ≤ 2 * π * |β|`. -/
private lemma norm_e_step_diff (n : ℕ) (β : ℝ) :
    ‖e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have h1 : e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β) =
      e ((n : ℝ) * β) * (e β - 1) := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, e_add]
    ring
  rw [h1, norm_mul, norm_e, one_mul]
  exact norm_e_sub_one_le β

/-- For a non-coprime residue `r < q` (`q ≠ 0`), at most one prime `p` has `p % q = r`,
and any such prime satisfies `p ≤ q`, giving `‖thetaAP_twist q r N β‖ ≤ log q`. -/
private lemma norm_thetaAP_twist_noncoprime_le {q r N : ℕ} (β : ℝ) (hq : q ≠ 0)
    (hr : r < q) (hncop : ¬ Nat.Coprime r q) :
    ‖thetaAP_twist q r N β‖ ≤ Real.log (q : ℝ) := by
  rw [thetaAP_twist_fiber q r N β hr]
  set s := ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p % q = r)
  have huniq : ∀ p ∈ s, p = if r = 0 then q else r := by
    intro p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hp_mod : p % q = r := (Finset.mem_filter.mp hp).2
    have hnotcop_pq : ¬ Nat.Coprime p q := by
      intro hcop
      apply hncop
      rw [← hp_mod, Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec]
      exact hcop.symm
    have hpdvd : p ∣ q := by
      by_contra hndvd
      exact hnotcop_pq (hp_prime.coprime_iff_not_dvd.mpr hndvd)
    have hp_le : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpdvd
    by_cases hr0 : r = 0
    · simp only [hr0, ↓reduceIte]
      have hqdvd : q ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
      exact Nat.dvd_antisymm hpdvd hqdvd
    · simp only [hr0, ↓reduceIte]
      have hp_lt : p < q := by
        rcases eq_or_lt_of_le hp_le with rfl | hlt
        · simp [Nat.mod_self] at hp_mod; omega
        · exact hlt
      rw [Nat.mod_eq_of_lt hp_lt] at hp_mod
      exact hp_mod
  have hsub : s ⊆ {if r = 0 then q else r} := fun p hp => Finset.mem_singleton.mpr (huniq p hp)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  by_cases hs : s = ∅
  · rw [hs, Finset.sum_empty, norm_zero]
    exact Real.log_nonneg hq1
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hseq : s = {p₀} := by
      ext p
      constructor
      · intro hp
        rw [Finset.mem_singleton]
        rw [huniq p hp, huniq p₀ hp₀]
      · intro hp
        rw [Finset.mem_singleton] at hp
        rwa [hp]
    rw [hseq, Finset.sum_singleton, norm_mul, norm_e, mul_one, Complex.norm_real]
    have hp₀_prime : p₀.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₀).1).2
    have hp₀_le : p₀ ≤ q := by
      have := huniq p₀ hp₀
      split_ifs at this <;> omega
    have hlog_nn : 0 ≤ Real.log (p₀ : ℝ) := Real.log_nonneg (by exact_mod_cast hp₀_prime.one_lt.le)
    rw [Real.norm_of_nonneg hlog_nn]
    exact Real.log_le_log (by exact_mod_cast hp₀_prime.pos) (by exact_mod_cast hp₀_le)

/-- Trivial upper bound: `0 ≤ chebyshevThetaAP q r n ≤ n * log n` (for `n ≥ 1`, and `≤ n * log N` for `n ≤ N`). -/
private lemma chebyshevThetaAP_le_mul_log {q r n N : ℕ} (hn : n ≤ N) (hN : 1 ≤ N) :
    Stage2DirichletAP.chebyshevThetaAP q r n ≤ (n : ℝ) * Real.log (N : ℝ) := by
  unfold Stage2DirichletAP.chebyshevThetaAP
  rw [Nat.floor_natCast]
  have h0 : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [h0, Finset.sum_insert (by simp)]
  simp only [Nat.not_prime_zero, false_and, ↓reduceIte, zero_add]
  calc ∑ k ∈ Finset.Icc 1 n, (if k.Prime ∧ k ≡ r [MOD q] then Real.log (k : ℝ) else 0)
      ≤ ∑ _k ∈ Finset.Icc 1 n, Real.log (N : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2.trans hn
        split_ifs
        · exact Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast hkN)
        · exact Real.log_nonneg (by exact_mod_cast hN)
    _ = (n : ℝ) * Real.log (N : ℝ) := by
        simp [Nat.card_Icc]

private lemma chebyshevThetaAP_nonneg (q r n : ℕ) :
    0 ≤ Stage2DirichletAP.chebyshevThetaAP q r n := by
  unfold Stage2DirichletAP.chebyshevThetaAP
  refine Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.1.one_lt.le)
  · exact le_rfl

/-- Asymptotic decay: for `c > 0` and any `K : ℝ`, `(log x)^K * exp (-c * √(log x)) → 0` as `x → ∞`. -/
private lemma tendsto_log_rpow_mul_exp_neg_sqrt {c : ℝ} (hc : 0 < c) (K : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ K * Real.exp (-c * Real.sqrt (Real.log x))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => u ^ (2 * K) * Real.exp (-c * u)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun t : ℝ => t ^ (2 * K) * Real.exp (-t)) atTop (𝓝 0) := by
      have := (isLittleO_rpow_exp_atTop (2 * K)).tendsto_div_nhds_zero
      refine this.congr' (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [Real.exp_neg, div_eq_mul_inv]
    have hscale : Tendsto (fun u : ℝ => (c * u) ^ (2 * K) * Real.exp (-(c * u))) atTop (𝓝 0) :=
      hpow.comp (Tendsto.const_mul_atTop hc tendsto_id)
    have hconst : Tendsto (fun u : ℝ => c ^ (-(2 * K)) * ((c * u) ^ (2 * K) * Real.exp (-(c * u))))
        atTop (𝓝 (c ^ (-(2 * K)) * 0)) := hscale.const_mul _
    rw [mul_zero] at hconst
    refine hconst.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [Real.mul_rpow hc.le hu.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hc,
      neg_add_cancel, Real.rpow_zero, one_mul, neg_mul]
  have hcomp : Tendsto (fun x : ℝ =>
      (Real.sqrt (Real.log x)) ^ (2 * K) * Real.exp (-c * Real.sqrt (Real.log x))) atTop (𝓝 0) :=
    h1.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlog]
  congr 2
  ring

/-- **Uniform Single-Arc Approximation via Unconditional Full Siegel–Walfisz**:
for every `B ≥ 1` and every `D ≥ 0`, for all sufficiently large `N`,
`‖S N (a/q + β) - (μ(q)/φ(q)) * v N β‖ ≤ N / (log N)^D` uniformly for all `1 ≤ q ≤ (log N)^B`,
`(a, q) = 1`, and `|β| ≤ (log N)^B / N`. -/
theorem single_arc_S_approx (B D : ℝ) (hB : 1 ≤ B) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, 16 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        let Q := (Real.log (N : ℝ)) ^ B
        ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊,
          ∀ a : ℕ, Nat.Coprime a q →
            ∀ β : ℝ, |β| ≤ Q / (N : ℝ) →
              ‖S N ((a : ℝ) / (q : ℝ) + β) -
                ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v N β‖ ≤
                (N : ℝ) / (Real.log (N : ℝ)) ^ D := by
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := Stage10SiegelWalfiszFull.siegel_walfisz_theta
  obtain ⟨C_sw, hC_sw, hsw⟩ := hsw_all (B + 1) (by linarith)
  set c₁ : ℝ := c_sw / 2
  have hc₁ : 0 < c₁ := by positivity
  -- Thresholds for asymptotic domination
  have h_log_ge : ∀ᶠ x : ℝ in atTop, 2 ^ (B + 1) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 ^ (B + 1)))
  have h_log_gt1 : ∀ᶠ x : ℝ in atTop, 2 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  have h_exp1 : ∀ᶠ x : ℝ in atTop,
      (1 + 2 * Real.pi) * C_sw * (Real.log x) ^ (2 * B + D) *
        Real.exp (-c₁ * Real.sqrt (Real.log x)) < 1 / 2 := by
    have h := ((tendsto_log_rpow_mul_exp_neg_sqrt hc₁ (2 * B + D)).const_mul
      ((1 + 2 * Real.pi) * C_sw)).eventually
      (Iio_mem_nhds (by linarith : (1 + 2 * Real.pi) * C_sw * 0 < (1 / 2 : ℝ)))
    filter_upwards [h] with x hx
    linarith
  have h_poly : ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ (2 * B + D + 2) / x < 1 / (8 * (1 + Real.pi)) := by
    have ht : Tendsto (fun x : ℝ => (Real.log x) ^ (2 * B + D + 2) / x ^ (1 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_rpow_atTop (2 * B + D + 2) zero_lt_one).tendsto_div_nhds_zero
    have ht' : Tendsto (fun x : ℝ => (Real.log x) ^ (2 * B + D + 2) / x) atTop (𝓝 0) := by
      refine ht.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
      rw [Real.rpow_one]
    exact ht'.eventually (Iio_mem_nhds (by positivity))
  have hall := (h_log_ge.and (h_log_gt1.and (h_exp1.and h_poly))).and (eventually_ge_atTop (16 : ℝ))
  rw [Filter.eventually_atTop] at hall
  obtain ⟨X₀, hX₀⟩ := hall
  refine ⟨max 16 ⌈X₀⌉₊, le_max_left _ _, fun N hN => ?_⟩
  intro Q q hq a hcop β hβ
  have hN16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_max_left 16 ⌈X₀⌉₊).trans hN
  have hNX : X₀ ≤ (N : ℝ) := (Nat.le_ceil X₀).trans (by exact_mod_cast (le_max_right 16 ⌈X₀⌉₊).trans hN)
  obtain ⟨⟨hlog_pow, hlog2, hexp_bd, hpoly_bd⟩, _⟩ := hX₀ (N : ℝ) hNX
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (N : ℝ) := by linarith
  have hQ_pos : 0 < Q := Real.rpow_pos_of_pos hlog_pos B
  have hQ_ge1 : 1 ≤ Q := Real.one_le_rpow (by linarith) (by linarith)
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hq_ne : q ≠ 0 := by omega
  have : NeZero q := ⟨hq_ne⟩
  have hqQ : (q : ℝ) ≤ Q :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le hQ_pos.le)
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  -- Apply `S_single_arc_approx`
  have happrox := S_single_arc_approx N a q β hq_ne hcop
  have hdiff : S N ((a : ℝ) / (q : ℝ) + β) -
      ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v N β =
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) *
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β)))) +
      ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
        e (((r : ℝ) * a) / q) * thetaAP_twist q r N β := by
    rw [happrox]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hdiff]
  -- Bound the non-coprime sum
  have hnoncop_bd : ‖∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
      e (((r : ℝ) * a) / q) * thetaAP_twist q r N β‖ ≤ Q * Real.log (N : ℝ) := by
    calc ‖∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
            e (((r : ℝ) * a) / q) * thetaAP_twist q r N β‖
        ≤ ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
            ‖e (((r : ℝ) * a) / q) * thetaAP_twist q r N β‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q), Real.log (N : ℝ) := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [norm_mul, norm_e, one_mul]
          have hr_lt : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
          have hr_ncop : ¬ Nat.Coprime r q := (Finset.mem_filter.mp hr).2
          have hlogq_le : Real.log (q : ℝ) ≤ Real.log (N : ℝ) := by
            refine Real.log_le_log (by positivity) ?_
            have hQleN : Q ≤ (N : ℝ) := by
              have h1 : Q ≤ (Real.log (N : ℝ)) ^ (2 * B + D + 2) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
              have h2 : (Real.log (N : ℝ)) ^ (2 * B + D + 2) < (N : ℝ) / (8 * (1 + Real.pi)) := by
                have := (div_lt_iff₀ hNpos).mp hpoly_bd
                linarith [show (1 / (8 * (1 + Real.pi))) * (N : ℝ) = (N : ℝ) / (8 * (1 + Real.pi)) by ring]
              have h3 : (N : ℝ) / (8 * (1 + Real.pi)) ≤ (N : ℝ) :=
                div_le_self hNpos.le (by linarith [Real.pi_pos])
              linarith
            exact hqQ.trans hQleN
          exact (norm_thetaAP_twist_noncoprime_le β hq_ne hr_lt hr_ncop).trans hlogq_le
      _ ≤ (q : ℝ) * Real.log (N : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hlog_pos.le
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      _ ≤ Q * Real.log (N : ℝ) := mul_le_mul_of_nonneg_right hqQ hlog_pos.le
  -- Uniform SW bound for any `n` with `√N ≤ n ≤ N`
  have hsw_large : ∀ r : ℕ, Nat.Coprime r q → ∀ n : ℕ, Real.sqrt (N : ℝ) ≤ (n : ℝ) → n ≤ N →
      |Stage2DirichletAP.chebyshevThetaAP q r n - (n : ℝ) / (q.totient : ℝ)| ≤
        C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
    intro r hrcop n hn_lo hn_hi
    have hn4 : (4 : ℝ) ≤ (n : ℝ) := by
      have : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [Real.le_sqrt (by norm_num) hNpos.le]; linarith
      linarith
    have hlogn_ge : Real.log (N : ℝ) / 2 ≤ Real.log (n : ℝ) := by
      have h1 : Real.log (Real.sqrt (N : ℝ)) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (Real.sqrt_pos.mpr hNpos) hn_lo
      rwa [Real.log_sqrt hNpos.le] at h1
    have hq_logn : (q : ℝ) ≤ (Real.log (n : ℝ)) ^ (B + 1) := by
      have h2B1 : (Real.log (N : ℝ) / 2) ^ (B + 1) =
          (Real.log (N : ℝ)) ^ B * (Real.log (N : ℝ) / 2 ^ (B + 1)) := by
        rw [Real.div_rpow hlog_pos.le (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_add hlog_pos, Real.rpow_one]
        ring
      have hratio : 1 ≤ Real.log (N : ℝ) / 2 ^ (B + 1) :=
        (one_le_div (Real.rpow_pos_of_pos (by norm_num) _)).mpr hlog_pow
      calc (q : ℝ) ≤ Q := hqQ
        _ = (Real.log (N : ℝ)) ^ B * 1 := by ring
        _ ≤ (Real.log (N : ℝ)) ^ B * (Real.log (N : ℝ) / 2 ^ (B + 1)) :=
            mul_le_mul_of_nonneg_left hratio hQ_pos.le
        _ = (Real.log (N : ℝ) / 2) ^ (B + 1) := h2B1.symm
        _ ≤ (Real.log (n : ℝ)) ^ (B + 1) :=
            Real.rpow_le_rpow (by linarith) hlogn_ge (by linarith)
    have hbd := hsw (n : ℝ) hn4 q hq_logn r hrcop
    have hsq_ge : Real.sqrt (Real.log (N : ℝ)) / 2 ≤ Real.sqrt (Real.log (n : ℝ)) := by
      have h1 : Real.sqrt (Real.log (N : ℝ) / 2) ≤ Real.sqrt (Real.log (n : ℝ)) :=
        Real.sqrt_le_sqrt hlogn_ge
      have h2 : Real.sqrt (Real.log (N : ℝ)) / 2 ≤ Real.sqrt (Real.log (N : ℝ) / 2) := by
        rw [Real.sqrt_div hlog_pos.le]
        have hsq2 : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr (by norm_num)) hsq2
      exact h2.trans h1
    have hexp_le : Real.exp (-c_sw * Real.sqrt (Real.log (n : ℝ))) ≤
        Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      dsimp only [c₁]
      nlinarith
    have hn_le_N : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn_hi
    calc |Stage2DirichletAP.chebyshevThetaAP q r n - (n : ℝ) / (q.totient : ℝ)|
        ≤ C_sw * (n : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (n : ℝ))) := hbd
      _ ≤ C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hn_le_N hC_sw.le) hexp_le
            (Real.exp_pos _).le (by positivity)
  -- Bound the coprime sum for each coprime `r`
  have hcop_term : ∀ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
      ‖e (((r : ℝ) * a) / q) *
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β)))‖ ≤
      1 + C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) +
        2 * Real.pi * Q * (Real.log (N : ℝ) + 1) * (1 + 1 / Real.sqrt (N : ℝ)) +
        2 * Real.pi * Q * C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
    intro r hr
    have hrcop : Nat.Coprime r q := (Finset.mem_filter.mp hr).2
    rw [norm_mul, norm_e, one_mul]
    have h1 : ‖-(1 : ℂ) / (q.totient : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_neg, norm_one, Complex.norm_natCast]
      exact div_le_one_of_le₀ hphi_ge1 (by positivity)
    have h2 : ‖((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
        e ((N : ℝ) * β)‖ ≤ C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
      rw [norm_mul, norm_e, mul_one]
      have hcast : ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) =
          ((Stage2DirichletAP.chebyshevThetaAP q r N - (N : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      have hsqN : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
        rw [Real.sqrt_le_left hNpos.le]; nlinarith
      exact hsw_large r hrcop N hsqN le_rfl
    -- Split the `n ∈ range N` sum into `n < √N` and `√N ≤ n`
    set M_cut := ⌊Real.sqrt (N : ℝ)⌋₊
    have hsum_bd : ‖∑ n ∈ Finset.range N,
        ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
          (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β))‖ ≤
        2 * Real.pi * Q * (Real.log (N : ℝ) + 1) * (1 + 1 / Real.sqrt (N : ℝ)) +
        2 * Real.pi * Q * C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
      have hstep : ∀ n ∈ Finset.range N,
          ‖((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
            (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β))‖ ≤
          |Stage2DirichletAP.chebyshevThetaAP q r n - (n : ℝ) / (q.totient : ℝ)| *
            (2 * Real.pi * Q / (N : ℝ)) := by
        intro n _
        rw [norm_mul]
        have hcast : ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) =
            ((Stage2DirichletAP.chebyshevThetaAP q r n - (n : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) := by
          push_cast; rfl
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc ‖e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β)‖
            ≤ 2 * Real.pi * |β| := norm_e_step_diff n β
          _ ≤ 2 * Real.pi * (Q / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hβ (by positivity)
          _ = 2 * Real.pi * Q / (N : ℝ) := by ring
      calc ‖∑ n ∈ Finset.range N,
              ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
                (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β))‖
          ≤ ∑ n ∈ Finset.range N,
              ‖((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
                (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β))‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range N,
              |Stage2DirichletAP.chebyshevThetaAP q r n - (n : ℝ) / (q.totient : ℝ)| *
                (2 * Real.pi * Q / (N : ℝ)) := Finset.sum_le_sum hstep
        _ = (2 * Real.pi * Q / (N : ℝ)) *
              ∑ n ∈ Finset.range N,
                |Stage2DirichletAP.chebyshevThetaAP q r n - (n : ℝ) / (q.totient : ℝ)| := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => mul_comm _ _
        _ ≤ (2 * Real.pi * Q / (N : ℝ)) *
              ((Real.sqrt (N : ℝ) + 1) * (Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1)) +
                (N : ℝ) * (C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun n => n ≤ M_cut)]
            refine add_le_add ?_ ?_
            · -- Small `n ≤ M_cut`: each term `≤ √N * (log N + 1)`, at most `√N + 1` terms
              calc ∑ n ∈ (Finset.range N).filter (fun n => n ≤ M_cut),
                      |Stage2DirichletAP.chebyshevThetaAP q r n - (n : ℝ) / (q.totient : ℝ)|
                  ≤ ∑ _n ∈ (Finset.range N).filter (fun n => n ≤ M_cut),
                      Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) := by
                    refine Finset.sum_le_sum fun n hn => ?_
                    have hnN : n ≤ N := (Finset.mem_range.mp (Finset.mem_filter.mp hn).1).le
                    have hnM : (n : ℝ) ≤ Real.sqrt (N : ℝ) :=
                      (Nat.cast_le.mpr (Finset.mem_filter.mp hn).2).trans
                        (Nat.floor_le (Real.sqrt_nonneg _))
                    have hth_nn := chebyshevThetaAP_nonneg q r n
                    have hth_le := chebyshevThetaAP_le_mul_log (q := q) (r := r) hnN (by omega)
                    have hdiv_le : (n : ℝ) / (q.totient : ℝ) ≤ (n : ℝ) :=
                      div_le_self (Nat.cast_nonneg n) hphi_ge1
                    have hdiv_nn : 0 ≤ (n : ℝ) / (q.totient : ℝ) := by positivity
                    rw [abs_le]
                    constructor
                    · nlinarith
                    · nlinarith
                _ = (((Finset.range N).filter (fun n => n ≤ M_cut)).card : ℝ) *
                      (Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1)) := by
                    rw [Finset.sum_const, nsmul_eq_mul]
                _ ≤ (Real.sqrt (N : ℝ) + 1) * (Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1)) := by
                    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                    have hsub : (Finset.range N).filter (fun n => n ≤ M_cut) ⊆
                        Finset.range (M_cut + 1) := fun n hn =>
                      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hn).2)
                    have hcard : ((Finset.range N).filter (fun n => n ≤ M_cut)).card ≤ M_cut + 1 :=
                      (Finset.card_le_card hsub).trans (by simp)
                    have hM_le : (M_cut : ℝ) ≤ Real.sqrt (N : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
                    have : (((Finset.range N).filter (fun n => n ≤ M_cut)).card : ℝ) ≤ (M_cut : ℝ) + 1 := by
                      exact_mod_cast hcard
                    linarith
            · -- Large `n > M_cut` (hence `√N ≤ n`): use `hsw_large`
              calc ∑ n ∈ (Finset.range N).filter (fun n => ¬ n ≤ M_cut),
                      |Stage2DirichletAP.chebyshevThetaAP q r n - (n : ℝ) / (q.totient : ℝ)|
                  ≤ ∑ _n ∈ (Finset.range N).filter (fun n => ¬ n ≤ M_cut),
                      C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
                    refine Finset.sum_le_sum fun n hn => ?_
                    have hnN : n ≤ N := (Finset.mem_range.mp (Finset.mem_filter.mp hn).1).le
                    have hgt : M_cut < n := not_le.mp (Finset.mem_filter.mp hn).2
                    have hsq : Real.sqrt (N : ℝ) ≤ (n : ℝ) :=
                      (Nat.lt_floor_add_one (Real.sqrt (N : ℝ))).le.trans (by exact_mod_cast hgt)
                    exact hsw_large r hrcop n hsq hnN
                _ ≤ (N : ℝ) * (C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ)))) := by
                    rw [Finset.sum_const, nsmul_eq_mul]
                    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
        _ = 2 * Real.pi * Q * (Real.log (N : ℝ) + 1) * (1 + 1 / Real.sqrt (N : ℝ)) +
            2 * Real.pi * Q * C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
            have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNpos.le
            have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
            have hmul : (Real.sqrt (N : ℝ) + 1) * Real.sqrt (N : ℝ) / (N : ℝ) =
                1 + 1 / Real.sqrt (N : ℝ) := by
              rw [div_eq_iff hNpos.ne']
              field_simp [hsq_ne]
              linarith [hsq]
            rw [mul_add]
            congr 1
            · calc (2 * Real.pi * Q / (N : ℝ)) *
                      ((Real.sqrt (N : ℝ) + 1) * (Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1)))
                  = 2 * Real.pi * Q * (Real.log (N : ℝ) + 1) *
                      ((Real.sqrt (N : ℝ) + 1) * Real.sqrt (N : ℝ) / (N : ℝ)) := by ring
                _ = 2 * Real.pi * Q * (Real.log (N : ℝ) + 1) * (1 + 1 / Real.sqrt (N : ℝ)) := by
                    rw [hmul]
            · field_simp [hNpos.ne']
    have htri1 := norm_sub_le
      (-(1 : ℂ) / (q.totient : ℂ) +
        ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) * e ((N : ℝ) * β))
      (∑ n ∈ Finset.range N,
        ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
          (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β)))
    have htri2 := norm_add_le (-(1 : ℂ) / (q.totient : ℂ))
      (((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) * e ((N : ℝ) * β))
    linarith
  -- Sum over coprime `r` (at most `q ≤ Q` terms) and combine with non-coprime bound
  have hcop_sum_bd :
      ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) *
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β)))‖ ≤
      Q * (1 + C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) +
        2 * Real.pi * Q * (Real.log (N : ℝ) + 1) * (1 + 1 / Real.sqrt (N : ℝ)) +
        2 * Real.pi * Q * C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ)))) := by
    calc ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), _‖
        ≤ ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), _ := Finset.sum_le_sum hcop_term
      _ ≤ (q : ℝ) * _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      _ ≤ Q * _ := mul_le_mul_of_nonneg_right hqQ (by positivity)
  -- Final assembly: split total into exponential part `≤ (1/2) * N / (log N)^D` and poly-log part `≤ (1/2) * N / (log N)^D`
  have htot : ‖(∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) *
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β)))) +
      ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
        e (((r : ℝ) * a) / q) * thetaAP_twist q r N β‖ ≤
      (1 + 2 * Real.pi) * C_sw * Q ^ 2 * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) +
      4 * (1 + Real.pi) * Q ^ 2 * (Real.log (N : ℝ)) ^ 2 := by
    have htri := norm_add_le
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e (((r : ℝ) * a) / q) *
        (-(1 : ℂ) / (q.totient : ℂ) +
          ((Stage2DirichletAP.chebyshevThetaAP q r N : ℂ) - (N : ℂ) / (q.totient : ℂ)) *
            e ((N : ℝ) * β) -
          ∑ n ∈ Finset.range N,
            ((Stage2DirichletAP.chebyshevThetaAP q r n : ℂ) - (n : ℂ) / (q.totient : ℂ)) *
              (e (((n + 1 : ℕ) : ℝ) * β) - e ((n : ℝ) * β))))
      (∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
        e (((r : ℝ) * a) / q) * thetaAP_twist q r N β)
    have hinv_sq : 1 + 1 / Real.sqrt (N : ℝ) ≤ 2 := by
      have : 1 ≤ Real.sqrt (N : ℝ) := by rw [Real.one_le_sqrt]; linarith
      have : 1 / Real.sqrt (N : ℝ) ≤ 1 := div_le_one_of_le₀ this (Real.sqrt_nonneg _)
      linarith
    have hQ_le_Q2 : Q ≤ Q ^ 2 := by nlinarith
    have hlog_le : Real.log (N : ℝ) + 1 ≤ (Real.log (N : ℝ)) ^ 2 := by nlinarith
    have h1_le_log2 : 1 ≤ (Real.log (N : ℝ)) ^ 2 := by nlinarith
    have hlog_le_log2 : Real.log (N : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by nlinarith
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hexp_nn : 0 ≤ C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by positivity
    have hterm_exp : Q * (C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ)))) +
        Q * (2 * Real.pi * Q * C_sw * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ)))) ≤
        (1 + 2 * Real.pi) * C_sw * Q ^ 2 * (N : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) := by
      nlinarith
    have hterm_poly : Q * 1 + Q * (2 * Real.pi * Q * (Real.log (N : ℝ) + 1) * (1 + 1 / Real.sqrt (N : ℝ))) +
        Q * Real.log (N : ℝ) ≤ 4 * (1 + Real.pi) * Q ^ 2 * (Real.log (N : ℝ)) ^ 2 := by
      have hmid : 2 * Real.pi * Q ^ 2 * (Real.log (N : ℝ) + 1) * (1 + 1 / Real.sqrt (N : ℝ)) ≤
          4 * Real.pi * Q ^ 2 * (Real.log (N : ℝ)) ^ 2 := by
        calc 2 * Real.pi * Q ^ 2 * (Real.log (N : ℝ) + 1) * (1 + 1 / Real.sqrt (N : ℝ))
            ≤ 2 * Real.pi * Q ^ 2 * (Real.log (N : ℝ)) ^ 2 * 2 := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hlog_le (by positivity)) hinv_sq
                (by positivity) (by positivity)
          _ = 4 * Real.pi * Q ^ 2 * (Real.log (N : ℝ)) ^ 2 := by ring
      nlinarith
    linarith
  -- Show each of the two pieces is `≤ (1/2) * N / (log N)^D`
  have hlogD_pos : 0 < (Real.log (N : ℝ)) ^ D := Real.rpow_pos_of_pos hlog_pos D
  have hQ2_eq : Q ^ 2 = (Real.log (N : ℝ)) ^ (2 * B) := by
    dsimp only [Q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog_pos.le]
    congr 1; push_cast; ring
  have hpiece1 : (1 + 2 * Real.pi) * C_sw * Q ^ 2 * (N : ℝ) *
      Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) ≤ (1 / 2) * ((N : ℝ) / (Real.log (N : ℝ)) ^ D) := by
    rw [hQ2_eq]
    have hrhs : (1 + 2 * Real.pi) * C_sw * (Real.log (N : ℝ)) ^ (2 * B) * (N : ℝ) *
        Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ))) =
        ((1 + 2 * Real.pi) * C_sw * (Real.log (N : ℝ)) ^ (2 * B + D) *
          Real.exp (-c₁ * Real.sqrt (Real.log (N : ℝ)))) * ((N : ℝ) / (Real.log (N : ℝ)) ^ D) := by
      rw [Real.rpow_add hlog_pos]
      field_simp [hlogD_pos.ne']
    rw [hrhs]
    exact mul_le_mul_of_nonneg_right hexp_bd.le (by positivity)
  have hpiece2 : 4 * (1 + Real.pi) * Q ^ 2 * (Real.log (N : ℝ)) ^ 2 ≤
      (1 / 2) * ((N : ℝ) / (Real.log (N : ℝ)) ^ D) := by
    rw [hQ2_eq]
    have hpow_comb : (Real.log (N : ℝ)) ^ (2 * B) * (Real.log (N : ℝ)) ^ 2 * (Real.log (N : ℝ)) ^ D =
        (Real.log (N : ℝ)) ^ (2 * B + D + 2) := by
      rw [← Real.rpow_natCast (Real.log (N : ℝ)) 2, ← Real.rpow_add hlog_pos, ← Real.rpow_add hlog_pos]
      congr 1; push_cast; ring
    have hmul := (div_lt_iff₀ hNpos).mp hpoly_bd
    rw [show (1 / 2 : ℝ) * ((N : ℝ) / (Real.log (N : ℝ)) ^ D) =
        ((N : ℝ) / 2) / (Real.log (N : ℝ)) ^ D by ring, le_div_iff₀ hlogD_pos]
    have hpi1 : 0 < 1 + Real.pi := by linarith [Real.pi_pos]
    have hlt2 : 8 * (1 + Real.pi) * (Real.log (N : ℝ)) ^ (2 * B + D + 2) < (N : ℝ) := by
      have := mul_lt_mul_of_pos_left hmul (show 0 < 8 * (1 + Real.pi) by positivity)
      have hsimp : 8 * (1 + Real.pi) * (1 / (8 * (1 + Real.pi)) * (N : ℝ)) = (N : ℝ) := by
        field_simp [hpi1.ne']
      linarith
    have hlhs : 4 * (1 + Real.pi) * (Real.log (N : ℝ)) ^ (2 * B) * (Real.log (N : ℝ)) ^ 2 *
        (Real.log (N : ℝ)) ^ D = 4 * (1 + Real.pi) * (Real.log (N : ℝ)) ^ (2 * B + D + 2) := by
      rw [← hpow_comb]; ring
    nlinarith [hlhs]
  linarith

/-! ## Section 3: Exact Singular Integral & Geometric Tail Bound for `v N β` -/

/-- Trivial norm bound `‖v N β‖ ≤ N + 1`. -/
theorem norm_v_le (N : ℕ) (β : ℝ) : ‖v N β‖ ≤ (N : ℝ) + 1 := by
  unfold v
  calc ‖∑ m ∈ Finset.range (N + 1), e ((m : ℝ) * β)‖
      ≤ ∑ m ∈ Finset.range (N + 1), ‖e ((m : ℝ) * β)‖ := norm_sum_le _ _
    _ = (N : ℝ) + 1 := by simp [norm_e]

/-- Geometric-sum bound `‖v N β‖ ≤ 1 / (2 * |β|)` for `0 < |β| ≤ 1 / 2`. -/
theorem norm_v_le_inv_two_abs (N : ℕ) {β : ℝ} (hβ0 : β ≠ 0) (hβ : |β| ≤ 1 / 2) :
    ‖v N β‖ ≤ 1 / (2 * |β|) := by
  have hgeom_eq : v N β * (e β - 1) = e β ^ (N + 1) - 1 := by
    unfold v
    have hterm : ∀ m ∈ Finset.range (N + 1), e ((m : ℝ) * β) = e β ^ m := fun m _ =>
      e_natCast_mul β m
    rw [Finset.sum_congr rfl hterm]
    exact geom_sum_mul (e β) (N + 1)
  have hden_ge : 4 * |β| ≤ ‖e β - 1‖ := four_mul_abs_le_norm_e_sub_one hβ
  have hden_pos : 0 < ‖e β - 1‖ := lt_of_lt_of_le (by positivity : 0 < 4 * |β|) hden_ge
  have hnum_le : ‖e β ^ (N + 1) - 1‖ ≤ 2 := by
    calc ‖e β ^ (N + 1) - 1‖
        ≤ ‖e β ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  have hprod_norm : ‖v N β‖ * ‖e β - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom_eq]; exact hnum_le
  calc ‖v N β‖
      ≤ 2 / ‖e β - 1‖ := (le_div_iff₀ hden_pos).mpr hprod_norm
    _ ≤ 2 / (4 * |β|) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden_ge
    _ = 1 / (2 * |β|) := by ring

/-- Exact combinatorial count of triples `(m₁, m₂, m₃) ∈ [0..n]³` summing to `n`:
`∑_{m₁≤n} ∑_{m₂≤n} ∑_{m₃≤n} (if m₁ + m₂ + m₃ = n then 1 else 0) = (n + 1) * (n + 2) / 2`. -/
private lemma triple_sum_count_nat (n : ℕ) :
    (∑ m₁ ∈ Finset.range (n + 1), ∑ m₂ ∈ Finset.range (n + 1), ∑ m₃ ∈ Finset.range (n + 1),
      if m₁ + m₂ + m₃ = n then (1 : ℝ) else 0) = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
  have hinner : ∀ m₁ ∈ Finset.range (n + 1),
      (∑ m₂ ∈ Finset.range (n + 1), ∑ m₃ ∈ Finset.range (n + 1),
        if m₁ + m₂ + m₃ = n then (1 : ℝ) else 0) = ((n - m₁ : ℕ) : ℝ) + 1 := by
    intro m₁ hm₁
    have hm₁_le : m₁ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm₁)
    have hinner2 : ∀ m₂ ∈ Finset.range (n + 1),
        (∑ m₃ ∈ Finset.range (n + 1), if m₁ + m₂ + m₃ = n then (1 : ℝ) else 0) =
          if m₂ ≤ n - m₁ then (1 : ℝ) else 0 := by
      intro m₂ _
      by_cases hle : m₂ ≤ n - m₁
      · simp only [hle, ↓reduceIte]
        have heq : (∑ m₃ ∈ Finset.range (n + 1), if m₁ + m₂ + m₃ = n then (1 : ℝ) else 0) =
            ∑ m₃ ∈ Finset.range (n + 1), if m₃ = n - m₁ - m₂ then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun m₃ _ => ?_
          have hiff : (m₁ + m₂ + m₃ = n) ↔ (m₃ = n - m₁ - m₂) := by omega
          simp [hiff]
        rw [heq, Finset.sum_ite_eq']
        simp [show n - m₁ - m₂ < n + 1 by omega]
      · simp only [hle, ↓reduceIte]
        refine Finset.sum_eq_zero fun m₃ _ => ?_
        have hne : m₁ + m₂ + m₃ ≠ n := by omega
        simp [hne]
    rw [Finset.sum_congr rfl hinner2, ← Finset.sum_filter]
    have hfilt : (Finset.range (n + 1)).filter (fun m₂ => m₂ ≤ n - m₁) =
        Finset.range (n - m₁ + 1) := by
      ext m₂; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast; ring
  rw [Finset.sum_congr rfl hinner]
  -- Evaluate `∑_{m₁=0}^n ((n - m₁) + 1) = (n + 1)(n + 2) / 2` by induction on `n`
  clear hinner
  induction n with
  | zero => norm_num
  | succ k ih =>
    have hsplit : ∑ m₁ ∈ Finset.range (k + 1 + 1), (((k + 1 - m₁ : ℕ) : ℝ) + 1) =
        (∑ m₁ ∈ Finset.range (k + 1), (((k - m₁ : ℕ) : ℝ) + 1)) + ((k : ℝ) + 2) := by
      rw [Finset.sum_range_succ]
      have h0 : k + 1 - (k + 1) = 0 := Nat.sub_self _
      rw [h0, Nat.cast_zero, zero_add]
      have hterm : ∑ m₁ ∈ Finset.range (k + 1), (((k + 1 - m₁ : ℕ) : ℝ) + 1) =
          (∑ m₁ ∈ Finset.range (k + 1), (((k - m₁ : ℕ) : ℝ) + 1)) + ((k : ℝ) + 1) := by
        have h1 : ∀ m₁ ∈ Finset.range (k + 1),
            (((k + 1 - m₁ : ℕ) : ℝ) + 1) = ((((k - m₁ : ℕ) : ℝ) + 1) + 1) := by
          intro m₁ hm₁
          have hle : m₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm₁)
          rw [show k + 1 - m₁ = (k - m₁) + 1 by omega]
          push_cast; ring
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one]
        push_cast; ring
      linarith
    rw [hsplit, ih]
    push_cast
    ring

/-- **Exact Singular Integral**: `∫_{-1/2}^{1/2} (v n β)^3 e(-n β) dβ = (n + 1)(n + 2) / 2`. -/
theorem singular_integral_exact (n : ℕ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), (v n β) ^ 3 * e (-(n : ℝ) * β) =
      ((((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 : ℝ) : ℂ) := by
  -- Step 1: shift `[-1/2, 1/2]` to `[0, 1]` by 1-periodicity
  have hcont : Continuous (fun β : ℝ => (v n β) ^ 3 * e (-(n : ℝ) * β)) := by
    unfold v; fun_prop
  have hper : ∀ β : ℝ, (v n (β + 1)) ^ 3 * e (-(n : ℝ) * (β + 1)) =
      (v n β) ^ 3 * e (-(n : ℝ) * β) := by
    intro β
    have hv : v n (β + 1) = v n β := by
      unfold v
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_add, mul_one, e_add, e_natCast, mul_one]
    have he : e (-(n : ℝ) * (β + 1)) = e (-(n : ℝ) * β) := by
      rw [show -(n : ℝ) * (β + 1) = -(n : ℝ) * β + ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring,
        e_add, e_intCast, mul_one]
    rw [hv, he]
  have hshift : ∫ β in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), (v n β) ^ 3 * e (-(n : ℝ) * β) =
      ∫ β in (0 : ℝ)..1, (v n β) ^ 3 * e (-(n : ℝ) * β) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have hleft : ∫ β in (-(1 / 2 : ℝ))..0, (v n β) ^ 3 * e (-(n : ℝ) * β) =
        ∫ β in (1 / 2 : ℝ)..1, (v n β) ^ 3 * e (-(n : ℝ) * β) := by
      have h1 := intervalIntegral.integral_comp_add_right
        (fun β => (v n β) ^ 3 * e (-(n : ℝ) * β)) (1 : ℝ) (a := -(1 / 2 : ℝ)) (b := 0)
      have h2 : (∫ β in (-(1 / 2 : ℝ))..0, (v n (β + 1)) ^ 3 * e (-(n : ℝ) * (β + 1))) =
          ∫ β in (-(1 / 2 : ℝ))..0, (v n β) ^ 3 * e (-(n : ℝ) * β) :=
        intervalIntegral.integral_congr fun β _ => hper β
      rw [h2] at h1
      have ha : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
      have hb : (0 : ℝ) + 1 = 1 := by norm_num
      rw [ha, hb] at h1
      exact h1
    rw [hleft, add_comm, intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rw [hshift]
  -- Step 2: expand `(v n β)^3 * e(-n β)` and apply orthogonality
  have hexpand : ∀ β : ℝ, (v n β) ^ 3 * e (-(n : ℝ) * β) =
      ∑ m₁ ∈ Finset.range (n + 1), ∑ m₂ ∈ Finset.range (n + 1), ∑ m₃ ∈ Finset.range (n + 1),
        e ((((m₁ + m₂ + m₃ : ℤ) - n : ℤ) : ℝ) * β) := by
    intro β
    unfold v
    rw [sum_cube_general, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₃ _ => ?_
    rw [← e_add, ← e_add, ← e_add]
    congr 1; push_cast; ring
  simp_rw [hexpand]
  have hint3 : ∀ m₁ m₂ m₃ : ℕ,
      IntervalIntegrable (fun β : ℝ => e ((((m₁ + m₂ + m₃ : ℤ) - n : ℤ) : ℝ) * β)) volume 0 1 :=
    fun m₁ m₂ m₃ => (by fun_prop : Continuous _).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finsetSum fun m₁ _ =>
    intervalIntegrable_sum_fun _ _ fun m₂ _ => intervalIntegrable_sum_fun _ _ fun m₃ _ => hint3 m₁ m₂ m₃]
  have hswap : (∑ m₁ ∈ Finset.range (n + 1),
      ∫ β in (0 : ℝ)..1, ∑ m₂ ∈ Finset.range (n + 1), ∑ m₃ ∈ Finset.range (n + 1),
        e ((((m₁ + m₂ + m₃ : ℤ) - n : ℤ) : ℝ) * β)) =
      ∑ m₁ ∈ Finset.range (n + 1), ∑ m₂ ∈ Finset.range (n + 1), ∑ m₃ ∈ Finset.range (n + 1),
        if m₁ + m₂ + m₃ = n then (1 : ℂ) else 0 := by
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [intervalIntegral.integral_finsetSum fun m₂ _ =>
      intervalIntegrable_sum_fun _ _ fun m₃ _ => hint3 m₁ m₂ m₃]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [intervalIntegral.integral_finsetSum fun m₃ _ => hint3 m₁ m₂ m₃]
    refine Finset.sum_congr rfl fun m₃ _ => ?_
    rw [integral_e_mul_intCast]
    simp only [sum_eq_iff]
  rw [hswap]
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) (triple_sum_count_nat n)
  rw [← hcast]
  push_cast
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
    Finset.sum_congr rfl fun m₃ _ => by split_ifs <;> simp

/-- Tail bound for the singular integral: for `0 < δ ≤ 1/2`,
`‖∫_{-δ}^{δ} (v N β)^3 e(-n β) - ∫_{-1/2}^{1/2} (v N β)^3 e(-n β)‖ ≤ 1 / (8 * δ^2)`. -/
theorem singular_integral_tail_bound (N n : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ‖(∫ β in (-δ)..δ, (v N β) ^ 3 * e (-(n : ℝ) * β)) -
      (∫ β in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), (v N β) ^ 3 * e (-(n : ℝ) * β))‖ ≤
      1 / (8 * δ ^ 2) := by
  set g : ℝ → ℂ := fun β => (v N β) ^ 3 * e (-(n : ℝ) * β)
  have hcont : Continuous g := by dsimp only [g, v]; fun_prop
  have hsplit : (∫ β in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), g β) =
      (∫ β in (-(1 / 2 : ℝ))..(-δ), g β) + (∫ β in (-δ)..δ, g β) +
        (∫ β in δ..(1 / 2 : ℝ), g β) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) (-(1 / 2 : ℝ)) (-δ))
      (hcont.intervalIntegrable (μ := volume) (-δ) δ)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) (-(1 / 2 : ℝ)) δ)
      (hcont.intervalIntegrable (μ := volume) δ (1 / 2 : ℝ))
    rw [← h2, ← h1]
  have hsub : (∫ β in (-δ)..δ, g β) - (∫ β in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), g β) =
      -((∫ β in (-(1 / 2 : ℝ))..(-δ), g β) + (∫ β in δ..(1 / 2 : ℝ), g β)) := by
    rw [hsplit]; ring
  rw [hsub, norm_neg]
  -- Shared bound `∫_δ^{1/2} ‖g β‖ dβ ≤ 1 / (16 δ^2)`
  have hint_norm_bound : ∫ β in δ..(1 / 2 : ℝ), ‖g β‖ ≤ 1 / (16 * δ ^ 2) := by
    have hdom_cont : ContinuousOn (fun β : ℝ => 1 / (8 * β ^ 3)) (Set.uIcc δ (1 / 2 : ℝ)) := by
      rw [Set.uIcc_of_le hδ]
      refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 3)) fun β hβ => ?_
      have hβp : 0 < β := lt_of_lt_of_le hδ0 hβ.1
      positivity
    have hderiv : ∀ β ∈ Set.uIcc δ (1 / 2 : ℝ),
        HasDerivAt (fun x : ℝ => -(1 / (16 * x ^ 2))) (1 / (8 * β ^ 3)) β := by
      intro β hβ
      rw [Set.uIcc_of_le hδ] at hβ
      have hβp : 0 < β := lt_of_lt_of_le hδ0 hβ.1
      have hd1 : HasDerivAt (fun x : ℝ => 16 * x ^ 2) (32 * β) β := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          ((hasDerivAt_pow 2 β).const_mul (16 : ℝ)).congr_deriv (by ring)
      have hd2 := (hd1.inv (by positivity)).neg
      refine (hd2.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp [one_div])).congr_deriv ?_
      field_simp [hβp.ne']; ring
    calc ∫ β in δ..(1 / 2 : ℝ), ‖g β‖
        ≤ ∫ β in δ..(1 / 2 : ℝ), 1 / (8 * β ^ 3) :=
          intervalIntegral.integral_mono_on hδ (hcont.norm.intervalIntegrable _ _)
            hdom_cont.intervalIntegrable (fun β hβ => by
              have hβp : 0 < β := lt_of_lt_of_le hδ0 hβ.1
              have hv := norm_v_le_inv_two_abs N hβp.ne' (by rw [abs_of_pos hβp]; exact hβ.2)
              rw [abs_of_pos hβp] at hv
              have hgn : ‖g β‖ = ‖v N β‖ ^ 3 := by simp [g, norm_pow, norm_e]
              rw [hgn]
              calc ‖v N β‖ ^ 3 ≤ (1 / (2 * β)) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hv 3
                _ = 1 / (8 * β ^ 3) := by ring)
      _ = -(1 / (16 * (1 / 2 : ℝ) ^ 2)) - -(1 / (16 * δ ^ 2)) :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hdom_cont.intervalIntegrable
      _ ≤ 1 / (16 * δ ^ 2) := by norm_num
  have hright_bound : ‖∫ β in δ..(1 / 2 : ℝ), g β‖ ≤ 1 / (16 * δ ^ 2) :=
    (intervalIntegral.norm_integral_le_integral_norm hδ).trans hint_norm_bound
  have hleft_bound : ‖∫ β in (-(1 / 2 : ℝ))..(-δ), g β‖ ≤ 1 / (16 * δ ^ 2) := by
    have href : (∫ β in (-(1 / 2 : ℝ))..(-δ), ‖g β‖) = ∫ β in δ..(1 / 2 : ℝ), ‖g (-β)‖ :=
      (intervalIntegral.integral_comp_neg (fun β => ‖g β‖) (a := δ) (b := 1 / 2)).symm
    have hgn_neg : ∀ β : ℝ, ‖g (-β)‖ = ‖g β‖ := by
      intro β
      have hv_neg : v N (-β) = star (v N β) := by
        unfold v
        rw [star_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [e_star]; congr 1; ring
      have h1 : ‖g (-β)‖ = ‖v N (-β)‖ ^ 3 := by simp [g, norm_pow, norm_e]
      have h2 : ‖g β‖ = ‖v N β‖ ^ 3 := by simp [g, norm_pow, norm_e]
      rw [h1, h2, hv_neg, norm_star]
    calc ‖∫ β in (-(1 / 2 : ℝ))..(-δ), g β‖
        ≤ ∫ β in (-(1 / 2 : ℝ))..(-δ), ‖g β‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ∫ β in δ..(1 / 2 : ℝ), ‖g β‖ := by
          rw [href]; exact intervalIntegral.integral_congr fun β _ => hgn_neg β
      _ ≤ 1 / (16 * δ ^ 2) := hint_norm_bound
  have htri := norm_add_le (∫ β in (-(1 / 2 : ℝ))..(-δ), g β) (∫ β in δ..(1 / 2 : ℝ), g β)
  have hhalf : 1 / (16 * δ ^ 2) + 1 / (16 * δ ^ 2) = 1 / (8 * δ ^ 2) := by ring
  linarith

/-! ## Section 4: Ramanujan Sums, Multiplicativity, Totient Bound & Truncated Singular Series -/

/-- Full roots-of-unity sum for general modulus `m`: `∑_{s < m} e(s n / m) = if m ∣ n then m else 0`. -/
private lemma sum_e_div_general (m n : ℕ) (hm : m ≠ 0) :
    ∑ s ∈ Finset.range m, e (((s : ℝ) * (n : ℝ)) / (m : ℝ)) =
      if m ∣ n then (m : ℂ) else 0 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  by_cases hdvd : m ∣ n
  · simp only [hdvd, ↓reduceIte]
    obtain ⟨k, hk⟩ := hdvd
    have hterm : ∀ s ∈ Finset.range m, e (((s : ℝ) * (n : ℝ)) / (m : ℝ)) = 1 := by
      intro s _
      rw [hk]
      have harg : ((s : ℝ) * ((m * k : ℕ) : ℝ)) / (m : ℝ) = ((s * k : ℕ) : ℝ) := by
        push_cast; field_simp [hm0]
      rw [harg, e_natCast]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · simp only [hdvd, ↓reduceIte]
    set z := e ((n : ℝ) / (m : ℝ))
    have hterm : ∀ s ∈ Finset.range m, e (((s : ℝ) * (n : ℝ)) / (m : ℝ)) = z ^ s := by
      intro s _
      rw [show ((s : ℝ) * (n : ℝ)) / (m : ℝ) = (s : ℝ) * ((n : ℝ) / (m : ℝ)) by ring,
        e_natCast_mul]
    rw [Finset.sum_congr rfl hterm]
    have hzm : z ^ m = 1 := by
      dsimp only [z]
      rw [← e_natCast_mul, show (m : ℝ) * ((n : ℝ) / (m : ℝ)) = (n : ℝ) by field_simp [hm0],
        e_natCast]
    have hz1 : z ≠ 1 := by
      intro h1
      apply hdvd
      rw [e_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have hk0 : 0 ≤ k := by
        have : (0 : ℝ) ≤ (n : ℝ) / (m : ℝ) := by positivity
        rw [hk] at this; exact_mod_cast this
      obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hk0
      refine ⟨r, ?_⟩
      have hnm : (n : ℝ) = (m : ℝ) * (k : ℝ) := by field_simp [hm0] at hk ⊢; linarith
      rw [hr] at hnm
      exact_mod_cast hnm
    have hgeom := geom_sum_mul z m
    rw [hzm, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hz1)

/-- Classical Möbius divisor formula for the Ramanujan sum:
`c_q(n) = ∑_{k ∣ gcd(q, n)} k * μ(q / k)` for `q ≠ 0`. -/
theorem ramanujanSum_eq_sum_moebius (q n : ℕ) (hq : q ≠ 0) :
    ramanujanSum q n =
      ∑ k ∈ (Nat.gcd q n).divisors, (k : ℂ) * (ArithmeticFunction.moebius (q / k) : ℂ) := by
  simp only [ramanujanSum]
  have hexpand : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
      e (((r : ℝ) * n) / q) =
      ∑ r ∈ Finset.range q, (∑ d ∈ (Nat.gcd r q).divisors,
        (ArithmeticFunction.moebius d : ℂ)) * e (((r : ℝ) * n) / q) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hite : ite (Nat.Coprime r q) (e (((r : ℝ) * n) / q)) 0 =
        ite (Nat.Coprime r q) (1 : ℂ) 0 * e (((r : ℝ) * n) / q) := by split_ifs <;> simp
    rw [hite, coprime_indicator_moebius r q hq]
  rw [hexpand]
  have hswap : ∑ r ∈ Finset.range q, (∑ d ∈ (Nat.gcd r q).divisors,
      (ArithmeticFunction.moebius d : ℂ)) * e (((r : ℝ) * n) / q) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e (((r : ℝ) * n) / q) := by
    have h1 : ∑ r ∈ Finset.range q, (∑ d ∈ (Nat.gcd r q).divisors,
        (ArithmeticFunction.moebius d : ℂ)) * e (((r : ℝ) * n) / q) =
        ∑ r ∈ Finset.range q, ∑ d ∈ q.divisors.filter (fun d => d ∣ r),
          (ArithmeticFunction.moebius d : ℂ) * e (((r : ℝ) * n) / q) := by
      refine Finset.sum_congr rfl fun r _ => by rw [divisors_gcd_eq_filter r q hq, ← Finset.sum_mul]
    rw [h1]
    have h2 : ∑ r ∈ Finset.range q, ∑ d ∈ q.divisors.filter (fun d => d ∣ r),
        (ArithmeticFunction.moebius d : ℂ) * e (((r : ℝ) * n) / q) =
        ∑ r ∈ Finset.range q, ∑ d ∈ q.divisors,
          ite (d ∣ r) ((ArithmeticFunction.moebius d : ℂ) * e (((r : ℝ) * n) / q)) 0 := by
      refine Finset.sum_congr rfl fun r _ => by rw [Finset.sum_filter]
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => by rw [← Finset.sum_filter, Finset.mul_sum]
  rw [hswap]
  have hinner : ∀ d ∈ q.divisors,
      ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e (((r : ℝ) * n) / q) =
        if (q / d) ∣ n then ((q / d : ℕ) : ℂ) else 0 := by
    intro d hd
    have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)
    have hqdnz : q / d ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd) hdpos; omega
    rw [sum_filter_dvd_reindex q d hdvd hdpos]
    have hrew : ∑ s ∈ Finset.range (q / d), e ((((d * s : ℕ) : ℝ) * n) / q) =
        ∑ s ∈ Finset.range (q / d), e (((s : ℝ) * n) / ((q / d : ℕ) : ℝ)) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      have hqeq : (q : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [hqeq]; field_simp [hdpos.ne', hqdnz]; push_cast; ring
    rw [hrew, sum_e_div_general (q / d) n hqdnz]
  rw [Finset.sum_congr rfl fun d hd => by rw [hinner d hd]]
  -- Reindex `d ↦ k = q / d`
  have hfilt : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
      (if (q / d) ∣ n then ((q / d : ℕ) : ℂ) else 0) =
      ∑ d ∈ q.divisors.filter (fun d => (q / d) ∣ n),
        ((q / d : ℕ) : ℂ) * (ArithmeticFunction.moebius d : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
  rw [hfilt]
  refine Finset.sum_bij (fun d _ => q / d) ?_ ?_ ?_ ?_
  · intro d hd
    have hdq : d ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hqdn : (q / d) ∣ n := (Finset.mem_filter.mp hd).2
    rw [Nat.mem_divisors]
    refine ⟨Nat.dvd_gcd (Nat.div_dvd_of_dvd hdq) hqdn, ?_⟩
    exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hq))
  · intro d₁ hd₁ d₂ hd₂ heq
    have h1 : d₁ ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd₁).1).1
    have h2 : d₂ ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd₂).1).1
    have hq1 : d₁ * (q / d₁) = q := Nat.mul_div_cancel' h1
    have hq2 : d₂ * (q / d₂) = q := Nat.mul_div_cancel' h2
    have hpos : 0 < q / d₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) h1)
      (Nat.pos_of_dvd_of_pos h1 (Nat.pos_of_ne_zero hq))
    rw [← heq] at hq2
    exact Nat.eq_of_mul_eq_mul_right hpos (hq1.trans hq2.symm)
  · intro k hk
    have hkg : k ∣ Nat.gcd q n := (Nat.mem_divisors.mp hk).1
    have hkq : k ∣ q := Nat.dvd_trans hkg (Nat.gcd_dvd_left q n)
    have hkn : k ∣ n := Nat.dvd_trans hkg (Nat.gcd_dvd_right q n)
    have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hkq (Nat.pos_of_ne_zero hq)
    have hqdk : q / (q / k) = k := Nat.div_div_self hkq hq
    refine ⟨q / k, ?_, hqdk⟩
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.div_dvd_of_dvd hkq, hq⟩, by rwa [hqdk]⟩
  · intro d hd
    have hdq : d ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    rw [Nat.div_div_self hdq hq]

/-- `ramanujanSum q n` is real (an integer cast to `ℂ`). -/
theorem ramanujanSum_eq_ofReal (q n : ℕ) (hq : q ≠ 0) :
    ramanujanSum q n = ((ramanujanSum q n).re : ℂ) := by
  rw [ramanujanSum_eq_sum_moebius q n hq]
  have h : (∑ k ∈ (Nat.gcd q n).divisors, (k : ℂ) * (ArithmeticFunction.moebius (q / k) : ℂ)) =
      (((∑ k ∈ (Nat.gcd q n).divisors, (k : ℝ) * (ArithmeticFunction.moebius (q / k) : ℝ)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h, Complex.ofReal_re]

/-- The negative-phase Ramanujan sum equals `ramanujanSum q n` (since it is real). -/
theorem sum_e_neg_div_eq_ramanujanSum (q n : ℕ) (hq : q ≠ 0) :
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      e (-((a : ℝ) * (n : ℝ)) / (q : ℝ)) = ramanujanSum q n := by
  have hstar : ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      e (-((a : ℝ) * (n : ℝ)) / (q : ℝ)) = star (ramanujanSum q n) := by
    unfold ramanujanSum
    rw [star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [e_star]; congr 1; ring
  rw [hstar, ramanujanSum_eq_ofReal q n hq]
  simp

/-- Multiplicativity of `ramanujanSum · n` for coprime moduli `q₁, q₂`. -/
theorem ramanujanSum_mul_of_coprime {q₁ q₂ : ℕ} (n : ℕ) (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hcop : Nat.Coprime q₁ q₂) :
    ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n := by
  rw [ramanujanSum_eq_sum_moebius (q₁ * q₂) n (mul_ne_zero hq₁ hq₂),
    ramanujanSum_eq_sum_moebius q₁ n hq₁, ramanujanSum_eq_sum_moebius q₂ n hq₂]
  have hgcd : Nat.gcd (q₁ * q₂) n = Nat.gcd q₁ n * Nat.gcd q₂ n := by
    rw [Nat.gcd_comm, Nat.gcd_comm q₁ n, Nat.gcd_comm q₂ n]
    exact hcop.gcd_mul n
  have hcop_g : Nat.Coprime (Nat.gcd q₁ n) (Nat.gcd q₂ n) :=
    hcop.coprime_dvd_left (Nat.gcd_dvd_left q₁ n) |>.coprime_dvd_right (Nat.gcd_dvd_left q₂ n)
  rw [hgcd, Finset.sum_mul_sum]
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2)
      ((Nat.gcd q₁ n).divisors ×ˢ (Nat.gcd q₂ n).divisors : Finset (ℕ × ℕ)) := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    have ha₁ : a₁ ∣ Nat.gcd q₁ n := (Nat.mem_divisors.mp (Finset.mem_product.mp h₁).1).1
    have hb₁ : b₁ ∣ Nat.gcd q₂ n := (Nat.mem_divisors.mp (Finset.mem_product.mp h₁).2).1
    have ha₂ : a₂ ∣ Nat.gcd q₁ n := (Nat.mem_divisors.mp (Finset.mem_product.mp h₂).1).1
    have hb₂ : b₂ ∣ Nat.gcd q₂ n := (Nat.mem_divisors.mp (Finset.mem_product.mp h₂).2).1
    have hc₁₂ : Nat.Coprime a₁ b₂ := hcop_g.coprime_dvd_left ha₁ |>.coprime_dvd_right hb₂
    have hc₂₁ : Nat.Coprime a₂ b₁ := hcop_g.coprime_dvd_left ha₂ |>.coprime_dvd_right hb₁
    dsimp only at heq
    have ha_eq : a₁ = a₂ := Nat.dvd_antisymm
      (hc₁₂.dvd_of_dvd_mul_right ⟨b₁, heq.symm⟩)
      (hc₂₁.dvd_of_dvd_mul_right ⟨b₂, heq⟩)
    have hb_eq : b₁ = b₂ := Nat.dvd_antisymm
      (hc₂₁.symm.dvd_of_dvd_mul_left ⟨a₁, heq.symm.trans (mul_comm a₁ b₁)⟩)
      (hc₁₂.symm.dvd_of_dvd_mul_left ⟨a₂, heq.trans (mul_comm a₂ b₂)⟩)
    exact Prod.ext ha_eq hb_eq
  have himg : (Nat.gcd q₁ n * Nat.gcd q₂ n).divisors =
      ((Nat.gcd q₁ n).divisors ×ˢ (Nat.gcd q₂ n).divisors).image (fun x => x.1 * x.2) := by
    have hg₁_ne : Nat.gcd q₁ n ≠ 0 :=
      Nat.ne_of_gt (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hq₁))
    have hg₂_ne : Nat.gcd q₂ n ≠ 0 :=
      Nat.ne_of_gt (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hq₂))
    ext k
    simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨hk, _⟩
      refine ⟨(Nat.gcd k (Nat.gcd q₁ n), Nat.gcd k (Nat.gcd q₂ n)),
        ⟨⟨Nat.gcd_dvd_right _ _, hg₁_ne⟩, ⟨Nat.gcd_dvd_right _ _, hg₂_ne⟩⟩, ?_⟩
      dsimp only
      rw [← hcop_g.gcd_mul k, Nat.gcd_eq_left hk]
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, _⟩, ⟨hb, _⟩⟩, rfl⟩
      exact ⟨mul_dvd_mul ha hb, mul_ne_zero hg₁_ne hg₂_ne⟩
  rw [himg, Finset.sum_image hinj, Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have haq : a ∣ q₁ := Nat.dvd_trans (Nat.mem_divisors.mp ha).1 (Nat.gcd_dvd_left q₁ n)
  have hbq : b ∣ q₂ := Nat.dvd_trans (Nat.mem_divisors.mp hb).1 (Nat.gcd_dvd_left q₂ n)
  have hdiv : (q₁ * q₂) / (a * b) = (q₁ / a) * (q₂ / b) := Nat.mul_div_mul_comm haq hbq
  have hcop_div : Nat.Coprime (q₁ / a) (q₂ / b) :=
    hcop.coprime_dvd_left (Nat.div_dvd_of_dvd haq) |>.coprime_dvd_right (Nat.div_dvd_of_dvd hbq)
  rw [hdiv, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_div]
  push_cast
  ring

/-- The real singular-series summand `(μ(q) / φ(q))^3 * c_q(n)`. -/
def singularTerm (q n : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ)) ^ 3) * (ramanujanSum q n).re

lemma singularTerm_one (n : ℕ) : singularTerm 1 n = 1 := by
  unfold singularTerm ramanujanSum
  have h : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  rw [h, Finset.sum_singleton]
  simp [e]

lemma singularTerm_eq_zero_of_not_squarefree {q : ℕ} (n : ℕ) (h : ¬ Squarefree q) :
    singularTerm q n = 0 := by
  unfold singularTerm
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  simp

lemma singularTerm_mul_of_coprime {q₁ q₂ : ℕ} (n : ℕ) (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hcop : Nat.Coprime q₁ q₂) :
    singularTerm (q₁ * q₂) n = singularTerm q₁ n * singularTerm q₂ n := by
  unfold singularTerm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    Nat.totient_mul hcop, ramanujanSum_mul_of_coprime n hq₁ hq₂ hcop]
  have hre : (ramanujanSum q₁ n * ramanujanSum q₂ n).re =
      (ramanujanSum q₁ n).re * (ramanujanSum q₂ n).re := by
    conv_lhs => rw [ramanujanSum_eq_ofReal q₁ n hq₁, ramanujanSum_eq_ofReal q₂ n hq₂]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  push_cast
  ring

lemma one_add_singularTerm_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    1 + singularTerm p n = singularLocalFactor p n := by
  have : Fact p.Prime := ⟨hp⟩
  unfold singularTerm singularLocalFactor
  rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp, ramanujanSum_prime p n]
  have hphi : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    simpa using Nat.cast_sub (R := ℝ) hp.one_lt.le
  rw [hphi]
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  split_ifs with hdvd
  · have hre : ((p : ℂ) - 1).re = (p : ℝ) - 1 := by simp
    rw [hre]; push_cast; field_simp [hpm1]; ring
  · have hre : (-1 : ℂ).re = -1 := by simp
    rw [hre]; push_cast; field_simp [hpm1]; ring

/-- Key uniform bound: `|singularTerm q n| ≤ 1 / φ(q)^2` for all `q ≥ 1` and all `n`. -/
theorem abs_singularTerm_le_inv_totient_sq {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    |singularTerm q n| ≤ 1 / (q.totient : ℝ) ^ 2 := by
  by_cases hsf : Squarefree q
  · set g := Nat.gcd q n
    set r := q / g
    have hg_dvd_q : g ∣ q := Nat.gcd_dvd_left q n
    have hg_dvd_n : g ∣ n := Nat.gcd_dvd_right q n
    have hq_eq : q = g * r := (Nat.mul_div_cancel' hg_dvd_q).symm
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hq)
    have hr_pos : 0 < r := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hg_dvd_q) hg_pos
    have hcop_gr : Nat.Coprime g r := by
      rw [Nat.coprime_iff_gcd_eq_one]
      set d := Nat.gcd g r
      have hd2 : d * d ∣ q := by
        rw [hq_eq]
        exact mul_dvd_mul (Nat.gcd_dvd_left g r) (Nat.gcd_dvd_right g r)
      have hunit : IsUnit d := hsf d hd2
      exact Nat.isUnit_iff.mp hunit
    have hcop_rn : Nat.Coprime r n := by
      rw [Nat.coprime_iff_gcd_eq_one]
      set d := Nat.gcd r n
      have hd_r : d ∣ r := Nat.gcd_dvd_left r n
      have hd_n : d ∣ n := Nat.gcd_dvd_right r n
      have hcop_gd : Nat.Coprime g d := hcop_gr.coprime_dvd_right hd_r
      have hgd_q : g * d ∣ q := by rw [hq_eq]; exact mul_dvd_mul_left g hd_r
      have hgd_n : g * d ∣ n := hcop_gd.mul_dvd_of_dvd_of_dvd hg_dvd_n hd_n
      have hgd_g : g * d ∣ g := Nat.dvd_gcd hgd_q hgd_n
      have hd_dvd_1 : d ∣ 1 := by
        obtain ⟨k, hk⟩ := hgd_g
        refine ⟨k, ?_⟩
        have : g * 1 = g * (d * k) := by linarith
        exact Nat.eq_of_mul_eq_mul_left hg_pos this
      exact Nat.dvd_one.mp hd_dvd_1
    have hram_q : ramanujanSum q n = ramanujanSum g n * ramanujanSum r n := by
      conv_lhs => rw [hq_eq]
      exact ramanujanSum_mul_of_coprime n hg_pos.ne' hr_pos.ne' hcop_gr
    have hram_g : ramanujanSum g n = (g.totient : ℂ) := by
      unfold ramanujanSum
      obtain ⟨k, hk⟩ := hg_dvd_n
      have hterm : ∀ a ∈ (Finset.range g).filter (fun a => Nat.Coprime a g),
          e (((a : ℝ) * (n : ℝ)) / (g : ℝ)) = 1 := by
        intro a _
        rw [hk]
        have harg : ((a : ℝ) * ((g * k : ℕ) : ℝ)) / (g : ℝ) = ((a * k : ℕ) : ℝ) := by
          push_cast; field_simp [hg_pos.ne']
        rw [harg, e_natCast]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      rw [Nat.totient_eq_card_coprime]
      congr 1; ext a; simp [Nat.coprime_comm]
    have hram_r : ramanujanSum r n = (ArithmeticFunction.moebius r : ℂ) :=
      ramanujanSum_eq_moebius_of_coprime r n hr_pos.ne' hcop_rn.symm
    have hram_abs : |(ramanujanSum q n).re| ≤ (g.totient : ℝ) := by
      calc |(ramanujanSum q n).re|
          ≤ ‖ramanujanSum q n‖ := Complex.abs_re_le_norm _
        _ = ‖(g.totient : ℂ)‖ * ‖(ArithmeticFunction.moebius r : ℂ)‖ := by
            rw [hram_q, hram_g, hram_r, norm_mul]
        _ ≤ (g.totient : ℝ) * 1 := by
            rw [Complex.norm_natCast, Complex.norm_intCast]
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            by_cases hsf_r : Squarefree r
            · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf_r]; simp
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf_r]; simp
        _ = (g.totient : ℝ) := mul_one _
    have hmu_le : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]; simp
    have hphi_q : (q.totient : ℝ) = (g.totient : ℝ) * (r.totient : ℝ) := by
      conv_lhs => rw [hq_eq]
      rw [Nat.totient_mul hcop_gr]; push_cast; rfl
    have hphi_g_pos : (0 : ℝ) < (g.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hg_pos
    have hphi_r_ge1 : (1 : ℝ) ≤ (r.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hr_pos
    unfold singularTerm
    rw [abs_mul, abs_pow, abs_div,
      show |(q.totient : ℝ)| = (q.totient : ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
    calc (|(ArithmeticFunction.moebius q : ℝ)| / (q.totient : ℝ)) ^ 3 * |(ramanujanSum q n).re|
        ≤ (1 / (q.totient : ℝ)) ^ 3 * (g.totient : ℝ) := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity)
            (div_le_div_of_nonneg_right hmu_le (Nat.cast_nonneg _)) 3)
            hram_abs (abs_nonneg _) (by positivity)
      _ = 1 / ((g.totient : ℝ) ^ 2 * (r.totient : ℝ) ^ 3) := by
          rw [hphi_q]; field_simp [hphi_g_pos.ne', (show (0 : ℝ) < (r.totient : ℝ) by linarith).ne']
      _ ≤ 1 / ((g.totient : ℝ) ^ 2 * (r.totient : ℝ) ^ 2) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          have hr3 : (r.totient : ℝ) ^ 2 ≤ (r.totient : ℝ) ^ 3 := by nlinarith
          exact mul_le_mul_of_nonneg_left hr3 (sq_nonneg _)
      _ = 1 / (q.totient : ℝ) ^ 2 := by rw [hphi_q]; ring
  · rw [singularTerm_eq_zero_of_not_squarefree n hsf, abs_zero]
    positivity

/-- Elementary prime-power inequality for `q^3 ≤ 16 * φ(q)^4`. -/
private def totientWeight (q : ℕ) : ℕ :=
  (if 2 ∣ q then 8 else 1) * (if 3 ∣ q then 2 else 1)

private lemma totientWeight_le_16 (q : ℕ) : totientWeight q ≤ 16 := by
  unfold totientWeight
  split_ifs <;> omega

private lemma prime_pow_cube_le_totient_pow4 {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (p ^ k) ^ 3 ≤ (if p = 2 then 8 else if p = 3 then 2 else 1) * ((p ^ k).totient) ^ 4 := by
  rw [Nat.totient_prime_pow hp (by omega : 0 < k)]
  have hpow : (p ^ k) ^ 3 = p ^ (3 * k) := by rw [← pow_mul]; ring_nf
  have htot4 : (p ^ (k - 1) * (p - 1)) ^ 4 = p ^ (4 * (k - 1)) * (p - 1) ^ 4 := by
    rw [mul_pow, ← pow_mul]; ring_nf
  rw [hpow, htot4]
  by_cases hp2 : p = 2
  · subst hp2
    simp only [↓reduceIte]
    have h1 : (2 - 1 : ℕ) ^ 4 = 1 := by norm_num
    rw [h1, mul_one, show 8 * 2 ^ (4 * (k - 1)) = 2 ^ (3 + 4 * (k - 1)) by rw [pow_add]; norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · by_cases hp3 : p = 3
    · subst hp3
      simp only [hp2, ↓reduceIte]
      have h1 : 2 * (3 ^ (4 * (k - 1)) * (3 - 1) ^ 4) = 32 * 3 ^ (4 * (k - 1)) := by ring
      rw [h1]
      have hsplit : 3 ^ (3 * k) = 27 * 3 ^ (3 * (k - 1)) := by
        rw [show 3 * k = 3 + 3 * (k - 1) by omega, pow_add]; norm_num
      rw [hsplit]
      exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
    · simp only [hp2, hp3, ↓reduceIte, one_mul]
      have hp4 : p ≠ 4 := fun h => by subst h; norm_num at hp
      have hp5 : 5 ≤ p := by have := hp.two_le; omega
      have hcube : p ^ 3 ≤ (p - 1) ^ 4 := by
        obtain ⟨t, rfl⟩ : ∃ t, p = t + 5 := ⟨p - 5, by omega⟩
        have hsub : t + 5 - 1 = t + 4 := by omega
        rw [hsub]
        have hdiff : (t + 4) ^ 4 = (t + 5) ^ 3 + (t ^ 4 + 15 * t ^ 3 + 81 * t ^ 2 + 181 * t + 131) := by
          ring
        omega
      have hsplit : p ^ (3 * k) = p ^ (3 * (k - 1)) * p ^ 3 := by
        rw [← pow_add, show 3 * (k - 1) + 3 = 3 * k by omega]
      rw [hsplit]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right hp.pos (by omega)) hcube

private lemma cube_le_totientWeight_mul_totient_pow4 :
    ∀ q : ℕ, 1 ≤ q → q ^ 3 ≤ totientWeight q * q.totient ^ 4 := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq1
    by_cases h1 : q = 1
    · subst h1; unfold totientWeight; norm_num
    · obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd h1
      set k := q.factorization p
      have hk : 1 ≤ k := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpq
      have hpk_dvd : p ^ k ∣ q := Nat.ordProj_dvd q p
      set m := q / p ^ k
      have hq_eq : q = p ^ k * m := (Nat.mul_div_cancel' hpk_dvd).symm
      have hm_pos : 1 ≤ m := Nat.div_pos (Nat.le_of_dvd (by omega) hpk_dvd) (pow_pos hp.pos k)
      have hpk_gt1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
      have hm_lt : m < q := by
        calc m = 1 * m := (one_mul m).symm
          _ < p ^ k * m := Nat.mul_lt_mul_of_pos_right hpk_gt1 (by omega)
          _ = q := hq_eq.symm
      have hnot_pm : ¬ p ∣ m := by
        intro hpm
        have h1' : p ^ (k + 1) ∣ q := by
          rw [hq_eq, pow_succ]
          exact mul_dvd_mul_left (p ^ k) hpm
        have hle := (hp.pow_dvd_iff_le_factorization (by omega)).mp h1'
        omega
      have hcop : Nat.Coprime (p ^ k) m :=
        (hp.coprime_iff_not_dvd.mpr hnot_pm).pow_left k
      have hih := ih m hm_lt hm_pos
      have hpk := prime_pow_cube_le_totient_pow4 hp hk
      have hwt : (if p = 2 then 8 else if p = 3 then 2 else 1) * totientWeight m =
          totientWeight q := by
        have hdvd2 : (2 ∣ q) ↔ (p = 2 ∨ 2 ∣ m) := by
          rw [hq_eq, Nat.prime_two.dvd_mul]
          constructor
          · rintro (h | h)
            · left; exact (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
                (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h) |>.symm
            · exact Or.inr h
          · rintro (rfl | h)
            · exact Or.inl (dvd_pow_self 2 (by omega))
            · exact Or.inr h
        have hdvd3 : (3 ∣ q) ↔ (p = 3 ∨ 3 ∣ m) := by
          rw [hq_eq, Nat.prime_three.dvd_mul]
          constructor
          · rintro (h | h)
            · left; exact (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
                (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) |>.symm
            · exact Or.inr h
          · rintro (rfl | h)
            · exact Or.inl (dvd_pow_self 3 (by omega))
            · exact Or.inr h
        unfold totientWeight
        by_cases hp2 : p = 2
        · subst hp2
          have h2q : 2 ∣ q := hdvd2.mpr (Or.inl rfl)
          have h3iff : (3 ∣ q) ↔ (3 ∣ m) := by simp [hdvd3]
          simp only [↓reduceIte, h2q, hnot_pm, h3iff]
          ring
        · by_cases hp3 : p = 3
          · subst hp3
            have h3q : 3 ∣ q := hdvd3.mpr (Or.inl rfl)
            have h2iff : (2 ∣ q) ↔ (2 ∣ m) := by simp [hdvd2]
            simp only [hp2, ↓reduceIte, h3q, hnot_pm, h2iff]
            ring
          · have h2iff : (2 ∣ q) ↔ (2 ∣ m) := by simp [hdvd2, hp2]
            have h3iff : (3 ∣ q) ↔ (3 ∣ m) := by simp [hdvd3, hp3]
            simp only [hp2, hp3, ↓reduceIte, h2iff, h3iff]
            ring
      calc q ^ 3 = (p ^ k) ^ 3 * m ^ 3 := by rw [hq_eq, mul_pow]
        _ ≤ ((if p = 2 then 8 else if p = 3 then 2 else 1) * (p ^ k).totient ^ 4) *
              (totientWeight m * m.totient ^ 4) := Nat.mul_le_mul hpk hih
        _ = ((if p = 2 then 8 else if p = 3 then 2 else 1) * totientWeight m) *
              ((p ^ k).totient * m.totient) ^ 4 := by ring
        _ = totientWeight q * q.totient ^ 4 := by
            rw [hwt, ← Nat.totient_mul hcop, ← hq_eq]

/-- **Exact Elementary Totient Lower Bound**: `q^3 ≤ 16 * φ(q)^4` for all `q : ℕ`. -/
theorem cube_le_sixteen_mul_totient_pow4 (q : ℕ) : q ^ 3 ≤ 16 * q.totient ^ 4 := by
  by_cases h0 : q = 0
  · subst h0; norm_num
  · calc q ^ 3 ≤ totientWeight q * q.totient ^ 4 :=
          cube_le_totientWeight_mul_totient_pow4 q (by omega)
      _ ≤ 16 * q.totient ^ 4 := Nat.mul_le_mul_right _ (totientWeight_le_16 q)

/-- Corollary: `1 / φ(q)^2 ≤ 4 / (q * √q)` for all `q ≥ 1`. -/
theorem inv_totient_sq_le_four_div_mul_sqrt {q : ℕ} (hq : 1 ≤ q) :
    1 / (q.totient : ℝ) ^ 2 ≤ 4 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hnat : ((q : ℝ) ^ 3) ≤ 16 * (q.totient : ℝ) ^ 4 := by
    exact_mod_cast cube_le_sixteen_mul_totient_pow4 q
  have hsq : ((q : ℝ) * Real.sqrt (q : ℝ)) ^ 2 ≤ (4 * (q.totient : ℝ) ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hqpos.le]
    nlinarith
  have hle : (q : ℝ) * Real.sqrt (q : ℝ) ≤ 4 * (q.totient : ℝ) ^ 2 := by
    nlinarith [mul_pos hqpos (Real.sqrt_pos.mpr hqpos), pow_pos hphi_pos 2]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Telescoping bound: `∑_{q ∈ Ioc M R} 1 / (q * √q) ≤ 2 / √M` for all `1 ≤ M`. -/
private lemma sum_Ioc_inv_mul_sqrt_le {M : ℕ} (hM : 1 ≤ M) (R : ℕ) :
    ∑ q ∈ Finset.Ioc M R, 1 / ((q : ℝ) * Real.sqrt (q : ℝ)) ≤ 2 / Real.sqrt (M : ℝ) := by
  have hstrong : ∀ R : ℕ, M ≤ R →
      ∑ q ∈ Finset.Ioc M R, 1 / ((q : ℝ) * Real.sqrt (q : ℝ)) ≤
        2 / Real.sqrt (M : ℝ) - 2 / Real.sqrt (R : ℝ) := by
    intro R hMR
    induction R, hMR using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have hIoc : Finset.Ioc M (k + 1) = insert (k + 1) (Finset.Ioc M k) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      rw [hIoc, Finset.sum_insert (by simp)]
      have hstep : 1 / (((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)) ≤
          2 / Real.sqrt (k : ℝ) - 2 / Real.sqrt ((k + 1 : ℕ) : ℝ) := by
        set a := Real.sqrt (k : ℝ)
        set b := Real.sqrt ((k + 1 : ℕ) : ℝ)
        have ha : 0 < a := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
        have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
        have ha_le_b : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
        have hba : b ^ 2 - a ^ 2 = 1 := by
          rw [Real.sq_sqrt (Nat.cast_nonneg k), Real.sq_sqrt (Nat.cast_nonneg (k + 1))]
          push_cast; ring
        have hdiff : 2 / a - 2 / b = 2 / (a * b * (a + b)) := by
          have hab : a + b ≠ 0 := by linarith
          field_simp [ha.ne', hb.ne', hab]
          nlinarith [hba]
        rw [hdiff, show ((k + 1 : ℕ) : ℝ) * b = b ^ 3 by
          rw [show ((k + 1 : ℕ) : ℝ) = b ^ 2 from (Real.sq_sqrt (Nat.cast_nonneg (k + 1))).symm]; ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right ha_le_b hb.le]
      linarith
  by_cases hMR : M ≤ R
  · have h := hstrong R hMR
    have : 0 ≤ 2 / Real.sqrt (R : ℝ) := by positivity
    linarith
  · have hemp : Finset.Ioc M R = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    positivity

/-- Finite Euler-product expansion over `primesUpTo M`:
`∏_{p ≤ M} singularLocalFactor p n = ∑_{t ∈ (primesUpTo M).powerset} singularTerm (∏_{p ∈ t} p) n`. -/
private lemma prod_singularLocalFactor_eq_sum_powerset (M n : ℕ) :
    ∏ p ∈ primesUpTo M, singularLocalFactor p n =
      ∑ t ∈ (primesUpTo M).powerset, singularTerm (∏ p ∈ t, p) n := by
  have h1 : ∏ p ∈ primesUpTo M, singularLocalFactor p n =
      ∏ p ∈ primesUpTo M, (1 + singularTerm p n) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    exact (one_add_singularTerm_prime (Finset.mem_filter.mp hp).2 n).symm
  rw [h1, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hprime_t : ∀ p ∈ t, p.Prime := fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_powerset.mp ht hp)).2
  clear ht h1
  induction t using Finset.induction_on with
  | empty => simp [singularTerm_one]
  | insert p s hps ih =>
    have hp : p.Prime := hprime_t p (Finset.mem_insert_self p s)
    have hs : ∀ r ∈ s, r.Prime := fun r hr => hprime_t r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hps, Finset.prod_insert hps, ih hs]
    have hs_ne : (∏ r ∈ s, r) ≠ 0 := by
      intro h0
      obtain ⟨r, hr, hr0⟩ := Finset.prod_eq_zero_iff.mp h0
      exact (hs r hr).ne_zero hr0
    have hcop : Nat.Coprime p (∏ r ∈ s, r) := by
      refine Nat.Coprime.prod_right fun r hr => ?_
      have hrp := hs r hr
      have hne : p ≠ r := fun heq => hps (heq ▸ hr)
      exact (Nat.coprime_primes hp hrp).mpr hne
    exact (singularTerm_mul_of_coprime n hp.ne_zero hs_ne hcop).symm

/-- Injectivity of `t ↦ ∏ p ∈ t, p` on subsets of primes. -/
private lemma prod_primes_injOn (M : ℕ) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) ((primesUpTo M).powerset : Set (Finset ℕ)) := by
  intro t₁ ht₁ t₂ ht₂ heq
  have hp₁ : ∀ p ∈ t₁, p.Prime := fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_powerset.mp ht₁ hp)).2
  have hp₂ : ∀ p ∈ t₂, p.Prime := fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_powerset.mp ht₂ hp)).2
  dsimp only at heq
  ext p
  constructor
  · intro hp
    have hdvd : p ∣ ∏ r ∈ t₂, r := by rw [← heq]; exact Finset.dvd_prod_of_mem _ hp
    obtain ⟨r, hr, hpr⟩ := (hp₁ p hp).prime.dvd_finsetProd_iff _ |>.mp hdvd
    have hEq : p = r := (Nat.prime_dvd_prime_iff_eq (hp₁ p hp) (hp₂ r hr)).mp hpr
    exact hEq ▸ hr
  · intro hp
    have hdvd : p ∣ ∏ r ∈ t₁, r := by rw [heq]; exact Finset.dvd_prod_of_mem _ hp
    obtain ⟨r, hr, hpr⟩ := (hp₂ p hp).prime.dvd_finsetProd_iff _ |>.mp hdvd
    have hEq : p = r := (Nat.prime_dvd_prime_iff_eq (hp₂ p hp) (hp₁ r hr)).mp hpr
    exact hEq ▸ hr

/-- Product of distinct primes is squarefree and `≥ 1`. -/
private lemma squarefree_prod_of_primes {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) ∧ 1 ≤ ∏ p ∈ t, p := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    have hp : p.Prime := ht p (Finset.mem_insert_self p s)
    have hs : ∀ r ∈ s, r.Prime := fun r hr => ht r (Finset.mem_insert_of_mem hr)
    obtain ⟨hsf, hpos⟩ := ih hs
    rw [Finset.prod_insert hps]
    have hcop : Nat.Coprime p (∏ r ∈ s, r) := by
      refine Nat.Coprime.prod_right fun r hr =>
        (Nat.coprime_primes hp (hs r hr)).mpr (fun heq => hps (heq ▸ hr))
    refine ⟨(Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hsf⟩, ?_⟩
    exact Nat.mul_pos hp.pos hpos

/-- **Truncated Singular Series Lower Bound**: for all `Odd n` and `M ≥ 2`,
`2 * (2 - π² / 6) - 8 / √M ≤ ∑_{q = 1}^M singularTerm q n`. -/
theorem truncated_singular_series_lower_bound {n : ℕ} (hn : Odd n) {M : ℕ} (hM : 2 ≤ M) :
    2 * (2 - Real.pi ^ 2 / 6) - 8 / Real.sqrt (M : ℝ) ≤
      ∑ q ∈ Finset.Icc 1 M, singularTerm q n := by
  set B := (primesUpTo M).powerset.image (fun t => ∏ p ∈ t, p)
  set A_sf := (Finset.Icc 1 M).filter Squarefree
  have hprod_eq : ∏ p ∈ primesUpTo M, singularLocalFactor p n = ∑ q ∈ B, singularTerm q n := by
    rw [prod_singularLocalFactor_eq_sum_powerset, Finset.sum_image (prod_primes_injOn M)]
  have hA_eq : ∑ q ∈ Finset.Icc 1 M, singularTerm q n = ∑ q ∈ A_sf, singularTerm q n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hsf : Squarefree q
    · simp [hsf]
    · simp [hsf, singularTerm_eq_zero_of_not_squarefree n hsf]
  have hsub : A_sf ⊆ B := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    have hqM : q ≤ M := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
    have hsf : Squarefree q := (Finset.mem_filter.mp hq).2
    rw [Finset.mem_image]
    refine ⟨q.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hsf⟩
    rw [Finset.mem_powerset]
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hp_le : p ≤ M := (Nat.le_of_dvd (by omega) hp_dvd).trans hqM
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hp_le), hp_prime⟩
  have hdiff : (∏ p ∈ primesUpTo M, singularLocalFactor p n) -
      (∑ q ∈ Finset.Icc 1 M, singularTerm q n) =
      ∑ q ∈ B \ A_sf, singularTerm q n := by
    rw [hprod_eq, hA_eq, ← Finset.sum_sdiff hsub]
    ring
  set R := B.sup id
  have htail_sub : B \ A_sf ⊆ Finset.Ioc M R := by
    intro q hq
    have hqB : q ∈ B := (Finset.mem_sdiff.mp hq).1
    have hqnA : q ∉ A_sf := (Finset.mem_sdiff.mp hq).2
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hqB
    have hpt : ∀ p ∈ t, p.Prime := fun p hp =>
      (Finset.mem_filter.mp (Finset.mem_powerset.mp ht hp)).2
    obtain ⟨hsf, hpos⟩ := squarefree_prod_of_primes hpt
    have hgt : M < ∏ p ∈ t, p := by
      by_contra hle
      apply hqnA
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, not_lt.mp hle⟩, hsf⟩
    have hleR : ∏ p ∈ t, p ≤ R := Finset.le_sup (f := id) hqB
    exact Finset.mem_Ioc.mpr ⟨hgt, hleR⟩
  have htail_bd : |∑ q ∈ B \ A_sf, singularTerm q n| ≤ 8 / Real.sqrt (M : ℝ) := by
    calc |∑ q ∈ B \ A_sf, singularTerm q n|
        ≤ ∑ q ∈ B \ A_sf, |singularTerm q n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ B \ A_sf, 4 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hqM : M < q := (Finset.mem_Ioc.mp (htail_sub hq)).1
          exact (abs_singularTerm_le_inv_totient_sq (by omega) n).trans
            (inv_totient_sq_le_four_div_mul_sqrt (by omega))
      _ ≤ ∑ q ∈ Finset.Ioc M R, 4 / ((q : ℝ) * Real.sqrt (q : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg htail_sub fun q _ _ => by positivity
      _ = 4 * ∑ q ∈ Finset.Ioc M R, 1 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by ring
      _ ≤ 4 * (2 / Real.sqrt (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_inv_mul_sqrt_le (by omega) R) (by norm_num)
      _ = 8 / Real.sqrt (M : ℝ) := by ring
  have hprod_lb : 2 * (2 - Real.pi ^ 2 / 6) ≤ ∏ p ∈ primesUpTo M, singularLocalFactor p n :=
    singularPartialProd_lower_bound hn M hM
  have hdiff_le : (∏ p ∈ primesUpTo M, singularLocalFactor p n) -
      (∑ q ∈ Finset.Icc 1 M, singularTerm q n) ≤ 8 / Real.sqrt (M : ℝ) := by
    rw [hdiff]; exact (le_abs_self _).trans htail_bd
  linarith

/-- Uniform upper bound on the truncated singular series: `|∑_{q=1}^M singularTerm q n| ≤ 12`. -/
theorem abs_truncated_singular_series_le (M n : ℕ) :
    |∑ q ∈ Finset.Icc 1 M, singularTerm q n| ≤ 12 := by
  by_cases hM : M = 0
  · subst hM; simp
  · have hsplit : Finset.Icc 1 M = insert 1 (Finset.Ioc 1 M) := by
      ext q; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
    calc |∑ q ∈ Finset.Icc 1 M, singularTerm q n|
        ≤ ∑ q ∈ Finset.Icc 1 M, |singularTerm q n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 M, 4 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          exact (abs_singularTerm_le_inv_totient_sq (by omega) n).trans
            (inv_totient_sq_le_four_div_mul_sqrt hq1)
      _ = 4 + 4 * ∑ q ∈ Finset.Ioc 1 M, 1 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
          rw [hsplit, Finset.sum_insert (by simp)]
          norm_num
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => by ring
      _ ≤ 4 + 4 * (2 / Real.sqrt (1 : ℝ)) := by
          have := sum_Ioc_inv_mul_sqrt_le (M := 1) le_rfl M
          linarith
      _ = 12 := by norm_num

/-! ## Section 5: Master Unconditional Major-Arc Lower Bound -/

/-- Algebraic cube-difference bound: `‖A^3 - B^3‖ ≤ ‖A - B‖ * (‖A‖^2 + ‖A‖ * ‖B‖ + ‖B‖^2)`. -/
private lemma norm_cube_sub_cube_le (A B : ℂ) :
    ‖A ^ 3 - B ^ 3‖ ≤ ‖A - B‖ * (‖A‖ ^ 2 + ‖A‖ * ‖B‖ + ‖B‖ ^ 2) := by
  have h : A ^ 3 - B ^ 3 = (A - B) * (A ^ 2 + A * B + B ^ 2) := by ring
  rw [h, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖A ^ 2 + A * B + B ^ 2‖
      ≤ ‖A ^ 2 + A * B‖ + ‖B ^ 2‖ := norm_add_le _ _
    _ ≤ ‖A ^ 2‖ + ‖A * B‖ + ‖B ^ 2‖ := by linarith [norm_add_le (A ^ 2) (A * B)]
    _ = ‖A‖ ^ 2 + ‖A‖ * ‖B‖ + ‖B‖ ^ 2 := by rw [norm_pow, norm_mul, norm_pow]

/-- **UNCONDITIONAL MAJOR-ARC INTEGRAL LOWER BOUND**:
for EVERY `B ≥ 1`, there exists `N₀ ≥ 16` such that for all odd `n ≥ N₀`,
`(1 / 4) * (2 * (2 - π² / 6)) * n² ≤ (∫ α in majorArcs n ((log n)^B), (S n α)³ * e (-n α)).re`. -/
theorem major_arc_integral_lower_bound (B : ℝ) (hB : 1 ≤ B) :
    ∃ N₀ : ℕ, 16 ≤ N₀ ∧
      ∀ n : ℕ, N₀ ≤ n → Odd n →
        (1 / 4 : ℝ) * (2 * (2 - Real.pi ^ 2 / 6)) * (n : ℝ) ^ 2 ≤
          (∫ α in majorArcs n ((Real.log (n : ℝ)) ^ B),
            (S n α) ^ 3 * e (-(n : ℝ) * α)).re := by
  set c_S : ℝ := 2 * (2 - Real.pi ^ 2 / 6)
  have hcS_pos : 0 < c_S := singular_series_constant_pos
  obtain ⟨N_sw, hNsw16, happrox⟩ := single_arc_S_approx B (3 * B + 2) hB (by linarith)
  -- Asymptotic thresholds for `n`
  have h1 : ∀ᶠ x : ℝ in atTop, 4 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4 : ℝ))
  have h2 : ∀ᶠ x : ℝ in atTop, 2 * (Real.log x) ^ (3 * B) < x := by
    have ht : Tendsto (fun x : ℝ => (Real.log x) ^ (3 * B) / x) atTop (𝓝 0) := by
      have h := (isLittleO_log_rpow_rpow_atTop (3 * B) zero_lt_one).tendsto_div_nhds_zero
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
      rw [Real.rpow_one]
    filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_gt_atTop (0 : ℝ)] with x hlt hpos
    have := (div_lt_iff₀ hpos).mp hlt
    linarith
  have h3 : ∀ᶠ x : ℝ in atTop, (32 / c_S) ^ 2 + 2 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((32 / c_S) ^ 2 + 2))
  have h4 : ∀ᶠ x : ℝ in atTop, 400 / c_S + 2 ≤ (Real.log x) ^ 2 := by
    have ht : Tendsto (fun x : ℝ => (Real.log x) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp Real.tendsto_log_atTop
    exact ht.eventually (eventually_ge_atTop (400 / c_S + 2))
  have hall := h1.and (h2.and (h3.and h4))
  rw [Filter.eventually_atTop] at hall
  obtain ⟨X₀, hX₀⟩ := hall
  refine ⟨max N_sw ⌈X₀⌉₊, hNsw16.trans (le_max_left _ _), fun n hn hodd => ?_⟩
  have hn_sw : N_sw ≤ n := (le_max_left _ _).trans hn
  have hn16 : 16 ≤ n := hNsw16.trans hn_sw
  have hnX : X₀ ≤ (n : ℝ) := (Nat.le_ceil X₀).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  obtain ⟨hlog4, h2Q3, hlog_S, hlog2_err⟩ := hX₀ (n : ℝ) hnX
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  set Q : ℝ := (Real.log (n : ℝ)) ^ B
  have hQ_ge_log : Real.log (n : ℝ) ≤ Q := by
    calc Real.log (n : ℝ) = (Real.log (n : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log (n : ℝ)) ^ B := Real.rpow_le_rpow_of_exponent_le (by linarith) hB
  have hQ_ge1 : 1 ≤ Q := by linarith
  have hQ_pos : 0 < Q := by linarith
  have hQ3_eq : Q ^ 3 = (Real.log (n : ℝ)) ^ (3 * B) := by
    dsimp only [Q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog_pos.le]
    congr 1; push_cast; ring
  have hQN : 2 * Q ^ 3 < (n : ℝ) := by rw [hQ3_eq]; exact h2Q3
  set δ : ℝ := Q / (n : ℝ)
  have hδ_pos : 0 < δ := div_pos hQ_pos hn_pos
  have hδ_le_half : δ ≤ 1 / 2 := by
    dsimp only [δ]
    rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 2)]
    have hQ2 : Q ≤ Q ^ 2 := by nlinarith
    have hQ_le_Q3 : Q ≤ Q ^ 3 := by nlinarith
    nlinarith
  set M := ⌊Q⌋₊
  -- Step 1: Decompose `∫_{majorArcs n Q}` via `integral_majorArcs_eq_sum`
  have hFcont : Continuous (fun α : ℝ => (S n α) ^ 3 * e (-(n : ℝ) * α)) := by
    have : Continuous (S n) := by unfold S; fun_prop
    fun_prop
  have hFper : ∀ α : ℝ, (S n (α + 1)) ^ 3 * e (-(n : ℝ) * (α + 1)) =
      (S n α) ^ 3 * e (-(n : ℝ) * α) := by
    intro α
    have hS : S n (α + 1) = S n α := by
      unfold S
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_add, mul_one, e_add, e_natCast, mul_one]
    have he : e (-(n : ℝ) * (α + 1)) = e (-(n : ℝ) * α) := by
      rw [show -(n : ℝ) * (α + 1) = -(n : ℝ) * α + ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring,
        e_add, e_intCast, mul_one]
    rw [hS, he]
  have hdecomp := integral_majorArcs_eq_sum hQ_ge1 hQN hFcont hFper
  -- Step 2: Compare the major-arc integral with the model integral
  set modelInt : ℂ :=
    (∑ q ∈ Finset.Icc 1 M, (singularTerm q n : ℂ)) *
      (∫ β in (-δ)..δ, (v n β) ^ 3 * e (-(n : ℝ) * β))
  have hmodel_eq : modelInt =
      ∑ q ∈ Finset.Icc 1 M,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ∫ β in (-δ)..δ,
            (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
              e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)) := by
    dsimp only [modelInt]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq_ne : q ≠ 0 := by have := (Finset.mem_Icc.mp hq).1; omega
    have hterm_a : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        (∫ β in (-δ)..δ,
          (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
            e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β))) =
        (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
          e (-((a : ℝ) * (n : ℝ)) / (q : ℝ))) *
          (∫ β in (-δ)..δ, (v n β) ^ 3 * e (-(n : ℝ) * β)) := by
      intro a _
      have hcongr : ∀ β : ℝ,
          (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
            e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)) =
          (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
            e (-((a : ℝ) * (n : ℝ)) / (q : ℝ))) * ((v n β) ^ 3 * e (-(n : ℝ) * β)) := by
        intro β
        have he : e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)) =
            e (-((a : ℝ) * (n : ℝ)) / (q : ℝ)) * e (-(n : ℝ) * β) := by
          rw [← e_add]; congr 1; ring
        rw [he]; ring
      simp_rw [hcongr]
      rw [intervalIntegral.integral_const_mul]
    rw [Finset.sum_congr rfl hterm_a, ← Finset.sum_mul, ← Finset.mul_sum,
      sum_e_neg_div_eq_ramanujanSum q n hq_ne, ramanujanSum_eq_ofReal q n hq_ne]
    congr 1
    unfold singularTerm
    push_cast
    rfl
  -- Bound `‖∫_{majorArcs} - modelInt‖ ≤ 24 * n^2 / (log n)^2`
  set E : ℝ := (n : ℝ) / (Real.log (n : ℝ)) ^ (3 * B + 2)
  have hE_le : E ≤ (n : ℝ) := by
    dsimp only [E]
    refine div_le_self hn_pos.le ?_
    exact Real.one_le_rpow (by linarith) (by linarith)
  have herr_approx : ‖(∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)) - modelInt‖ ≤
      48 * (n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 := by
    rw [hdecomp, hmodel_eq, ← Finset.sum_sub_distrib]
    calc ‖∑ q ∈ Finset.Icc 1 M,
            ((∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              ∫ β in (-δ)..δ, (S n ((a : ℝ) / (q : ℝ) + β)) ^ 3 *
                e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β))) -
            (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              ∫ β in (-δ)..δ,
                (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
                  e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β))))‖
        ≤ ∑ q ∈ Finset.Icc 1 M,
            ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              ((∫ β in (-δ)..δ, (S n ((a : ℝ) / (q : ℝ) + β)) ^ 3 *
                  e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β))) -
                (∫ β in (-δ)..δ,
                  (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
                    e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β))))‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
          rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ q ∈ Finset.Icc 1 M, ∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            (48 * Q * (n : ℝ) * E) := by
          refine Finset.sum_le_sum fun q hq => ?_
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
          have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
            exact_mod_cast Nat.totient_pos.mpr hq1
          have hcont_S : Continuous (fun β : ℝ =>
              (S n ((a : ℝ) / (q : ℝ) + β)) ^ 3 * e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β))) := by
            have : Continuous (S n) := by unfold S; fun_prop
            fun_prop
          have hcont_M : Continuous (fun β : ℝ =>
              (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
                e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β))) := by
            unfold v; fun_prop
          rw [← intervalIntegral.integral_sub (hcont_S.intervalIntegrable _ _)
            (hcont_M.intervalIntegrable _ _)]
          have hpt : ∀ β ∈ Set.Icc (-δ) δ,
              ‖(S n ((a : ℝ) / (q : ℝ) + β)) ^ 3 * e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)) -
                (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
                  e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β))‖ ≤ 24 * (n : ℝ) ^ 2 * E := by
            intro β hβ
            have hβ_abs : |β| ≤ δ := abs_le.mpr hβ
            have hdiff_pt := happrox n hn_sw q hq a hcop β hβ_abs
            have hfactor : (S n ((a : ℝ) / (q : ℝ) + β)) ^ 3 * e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)) -
                (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
                  e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)) =
                ((S n ((a : ℝ) / (q : ℝ) + β)) ^ 3 -
                  (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3) *
                  e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)) := by ring
            rw [hfactor, norm_mul, norm_e, mul_one]
            set A_val := S n ((a : ℝ) / (q : ℝ) + β)
            set B_val := ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β
            have hB_le : ‖B_val‖ ≤ 2 * (n : ℝ) := by
              dsimp only [B_val]
              rw [norm_mul, norm_div, Complex.norm_natCast]
              have hmu : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
                by_cases hsf : Squarefree q
                · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]; simp
                · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
              have hfrac : ‖(ArithmeticFunction.moebius q : ℂ)‖ / (q.totient : ℝ) ≤ 1 :=
                div_le_one_of_le₀ (hmu.trans hphi_ge1) (by positivity)
              have hv := norm_v_le n β
              have hn1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
                have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
                linarith
              calc ‖(ArithmeticFunction.moebius q : ℂ)‖ / (q.totient : ℝ) * ‖v n β‖
                  ≤ 1 * (2 * (n : ℝ)) := mul_le_mul hfrac (hv.trans hn1) (norm_nonneg _) zero_le_one
                _ = 2 * (n : ℝ) := one_mul _
            have hA_le : ‖A_val‖ ≤ 3 * (n : ℝ) := by
              have htri : ‖A_val‖ ≤ ‖A_val - B_val‖ + ‖B_val‖ := by
                simpa [sub_add_cancel] using norm_add_le (A_val - B_val) B_val
              linarith
            calc ‖A_val ^ 3 - B_val ^ 3‖
                ≤ ‖A_val - B_val‖ * (‖A_val‖ ^ 2 + ‖A_val‖ * ‖B_val‖ + ‖B_val‖ ^ 2) :=
                  norm_cube_sub_cube_le A_val B_val
              _ ≤ E * ((3 * (n : ℝ)) ^ 2 + (3 * (n : ℝ)) * (2 * (n : ℝ)) + (2 * (n : ℝ)) ^ 2) := by
                  refine mul_le_mul hdiff_pt ?_ (by positivity) (by positivity)
                  nlinarith [norm_nonneg A_val, norm_nonneg B_val]
              _ ≤ 24 * (n : ℝ) ^ 2 * E := by nlinarith [show (0 : ℝ) ≤ E by positivity]
          calc ‖∫ β in (-δ)..δ,
                  ((S n ((a : ℝ) / (q : ℝ) + β)) ^ 3 * e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)) -
                    (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * v n β) ^ 3 *
                      e (-(n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))‖
              ≤ (24 * (n : ℝ) ^ 2 * E) * |δ - (-δ)| :=
                intervalIntegral.norm_integral_le_of_norm_le_const fun β hβ => by
                  rw [Set.uIoc_of_le (by linarith)] at hβ
                  exact hpt β ⟨hβ.1.le, hβ.2⟩
            _ = (24 * (n : ℝ) ^ 2 * E) * (2 * δ) := by
                rw [sub_neg_eq_add, show δ + δ = 2 * δ by ring, abs_of_pos (by positivity)]
            _ = 48 * Q * (n : ℝ) * E := by dsimp only [δ]; field_simp [hn_pos.ne']; ring
      _ ≤ Q ^ 2 * (48 * Q * (n : ℝ) * E) := by
          have hinner_le : ∀ q ∈ Finset.Icc 1 M,
              (∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (48 * Q * (n : ℝ) * E)) ≤
              Q * (48 * Q * (n : ℝ) * E) := by
            intro q hq
            rw [Finset.sum_const, nsmul_eq_mul]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hcard : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ (q : ℝ) := by
              exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
            have hqQ : (q : ℝ) ≤ Q :=
              (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le hQ_pos.le)
            exact hcard.trans hqQ
          calc ∑ q ∈ Finset.Icc 1 M, ∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
                  (48 * Q * (n : ℝ) * E)
              ≤ ∑ _q ∈ Finset.Icc 1 M, Q * (48 * Q * (n : ℝ) * E) := Finset.sum_le_sum hinner_le
            _ = ((Finset.Icc 1 M).card : ℝ) * (Q * (48 * Q * (n : ℝ) * E)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ Q * (Q * (48 * Q * (n : ℝ) * E)) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                have hcard : ((Finset.Icc 1 M).card : ℝ) ≤ (M : ℝ) := by simp
                exact hcard.trans (Nat.floor_le hQ_pos.le)
            _ = Q ^ 2 * (48 * Q * (n : ℝ) * E) := by ring
      _ = 48 * (n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 := by
          have hmul : Q ^ 2 * (48 * Q * (n : ℝ) * E) = 48 * Q ^ 3 * (n : ℝ) * E := by ring
          rw [hmul, hQ3_eq]
          dsimp only [E]
          rw [Real.rpow_add hlog_pos, show (Real.log (n : ℝ)) ^ (2 : ℝ) = (Real.log (n : ℝ)) ^ (2 : ℕ) by
            norm_cast]
          field_simp [(Real.rpow_pos_of_pos hlog_pos (3 * B)).ne', hlog_pos.ne']
  -- Step 3: Compare `modelInt` with the exact real main term
  set singSum : ℝ := ∑ q ∈ Finset.Icc 1 M, singularTerm q n
  set exactMain : ℝ := singSum * (((n : ℝ) + 1) * ((n : ℝ) + 2) / 2)
  have herr_tail : ‖modelInt - (exactMain : ℂ)‖ ≤ (3 / 2 : ℝ) * (n : ℝ) ^ 2 / Q ^ 2 := by
    have hrew : modelInt - (exactMain : ℂ) =
        (singSum : ℂ) *
          ((∫ β in (-δ)..δ, (v n β) ^ 3 * e (-(n : ℝ) * β)) -
            (∫ β in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), (v n β) ^ 3 * e (-(n : ℝ) * β))) := by
      rw [singular_integral_exact n]
      dsimp only [modelInt, exactMain, singSum]
      push_cast
      ring
    rw [hrew, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hs12 : |singSum| ≤ 12 := abs_truncated_singular_series_le M n
    have htail := singular_integral_tail_bound n n hδ_pos hδ_le_half
    have hδ_inv : 1 / (8 * δ ^ 2) = (n : ℝ) ^ 2 / (8 * Q ^ 2) := by
      dsimp only [δ]; field_simp [hn_pos.ne', hQ_pos.ne']
    rw [hδ_inv] at htail
    calc |singSum| * ‖_‖
        ≤ 12 * ((n : ℝ) ^ 2 / (8 * Q ^ 2)) :=
          mul_le_mul hs12 htail (norm_nonneg _) (by norm_num)
      _ = (3 / 2 : ℝ) * (n : ℝ) ^ 2 / Q ^ 2 := by ring
  -- Step 4: Lower-bound `exactMain` and subtract the two error bounds
  have hM2 : 2 ≤ M := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ Q))
  have hM_ge : (32 / c_S) ^ 2 ≤ (M : ℝ) := by
    have hfl := Nat.lt_floor_add_one Q
    linarith
  have hsing_lb : (3 / 4 : ℝ) * c_S ≤ singSum := by
    have hlb : c_S - 8 / Real.sqrt (M : ℝ) ≤ singSum :=
      truncated_singular_series_lower_bound hodd hM2
    have hsqM : 32 / c_S ≤ Real.sqrt (M : ℝ) :=
      Real.le_sqrt_of_sq_le hM_ge
    have h8div : 8 / Real.sqrt (M : ℝ) ≤ c_S / 4 := by
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < M))) (by norm_num)]
      have := mul_le_mul_of_nonneg_left hsqM hcS_pos.le
      rw [mul_div_cancel₀ _ hcS_pos.ne'] at this
      linarith
    linarith
  have hmain_lb : (3 / 8 : ℝ) * c_S * (n : ℝ) ^ 2 ≤ exactMain := by
    dsimp only [exactMain]
    have hquad : (n : ℝ) ^ 2 / 2 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by nlinarith
    nlinarith
  have herr_total : 48 * (n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 +
      (3 / 2 : ℝ) * (n : ℝ) ^ 2 / Q ^ 2 ≤ (1 / 8 : ℝ) * c_S * (n : ℝ) ^ 2 := by
    have hQ2_ge : (Real.log (n : ℝ)) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hlog_pos.le hQ_ge_log 2
    have h2 : (3 / 2 : ℝ) * (n : ℝ) ^ 2 / Q ^ 2 ≤ (3 / 2 : ℝ) * (n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hQ2_ge
    have hsum_frac : (48 + 3 / 2 : ℝ) / (Real.log (n : ℝ)) ^ 2 ≤ (1 / 8 : ℝ) * c_S := by
      rw [div_le_iff₀ (by positivity)]
      have hmul := mul_le_mul_of_nonneg_left hlog2_err hcS_pos.le
      rw [mul_add, mul_div_cancel₀ _ hcS_pos.ne'] at hmul
      linarith
    have hfac : 48 * (n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 +
        (3 / 2 : ℝ) * (n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 =
        ((48 + 3 / 2 : ℝ) / (Real.log (n : ℝ)) ^ 2) * (n : ℝ) ^ 2 := by ring
    nlinarith
  -- Conclude using `|z.re - exactMain| ≤ ‖z - exactMain‖ ≤ herr_approx + herr_tail`
  have hre_diff :
      |(∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)).re - exactMain| ≤
        48 * (n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 + (3 / 2 : ℝ) * (n : ℝ) ^ 2 / Q ^ 2 := by
    have h1 : |(∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)).re - exactMain| =
        |((∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)) - (exactMain : ℂ)).re| := by
      simp
    rw [h1]
    calc |((∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)) - (exactMain : ℂ)).re|
        ≤ ‖(∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)) - (exactMain : ℂ)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ‖(∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)) - modelInt‖ +
          ‖modelInt - (exactMain : ℂ)‖ := by
          simpa [sub_add_sub_cancel] using norm_add_le
            ((∫ α in majorArcs n Q, (S n α) ^ 3 * e (-(n : ℝ) * α)) - modelInt)
            (modelInt - (exactMain : ℂ))
      _ ≤ 48 * (n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2 + (3 / 2 : ℝ) * (n : ℝ) ^ 2 / Q ^ 2 :=
          add_le_add herr_approx herr_tail
  linarith [(abs_le.mp hre_diff).1]

end

#print axioms RHDirect.Vinogradov.measurableSet_majorArcs
#print axioms RHDirect.Vinogradov.majorArc_disjoint
#print axioms RHDirect.Vinogradov.integral_majorArcs_eq_sum
#print axioms RHDirect.Vinogradov.single_arc_S_approx
#print axioms RHDirect.Vinogradov.singular_integral_exact
#print axioms RHDirect.Vinogradov.singular_integral_tail_bound
#print axioms RHDirect.Vinogradov.truncated_singular_series_lower_bound
#print axioms RHDirect.Vinogradov.major_arc_integral_lower_bound

end RHDirect.Vinogradov
