import RHDirect.VinogradovExpSum
import RHDirect.VinogradovMinorArc
import RHDirect.Stage11BombieriVinogradov
import RHDirect.Stage8BarbanDavenport
import RHDirect.Stage4ExplicitFormula
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Vinogradov's Three-Primes Theorem — Unconditional Minor-Arc `L^∞` Bound

100%-unconditional (`0` extra hypotheses, `0` `sorry`, `0` custom `axiom`s, native Mathlib
`Nat.Prime`, `Real.log`, `Complex.exp`, `ArithmeticFunction.vonMangoldt`) formalization of
Vinogradov's minor-arc `L^∞` bound via Vaughan's identity (1977):

1. **Dirichlet's Approximation Theorem** (`dirichlet_approximation`): for every `α : ℝ` and `τ ≥ 1`,
   `∃ 1 ≤ q ≤ τ, ∃ a : ℤ, Coprime a.natAbs q ∧ |α - a/q| ≤ 1 / (q * τ)`.
2. **Prime-Power Comparison** (`norm_S_sub_S_Λ_le`): `‖S N α - S_Λ N α‖ ≤ √N · log N`.
3. **Exponential Sum & Reciprocal-Distance Bounds** (`norm_sum_e_Icc_le`,
   `sum_expBound_const_le`, `sum_expBound_div_le`): geometric-sum bound via Jordan's inequality
   and uniform reciprocal-distance sums over blocks of length `q`.
4. **Twisted Vaughan Identity & Type I / Type II Bounds** (`vaughan_exp_sum_bound`):
   `‖S N α‖ ≤ 130 · (1 + log (2 N))⁴ · (N / √q + N^{4/5} + √(N q))`.
5. **Headline Minor-Arc `L^∞` Bound** (`vinogradov_minor_arc_sup_bound`):
   for every `A ≥ 0`, `∃ B ≥ 1, ∃ C > 0`, such that for all `N ≥ 3` and all
   `α ∈ minorArcs N ((Real.log N) ^ B)`, `‖S N α‖ ≤ C · N / (Real.log N) ^ A`.
-/

open Real Complex Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Vinogradov

noncomputable section

/-! ## Section 1: Minor Arcs & Dirichlet's Approximation Theorem -/

/-- Minor arcs on `[0, 1]` with cutoff parameter `Q`:
points `α ∈ [0, 1]` outside all major arcs `|α - a/q| ≤ Q / N` with `1 ≤ q ≤ ⌊Q⌋₊`,
`0 ≤ a ≤ q`, and `Nat.Coprime a q`. Matches `VinogradovMajorArcEval.majorArcs` definitionally. -/
def minorArcs (N : ℕ) (Q : ℝ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 \
    (Set.Icc (0 : ℝ) 1 ∩
      ⋃ q ∈ Finset.Icc 1 ⌊Q⌋₊,
        ⋃ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
          {α : ℝ | |α - (a : ℝ) / (q : ℝ)| ≤ Q / (N : ℝ)})

/-- **Dirichlet's Approximation Theorem** (1842), unconditional for all `α : ℝ` and `τ ≥ 1`:
there exist `1 ≤ q ≤ τ` and `a : ℤ` with `Nat.Coprime a.natAbs q` and
`|α - a / q| ≤ 1 / (q * τ)`. -/
theorem dirichlet_approximation (α : ℝ) (τ : ℝ) (hτ : 1 ≤ τ) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ τ ∧
      ∃ a : ℤ, Nat.Coprime a.natAbs q ∧ |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * τ) := by
  set M : ℕ := ⌊τ⌋₊ with hM_def
  have hM1 : 1 ≤ M := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hτ)
  have hM_le : (M : ℝ) ≤ τ := Nat.floor_le (by linarith)
  have hτ_lt : τ < (M : ℝ) + 1 := Nat.lt_floor_add_one τ
  have hM1_pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  -- First produce a (not necessarily reduced) pair `(q₀, a₀)` with `1 ≤ q₀ ≤ M` and
  -- `|(q₀ : ℝ) * α - a₀| ≤ 1 / (M + 1)`.
  have hraw : ∃ q₀ : ℕ, 1 ≤ q₀ ∧ q₀ ≤ M ∧
      ∃ a₀ : ℤ, |(q₀ : ℝ) * α - (a₀ : ℝ)| ≤ 1 / ((M : ℝ) + 1) := by
    by_cases hlow : ∃ k ∈ Finset.Icc 1 M,
        Int.fract ((k : ℝ) * α) ≤ 1 / ((M : ℝ) + 1) ∨
        1 - 1 / ((M : ℝ) + 1) ≤ Int.fract ((k : ℝ) * α)
    · obtain ⟨k, hk, hcase⟩ := hlow
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
      refine ⟨k, hk1, hkM, ?_⟩
      rcases hcase with hle | hge
      · refine ⟨⌊(k : ℝ) * α⌋, ?_⟩
        have hfr : (k : ℝ) * α - (⌊(k : ℝ) * α⌋ : ℝ) = Int.fract ((k : ℝ) * α) := rfl
        rw [hfr, abs_of_nonneg (Int.fract_nonneg _)]
        exact hle
      · refine ⟨⌊(k : ℝ) * α⌋ + 1, ?_⟩
        have hfr : (k : ℝ) * α - ((⌊(k : ℝ) * α⌋ + 1 : ℤ) : ℝ) =
            Int.fract ((k : ℝ) * α) - 1 := by
          push_cast; simp only [Int.fract]; ring
        rw [hfr, abs_of_nonpos (by linarith [Int.fract_lt_one ((k : ℝ) * α)])]
        linarith
    · push Not at hlow
      -- Every `k ∈ Icc 1 M` has `1/(M+1) < fract(k α) < 1 - 1/(M+1)`,
      -- so `⌊(M+1) * fract(k α)⌋₊ ∈ Icc 1 (M - 1)`.
      -- Since `|Icc 1 M| = M > M - 1 = |Icc 1 (M - 1)|`, pigeonhole yields `k₁ ≠ k₂`.
      have hmaps : ∀ k ∈ Finset.Icc 1 M,
          ⌊((M : ℝ) + 1) * Int.fract ((k : ℝ) * α)⌋₊ ∈ Finset.Icc 1 (M - 1) := by
        intro k hk
        obtain ⟨hgt, hlt⟩ := hlow k hk
        simp only [Finset.mem_Icc]
        have hmul_gt : (1 : ℝ) < ((M : ℝ) + 1) * Int.fract ((k : ℝ) * α) := by
          have := (div_lt_iff₀ hM1_pos).mp hgt
          linarith
        have hmul_lt : ((M : ℝ) + 1) * Int.fract ((k : ℝ) * α) < (M : ℝ) := by
          have h1 : ((M : ℝ) + 1) * (1 - 1 / ((M : ℝ) + 1)) = (M : ℝ) := by
            field_simp [hM1_pos.ne']; ring
          nlinarith
        have hge1 : 1 ≤ ⌊((M : ℝ) + 1) * Int.fract ((k : ℝ) * α)⌋₊ :=
          (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hmul_gt.le)
        have hltM : ⌊((M : ℝ) + 1) * Int.fract ((k : ℝ) * α)⌋₊ < M :=
          (Nat.floor_lt (by linarith)).mpr hmul_lt
        exact ⟨hge1, by omega⟩
      have hcard : (Finset.Icc 1 (M - 1)).card < (Finset.Icc 1 M).card := by
        simp only [Nat.card_Icc]; omega
      obtain ⟨k₁, hk₁, k₂, hk₂, hne, heq⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
      have hex_lt : ∃ i ∈ Finset.Icc 1 M, ∃ j ∈ Finset.Icc 1 M, i < j ∧
          ⌊((M : ℝ) + 1) * Int.fract ((i : ℝ) * α)⌋₊ =
            ⌊((M : ℝ) + 1) * Int.fract ((j : ℝ) * α)⌋₊ := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ⟨k₁, hk₁, k₂, hk₂, hlt, heq⟩
        · exact ⟨k₂, hk₂, k₁, hk₁, hgt, heq.symm⟩
      obtain ⟨i, hi, j, hj, hij, hfl_eq⟩ := hex_lt
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hjM : j ≤ M := (Finset.mem_Icc.mp hj).2
      refine ⟨j - i, by omega, by omega, ⌊(j : ℝ) * α⌋ - ⌊(i : ℝ) * α⌋, ?_⟩
      have hsub_eq : ((j - i : ℕ) : ℝ) * α - ((⌊(j : ℝ) * α⌋ - ⌊(i : ℝ) * α⌋ : ℤ) : ℝ) =
          Int.fract ((j : ℝ) * α) - Int.fract ((i : ℝ) * α) := by
        rw [Nat.cast_sub hij.le]
        push_cast
        simp only [Int.fract]
        ring
      rw [hsub_eq]
      have hbi1 : (⌊((M : ℝ) + 1) * Int.fract ((i : ℝ) * α)⌋₊ : ℝ) ≤
          ((M : ℝ) + 1) * Int.fract ((i : ℝ) * α) :=
        Nat.floor_le (by positivity [Int.fract_nonneg ((i : ℝ) * α)])
      have hbi2 : ((M : ℝ) + 1) * Int.fract ((i : ℝ) * α) <
          (⌊((M : ℝ) + 1) * Int.fract ((i : ℝ) * α)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hbj1 : (⌊((M : ℝ) + 1) * Int.fract ((j : ℝ) * α)⌋₊ : ℝ) ≤
          ((M : ℝ) + 1) * Int.fract ((j : ℝ) * α) :=
        Nat.floor_le (by positivity [Int.fract_nonneg ((j : ℝ) * α)])
      have hbj2 : ((M : ℝ) + 1) * Int.fract ((j : ℝ) * α) <
          (⌊((M : ℝ) + 1) * Int.fract ((j : ℝ) * α)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      rw [hfl_eq] at hbi1 hbi2
      have habs_mul : |((M : ℝ) + 1) * (Int.fract ((j : ℝ) * α) - Int.fract ((i : ℝ) * α))| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul, abs_of_pos hM1_pos] at habs_mul
      exact (le_div_iff₀' hM1_pos).mpr habs_mul
  -- Reduce `a₀ / q₀` to lowest terms `a / q`
  obtain ⟨q₀, hq₀1, hq₀M, a₀, happrox⟩ := hraw
  set g : ℕ := Nat.gcd a₀.natAbs q₀ with hg_def
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right a₀.natAbs hq₀1
  have hg_dvd_q₀ : g ∣ q₀ := Nat.gcd_dvd_right a₀.natAbs q₀
  have hg_dvd_a₀ : (g : ℤ) ∣ a₀ :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_left a₀.natAbs q₀)
  set q : ℕ := q₀ / g with hq_def
  set a : ℤ := a₀ / (g : ℤ) with ha_def
  have hq1 : 1 ≤ q := Nat.div_pos (Nat.le_of_dvd hq₀1 hg_dvd_q₀) hg_pos
  have hq_le_q₀ : q ≤ q₀ := Nat.div_le_self q₀ g
  have hq_le_τ : (q : ℝ) ≤ τ :=
    (Nat.cast_le.mpr (hq_le_q₀.trans hq₀M)).trans hM_le
  have hcop : Nat.Coprime a.natAbs q := by
    have ha_natAbs : a.natAbs = a₀.natAbs / g := by
      rw [ha_def, Int.natAbs_ediv_of_dvd hg_dvd_a₀, Int.natAbs_natCast]
    rw [ha_natAbs, hq_def]
    exact Nat.coprime_div_gcd_div_gcd hg_pos
  refine ⟨q, hq1, hq_le_τ, a, hcop, ?_⟩
  have haq_eq : (a : ℝ) / (q : ℝ) = (a₀ : ℝ) / (q₀ : ℝ) := by
    have hq₀_eq : (q₀ : ℝ) = (g : ℝ) * (q : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hg_dvd_q₀).symm
    have ha₀_eq : (a₀ : ℝ) = (g : ℝ) * (a : ℝ) := by
      have h1 : (g : ℤ) * a = a₀ := Int.mul_ediv_cancel' hg_dvd_a₀
      exact_mod_cast h1.symm
    have hg_ne : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
    have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [ha₀_eq, hq₀_eq]
    field_simp [hg_ne, hq_ne]
  rw [haq_eq]
  have hq₀_pos : (0 : ℝ) < (q₀ : ℝ) := Nat.cast_pos.mpr hq₀1
  have h1 : |α - (a₀ : ℝ) / (q₀ : ℝ)| = |(q₀ : ℝ) * α - (a₀ : ℝ)| / (q₀ : ℝ) := by
    calc |α - (a₀ : ℝ) / (q₀ : ℝ)|
        = |((q₀ : ℝ) * α - (a₀ : ℝ)) / (q₀ : ℝ)| := by congr 1; field_simp [hq₀_pos.ne']
      _ = |(q₀ : ℝ) * α - (a₀ : ℝ)| / (q₀ : ℝ) := by rw [abs_div, abs_of_pos hq₀_pos]
  rw [h1]
  have h2 : |(q₀ : ℝ) * α - (a₀ : ℝ)| / (q₀ : ℝ) ≤ 1 / ((q₀ : ℝ) * ((M : ℝ) + 1)) := by
    calc |(q₀ : ℝ) * α - (a₀ : ℝ)| / (q₀ : ℝ)
        ≤ (1 / ((M : ℝ) + 1)) / (q₀ : ℝ) :=
          div_le_div_of_nonneg_right happrox hq₀_pos.le
      _ = 1 / ((q₀ : ℝ) * ((M : ℝ) + 1)) := by
          rw [div_div, mul_comm]
  refine h2.trans ?_
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq1
  have hτ_pos : (0 : ℝ) < τ := by linarith
  refine one_div_le_one_div_of_le (mul_pos hq_pos hτ_pos) ?_
  exact mul_le_mul (Nat.cast_le.mpr hq_le_q₀) hτ_lt.le hτ_pos.le hq₀_pos.le

/-- Every point `α ∈ minorArcs N Q` (with `1 ≤ Q < N`) admits a Dirichlet approximation
`a / q` with `Q < q ≤ N / Q`, `Nat.Coprime a.natAbs q`, and `|α - a / q| ≤ 1 / q²`. -/
theorem minorArcs_dirichlet_approx {N : ℕ} {Q α : ℝ}
    (hQ1 : 1 ≤ Q) (hQN : Q < (N : ℝ)) (hα : α ∈ minorArcs N Q) :
    ∃ q : ℕ, 1 ≤ q ∧ Q < (q : ℝ) ∧ (q : ℝ) ≤ (N : ℝ) / Q ∧
      ∃ a : ℤ, Nat.Coprime a.natAbs q ∧ |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 := by
  have hQ_pos : 0 < Q := by linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hτ : 1 ≤ (N : ℝ) / Q := (one_le_div hQ_pos).mpr hQN.le
  obtain ⟨q, hq1, hqτ, a, hcop, happrox⟩ := dirichlet_approximation α ((N : ℝ) / Q) hτ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq1
  have happrox_QN : |α - (a : ℝ) / (q : ℝ)| ≤ Q / ((q : ℝ) * (N : ℝ)) := by
    have hEq : 1 / ((q : ℝ) * ((N : ℝ) / Q)) = Q / ((q : ℝ) * (N : ℝ)) := by
      field_simp [hq_pos.ne', hQ_pos.ne', hN_pos.ne']
    rwa [hEq] at happrox
  have happrox_sq : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happrox.trans ?_
    rw [sq]
    exact one_div_le_one_div_of_le (mul_pos hq_pos hq_pos)
      (mul_le_mul_of_nonneg_left hqτ hq_pos.le)
  have hQ_lt_q : Q < (q : ℝ) := by
    by_contra hle
    push Not at hle
    have hα_Icc : α ∈ Set.Icc (0 : ℝ) 1 := hα.1
    have hα_not : α ∉ (Set.Icc (0 : ℝ) 1 ∩
        ⋃ q' ∈ Finset.Icc 1 ⌊Q⌋₊,
          ⋃ a' ∈ (Finset.range (q' + 1)).filter (fun a' => Nat.Coprime a' q'),
            {x : ℝ | |x - (a' : ℝ) / (q' : ℝ)| ≤ Q / (N : ℝ)}) := hα.2
    have hlt_inv : |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) := by
      calc |α - (a : ℝ) / (q : ℝ)|
          ≤ Q / ((q : ℝ) * (N : ℝ)) := happrox_QN
        _ < (N : ℝ) / ((q : ℝ) * (N : ℝ)) :=
            div_lt_div_of_pos_right hQN (mul_pos hq_pos hN_pos)
        _ = 1 / (q : ℝ) := by field_simp [hq_pos.ne', hN_pos.ne']
    have ha_nonneg : 0 ≤ a := by
      by_contra hneg
      have ha_le : (a : ℝ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
      have h1 : (a : ℝ) / (q : ℝ) ≤ -(1 / (q : ℝ)) := by
        have := div_le_div_of_nonneg_right ha_le hq_pos.le
        linarith [show (-1 : ℝ) / (q : ℝ) = -(1 / (q : ℝ)) by ring]
      have h2 : 0 ≤ α := hα_Icc.1
      linarith [(abs_lt.mp hlt_inv).2]
    have ha_le_q : a ≤ (q : ℤ) := by
      by_contra hgt
      have ha_ge : ((q : ℝ) + 1) ≤ (a : ℝ) := by exact_mod_cast (show (q : ℤ) + 1 ≤ a by omega)
      have h1 : 1 + 1 / (q : ℝ) ≤ (a : ℝ) / (q : ℝ) := by
        have : ((q : ℝ) + 1) / (q : ℝ) = 1 + 1 / (q : ℝ) := by field_simp [hq_pos.ne']
        rw [← this]
        exact div_le_div_of_nonneg_right ha_ge hq_pos.le
      have h2 : α ≤ 1 := hα_Icc.2
      linarith [(abs_lt.mp hlt_inv).1]
    set a' : ℕ := a.natAbs
    have ha_eq : (a : ℝ) = (a' : ℝ) := by
      have : (a' : ℤ) = a := Int.natAbs_of_nonneg ha_nonneg
      exact_mod_cast this.symm
    have ha'_le : a' ≤ q := by
      have : (a' : ℤ) = a := Int.natAbs_of_nonneg ha_nonneg
      omega
    apply hα_not
    refine ⟨hα_Icc, Set.mem_iUnion₂.mpr ⟨q, ?_, Set.mem_iUnion₂.mpr ⟨a', ?_, ?_⟩⟩⟩
    · exact Finset.mem_Icc.mpr ⟨hq1, (Nat.le_floor_iff hQ_pos.le).mpr hle⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcop⟩
    · change |α - (a' : ℝ) / (q : ℝ)| ≤ Q / (N : ℝ)
      rw [← ha_eq]
      calc |α - (a : ℝ) / (q : ℝ)|
          ≤ Q / ((q : ℝ) * (N : ℝ)) := happrox_QN
        _ ≤ Q / (1 * (N : ℝ)) := by
            apply div_le_div_of_nonneg_left hQ_pos.le (by positivity)
            exact mul_le_mul_of_nonneg_right (Nat.one_le_cast.mpr hq1) hN_pos.le
        _ = Q / (N : ℝ) := by ring
  exact ⟨q, hq1, hQ_lt_q, hqτ, a, hcop, happrox_sq⟩

/-! ## Section 2: Von Mangoldt Exponential Sum & Prime-Power Comparison -/

/-- The von Mangoldt exponential sum `S_Λ(N, α) = ∑_{1 ≤ n ≤ N} Λ(n) e(n α)`. -/
def S_Λ (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * e ((n : ℝ) * α)

/-- Unconditional prime-power comparison: `‖S N α - S_Λ N α‖ ≤ √N · log N` for `N ≥ 1`. -/
theorem norm_S_sub_S_Λ_le (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ‖S N α - S_Λ N α‖ ≤ Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  have hS_eq : S N α =
      ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, (Λ n : ℂ) * e ((n : ℝ) * α) := by
    unfold S
    have hset : (Finset.range (N + 1)).filter Nat.Prime = (Finset.Icc 1 N).filter Nat.Prime := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨hn, hp⟩; exact ⟨⟨hp.one_le, by omega⟩, hp⟩
      · rintro ⟨⟨_, hn⟩, hp⟩; exact ⟨by omega, hp⟩
    rw [hset]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  have hsub : S N α - S_Λ N α =
      - ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime), (Λ n : ℂ) * e ((n : ℝ) * α) := by
    rw [hS_eq, S_Λ, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime]
    ring
  rw [hsub, norm_neg]
  have htri :
      ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime), (Λ n : ℂ) * e ((n : ℝ) * α)‖ ≤
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime), Λ n := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, norm_e, mul_one, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hpsi_theta :
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime), Λ n =
        RHDirect.chebyshevPsi (N : ℝ) - Stage2DirichletAP.chebyshevTheta (N : ℝ) := by
    unfold RHDirect.chebyshevPsi Stage2DirichletAP.chebyshevTheta
    rw [Nat.floor_natCast]
    have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
    have htheta :
        ∑ n ∈ insert 0 (Finset.Icc 1 N), (if n.Prime then Real.log (n : ℝ) else 0) =
          ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, Λ n := by
      rw [Finset.sum_insert (by simp), if_neg Nat.not_prime_zero, zero_add, ← Finset.sum_filter]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
    rw [htheta, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime]
    ring
  refine htri.trans ?_
  rw [hpsi_theta]
  exact (Stage2DirichletAP.chebyshevPsi_sub_chebyshevTheta_bounds (Nat.one_le_cast.mpr hN)).2

/-! ## Section 3: Distance to Nearest Integer, Linear Exponential Sum, & Reciprocal-Distance Lemmas -/

/-- Distance from `x : ℝ` to the nearest integer: `‖x‖_{ℝ/ℤ} = |x - round x|`. -/
def distInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

theorem distInt_nonneg (x : ℝ) : 0 ≤ distInt x := abs_nonneg _

theorem distInt_le_half (x : ℝ) : distInt x ≤ 1 / 2 := abs_sub_round x

theorem distInt_le_abs_sub_int (x : ℝ) (k : ℤ) : distInt x ≤ |x - (k : ℝ)| := by
  unfold distInt
  by_cases h : k = round x
  · rw [h]
  · have hdiff : (1 : ℝ) ≤ |(round x : ℝ) - (k : ℝ)| := by
      have hne : (round x - k : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      have h1 : (1 : ℤ) ≤ |round x - k| := Int.one_le_abs hne
      have h2 : (1 : ℝ) ≤ ((|round x - k| : ℤ) : ℝ) := by exact_mod_cast h1
      simpa [Int.cast_abs] using h2
    have htri : |(round x : ℝ) - (k : ℝ)| ≤ |x - (round x : ℝ)| + |x - (k : ℝ)| := by
      have heq : (round x : ℝ) - (k : ℝ) = (x - (k : ℝ)) - (x - (round x : ℝ)) := by ring
      rw [heq]
      linarith [abs_sub (x - (k : ℝ)) (x - (round x : ℝ))]
    have hhalf := abs_sub_round x
    linarith

theorem distInt_add_int (x : ℝ) (k : ℤ) : distInt (x + (k : ℝ)) = distInt x := by
  unfold distInt
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

theorem distInt_sub_int (x : ℝ) (k : ℤ) : distInt (x - (k : ℝ)) = distInt x := by
  have h := distInt_add_int x (-k)
  simpa [sub_eq_add_neg] using h

theorem distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  refine le_antisymm ?_ ?_
  · calc distInt (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := distInt_le_abs_sub_int (-x) (-round x)
      _ = |-(x - (round x : ℝ))| := by push_cast; congr 1; ring
      _ = distInt x := abs_neg _
  · calc distInt x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := distInt_le_abs_sub_int x (-round (-x))
      _ = |-((-x) - (round (-x) : ℝ))| := by push_cast; congr 1; ring
      _ = distInt (-x) := abs_neg _

theorem distInt_triangle_sub (x y : ℝ) : distInt x - |y| ≤ distInt (x + y) := by
  set k : ℤ := round (x + y)
  have h1 : distInt x ≤ |x - (k : ℝ)| := distInt_le_abs_sub_int x k
  have h2 : |x - (k : ℝ)| ≤ |x + y - (k : ℝ)| + |y| := by
    have : x - (k : ℝ) = (x + y - (k : ℝ)) - y := by ring
    rw [this]
    exact abs_sub _ _
  have h3 : |x + y - (k : ℝ)| = distInt (x + y) := rfl
  linarith

/-- Safe capped exponential-sum bound `min(B, 1 / (2 ‖x‖_{ℝ/ℤ}))` (equals `B` when `‖x‖_{ℝ/ℤ} = 0`). -/
def expBound (B : ℝ) (x : ℝ) : ℝ :=
  if distInt x = 0 then B else min B (1 / (2 * distInt x))

theorem expBound_nonneg {B : ℝ} (hB : 0 ≤ B) (x : ℝ) : 0 ≤ expBound B x := by
  unfold expBound
  split_ifs with h
  · exact hB
  · exact le_min hB (by positivity [distInt_nonneg x])

theorem expBound_le_cap (B : ℝ) (x : ℝ) : expBound B x ≤ B := by
  unfold expBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem expBound_le_inv {B x : ℝ} (hx : 0 < distInt x) :
    expBound B x ≤ 1 / (2 * distInt x) := by
  unfold expBound
  rw [if_neg hx.ne']
  exact min_le_right _ _

theorem expBound_mono_cap {B₁ B₂ : ℝ} (h : B₁ ≤ B₂) (x : ℝ) :
    expBound B₁ x ≤ expBound B₂ x := by
  unfold expBound
  split_ifs
  · exact h
  · exact min_le_min_right _ h

theorem expBound_neg (B : ℝ) (x : ℝ) : expBound B (-x) = expBound B x := by
  unfold expBound
  rw [distInt_neg]

/-- Helper: sum of a nonnegative function over a `biUnion` is bounded by the double sum. -/
private theorem sum_biUnion_le_sum_sum {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion : ∑ b ∈ t a ∪ s.biUnion t, f b ≤
        ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hinter : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := Finset.sum_nonneg fun b _ => hf b
      linarith
    linarith

/-- Lower bound `4 · distInt α ≤ ‖e(α) - 1‖` via Jordan's inequality `2t/π ≤ sin t`. -/
theorem four_mul_distInt_le_norm_e_sub_one (α : ℝ) :
    4 * distInt α ≤ ‖e α - 1‖ := by
  set t : ℝ := α - (round α : ℝ) with ht_def
  have he_eq : e α = e t := by
    have hα : α = t + (round α : ℝ) := by simp only [ht_def]; ring
    rw [hα, e_add, e_intCast, mul_one]
  rw [he_eq]
  have hfac : e t - 1 = e (t / 2) * (e (t / 2) - e (-(t / 2))) := by
    rw [mul_sub, ← e_add, ← e_add]
    have h1 : t / 2 + t / 2 = t := by ring
    have h2 : t / 2 + -(t / 2) = 0 := by ring
    rw [h1, h2, e_zero]
  have hsin_eq : e (t / 2) - e (-(t / 2)) = (2 * Real.sin (Real.pi * t) : ℂ) * Complex.I := by
    simp only [e]
    rw [show (↑(2 * Real.pi * (t / 2)) : ℂ) * Complex.I = ((Real.pi * t : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
        show (↑(2 * Real.pi * -(t / 2)) : ℂ) * Complex.I = ((-(Real.pi * t) : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hfac, norm_mul, norm_e, one_mul, hsin_eq, norm_mul, Complex.norm_I, mul_one,
    show (2 * Real.sin (Real.pi * t) : ℂ) = ((2 * Real.sin (Real.pi * t) : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have habs_t : |t| = distInt α := rfl
  have ht_le : |t| ≤ 1 / 2 := distInt_le_half α
  have harg_nn : 0 ≤ Real.pi * |t| := mul_nonneg hpi_pos.le (abs_nonneg _)
  have harg_le : Real.pi * |t| ≤ Real.pi / 2 := by nlinarith
  have hjordan : 2 / Real.pi * (Real.pi * |t|) ≤ Real.sin (Real.pi * |t|) :=
    Real.mul_le_sin harg_nn harg_le
  have hsin_nn : 0 ≤ Real.sin (Real.pi * |t|) :=
    Real.sin_nonneg_of_nonneg_of_le_pi harg_nn (by linarith)
  have hsin_abs : |Real.sin (Real.pi * t)| = Real.sin (Real.pi * |t|) := by
    rcases le_or_gt 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0, abs_of_nonneg (by rwa [abs_of_nonneg ht0] at hsin_nn)]
    · have h1 : Real.sin (Real.pi * |t|) = -Real.sin (Real.pi * t) := by
        rw [abs_of_neg ht0, mul_neg, Real.sin_neg]
      rw [h1] at hsin_nn ⊢
      exact abs_of_nonpos (by linarith)
  rw [hsin_abs, ← habs_t]
  have hsimp : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
    field_simp [hpi_pos.ne']
  linarith

/-- Telescoping identity for geometric exponential sums on `Icc a b`. -/
private theorem mul_sum_e_Icc (a b : ℕ) (hab : a ≤ b) (α : ℝ) :
    (e α - 1) * ∑ n ∈ Finset.Icc a b, e ((n : ℝ) * α) =
      e (((b + 1 : ℕ) : ℝ) * α) - e ((a : ℝ) * α) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero =>
    simp only [add_zero, Finset.Icc_self, Finset.sum_singleton]
    rw [sub_mul, one_mul, ← e_add]
    congr 1; congr 1; push_cast; ring
  | succ k ih =>
    have hIcc : Finset.Icc a (a + (k + 1)) =
        insert (a + (k + 1)) (Finset.Icc a (a + k)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), mul_add, ih (by omega)]
    have hstep : (e α - 1) * e (((a + (k + 1) : ℕ) : ℝ) * α) =
        e (((a + (k + 1) + 1 : ℕ) : ℝ) * α) - e (((a + (k + 1) : ℕ) : ℝ) * α) := by
      rw [sub_mul, one_mul, ← e_add]
      congr 1; congr 1; push_cast; ring
    rw [hstep]
    have hEq : a + k + 1 = a + (k + 1) := by omega
    rw [hEq]
    ring

/-- Linear exponential sum bound on any integer interval `Icc a b`:
`‖∑_{n ∈ Icc a b} e(n α)‖ ≤ expBound ((Icc a b).card) α`. -/
theorem norm_sum_e_Icc_le (a b : ℕ) (α : ℝ) :
    ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * α)‖ ≤ expBound ((Finset.Icc a b).card : ℝ) α := by
  have htriv : ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * α)‖ ≤ ((Finset.Icc a b).card : ℝ) := by
    calc ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * α)‖
        ≤ ∑ n ∈ Finset.Icc a b, ‖e ((n : ℝ) * α)‖ := norm_sum_le _ _
      _ = ∑ _n ∈ Finset.Icc a b, (1 : ℝ) := Finset.sum_congr rfl fun n _ => norm_e _
      _ = ((Finset.Icc a b).card : ℝ) := by simp
  unfold expBound
  split_ifs with h0
  · exact htriv
  · refine le_min htriv ?_
    have hpos : 0 < distInt α := lt_of_le_of_ne (distInt_nonneg α) (Ne.symm h0)
    by_cases hab : a ≤ b
    · have htele := mul_sum_e_Icc a b hab α
      have hnorm_prod : ‖e α - 1‖ * ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * α)‖ ≤ 2 := by
        rw [← norm_mul, htele]
        calc ‖e (((b + 1 : ℕ) : ℝ) * α) - e ((a : ℝ) * α)‖
            ≤ ‖e (((b + 1 : ℕ) : ℝ) * α)‖ + ‖e ((a : ℝ) * α)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_e, norm_e]; norm_num
      have hlb : 4 * distInt α ≤ ‖e α - 1‖ := four_mul_distInt_le_norm_e_sub_one α
      have h4 : (4 * distInt α) * ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * α)‖ ≤ 2 :=
        (mul_le_mul_of_nonneg_right hlb (norm_nonneg _)).trans hnorm_prod
      rw [le_div_iff₀ (by positivity : 0 < 2 * distInt α)]
      linarith
    · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty hab
      rw [hempty, Finset.sum_empty, norm_zero]
      positivity

/-- Elementary harmonic sum upper bound: `∑_{k=1}^M 1 / k ≤ 1 + Real.log M` for `M ≥ 1`. -/
theorem harmonic_Icc_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (M : ℝ) := by
  induction M with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have h1 : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = - (1 / ((m + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp [hm1_pos.ne']; ring
        have hlog := Real.log_le_sub_one_of_pos (div_pos hm_pos hm1_pos)
        rw [Real.log_div hm_pos.ne' hm1_pos.ne', h1] at hlog
        linarith
      linarith [ih hm]

/-- **One-block Reciprocal-Distance Lemma**: for `q ≥ 1`, `Nat.Coprime a.natAbs q`,
`|α - a / q| ≤ 1 / q²`, any starting shift `h₀ : ℕ`, and any cap `B ≥ 0`:
`∑_{r=0}^{q-1} expBound B ((h₀ + r) α) ≤ 3 B + q (1 + log q)`. -/
theorem sum_expBound_block_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : Nat.Coprime a.natAbs q)
    {α B : ℝ} (hB : 0 ≤ B) (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) (h₀ : ℕ) :
    ∑ r ∈ Finset.range q, expBound B (((h₀ + r : ℕ) : ℝ) * α) ≤
      3 * B + (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hlog_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hq)
  by_cases hq3 : q ≤ 3
  · calc ∑ r ∈ Finset.range q, expBound B (((h₀ + r : ℕ) : ℝ) * α)
        ≤ ∑ _r ∈ Finset.range q, B :=
          Finset.sum_le_sum fun r _ => expBound_le_cap B _
      _ = (q : ℝ) * B := by simp
      _ ≤ 3 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hq3) hB
      _ ≤ 3 * B + (q : ℝ) * (1 + Real.log (q : ℝ)) := by nlinarith
  push Not at hq3
  set β : ℝ := α - (a : ℝ) / (q : ℝ) with hβ_def
  have hβ_le : |β| ≤ 1 / (q : ℝ) ^ 2 := happrox
  set x₀ : ℝ := ((h₀ : ℝ) + ((q - 1 : ℕ) : ℝ) / 2) * β with hx₀_def
  set c : ℤ := round ((q : ℝ) * x₀) with hc_def
  have hx₀_err : |x₀ - (c : ℝ) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
    have h1 : |(q : ℝ) * x₀ - (c : ℝ)| ≤ 1 / 2 := abs_sub_round ((q : ℝ) * x₀)
    have h2 : |x₀ - (c : ℝ) / (q : ℝ)| = |(q : ℝ) * x₀ - (c : ℝ)| / (q : ℝ) := by
      calc |x₀ - (c : ℝ) / (q : ℝ)|
          = |((q : ℝ) * x₀ - (c : ℝ)) / (q : ℝ)| := by congr 1; field_simp [hq_pos.ne']
        _ = |(q : ℝ) * x₀ - (c : ℝ)| / (q : ℝ) := by rw [abs_div, abs_of_pos hq_pos]
    rw [h2]
    calc |(q : ℝ) * x₀ - (c : ℝ)| / (q : ℝ)
        ≤ (1 / 2) / (q : ℝ) := div_le_div_of_nonneg_right h1 hq_pos.le
      _ = 1 / (2 * (q : ℝ)) := by ring
  let j : ℕ → ℕ := fun r => ((((h₀ + r : ℕ) : ℤ) * a + c) % (q : ℤ)).toNat
  have hj_lt : ∀ r, j r < q := by
    intro r
    have hmod_lt : (((h₀ + r : ℕ) : ℤ) * a + c) % (q : ℤ) < (q : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hq)
    have hmod_nn : 0 ≤ (((h₀ + r : ℕ) : ℤ) * a + c) % (q : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast (show q ≠ 0 by omega))
    exact (Int.toNat_lt hmod_nn).mpr hmod_lt
  have hj_inj : Set.InjOn j (Finset.range q : Set ℕ) := by
    intro r₁ hr₁ r₂ hr₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at hr₁ hr₂
    have hnn₁ : 0 ≤ (((h₀ + r₁ : ℕ) : ℤ) * a + c) % (q : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast (show q ≠ 0 by omega))
    have hnn₂ : 0 ≤ (((h₀ + r₂ : ℕ) : ℤ) * a + c) % (q : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast (show q ≠ 0 by omega))
    have hmod_eq : (((h₀ + r₁ : ℕ) : ℤ) * a + c) % (q : ℤ) =
        (((h₀ + r₂ : ℕ) : ℤ) * a + c) % (q : ℤ) := by
      have h1 : (j r₁ : ℤ) = (((h₀ + r₁ : ℕ) : ℤ) * a + c) % (q : ℤ) :=
        Int.toNat_of_nonneg hnn₁
      have h2 : (j r₂ : ℤ) = (((h₀ + r₂ : ℕ) : ℤ) * a + c) % (q : ℤ) :=
        Int.toNat_of_nonneg hnn₂
      rw [← h1, ← h2, heq]
    have hdvd : (q : ℤ) ∣ (((r₁ : ℤ) - (r₂ : ℤ)) * a) := by
      have hdiff : (((h₀ + r₁ : ℕ) : ℤ) * a + c) - (((h₀ + r₂ : ℕ) : ℤ) * a + c) =
          ((r₁ : ℤ) - (r₂ : ℤ)) * a := by push_cast; ring
      rw [← hdiff]
      exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmod_eq, sub_self, Int.zero_emod])
    have hdvd_nat : q ∣ ((r₁ : ℤ) - (r₂ : ℤ)).natAbs * a.natAbs := by
      have h1 := Int.natCast_dvd.mp hdvd
      rwa [Int.natAbs_mul] at h1
    have hdvd_r : q ∣ ((r₁ : ℤ) - (r₂ : ℤ)).natAbs :=
      (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right hdvd_nat
    have hlt_q : ((r₁ : ℤ) - (r₂ : ℤ)).natAbs < q := by omega
    have hzero : ((r₁ : ℤ) - (r₂ : ℤ)).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_r hlt_q
    omega
  let g : ℕ → ℝ := fun u =>
    if u ≤ 1 ∨ q - 1 ≤ u then B
    else (q : ℝ) / (2 * ((min u (q - u) - 1 : ℕ) : ℝ))
  have hpoint : ∀ r ∈ Finset.range q, expBound B (((h₀ + r : ℕ) : ℝ) * α) ≤ g (j r) := by
    intro r hr
    have hr_lt : r < q := Finset.mem_range.mp hr
    dsimp only [g]
    split_ifs with hbad
    · exact expBound_le_cap B _
    · push Not at hbad
      obtain ⟨hj2, hjq2⟩ := hbad
      have hju_ge2 : 2 ≤ min (j r) (q - j r) := by omega
      set b_r : ℤ := ((h₀ + r : ℕ) : ℤ) * a + c
      set k_int : ℤ := b_r / (q : ℤ)
      set ε_r : ℝ := (x₀ - (c : ℝ) / (q : ℝ)) + ((r : ℝ) - ((q - 1 : ℕ) : ℝ) / 2) * β
      have hdecomp : ((h₀ + r : ℕ) : ℝ) * α = (k_int : ℝ) + ((j r : ℝ) / (q : ℝ) + ε_r) := by
        have hmod_nn : 0 ≤ b_r % (q : ℤ) :=
          Int.emod_nonneg _ (by exact_mod_cast (show q ≠ 0 by omega))
        have hbr_eq : (b_r : ℝ) = (q : ℝ) * (k_int : ℝ) + (j r : ℝ) := by
          have h1 : (j r : ℤ) = b_r % (q : ℤ) := Int.toNat_of_nonneg hmod_nn
          have h2 : (q : ℤ) * (b_r / (q : ℤ)) + b_r % (q : ℤ) = b_r := Int.mul_ediv_add_emod b_r q
          have h3 : (b_r : ℤ) = (q : ℤ) * k_int + (j r : ℤ) := by rw [h1]; linarith
          exact_mod_cast h3
        have hα_eq : α = (a : ℝ) / (q : ℝ) + β := by simp only [hβ_def]; ring
        rw [hα_eq]
        have hbr_cast : (b_r : ℝ) = ((h₀ + r : ℕ) : ℝ) * (a : ℝ) + (c : ℝ) := by
          simp only [b_r]; push_cast; ring
        have h1 : ((h₀ + r : ℕ) : ℝ) * ((a : ℝ) / (q : ℝ) + β) =
            (b_r : ℝ) / (q : ℝ) + ε_r := by
          simp only [ε_r, hx₀_def, hbr_cast]
          push_cast
          field_simp [hq_pos.ne']
          ring
        rw [h1, hbr_eq]
        field_simp [hq_pos.ne']
        ring
      have hε_lt : |ε_r| < 1 / (q : ℝ) := by
        have hr_half : |(r : ℝ) - ((q - 1 : ℕ) : ℝ) / 2| ≤ ((q - 1 : ℕ) : ℝ) / 2 := by
          rw [abs_le]
          have hr_le : (r : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show r ≤ q - 1 by omega)
          constructor <;> linarith
        have hterm2 : |((r : ℝ) - ((q - 1 : ℕ) : ℝ) / 2) * β| < 1 / (2 * (q : ℝ)) := by
          rw [abs_mul]
          calc |(r : ℝ) - ((q - 1 : ℕ) : ℝ) / 2| * |β|
              ≤ (((q - 1 : ℕ) : ℝ) / 2) * (1 / (q : ℝ) ^ 2) :=
                mul_le_mul hr_half hβ_le (abs_nonneg _) (by positivity)
            _ < ((q : ℝ) / 2) * (1 / (q : ℝ) ^ 2) := by
                apply mul_lt_mul_of_pos_right _ (by positivity)
                have : ((q - 1 : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast (show q - 1 < q by omega)
                linarith
            _ = 1 / (2 * (q : ℝ)) := by field_simp [hq_pos.ne']
        calc |ε_r| ≤ |x₀ - (c : ℝ) / (q : ℝ)| + |((r : ℝ) - ((q - 1 : ℕ) : ℝ) / 2) * β| :=
              abs_add_le _ _
          _ < 1 / (2 * (q : ℝ)) + 1 / (2 * (q : ℝ)) := by linarith
          _ = 1 / (q : ℝ) := by ring
      set d_r : ℕ := min (j r) (q - j r)
      have hdist_jr : (d_r : ℝ) / (q : ℝ) ≤ distInt ((j r : ℝ) / (q : ℝ)) := by
        unfold distInt
        set k₀ : ℤ := round ((j r : ℝ) / (q : ℝ))
        by_cases hk0 : k₀ ≤ 0
        · have h1 : (k₀ : ℝ) ≤ 0 := by exact_mod_cast hk0
          have h2 : (d_r : ℝ) ≤ (j r : ℝ) := Nat.cast_le.mpr (min_le_left _ _)
          have h3 : (d_r : ℝ) / (q : ℝ) ≤ (j r : ℝ) / (q : ℝ) - (k₀ : ℝ) := by
            have := div_le_div_of_nonneg_right h2 hq_pos.le
            linarith
          exact h3.trans (le_abs_self _)
        · have hk1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ k₀ by omega)
          have h2 : (d_r : ℝ) ≤ ((q - j r : ℕ) : ℝ) := Nat.cast_le.mpr (min_le_right _ _)
          have h3 : ((q - j r : ℕ) : ℝ) / (q : ℝ) = 1 - (j r : ℝ) / (q : ℝ) := by
            rw [Nat.cast_sub (hj_lt r).le]
            field_simp [hq_pos.ne']
          have h4 : (d_r : ℝ) / (q : ℝ) ≤ (k₀ : ℝ) - (j r : ℝ) / (q : ℝ) := by
            have := div_le_div_of_nonneg_right h2 hq_pos.le
            linarith
          exact h4.trans (by rw [abs_sub_comm]; exact le_abs_self _)
      have hdist_lb : ((d_r - 1 : ℕ) : ℝ) / (q : ℝ) <
          distInt (((h₀ + r : ℕ) : ℝ) * α) := by
        rw [hdecomp, add_comm (k_int : ℝ), distInt_add_int]
        have htri := distInt_triangle_sub ((j r : ℝ) / (q : ℝ)) ε_r
        have hcast : ((d_r - 1 : ℕ) : ℝ) / (q : ℝ) = (d_r : ℝ) / (q : ℝ) - 1 / (q : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ d_r)]
          push_cast; ring
        linarith
      have hdm1_pos : (0 : ℝ) < ((d_r - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdist_pos : 0 < distInt (((h₀ + r : ℕ) : ℝ) * α) :=
        lt_trans (div_pos hdm1_pos hq_pos) hdist_lb
      calc expBound B (((h₀ + r : ℕ) : ℝ) * α)
          ≤ 1 / (2 * distInt (((h₀ + r : ℕ) : ℝ) * α)) := expBound_le_inv hdist_pos
        _ ≤ 1 / (2 * (((d_r - 1 : ℕ) : ℝ) / (q : ℝ))) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = (q : ℝ) / (2 * ((d_r - 1 : ℕ) : ℝ)) := by
            field_simp [hq_pos.ne', hdm1_pos.ne']
  have hsum_eq : ∑ r ∈ Finset.range q, g (j r) = ∑ u ∈ Finset.range q, g u := by
    refine Finset.sum_bij (fun r _ => j r) (fun r _ => Finset.mem_range.mpr (hj_lt r))
      (fun r₁ hr₁ r₂ hr₂ h => hj_inj hr₁ hr₂ h) ?_ (fun _ _ => rfl)
    have hcard_eq : ((Finset.range q).image j).card = (Finset.range q).card :=
      Finset.card_image_of_injOn hj_inj
    have hsub : (Finset.range q).image j ⊆ Finset.range q := by
      intro u hu
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_range.mpr (hj_lt r)
    have himg : (Finset.range q).image j = Finset.range q :=
      Finset.eq_of_subset_of_card_le hsub hcard_eq.ge
    intro u hu
    rw [← himg] at hu
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨r, hr, rfl⟩
  have hsum_g : ∑ u ∈ Finset.range q, g u ≤ 3 * B + (q : ℝ) * (1 + Real.log (q : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun u => u ≤ 1 ∨ q - 1 ≤ u)]
    have hbad_sum : ∑ u ∈ (Finset.range q).filter (fun u => u ≤ 1 ∨ q - 1 ≤ u), g u ≤ 3 * B := by
      have hsub : (Finset.range q).filter (fun u => u ≤ 1 ∨ q - 1 ≤ u) ⊆ {0, 1, q - 1} := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton] at hu ⊢
        omega
      have hcard_le : ((Finset.range q).filter (fun u => u ≤ 1 ∨ q - 1 ≤ u)).card ≤ 3 := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_insert_le (0 : ℕ) ({1, q - 1} : Finset ℕ)
        have h3 := Finset.card_insert_le (1 : ℕ) ({q - 1} : Finset ℕ)
        simp only [Finset.card_singleton] at h3
        omega
      calc ∑ u ∈ (Finset.range q).filter (fun u => u ≤ 1 ∨ q - 1 ≤ u), g u
          = ∑ _u ∈ (Finset.range q).filter (fun u => u ≤ 1 ∨ q - 1 ≤ u), B := by
            refine Finset.sum_congr rfl fun u hu => ?_
            simp only [g, if_pos (Finset.mem_filter.mp hu).2]
        _ = (((Finset.range q).filter (fun u => u ≤ 1 ∨ q - 1 ≤ u)).card : ℝ) * B := by simp
        _ ≤ 3 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) hB
    have hgood_sum :
        ∑ u ∈ (Finset.range q).filter (fun u => ¬(u ≤ 1 ∨ q - 1 ≤ u)), g u ≤
          (q : ℝ) * (1 + Real.log (q : ℝ)) := by
      set G := (Finset.range q).filter (fun u => ¬(u ≤ 1 ∨ q - 1 ≤ u))
      rw [← Finset.sum_filter_add_sum_filter_not G (fun u => u ≤ q / 2)]
      have hL : ∑ u ∈ G.filter (fun u => u ≤ q / 2), g u ≤
          ((q : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 q, (1 : ℝ) / (k : ℝ) := by
        have hrew : ∑ u ∈ G.filter (fun u => u ≤ q / 2), g u =
            ((q : ℝ) / 2) * ∑ u ∈ G.filter (fun u => u ≤ q / 2), (1 : ℝ) / ((u - 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          simp only [G, Finset.mem_filter, Finset.mem_range] at hu
          have hmin : min u (q - u) = u := min_eq_left (by omega)
          simp only [g, if_neg hu.1.2, hmin]
          ring
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hinj : Set.InjOn (fun u => u - 1) (G.filter (fun u => u ≤ q / 2) : Set ℕ) := by
          intro u₁ hu₁ u₂ hu₂ h
          dsimp only at h
          simp only [G, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hu₁ hu₂
          omega
        have himg_sub : (G.filter (fun u => u ≤ q / 2)).image (fun u : ℕ => u - 1) ⊆ Finset.Icc 1 q := by
          intro k hk
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
          simp only [G, Finset.mem_filter, Finset.mem_range] at hu
          simp only [Finset.mem_Icc]; omega
        calc ∑ u ∈ G.filter (fun u => u ≤ q / 2), (1 : ℝ) / ((u - 1 : ℕ) : ℝ)
            = ∑ k ∈ (G.filter (fun u => u ≤ q / 2)).image (fun u : ℕ => u - 1), (1 : ℝ) / (k : ℝ) :=
              (Finset.sum_image (f := fun k : ℕ => (1 : ℝ) / (k : ℝ))
                (fun a ha b hb h => hinj ha hb h)).symm
          _ ≤ ∑ k ∈ Finset.Icc 1 q, (1 : ℝ) / (k : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity
      have hR : ∑ u ∈ G.filter (fun u => ¬ u ≤ q / 2), g u ≤
          ((q : ℝ) / 2) * ∑ k ∈ Finset.Icc 1 q, (1 : ℝ) / (k : ℝ) := by
        have hrew : ∑ u ∈ G.filter (fun u => ¬ u ≤ q / 2), g u =
            ((q : ℝ) / 2) * ∑ u ∈ G.filter (fun u => ¬ u ≤ q / 2), (1 : ℝ) / ((q - u - 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          simp only [G, Finset.mem_filter, Finset.mem_range] at hu
          have hmin : min u (q - u) = q - u := min_eq_right (by omega)
          simp only [g, if_neg hu.1.2, hmin]
          ring
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hinj : Set.InjOn (fun u => q - u - 1) (G.filter (fun u => ¬ u ≤ q / 2) : Set ℕ) := by
          intro u₁ hu₁ u₂ hu₂ h
          dsimp only at h
          simp only [G, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hu₁ hu₂
          omega
        have himg_sub :
            (G.filter (fun u => ¬ u ≤ q / 2)).image (fun u => q - u - 1) ⊆ Finset.Icc 1 q := by
          intro k hk
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
          simp only [G, Finset.mem_filter, Finset.mem_range] at hu
          simp only [Finset.mem_Icc]; omega
        calc ∑ u ∈ G.filter (fun u => ¬ u ≤ q / 2), (1 : ℝ) / ((q - u - 1 : ℕ) : ℝ)
            = ∑ k ∈ (G.filter (fun u => ¬ u ≤ q / 2)).image (fun u => q - u - 1),
                (1 : ℝ) / (k : ℝ) :=
              (Finset.sum_image (f := fun k : ℕ => (1 : ℝ) / (k : ℝ))
                (fun a ha b hb h => hinj ha hb h)).symm
          _ ≤ ∑ k ∈ Finset.Icc 1 q, (1 : ℝ) / (k : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity
      have hharm := harmonic_Icc_le q hq
      nlinarith
    linarith
  calc ∑ r ∈ Finset.range q, expBound B (((h₀ + r : ℕ) : ℝ) * α)
      ≤ ∑ r ∈ Finset.range q, g (j r) := Finset.sum_le_sum hpoint
    _ = ∑ u ∈ Finset.range q, g u := hsum_eq
    _ ≤ 3 * B + (q : ℝ) * (1 + Real.log (q : ℝ)) := hsum_g

/-- **Constant-Cap Reciprocal-Distance Sum** (for Type II):
`∑_{h=1}^H expBound B (h α) ≤ 3 (H / q + 1) B + (H + q) (1 + log q)`. -/
theorem sum_expBound_const_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : Nat.Coprime a.natAbs q)
    {α B : ℝ} (hB : 0 ≤ B) (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) (H : ℕ) :
    ∑ h ∈ Finset.Icc 1 H, expBound B ((h : ℝ) * α) ≤
      3 * ((H : ℝ) / (q : ℝ) + 1) * B + ((H : ℝ) + (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hcover : Finset.Icc 1 H ⊆
      (Finset.range (H / q + 1)).biUnion (fun k => (Finset.range q).image (fun r => 1 + k * q + r)) := by
    intro h hh
    simp only [Finset.mem_Icc] at hh
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    refine ⟨(h - 1) / q, ?_, (h - 1) % q, Nat.mod_lt _ hq, ?_⟩
    · exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
    · have hdm := Nat.div_add_mod (h - 1) q
      rw [mul_comm] at hdm
      omega
  have hle_biUnion :
      ∑ h ∈ Finset.Icc 1 H, expBound B ((h : ℝ) * α) ≤
        ∑ k ∈ Finset.range (H / q + 1),
          ∑ r ∈ Finset.range q, expBound B (((1 + k * q + r : ℕ) : ℝ) * α) := by
    calc ∑ h ∈ Finset.Icc 1 H, expBound B ((h : ℝ) * α)
        ≤ ∑ h ∈ (Finset.range (H / q + 1)).biUnion
              (fun k => (Finset.range q).image (fun r => 1 + k * q + r)),
            expBound B ((h : ℝ) * α) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => expBound_nonneg hB _
      _ ≤ ∑ k ∈ Finset.range (H / q + 1),
            ∑ h ∈ (Finset.range q).image (fun r => 1 + k * q + r),
              expBound B ((h : ℝ) * α) :=
          sum_biUnion_le_sum_sum _ _ (fun h : ℕ => expBound B ((h : ℝ) * α))
            (fun _ => expBound_nonneg hB _)
      _ = ∑ k ∈ Finset.range (H / q + 1),
            ∑ r ∈ Finset.range q, expBound B (((1 + k * q + r : ℕ) : ℝ) * α) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_image]
          intro r₁ _ r₂ _ h; dsimp only at h; omega
  have hblock := fun k => sum_expBound_block_le hq hcop hB happrox (1 + k * q)
  have hsum_blocks :
      ∑ k ∈ Finset.range (H / q + 1),
        ∑ r ∈ Finset.range q, expBound B (((1 + k * q + r : ℕ) : ℝ) * α) ≤
          ((H / q + 1 : ℕ) : ℝ) * (3 * B + (q : ℝ) * (1 + Real.log (q : ℝ))) := by
    calc ∑ k ∈ Finset.range (H / q + 1),
          ∑ r ∈ Finset.range q, expBound B (((1 + k * q + r : ℕ) : ℝ) * α)
        ≤ ∑ _k ∈ Finset.range (H / q + 1), (3 * B + (q : ℝ) * (1 + Real.log (q : ℝ))) :=
          Finset.sum_le_sum fun k _ => hblock k
      _ = ((H / q + 1 : ℕ) : ℝ) * (3 * B + (q : ℝ) * (1 + Real.log (q : ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hdiv_le : ((H / q : ℕ) : ℝ) ≤ (H : ℝ) / (q : ℝ) := by
    rw [le_div_iff₀ hq_pos]
    exact_mod_cast Nat.div_mul_le_self H q
  have hdiv_mul : ((H / q + 1 : ℕ) : ℝ) * (q : ℝ) ≤ (H : ℝ) + (q : ℝ) := by
    push_cast
    have : ((H / q : ℕ) : ℝ) * (q : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.div_mul_le_self H q
    linarith
  have hlog_nn : 0 ≤ 1 + Real.log (q : ℝ) := by
    linarith [Real.log_nonneg (Nat.one_le_cast.mpr hq)]
  refine hle_biUnion.trans (hsum_blocks.trans ?_)
  have h1 : ((H / q + 1 : ℕ) : ℝ) * (3 * B) ≤ 3 * ((H : ℝ) / (q : ℝ) + 1) * B := by
    push_cast; nlinarith
  have h2 : ((H / q + 1 : ℕ) : ℝ) * ((q : ℝ) * (1 + Real.log (q : ℝ))) ≤
      ((H : ℝ) + (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hdiv_mul hlog_nn
  linarith

/-- **Hyperbolic-Cap Reciprocal-Distance Sum** (for Type I):
for `1 ≤ q`, `(a, q) = 1`, `|α - a/q| ≤ 1/q²`, `X ≥ 0`, `D ≥ 1`:
`∑_{m=1}^D expBound (X / m) (m α) ≤ (6 X / q) (1 + log (D + 1)) + (D + 3 q) (1 + log q)`. -/
theorem sum_expBound_div_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : Nat.Coprime a.natAbs q)
    {α X : ℝ} (hX : 0 ≤ X) (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2)
    {D : ℕ} (_hD : 1 ≤ D) :
    ∑ m ∈ Finset.Icc 1 D, expBound (X / (m : ℝ)) ((m : ℝ) * α) ≤
      (6 * X / (q : ℝ)) * (1 + Real.log ((D + 1 : ℕ) : ℝ)) +
        ((D : ℝ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hlogq_nn : 0 ≤ 1 + Real.log (q : ℝ) := by
    linarith [Real.log_nonneg (Nat.one_le_cast.mpr hq)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 D) (fun m => m ≤ q / 2)]
  -- Part 1: `1 ≤ m ≤ min D (q / 2)`
  have hPart1 :
      ∑ m ∈ (Finset.Icc 1 D).filter (fun m => m ≤ q / 2),
          expBound (X / (m : ℝ)) ((m : ℝ) * α) ≤
        2 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
    by_cases hq1 : q = 1
    · have hempty : (Finset.Icc 1 D).filter (fun m => m ≤ q / 2) = ∅ := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [hempty, Finset.sum_empty]
      positivity
    have hq2 : 2 ≤ q := by omega
    set S1 := (Finset.Icc 1 D).filter (fun m => m ≤ q / 2)
    set β : ℝ := α - (a : ℝ) / (q : ℝ)
    let j : ℕ → ℕ := fun m => (((m : ℤ) * a) % (q : ℤ)).toNat
    have hj_mem : ∀ m ∈ S1, j m ∈ Finset.Icc 1 (q - 1) := by
      intro m hm
      simp only [S1, Finset.mem_filter, Finset.mem_Icc] at hm
      have hmod_nn : 0 ≤ ((m : ℤ) * a) % (q : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast (show q ≠ 0 by omega))
      have hmod_lt : ((m : ℤ) * a) % (q : ℤ) < (q : ℤ) :=
        Int.emod_lt_of_pos _ (by exact_mod_cast hq)
      have hmod_ne0 : ((m : ℤ) * a) % (q : ℤ) ≠ 0 := by
        intro h0
        have hdvd : (q : ℤ) ∣ (m : ℤ) * a := Int.dvd_of_emod_eq_zero h0
        have hdvd_nat : q ∣ m * a.natAbs := by
          have h1 := Int.natCast_dvd.mp hdvd
          rwa [Int.natAbs_mul, Int.natAbs_natCast] at h1
        have hdvd_m : q ∣ m := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right hdvd_nat
        have := Nat.le_of_dvd (by omega) hdvd_m
        omega
      have hj_pos : 0 < j m := (Int.lt_toNat).mpr (by omega)
      have hj_lt_q : j m < q := (Int.toNat_lt hmod_nn).mpr hmod_lt
      simp only [Finset.mem_Icc]
      omega
    have hj_inj : Set.InjOn j (S1 : Set ℕ) := by
      intro m₁ hm₁ m₂ hm₂ heq
      simp only [S1, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm₁ hm₂
      have hnn₁ : 0 ≤ ((m₁ : ℤ) * a) % (q : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast (show q ≠ 0 by omega))
      have hnn₂ : 0 ≤ ((m₂ : ℤ) * a) % (q : ℤ) :=
        Int.emod_nonneg _ (by exact_mod_cast (show q ≠ 0 by omega))
      have hmod_eq : ((m₁ : ℤ) * a) % (q : ℤ) = ((m₂ : ℤ) * a) % (q : ℤ) := by
        have h1 : (j m₁ : ℤ) = ((m₁ : ℤ) * a) % (q : ℤ) := Int.toNat_of_nonneg hnn₁
        have h2 : (j m₂ : ℤ) = ((m₂ : ℤ) * a) % (q : ℤ) := Int.toNat_of_nonneg hnn₂
        rw [← h1, ← h2, heq]
      have hdvd : (q : ℤ) ∣ ((m₁ : ℤ) - (m₂ : ℤ)) * a := by
        have hdiff : (m₁ : ℤ) * a - (m₂ : ℤ) * a = ((m₁ : ℤ) - (m₂ : ℤ)) * a := by ring
        rw [← hdiff]
        exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmod_eq, sub_self, Int.zero_emod])
      have hdvd_nat : q ∣ ((m₁ : ℤ) - (m₂ : ℤ)).natAbs * a.natAbs := by
        have h1 := Int.natCast_dvd.mp hdvd
        rwa [Int.natAbs_mul] at h1
      have hdvd_m : q ∣ ((m₁ : ℤ) - (m₂ : ℤ)).natAbs :=
        (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right hdvd_nat
      have hlt_q : ((m₁ : ℤ) - (m₂ : ℤ)).natAbs < q := by omega
      have hzero : ((m₁ : ℤ) - (m₂ : ℤ)).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_m hlt_q
      omega
    have hpt1 : ∀ m ∈ S1, expBound (X / (m : ℝ)) ((m : ℝ) * α) ≤
        (q : ℝ) / ((min (j m) (q - j m) : ℕ) : ℝ) := by
      intro m hm
      have hjm := Finset.mem_Icc.mp (hj_mem m hm)
      have hm_le : m ≤ q / 2 := (Finset.mem_filter.mp hm).2
      set d_m : ℕ := min (j m) (q - j m)
      have hd1 : 1 ≤ d_m := by omega
      have hd_pos : (0 : ℝ) < (d_m : ℝ) := Nat.cast_pos.mpr hd1
      set k_int : ℤ := ((m : ℤ) * a) / (q : ℤ)
      have hdecomp : (m : ℝ) * α = (k_int : ℝ) + ((j m : ℝ) / (q : ℝ) + (m : ℝ) * β) := by
        have hnn : 0 ≤ ((m : ℤ) * a) % (q : ℤ) :=
          Int.emod_nonneg _ (by exact_mod_cast (show q ≠ 0 by omega))
        have hma : ((m : ℝ) * (a : ℝ)) = (q : ℝ) * (k_int : ℝ) + (j m : ℝ) := by
          have h1 : (j m : ℤ) = ((m : ℤ) * a) % (q : ℤ) := Int.toNat_of_nonneg hnn
          have h2 : (q : ℤ) * k_int + (j m : ℤ) = (m : ℤ) * a := by
            rw [h1]; exact Int.mul_ediv_add_emod ((m : ℤ) * a) q
          exact_mod_cast h2.symm
        have hα_eq : α = (a : ℝ) / (q : ℝ) + β := by simp only [β]; ring
        rw [hα_eq, mul_add, ← mul_div_assoc, hma]
        field_simp [hq_pos.ne']
        ring
      have hmβ_le : |(m : ℝ) * β| ≤ 1 / (2 * (q : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
        have hm_half : (m : ℝ) ≤ (q : ℝ) / 2 := by
          have : 2 * m ≤ q := by omega
          have : (2 : ℝ) * (m : ℝ) ≤ (q : ℝ) := by exact_mod_cast this
          linarith
        calc (m : ℝ) * |β| ≤ ((q : ℝ) / 2) * (1 / (q : ℝ) ^ 2) :=
              mul_le_mul hm_half happrox (abs_nonneg _) (by positivity)
          _ = 1 / (2 * (q : ℝ)) := by field_simp [hq_pos.ne']
      have hdist_jm : (d_m : ℝ) / (q : ℝ) ≤ distInt ((j m : ℝ) / (q : ℝ)) := by
        unfold distInt
        set k₀ : ℤ := round ((j m : ℝ) / (q : ℝ))
        by_cases hk0 : k₀ ≤ 0
        · have h1 : (k₀ : ℝ) ≤ 0 := by exact_mod_cast hk0
          have h2 : (d_m : ℝ) ≤ (j m : ℝ) := Nat.cast_le.mpr (min_le_left _ _)
          have h3 := div_le_div_of_nonneg_right h2 hq_pos.le
          exact (by linarith : (d_m : ℝ) / (q : ℝ) ≤ (j m : ℝ) / (q : ℝ) - (k₀ : ℝ)).trans
            (le_abs_self _)
        · have hk1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ k₀ by omega)
          have h2 : (d_m : ℝ) ≤ ((q - j m : ℕ) : ℝ) := Nat.cast_le.mpr (min_le_right _ _)
          have h3 : ((q - j m : ℕ) : ℝ) / (q : ℝ) = 1 - (j m : ℝ) / (q : ℝ) := by
            rw [Nat.cast_sub (by omega : j m ≤ q)]; field_simp [hq_pos.ne']
          have h4 := div_le_div_of_nonneg_right h2 hq_pos.le
          exact (by linarith : (d_m : ℝ) / (q : ℝ) ≤ (k₀ : ℝ) - (j m : ℝ) / (q : ℝ)).trans
            (by rw [abs_sub_comm]; exact le_abs_self _)
      have hdist_lb : (d_m : ℝ) / (2 * (q : ℝ)) ≤ distInt ((m : ℝ) * α) := by
        rw [hdecomp, add_comm (k_int : ℝ), distInt_add_int]
        have htri := distInt_triangle_sub ((j m : ℝ) / (q : ℝ)) ((m : ℝ) * β)
        have hd_ge1 : (1 : ℝ) ≤ (d_m : ℝ) := Nat.one_le_cast.mpr hd1
        have hcalc : (d_m : ℝ) / (2 * (q : ℝ)) ≤ (d_m : ℝ) / (q : ℝ) - 1 / (2 * (q : ℝ)) := by
          have : (d_m : ℝ) / (q : ℝ) - (d_m : ℝ) / (2 * (q : ℝ)) = (d_m : ℝ) / (2 * (q : ℝ)) := by ring
          have h1 : 1 / (2 * (q : ℝ)) ≤ (d_m : ℝ) / (2 * (q : ℝ)) :=
            div_le_div_of_nonneg_right hd_ge1 (by positivity)
          linarith
        linarith
      have hdist_pos : 0 < distInt ((m : ℝ) * α) :=
        lt_of_lt_of_le (by positivity) hdist_lb
      calc expBound (X / (m : ℝ)) ((m : ℝ) * α)
          ≤ 1 / (2 * distInt ((m : ℝ) * α)) := expBound_le_inv hdist_pos
        _ ≤ 1 / (2 * ((d_m : ℝ) / (2 * (q : ℝ)))) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = (q : ℝ) / (d_m : ℝ) := by field_simp [hq_pos.ne', hd_pos.ne']
    have hsum_Icc : ∑ u ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((min u (q - u) : ℕ) : ℝ) ≤
        2 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (q - 1)) (fun u => u ≤ q / 2)]
      have hL : ∑ u ∈ (Finset.Icc 1 (q - 1)).filter (fun u => u ≤ q / 2),
            (q : ℝ) / ((min u (q - u) : ℕ) : ℝ) ≤ (q : ℝ) * ∑ d ∈ Finset.Icc 1 q, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]
        calc ∑ u ∈ (Finset.Icc 1 (q - 1)).filter (fun u => u ≤ q / 2),
              (q : ℝ) / ((min u (q - u) : ℕ) : ℝ)
            = ∑ u ∈ (Finset.Icc 1 (q - 1)).filter (fun u => u ≤ q / 2), (q : ℝ) * ((1 : ℝ) / (u : ℝ)) := by
              refine Finset.sum_congr rfl fun u hu => ?_
              have hu' := Finset.mem_filter.mp hu
              have hmin : min u (q - u) = u := min_eq_left (by omega)
              rw [hmin]; ring
          _ ≤ ∑ d ∈ Finset.Icc 1 q, (q : ℝ) * ((1 : ℝ) / (d : ℝ)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
              intro u hu; simp only [Finset.mem_filter, Finset.mem_Icc] at hu ⊢; omega
      have hR : ∑ u ∈ (Finset.Icc 1 (q - 1)).filter (fun u => ¬ u ≤ q / 2),
            (q : ℝ) / ((min u (q - u) : ℕ) : ℝ) ≤ (q : ℝ) * ∑ d ∈ Finset.Icc 1 q, (1 : ℝ) / (d : ℝ) := by
        have hrew : ∑ u ∈ (Finset.Icc 1 (q - 1)).filter (fun u => ¬ u ≤ q / 2),
              (q : ℝ) / ((min u (q - u) : ℕ) : ℝ) =
            (q : ℝ) * ∑ u ∈ (Finset.Icc 1 (q - 1)).filter (fun u => ¬ u ≤ q / 2),
              (1 : ℝ) / ((q - u : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          have hu' := Finset.mem_filter.mp hu
          have hmin : min u (q - u) = q - u := min_eq_right (by omega)
          rw [hmin]; ring
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ hq_pos.le
        have hinj : Set.InjOn (fun u => q - u)
            (((Finset.Icc 1 (q - 1)).filter (fun u => ¬ u ≤ q / 2)) : Set ℕ) := by
          intro u₁ hu₁ u₂ hu₂ h
          dsimp only at h
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hu₁ hu₂
          omega
        have hsub : ((Finset.Icc 1 (q - 1)).filter (fun u => ¬ u ≤ q / 2)).image (fun u => q - u) ⊆
            Finset.Icc 1 q := by
          intro d hd
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hd
          simp only [Finset.mem_filter, Finset.mem_Icc] at hu ⊢; omega
        calc ∑ u ∈ (Finset.Icc 1 (q - 1)).filter (fun u => ¬ u ≤ q / 2), (1 : ℝ) / ((q - u : ℕ) : ℝ)
            = ∑ d ∈ ((Finset.Icc 1 (q - 1)).filter (fun u => ¬ u ≤ q / 2)).image (fun u => q - u),
                (1 : ℝ) / (d : ℝ) :=
              (Finset.sum_image (f := fun d : ℕ => (1 : ℝ) / (d : ℝ))
                (fun a ha b hb h => hinj ha hb h)).symm
          _ ≤ ∑ d ∈ Finset.Icc 1 q, (1 : ℝ) / (d : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      have hharm := harmonic_Icc_le q hq
      nlinarith
    calc ∑ m ∈ S1, expBound (X / (m : ℝ)) ((m : ℝ) * α)
        ≤ ∑ m ∈ S1, (q : ℝ) / ((min (j m) (q - j m) : ℕ) : ℝ) := Finset.sum_le_sum hpt1
      _ = ∑ u ∈ S1.image j, (q : ℝ) / ((min u (q - u) : ℕ) : ℝ) :=
          (Finset.sum_image (f := fun u : ℕ => (q : ℝ) / ((min u (q - u) : ℕ) : ℝ))
            (fun a ha b hb h => hj_inj ha hb h)).symm
      _ ≤ ∑ u ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((min u (q - u) : ℕ) : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun u _ _ => by positivity)
          intro u hu
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hu
          exact hj_mem m hm
      _ ≤ 2 * (q : ℝ) * (1 + Real.log (q : ℝ)) := hsum_Icc
  -- Part 2: `q / 2 < m ≤ D`, covered by blocks `k = 0, ..., D / q` of length `q`
  have hPart2 :
      ∑ m ∈ (Finset.Icc 1 D).filter (fun m => ¬ m ≤ q / 2),
          expBound (X / (m : ℝ)) ((m : ℝ) * α) ≤
        (6 * X / (q : ℝ)) * (1 + Real.log ((D + 1 : ℕ) : ℝ)) +
          ((D : ℝ) + (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
    set S2 := (Finset.Icc 1 D).filter (fun m => ¬ m ≤ q / 2)
    have hcover : S2 ⊆ (Finset.range (D / q + 1)).biUnion
        (fun k => (Finset.range q).image (fun r => (q / 2 + 1 + k * q) + r)) := by
      intro m hm
      simp only [S2, Finset.mem_filter, Finset.mem_Icc] at hm
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
      refine ⟨(m - (q / 2 + 1)) / q, ?_, (m - (q / 2 + 1)) % q, Nat.mod_lt _ hq, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
      · have hdm := Nat.div_add_mod (m - (q / 2 + 1)) q
        rw [mul_comm] at hdm
        omega
    have hle_blocks :
        ∑ m ∈ S2, expBound (X / (m : ℝ)) ((m : ℝ) * α) ≤
          ∑ k ∈ Finset.range (D / q + 1),
            ∑ r ∈ Finset.range q,
              expBound (2 * X / (((2 * k + 1 : ℕ) : ℝ) * (q : ℝ)))
                ((((q / 2 + 1 + k * q) + r : ℕ) : ℝ) * α) := by
      calc ∑ m ∈ S2, expBound (X / (m : ℝ)) ((m : ℝ) * α)
          ≤ ∑ m ∈ (Finset.range (D / q + 1)).biUnion
                (fun k => (Finset.range q).image (fun r => (q / 2 + 1 + k * q) + r)),
              expBound (X / (m : ℝ)) ((m : ℝ) * α) :=
            Finset.sum_le_sum_of_subset_of_nonneg hcover fun m _ _ =>
              expBound_nonneg (by positivity) _
        _ ≤ ∑ k ∈ Finset.range (D / q + 1),
              ∑ m ∈ (Finset.range q).image (fun r => (q / 2 + 1 + k * q) + r),
                expBound (X / (m : ℝ)) ((m : ℝ) * α) :=
            sum_biUnion_le_sum_sum _ _ (fun m : ℕ => expBound (X / (m : ℝ)) ((m : ℝ) * α))
              (fun m => expBound_nonneg (div_nonneg hX (Nat.cast_nonneg m)) _)
        _ = ∑ k ∈ Finset.range (D / q + 1),
              ∑ r ∈ Finset.range q,
                expBound (X / (((q / 2 + 1 + k * q) + r : ℕ) : ℝ))
                  ((((q / 2 + 1 + k * q) + r : ℕ) : ℝ) * α) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_image]
            intro r₁ _ r₂ _ h; dsimp only at h; omega
        _ ≤ ∑ k ∈ Finset.range (D / q + 1),
              ∑ r ∈ Finset.range q,
                expBound (2 * X / (((2 * k + 1 : ℕ) : ℝ) * (q : ℝ)))
                  ((((q / 2 + 1 + k * q) + r : ℕ) : ℝ) * α) := by
            refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun r _ => ?_
            refine expBound_mono_cap ?_ _
            have hnat : (2 * k + 1) * q ≤ 2 * ((q / 2 + 1 + k * q) + r) := by
              have hq_div : q ≤ 2 * (q / 2) + 1 := by omega
              nlinarith
            have hreal : (((2 * k + 1 : ℕ) : ℝ) * (q : ℝ)) ≤
                2 * (((q / 2 + 1 + k * q) + r : ℕ) : ℝ) := by exact_mod_cast hnat
            have hm_pos : (0 : ℝ) < (((q / 2 + 1 + k * q) + r : ℕ) : ℝ) :=
              Nat.cast_pos.mpr (by omega)
            rw [div_le_div_iff₀ hm_pos (by positivity)]
            nlinarith
    have hsum_blocks :
        ∑ k ∈ Finset.range (D / q + 1),
          ∑ r ∈ Finset.range q,
            expBound (2 * X / (((2 * k + 1 : ℕ) : ℝ) * (q : ℝ)))
              ((((q / 2 + 1 + k * q) + r : ℕ) : ℝ) * α) ≤
          ∑ k ∈ Finset.range (D / q + 1),
            (3 * (2 * X / (((2 * k + 1 : ℕ) : ℝ) * (q : ℝ))) + (q : ℝ) * (1 + Real.log (q : ℝ))) :=
      Finset.sum_le_sum fun k _ =>
        sum_expBound_block_le hq hcop (by positivity) happrox (q / 2 + 1 + k * q)
    refine hle_blocks.trans (hsum_blocks.trans ?_)
    rw [Finset.sum_add_distrib]
    have hterm1 :
        ∑ k ∈ Finset.range (D / q + 1),
            3 * (2 * X / (((2 * k + 1 : ℕ) : ℝ) * (q : ℝ))) ≤
          (6 * X / (q : ℝ)) * (1 + Real.log ((D + 1 : ℕ) : ℝ)) := by
      have hrew :
          ∑ k ∈ Finset.range (D / q + 1),
              3 * (2 * X / (((2 * k + 1 : ℕ) : ℝ) * (q : ℝ))) =
            (6 * X / (q : ℝ)) *
              ∑ k ∈ Finset.range (D / q + 1), (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hrew]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ∑ k ∈ Finset.range (D / q + 1), (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ)
          ≤ ∑ k ∈ Finset.range (D / q + 1), (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            exact one_div_le_one_div_of_le (Nat.cast_pos.mpr (by omega))
              (by exact_mod_cast (by omega : k + 1 ≤ 2 * k + 1))
        _ = ∑ j ∈ Finset.Icc 1 (D / q + 1), (1 : ℝ) / (j : ℝ) := by
            refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ (fun _ _ => rfl)
            · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
            · intro k₁ _ k₂ _ h; omega
            · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
              exact ⟨j - 1, by omega, by omega⟩
        _ ≤ 1 + Real.log ((D / q + 1 : ℕ) : ℝ) := harmonic_Icc_le (D / q + 1) (Nat.succ_pos _)
        _ ≤ 1 + Real.log ((D + 1 : ℕ) : ℝ) := by
            have hle : ((D / q + 1 : ℕ) : ℝ) ≤ ((D + 1 : ℕ) : ℝ) :=
              Nat.cast_le.mpr (Nat.add_le_add_right (Nat.div_le_self D q) 1)
            have hpos : (0 : ℝ) < ((D / q + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
            linarith [Real.log_le_log hpos hle]
    have hterm2 :
        ∑ _k ∈ Finset.range (D / q + 1), (q : ℝ) * (1 + Real.log (q : ℝ)) ≤
          ((D : ℝ) + (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hlogq_nn
      push_cast
      have : ((D / q : ℕ) : ℝ) * (q : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.div_mul_le_self D q
      linarith
    linarith
  linarith

/-! ## Section 4: Twisted Vaughan Decomposition & Type I / Type II Bounds -/

/-- Vaughan Type 0 cutoff exponential sum `T₀(V, N, α) = ∑_{1 ≤ n ≤ min N V} Λ(n) e(n α)`. -/
def vaughanT0 (V N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (min N V), (Λ n : ℂ) * e ((n : ℝ) * α)

/-- Vaughan Type I first exponential sum `T₁(U, N, α) = ∑_{d ≤ U} μ(d) ∑_{m ≤ N/d} log(m) e(d m α)`. -/
def vaughanT1 (U N : ℕ) (α : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
    ∑ m ∈ Finset.Icc 1 (N / d), (Real.log (m : ℝ) : ℂ) * e (((d * m : ℕ) : ℝ) * α)

/-- Vaughan Type I second exponential sum
`T₂(U, V, N, α) = ∑_{d ≤ U} μ(d) ∑_{m ≤ V} Λ(m) ∑_{r ≤ N/(d m)} e(d m r α)`. -/
def vaughanT2 (U V N : ℕ) (α : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
    ∑ m ∈ Finset.Icc 1 V, (Λ m : ℂ) *
      ∑ r ∈ Finset.Icc 1 (N / (d * m)), e (((d * m * r : ℕ) : ℝ) * α)

/-- Vaughan Type II bilinear exponential sum
`T₃(U, V, N, α) = ∑_{V < m ≤ N/U} Λ(m) ∑_{U < k ≤ N/m} c_U(k) e(m k α)`. -/
def vaughanT3 (U V N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc V (N / U), (Λ m : ℂ) *
    ∑ k ∈ Finset.Ioc U (N / m),
      (Stage11BombieriVinogradov.vaughanMollifier U k : ℂ) * e (((m * k : ℕ) : ℝ) * α)

/-- Exact Vaughan decomposition of the exponential sum `S_Λ N α` for all `U ≥ 1`. -/
theorem S_Λ_vaughan_decomp {U V N : ℕ} (hU : 1 ≤ U) (α : ℝ) :
    S_Λ N α = vaughanT0 V N α + vaughanT1 U N α - vaughanT2 U V N α - vaughanT3 U V N α := by
  unfold S_Λ
  have hpoint :
      ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * e ((n : ℝ) * α) =
        ∑ n ∈ Finset.Icc 1 N, (Stage11BombieriVinogradov.vaughanA0 V n : ℂ) * e ((n : ℝ) * α) +
        ∑ n ∈ Finset.Icc 1 N, (Stage11BombieriVinogradov.vaughanA1 U n : ℂ) * e ((n : ℝ) * α) -
        ∑ n ∈ Finset.Icc 1 N, (Stage11BombieriVinogradov.vaughanA2 U V n : ℂ) * e ((n : ℝ) * α) -
        ∑ n ∈ Finset.Icc 1 N, (Stage11BombieriVinogradov.vaughanA3 U V n : ℂ) * e ((n : ℝ) * α) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hv := congrArg (Complex.ofReal : ℝ → ℂ)
      (Stage11BombieriVinogradov.vaughan_identity (U := U) (V := V) hU hn1)
    simp only [Complex.ofReal_add, Complex.ofReal_sub] at hv
    rw [hv]; ring
  rw [hpoint]
  -- Match T₀
  have hT0 :
      ∑ n ∈ Finset.Icc 1 N, (Stage11BombieriVinogradov.vaughanA0 V n : ℂ) * e ((n : ℝ) * α) =
        vaughanT0 V N α := by
    unfold Stage11BombieriVinogradov.vaughanA0 vaughanT0
    have hfilt : (Finset.Icc 1 N).filter (· ≤ V) = Finset.Icc 1 (min N V) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]; tauto
    rw [← hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n ≤ V <;> simp [h]
  -- Match T₁
  have hT1 :
      ∑ n ∈ Finset.Icc 1 N, (Stage11BombieriVinogradov.vaughanA1 U n : ℂ) * e ((n : ℝ) * α) =
        vaughanT1 U N α := by
    unfold Stage11BombieriVinogradov.vaughanA1 vaughanT1
    have h1 :
        ∑ n ∈ Finset.Icc 1 N,
            ((∑ d ∈ n.divisors.filter (· ≤ U),
              (ArithmeticFunction.moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ) : ℝ) : ℂ) *
              e ((n : ℝ) * α) =
          ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 U,
            if d ∣ n then
              (ArithmeticFunction.moebius d : ℂ) *
                ((Real.log ((n / d : ℕ) : ℝ) : ℂ) * e (((d * (n / d) : ℕ) : ℝ) * α))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_filter]
      have hset : n.divisors.filter (· ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
        ext d; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdU⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn1, hdU⟩, hdn⟩
        · rintro ⟨⟨_, hdU⟩, hdn⟩; exact ⟨⟨hdn, by omega⟩, hdU⟩
      rw [hset]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdn : d ∣ n := (Finset.mem_filter.mp hd).2
      rw [Nat.mul_div_cancel' hdn, Complex.ofReal_mul, Complex.ofReal_intCast]
      ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have hm1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn.1.1 hn.2) hd1
      exact ⟨hm1, (Nat.le_div_iff_mul_le hd1).mpr (by rw [Nat.div_mul_cancel hn.2]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2, heq]
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨d * m, ?_, Nat.mul_div_cancel_left m hd1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd1).mp hm.2
      rwa [mul_comm] at this
    · intro n _; rfl
  -- Match T₂
  have hT2 :
      ∑ n ∈ Finset.Icc 1 N, (Stage11BombieriVinogradov.vaughanA2 U V n : ℂ) * e ((n : ℝ) * α) =
        vaughanT2 U V N α := by
    unfold Stage11BombieriVinogradov.vaughanA2 vaughanT2
    have h1 :
        ∑ n ∈ Finset.Icc 1 N,
            ((∑ d ∈ n.divisors.filter (· ≤ U),
              (ArithmeticFunction.moebius d : ℝ) *
                ∑ m ∈ (n / d).divisors.filter (· ≤ V), Λ m : ℝ) : ℂ) * e ((n : ℝ) * α) =
          ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 U, ∑ m ∈ Finset.Icc 1 V,
            if d * m ∣ n then
              (ArithmeticFunction.moebius d : ℂ) *
                ((Λ m : ℂ) * e (((d * m * (n / (d * m)) : ℕ) : ℝ) * α))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Complex.ofReal_sum, Finset.sum_mul]
      have hsetD : n.divisors.filter (· ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
        ext d; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdU⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn1, hdU⟩, hdn⟩
        · rintro ⟨⟨_, hdU⟩, hdn⟩; exact ⟨⟨hdn, by omega⟩, hdU⟩
      rw [hsetD, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      by_cases hdn : d ∣ n
      · rw [if_pos hdn, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_sum,
          Finset.mul_sum, Finset.sum_mul, ← Finset.sum_filter]
        have hsetM : (n / d).divisors.filter (· ≤ V) =
            (Finset.Icc 1 V).filter (fun m => d * m ∣ n) := by
          ext m; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨hm, _⟩, hmV⟩
            have hdm : d * m ∣ n := by
              obtain ⟨r, hr⟩ := hm
              exact ⟨r, by rw [← Nat.mul_div_cancel' hdn, hr]; ring⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos (dvd_of_mul_left_dvd hdm) hn1, hmV⟩, hdm⟩
          · rintro ⟨⟨_, hmV⟩, hdm⟩
            have hnd_ne : n / d ≠ 0 :=
              Nat.div_ne_zero_iff.mpr ⟨by omega, Nat.le_of_dvd hn1 hdn⟩
            have hm_dvd : m ∣ n / d := by
              obtain ⟨r, hr⟩ := hdm
              refine ⟨r, Nat.eq_of_mul_eq_mul_left hd1 ?_⟩
              rw [Nat.mul_div_cancel' hdn, hr]; ring
            exact ⟨⟨hm_dvd, hnd_ne⟩, hmV⟩
        rw [hsetM]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hdm : d * m ∣ n := (Finset.mem_filter.mp hm).2
        rw [Nat.mul_div_cancel' hdm]
        ring
      · rw [if_neg hdn]
        symm
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [if_neg (fun hdm => hdn (dvd_of_mul_right_dvd hdm))]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hdm1 : 1 ≤ d * m := Nat.mul_pos hd1 hm1
    rw [← Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / (d * m)) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have hr1 : 1 ≤ n / (d * m) := Nat.div_pos (Nat.le_of_dvd hn.1.1 hn.2) hdm1
      exact ⟨hr1, (Nat.le_div_iff_mul_le hdm1).mpr (by rw [Nat.div_mul_cancel hn.2]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2, heq]
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      refine ⟨d * m * r, ?_, Nat.mul_div_cancel_left r hdm1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hdm1 hr.1, ?_⟩, dvd_mul_right (d * m) r⟩
      have := (Nat.le_div_iff_mul_le hdm1).mp hr.2
      rwa [mul_comm] at this
    · intro n _; ring
  -- Match T₃
  have hT3 :
      ∑ n ∈ Finset.Icc 1 N, (Stage11BombieriVinogradov.vaughanA3 U V n : ℂ) * e ((n : ℝ) * α) =
        vaughanT3 U V N α := by
    unfold Stage11BombieriVinogradov.vaughanA3 vaughanT3
    have h1 :
        ∑ n ∈ Finset.Icc 1 N,
            ((∑ m ∈ n.divisors.filter (fun m => V < m ∧ U < n / m),
              Λ m * Stage11BombieriVinogradov.vaughanMollifier U (n / m) : ℝ) : ℂ) *
              e ((n : ℝ) * α) =
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc V (N / U),
            if m ∣ n ∧ U < n / m then
              (Λ m : ℂ) * ((Stage11BombieriVinogradov.vaughanMollifier U (n / m) : ℂ) *
                e (((m * (n / m) : ℕ) : ℝ) * α))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      rw [Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_filter]
      have hset : n.divisors.filter (fun m => V < m ∧ U < n / m) =
          (Finset.Ioc V (N / U)).filter (fun m => m ∣ n ∧ U < n / m) := by
        ext m; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hmn, _⟩, hVm, hUnm⟩
          have hm_le : m ≤ N / U := (Nat.le_div_iff_mul_le hU).mpr (by
            have h1 : m * U ≤ m * (n / m) := Nat.mul_le_mul_left m (by omega)
            rw [Nat.mul_div_cancel' hmn] at h1
            exact h1.trans hnN)
          exact ⟨⟨hVm, hm_le⟩, hmn, hUnm⟩
        · rintro ⟨⟨hVm, _⟩, hmn, hUnm⟩
          exact ⟨⟨hmn, by omega⟩, hVm, hUnm⟩
      rw [hset]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmn : m ∣ n := (Finset.mem_filter.mp hm).2.1
      rw [Nat.mul_div_cancel' hmn, Complex.ofReal_mul]
      ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := by have := (Finset.mem_Ioc.mp hm).1; omega
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / m) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
      exact ⟨hn.2.2, (Nat.le_div_iff_mul_le hm1).mpr (by rw [Nat.div_mul_cancel hn.2.1]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2.1,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2.1, heq]
    · intro k hk
      simp only [Finset.mem_Ioc] at hk
      refine ⟨m * k, ?_, Nat.mul_div_cancel_left k hm1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hm1 (by omega), ?_⟩, dvd_mul_right m k, ?_⟩
      · have := (Nat.le_div_iff_mul_le hm1).mp hk.2
        rwa [mul_comm] at this
      · rw [Nat.mul_div_cancel_left k hm1]; exact hk.1
    · intro n _; rfl
  rw [hT0, hT1, hT2, hT3]

/-- Elementary bound `‖(μ(d) : ℂ)‖ ≤ 1`. -/
private theorem norm_moebius_le_one (d : ℕ) :
    ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
  by_cases hsq : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    simp [norm_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- Type 0 bound: `‖vaughanT0 V N α‖ ≤ 6 * V` for `V ≥ 1`. -/
theorem norm_vaughanT0_le {V N : ℕ} (hV : 1 ≤ V) (α : ℝ) :
    ‖vaughanT0 V N α‖ ≤ 6 * (V : ℝ) := by
  unfold vaughanT0
  calc ‖∑ n ∈ Finset.Icc 1 (min N V), (Λ n : ℂ) * e ((n : ℝ) * α)‖
      ≤ ∑ n ∈ Finset.Icc 1 (min N V), ‖(Λ n : ℂ) * e ((n : ℝ) * α)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 (min N V), Λ n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul, norm_e, mul_one, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ ∑ n ∈ Finset.range (V + 1), Λ n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        intro n hn; simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
    _ = RHDirect.chebyshevPsi (V : ℝ) := by
        unfold RHDirect.chebyshevPsi; rw [Nat.floor_natCast]
    _ ≤ 6 * (V : ℝ) := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (Nat.one_le_cast.mpr hV)

/-- Summation-by-parts bound for log-weighted linear exponential sums:
`‖∑_{m=1}^M (log m) e(m θ)‖ ≤ (log M) · expBound M θ` for all `M ≥ 1`. -/
theorem norm_sum_log_mul_e_le (M : ℕ) (hM : 1 ≤ M) (θ : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 M, (Real.log (m : ℝ) : ℂ) * e ((m : ℝ) * θ)‖ ≤
      Real.log (M : ℝ) * expBound (M : ℝ) θ := by
  -- Telescoping representation: `log m = ∑_{k=1}^{m-1} (log (k+1) - log k)` for `m ≥ 1`
  have hlog_tele : ∀ m : ℕ, 1 ≤ m →
      Real.log (m : ℝ) = ∑ k ∈ Finset.Icc 1 (m - 1),
        (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) := by
    intro m hm
    induction m with
    | zero => omega
    | succ r ih =>
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have hIcc : Finset.Icc 1 r = insert r (Finset.Icc 1 (r - 1)) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        simp only [Nat.add_sub_cancel]
        rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ← ih hr]
        ring
  -- Swap sums over `m ∈ Icc 1 M` and `k ∈ Icc 1 (M - 1)`
  have hswap :
      ∑ m ∈ Finset.Icc 1 M, (Real.log (m : ℝ) : ℂ) * e ((m : ℝ) * θ) =
        ∑ k ∈ Finset.Icc 1 (M - 1),
          ((Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) : ℝ) : ℂ) *
            ∑ m ∈ Finset.Icc (k + 1) M, e ((m : ℝ) * θ) := by
    calc ∑ m ∈ Finset.Icc 1 M, (Real.log (m : ℝ) : ℂ) * e ((m : ℝ) * θ)
        = ∑ m ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 (M - 1),
            if k < m then
              ((Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * θ)
            else 0 := by
          refine Finset.sum_congr rfl fun m hm => ?_
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
          rw [hlog_tele m hm1, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext k; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
      _ = ∑ k ∈ Finset.Icc 1 (M - 1), ∑ m ∈ Finset.Icc 1 M,
            if k < m then
              ((Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * θ)
            else 0 := Finset.sum_comm
      _ = ∑ k ∈ Finset.Icc 1 (M - 1),
            ((Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) : ℝ) : ℂ) *
              ∑ m ∈ Finset.Icc (k + 1) M, e ((m : ℝ) * θ) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [← Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext m; simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢; omega
  rw [hswap]
  calc ‖∑ k ∈ Finset.Icc 1 (M - 1),
          ((Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) : ℝ) : ℂ) *
            ∑ m ∈ Finset.Icc (k + 1) M, e ((m : ℝ) * θ)‖
      ≤ ∑ k ∈ Finset.Icc 1 (M - 1),
          ‖((Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) : ℝ) : ℂ) *
            ∑ m ∈ Finset.Icc (k + 1) M, e ((m : ℝ) * θ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 (M - 1),
          (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) * expBound (M : ℝ) θ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hdiff_nn : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
          have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
          linarith [Real.log_le_log hk_pos (Nat.cast_le.mpr (Nat.le_succ k))]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hdiff_nn]
        refine mul_le_mul_of_nonneg_left ?_ hdiff_nn
        refine (norm_sum_e_Icc_le (k + 1) M θ).trans ?_
        refine expBound_mono_cap ?_ θ
        have hcard : (Finset.Icc (k + 1) M).card ≤ M := by simp only [Nat.card_Icc]; omega
        exact_mod_cast hcard
    _ = (∑ k ∈ Finset.Icc 1 (M - 1), (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ))) *
          expBound (M : ℝ) θ := (Finset.sum_mul _ _ _).symm
    _ = Real.log (M : ℝ) * expBound (M : ℝ) θ := by rw [← hlog_tele M hM]

/-- Type I bound for `T₁`. -/
theorem norm_vaughanT1_le {U N q : ℕ} (hU : 1 ≤ U) (hN : 1 ≤ N) (hq : 1 ≤ q)
    {a : ℤ} (hcop : Nat.Coprime a.natAbs q) {α : ℝ}
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ‖vaughanT1 U N α‖ ≤
      Real.log (N : ℝ) *
        ((6 * (N : ℝ) / (q : ℝ)) * (1 + Real.log ((U + 1 : ℕ) : ℝ)) +
          ((U : ℝ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ))) := by
  unfold vaughanT1
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hN)
  calc ‖∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ Finset.Icc 1 (N / d), (Real.log (m : ℝ) : ℂ) * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Icc 1 U,
          ‖(ArithmeticFunction.moebius d : ℂ) *
            ∑ m ∈ Finset.Icc 1 (N / d), (Real.log (m : ℝ) : ℂ) * e (((d * m : ℕ) : ℝ) * α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 U, Real.log (N : ℝ) * expBound ((N : ℝ) / (d : ℝ)) ((d : ℝ) * α) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        rw [norm_mul]
        refine (mul_le_mul_of_nonneg_right (norm_moebius_le_one d) (norm_nonneg _)).trans ?_
        rw [one_mul]
        by_cases hNd : N / d = 0
        · rw [hNd]
          have hempty : Finset.Icc 1 0 = ∅ := by decide
          rw [hempty, Finset.sum_empty, norm_zero]
          exact mul_nonneg hlogN_nn (expBound_nonneg (by positivity) _)
        · have hNd1 : 1 ≤ N / d := Nat.pos_of_ne_zero hNd
          have heq : ∑ m ∈ Finset.Icc 1 (N / d),
                (Real.log (m : ℝ) : ℂ) * e (((d * m : ℕ) : ℝ) * α) =
              ∑ m ∈ Finset.Icc 1 (N / d),
                (Real.log (m : ℝ) : ℂ) * e ((m : ℝ) * ((d : ℝ) * α)) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            congr 2; push_cast; ring
          rw [heq]
          refine (norm_sum_log_mul_e_le (N / d) hNd1 ((d : ℝ) * α)).trans ?_
          have hlog_le : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
            Real.log_le_log (Nat.cast_pos.mpr hNd1) (Nat.cast_le.mpr (Nat.div_le_self N d))
          have hdiv_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
            rw [le_div_iff₀ (Nat.cast_pos.mpr hd1)]
            exact_mod_cast Nat.div_mul_le_self N d
          exact mul_le_mul hlog_le (expBound_mono_cap hdiv_le _)
            (expBound_nonneg (Nat.cast_nonneg _) _) hlogN_nn
    _ = Real.log (N : ℝ) * ∑ d ∈ Finset.Icc 1 U, expBound ((N : ℝ) / (d : ℝ)) ((d : ℝ) * α) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (N : ℝ) *
          ((6 * (N : ℝ) / (q : ℝ)) * (1 + Real.log ((U + 1 : ℕ) : ℝ)) +
            ((U : ℝ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (sum_expBound_div_le hq hcop (Nat.cast_nonneg N) happrox hU) hlogN_nn

/-- Type I bound for `T₂`. -/
theorem norm_vaughanT2_le {U V N q : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hN : 1 ≤ N) (hq : 1 ≤ q)
    {a : ℤ} (hcop : Nat.Coprime a.natAbs q) {α : ℝ}
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ‖vaughanT2 U V N α‖ ≤
      Real.log (N : ℝ) *
        ((6 * (N : ℝ) / (q : ℝ)) * (1 + Real.log ((U * V + 1 : ℕ) : ℝ)) +
          ((U * V : ℕ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ))) := by
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hN)
  -- Group `T₂` by `k = d * m ∈ Icc 1 (U * V)`
  let E : ℕ → ℂ := fun k => ∑ r ∈ Finset.Icc 1 (N / k), e ((r : ℝ) * ((k : ℝ) * α))
  have hgroup :
      vaughanT2 U V N α =
        ∑ k ∈ Finset.Icc 1 (U * V),
          (∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter (fun p => p.1 * p.2 = k),
            (ArithmeticFunction.moebius p.1 : ℂ) * (Λ p.2 : ℂ)) * E k := by
    unfold vaughanT2
    have hprod :
        ∑ d ∈ Finset.Icc 1 U, (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ Finset.Icc 1 V, (Λ m : ℂ) *
            ∑ r ∈ Finset.Icc 1 (N / (d * m)), e (((d * m * r : ℕ) : ℝ) * α) =
          ∑ p ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 V,
            (ArithmeticFunction.moebius p.1 : ℂ) * (Λ p.2 : ℂ) * E (p.1 * p.2) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_assoc]
      congr 2
      simp only [E]
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 1; push_cast; ring
    rw [hprod]
    have hmaps : ∀ p ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 V, p.1 * p.2 ∈ Finset.Icc 1 (U * V) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_Icc] at hp ⊢
      exact ⟨Nat.mul_pos hp.1.1 hp.2.1, Nat.mul_le_mul hp.1.2 hp.2.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2]
  rw [hgroup]
  calc ‖∑ k ∈ Finset.Icc 1 (U * V),
          (∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter (fun p => p.1 * p.2 = k),
            (ArithmeticFunction.moebius p.1 : ℂ) * (Λ p.2 : ℂ)) * E k‖
      ≤ ∑ k ∈ Finset.Icc 1 (U * V),
          ‖(∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter (fun p => p.1 * p.2 = k),
            (ArithmeticFunction.moebius p.1 : ℂ) * (Λ p.2 : ℂ)) * E k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 (U * V),
          Real.log (N : ℝ) * expBound ((N : ℝ) / (k : ℝ)) ((k : ℝ) * α) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        by_cases hkN : N < k
        · have hE0 : E k = 0 := by
            simp only [E, Nat.div_eq_of_lt hkN]
            have hempty : Finset.Icc 1 0 = ∅ := by decide
            rw [hempty, Finset.sum_empty]
          rw [hE0, mul_zero, norm_zero]
          exact mul_nonneg hlogN_nn (expBound_nonneg (by positivity) _)
        · have hk_le_N : k ≤ N := Nat.not_lt.mp hkN
          rw [norm_mul]
          -- Bound coefficient norm by `∑_{m ∣ k} Λ m = log k ≤ log N`
          have hcoeff :
              ‖∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter (fun p => p.1 * p.2 = k),
                (ArithmeticFunction.moebius p.1 : ℂ) * (Λ p.2 : ℂ)‖ ≤ Real.log (N : ℝ) := by
            set F := (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter (fun p => p.1 * p.2 = k)
            have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) (F : Set (ℕ × ℕ)) := by
              intro p₁ hp₁ p₂ hp₂ heq
              dsimp only at heq
              simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
                Finset.mem_Icc] at hp₁ hp₂
              have h2 : p₁.1 * p₁.2 = p₂.1 * p₁.2 := by rw [hp₁.2, heq, hp₂.2]
              have h1 : p₁.1 = p₂.1 := Nat.eq_of_mul_eq_mul_right hp₁.1.2.1 h2
              exact Prod.ext h1 heq
            have hsub : F.image (fun p : ℕ × ℕ => p.2) ⊆ k.divisors := by
              intro m hm
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
              simp only [F, Finset.mem_filter] at hp
              exact Nat.mem_divisors.mpr ⟨⟨p.1, by rw [mul_comm, hp.2]⟩, by omega⟩
            calc ‖∑ p ∈ F, (ArithmeticFunction.moebius p.1 : ℂ) * (Λ p.2 : ℂ)‖
                ≤ ∑ p ∈ F, ‖(ArithmeticFunction.moebius p.1 : ℂ) * (Λ p.2 : ℂ)‖ := norm_sum_le _ _
              _ ≤ ∑ p ∈ F, Λ p.2 := by
                  refine Finset.sum_le_sum fun p _ => ?_
                  rw [norm_mul, Complex.norm_real,
                    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
                  exact (mul_le_mul_of_nonneg_right (norm_moebius_le_one p.1)
                    ArithmeticFunction.vonMangoldt_nonneg).trans (by rw [one_mul])
              _ = ∑ m ∈ F.image (fun p : ℕ × ℕ => p.2), Λ m :=
                  (Finset.sum_image (f := fun m : ℕ => Λ m)
                    (fun a ha b hb h => hinj ha hb h)).symm
              _ ≤ ∑ m ∈ k.divisors, Λ m :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub
                    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
              _ = Real.log (k : ℝ) := ArithmeticFunction.vonMangoldt_sum
              _ ≤ Real.log (N : ℝ) :=
                  Real.log_le_log (Nat.cast_pos.mpr hk1) (Nat.cast_le.mpr hk_le_N)
          have hE_le : ‖E k‖ ≤ expBound ((N : ℝ) / (k : ℝ)) ((k : ℝ) * α) := by
            refine (norm_sum_e_Icc_le 1 (N / k) ((k : ℝ) * α)).trans ?_
            refine expBound_mono_cap ?_ _
            simp only [Nat.card_Icc, Nat.add_sub_cancel]
            rw [le_div_iff₀ (Nat.cast_pos.mpr hk1)]
            exact_mod_cast Nat.div_mul_le_self N k
          exact mul_le_mul hcoeff hE_le (norm_nonneg _) hlogN_nn
    _ = Real.log (N : ℝ) * ∑ k ∈ Finset.Icc 1 (U * V), expBound ((N : ℝ) / (k : ℝ)) ((k : ℝ) * α) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (N : ℝ) *
          ((6 * (N : ℝ) / (q : ℝ)) * (1 + Real.log ((U * V + 1 : ℕ) : ℝ)) +
            ((U * V : ℕ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (sum_expBound_div_le hq hcop (Nat.cast_nonneg N) happrox (Nat.mul_pos hU hV)) hlogN_nn

/-- Elementary square-root subadditivity `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
private theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- Single dyadic Type II block bound via Cauchy–Schwarz and `sum_expBound_const_le`. -/
private theorem norm_vaughanT3_dyadic_le {U V N M q : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hN : 1 ≤ N) (hM : 1 ≤ M) (hq : 1 ≤ q)
    {a : ℤ} (hcop : Nat.Coprime a.natAbs q) {α : ℝ}
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ‖∑ m ∈ (Finset.Ioc V (N / U)).filter (fun m => M < m ∧ m ≤ 2 * M), (Λ m : ℂ) *
        ∑ k ∈ Finset.Ioc U (N / m),
          (Stage11BombieriVinogradov.vaughanMollifier U k : ℂ) * e (((m * k : ℕ) : ℝ) * α)‖ ≤
      13 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * Real.sqrt (1 + Real.log (q : ℝ)) *
        ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
          (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ))) := by
  set I := (Finset.Ioc V (N / U)).filter (fun m => M < m ∧ m ≤ 2 * M)
  have hlog2N_nn : 0 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_nonneg (by have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN; linarith)
  have hlogq_nn : 0 ≤ 1 + Real.log (q : ℝ) := by
    linarith [Real.log_nonneg (Nat.one_le_cast.mpr hq)]
  by_cases hI : I.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hI, Finset.sum_empty, norm_zero]
    positivity
  -- Extract bounds `M ≤ N / U`, `V < 2 * M`, `M < N` from `m₀ ∈ I`
  obtain ⟨m₀, hm₀⟩ := hI
  simp only [I, Finset.mem_filter, Finset.mem_Ioc] at hm₀
  have hM_le_NU : M ≤ N / U := by omega
  have hV_lt_2M : V < 2 * M := by omega
  have hM_lt_N : M < N := lt_of_lt_of_le hm₀.2.1 (hm₀.1.2.trans (Nat.div_le_self N U))
  have hNM1 : 1 ≤ N / M := Nat.div_pos hM_lt_N.le hM
  -- Rewrite `I` as an explicit interval `Finset.Icc A B`
  set L_I : ℕ := max (V + 1) (M + 1)
  set R_I : ℕ := min (N / U) (2 * M)
  have hI_eq : I = Finset.Icc L_I R_I := by
    ext m; simp only [I, L_I, R_I, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]; omega
  -- Define inner sum `f m`
  let f : ℕ → ℂ := fun m =>
    ∑ k ∈ Finset.Ioc U (N / m),
      (Stage11BombieriVinogradov.vaughanMollifier U k : ℂ) * e (((m * k : ℕ) : ℝ) * α)
  -- Step 1: Cauchy–Schwarz on `∑ m ∈ I, Λ(m) * f(m)`
  have hCS : ‖∑ m ∈ I, (Λ m : ℂ) * f m‖ ^ 2 ≤
      (∑ m ∈ I, (Λ m) ^ 2) * (∑ m ∈ I, ‖f m‖ ^ 2) := by
    have htri : ‖∑ m ∈ I, (Λ m : ℂ) * f m‖ ≤ ∑ m ∈ I, Λ m * ‖f m‖ := by
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun m _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc ‖∑ m ∈ I, (Λ m : ℂ) * f m‖ ^ 2
        ≤ (∑ m ∈ I, Λ m * ‖f m‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ m ∈ I, (Λ m) ^ 2) * (∑ m ∈ I, ‖f m‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq I (fun m => Λ m) (fun m => ‖f m‖)
  -- Step 2: Bound `∑ m ∈ I, Λ(m)² ≤ 12 * M * (1 + log (2 N))`
  have hL2_Λ : ∑ m ∈ I, (Λ m) ^ 2 ≤ 12 * (M : ℝ) * (1 + Real.log (2 * (N : ℝ))) := by
    have hI_sub : I ⊆ Finset.Icc 1 (2 * M) := by
      intro m hm; simp only [I, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hm ⊢; omega
    have h2M1 : (1 : ℝ) ≤ ((2 * M : ℕ) : ℝ) := Nat.one_le_cast.mpr (by omega)
    have hsum1 := Stage3BombieriVinogradov.sum_vonMangoldt_sq_le_log_mul_psi (x := ((2 * M : ℕ) : ℝ)) h2M1
    rw [Nat.floor_natCast] at hsum1
    have hpsi := Stage4ExplicitFormula.chebyshevPsi_le_six_mul h2M1
    have hlog_le : Real.log ((2 * M : ℕ) : ℝ) ≤ 1 + Real.log (2 * (N : ℝ)) := by
      have h1 : Real.log ((2 * M : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
        apply Real.log_le_log (by positivity)
        have : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hM_lt_N.le
        push_cast; linarith
      linarith
    calc ∑ m ∈ I, (Λ m) ^ 2
        ≤ ∑ m ∈ Finset.Icc 1 (2 * M), (Λ m) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hI_sub fun _ _ _ => sq_nonneg _
      _ = ∑ m ∈ Finset.Icc 1 (2 * M), ‖(Λ m : ℂ)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ Real.log ((2 * M : ℕ) : ℝ) * RHDirect.chebyshevPsi ((2 * M : ℕ) : ℝ) := hsum1
      _ ≤ (1 + Real.log (2 * (N : ℝ))) * (6 * ((2 * M : ℕ) : ℝ)) := by
          have hpsi_nn : 0 ≤ RHDirect.chebyshevPsi ((2 * M : ℕ) : ℝ) :=
            Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
          exact mul_le_mul hlog_le hpsi hpsi_nn (by linarith)
      _ = 12 * (M : ℝ) * (1 + Real.log (2 * (N : ℝ))) := by push_cast; ring
  -- Step 3: Expand and bound `∑ m ∈ I, ‖f m‖²`
  set K := Finset.Ioc U (N / M)
  let c : ℕ → ℝ := Stage11BombieriVinogradov.vaughanMollifier U
  have hL2_c : ∑ k ∈ K, (c k) ^ 2 ≤ ((N / M : ℕ) : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3 := by
    have hK_sub : K ⊆ Finset.Icc 1 (N / M) := by
      intro k hk; simp only [K, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega
    calc ∑ k ∈ K, (c k) ^ 2
        ≤ ∑ k ∈ Finset.Icc 1 (N / M), (c k) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hK_sub fun _ _ _ => sq_nonneg _
      _ ≤ ∑ k ∈ Finset.Icc 1 (N / M), (k.divisors.card : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [← sq_abs (c k)]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (Stage11BombieriVinogradov.abs_vaughanMollifier_le_divisors U k) 2
      _ ≤ ((N / M : ℕ) : ℝ) * (1 + Real.log ((N / M : ℕ) : ℝ)) ^ 3 :=
          Stage10ZeroDensity.sum_divisors_card_sq_le hNM1
      _ ≤ ((N / M : ℕ) : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3 := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hlog_le : Real.log ((N / M : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
            apply Real.log_le_log (Nat.cast_pos.mpr hNM1)
            have h1 : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (Nat.div_le_self N M)
            linarith
          exact pow_le_pow_left₀
            (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr hNM1)]) (by linarith) 3
  -- Expand `∑ m ∈ I, ‖f m‖²` by swapping sums over `m ∈ I` and `(k₁, k₂) ∈ K × K`
  have hinner_sq :
      ∑ m ∈ I, ‖f m‖ ^ 2 ≤
        (∑ k ∈ K, (c k) ^ 2) *
          ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α)) := by
    have hnorm_sq : ∀ m ∈ I, ‖f m‖ ^ 2 =
        (∑ k₁ ∈ K, ∑ k₂ ∈ K,
          if k₁ ≤ N / m ∧ k₂ ≤ N / m then
            ((c k₁ * c k₂ : ℝ) : ℂ) * e ((m : ℝ) * (((k₁ : ℤ) - (k₂ : ℤ) : ℝ) * α))
          else 0).re := by
      intro m hm
      have hm_gt : M < m := (Finset.mem_filter.mp hm).2.1
      have hsub_K : Finset.Ioc U (N / m) ⊆ K := by
        intro k hk
        simp only [K, Finset.mem_Ioc] at hk ⊢
        exact ⟨hk.1, hk.2.trans (Nat.div_le_div_left hm_gt.le hM)⟩
      have hf_eq : f m = ∑ k ∈ K, if k ≤ N / m then (c k : ℂ) * e (((m * k : ℕ) : ℝ) * α) else 0 := by
        simp only [f, c, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext k; simp only [K, Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · intro hk; exact ⟨⟨hk.1, hk.2.trans (Nat.div_le_div_left hm_gt.le hM)⟩, hk.2⟩
        · rintro ⟨⟨hUk, _⟩, hkm⟩; exact ⟨hUk, hkm⟩
      have hsq : (‖f m‖ ^ 2 : ℝ) = (f m * star (f m)).re := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [hsq, hf_eq]
      congr 1
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => ?_
      by_cases h1 : k₁ ≤ N / m <;> by_cases h2 : k₂ ≤ N / m <;> simp only [h1, h2, and_self,
        and_false, false_and, ite_true, ite_false, mul_zero, zero_mul, star_zero]
      rw [star_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, e_star]
      have he : e (((m * k₁ : ℕ) : ℝ) * α) * e (-(((m * k₂ : ℕ) : ℝ) * α)) =
          e ((m : ℝ) * (((k₁ : ℤ) - (k₂ : ℤ) : ℝ) * α)) := by
        rw [← e_add]; congr 1; push_cast; ring
      calc ((c k₁ : ℂ) * e (((m * k₁ : ℕ) : ℝ) * α)) *
            (e (-(((m * k₂ : ℕ) : ℝ) * α)) * (c k₂ : ℂ))
          = ((c k₁ : ℂ) * (c k₂ : ℂ)) *
              (e (((m * k₁ : ℕ) : ℝ) * α) * e (-(((m * k₂ : ℕ) : ℝ) * α))) := by ring
        _ = ((c k₁ * c k₂ : ℝ) : ℂ) * e ((m : ℝ) * (((k₁ : ℤ) - (k₂ : ℤ) : ℝ) * α)) := by
            rw [he, Complex.ofReal_mul]
    have hre_swap :
        ∑ m ∈ I, ‖f m‖ ^ 2 =
          (∑ k₁ ∈ K, ∑ k₂ ∈ K, ((c k₁ * c k₂ : ℝ) : ℂ) *
            ∑ m ∈ Finset.Icc L_I (min R_I (N / max k₁ k₂)),
              e ((m : ℝ) * (((k₁ : ℤ) - (k₂ : ℤ) : ℝ) * α))).re := by
      rw [Finset.sum_congr rfl hnorm_sq, ← Complex.re_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k₁ hk₁ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k₂ hk₂ => ?_
      have hk₁1 : 1 ≤ k₁ := by have := (Finset.mem_Ioc.mp hk₁).1; omega
      have hk₂1 : 1 ≤ k₂ := by have := (Finset.mem_Ioc.mp hk₂).1; omega
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      rw [hI_eq]
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hLm, hmR⟩, h1, h2⟩
        have hm1 : 1 ≤ m := by omega
        have hmul1 : k₁ * m ≤ N := (Nat.le_div_iff_mul_le hm1).mp h1
        have hmul2 : k₂ * m ≤ N := (Nat.le_div_iff_mul_le hm1).mp h2
        have hmul_max : m * max k₁ k₂ ≤ N := by
          rcases le_total k₁ k₂ with hle | hle
          · rw [max_eq_right hle, mul_comm]; exact hmul2
          · rw [max_eq_left hle, mul_comm]; exact hmul1
        have hm_div : m ≤ N / max k₁ k₂ :=
          (Nat.le_div_iff_mul_le (by omega : 0 < max k₁ k₂)).mpr hmul_max
        exact ⟨hLm, le_min hmR hm_div⟩
      · rintro ⟨hLm, hm_min⟩
        have hmR : m ≤ R_I := le_trans hm_min (min_le_left _ _)
        have hm_div : m ≤ N / max k₁ k₂ := le_trans hm_min (min_le_right _ _)
        have hm1 : 1 ≤ m := by omega
        have hmul_max : m * max k₁ k₂ ≤ N :=
          (Nat.le_div_iff_mul_le (by omega : 0 < max k₁ k₂)).mp hm_div
        have h1 : k₁ ≤ N / m := (Nat.le_div_iff_mul_le hm1).mpr (by
          calc k₁ * m = m * k₁ := mul_comm _ _
            _ ≤ m * max k₁ k₂ := Nat.mul_le_mul_left m (le_max_left _ _)
            _ ≤ N := hmul_max)
        have h2 : k₂ ≤ N / m := (Nat.le_div_iff_mul_le hm1).mpr (by
          calc k₂ * m = m * k₂ := mul_comm _ _
            _ ≤ m * max k₁ k₂ := Nat.mul_le_mul_left m (le_max_right _ _)
            _ ≤ N := hmul_max)
        exact ⟨⟨hLm, hmR⟩, h1, h2⟩
    rw [hre_swap]
    have hstep1 :
        (∑ k₁ ∈ K, ∑ k₂ ∈ K, ((c k₁ * c k₂ : ℝ) : ℂ) *
          ∑ m ∈ Finset.Icc L_I (min R_I (N / max k₁ k₂)),
            e ((m : ℝ) * (((k₁ : ℤ) - (k₂ : ℤ) : ℝ) * α))).re ≤
          ∑ k₁ ∈ K, ∑ k₂ ∈ K, |c k₁| * |c k₂| *
            expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) := by
      refine (Complex.re_le_norm _).trans ?_
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun k₁ _ => (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun k₂ _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hcard_le : ((Finset.Icc L_I (min R_I (N / max k₁ k₂))).card : ℝ) ≤ (M : ℝ) := by
        have hcard : (Finset.Icc L_I (min R_I (N / max k₁ k₂))).card ≤ M := by
          simp only [Nat.card_Icc, L_I, R_I]; omega
        exact_mod_cast hcard
      have habs_exp : expBound (M : ℝ) (((k₁ : ℤ) - (k₂ : ℤ) : ℝ) * α) =
          expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) := by
        rcases le_or_gt (k₂ : ℤ) (k₁ : ℤ) with hle | hgt
        · have h1 : (((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℤ) = (k₁ : ℤ) - (k₂ : ℤ) :=
            Int.natAbs_of_nonneg (sub_nonneg.mpr hle)
          have h2 : (((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) = ((k₁ : ℤ) - (k₂ : ℤ) : ℝ) := by
            rw [← Int.cast_natCast, h1]; push_cast; rfl
          rw [h2]
        · have h1 : (((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℤ) = -((k₁ : ℤ) - (k₂ : ℤ)) :=
            Int.ofNat_natAbs_of_nonpos (by omega)
          have h2 : (((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) = -((k₁ : ℤ) - (k₂ : ℤ) : ℝ) := by
            rw [← Int.cast_natCast, h1]; push_cast; ring
          rw [h2, neg_mul, expBound_neg]
      rw [← habs_exp]
      exact (norm_sum_e_Icc_le _ _ _).trans (expBound_mono_cap hcard_le _)
    refine hstep1.trans ?_
    -- Split into diagonal (`k₁ = k₂`) and off-diagonal (`k₁ ≠ k₂`), using `|a||b| ≤ (a² + b²)/2`
    have hdiag_off :
        ∑ k₁ ∈ K, ∑ k₂ ∈ K, |c k₁| * |c k₂| *
            expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) ≤
          ∑ k₁ ∈ K, (c k₁) ^ 2 *
            ((M : ℝ) + ∑ k₂ ∈ K.filter (· ≠ k₁),
              expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α)) := by
      have hamgm :
          ∑ k₁ ∈ K, ∑ k₂ ∈ K, |c k₁| * |c k₂| *
              expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) ≤
            ∑ k₁ ∈ K, ∑ k₂ ∈ K, (((c k₁) ^ 2 + (c k₂) ^ 2) / 2) *
              expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) := by
        refine Finset.sum_le_sum fun k₁ _ => Finset.sum_le_sum fun k₂ _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (expBound_nonneg (Nat.cast_nonneg M) _)
        have hsq : 0 ≤ (|c k₁| - |c k₂|) ^ 2 := sq_nonneg _
        nlinarith [sq_abs (c k₁), sq_abs (c k₂)]
      have hsymm :
          ∑ k₁ ∈ K, ∑ k₂ ∈ K, (((c k₁) ^ 2 + (c k₂) ^ 2) / 2) *
              expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) =
            ∑ k₁ ∈ K, ∑ k₂ ∈ K, (c k₁) ^ 2 *
              expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) := by
        have hsplit :
            ∑ k₁ ∈ K, ∑ k₂ ∈ K, (((c k₁) ^ 2 + (c k₂) ^ 2) / 2) *
                expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) =
              (∑ k₁ ∈ K, ∑ k₂ ∈ K, ((c k₁) ^ 2 / 2) *
                expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α)) +
              (∑ k₁ ∈ K, ∑ k₂ ∈ K, ((c k₂) ^ 2 / 2) *
                expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k₁ _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k₂ _ => by ring
        rw [hsplit]
        have hswap2 :
            (∑ k₁ ∈ K, ∑ k₂ ∈ K, ((c k₂) ^ 2 / 2) *
                expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α)) =
              ∑ k₁ ∈ K, ∑ k₂ ∈ K, ((c k₁) ^ 2 / 2) *
                expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => ?_
          have hna : ((k₂ : ℤ) - (k₁ : ℤ)).natAbs = ((k₁ : ℤ) - (k₂ : ℤ)).natAbs := by omega
          rw [hna]
        rw [hswap2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k₁ _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k₂ _ => by ring
      refine hamgm.trans (hsymm.le.trans ?_)
      refine Finset.sum_le_sum fun k₁ hk₁ => ?_
      rw [← Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not K (fun k₂ => k₂ = k₁)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hdiag : ∑ k₂ ∈ K.filter (fun k₂ => k₂ = k₁),
            expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) ≤ (M : ℝ) := by
        have hfilt : K.filter (fun k₂ => k₂ = k₁) = {k₁} := by
          ext k₂; simp only [Finset.mem_filter, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨h ▸ hk₁, h⟩⟩
        rw [hfilt, Finset.sum_singleton]
        exact expBound_le_cap (M : ℝ) _
      linarith
    refine hdiag_off.trans ?_
    -- For each `k₁ ∈ K`, `∑_{k₂ ∈ K, k₂ ≠ k₁} expBound M (|k₁ - k₂| α) ≤ 2 * ∑_{h=1}^{N/M} expBound M (h α)`
    have hinner_k₁ : ∀ k₁ ∈ K,
        ∑ k₂ ∈ K.filter (· ≠ k₁),
            expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) ≤
          2 * ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α) := by
      intro k₁ hk₁
      simp only [K, Finset.mem_Ioc] at hk₁
      rw [← Finset.sum_filter_add_sum_filter_not (K.filter (· ≠ k₁)) (fun k₂ => k₂ < k₁)]
      have hlt : ∑ k₂ ∈ (K.filter (· ≠ k₁)).filter (fun k₂ => k₂ < k₁),
            expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) ≤
          ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α) := by
        set Slt := (K.filter (· ≠ k₁)).filter (fun k₂ => k₂ < k₁)
        have hinj : Set.InjOn (fun k₂ : ℕ => k₁ - k₂) (Slt : Set ℕ) := by
          intro a ha b hb h; dsimp only at h
          simp only [Slt, Finset.mem_coe, Finset.mem_filter] at ha hb; omega
        have hsub : Slt.image (fun k₂ : ℕ => k₁ - k₂) ⊆ Finset.Icc 1 (N / M) := by
          intro h hh
          obtain ⟨k₂, hk₂, rfl⟩ := Finset.mem_image.mp hh
          simp only [Slt, K, Finset.mem_filter, Finset.mem_Ioc] at hk₂
          simp only [Finset.mem_Icc]; omega
        calc ∑ k₂ ∈ Slt, expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α)
            = ∑ k₂ ∈ Slt, expBound (M : ℝ) (((k₁ - k₂ : ℕ) : ℝ) * α) := by
              refine Finset.sum_congr rfl fun k₂ hk₂ => ?_
              simp only [Slt, Finset.mem_filter] at hk₂
              have : ((k₁ : ℤ) - (k₂ : ℤ)).natAbs = k₁ - k₂ := by omega
              rw [this]
          _ = ∑ h ∈ Slt.image (fun k₂ : ℕ => k₁ - k₂), expBound (M : ℝ) ((h : ℝ) * α) :=
              (Finset.sum_image (f := fun h : ℕ => expBound (M : ℝ) ((h : ℝ) * α))
                (fun a ha b hb h => hinj ha hb h)).symm
          _ ≤ ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun _ _ _ => expBound_nonneg (Nat.cast_nonneg M) _)
      have hgt : ∑ k₂ ∈ (K.filter (· ≠ k₁)).filter (fun k₂ => ¬ k₂ < k₁),
            expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α) ≤
          ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α) := by
        set Sgt := (K.filter (· ≠ k₁)).filter (fun k₂ => ¬ k₂ < k₁)
        have hinj : Set.InjOn (fun k₂ : ℕ => k₂ - k₁) (Sgt : Set ℕ) := by
          intro a ha b hb h; dsimp only at h
          simp only [Sgt, Finset.mem_coe, Finset.mem_filter] at ha hb; omega
        have hsub : Sgt.image (fun k₂ : ℕ => k₂ - k₁) ⊆ Finset.Icc 1 (N / M) := by
          intro h hh
          obtain ⟨k₂, hk₂, rfl⟩ := Finset.mem_image.mp hh
          simp only [Sgt, K, Finset.mem_filter, Finset.mem_Ioc] at hk₂
          simp only [Finset.mem_Icc]; omega
        calc ∑ k₂ ∈ Sgt, expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α)
            = ∑ k₂ ∈ Sgt, expBound (M : ℝ) (((k₂ - k₁ : ℕ) : ℝ) * α) := by
              refine Finset.sum_congr rfl fun k₂ hk₂ => ?_
              simp only [Sgt, Finset.mem_filter] at hk₂
              have : ((k₁ : ℤ) - (k₂ : ℤ)).natAbs = k₂ - k₁ := by omega
              rw [this]
          _ = ∑ h ∈ Sgt.image (fun k₂ : ℕ => k₂ - k₁), expBound (M : ℝ) ((h : ℝ) * α) :=
              (Finset.sum_image (f := fun h : ℕ => expBound (M : ℝ) ((h : ℝ) * α))
                (fun a ha b hb h => hinj ha hb h)).symm
          _ ≤ ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun _ _ _ => expBound_nonneg (Nat.cast_nonneg M) _)
      linarith
    calc ∑ k₁ ∈ K, (c k₁) ^ 2 *
            ((M : ℝ) + ∑ k₂ ∈ K.filter (· ≠ k₁),
              expBound (M : ℝ) ((((k₁ : ℤ) - (k₂ : ℤ)).natAbs : ℝ) * α))
        ≤ ∑ k₁ ∈ K, (c k₁) ^ 2 *
            ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α)) :=
          Finset.sum_le_sum fun k₁ hk₁ =>
            mul_le_mul_of_nonneg_left (by linarith [hinner_k₁ k₁ hk₁]) (sq_nonneg _)
      _ = (∑ k ∈ K, (c k) ^ 2) *
            ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α)) :=
          (Finset.sum_mul _ _ _).symm
  -- Step 4: Plug in `sum_expBound_const_le` with `H = N / M` and `B = M`
  have hexp_sum := sum_expBound_const_le hq hcop (Nat.cast_nonneg M) happrox (N / M)
  have hNM_mul_M : ((N / M : ℕ) : ℝ) * (M : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N M
  have hM_le_NU_real : (M : ℝ) ≤ (N : ℝ) / (U : ℝ) := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr hU)]
    have : M * U ≤ (N / U) * U := Nat.mul_le_mul_right U hM_le_NU
    exact_mod_cast this.trans (Nat.div_mul_le_self N U)
  have hNM_le_2NV : ((N / M : ℕ) : ℝ) ≤ 2 * (N : ℝ) / (V : ℝ) := by
    have h1 : ((N / M : ℕ) : ℝ) * (V : ℝ) ≤ 2 * (N : ℝ) := by
      have hV_le : (V : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hV_lt_2M.le
      calc ((N / M : ℕ) : ℝ) * (V : ℝ) ≤ ((N / M : ℕ) : ℝ) * (2 * (M : ℝ)) :=
            mul_le_mul_of_nonneg_left hV_le (Nat.cast_nonneg _)
        _ = 2 * (((N / M : ℕ) : ℝ) * (M : ℝ)) := by ring
        _ ≤ 2 * (N : ℝ) := by linarith
    rw [le_div_iff₀ (Nat.cast_pos.mpr hV)]
    exact h1
  have hlogq_ge1 : 1 ≤ 1 + Real.log (q : ℝ) := by
    linarith [Real.log_nonneg (Nat.one_le_cast.mpr hq)]
  have hbracket :
      (M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α) ≤
        14 * (1 + Real.log (q : ℝ)) *
          ((N : ℝ) / (q : ℝ) + (N : ℝ) / (U : ℝ) + (N : ℝ) / (V : ℝ) + (q : ℝ)) := by
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
    have hterm_Nq : ((N / M : ℕ) : ℝ) / (q : ℝ) * (M : ℝ) ≤ (N : ℝ) / (q : ℝ) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hNM_mul_M hq_pos.le
    have h1 : 3 * (((N / M : ℕ) : ℝ) / (q : ℝ) + 1) * (M : ℝ) ≤
        3 * ((N : ℝ) / (q : ℝ)) + 3 * (M : ℝ) := by
      have : 3 * (((N / M : ℕ) : ℝ) / (q : ℝ) + 1) * (M : ℝ) =
          3 * (((N / M : ℕ) : ℝ) / (q : ℝ) * (M : ℝ)) + 3 * (M : ℝ) := by ring
      linarith
    have h2 : (M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α) ≤
        6 * ((N : ℝ) / (q : ℝ)) + 7 * (M : ℝ) +
          2 * (((N / M : ℕ) : ℝ) + (q : ℝ)) * (1 + Real.log (q : ℝ)) := by linarith
    have h3 : 6 * ((N : ℝ) / (q : ℝ)) + 7 * (M : ℝ) ≤
        (6 * ((N : ℝ) / (q : ℝ)) + 7 * ((N : ℝ) / (U : ℝ))) * (1 + Real.log (q : ℝ)) := by
      have ha : 0 ≤ 6 * ((N : ℝ) / (q : ℝ)) + 7 * ((N : ℝ) / (U : ℝ)) := by positivity
      nlinarith
    have h4 : 2 * (((N / M : ℕ) : ℝ) + (q : ℝ)) * (1 + Real.log (q : ℝ)) ≤
        (4 * ((N : ℝ) / (V : ℝ)) + 2 * (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
      have : 2 * (((N / M : ℕ) : ℝ) + (q : ℝ)) ≤ 4 * ((N : ℝ) / (V : ℝ)) + 2 * (q : ℝ) := by
        have : 2 * (N : ℝ) / (V : ℝ) = 2 * ((N : ℝ) / (V : ℝ)) := by ring
        linarith
      exact mul_le_mul_of_nonneg_right this hlogq_nn
    nlinarith [show (0 : ℝ) ≤ (N : ℝ) / (q : ℝ) by positivity,
               show (0 : ℝ) ≤ (N : ℝ) / (U : ℝ) by positivity,
               show (0 : ℝ) ≤ (N : ℝ) / (V : ℝ) by positivity,
               show (0 : ℝ) ≤ (q : ℝ) by positivity]
  -- Step 5: Combine Cauchy–Schwarz, `L²` bounds, and take square roots
  have hsq_bound :
      ‖∑ m ∈ I, (Λ m : ℂ) * f m‖ ^ 2 ≤
        (13 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * Real.sqrt (1 + Real.log (q : ℝ)) *
          ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
            (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ)))) ^ 2 := by
    have hprod_L2 :
        (∑ m ∈ I, (Λ m) ^ 2) * (∑ k ∈ K, (c k) ^ 2) ≤
          12 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 4 := by
      calc (∑ m ∈ I, (Λ m) ^ 2) * (∑ k ∈ K, (c k) ^ 2)
          ≤ (12 * (M : ℝ) * (1 + Real.log (2 * (N : ℝ)))) *
              (((N / M : ℕ) : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 3) :=
            mul_le_mul hL2_Λ hL2_c (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = 12 * (((N / M : ℕ) : ℝ) * (M : ℝ)) * (1 + Real.log (2 * (N : ℝ))) ^ 4 := by ring
        _ ≤ 12 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 4 := by
            gcongr
    have hcombined :
        ‖∑ m ∈ I, (Λ m : ℂ) * f m‖ ^ 2 ≤
          168 * (1 + Real.log (2 * (N : ℝ))) ^ 4 * (1 + Real.log (q : ℝ)) *
            ((N : ℝ) * ((N : ℝ) / (q : ℝ) + (N : ℝ) / (U : ℝ) + (N : ℝ) / (V : ℝ) + (q : ℝ))) := by
      calc ‖∑ m ∈ I, (Λ m : ℂ) * f m‖ ^ 2
          ≤ (∑ m ∈ I, (Λ m) ^ 2) * (∑ m ∈ I, ‖f m‖ ^ 2) := hCS
        _ ≤ (∑ m ∈ I, (Λ m) ^ 2) *
              ((∑ k ∈ K, (c k) ^ 2) *
                ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α))) :=
            mul_le_mul_of_nonneg_left hinner_sq (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        _ = ((∑ m ∈ I, (Λ m) ^ 2) * (∑ k ∈ K, (c k) ^ 2)) *
              ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N / M), expBound (M : ℝ) ((h : ℝ) * α)) := by ring
        _ ≤ (12 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 4) *
              (14 * (1 + Real.log (q : ℝ)) *
                ((N : ℝ) / (q : ℝ) + (N : ℝ) / (U : ℝ) + (N : ℝ) / (V : ℝ) + (q : ℝ))) :=
            mul_le_mul hprod_L2 hbracket
              (add_nonneg (Nat.cast_nonneg M) (mul_nonneg (by norm_num)
                (Finset.sum_nonneg fun _ _ => expBound_nonneg (Nat.cast_nonneg M) _)))
              (by positivity)
        _ = 168 * (1 + Real.log (2 * (N : ℝ))) ^ 4 * (1 + Real.log (q : ℝ)) *
              ((N : ℝ) * ((N : ℝ) / (q : ℝ) + (N : ℝ) / (U : ℝ) + (N : ℝ) / (V : ℝ) + (q : ℝ))) := by
            ring
    refine hcombined.trans ?_
    have h4sq :
        (N : ℝ) * ((N : ℝ) / (q : ℝ) + (N : ℝ) / (U : ℝ) + (N : ℝ) / (V : ℝ) + (q : ℝ)) ≤
          ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
            (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ))) ^ 2 := by
      have ha : ((N : ℝ) / Real.sqrt (q : ℝ)) ^ 2 = (N : ℝ) * ((N : ℝ) / (q : ℝ)) := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg q)]; ring
      have hb : ((N : ℝ) / Real.sqrt (U : ℝ)) ^ 2 = (N : ℝ) * ((N : ℝ) / (U : ℝ)) := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg U)]; ring
      have hc : ((N : ℝ) / Real.sqrt (V : ℝ)) ^ 2 = (N : ℝ) * ((N : ℝ) / (V : ℝ)) := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg V)]; ring
      have hd : (Real.sqrt ((N : ℝ) * (q : ℝ))) ^ 2 = (N : ℝ) * (q : ℝ) :=
        Real.sq_sqrt (by positivity)
      set A1 := (N : ℝ) / Real.sqrt (q : ℝ)
      set A2 := (N : ℝ) / Real.sqrt (U : ℝ)
      set A3 := (N : ℝ) / Real.sqrt (V : ℝ)
      set A4 := Real.sqrt ((N : ℝ) * (q : ℝ))
      have hA1 : 0 ≤ A1 := by positivity
      have hA2 : 0 ≤ A2 := by positivity
      have hA3 : 0 ≤ A3 := by positivity
      have hA4 : 0 ≤ A4 := by positivity
      nlinarith
    have hrhs_eq :
        (13 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * Real.sqrt (1 + Real.log (q : ℝ)) *
          ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
            (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ)))) ^ 2 =
        169 * (1 + Real.log (2 * (N : ℝ))) ^ 4 * (1 + Real.log (q : ℝ)) *
          ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
            (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ))) ^ 2 := by
      have hsq_q : Real.sqrt (1 + Real.log (q : ℝ)) ^ 2 = 1 + Real.log (q : ℝ) :=
        Real.sq_sqrt hlogq_nn
      calc (13 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * Real.sqrt (1 + Real.log (q : ℝ)) *
              ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
                (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ)))) ^ 2
          = 169 * (1 + Real.log (2 * (N : ℝ))) ^ 4 * (Real.sqrt (1 + Real.log (q : ℝ)) ^ 2) *
              ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
                (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ))) ^ 2 := by ring
        _ = 169 * (1 + Real.log (2 * (N : ℝ))) ^ 4 * (1 + Real.log (q : ℝ)) *
              ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
                (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ))) ^ 2 := by
            rw [hsq_q]
    rw [hrhs_eq]
    have hcoeff_le : 168 * (1 + Real.log (2 * (N : ℝ))) ^ 4 * (1 + Real.log (q : ℝ)) ≤
        169 * (1 + Real.log (2 * (N : ℝ))) ^ 4 * (1 + Real.log (q : ℝ)) := by
      have : 0 ≤ (1 + Real.log (2 * (N : ℝ))) ^ 4 * (1 + Real.log (q : ℝ)) := by positivity
      linarith
    exact mul_le_mul hcoeff_le h4sq (by positivity) (by positivity)
  exact le_of_sq_le_sq hsq_bound (by positivity)

/-- Full Type II bound for `vaughanT3` by summing over `Nat.log 2 N + 1` dyadic blocks. -/
theorem norm_vaughanT3_le {U V N q : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hN : 1 ≤ N)
    (hq : 1 ≤ q) (hqN : q ≤ N) {a : ℤ} (hcop : Nat.Coprime a.natAbs q) {α : ℝ}
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ‖vaughanT3 U V N α‖ ≤
      26 * (1 + Real.log (2 * (N : ℝ))) ^ 4 *
        ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
          (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ))) := by
  unfold vaughanT3
  -- Partition `Ioc V (N / U)` by dyadic blocks `I_j = {m ∈ Ioc V (N / U) | 2^j < m ≤ 2^(j+1)}`
  set J : ℕ := Nat.log 2 N + 1
  have hpart :
      ∑ m ∈ Finset.Ioc V (N / U), (Λ m : ℂ) *
          ∑ k ∈ Finset.Ioc U (N / m),
            (Stage11BombieriVinogradov.vaughanMollifier U k : ℂ) * e (((m * k : ℕ) : ℝ) * α) =
        ∑ j ∈ Finset.range J,
          ∑ m ∈ (Finset.Ioc V (N / U)).filter (fun m => 2 ^ j < m ∧ m ≤ 2 * 2 ^ j),
            (Λ m : ℂ) * ∑ k ∈ Finset.Ioc U (N / m),
              (Stage11BombieriVinogradov.vaughanMollifier U k : ℂ) * e (((m * k : ℕ) : ℝ) * α) := by
    let F : ℕ → ℂ := fun m => (Λ m : ℂ) * ∑ k ∈ Finset.Ioc U (N / m),
      (Stage11BombieriVinogradov.vaughanMollifier U k : ℂ) * e (((m * k : ℕ) : ℝ) * α)
    change ∑ m ∈ Finset.Ioc V (N / U), F m =
      ∑ j ∈ Finset.range J, ∑ m ∈ (Finset.Ioc V (N / U)).filter (fun m => 2 ^ j < m ∧ m ≤ 2 * 2 ^ j), F m
    -- Map each `m ≥ 2` to `j = Nat.log 2 (m - 1)` so `2^j ≤ m - 1 < 2^(j+1)`, i.e. `2^j < m ≤ 2 * 2^j`
    have hmaps : ∀ m ∈ Finset.Ioc V (N / U), Nat.log 2 (m - 1) ∈ Finset.range J := by
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      simp only [Finset.mem_range, J]
      have hm_le : m - 1 ≤ N := (Nat.sub_le m 1).trans (hm.2.trans (Nat.div_le_self N U))
      exact Nat.lt_succ_of_le (Nat.log_mono_right hm_le)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hm, hj⟩
      have hm1 : 1 ≤ m - 1 := by omega
      have hlb : 2 ^ j ≤ m - 1 := hj ▸ Nat.pow_log_le_self 2 (by omega)
      have hub : m - 1 < 2 ^ (j + 1) := hj ▸ Nat.lt_pow_succ_log_self (by norm_num) (m - 1)
      have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      exact ⟨hm, by omega, by omega⟩
    · rintro ⟨hm, h1, h2⟩
      refine ⟨hm, ?_⟩
      have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      have hle : j ≤ Nat.log 2 (m - 1) := Nat.le_log_of_pow_le (by norm_num) (by omega)
      have hlt : Nat.log 2 (m - 1) < j + 1 := Nat.log_lt_of_lt_pow (by omega) (by omega)
      omega
  rw [hpart]
  have hlog2N_nn : 0 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_nonneg (by have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN; linarith)
  have hlogq_le : 1 + Real.log (q : ℝ) ≤ 1 + Real.log (2 * (N : ℝ)) := by
    have hq_le : (q : ℝ) ≤ 2 * (N : ℝ) := by
      have : (q : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hqN
      linarith
    linarith [Real.log_le_log (Nat.cast_pos.mpr hq) hq_le]
  have hsqrt_q : Real.sqrt (1 + Real.log (q : ℝ)) ≤ 1 + Real.log (2 * (N : ℝ)) := by
    have h1 : 1 ≤ 1 + Real.log (2 * (N : ℝ)) := by linarith
    calc Real.sqrt (1 + Real.log (q : ℝ))
        ≤ Real.sqrt (1 + Real.log (2 * (N : ℝ))) := Real.sqrt_le_sqrt hlogq_le
      _ ≤ 1 + Real.log (2 * (N : ℝ)) := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
  have hJ_le : (J : ℝ) ≤ 2 * (1 + Real.log (2 * (N : ℝ))) := by
    have hpow : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) :=
      Nat.cast_le.mpr (Nat.pow_log_le_self 2 (by omega))
    have hlog_pow : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hpow
      simpa [Nat.cast_pow, Real.log_pow] using h1
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogN_le : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (Nat.cast_pos.mpr hN) (by linarith [Nat.cast_nonneg (α := ℝ) N])
    have hnat : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (2 * (N : ℝ)) := by
      have : (Nat.log 2 N : ℝ) * (1 / 2) ≤ Real.log (2 * (N : ℝ)) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 N)]
      linarith
    simp only [J]; push_cast; linarith
  set B_fac : ℝ := (N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
    (N : ℝ) / Real.sqrt (V : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ))
  calc ‖∑ j ∈ Finset.range J,
          ∑ m ∈ (Finset.Ioc V (N / U)).filter (fun m => 2 ^ j < m ∧ m ≤ 2 * 2 ^ j),
            (Λ m : ℂ) * ∑ k ∈ Finset.Ioc U (N / m),
              (Stage11BombieriVinogradov.vaughanMollifier U k : ℂ) * e (((m * k : ℕ) : ℝ) * α)‖
      ≤ ∑ j ∈ Finset.range J,
          ‖∑ m ∈ (Finset.Ioc V (N / U)).filter (fun m => 2 ^ j < m ∧ m ≤ 2 * 2 ^ j),
            (Λ m : ℂ) * ∑ k ∈ Finset.Ioc U (N / m),
              (Stage11BombieriVinogradov.vaughanMollifier U k : ℂ) * e (((m * k : ℕ) : ℝ) * α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range J,
          13 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * Real.sqrt (1 + Real.log (q : ℝ)) * B_fac :=
        Finset.sum_le_sum fun j _ =>
          norm_vaughanT3_dyadic_le hU hV hN (Nat.one_le_two_pow) hq hcop happrox
    _ = (J : ℝ) * (13 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * Real.sqrt (1 + Real.log (q : ℝ)) * B_fac) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * (1 + Real.log (2 * (N : ℝ)))) *
          (13 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * (1 + Real.log (2 * (N : ℝ))) * B_fac) := by
        apply mul_le_mul hJ_le _ (by positivity) (by positivity)
        have hB_nn : 0 ≤ B_fac := by positivity
        have h13 : 0 ≤ 13 * (1 + Real.log (2 * (N : ℝ))) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hsqrt_q h13]
    _ = 26 * (1 + Real.log (2 * (N : ℝ))) ^ 4 * B_fac := by ring

/-! ## Section 5: Vaughan's Exponential Sum Bound & Vinogradov's Minor-Arc `L^∞` Theorem -/

/-- **Unconditional Vinogradov–Vaughan Exponential Sum Bound (1977)**:
for all `N ≥ 3`, `1 ≤ q ≤ N`, `a : ℤ` with `Nat.Coprime a.natAbs q`, and `|α - a/q| ≤ 1/q²`:
`‖S N α‖ ≤ 130 · (1 + log (2 N))⁴ · (N / √q + N^{4/5} + √(N q))`. -/
theorem vaughan_exp_sum_bound {N q : ℕ} (hN : 3 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N)
    {a : ℤ} (hcop : Nat.Coprime a.natAbs q) {α : ℝ}
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ‖S N α‖ ≤
      130 * (1 + Real.log (2 * (N : ℝ))) ^ 4 *
        ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((N : ℝ) * (q : ℝ))) := by
  have hN1 : 1 ≤ N := by omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
  set U : ℕ := ⌊(N : ℝ) ^ ((2 : ℝ) / 5)⌋₊ with hU_def
  have hN25_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) :=
    Real.one_le_rpow hN_ge1 (by norm_num)
  have hU1 : 1 ≤ U := (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hN25_ge1)
  have hU_le : (U : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := Nat.floor_le (by positivity)
  have hN25_lt : (N : ℝ) ^ ((2 : ℝ) / 5) < (U : ℝ) + 1 := Nat.lt_floor_add_one _
  have hU_lb : (N : ℝ) ^ ((2 : ℝ) / 5) / 2 ≤ (U : ℝ) := by
    have h1 : (1 : ℝ) ≤ (U : ℝ) := Nat.one_le_cast.mpr hU1
    linarith
  have hU_le_N : (U : ℝ) ≤ (N : ℝ) := by
    refine hU_le.trans ?_
    calc (N : ℝ) ^ ((2 : ℝ) / 5) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  set L : ℝ := 1 + Real.log (2 * (N : ℝ))
  have hL_ge1 : 1 ≤ L := by
    have : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hL_ge_logN : Real.log (N : ℝ) ≤ L := by
    have h1 : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log hN_pos (by linarith)
    linarith
  have hL_ge_logq : 1 + Real.log (q : ℝ) ≤ L := by
    have hq_le : (q : ℝ) ≤ 2 * (N : ℝ) := by
      have : (q : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hqN
      linarith
    linarith [Real.log_le_log (Nat.cast_pos.mpr hq) hq_le]
  have hL_ge_logU1 : 1 + Real.log ((U + 1 : ℕ) : ℝ) ≤ L := by
    have hU1_le : ((U + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by push_cast; linarith
    linarith [Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos U)) hU1_le]
  have hL_ge_logU21 : 1 + Real.log ((U * U + 1 : ℕ) : ℝ) ≤ L := by
    have hUU_le : ((U * U : ℕ) : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := by
      push_cast
      calc (U : ℝ) * (U : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) * (N : ℝ) ^ ((2 : ℝ) / 5) :=
            mul_le_mul hU_le hU_le (Nat.cast_nonneg U) (by positivity)
        _ = (N : ℝ) ^ (((2 : ℝ) / 5) + ((2 : ℝ) / 5)) := (Real.rpow_add hN_pos _ _).symm
        _ = (N : ℝ) ^ ((4 : ℝ) / 5) := by norm_num
    have hN45_le : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (N : ℝ) := by
      calc (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
        _ = (N : ℝ) := Real.rpow_one _
    have hUU1_le : ((U * U + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by push_cast at hUU_le ⊢; linarith
    linarith [Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos _)) hUU1_le]
  set M_sum : ℝ := (N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) ^ ((4 : ℝ) / 5) +
    Real.sqrt ((N : ℝ) * (q : ℝ))
  have hM_nn : 0 ≤ M_sum := by positivity
  -- Useful term comparisons against `M_sum`
  have hNq_le : (N : ℝ) / (q : ℝ) ≤ (N : ℝ) / Real.sqrt (q : ℝ) := by
    have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := Nat.one_le_cast.mpr hq
    have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    exact div_le_div_of_nonneg_left hN_pos.le (Real.sqrt_pos.mpr (by positivity)) hsq
  have hq_le_sqrtNq : (q : ℝ) ≤ Real.sqrt ((N : ℝ) * (q : ℝ)) := by
    rw [Real.le_sqrt (Nat.cast_nonneg q) (by positivity)]
    have : (q : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hqN
    nlinarith
  have hN25_le_N45 : (N : ℝ) ^ ((2 : ℝ) / 5) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
  have hsqrtN_le_N45 : Real.sqrt (N : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
  have hUU_le_N45 : ((U * U : ℕ) : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := by
    push_cast
    calc (U : ℝ) * (U : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) * (N : ℝ) ^ ((2 : ℝ) / 5) :=
          mul_le_mul hU_le hU_le (Nat.cast_nonneg U) (by positivity)
      _ = (N : ℝ) ^ (((2 : ℝ) / 5) + ((2 : ℝ) / 5)) := (Real.rpow_add hN_pos _ _).symm
      _ = (N : ℝ) ^ ((4 : ℝ) / 5) := by norm_num
  have hN_div_sqrtU : (N : ℝ) / Real.sqrt (U : ℝ) ≤ 2 * (N : ℝ) ^ ((4 : ℝ) / 5) := by
    have hsqrtU_lb : (N : ℝ) ^ ((1 : ℝ) / 5) / 2 ≤ Real.sqrt (U : ℝ) := by
      have h1 : ((N : ℝ) ^ ((1 : ℝ) / 5) / 2) ^ 2 ≤ (U : ℝ) := by
        calc ((N : ℝ) ^ ((1 : ℝ) / 5) / 2) ^ 2
            = ((N : ℝ) ^ ((1 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 5)) / 4 := by ring
          _ = (N : ℝ) ^ (((1 : ℝ) / 5) + ((1 : ℝ) / 5)) / 4 := by
              rw [← Real.rpow_add hN_pos]
          _ = (N : ℝ) ^ ((2 : ℝ) / 5) / 4 := by norm_num
          _ ≤ (N : ℝ) ^ ((2 : ℝ) / 5) / 2 := by
              have : 0 ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := by positivity
              linarith
          _ ≤ (U : ℝ) := hU_lb
      exact (Real.le_sqrt (by positivity) (Nat.cast_nonneg U)).mpr h1
    calc (N : ℝ) / Real.sqrt (U : ℝ)
        ≤ (N : ℝ) / ((N : ℝ) ^ ((1 : ℝ) / 5) / 2) :=
          div_le_div_of_nonneg_left hN_pos.le (by positivity) hsqrtU_lb
      _ = 2 * ((N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 5)) := by ring
      _ = 2 * (N : ℝ) ^ ((4 : ℝ) / 5) := by
          congr 1
          rw [div_eq_iff (Real.rpow_pos_of_pos hN_pos _).ne', ← Real.rpow_add hN_pos]
          norm_num
  -- Bound each of the 5 pieces in terms of `L^4 * M_sum`
  have hL_le_L2 : L ≤ L ^ 2 := by nlinarith
  have hL2_le_L4 : L ^ 2 ≤ L ^ 4 := by
    have : L ^ 4 = (L ^ 2) ^ 2 := by ring
    nlinarith
  have hL_le_L4 : L ≤ L ^ 4 := hL_le_L2.trans hL2_le_L4
  have h1_le_L4 : 1 ≤ L ^ 4 := hL_ge1.trans hL_le_L4
  have hDiff : ‖S N α - S_Λ N α‖ ≤ 1 * L ^ 4 * M_sum := by
    calc ‖S N α - S_Λ N α‖ ≤ Real.sqrt (N : ℝ) * Real.log (N : ℝ) := norm_S_sub_S_Λ_le N hN1 α
      _ ≤ (N : ℝ) ^ ((4 : ℝ) / 5) * L :=
          mul_le_mul hsqrtN_le_N45 hL_ge_logN (Real.log_nonneg hN_ge1) (by positivity)
      _ ≤ M_sum * L ^ 4 := by
          have : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ M_sum := by
            simp only [M_sum]; linarith [show (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (q : ℝ) by positivity,
              Real.sqrt_nonneg ((N : ℝ) * (q : ℝ))]
          exact mul_le_mul this hL_le_L4 (by linarith) hM_nn
      _ = 1 * L ^ 4 * M_sum := by ring
  have hT0 : ‖vaughanT0 U N α‖ ≤ 6 * L ^ 4 * M_sum := by
    have h1 := norm_vaughanT0_le (N := N) hU1 α
    have h2 : (U : ℝ) ≤ M_sum := by
      have : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ M_sum := by
        simp only [M_sum]; linarith [show (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (q : ℝ) by positivity,
          Real.sqrt_nonneg ((N : ℝ) * (q : ℝ))]
      linarith
    have h3 : 6 * (U : ℝ) ≤ 6 * (1 * M_sum) := by linarith
    have h4 : 6 * (1 * M_sum) ≤ 6 * (L ^ 4 * M_sum) := by
      gcongr
    linarith
  have hT1 : ‖vaughanT1 U N α‖ ≤ 9 * L ^ 4 * M_sum := by
    have h1 := norm_vaughanT1_le hU1 hN1 hq hcop happrox
    have hinner :
        (6 * (N : ℝ) / (q : ℝ)) * (1 + Real.log ((U + 1 : ℕ) : ℝ)) +
          ((U : ℝ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ)) ≤ 9 * L * M_sum := by
      have ha : (6 * (N : ℝ) / (q : ℝ)) * (1 + Real.log ((U + 1 : ℕ) : ℝ)) ≤
          6 * ((N : ℝ) / Real.sqrt (q : ℝ)) * L := by
        have h6 : 6 * (N : ℝ) / (q : ℝ) ≤ 6 * ((N : ℝ) / Real.sqrt (q : ℝ)) := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hNq_le (by norm_num)
        exact mul_le_mul h6 hL_ge_logU1
          (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr (Nat.succ_pos U))]) (by positivity)
      have hb : ((U : ℝ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ)) ≤
          ((N : ℝ) ^ ((4 : ℝ) / 5) + 3 * Real.sqrt ((N : ℝ) * (q : ℝ))) * L :=
        mul_le_mul (by linarith) hL_ge_logq
          (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr hq)]) (by positivity)
      simp only [M_sum]
      nlinarith [show (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (q : ℝ) by positivity,
                 show (0 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) by positivity,
                 Real.sqrt_nonneg ((N : ℝ) * (q : ℝ))]
    calc ‖vaughanT1 U N α‖
        ≤ Real.log (N : ℝ) * (9 * L * M_sum) :=
          h1.trans (mul_le_mul_of_nonneg_left hinner (Real.log_nonneg hN_ge1))
      _ ≤ L * (9 * L * M_sum) := mul_le_mul_of_nonneg_right hL_ge_logN (by positivity)
      _ = 9 * L ^ 2 * M_sum := by ring
      _ ≤ 9 * L ^ 4 * M_sum := by gcongr
  have hT2 : ‖vaughanT2 U U N α‖ ≤ 9 * L ^ 4 * M_sum := by
    have h1 := norm_vaughanT2_le hU1 hU1 hN1 hq hcop happrox
    have hinner :
        (6 * (N : ℝ) / (q : ℝ)) * (1 + Real.log ((U * U + 1 : ℕ) : ℝ)) +
          ((U * U : ℕ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ)) ≤ 9 * L * M_sum := by
      have ha : (6 * (N : ℝ) / (q : ℝ)) * (1 + Real.log ((U * U + 1 : ℕ) : ℝ)) ≤
          6 * ((N : ℝ) / Real.sqrt (q : ℝ)) * L := by
        have h6 : 6 * (N : ℝ) / (q : ℝ) ≤ 6 * ((N : ℝ) / Real.sqrt (q : ℝ)) := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hNq_le (by norm_num)
        exact mul_le_mul h6 hL_ge_logU21
          (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr (Nat.succ_pos (U * U)))]) (by positivity)
      have hb : (((U * U : ℕ) : ℝ) + 3 * (q : ℝ)) * (1 + Real.log (q : ℝ)) ≤
          ((N : ℝ) ^ ((4 : ℝ) / 5) + 3 * Real.sqrt ((N : ℝ) * (q : ℝ))) * L :=
        mul_le_mul (by linarith) hL_ge_logq
          (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr hq)]) (by positivity)
      simp only [M_sum]
      nlinarith [show (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (q : ℝ) by positivity,
                 show (0 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) by positivity,
                 Real.sqrt_nonneg ((N : ℝ) * (q : ℝ))]
    calc ‖vaughanT2 U U N α‖
        ≤ Real.log (N : ℝ) * (9 * L * M_sum) :=
          h1.trans (mul_le_mul_of_nonneg_left hinner (Real.log_nonneg hN_ge1))
      _ ≤ L * (9 * L * M_sum) := mul_le_mul_of_nonneg_right hL_ge_logN (by positivity)
      _ = 9 * L ^ 2 * M_sum := by ring
      _ ≤ 9 * L ^ 4 * M_sum := by gcongr
  have hT3 : ‖vaughanT3 U U N α‖ ≤ 104 * L ^ 4 * M_sum := by
    have h1 := norm_vaughanT3_le hU1 hU1 hN1 hq hqN hcop happrox
    have hfac :
        (N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) / Real.sqrt (U : ℝ) +
          (N : ℝ) / Real.sqrt (U : ℝ) + Real.sqrt ((N : ℝ) * (q : ℝ)) ≤ 4 * M_sum := by
      simp only [M_sum]
      linarith [show (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (q : ℝ) by positivity,
                Real.sqrt_nonneg ((N : ℝ) * (q : ℝ))]
    calc ‖vaughanT3 U U N α‖
        ≤ 26 * L ^ 4 * (4 * M_sum) := h1.trans (mul_le_mul_of_nonneg_left hfac (by positivity))
      _ = 104 * L ^ 4 * M_sum := by ring
  -- Combine via triangle inequality
  have hdecomp : S N α = (S N α - S_Λ N α) +
      (vaughanT0 U N α + vaughanT1 U N α - vaughanT2 U U N α - vaughanT3 U U N α) := by
    rw [← S_Λ_vaughan_decomp (U := U) (V := U) hU1 α]; ring
  rw [hdecomp]
  have htri :
      ‖(S N α - S_Λ N α) +
        (vaughanT0 U N α + vaughanT1 U N α - vaughanT2 U U N α - vaughanT3 U U N α)‖ ≤
        ‖S N α - S_Λ N α‖ + ‖vaughanT0 U N α‖ + ‖vaughanT1 U N α‖ +
          ‖vaughanT2 U U N α‖ + ‖vaughanT3 U U N α‖ := by
    calc ‖(S N α - S_Λ N α) +
            (vaughanT0 U N α + vaughanT1 U N α - vaughanT2 U U N α - vaughanT3 U U N α)‖
        ≤ ‖S N α - S_Λ N α‖ +
            ‖vaughanT0 U N α + vaughanT1 U N α - vaughanT2 U U N α - vaughanT3 U U N α‖ :=
          norm_add_le _ _
      _ ≤ ‖S N α - S_Λ N α‖ +
            (‖vaughanT0 U N α + vaughanT1 U N α - vaughanT2 U U N α‖ + ‖vaughanT3 U U N α‖) := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ‖S N α - S_Λ N α‖ +
            ((‖vaughanT0 U N α + vaughanT1 U N α‖ + ‖vaughanT2 U U N α‖) + ‖vaughanT3 U U N α‖) := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ‖S N α - S_Λ N α‖ +
            (((‖vaughanT0 U N α‖ + ‖vaughanT1 U N α‖) + ‖vaughanT2 U U N α‖) + ‖vaughanT3 U U N α‖) := by
          gcongr; exact norm_add_le _ _
      _ = ‖S N α - S_Λ N α‖ + ‖vaughanT0 U N α‖ + ‖vaughanT1 U N α‖ +
            ‖vaughanT2 U U N α‖ + ‖vaughanT3 U U N α‖ := by ring
  linarith [show 1 * L ^ 4 * M_sum + 6 * L ^ 4 * M_sum + 9 * L ^ 4 * M_sum +
      9 * L ^ 4 * M_sum + 104 * L ^ 4 * M_sum ≤ 130 * L ^ 4 * M_sum by
    have : 0 ≤ L ^ 4 * M_sum := by positivity
    linarith]

/-- Elementary growth dominance: for any `k ≥ 0` and `ε > 0`, eventually `(log x)^k ≤ x^ε`. -/
private theorem exists_log_rpow_le_rpow (k ε : ℝ) (hk : 0 ≤ k) (hε : 0 < ε) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → (Real.log x) ^ k ≤ x ^ ε := by
  by_cases hk0 : k = 0
  · refine ⟨1, le_rfl, fun x hx => ?_⟩
    rw [hk0, Real.rpow_zero]
    exact Real.one_le_rpow hx hε.le
  have hk_pos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
  set c : ℝ := ε / (2 * k) with hc_def
  have hc_pos : 0 < c := by positivity
  set C0 : ℝ := (1 / c) ^ k
  have hC0_pos : 0 < C0 := Real.rpow_pos_of_pos (by positivity) k
  set X₀ : ℝ := max 1 (C0 ^ (2 / ε))
  refine ⟨X₀, le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx_pos : 0 < x := by linarith
  have hx_C0 : C0 ^ (2 / ε) ≤ x := le_trans (le_max_right _ _) hx
  -- `c * log x = log (x^c) ≤ x^c`, so `log x ≤ (1/c) * x^c`
  have hlog_le : Real.log x ≤ (1 / c) * x ^ c := by
    have h1 : Real.log (x ^ c) ≤ x ^ c := by
      have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos c)
      linarith
    rw [Real.log_rpow hx_pos] at h1
    have h2 : Real.log x ≤ x ^ c / c := (le_div_iff₀' hc_pos).mpr h1
    linarith [show x ^ c / c = (1 / c) * x ^ c by ring]
  have hpow1 : (Real.log x) ^ k ≤ C0 * x ^ (ε / 2) := by
    calc (Real.log x) ^ k
        ≤ ((1 / c) * x ^ c) ^ k :=
          Real.rpow_le_rpow (Real.log_nonneg hx1) hlog_le hk
      _ = (1 / c) ^ k * (x ^ c) ^ k := Real.mul_rpow (by positivity) (by positivity)
      _ = C0 * x ^ (c * k) := by rw [← Real.rpow_mul hx_pos.le]
      _ = C0 * x ^ (ε / 2) := by
          congr 2
          simp only [hc_def]; field_simp [hk_pos.ne']
  have hC0_le : C0 ≤ x ^ (ε / 2) := by
    calc C0 = (C0 ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul hC0_pos.le]
          have : (2 / ε) * (ε / 2) = 1 := by field_simp [hε.ne']
          rw [this, Real.rpow_one]
      _ ≤ x ^ (ε / 2) := Real.rpow_le_rpow (by positivity) hx_C0 (by positivity)
  calc (Real.log x) ^ k
      ≤ C0 * x ^ (ε / 2) := hpow1
    _ ≤ x ^ (ε / 2) * x ^ (ε / 2) := mul_le_mul_of_nonneg_right hC0_le (by positivity)
    _ = x ^ (ε / 2 + ε / 2) := (Real.rpow_add hx_pos _ _).symm
    _ = x ^ ε := by congr 1; ring

/-- **Headline Unconditional Vinogradov Minor-Arc `L^∞` Bound**:
for every `A ≥ 0`, there exist `B ≥ 1` and `C > 0` such that for all `N ≥ 3` and every
`α ∈ minorArcs N ((Real.log N) ^ B)`,
`‖S N α‖ ≤ C · N / (Real.log N) ^ A`. -/
theorem vinogradov_minor_arc_sup_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      ∀ α ∈ minorArcs N ((Real.log (N : ℝ)) ^ B),
        ‖S N α‖ ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  set B : ℝ := 2 * A + 10
  have hB1 : 1 ≤ B := by linarith
  -- Choose `X₁` so `(log x)^(2 B) ≤ x^(1/2)` (hence `(log x)^(2 B) < x` for `x ≥ max 2 X₁`)
  -- and `X₂` so `(log x)^(A + 4) ≤ x^(1/5)`
  obtain ⟨X₁, hX₁_1, hX₁⟩ := exists_log_rpow_le_rpow (2 * B) (1 / 2) (by linarith) (by norm_num)
  obtain ⟨X₂, hX₂_1, hX₂⟩ := exists_log_rpow_le_rpow (A + 4) (1 / 5) (by linarith) (by norm_num)
  set X₀ : ℝ := max (max 3 X₁) X₂
  have hX₀_ge3 : 3 ≤ X₀ := le_trans (le_max_left 3 X₁) (le_max_left _ _)
  have hlog3_gt1 : 1 < Real.log (3 : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    linarith [Real.exp_one_lt_d9]
  have hlogX₀_pos : 0 < Real.log X₀ :=
    lt_trans zero_lt_one (lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) hX₀_ge3))
  set C : ℝ := max 31590 (6 * (Real.log X₀) ^ A)
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 31590) (le_max_left _ _)
  refine ⟨B, C, hB1, hC_pos, fun N hN α hα => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN_ge3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN_gt1 : 1 < Real.log (N : ℝ) :=
    lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) hN_ge3)
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  by_cases hlarge : X₀ ≤ (N : ℝ)
  · -- Large-`N` regime: Dirichlet approximation + Vaughan's bound
    set Q : ℝ := (Real.log (N : ℝ)) ^ B
    have hQ1 : 1 ≤ Q := Real.one_le_rpow hlogN_gt1.le (by linarith)
    have hQ_pos : 0 < Q := by linarith
    have hN_ge_X₁ : X₁ ≤ (N : ℝ) := le_trans (le_trans (le_max_right 3 X₁) (le_max_left _ _)) hlarge
    have hN_ge_X₂ : X₂ ≤ (N : ℝ) := le_trans (le_max_right _ _) hlarge
    have hQ2_lt_N : Q ^ 2 < (N : ℝ) := by
      have h1 : Q ^ 2 = (Real.log (N : ℝ)) ^ (2 * B) := by
        rw [← Real.rpow_natCast Q 2, ← Real.rpow_mul hlogN_pos.le]
        congr 1; push_cast; ring
      have h2 : (Real.log (N : ℝ)) ^ (2 * B) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := hX₁ (N : ℝ) hN_ge_X₁
      have h3 : (N : ℝ) ^ ((1 : ℝ) / 2) < (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
      rw [Real.rpow_one] at h3
      linarith
    have hQN : Q < (N : ℝ) := by nlinarith
    obtain ⟨q, hq1, hQ_lt_q, hq_le_NQ, a, hcop, happrox⟩ :=
      minorArcs_dirichlet_approx hQ1 hQN hα
    have hqN_real : (q : ℝ) ≤ (N : ℝ) :=
      hq_le_NQ.trans (div_le_self hN_pos.le hQ1)
    have hqN : q ≤ N := by exact_mod_cast hqN_real
    have hvaugh := vaughan_exp_sum_bound hN hq1 hqN hcop happrox
    -- Bound `(1 + log (2 N)) ≤ 3 * log N`
    have hL_le : 1 + Real.log (2 * (N : ℝ)) ≤ 3 * Real.log (N : ℝ) := by
      rw [Real.log_mul (by norm_num) hN_pos.ne']
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hL4_le : (1 + Real.log (2 * (N : ℝ))) ^ 4 ≤ 81 * (Real.log (N : ℝ)) ^ 4 := by
      calc (1 + Real.log (2 * (N : ℝ))) ^ 4
          ≤ (3 * Real.log (N : ℝ)) ^ 4 :=
            pow_le_pow_left₀ (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (N : ℝ))])
              hL_le 4
        _ = 81 * (Real.log (N : ℝ)) ^ 4 := by ring
    -- Bound each of the three terms by `N / (log N)^(A + 4)`
    have hsqrtQ : Real.sqrt Q = (Real.log (N : ℝ)) ^ (A + 5) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlogN_pos.le]
      congr 1; simp only [B]; ring
    have hpow_mono : (Real.log (N : ℝ)) ^ (A + 4) ≤ (Real.log (N : ℝ)) ^ (A + 5) :=
      Real.rpow_le_rpow_of_exponent_le hlogN_gt1.le (by linarith)
    have hterm1 : (N : ℝ) / Real.sqrt (q : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4) := by
      calc (N : ℝ) / Real.sqrt (q : ℝ)
          ≤ (N : ℝ) / Real.sqrt Q :=
            div_le_div_of_nonneg_left hN_pos.le (Real.sqrt_pos.mpr hQ_pos)
              (Real.sqrt_le_sqrt hQ_lt_q.le)
        _ = (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 5) := by rw [hsqrtQ]
        _ ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4) :=
            div_le_div_of_nonneg_left hN_pos.le (Real.rpow_pos_of_pos hlogN_pos _) hpow_mono
    have hterm2 : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4) := by
      have hlog_le_N15 : (Real.log (N : ℝ)) ^ (A + 4) ≤ (N : ℝ) ^ ((1 : ℝ) / 5) :=
        hX₂ (N : ℝ) hN_ge_X₂
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogN_pos _)]
      calc (N : ℝ) ^ ((4 : ℝ) / 5) * (Real.log (N : ℝ)) ^ (A + 4)
          ≤ (N : ℝ) ^ ((4 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 5) :=
            mul_le_mul_of_nonneg_left hlog_le_N15 (by positivity)
        _ = (N : ℝ) ^ (((4 : ℝ) / 5) + ((1 : ℝ) / 5)) := (Real.rpow_add hN_pos _ _).symm
        _ = (N : ℝ) := by norm_num
    have hterm3 : Real.sqrt ((N : ℝ) * (q : ℝ)) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4) := by
      have hNq_le : (N : ℝ) * (q : ℝ) ≤ (N : ℝ) ^ 2 / Q := by
        calc (N : ℝ) * (q : ℝ) ≤ (N : ℝ) * ((N : ℝ) / Q) :=
              mul_le_mul_of_nonneg_left hq_le_NQ hN_pos.le
          _ = (N : ℝ) ^ 2 / Q := by ring
      calc Real.sqrt ((N : ℝ) * (q : ℝ))
          ≤ Real.sqrt ((N : ℝ) ^ 2 / Q) := Real.sqrt_le_sqrt hNq_le
        _ = (N : ℝ) / Real.sqrt Q := by
            rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hN_pos.le]
        _ = (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 5) := by rw [hsqrtQ]
        _ ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4) :=
            div_le_div_of_nonneg_left hN_pos.le (Real.rpow_pos_of_pos hlogN_pos _) hpow_mono
    have hM_le : (N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((N : ℝ) * (q : ℝ)) ≤ 3 * ((N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4)) := by
      linarith
    have hpow_cancel : (Real.log (N : ℝ)) ^ 4 * ((N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4)) =
        (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
      have h4_eq : (Real.log (N : ℝ)) ^ (4 : ℕ) = (Real.log (N : ℝ)) ^ (4 : ℝ) := by
        rw [← Real.rpow_natCast]; norm_num
      rw [h4_eq, Real.rpow_add hlogN_pos]
      have h4 : (Real.log (N : ℝ)) ^ (4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hlogN_pos _).ne'
      have hA_ne : (Real.log (N : ℝ)) ^ A ≠ 0 := (Real.rpow_pos_of_pos hlogN_pos _).ne'
      field_simp [h4, hA_ne]
    calc ‖S N α‖
        ≤ 130 * (1 + Real.log (2 * (N : ℝ))) ^ 4 *
            ((N : ℝ) / Real.sqrt (q : ℝ) + (N : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((N : ℝ) * (q : ℝ))) := hvaugh
      _ ≤ (130 * (81 * (Real.log (N : ℝ)) ^ 4)) *
            (3 * ((N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4))) := by
          apply mul_le_mul _ hM_le (by positivity) (by positivity)
          linarith
      _ = 31590 * ((Real.log (N : ℝ)) ^ 4 * ((N : ℝ) / (Real.log (N : ℝ)) ^ (A + 4))) := by ring
      _ = 31590 * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) := by rw [hpow_cancel]
      _ = 31590 * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring
      _ ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
          apply div_le_div_of_nonneg_right _ (Real.rpow_pos_of_pos hlogN_pos A).le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hN_pos.le
  · -- Small-`N` regime (`3 ≤ N < X₀`): trivial Chebyshev upper bound `‖S N α‖ ≤ 6 N`
    push Not at hlarge
    have htriv : ‖S N α‖ ≤ 6 * (N : ℝ) := by
      refine (norm_S_le N α).trans ?_
      have hle_psi : ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) ≤
          RHDirect.chebyshevPsi (N : ℝ) := by
        unfold RHDirect.chebyshevPsi
        rw [Nat.floor_natCast]
        calc ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ)
            = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Λ p := by
              refine Finset.sum_congr rfl fun p hp => ?_
              exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm
          _ ≤ ∑ n ∈ Finset.range (N + 1), Λ n :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      exact hle_psi.trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (Nat.one_le_cast.mpr hN1))
    have hlog_le : (Real.log (N : ℝ)) ^ A ≤ (Real.log X₀) ^ A :=
      Real.rpow_le_rpow hlogN_pos.le (Real.log_le_log hN_pos hlarge.le) hA
    have hpow_pos : 0 < (Real.log (N : ℝ)) ^ A := Real.rpow_pos_of_pos hlogN_pos A
    have hC_ge : 6 * (Real.log (N : ℝ)) ^ A ≤ C := by
      calc 6 * (Real.log (N : ℝ)) ^ A
          ≤ 6 * (Real.log X₀) ^ A := mul_le_mul_of_nonneg_left hlog_le (by norm_num)
        _ ≤ C := le_max_right _ _
    rw [le_div_iff₀ hpow_pos]
    calc ‖S N α‖ * (Real.log (N : ℝ)) ^ A
        ≤ (6 * (N : ℝ)) * (Real.log (N : ℝ)) ^ A :=
          mul_le_mul_of_nonneg_right htriv hpow_pos.le
      _ = (6 * (Real.log (N : ℝ)) ^ A) * (N : ℝ) := by ring
      _ ≤ C * (N : ℝ) := mul_le_mul_of_nonneg_right hC_ge hN_pos.le

end

#print axioms RHDirect.Vinogradov.dirichlet_approximation
#print axioms RHDirect.Vinogradov.minorArcs_dirichlet_approx
#print axioms RHDirect.Vinogradov.norm_S_sub_S_Λ_le
#print axioms RHDirect.Vinogradov.vaughan_exp_sum_bound
#print axioms RHDirect.Vinogradov.vinogradov_minor_arc_sup_bound

end RHDirect.Vinogradov
