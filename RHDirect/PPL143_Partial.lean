import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# PPL 143 & PPL 150 (Kimberling #13.3 & #13.4, `A131388` / `A131389`) — Partial Structural & Barrier Milestone

**Honest Scope Notice (BOTH PPL 143 and PPL 150 REMAIN OPEN):**
- **PPL 143 (Kimberling #13.3, $25):** Whenever `d(k) > 0`, at least one of `d(k+1), d(k+2), d(k+3)` is positive (equivalently, no run of `3` consecutive negative `d(i)` occurs after `d(1) = 0`). Remains **OPEN**.
- **PPL 150 (Kimberling #13.4, $20):** Whenever `d(k) < 0`, at least one of `d(k+1), d(k+2), d(k+3)` is negative (equivalently, no run of `3` consecutive positive `d(i)` occurs after `d(1) = 0`). Remains **OPEN**.
- This file formalizes the unconditionally proved structural theorems and local-invariant perturbation barriers from `scripts/ppl143_findings.md` using **pure Mathlib signatures only** (`0` custom or `private` definitions in any public theorem signature).

## Verified Theorems
1. `ppl143_existence_well_defined`: Existence of the greedy self-avoiding sequence `(a, d)` from any `1 ≤ a₁` and any `d₁`, with `1 ≤ a k`, `a (k + 1) = a k + d (k + 1)`, exact Step 1 / Step 2 rule, injectivity of `a` and `d` on `1 ≤ ·`, and sign-partition count `s₁(k) + s₂(k) = k - (if d₁ = 0 then 1 else 0)`.
2. `ppl143_uniqueness`: Uniqueness / determinism of any `(a, d)` satisfying the greedy rule from `(a₁, d₁)`.
3. `ppl143_excess_nonneg` & `ppl143_excess_conservation`: Nonnegative excess `2 * ∑ x ∈ S, x - |S|(|S| + 1) ≥ 0` and exact conservation identity `2 * a(k) = 2 + k * (s₂(k) - s₁(k)) + 2 * Δ(D⁺(k)) - 2 * Δ(D⁻(k))`.
4. `ppl143_step2_pigeonhole_bound`: Step-2 pigeonhole upper bound `a(n) ≤ n + s₁(n) ≤ 2 * n - 1` whenever Step 1 fails at `n ≥ 1`.
5. `ppl143_neg_run_lower_bound`: Negative `r`-run lower bound `m_A(k) + r * M_neg(k) + r * (r - 1) / 2 ≤ a(k)`.
6. `ppl143_pos_run_sandwich`: Positive `r`-run (`r ≥ 2`) sandwich `m_A(k-1) + (r-1) * M_pos(k) + (r-1)(r-2)/2 ≤ a(k+r-1) ≤ k + r - 1 + s₁(k)`.
7. `ppl143_infinitely_many_pos_neg`: Unconditional infinitude `∀ N, (∃ n ≥ N, 0 < d n) ∧ (∃ n ≥ N, d n < 0)`.
8. `ppl143_perturbed_neg3_barrier` & `ppl143_perturbed_pos3_barrier`: Perturbed-start counterexamples under Kimberling's exact Step 1 / Step 2 rule producing `NEG3` (`a₁ = 8, d₁ = 0 ↦ d = (0, -1, -2, -3)`) and `POS3` (`a₁ = 2, d₁ = -1 ↦ d = (-1, 1, 2, 3)`), proving no invariant of the local transition rule alone forbids 3-runs.
-/

namespace PPL143

section GreedyStepConstruction

private noncomputable def step1Cands (A D : Finset ℤ) (x : ℤ) : Finset ℤ :=
  (Finset.Ioo (1 - x) 0).filter (fun h => h ∉ D ∧ x + h ∉ A)

private lemma exists_pos_step2_cand (A D : Finset ℤ) (x : ℤ) :
    ∃ h : ℕ, 1 ≤ h ∧ (h : ℤ) ∉ D ∧ x + (h : ℤ) ∉ A := by
  let N : ℕ := A.card + D.card + 1
  let S : Finset ℕ := Finset.Icc 1 N
  let badD : Finset ℕ := (D.filter (fun z => 1 ≤ z)).image Int.toNat
  let badA : Finset ℕ := (A.filter (fun z => 1 ≤ z - x)).image (fun z => (z - x).toNat)
  have hcard_lt : (badD ∪ badA).card < S.card := by
    have h1 : (badD ∪ badA).card ≤ badD.card + badA.card := Finset.card_union_le _ _
    have h2 : badD.card ≤ D.card := le_trans Finset.card_image_le (Finset.card_filter_le _ _)
    have h3 : badA.card ≤ A.card := le_trans Finset.card_image_le (Finset.card_filter_le _ _)
    have hS : S.card = N := by simp [S]
    omega
  obtain ⟨h, hhS, hhbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  refine ⟨h, (Finset.mem_Icc.mp hhS).1, ?_, ?_⟩
  · intro hD
    apply hhbad
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(h : ℤ),
      Finset.mem_filter.mpr ⟨hD, by exact_mod_cast (Finset.mem_Icc.mp hhS).1⟩, Int.toNat_natCast h⟩)
  · intro hA
    apply hhbad
    refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x + (h : ℤ),
      Finset.mem_filter.mpr ⟨hA, by have := (Finset.mem_Icc.mp hhS).1; omega⟩, ?_⟩)
    simp

private noncomputable def greedyStep (A D : Finset ℤ) (x : ℤ) : ℤ :=
  if hne : (step1Cands A D x).Nonempty then
    (step1Cands A D x).max' hne
  else
    letI : DecidablePred (fun h : ℕ => 1 ≤ h ∧ (h : ℤ) ∉ D ∧ x + (h : ℤ) ∉ A) :=
      Classical.decPred _
    (Nat.find (exists_pos_step2_cand A D x) : ℤ)

private lemma greedyStep_spec (A D : Finset ℤ) {x : ℤ} (_hx : 1 ≤ x) :
    (1 - x < greedyStep A D x ∧ greedyStep A D x < 0 ∧
      greedyStep A D x ∉ D ∧ x + greedyStep A D x ∉ A ∧
      ∀ h' : ℤ, greedyStep A D x < h' → h' < 0 → h' ∈ D ∨ x + h' ∈ A) ∨
    ((∀ h : ℤ, 1 - x < h → h < 0 → h ∈ D ∨ x + h ∈ A) ∧
      0 < greedyStep A D x ∧ greedyStep A D x ∉ D ∧ x + greedyStep A D x ∉ A ∧
      ∀ h' : ℤ, 0 < h' → h' < greedyStep A D x → h' ∈ D ∨ x + h' ∈ A) := by
  by_cases hne : (step1Cands A D x).Nonempty
  · left
    have hval : greedyStep A D x = (step1Cands A D x).max' hne := by
      dsimp [greedyStep]; exact dif_pos hne
    rw [hval]
    have hmem := Finset.mem_filter.mp (Finset.max'_mem (step1Cands A D x) hne)
    have hIoo := Finset.mem_Ioo.mp hmem.1
    refine ⟨hIoo.1, hIoo.2, hmem.2.1, hmem.2.2, ?_⟩
    intro h' hlt0 hlt1
    by_contra hnot
    push Not at hnot
    have hmem' : h' ∈ step1Cands A D x :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨lt_trans hIoo.1 hlt0, hlt1⟩, hnot.1, hnot.2⟩
    have hle := Finset.le_max' (step1Cands A D x) h' hmem'
    omega
  · right
    let _ : DecidablePred (fun h : ℕ => 1 ≤ h ∧ (h : ℤ) ∉ D ∧ x + (h : ℤ) ∉ A) :=
      Classical.decPred _
    have hval : greedyStep A D x = (Nat.find (exists_pos_step2_cand A D x) : ℤ) := by
      dsimp [greedyStep]; exact dif_neg hne
    rw [hval]
    have hspec := Nat.find_spec (exists_pos_step2_cand A D x)
    refine ⟨?_, by exact_mod_cast hspec.1, hspec.2.1, hspec.2.2, ?_⟩
    · intro h h1 h2
      by_contra hnot
      push Not at hnot
      exact hne ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨h1, h2⟩, hnot.1, hnot.2⟩⟩
    · intro h' h0 hlt
      have hpos : 0 < h'.toNat := by omega
      have hlt_nat : h'.toNat < Nat.find (exists_pos_step2_cand A D x) := by omega
      have hmin := Nat.find_min (exists_pos_step2_cand A D x) hlt_nat
      have hcast : (h'.toNat : ℤ) = h' := Int.toNat_of_nonneg h0.le
      by_contra hnot
      push Not at hnot
      apply hmin
      refine ⟨hpos, ?_, ?_⟩
      · simpa [hcast] using hnot.1
      · simpa [hcast] using hnot.2

private lemma greedyStep_pos (A D : Finset ℤ) {x : ℤ} (hx : 1 ≤ x) :
    1 ≤ x + greedyStep A D x := by
  rcases greedyStep_spec A D hx with h1 | h2
  · omega
  · omega

private noncomputable def kimState (a₁ d₁ : ℤ) : ℕ → ℤ × ℤ × Finset ℤ × Finset ℤ
  | 0 => (a₁, d₁, {a₁}, {d₁})
  | n + 1 =>
    let st := kimState a₁ d₁ n
    let h := greedyStep st.2.2.1 st.2.2.2 st.1
    (st.1 + h, h, insert (st.1 + h) st.2.2.1, insert h st.2.2.2)

private lemma kimState_sets (a₁ d₁ : ℤ) (n : ℕ) :
    (kimState a₁ d₁ n).2.2.1 = (Finset.Icc 1 (n + 1)).image (fun i => (kimState a₁ d₁ (i - 1)).1) ∧
    (kimState a₁ d₁ n).2.2.2 = (Finset.Icc 1 (n + 1)).image (fun i => (kimState a₁ d₁ (i - 1)).2.1) := by
  induction n with
  | zero =>
    simp [kimState]
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1 + 1) = insert (n + 1 + 1) (Finset.Icc 1 (n + 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hst1 : (kimState a₁ d₁ (n + 1)).2.2.1 =
        insert (kimState a₁ d₁ (n + 1)).1 (kimState a₁ d₁ n).2.2.1 := rfl
    have hst2 : (kimState a₁ d₁ (n + 1)).2.2.2 =
        insert (kimState a₁ d₁ (n + 1)).2.1 (kimState a₁ d₁ n).2.2.2 := rfl
    constructor
    · rw [hst1, ih.1, hIcc, Finset.image_insert]
      rfl
    · rw [hst2, ih.2, hIcc, Finset.image_insert]
      rfl

private lemma kimState_ge_one (a₁ d₁ : ℤ) (ha₁ : 1 ≤ a₁) (n : ℕ) :
    1 ≤ (kimState a₁ d₁ n).1 := by
  induction n with
  | zero => exact ha₁
  | succ n ih =>
    change 1 ≤ (kimState a₁ d₁ n).1 + greedyStep _ _ _
    exact greedyStep_pos _ _ ih

/-- Theorem 1a (Well-Definedness, Positivity, Injectivity & Sign Partition):
For any valid initial pair `(a₁, d₁)` with `1 ≤ a₁`, there exist sequences `a d : ℕ → ℤ` starting at
`a 1 = a₁, d 1 = d₁` and obeying Kimberling's exact greedy Step 1 / Step 2 transition rule at every
step `k ≥ 1`, with `1 ≤ a k`, `a (k + 1) = a k + d (k + 1)`, `a` and `d` injective on `{k | 1 ≤ k}`,
and `s₂(k) + s₁(k) = k - (if d₁ = 0 then 1 else 0)`. -/
theorem ppl143_existence_well_defined (a₁ d₁ : ℤ) (ha₁ : 1 ≤ a₁) :
    ∃ a d : ℕ → ℤ,
      a 1 = a₁ ∧ d 1 = d₁ ∧
      (∀ k : ℕ, 1 ≤ k → 1 ≤ a k ∧ a (k + 1) = a k + d (k + 1)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (1 - a k < d (k + 1) ∧ d (k + 1) < 0 ∧
          d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
          a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
          ∀ h' : ℤ, d (k + 1) < h' → h' < 0 →
            h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a) ∨
        ((∀ h : ℤ, 1 - a k < h → h < 0 →
            h ∈ (Finset.Icc 1 k).image d ∨ a k + h ∈ (Finset.Icc 1 k).image a) ∧
          0 < d (k + 1) ∧
          d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
          a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
          ∀ h' : ℤ, 0 < h' → h' < d (k + 1) →
            h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a)) ∧
      Set.InjOn a {k : ℕ | 1 ≤ k} ∧ Set.InjOn d {k : ℕ | 1 ≤ k} ∧
      (∀ k : ℕ, 1 ≤ k →
        (((Finset.Icc 1 k).image d).filter (0 < ·)).card +
          (((Finset.Icc 1 k).image d).filter (· < 0)).card =
            k - (if d₁ = 0 then 1 else 0)) := by
  let a : ℕ → ℤ := fun k => (kimState a₁ d₁ (k - 1)).1
  let d : ℕ → ℤ := fun k => (kimState a₁ d₁ (k - 1)).2.1
  have ha_ge : ∀ k : ℕ, 1 ≤ k → 1 ≤ a k := fun k _ => kimState_ge_one a₁ d₁ ha₁ (k - 1)
  have hstep_val : ∀ k : ℕ, 1 ≤ k →
      a (k + 1) = a k + d (k + 1) ∧
      d (k + 1) = greedyStep ((Finset.Icc 1 k).image a) ((Finset.Icc 1 k).image d) (a k) := by
    intro k hk
    have hkm : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    have hsets := kimState_sets a₁ d₁ (k - 1)
    rw [← hkm] at hsets
    have hA_eq : (kimState a₁ d₁ (k - 1)).2.2.1 = (Finset.Icc 1 k).image a := hsets.1
    have hD_eq : (kimState a₁ d₁ (k - 1)).2.2.2 = (Finset.Icc 1 k).image d := hsets.2
    have hst : kimState a₁ d₁ k =
        (let st := kimState a₁ d₁ (k - 1)
         let h := greedyStep st.2.2.1 st.2.2.2 st.1
         (st.1 + h, h, insert (st.1 + h) st.2.2.1, insert h st.2.2.2)) := by
      conv_lhs => rw [hkm, kimState]
    have ha1_eq : a (k + 1) = (kimState a₁ d₁ k).1 := rfl
    have hd1_eq : d (k + 1) = (kimState a₁ d₁ k).2.1 := rfl
    rw [ha1_eq, hd1_eq, hst]
    simp only
    rw [hA_eq, hD_eq]
    exact ⟨rfl, rfl⟩
  have hrule : ∀ k : ℕ, 1 ≤ k →
      (1 - a k < d (k + 1) ∧ d (k + 1) < 0 ∧
        d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
        a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
        ∀ h' : ℤ, d (k + 1) < h' → h' < 0 →
          h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a) ∨
      ((∀ h : ℤ, 1 - a k < h → h < 0 →
          h ∈ (Finset.Icc 1 k).image d ∨ a k + h ∈ (Finset.Icc 1 k).image a) ∧
        0 < d (k + 1) ∧
        d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
        a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
        ∀ h' : ℤ, 0 < h' → h' < d (k + 1) →
          h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a) := by
    intro k hk
    rw [(hstep_val k hk).2]
    exact greedyStep_spec _ _ (ha_ge k hk)
  have hinj_a : Set.InjOn a {k : ℕ | 1 ≤ k} := by
    intro i hi j hj heq
    have hi1_le : 1 ≤ i := hi
    have hj1_le : 1 ≤ j := hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have hmem : a i ∈ (Finset.Icc 1 (j - 1)).image a :=
        Finset.mem_image_of_mem a (Finset.mem_Icc.mpr ⟨hi1_le, by omega⟩)
      have hj1 : 1 ≤ j - 1 := by omega
      have hnot : a j ∉ (Finset.Icc 1 (j - 1)).image a := by
        have hr := hrule (j - 1) hj1
        have hsum := (hstep_val (j - 1) hj1).1
        rw [show j - 1 + 1 = j by omega] at hr hsum
        rw [hsum]
        rcases hr with hr1 | hr2
        · exact hr1.2.2.2.1
        · exact hr2.2.2.2.1
      rw [← heq] at hnot
      exact absurd hmem hnot
    · rfl
    · have hmem : a j ∈ (Finset.Icc 1 (i - 1)).image a :=
        Finset.mem_image_of_mem a (Finset.mem_Icc.mpr ⟨hj1_le, by omega⟩)
      have hi1 : 1 ≤ i - 1 := by omega
      have hnot : a i ∉ (Finset.Icc 1 (i - 1)).image a := by
        have hr := hrule (i - 1) hi1
        have hsum := (hstep_val (i - 1) hi1).1
        rw [show i - 1 + 1 = i by omega] at hr hsum
        rw [hsum]
        rcases hr with hr1 | hr2
        · exact hr1.2.2.2.1
        · exact hr2.2.2.2.1
      rw [heq] at hnot
      exact absurd hmem hnot
  have hinj_d : Set.InjOn d {k : ℕ | 1 ≤ k} := by
    intro i hi j hj heq
    have hi1_le : 1 ≤ i := hi
    have hj1_le : 1 ≤ j := hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have hmem : d i ∈ (Finset.Icc 1 (j - 1)).image d :=
        Finset.mem_image_of_mem d (Finset.mem_Icc.mpr ⟨hi1_le, by omega⟩)
      have hj1 : 1 ≤ j - 1 := by omega
      have hnot : d j ∉ (Finset.Icc 1 (j - 1)).image d := by
        have hr := hrule (j - 1) hj1
        rw [show j - 1 + 1 = j by omega] at hr
        rcases hr with hr1 | hr2
        · exact hr1.2.2.1
        · exact hr2.2.2.1
      rw [← heq] at hnot
      exact absurd hmem hnot
    · rfl
    · have hmem : d j ∈ (Finset.Icc 1 (i - 1)).image d :=
        Finset.mem_image_of_mem d (Finset.mem_Icc.mpr ⟨hj1_le, by omega⟩)
      have hi1 : 1 ≤ i - 1 := by omega
      have hnot : d i ∉ (Finset.Icc 1 (i - 1)).image d := by
        have hr := hrule (i - 1) hi1
        rw [show i - 1 + 1 = i by omega] at hr
        rcases hr with hr1 | hr2
        · exact hr1.2.2.1
        · exact hr2.2.2.1
      rw [heq] at hnot
      exact absurd hmem hnot
  refine ⟨a, d, rfl, rfl, fun k hk => ⟨ha_ge k hk, (hstep_val k hk).1⟩, hrule, hinj_a, hinj_d, ?_⟩
  intro k hk
  have hD_card : ((Finset.Icc 1 k).image d).card = k := by
    rw [Finset.card_image_of_injOn (fun x hx y hy hxy =>
      hinj_d (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hy).1 hxy)]
    simp
  have hsplit : (((Finset.Icc 1 k).image d).filter (0 < ·)).card +
      (((Finset.Icc 1 k).image d).filter (· < 0)).card +
      (((Finset.Icc 1 k).image d).filter (· = 0)).card = k := by
    have hdisj1 : Disjoint (((Finset.Icc 1 k).image d).filter (0 < ·))
        (((Finset.Icc 1 k).image d).filter (· < 0)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hdisj2 : Disjoint ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
        (((Finset.Icc 1 k).image d).filter (· < 0)))
        (((Finset.Icc 1 k).image d).filter (· = 0)) := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega,
        Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega⟩
    have hunion : ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
        (((Finset.Icc 1 k).image d).filter (· < 0))) ∪
        (((Finset.Icc 1 k).image d).filter (· = 0)) = (Finset.Icc 1 k).image d := by
      ext z
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨hz, _⟩ | ⟨hz, _⟩) | ⟨hz, _⟩) <;> exact hz
      · intro hz
        rcases lt_trichotomy z 0 with hlt | rfl | hgt
        · exact Or.inl (Or.inr ⟨hz, hlt⟩)
        · exact Or.inr ⟨hz, rfl⟩
        · exact Or.inl (Or.inl ⟨hz, hgt⟩)
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2, hunion,
      hD_card]
  have hzero_card : (((Finset.Icc 1 k).image d).filter (· = 0)).card = if d₁ = 0 then 1 else 0 := by
    have hd_nz : ∀ i : ℕ, 2 ≤ i → d i ≠ 0 := by
      intro i hi
      have hr := hrule (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at hr
      rcases hr with hr1 | hr2 <;> omega
    by_cases hd0 : d₁ = 0
    · rw [if_pos hd0]
      have hset : ((Finset.Icc 1 k).image d).filter (· = 0) = {0} := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨i, ⟨_, _⟩, rfl⟩, hz⟩; exact hz
        · rintro rfl
          exact ⟨⟨1, ⟨le_refl _, hk⟩, hd0⟩, rfl⟩
      rw [hset, Finset.card_singleton]
    · rw [if_neg hd0]
      have hset : ((Finset.Icc 1 k).image d).filter (· = 0) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hz_mem, rfl⟩
        rcases Finset.mem_image.mp hz_mem with ⟨i, hi, hdi⟩
        rcases eq_or_lt_of_le (Finset.mem_Icc.mp hi).1 with rfl | hi2
        · exact hd0 hdi
        · exact hd_nz i hi2 hdi
      rw [hset, Finset.card_empty]
  omega

/-- Theorem 1b (Uniqueness / Determinism):
Any two sequences `(a, d)` and `(a', d')` satisfying `a 1 = a₁`, `d 1 = d₁`, `a (k+1) = a k + d (k+1)`
and the exact greedy Step 1 / Step 2 rule agree identically for all `k ≥ 1`. -/
theorem ppl143_uniqueness {a₁ d₁ : ℤ} (a d a' d' : ℕ → ℤ)
    (ha1 : a 1 = a₁) (hd1 : d 1 = d₁) (ha1' : a' 1 = a₁) (hd1' : d' 1 = d₁)
    (hrec : ∀ k : ℕ, 1 ≤ k → a (k + 1) = a k + d (k + 1))
    (hrec' : ∀ k : ℕ, 1 ≤ k → a' (k + 1) = a' k + d' (k + 1))
    (hrule : ∀ k : ℕ, 1 ≤ k →
      (1 - a k < d (k + 1) ∧ d (k + 1) < 0 ∧
        d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
        a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
        ∀ h' : ℤ, d (k + 1) < h' → h' < 0 →
          h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a) ∨
      ((∀ h : ℤ, 1 - a k < h → h < 0 →
          h ∈ (Finset.Icc 1 k).image d ∨ a k + h ∈ (Finset.Icc 1 k).image a) ∧
        0 < d (k + 1) ∧
        d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
        a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
        ∀ h' : ℤ, 0 < h' → h' < d (k + 1) →
          h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a))
    (hrule' : ∀ k : ℕ, 1 ≤ k →
      (1 - a' k < d' (k + 1) ∧ d' (k + 1) < 0 ∧
        d' (k + 1) ∉ (Finset.Icc 1 k).image d' ∧
        a' k + d' (k + 1) ∉ (Finset.Icc 1 k).image a' ∧
        ∀ h' : ℤ, d' (k + 1) < h' → h' < 0 →
          h' ∈ (Finset.Icc 1 k).image d' ∨ a' k + h' ∈ (Finset.Icc 1 k).image a') ∨
      ((∀ h : ℤ, 1 - a' k < h → h < 0 →
          h ∈ (Finset.Icc 1 k).image d' ∨ a' k + h ∈ (Finset.Icc 1 k).image a') ∧
        0 < d' (k + 1) ∧
        d' (k + 1) ∉ (Finset.Icc 1 k).image d' ∧
        a' k + d' (k + 1) ∉ (Finset.Icc 1 k).image a' ∧
        ∀ h' : ℤ, 0 < h' → h' < d' (k + 1) →
          h' ∈ (Finset.Icc 1 k).image d' ∨ a' k + h' ∈ (Finset.Icc 1 k).image a')) :
    ∀ k : ℕ, 1 ≤ k → a k = a' k ∧ d k = d' k := by
  have hstrong : ∀ k : ℕ, 1 ≤ k → ∀ i ∈ Finset.Icc 1 k, a i = a' i ∧ d i = d' i := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro i hi
      have hi1 : i = 1 := by have := Finset.mem_Icc.mp hi; omega
      subst hi1
      exact ⟨ha1.trans ha1'.symm, hd1.trans hd1'.symm⟩
    | succ k hk ih =>
      have hA_eq : (Finset.Icc 1 k).image a = (Finset.Icc 1 k).image a' :=
        Finset.image_congr fun i hi => (ih i hi).1
      have hD_eq : (Finset.Icc 1 k).image d = (Finset.Icc 1 k).image d' :=
        Finset.image_congr fun i hi => (ih i hi).2
      have hak : a k = a' k := (ih k (Finset.mem_Icc.mpr ⟨hk, le_refl _⟩)).1
      have hd_eq : d (k + 1) = d' (k + 1) := by
        have r1 := hrule k hk
        have r2 := hrule' k hk
        rw [← hA_eq, ← hD_eq, ← hak] at r2
        rcases r1 with hr1 | hr2 <;> rcases r2 with hr1' | hr2'
        · by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rcases hr1.2.2.2.2 (d' (k + 1)) hlt hr1'.2.1 with hD | hA
            · exact False.elim (hr1'.2.2.1 hD)
            · exact False.elim (hr1'.2.2.2.1 hA)
          · rcases hr1'.2.2.2.2 (d (k + 1)) hgt hr1.2.1 with hD | hA
            · exact False.elim (hr1.2.2.1 hD)
            · exact False.elim (hr1.2.2.2.1 hA)
        · exfalso
          rcases hr2'.1 (d (k + 1)) hr1.1 hr1.2.1 with hD | hA
          · exact hr1.2.2.1 hD
          · exact hr1.2.2.2.1 hA
        · exfalso
          rcases hr2.1 (d' (k + 1)) hr1'.1 hr1'.2.1 with hD | hA
          · exact hr1'.2.2.1 hD
          · exact hr1'.2.2.2.1 hA
        · by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rcases hr2'.2.2.2.2 (d (k + 1)) hr2.2.1 hlt with hD | hA
            · exact False.elim (hr2.2.2.1 hD)
            · exact False.elim (hr2.2.2.2.1 hA)
          · rcases hr2.2.2.2.2 (d' (k + 1)) hr2'.2.1 hgt with hD | hA
            · exact False.elim (hr2'.2.2.1 hD)
            · exact False.elim (hr2'.2.2.2.1 hA)
      have ha_eq : a (k + 1) = a' (k + 1) := by
        rw [hrec k hk, hrec' k hk, hak, hd_eq]
      intro i hi
      rcases eq_or_lt_of_le (Finset.mem_Icc.mp hi).2 with rfl | hilt
      · exact ⟨ha_eq, hd_eq⟩
      · exact ih i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, by omega⟩)
  intro k hk
  exact hstrong k hk k (Finset.mem_Icc.mpr ⟨hk, le_refl _⟩)

end GreedyStepConstruction

section ExcessAndPigeonhole

/-- Theorem 2a (Nonnegative Excess of Any Finite Set of Positive Integers):
For any finite set `S : Finset ℤ` with `∀ x ∈ S, 1 ≤ x`, `2 * ∑ x ∈ S, x ≥ |S| * (|S| + 1)`. -/
theorem ppl143_excess_nonneg (S : Finset ℤ) (hpos : ∀ x ∈ S, 1 ≤ x) :
    (S.card : ℤ) * ((S.card : ℤ) + 1) ≤ 2 * ∑ x ∈ S, x := by
  suffices h : ∀ (n : ℕ) (T : Finset ℤ), T.card = n → (∀ x ∈ T, 1 ≤ x) →
      (n : ℤ) * ((n : ℤ) + 1) ≤ 2 * ∑ x ∈ T, x from h S.card S rfl hpos
  intro n
  induction n with
  | zero =>
    intro T hcard _
    rw [Finset.card_eq_zero.mp hcard]
    simp
  | succ n ih =>
    intro T hcard hTpos
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    let m := T.max' hne
    have hm_mem : m ∈ T := Finset.max'_mem T hne
    have hm_pos : 1 ≤ m := hTpos m hm_mem
    have hsub : T ⊆ Finset.Icc 1 m := fun x hx =>
      Finset.mem_Icc.mpr ⟨hTpos x hx, Finset.le_max' T x hx⟩
    have hm_ge : (n + 1 : ℤ) ≤ m := by
      have hcard_le : T.card ≤ (Finset.Icc 1 m).card := Finset.card_le_card hsub
      rw [hcard, Int.card_Icc] at hcard_le
      omega
    let T' := T.erase m
    have hT'_card : T'.card = n := by
      rw [Finset.card_erase_of_mem hm_mem, hcard, Nat.add_sub_cancel]
    have ihT' := ih T' hT'_card fun x hx => hTpos x (Finset.mem_of_mem_erase hx)
    have hsum_split : ∑ x ∈ T, x = m + ∑ x ∈ T', x := by
      rw [← Finset.add_sum_erase T _ hm_mem]
    rw [hsum_split]
    push_cast
    linarith

/-- Theorem 2b (Exact Excess Conservation Identity):
For any `a d : ℕ → ℤ` starting at `a 1 = 1, d 1 = 0` with `a (i+1) = a i + d (i+1)` and `d`
injective on `1 ≤ ·`:
`2 * a(k) = 2 + k * (s₂(k) - s₁(k)) + (2 * ∑_{D^+} x - s₂(s₂+1)) - (2 * ∑_{D^-} y - s₁(s₁+1))`
and `s₁(k) + s₂(k) = k - 1`. -/
theorem ppl143_excess_conservation {a d : ℕ → ℤ}
    (ha1 : a 1 = 1) (hd1 : d 1 = 0)
    (hrec : ∀ i : ℕ, 1 ≤ i → a (i + 1) = a i + d (i + 1))
    (hinj_d : Set.InjOn d {i : ℕ | 1 ≤ i})
    {k : ℕ} (hk : 1 ≤ k) :
    let Dpos := ((Finset.Icc 1 k).image d).filter (0 < ·)
    let Dneg := (((Finset.Icc 1 k).image d).filter (· < 0)).image Neg.neg
    let s₂ : ℕ := Dpos.card
    let s₁ : ℕ := Dneg.card
    s₁ + s₂ = k - 1 ∧
    2 * a k = 2 + (k : ℤ) * ((s₂ : ℤ) - (s₁ : ℤ)) +
      (2 * ∑ x ∈ Dpos, x - (s₂ : ℤ) * ((s₂ : ℤ) + 1)) -
      (2 * ∑ y ∈ Dneg, y - (s₁ : ℤ) * ((s₁ : ℤ) + 1)) := by
  intro Dpos Dneg s₂ s₁
  have hD_card : ((Finset.Icc 1 k).image d).card = k := by
    rw [Finset.card_image_of_injOn (fun x hx y hy hxy =>
      hinj_d (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hy).1 hxy)]
    simp
  have hDneg_card : s₁ = (((Finset.Icc 1 k).image d).filter (· < 0)).card :=
    Finset.card_image_of_injective _ neg_injective
  have hs12 : s₁ + s₂ = k - 1 := by
    have hdisj1 : Disjoint (((Finset.Icc 1 k).image d).filter (0 < ·))
        (((Finset.Icc 1 k).image d).filter (· < 0)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hdisj2 : Disjoint ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
        (((Finset.Icc 1 k).image d).filter (· < 0))) ({0} : Finset ℤ) := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_singleton_right.mpr (fun h => by
          have := (Finset.mem_filter.mp h).2; omega),
        Finset.disjoint_singleton_right.mpr (fun h => by
          have := (Finset.mem_filter.mp h).2; omega)⟩
    have hunion : ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
        (((Finset.Icc 1 k).image d).filter (· < 0))) ∪ ({0} : Finset ℤ) =
        (Finset.Icc 1 k).image d := by
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ((⟨hz, _⟩ | ⟨hz, _⟩) | rfl)
        · exact hz
        · exact hz
        · exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hk⟩, hd1⟩
      · intro hz
        rcases lt_trichotomy z 0 with hlt | rfl | hgt
        · exact Or.inl (Or.inr ⟨hz, hlt⟩)
        · exact Or.inr rfl
        · exact Or.inl (Or.inl ⟨hz, hgt⟩)
    have hcard_u : s₂ + s₁ + 1 = k := by
      rw [hDneg_card]
      calc (((Finset.Icc 1 k).image d).filter (0 < ·)).card +
            (((Finset.Icc 1 k).image d).filter (· < 0)).card + 1
          = ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
              (((Finset.Icc 1 k).image d).filter (· < 0))).card + ({0} : Finset ℤ).card := by
            rw [Finset.card_union_of_disjoint hdisj1, Finset.card_singleton]
        _ = (((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
              (((Finset.Icc 1 k).image d).filter (· < 0))) ∪ ({0} : Finset ℤ)).card := by
            rw [Finset.card_union_of_disjoint hdisj2]
        _ = k := by rw [hunion, hD_card]
    omega
  refine ⟨hs12, ?_⟩
  have htele : a k = 1 + ∑ i ∈ Finset.Icc 1 k, d i := by
    clear Dpos Dneg s₂ s₁ hD_card hDneg_card hs12
    induction k, hk using Nat.le_induction with
    | base => simp [ha1, hd1]
    | succ k hk ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
      rw [hrec k hk, ih, hIcc, Finset.sum_insert hnot]
      ring
  have hsum_img : ∑ i ∈ Finset.Icc 1 k, d i = ∑ z ∈ (Finset.Icc 1 k).image d, z := by
    symm
    exact Finset.sum_image (fun x hx y hy hxy =>
      hinj_d (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hy).1 hxy)
  have hsum_split : ∑ z ∈ (Finset.Icc 1 k).image d, z =
      ∑ x ∈ Dpos, x - ∑ y ∈ Dneg, y := by
    have hDneg_sum : ∑ y ∈ Dneg, y =
        - ∑ z ∈ ((Finset.Icc 1 k).image d).filter (· < 0), z := by
      dsimp [Dneg]
      rw [Finset.sum_image (fun x _ y _ h => neg_inj.mp h), Finset.sum_neg_distrib]
    have hdisj1 : Disjoint (((Finset.Icc 1 k).image d).filter (0 < ·))
        (((Finset.Icc 1 k).image d).filter (· < 0)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hdisj2 : Disjoint ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
        (((Finset.Icc 1 k).image d).filter (· < 0))) ({0} : Finset ℤ) := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_singleton_right.mpr (fun h => by
          have := (Finset.mem_filter.mp h).2; omega),
        Finset.disjoint_singleton_right.mpr (fun h => by
          have := (Finset.mem_filter.mp h).2; omega)⟩
    have hunion : ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
        (((Finset.Icc 1 k).image d).filter (· < 0))) ∪ ({0} : Finset ℤ) =
        (Finset.Icc 1 k).image d := by
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ((⟨hz, _⟩ | ⟨hz, _⟩) | rfl)
        · exact hz
        · exact hz
        · exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hk⟩, hd1⟩
      · intro hz
        rcases lt_trichotomy z 0 with hlt | rfl | hgt
        · exact Or.inl (Or.inr ⟨hz, hlt⟩)
        · exact Or.inr rfl
        · exact Or.inl (Or.inl ⟨hz, hgt⟩)
    rw [hDneg_sum, sub_neg_eq_add, ← Finset.sum_union hdisj1]
    calc ∑ z ∈ (Finset.Icc 1 k).image d, z
        = ∑ z ∈ (((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
            (((Finset.Icc 1 k).image d).filter (· < 0))) ∪ ({0} : Finset ℤ)), z := by
          rw [hunion]
      _ = ∑ z ∈ ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
            (((Finset.Icc 1 k).image d).filter (· < 0))), z + ∑ z ∈ ({0} : Finset ℤ), z :=
          Finset.sum_union hdisj2
      _ = ∑ z ∈ ((((Finset.Icc 1 k).image d).filter (0 < ·)) ∪
            (((Finset.Icc 1 k).image d).filter (· < 0))), z := by simp
  have hcard_id : (k : ℤ) * ((s₂ : ℤ) - (s₁ : ℤ)) =
      (s₂ : ℤ) * ((s₂ : ℤ) + 1) - (s₁ : ℤ) * ((s₁ : ℤ) + 1) := by
    have hk_eq : (k : ℤ) = (s₂ : ℤ) + (s₁ : ℤ) + 1 := by omega
    rw [hk_eq]
    ring
  rw [htele, hsum_img, hsum_split, hcard_id]
  ring

/-- Theorem 3 (Step-2 Pigeonhole Upper Bound):
Whenever Step 1 fails at step `n ≥ 1` (e.g., whenever Step 2 fires with `d (n+1) > 0`),
`a(n) ≤ n + s₁(n)`, and when `0 ≤ d 1`, `n + s₁(n) ≤ 2 * n - 1`. -/
theorem ppl143_step2_pigeonhole_bound {a d : ℕ → ℤ}
    (ha1 : a 1 = 1) (hd1 : 0 ≤ d 1)
    (ha_pos : ∀ i : ℕ, 1 ≤ i → 1 ≤ a i)
    (hinj_a : Set.InjOn a {i : ℕ | 1 ≤ i})
    {n : ℕ} (hn : 1 ≤ n)
    (hstep1_fail : ∀ h : ℤ, 1 - a n < h → h < 0 →
      h ∈ (Finset.Icc 1 n).image d ∨ a n + h ∈ (Finset.Icc 1 n).image a) :
    let s₁ := (((Finset.Icc 1 n).image d).filter (· < 0)).card
    a n ≤ (n : ℤ) + (s₁ : ℤ) ∧ (n : ℤ) + (s₁ : ℤ) ≤ 2 * (n : ℤ) - 1 := by
  intro s₁
  have hs1_le : s₁ ≤ n - 1 := by
    have hsub : ((Finset.Icc 1 n).image d).filter (· < 0) ⊆
        (Finset.Icc 2 n).image d := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hz_mem, hz_neg⟩
      rcases Finset.mem_image.mp hz_mem with ⟨i, hi, rfl⟩
      rcases eq_or_lt_of_le (Finset.mem_Icc.mp hi).1 with rfl | hi2
      · omega
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨hi2, (Finset.mem_Icc.mp hi).2⟩, rfl⟩
    have hle1 : s₁ ≤ ((Finset.Icc 2 n).image d).card := Finset.card_le_card hsub
    have hle2 : ((Finset.Icc 2 n).image d).card ≤ (Finset.Icc 2 n).card := Finset.card_image_le
    have hcard_Icc : (Finset.Icc 2 n).card = n - 1 := by simp [Nat.card_Icc]
    omega
  refine ⟨?_, by omega⟩
  rcases eq_or_lt_of_le hn with rfl | hn2
  · rw [ha1]; omega
  · have han_ge2 : 2 ≤ a n := by
      have hpos := ha_pos n hn
      have hne : a n ≠ 1 := by
        intro h1
        have := hinj_a hn (le_refl 1) (h1.trans ha1.symm)
        omega
      omega
    let V : Finset ℤ := Finset.Icc 1 (a n - 2)
    let S₁ : Finset ℤ := (((Finset.Icc 1 n).image d).filter (· < 0)).image Neg.neg
    let S₂ : Finset ℤ :=
      (((Finset.Icc 1 n).image a).erase (a 1) |>.erase (a n)).image (fun z => a n - z)
    have hV_sub : V ⊆ S₁ ∪ S₂ := by
      intro v hv
      have hv_Icc := Finset.mem_Icc.mp hv
      have h1 : 1 - a n < -v := by omega
      have h2 : -v < 0 := by omega
      rcases hstep1_fail (-v) h1 h2 with hD | hA
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨-v, ?_, by ring⟩)
        exact Finset.mem_filter.mpr ⟨hD, h2⟩
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a n + (-v), ?_, by ring⟩)
        have hne1 : a n + (-v) ≠ a 1 := by rw [ha1]; omega
        have hnen : a n + (-v) ≠ a n := by omega
        exact Finset.mem_erase.mpr ⟨hnen, Finset.mem_erase.mpr ⟨hne1, hA⟩⟩
    have hS1_card : S₁.card = s₁ := Finset.card_image_of_injective _ neg_injective
    have hS2_card : S₂.card ≤ n - 2 := by
      have hle1 : S₂.card ≤ (((Finset.Icc 1 n).image a).erase (a 1) |>.erase (a n)).card :=
        Finset.card_image_le
      have hA_card : ((Finset.Icc 1 n).image a).card = n := by
        rw [Finset.card_image_of_injOn (fun x hx y hy hxy =>
          hinj_a (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hy).1 hxy)]
        simp
      have ha1_mem : a 1 ∈ (Finset.Icc 1 n).image a :=
        Finset.mem_image_of_mem a (Finset.mem_Icc.mpr ⟨le_refl _, hn⟩)
      have han_mem : a n ∈ ((Finset.Icc 1 n).image a).erase (a 1) := by
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image_of_mem a (Finset.mem_Icc.mpr ⟨hn, le_refl _⟩)⟩
        intro heq
        have := hinj_a hn (le_refl 1) heq
        omega
      have hc1 : (((Finset.Icc 1 n).image a).erase (a 1)).card = n - 1 := by
        rw [Finset.card_erase_of_mem ha1_mem, hA_card]
      have hc2 : ((((Finset.Icc 1 n).image a).erase (a 1)).erase (a n)).card = n - 2 := by
        rw [Finset.card_erase_of_mem han_mem, hc1]
        omega
      omega
    have hV_card : V.card ≤ s₁ + (n - 2) := by
      calc V.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hV_sub
        _ ≤ S₁.card + S₂.card := Finset.card_union_le _ _
        _ ≤ s₁ + (n - 2) := by omega
    have hV_eq : (V.card : ℤ) = a n - 2 := by
      dsimp [V]
      rw [Int.card_Icc]
      omega
    have hleZ : (V.card : ℤ) ≤ (s₁ : ℤ) + ((n - 2 : ℕ) : ℤ) := by exact_mod_cast hV_card
    have hn2Z : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    omega

end ExcessAndPigeonhole

section RunConditionsAndInfinitude

/-- Theorem 4a (Exact Necessary Condition for a Negative `r`-Run):
If `d(k+1), ..., d(k+r) < 0` (`1 ≤ k, 1 ≤ r`) with `d` injective on `1 ≤ ·`, `a` injective on `1 ≤ ·`,
and `1 ≤ a(k+r)`, then for any hole thresholds `1 ≤ m_A` (all integers in `[1, m_A)` appear in `A(k)`)
and `1 ≤ M_neg` (all negatives of integers in `[1, M_neg)` appear in `D(k)`):
`2 * m_A + 2 * r * M_neg + r * (r - 1) ≤ 2 * a k` (and `m_A + r * M_neg + (r * (r - 1)) / 2 ≤ a k`). -/
theorem ppl143_neg_run_lower_bound {a d : ℕ → ℤ}
    (hrec : ∀ i : ℕ, 1 ≤ i → a (i + 1) = a i + d (i + 1))
    (hinj_a : Set.InjOn a {i : ℕ | 1 ≤ i})
    (hinj_d : Set.InjOn d {i : ℕ | 1 ≤ i})
    {k r : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r)
    (ha_kr : 1 ≤ a (k + r))
    (hneg : ∀ j ∈ Finset.Icc 1 r, d (k + j) < 0)
    {m_A M_neg : ℤ} (_hmA_pos : 1 ≤ m_A) (_hM_pos : 1 ≤ M_neg)
    (hmA : ∀ z : ℤ, 1 ≤ z → z < m_A → z ∈ (Finset.Icc 1 k).image a)
    (hMneg : ∀ z : ℤ, 1 ≤ z → z < M_neg → -z ∈ (Finset.Icc 1 k).image d) :
    2 * m_A + 2 * (r : ℤ) * M_neg + (r : ℤ) * ((r : ℤ) - 1) ≤ 2 * a k ∧
    m_A + (r : ℤ) * M_neg + ((r : ℤ) * ((r : ℤ) - 1)) / 2 ≤ a k := by
  have hmA_le : m_A ≤ a (k + r) := by
    by_contra hlt
    push Not at hlt
    have hmem := hmA (a (k + r)) ha_kr hlt
    rcases Finset.mem_image.mp hmem with ⟨i, hi, heq⟩
    have hi_mem := Finset.mem_Icc.mp hi
    have hi_le : i ≤ k := hi_mem.2
    have hi_eq : i = k + r := hinj_a hi_mem.1 (by omega : 1 ≤ k + r) heq
    omega
  let T : Finset ℤ := (Finset.Icc 1 r).image (fun j => -d (k + j) - (M_neg - 1))
  have hT_card : T.card = r := by
    dsimp [T]
    rw [Finset.card_image_of_injOn (fun x _ y _ hxy => by
      have hd_eq : d (k + x) = d (k + y) := by omega
      have := hinj_d (by omega : 1 ≤ k + x) (by omega : 1 ≤ k + y) hd_eq
      omega)]
    simp
  have hT_pos : ∀ z ∈ T, 1 ≤ z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    have hj_neg : d (k + j) < 0 := hneg j hj
    have hge_M : M_neg ≤ -d (k + j) := by
      by_contra hlt
      push Not at hlt
      have hmem := hMneg (-d (k + j)) (by omega) hlt
      rcases Finset.mem_image.mp hmem with ⟨i, hi, heq⟩
      have hd_eq : d i = d (k + j) := by omega
      have hi_eq := hinj_d (Finset.mem_Icc.mp hi).1 (by omega : 1 ≤ k + j) hd_eq
      have := (Finset.mem_Icc.mp hi).2
      have := (Finset.mem_Icc.mp hj).1
      omega
    omega
  have hT_sum := ppl143_excess_nonneg T hT_pos
  rw [hT_card] at hT_sum
  have hT_sum_eq : ∑ z ∈ T, z = (∑ j ∈ Finset.Icc 1 r, (-d (k + j))) - (r : ℤ) * (M_neg - 1) := by
    dsimp [T]
    rw [Finset.sum_image (fun x _ y _ hxy => by
      have hd_eq : d (k + x) = d (k + y) := by omega
      have := hinj_d (by omega : 1 ≤ k + x) (by omega : 1 ≤ k + y) hd_eq
      omega)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
    simp
  have htele : a (k + r) = a k + ∑ j ∈ Finset.Icc 1 r, d (k + j) := by
    clear T hT_card hT_pos hT_sum hT_sum_eq hmA_le hneg ha_kr
    induction r, hr using Nat.le_induction with
    | base => simp [hrec k hk]
    | succ r hr ih =>
      have hIcc : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : r + 1 ∉ Finset.Icc 1 r := by simp
      rw [← add_assoc, hrec (k + r) (by omega), ih, hIcc, Finset.sum_insert hnot]
      ring
  have hsum_neg : ∑ j ∈ Finset.Icc 1 r, (-d (k + j)) = a k - a (k + r) := by
    rw [Finset.sum_neg_distrib, htele]
    ring
  rw [hT_sum_eq, hsum_neg] at hT_sum
  have hdouble : 2 * m_A + 2 * (r : ℤ) * M_neg + (r : ℤ) * ((r : ℤ) - 1) ≤ 2 * a k := by
    linarith
  refine ⟨hdouble, ?_⟩
  have heven : ∃ q : ℤ, (r : ℤ) * ((r : ℤ) - 1) = 2 * q := by
    rcases Int.even_or_odd (r : ℤ) with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * ((r : ℤ) - 1), by rw [ht]; ring⟩
    · refine ⟨(r : ℤ) * t, ?_⟩
      have h1 : (r : ℤ) - 1 = 2 * t := by omega
      rw [h1]; ring
  rcases heven with ⟨q, hq⟩
  rw [hq, Int.mul_ediv_cancel_left _ (by norm_num)]
  linarith

/-- Theorem 4b (Exact Positive `r`-Run Sandwich, `r ≥ 2`):
If `d(k+1), ..., d(k+r) > 0` (`1 ≤ k`, `2 ≤ r`) and Step 1 fails at step `k + r - 1`, then:
`m_A(k-1) + (r-1) * M_pos(k) + (r-1)(r-2)/2 ≤ a(k+r-1) ≤ k + r - 1 + s₁(k)`. -/
theorem ppl143_pos_run_sandwich {a d : ℕ → ℤ}
    (ha1 : a 1 = 1) (hd1 : 0 ≤ d 1)
    (hrec : ∀ i : ℕ, 1 ≤ i → 1 ≤ a i ∧ a (i + 1) = a i + d (i + 1))
    (hinj_a : Set.InjOn a {i : ℕ | 1 ≤ i})
    (hinj_d : Set.InjOn d {i : ℕ | 1 ≤ i})
    {k r : ℕ} (hk : 1 ≤ k) (hr : 2 ≤ r)
    (hpos : ∀ j ∈ Finset.Icc 1 r, 0 < d (k + j))
    (hstep1_fail : ∀ h : ℤ, 1 - a (k + r - 1) < h → h < 0 →
      h ∈ (Finset.Icc 1 (k + r - 1)).image d ∨
      a (k + r - 1) + h ∈ (Finset.Icc 1 (k + r - 1)).image a)
    {m_A_prev M_pos : ℤ} (_hmA_pos : 1 ≤ m_A_prev) (_hM_pos : 1 ≤ M_pos)
    (hmA_prev : (k = 1 → m_A_prev ≤ 1) ∧
      (2 ≤ k → ∀ z : ℤ, 1 ≤ z → z < m_A_prev → z ∈ (Finset.Icc 1 (k - 1)).image a))
    (hMpos : ∀ z : ℤ, 1 ≤ z → z < M_pos → z ∈ (Finset.Icc 1 k).image d) :
    let s₁ := (((Finset.Icc 1 k).image d).filter (· < 0)).card
    (2 * m_A_prev + 2 * ((r : ℤ) - 1) * M_pos + ((r : ℤ) - 1) * ((r : ℤ) - 2) ≤
        2 * a (k + r - 1)) ∧
    m_A_prev + ((r : ℤ) - 1) * M_pos + (((r : ℤ) - 1) * ((r : ℤ) - 2)) / 2 ≤ a (k + r - 1) ∧
    a (k + r - 1) ≤ (k : ℤ) + (r : ℤ) - 1 + (s₁ : ℤ) := by
  intro s₁
  have hmA_le_ak : m_A_prev ≤ a k := by
    rcases eq_or_lt_of_le hk with rfl | hk2
    · rw [ha1]; exact hmA_prev.1 rfl
    · by_contra hlt
      push Not at hlt
      have hak_pos : 1 ≤ a k := (hrec k hk).1
      have hmem := hmA_prev.2 hk2 (a k) hak_pos hlt
      rcases Finset.mem_image.mp hmem with ⟨i, hi, heq⟩
      have := hinj_a (Finset.mem_Icc.mp hi).1 hk heq
      have := (Finset.mem_Icc.mp hi).2
      omega
  let T : Finset ℤ := (Finset.Icc 1 (r - 1)).image (fun j => d (k + j) - (M_pos - 1))
  have hT_card : T.card = r - 1 := by
    dsimp [T]
    rw [Finset.card_image_of_injOn (fun x _ y _ hxy => by
      have hd_eq : d (k + x) = d (k + y) := by omega
      have := hinj_d (by omega : 1 ≤ k + x) (by omega : 1 ≤ k + y) hd_eq
      omega)]
    simp
  have hT_pos : ∀ z ∈ T, 1 ≤ z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    have hj_pos : 0 < d (k + j) := hpos j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, by
      have := (Finset.mem_Icc.mp hj).2; omega⟩)
    have hge_M : M_pos ≤ d (k + j) := by
      by_contra hlt
      push Not at hlt
      have hmem := hMpos (d (k + j)) hj_pos hlt
      rcases Finset.mem_image.mp hmem with ⟨i, hi, heq⟩
      have hi_eq := hinj_d (Finset.mem_Icc.mp hi).1 (by omega : 1 ≤ k + j) heq
      have := (Finset.mem_Icc.mp hi).2
      have := (Finset.mem_Icc.mp hj).1
      omega
    omega
  have hT_sum := ppl143_excess_nonneg T hT_pos
  rw [hT_card] at hT_sum
  have hT_sum_eq : ∑ z ∈ T, z = (∑ j ∈ Finset.Icc 1 (r - 1), d (k + j)) -
      ((r - 1 : ℕ) : ℤ) * (M_pos - 1) := by
    dsimp [T]
    rw [Finset.sum_image (fun x _ y _ hxy => by
      have hd_eq : d (k + x) = d (k + y) := by omega
      have := hinj_d (by omega : 1 ≤ k + x) (by omega : 1 ≤ k + y) hd_eq
      omega)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
    simp
  have htele : a (k + (r - 1)) = a k + ∑ j ∈ Finset.Icc 1 (r - 1), d (k + j) := by
    have htele_aux : ∀ m : ℕ, 1 ≤ m → a (k + m) = a k + ∑ j ∈ Finset.Icc 1 m, d (k + j) := by
      intro m hm1
      induction m, hm1 using Nat.le_induction with
      | base => simp [(hrec k hk).2]
      | succ m hm ih =>
        have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
        rw [← add_assoc, (hrec (k + m) (by omega)).2, ih, hIcc, Finset.sum_insert hnot]
        ring
    exact htele_aux (r - 1) (by omega)
  have hkr_eq : k + (r - 1) = k + r - 1 := by omega
  rw [hkr_eq] at htele
  have hsum_pos : ∑ j ∈ Finset.Icc 1 (r - 1), d (k + j) = a (k + r - 1) - a k := by
    rw [htele]; ring
  rw [hT_sum_eq, hsum_pos] at hT_sum
  have hr1_cast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  rw [hr1_cast] at hT_sum
  have hdouble : 2 * m_A_prev + 2 * ((r : ℤ) - 1) * M_pos + ((r : ℤ) - 1) * ((r : ℤ) - 2) ≤
      2 * a (k + r - 1) := by linarith
  have heven : ∃ q : ℤ, ((r : ℤ) - 1) * ((r : ℤ) - 2) = 2 * q := by
    rcases Int.even_or_odd ((r : ℤ) - 1) with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * ((r : ℤ) - 2), by rw [ht]; ring⟩
    · refine ⟨((r : ℤ) - 1) * t, ?_⟩
      have h1 : (r : ℤ) - 2 = 2 * t := by omega
      rw [h1]; ring
  have hlower : m_A_prev + ((r : ℤ) - 1) * M_pos + (((r : ℤ) - 1) * ((r : ℤ) - 2)) / 2 ≤
      a (k + r - 1) := by
    rcases heven with ⟨q, hq⟩
    rw [hq, Int.mul_ediv_cancel_left _ (by norm_num)]
    linarith
  have hpig := ppl143_step2_pigeonhole_bound ha1 hd1 (fun i hi => (hrec i hi).1) hinj_a
    (by omega : 1 ≤ k + r - 1) hstep1_fail
  have hs1_eq : (((Finset.Icc 1 (k + r - 1)).image d).filter (· < 0)).card = s₁ := by
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨i, ⟨hi1, hi2⟩, rfl⟩, hz⟩
      by_cases hik : i ≤ k
      · exact ⟨⟨i, ⟨hi1, hik⟩, rfl⟩, hz⟩
      · have hj_mem : i - k ∈ Finset.Icc 1 r := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hpos_i := hpos (i - k) hj_mem
        rw [show k + (i - k) = i by omega] at hpos_i
        omega
    · rintro ⟨⟨i, ⟨hi1, hi2⟩, rfl⟩, hz⟩
      exact ⟨⟨i, ⟨hi1, by omega⟩, rfl⟩, hz⟩
  have hupper : a (k + r - 1) ≤ (k : ℤ) + (r : ℤ) - 1 + (s₁ : ℤ) := by
    have hle := hpig.1
    rw [hs1_eq] at hle
    have hcast : ((k + r - 1 : ℕ) : ℤ) = (k : ℤ) + (r : ℤ) - 1 := by omega
    rw [hcast] at hle
    exact hle
  exact ⟨hdouble, hlower, hupper⟩

/-- Theorem 4c (Unconditional Infinitude of Both Positive and Negative Signs):
For the exact greedy sequence `(a, d)` starting at `a 1 = 1, d 1 = 0`, both `d(n) > 0` and
`d(n) < 0` occur infinitely often (`∀ N, (∃ n ≥ N, 0 < d n) ∧ (∃ n ≥ N, d n < 0)`). -/
theorem ppl143_infinitely_many_pos_neg {a d : ℕ → ℤ}
    (ha1 : a 1 = 1) (hd1 : d 1 = 0)
    (hrec : ∀ k : ℕ, 1 ≤ k → 1 ≤ a k ∧ a (k + 1) = a k + d (k + 1))
    (hinj_a : Set.InjOn a {k : ℕ | 1 ≤ k})
    (hinj_d : Set.InjOn d {k : ℕ | 1 ≤ k})
    (hrule : ∀ k : ℕ, 1 ≤ k →
      (1 - a k < d (k + 1) ∧ d (k + 1) < 0 ∧
        d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
        a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
        ∀ h' : ℤ, d (k + 1) < h' → h' < 0 →
          h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a) ∨
      ((∀ h : ℤ, 1 - a k < h → h < 0 →
          h ∈ (Finset.Icc 1 k).image d ∨ a k + h ∈ (Finset.Icc 1 k).image a) ∧
        0 < d (k + 1) ∧
        d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
        a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
        ∀ h' : ℤ, 0 < h' → h' < d (k + 1) →
          h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a)) :
    ∀ N : ℕ, (∃ n ≥ N, 0 < d n) ∧ (∃ n ≥ N, d n < 0) := by
  have hd_nz : ∀ i : ℕ, 2 ≤ i → d i ≠ 0 := by
    intro i hi
    rcases hrule (i - 1) (by omega) with hr1 | hr2
    · rw [show i - 1 + 1 = i by omega] at hr1; omega
    · rw [show i - 1 + 1 = i by omega] at hr2; omega
  intro N
  let k : ℕ := max N 1
  have hk : 1 ≤ k := le_max_right _ _
  constructor
  · by_contra hno
    push Not at hno
    let r : ℕ := 2 * (a k).toNat + 2
    have hr : 1 ≤ r := by omega
    have hneg : ∀ j ∈ Finset.Icc 1 r, d (k + j) < 0 := fun j hj => by
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hle : d (k + j) ≤ 0 := hno (k + j) (by omega)
      have hne : d (k + j) ≠ 0 := hd_nz (k + j) (by omega)
      omega
    have hlb := ppl143_neg_run_lower_bound (fun i hi => (hrec i hi).2) hinj_a hinj_d hk hr
      (hrec (k + r) (by omega)).1 hneg (m_A := 1) (M_neg := 1) (le_refl 1) (le_refl 1)
      (fun _ h1 h2 => by omega) (fun _ h1 h2 => by omega)
    have h1 := hlb.1
    have hak_pos : 1 ≤ a k := (hrec k hk).1
    have hle_ak : 2 * (a k).toNat + 2 = r := rfl
    have hr_ge : (r : ℤ) ≥ 2 * a k + 2 := by omega
    have hr_sq : (r : ℤ) * ((r : ℤ) - 1) ≥ 0 := mul_nonneg (by omega) (by omega)
    linarith
  · by_contra hno
    push Not at hno
    let r : ℕ := 2 * k + 5
    have hr : 2 ≤ r := by omega
    have hpos : ∀ j ∈ Finset.Icc 1 r, 0 < d (k + j) := fun j hj => by
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hge : 0 ≤ d (k + j) := hno (k + j) (by omega)
      have hne : d (k + j) ≠ 0 := hd_nz (k + j) (by omega)
      omega
    have hstep1_fail : ∀ h : ℤ, 1 - a (k + r - 1) < h → h < 0 →
        h ∈ (Finset.Icc 1 (k + r - 1)).image d ∨
        a (k + r - 1) + h ∈ (Finset.Icc 1 (k + r - 1)).image a := by
      have hpos_last : 0 < d (k + r) := hpos r (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩)
      have hr_rule := hrule (k + r - 1) (by omega)
      rw [show k + r - 1 + 1 = k + r by omega] at hr_rule
      rcases hr_rule with hr1 | hr2
      · omega
      · exact hr2.1
    have hsand := ppl143_pos_run_sandwich ha1 (by omega : 0 ≤ d 1) hrec hinj_a hinj_d hk hr
      hpos hstep1_fail (m_A_prev := 1) (M_pos := 1) (le_refl 1) (le_refl 1)
      ⟨fun _ => le_refl 1, fun _ _ h1 h2 => by omega⟩ (fun _ h1 h2 => by omega)
    have hlow := hsand.1
    have hupp := hsand.2.2
    have hs1_le : (((Finset.Icc 1 k).image d).filter (· < 0)).card ≤ k := by
      have h1 : (((Finset.Icc 1 k).image d).filter (· < 0)).card ≤ ((Finset.Icc 1 k).image d).card :=
        Finset.card_filter_le _ _
      have h2 : ((Finset.Icc 1 k).image d).card ≤ (Finset.Icc 1 k).card := Finset.card_image_le
      simp only [Nat.card_Icc, Nat.add_sub_cancel] at h2
      omega
    have hrZ : (r : ℤ) = 2 * (k : ℤ) + 5 := by omega
    have hquad : 2 * (1 : ℤ) + 2 * ((r : ℤ) - 1) * 1 + ((r : ℤ) - 1) * ((r : ℤ) - 2) ≤
        2 * ((k : ℤ) + (r : ℤ) - 1 + (k : ℤ)) := by linarith
    rw [hrZ] at hquad
    nlinarith

end RunConditionsAndInfinitude

section PerturbationBarrierWitnesses

/-- Perturbation Barrier Witness 1 (`NEG3` under Kimberling's exact Step 1 / Step 2 rule):
Starting from `(a₁, d₁) = (8, 0)`, Kimberling's exact greedy recurrence produces `d(2) = -1, d(3) = -2,
d(4) = -3` (`a = (8, 7, 5, 2)`), showing no invariant of the local greedy step alone forbids `NEG3`. -/
theorem ppl143_perturbed_neg3_barrier :
    ∃ a d : ℕ → ℤ,
      a 1 = 8 ∧ d 1 = 0 ∧
      (∀ k : ℕ, 1 ≤ k → 1 ≤ a k ∧ a (k + 1) = a k + d (k + 1)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (1 - a k < d (k + 1) ∧ d (k + 1) < 0 ∧
          d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
          a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
          ∀ h' : ℤ, d (k + 1) < h' → h' < 0 →
            h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a) ∨
        ((∀ h : ℤ, 1 - a k < h → h < 0 →
            h ∈ (Finset.Icc 1 k).image d ∨ a k + h ∈ (Finset.Icc 1 k).image a) ∧
          0 < d (k + 1) ∧
          d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
          a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
          ∀ h' : ℤ, 0 < h' → h' < d (k + 1) →
            h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a)) ∧
      d 2 < 0 ∧ d 3 < 0 ∧ d 4 < 0 ∧ d 2 = -1 ∧ d 3 = -2 ∧ d 4 = -3 ∧
      a 2 = 7 ∧ a 3 = 5 ∧ a 4 = 2 := by
  obtain ⟨a, d, ha1, hd1, hrec, hrule, _⟩ := ppl143_existence_well_defined 8 0 (by omega)
  have hd2 : d 2 = -1 := by
    have hr := hrule 1 (le_refl 1)
    rw [show (1 : ℕ) + 1 = 2 from rfl] at hr
    rcases hr with hr1 | hr2
    · have hlt0 : d 2 < 0 := hr1.2.1
      by_contra hne
      have hlt1 : d 2 < -1 := by omega
      rcases hr1.2.2.2.2 (-1) hlt1 (by omega) with hD | hA
      · rcases Finset.mem_image.mp hD with ⟨i, hi, hid⟩
        have : i = 1 := by have := Finset.mem_Icc.mp hi; omega
        subst this; omega
      · rcases Finset.mem_image.mp hA with ⟨i, hi, hia⟩
        have : i = 1 := by have := Finset.mem_Icc.mp hi; omega
        subst this; omega
    · exfalso
      rcases hr2.1 (-1) (by omega) (by omega) with hD | hA
      · rcases Finset.mem_image.mp hD with ⟨i, hi, hid⟩
        have : i = 1 := by have := Finset.mem_Icc.mp hi; omega
        subst this; omega
      · rcases Finset.mem_image.mp hA with ⟨i, hi, hia⟩
        have : i = 1 := by have := Finset.mem_Icc.mp hi; omega
        subst this; omega
  have ha2 : a 2 = 7 := by
    have hr := (hrec 1 (le_refl 1)).2
    rw [show (1 : ℕ) + 1 = 2 from rfl] at hr; omega
  have hd3 : d 3 = -2 := by
    have hok : (-2 : ℤ) ∉ (Finset.Icc 1 2).image d ∧ a 2 + (-2) ∉ (Finset.Icc 1 2).image a := by
      constructor <;> intro hmem <;> rcases Finset.mem_image.mp hmem with ⟨i, hi, hieq⟩ <;>
        rcases (by have := Finset.mem_Icc.mp hi; omega : i = 1 ∨ i = 2) with rfl | rfl <;> omega
    have hr := hrule 2 (by omega)
    rw [show (2 : ℕ) + 1 = 3 from rfl] at hr
    rcases hr with hr1 | hr2
    · have hlt : d 3 < 0 := hr1.2.1
      have hne1 : d 3 ≠ -1 := by
        intro h
        apply hr1.2.2.1
        exact Finset.mem_image.mpr ⟨2, Finset.mem_Icc.mpr ⟨by omega, le_refl 2⟩, by omega⟩
      by_contra hne2
      have hlt2 : d 3 < -2 := by omega
      rcases hr1.2.2.2.2 (-2) hlt2 (by omega) with hD | hA
      · exact hok.1 hD
      · exact hok.2 hA
    · exfalso
      rcases hr2.1 (-2) (by omega) (by omega) with hD | hA
      · exact hok.1 hD
      · exact hok.2 hA
  have ha3 : a 3 = 5 := by
    have hr := (hrec 2 (by omega)).2
    rw [show (2 : ℕ) + 1 = 3 from rfl] at hr; omega
  have hd4 : d 4 = -3 := by
    have hok : (-3 : ℤ) ∉ (Finset.Icc 1 3).image d ∧ a 3 + (-3) ∉ (Finset.Icc 1 3).image a := by
      constructor <;> intro hmem <;> rcases Finset.mem_image.mp hmem with ⟨i, hi, hieq⟩ <;>
        rcases (by have := Finset.mem_Icc.mp hi; omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;>
        omega
    have hr := hrule 3 (by omega)
    rw [show (3 : ℕ) + 1 = 4 from rfl] at hr
    rcases hr with hr1 | hr2
    · have hlt : d 4 < 0 := hr1.2.1
      have hne1 : d 4 ≠ -1 := by
        intro h
        apply hr1.2.2.1
        exact Finset.mem_image.mpr ⟨2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      have hne2 : d 4 ≠ -2 := by
        intro h
        apply hr1.2.2.1
        exact Finset.mem_image.mpr ⟨3, Finset.mem_Icc.mpr ⟨by omega, le_refl 3⟩, by omega⟩
      by_contra hne3
      have hlt3 : d 4 < -3 := by omega
      rcases hr1.2.2.2.2 (-3) hlt3 (by omega) with hD | hA
      · exact hok.1 hD
      · exact hok.2 hA
    · exfalso
      rcases hr2.1 (-3) (by omega) (by omega) with hD | hA
      · exact hok.1 hD
      · exact hok.2 hA
  have ha4 : a 4 = 2 := by
    have hr := (hrec 3 (by omega)).2
    rw [show (3 : ℕ) + 1 = 4 from rfl] at hr; omega
  exact ⟨a, d, ha1, hd1, hrec, hrule, by omega, by omega, by omega, hd2, hd3, hd4, ha2, ha3, ha4⟩

/-- Perturbation Barrier Witness 2 (`POS3` under Kimberling's exact Step 1 / Step 2 rule):
Starting from `(a₁, d₁) = (2, -1)`, Kimberling's exact greedy recurrence produces `d(2) = 1, d(3) = 2,
d(4) = 3` (`a = (2, 3, 5, 8)`), showing no invariant of the local greedy step alone forbids `POS3`. -/
theorem ppl143_perturbed_pos3_barrier :
    ∃ a d : ℕ → ℤ,
      a 1 = 2 ∧ d 1 = -1 ∧
      (∀ k : ℕ, 1 ≤ k → 1 ≤ a k ∧ a (k + 1) = a k + d (k + 1)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (1 - a k < d (k + 1) ∧ d (k + 1) < 0 ∧
          d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
          a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
          ∀ h' : ℤ, d (k + 1) < h' → h' < 0 →
            h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a) ∨
        ((∀ h : ℤ, 1 - a k < h → h < 0 →
            h ∈ (Finset.Icc 1 k).image d ∨ a k + h ∈ (Finset.Icc 1 k).image a) ∧
          0 < d (k + 1) ∧
          d (k + 1) ∉ (Finset.Icc 1 k).image d ∧
          a k + d (k + 1) ∉ (Finset.Icc 1 k).image a ∧
          ∀ h' : ℤ, 0 < h' → h' < d (k + 1) →
            h' ∈ (Finset.Icc 1 k).image d ∨ a k + h' ∈ (Finset.Icc 1 k).image a)) ∧
      0 < d 2 ∧ 0 < d 3 ∧ 0 < d 4 ∧ d 2 = 1 ∧ d 3 = 2 ∧ d 4 = 3 ∧
      a 2 = 3 ∧ a 3 = 5 ∧ a 4 = 8 := by
  obtain ⟨a, d, ha1, hd1, hrec, hrule, _⟩ := ppl143_existence_well_defined 2 (-1) (by omega)
  have hd2 : d 2 = 1 := by
    have hr := hrule 1 (le_refl 1)
    rw [show (1 : ℕ) + 1 = 2 from rfl] at hr
    rcases hr with hr1 | hr2
    · omega
    · have hpos : 0 < d 2 := hr2.2.1
      have hok : (1 : ℤ) ∉ (Finset.Icc 1 1).image d ∧ a 1 + 1 ∉ (Finset.Icc 1 1).image a := by
        constructor <;> intro hmem <;> rcases Finset.mem_image.mp hmem with ⟨i, hi, hieq⟩ <;>
          have : i = 1 := by have := Finset.mem_Icc.mp hi; omega
        · subst this; omega
        · subst this; omega
      by_contra hne
      rcases hr2.2.2.2.2 1 (by omega) (by omega) with hD | hA
      · exact hok.1 hD
      · exact hok.2 hA
  have ha2 : a 2 = 3 := by
    have hr := (hrec 1 (le_refl 1)).2
    rw [show (1 : ℕ) + 1 = 2 from rfl] at hr; omega
  have hd3 : d 3 = 2 := by
    have hr := hrule 2 (by omega)
    rw [show (2 : ℕ) + 1 = 3 from rfl] at hr
    rcases hr with hr1 | hr2
    · exfalso
      have h1 : d 3 = -1 := by omega
      apply hr1.2.2.1
      exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩, by omega⟩
    · have hpos : 0 < d 3 := hr2.2.1
      have hne1 : d 3 ≠ 1 := by
        intro h1
        apply hr2.2.2.1
        exact Finset.mem_image.mpr ⟨2, Finset.mem_Icc.mpr ⟨by omega, le_refl 2⟩, by omega⟩
      have hok : (2 : ℤ) ∉ (Finset.Icc 1 2).image d ∧ a 2 + 2 ∉ (Finset.Icc 1 2).image a := by
        constructor <;> intro hmem <;> rcases Finset.mem_image.mp hmem with ⟨i, hi, hieq⟩ <;>
          rcases (by have := Finset.mem_Icc.mp hi; omega : i = 1 ∨ i = 2) with rfl | rfl <;> omega
      by_contra hne2
      rcases hr2.2.2.2.2 2 (by omega) (by omega) with hD | hA
      · exact hok.1 hD
      · exact hok.2 hA
  have ha3 : a 3 = 5 := by
    have hr := (hrec 2 (by omega)).2
    rw [show (2 : ℕ) + 1 = 3 from rfl] at hr; omega
  have hd4 : d 4 = 3 := by
    have hr := hrule 3 (by omega)
    rw [show (3 : ℕ) + 1 = 4 from rfl] at hr
    rcases hr with hr1 | hr2
    · exfalso
      have hbound : 1 - a 3 < d 4 := hr1.1
      have hlt0 : d 4 < 0 := hr1.2.1
      rcases (by omega : d 4 = -1 ∨ d 4 = -2 ∨ d 4 = -3) with h1 | h2 | h3
      · apply hr1.2.2.1
        exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩, by omega⟩
      · apply hr1.2.2.2.1
        exact Finset.mem_image.mpr ⟨2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · apply hr1.2.2.2.1
        exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩, by omega⟩
    · have hpos : 0 < d 4 := hr2.2.1
      have hne1 : d 4 ≠ 1 := by
        intro h1
        apply hr2.2.2.1
        exact Finset.mem_image.mpr ⟨2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      have hne2 : d 4 ≠ 2 := by
        intro h2
        apply hr2.2.2.1
        exact Finset.mem_image.mpr ⟨3, Finset.mem_Icc.mpr ⟨by omega, le_refl 3⟩, by omega⟩
      have hok : (3 : ℤ) ∉ (Finset.Icc 1 3).image d ∧ a 3 + 3 ∉ (Finset.Icc 1 3).image a := by
        constructor <;> intro hmem <;> rcases Finset.mem_image.mp hmem with ⟨i, hi, hieq⟩ <;>
          rcases (by have := Finset.mem_Icc.mp hi; omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;>
          omega
      by_contra hne3
      rcases hr2.2.2.2.2 3 (by omega) (by omega) with hD | hA
      · exact hok.1 hD
      · exact hok.2 hA
  have ha4 : a 4 = 8 := by
    have hr := (hrec 3 (by omega)).2
    rw [show (3 : ℕ) + 1 = 4 from rfl] at hr; omega
  exact ⟨a, d, ha1, hd1, hrec, hrule, by omega, by omega, by omega, hd2, hd3, hd4, ha2, ha3, ha4⟩

end PerturbationBarrierWitnesses

end PPL143
