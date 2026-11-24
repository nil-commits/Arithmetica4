/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Arithmetica4 Extension: Extremal Set Systems & Correlation Inequalities (`Arith4Ext.SetSystemsCorrelation`)

Reusable Tier A `Arithmetica4` library module built 100% from scratch on targeted Mathlib
imports (`0` monolithic `import Mathlib`, `0` Tier C imports, `0` custom axioms, `0` custom
or private definitions in any public theorem signature).

## Exported API (`namespace Arith4Ext.SetSystemsCorrelation`)
1. **Bollobás Set-Pairs, LYM & Sperner:**
   - `bollobas_set_pairs`: `Disjoint (A i) (B j) ↔ i = j` ⇒ `∑ i ∈ I, 1 / C(|A i| + |B i|, |A i|) ≤ 1`.
   - `bollobas_set_pairs_uniform`: uniform `(a, b)` specialization `I.card ≤ C(a + b, a)`.
   - `lym_inequality`: `∑ A ∈ ℱ, 1 / C(n, |A|) ≤ 1` for antichains `ℱ` on `Fin n`.
   - `choose_le_choose_half`: `Nat.choose n k ≤ Nat.choose n (n / 2)`.
   - `sperner_theorem`: `ℱ.card ≤ Nat.choose n (n / 2)` for antichains `ℱ` on `Fin n`.
2. **Erdős–Ko–Rado (`1961`):**
   - `erdos_ko_rado`: Katona cyclic-order proof (`1 ≤ k`, `2 * k ≤ n` ⇒ `ℱ.card ≤ C(n - 1, k - 1)`).
3. **Sauer–Shelah–Perles (`1972`):**
   - `sauer_shelah`: VC-dimension shatter-free bound `ℱ.card ≤ ∑ k ≤ d, C(n, k)`.
4. **Ahlswede–Daykin (`1978`), Harris–Kleitman–FKG & Marica–Schönheim (`1969`):**
   - `ahlswede_daykin_four_functions`: Four-Functions Inequality on `𝒫(Fin n)`.
   - `harris_kleitman_fkg`: weighted `p`-biased product-measure FKG correlation inequality.
   - `harris_kleitman_upsets`: counting correlation `U.card * V.card ≤ 2 ^ n * (U ∩ V).card` for up-sets.
   - `kleitman_down_down`: counting correlation `𝒜.card * ℬ.card ≤ 2 ^ n * (𝒜 ∩ ℬ).card` for down-sets.
   - `marica_schonheim`: `𝒜.card ≤ ((𝒜 ×ˢ 𝒜).image (fun p => p.1 \ p.2)).card`.
-/

namespace Arith4Ext.SetSystemsCorrelation

open scoped BigOperators

/-! ### Section 1: Permutation-Counting Core, Bollobás Set-Pairs, LYM & Sperner -/

/-- For `U : Finset (Fin n)` and `S ⊆ U`, `permBefore U S` is the finset of permutations
`π : Equiv.Perm (Fin n)` placing every element of `S` strictly before every element of `U \ S`. -/
private noncomputable def permBefore {n : ℕ} (U S : Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun π => ∀ x ∈ S, ∀ y ∈ U \ S, π x < π y)

/-- Partition identity: for any `U : Finset (Fin n)` and `a ≤ U.card`, every `π : Equiv.Perm (Fin n)`
belongs to `permBefore U S` for a unique `S ∈ U.powersetCard a`. -/
private lemma permBefore_partition {n a : ℕ} {U : Finset (Fin n)} (ha : a ≤ U.card)
    (π : Equiv.Perm (Fin n)) :
    ∃! S, S ∈ U.powersetCard a ∧ π ∈ permBefore U S := by
  let rank : Fin n → ℕ := fun x => (U.filter (fun z => π z < π x)).card
  have hrank_lt : ∀ x ∈ U, rank x < U.card := by
    intro x hx
    have hsub : U.filter (fun z => π z < π x) ⊆ U.erase x := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzU, hlt⟩
      exact Finset.mem_erase.mpr ⟨fun heq => by subst heq; exact lt_irrefl _ hlt, hzU⟩
    have hcard_er : (U.erase x).card < U.card := Finset.card_erase_lt_of_mem hx
    exact lt_of_le_of_lt (Finset.card_le_card hsub) hcard_er
  have hrank_inj : (U : Set (Fin n)).InjOn rank := by
    intro x₁ hx₁ x₂ hx₂ heq
    by_contra hne
    have hne_pi : π x₁ ≠ π x₂ := fun h => hne (π.injective h)
    rcases lt_or_gt_of_ne hne_pi with hlt | hlt
    · have hsub : U.filter (fun z => π z < π x₁) ⊂ U.filter (fun z => π z < π x₂) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨x₁, Finset.mem_filter.mpr ⟨hx₁, hlt⟩, fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩
        · intro z hz
          rcases Finset.mem_filter.mp hz with ⟨hzU, hzx₁⟩
          exact Finset.mem_filter.mpr ⟨hzU, lt_trans hzx₁ hlt⟩
      exact (Finset.card_lt_card hsub).ne heq
    · have hsub : U.filter (fun z => π z < π x₂) ⊂ U.filter (fun z => π z < π x₁) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨x₂, Finset.mem_filter.mpr ⟨hx₂, hlt⟩, fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩
        · intro z hz
          rcases Finset.mem_filter.mp hz with ⟨hzU, hzx₂⟩
          exact Finset.mem_filter.mpr ⟨hzU, lt_trans hzx₂ hlt⟩
      exact (Finset.card_lt_card hsub).ne heq.symm
  have himg_eq : U.image rank = Finset.range U.card := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro r hr
      rcases Finset.mem_image.mp hr with ⟨x, hx, rfl⟩
      exact Finset.mem_range.mpr (hrank_lt x hx)
    · rw [Finset.card_image_of_injOn hrank_inj, Finset.card_range]
  let S₀ : Finset (Fin n) := U.filter (fun x => rank x < a)
  have hS₀_img : S₀.image rank = Finset.range a := by
    ext r
    simp only [Finset.mem_image, S₀, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨x, ⟨_, hxa⟩, rfl⟩; exact hxa
    · intro hra
      have hrU : r ∈ Finset.range U.card := Finset.mem_range.mpr (lt_of_lt_of_le hra ha)
      rw [← himg_eq] at hrU
      rcases Finset.mem_image.mp hrU with ⟨x, hxU, hrx⟩
      exact ⟨x, ⟨hxU, hrx ▸ hra⟩, hrx⟩
  have hS₀_card : S₀.card = a := by
    have hinj : (S₀ : Set (Fin n)).InjOn rank := hrank_inj.mono (Finset.filter_subset _ _)
    rw [← Finset.card_image_of_injOn hinj, hS₀_img, Finset.card_range]
  have hS₀_mem : S₀ ∈ U.powersetCard a :=
    Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hS₀_card⟩
  have hS₀_perm : π ∈ permBefore U S₀ := by
    rw [permBefore, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun x hx y hy => ?_⟩
    have hxU : x ∈ U := (Finset.mem_filter.mp hx).1
    have hxlt : rank x < a := (Finset.mem_filter.mp hx).2
    have hyU : y ∈ U := (Finset.mem_sdiff.mp hy).1
    have hy_not : y ∉ S₀ := (Finset.mem_sdiff.mp hy).2
    have hage : a ≤ rank y := by
      by_contra hlt
      exact hy_not (Finset.mem_filter.mpr ⟨hyU, Nat.lt_of_not_le hlt⟩)
    have hrx_lt_y : rank x < rank y := lt_of_lt_of_le hxlt hage
    by_contra hge
    have hle : π y ≤ π x := le_of_not_gt hge
    have hsub : U.filter (fun z => π z < π y) ⊆ U.filter (fun z => π z < π x) := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzU, hzy⟩
      exact Finset.mem_filter.mpr ⟨hzU, lt_of_lt_of_le hzy hle⟩
    exact (Nat.not_le_of_lt hrx_lt_y) (Finset.card_le_card hsub)
  refine ⟨S₀, ⟨hS₀_mem, hS₀_perm⟩, ?_⟩
  rintro S ⟨hS_pow, hS_perm⟩
  rcases Finset.mem_powersetCard.mp hS_pow with ⟨hSU, hS_card⟩
  have hS_bef := (Finset.mem_filter.mp hS_perm).2
  have hsub : S ⊆ S₀ := by
    intro x hxS
    refine Finset.mem_filter.mpr ⟨hSU hxS, ?_⟩
    have hsub_er : U.filter (fun z => π z < π x) ⊆ S.erase x := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzU, hzx⟩
      refine Finset.mem_erase.mpr ⟨fun heq => by subst heq; exact lt_irrefl _ hzx, ?_⟩
      by_contra hzS
      have hxz := hS_bef x hxS z (Finset.mem_sdiff.mpr ⟨hzU, hzS⟩)
      exact lt_asymm hzx hxz
    have hcard_lt : (S.erase x).card < a := by
      rw [Finset.card_erase_of_mem hxS, hS_card]
      exact Nat.sub_lt (Nat.pos_of_ne_zero (by
        intro h0; rw [h0] at hS_card; simp [Finset.card_eq_zero.mp hS_card] at hxS)) one_pos
    exact lt_of_le_of_lt (Finset.card_le_card hsub_er) hcard_lt
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hS₀_card, hS_card])

/-- Swap bijection: any two subsets `S₁, S₂ ⊆ U` of the same cardinality give `(permBefore U S₁).card = (permBefore U S₂).card`. -/
private lemma permBefore_card_eq {n : ℕ} {U S₁ S₂ : Finset (Fin n)}
    (h1 : S₁ ⊆ U) (h2 : S₂ ⊆ U) (hcard : S₁.card = S₂.card) :
    (permBefore U S₁).card = (permBefore U S₂).card := by
  classical
  let e₁ : S₁ ≃ S₂ := Fintype.equivOfCardEq (by simp [hcard])
  let e₂ : ↥(U \ S₁) ≃ ↥(U \ S₂) := Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, Fintype.card_coe,
      Finset.card_sdiff_of_subset h1, Finset.card_sdiff_of_subset h2, hcard])
  let toFun : Fin n → Fin n := fun x =>
    if hx1 : x ∈ S₁ then (e₁ ⟨x, hx1⟩).1
    else if hxU : x ∈ U then (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨hxU, hx1⟩⟩).1
    else x
  let invFun : Fin n → Fin n := fun y =>
    if hy2 : y ∈ S₂ then (e₁.symm ⟨y, hy2⟩).1
    else if hyU : y ∈ U then (e₂.symm ⟨y, Finset.mem_sdiff.mpr ⟨hyU, hy2⟩⟩).1
    else y
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    dsimp only [toFun, invFun]
    by_cases hx1 : x ∈ S₁
    · have hm : (e₁ ⟨x, hx1⟩).1 ∈ S₂ := (e₁ ⟨x, hx1⟩).2
      rw [dif_pos hx1, dif_pos hm]
      simp
    · by_cases hxU : x ∈ U
      · have hy_mem := (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨hxU, hx1⟩⟩).2
        have hyU : (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨hxU, hx1⟩⟩).1 ∈ U :=
          (Finset.mem_sdiff.mp hy_mem).1
        have hy2 : (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨hxU, hx1⟩⟩).1 ∉ S₂ :=
          (Finset.mem_sdiff.mp hy_mem).2
        rw [dif_neg hx1, dif_pos hxU, dif_neg hy2, dif_pos hyU]
        simp
      · have hx2 : x ∉ S₂ := fun h => hxU (h2 h)
        rw [dif_neg hx1, dif_neg hxU, dif_neg hx2, dif_neg hxU]
  have hright : Function.RightInverse invFun toFun := by
    intro y
    dsimp only [toFun, invFun]
    by_cases hy2 : y ∈ S₂
    · have hm : (e₁.symm ⟨y, hy2⟩).1 ∈ S₁ := (e₁.symm ⟨y, hy2⟩).2
      rw [dif_pos hy2, dif_pos hm]
      simp
    · by_cases hyU : y ∈ U
      · have hx_mem := (e₂.symm ⟨y, Finset.mem_sdiff.mpr ⟨hyU, hy2⟩⟩).2
        have hxU : (e₂.symm ⟨y, Finset.mem_sdiff.mpr ⟨hyU, hy2⟩⟩).1 ∈ U :=
          (Finset.mem_sdiff.mp hx_mem).1
        have hx1 : (e₂.symm ⟨y, Finset.mem_sdiff.mpr ⟨hyU, hy2⟩⟩).1 ∉ S₁ :=
          (Finset.mem_sdiff.mp hx_mem).2
        rw [dif_neg hy2, dif_pos hyU, dif_neg hx1, dif_pos hxU]
        simp
      · have hy1 : y ∉ S₁ := fun h => hyU (h1 h)
        rw [dif_neg hy2, dif_neg hyU, dif_neg hy1, dif_neg hyU]
  let φ : Equiv.Perm (Fin n) := ⟨toFun, invFun, hleft, hright⟩
  have hφ_S : ∀ x ∈ S₁, φ x ∈ S₂ := by
    intro x hx1
    change toFun x ∈ S₂
    dsimp only [toFun]
    rw [dif_pos hx1]
    exact (e₁ ⟨x, hx1⟩).2
  have hφ_diff : ∀ y ∈ U \ S₁, φ y ∈ U \ S₂ := by
    intro y hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyU, hy1⟩
    change toFun y ∈ U \ S₂
    dsimp only [toFun]
    rw [dif_neg hy1, dif_pos hyU]
    exact (e₂ ⟨y, Finset.mem_sdiff.mpr ⟨hyU, hy1⟩⟩).2
  have hφ_symm_S : ∀ u ∈ S₂, φ.symm u ∈ S₁ := by
    intro u hu2
    change invFun u ∈ S₁
    dsimp only [invFun]
    rw [dif_pos hu2]
    exact (e₁.symm ⟨u, hu2⟩).2
  have hφ_symm_diff : ∀ v ∈ U \ S₂, φ.symm v ∈ U \ S₁ := by
    intro v hv
    rcases Finset.mem_sdiff.mp hv with ⟨hvU, hv2⟩
    change invFun v ∈ U \ S₁
    dsimp only [invFun]
    rw [dif_neg hv2, dif_pos hvU]
    exact (e₂.symm ⟨v, Finset.mem_sdiff.mpr ⟨hvU, hv2⟩⟩).2
  refine Finset.card_bij (fun π _ => π * φ.symm) ?_ ?_ ?_
  · intro π hπ
    rw [permBefore, Finset.mem_filter] at hπ ⊢
    refine ⟨Finset.mem_univ _, fun x hx y hy => ?_⟩
    exact hπ.2 (φ.symm x) (hφ_symm_S x hx) (φ.symm y) (hφ_symm_diff y hy)
  · intro π₁ _ π₂ _ h
    exact mul_right_cancel h
  · intro π' hπ'
    refine ⟨π' * φ, ?_, by ext x; simp⟩
    rw [permBefore, Finset.mem_filter] at hπ' ⊢
    refine ⟨Finset.mem_univ _, fun u hu v hv => ?_⟩
    exact hπ'.2 (φ u) (hφ_S u hu) (φ v) (hφ_diff v hv)

/-- Exact count: `(permBefore (A ∪ B) A).card * Nat.choose (A.card + B.card) A.card = n!`
whenever `A, B : Finset (Fin n)` are disjoint. -/
private lemma permBefore_card_mul_choose {n : ℕ} {A B : Finset (Fin n)} (hAB : Disjoint A B) :
    (permBefore (A ∪ B) A).card * Nat.choose (A.card + B.card) A.card = Nat.factorial n := by
  classical
  let U := A ∪ B
  have hU_card : U.card = A.card + B.card := Finset.card_union_of_disjoint hAB
  have ha_le : A.card ≤ U.card := hU_card ▸ Nat.le_add_right _ _
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n))) =
      (U.powersetCard A.card).biUnion (permBefore U) := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    obtain ⟨S, hS, _⟩ := permBefore_partition ha_le π
    exact ⟨S, hS⟩
  have hdisj : (U.powersetCard A.card : Set (Finset (Fin n))).PairwiseDisjoint (permBefore U) := by
    intro S₁ h1 S₂ h2 hne
    rw [Finset.mem_coe] at h1 h2
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π hp1 hp2
    obtain ⟨S, _, huniq⟩ := permBefore_partition ha_le π
    exact hne ((huniq S₁ ⟨h1, hp1⟩).trans (huniq S₂ ⟨h2, hp2⟩).symm)
  have hfact_card : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hcard_eq : Nat.factorial n =
      ∑ S ∈ U.powersetCard A.card, (permBefore U S).card := by
    rw [← hfact_card, huniv, Finset.card_biUnion hdisj]
  have hconst : ∑ S ∈ U.powersetCard A.card, (permBefore U S).card =
      (U.powersetCard A.card).card * (permBefore U A).card := by
    calc ∑ S ∈ U.powersetCard A.card, (permBefore U S).card
        = ∑ _S ∈ U.powersetCard A.card, (permBefore U A).card := by
            refine Finset.sum_congr rfl fun S hS => ?_
            rcases Finset.mem_powersetCard.mp hS with ⟨hSU, hScard⟩
            exact permBefore_card_eq hSU Finset.subset_union_left hScard
      _ = (U.powersetCard A.card).card * (permBefore U A).card := by
            rw [Finset.sum_const, smul_eq_mul]
  rw [hcard_eq, hconst, Finset.card_powersetCard, hU_card, mul_comm]

private lemma bollobas_fin {n : ℕ} {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (A B : ι → Finset (Fin n)) (hDisj : ∀ i ∈ I, ∀ j ∈ I, Disjoint (A i) (B j) ↔ i = j) :
    ∑ i ∈ I, (1 : ℝ) / (Nat.choose ((A i).card + (B i).card) (A i).card : ℝ) ≤ 1 := by
  classical
  let E : ι → Finset (Equiv.Perm (Fin n)) := fun i => permBefore (A i ∪ B i) (A i)
  have hE_disj : (I : Set ι).PairwiseDisjoint E := by
    intro i hi j hj hij
    rw [Finset.mem_coe] at hi hj
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π hπi hπj
    dsimp only [E] at hπi hπj
    rw [permBefore, Finset.mem_filter] at hπi hπj
    have hnd1 : ¬ Disjoint (A i) (B j) := fun h => hij ((hDisj i hi j hj).mp h)
    have hnd2 : ¬ Disjoint (A j) (B i) := fun h => hij ((hDisj j hj i hi).mp h).symm
    obtain ⟨x, hxAi, hxBj⟩ := Finset.not_disjoint_iff.mp hnd1
    obtain ⟨y, hyAj, hyBi⟩ := Finset.not_disjoint_iff.mp hnd2
    have hxy : π x < π y :=
      hπi.2 x hxAi y (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hyBi,
        Finset.disjoint_right.mp ((hDisj i hi i hi).mpr rfl) hyBi⟩)
    have hyx : π y < π x :=
      hπj.2 y hyAj x (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hxBj,
        Finset.disjoint_right.mp ((hDisj j hj j hj).mpr rfl) hxBj⟩)
    exact lt_asymm hxy hyx
  have hfact_card : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hsum_le : ∑ i ∈ I, (E i).card ≤ Nat.factorial n := by
    rw [← Finset.card_biUnion hE_disj, ← hfact_card]
    exact Finset.card_le_univ _
  have hn_pos : (0 : ℝ) < (Nat.factorial n : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hterm : ∀ i ∈ I,
      (1 : ℝ) / (Nat.choose ((A i).card + (B i).card) (A i).card : ℝ) =
        ((E i).card : ℝ) / (Nat.factorial n : ℝ) := by
    intro i hi
    have hAB : Disjoint (A i) (B i) := (hDisj i hi i hi).mpr rfl
    have hcnt := permBefore_card_mul_choose hAB
    have hchoose_pos : (0 : ℝ) < (Nat.choose ((A i).card + (B i).card) (A i).card : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right _ _))
    have hcntR : ((E i).card : ℝ) * (Nat.choose ((A i).card + (B i).card) (A i).card : ℝ) =
        (Nat.factorial n : ℝ) := by exact_mod_cast hcnt
    field_simp [hchoose_pos.ne', hn_pos.ne']
    linarith
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, div_le_one hn_pos]
  exact_mod_cast hsum_le

/-- **Bollobás Set-Pairs Inequality (1965)**: for any finite indexed family of pairs
`(A i, B i)` (`i ∈ I`) such that `Disjoint (A i) (B j) ↔ i = j`,
`∑ i ∈ I, 1 / C(|A i| + |B i|, |A i|) ≤ 1`. -/
theorem bollobas_set_pairs {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A B : ι → Finset α)
    (hDisj : ∀ i ∈ I, ∀ j ∈ I, Disjoint (A i) (B j) ↔ i = j) :
    ∑ i ∈ I, (1 : ℝ) / (Nat.choose ((A i).card + (B i).card) (A i).card : ℝ) ≤ 1 := by
  classical
  let U : Finset α := I.biUnion (fun i => A i ∪ B i)
  let e := Fintype.equivFin U
  let A' : ι → Finset (Fin (Fintype.card U)) := fun i =>
    (Finset.univ : Finset (Fin (Fintype.card U))).filter (fun k => (e.symm k).1 ∈ A i)
  let B' : ι → Finset (Fin (Fintype.card U)) := fun i =>
    (Finset.univ : Finset (Fin (Fintype.card U))).filter (fun k => (e.symm k).1 ∈ B i)
  have hA_sub : ∀ i ∈ I, A i ⊆ U := fun i hi _ hx =>
    Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_left _ hx⟩
  have hB_sub : ∀ i ∈ I, B i ⊆ U := fun i hi _ hx =>
    Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_right _ hx⟩
  have hA_card : ∀ i ∈ I, (A' i).card = (A i).card := by
    intro i hi
    refine Finset.card_bij (fun k _ => (e.symm k).1) ?_ ?_ ?_
    · intro k hk; exact (Finset.mem_filter.mp hk).2
    · intro k₁ _ k₂ _ h; exact e.symm.injective (Subtype.ext h)
    · intro x hx
      refine ⟨e ⟨x, hA_sub i hi hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩ <;> simp [hx]
  have hB_card : ∀ i ∈ I, (B' i).card = (B i).card := by
    intro i hi
    refine Finset.card_bij (fun k _ => (e.symm k).1) ?_ ?_ ?_
    · intro k hk; exact (Finset.mem_filter.mp hk).2
    · intro k₁ _ k₂ _ h; exact e.symm.injective (Subtype.ext h)
    · intro x hx
      refine ⟨e ⟨x, hB_sub i hi hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩ <;> simp [hx]
  have hDisj' : ∀ i ∈ I, ∀ j ∈ I, Disjoint (A' i) (B' j) ↔ i = j := by
    intro i hi j hj
    rw [← hDisj i hi j hj, Finset.disjoint_left, Finset.disjoint_left]
    constructor
    · intro h x hxA hxB
      have hxA' : e ⟨x, hA_sub i hi hxA⟩ ∈ A' i := by simp [A', hxA]
      have hxB' : e ⟨x, hA_sub i hi hxA⟩ ∈ B' j := by simp [B', hxB]
      exact h hxA' hxB'
    · intro h k hkA hkB
      exact h (Finset.mem_filter.mp hkA).2 (Finset.mem_filter.mp hkB).2
  have hmain := bollobas_fin I A' B' hDisj'
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_)) hmain
  rw [hA_card i hi, hB_card i hi]

/-- **Uniform Bollobás Set-Pairs Inequality**: if `Disjoint (A i) (B j) ↔ i = j` with
`|A i| = a` and `|B i| = b` for all `i ∈ I`, then `I.card ≤ Nat.choose (a + b) a`. -/
theorem bollobas_set_pairs_uniform {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (a b : ℕ) (I : Finset ι) (A B : ι → Finset α)
    (hA : ∀ i ∈ I, (A i).card = a) (hB : ∀ i ∈ I, (B i).card = b)
    (hDisj : ∀ i ∈ I, ∀ j ∈ I, Disjoint (A i) (B j) ↔ i = j) :
    I.card ≤ Nat.choose (a + b) a := by
  have hbol := bollobas_set_pairs I A B hDisj
  have hsum : ∑ i ∈ I, (1 : ℝ) / (Nat.choose ((A i).card + (B i).card) (A i).card : ℝ) =
      (I.card : ℝ) / (Nat.choose (a + b) a : ℝ) := by
    calc ∑ i ∈ I, (1 : ℝ) / (Nat.choose ((A i).card + (B i).card) (A i).card : ℝ)
        = ∑ _i ∈ I, (1 : ℝ) / (Nat.choose (a + b) a : ℝ) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [hA i hi, hB i hi]
      _ = (I.card : ℝ) / (Nat.choose (a + b) a : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [hsum] at hbol
  have hpos : (0 : ℝ) < (Nat.choose (a + b) a : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right a b))
  have hle : (I.card : ℝ) ≤ (Nat.choose (a + b) a : ℝ) := (div_le_one hpos).mp hbol
  exact_mod_cast hle

/-- **LYM Inequality (Lubell–Yamamoto–Meshalkin)**: for any antichain `ℱ : Finset (Finset (Fin n))`,
`∑ A ∈ ℱ, (1 : ℝ) / Nat.choose n A.card ≤ 1`. -/
theorem lym_inequality {n : ℕ} (ℱ : Finset (Finset (Fin n)))
    (hAnti : ∀ A ∈ ℱ, ∀ B ∈ ℱ, A ⊆ B → A = B) :
    ∑ A ∈ ℱ, (1 : ℝ) / (Nat.choose n A.card : ℝ) ≤ 1 := by
  let B : Finset (Fin n) → Finset (Fin n) := fun A => Finset.univ \ A
  have hDisj : ∀ A₁ ∈ ℱ, ∀ A₂ ∈ ℱ, Disjoint A₁ (B A₂) ↔ A₁ = A₂ := by
    intro A₁ h1 A₂ h2
    have hdisj_iff : Disjoint A₁ (Finset.univ \ A₂) ↔ A₁ ⊆ A₂ := by
      rw [Finset.disjoint_left]
      constructor
      · intro h x hx
        by_contra hx2
        exact h hx (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx2⟩)
      · intro hsub x hx1 hx2
        exact (Finset.mem_sdiff.mp hx2).2 (hsub hx1)
    rw [show B A₂ = Finset.univ \ A₂ from rfl, hdisj_iff]
    exact ⟨fun hsub => hAnti A₁ h1 A₂ h2 hsub, fun heq => heq ▸ Finset.Subset.rfl⟩
  have hbol := bollobas_set_pairs ℱ id B hDisj
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun A _ => ?_)) hbol
  have hsum : (id A).card + (B A).card = n := by
    simp only [id, B, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ,
      Fintype.card_fin]
    exact Nat.add_sub_cancel' (le_trans (Finset.card_le_univ A) (by simp))
  rw [hsum]; rfl

private lemma succ_mul_choose_eq_sub_mul (n k : ℕ) :
    (k + 1) * Nat.choose n (k + 1) = (n - k) * Nat.choose n k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rcases Nat.lt_trichotomy n k with hlt | rfl | hgt
      · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
        simp
      · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.sub_self]
        simp
      · rw [Nat.choose_succ_succ n (k + 1), mul_add, ih (k + 1), Nat.choose_succ_succ n k]
        have h1 : (k + 2) * Nat.choose n (k + 1) =
            Nat.choose n (k + 1) + (k + 1) * Nat.choose n (k + 1) := by ring
        rw [h1, ih k, Nat.succ_eq_add_one]
        have hsub1 : n + 1 - (k + 1) = n - k := by omega
        rw [hsub1]
        zify [show k ≤ n by omega, show k + 1 ≤ n by omega]
        ring

private lemma succ_mul_choose_succ (n k : ℕ) (hkn : k ≤ n) :
    (k + 1) * Nat.choose (n + 1) (k + 1) = (n + 1) * Nat.choose n k := by
  rw [Nat.choose_succ_succ n k, mul_add, succ_mul_choose_eq_sub_mul n k]
  zify [hkn]
  ring

/-- Central binomial maximality: `Nat.choose n k ≤ Nat.choose n (n / 2)` for all `n, k : ℕ`. -/
theorem choose_le_choose_half (n k : ℕ) : Nat.choose n k ≤ Nat.choose n (n / 2) := by
  have hinc : ∀ m : ℕ, m < n / 2 → Nat.choose n m ≤ Nat.choose n (m + 1) := by
    intro m hm
    have hmul := succ_mul_choose_eq_sub_mul n m
    have hle : m + 1 ≤ n - m := by omega
    have h2 : (m + 1) * Nat.choose n m ≤ (m + 1) * Nat.choose n (m + 1) := by
      rw [hmul]
      exact Nat.mul_le_mul_right (Nat.choose n m) hle
    exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos m)
  have hup : ∀ j : ℕ, j ≤ n / 2 → Nat.choose n j ≤ Nat.choose n (n / 2) := by
    intro j hj
    have hdiff : ∀ d : ℕ, ∀ m : ℕ, m + d = n / 2 → Nat.choose n m ≤ Nat.choose n (n / 2) := by
      intro d
      induction d with
      | zero => intro m hm; simp only [add_zero] at hm; rw [hm]
      | succ d ih =>
        intro m hm
        have hlt : m < n / 2 := by omega
        exact le_trans (hinc m hlt) (ih (m + 1) (by omega))
    exact hdiff (n / 2 - j) j (by omega)
  rcases le_or_gt k (n / 2) with hk | hk
  · exact hup k hk
  · rcases le_or_gt k n with hkn | hkn
    · rw [← Nat.choose_symm hkn]
      exact hup (n - k) (by omega)
    · rw [Nat.choose_eq_zero_of_lt hkn]
      exact Nat.zero_le _

/-- **Sperner's Theorem (1928)**: every antichain `ℱ : Finset (Finset (Fin n))` satisfies
`ℱ.card ≤ Nat.choose n (n / 2)`. -/
theorem sperner_theorem {n : ℕ} (ℱ : Finset (Finset (Fin n)))
    (hAnti : ∀ A ∈ ℱ, ∀ B ∈ ℱ, A ⊆ B → A = B) :
    ℱ.card ≤ Nat.choose n (n / 2) := by
  have hlym := lym_inequality ℱ hAnti
  have hpos : (0 : ℝ) < (Nat.choose n (n / 2) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.div_le_self n 2))
  have hlow : (ℱ.card : ℝ) / (Nat.choose n (n / 2) : ℝ) ≤
      ∑ A ∈ ℱ, (1 : ℝ) / (Nat.choose n A.card : ℝ) := by
    calc (ℱ.card : ℝ) / (Nat.choose n (n / 2) : ℝ)
        = ∑ _A ∈ ℱ, (1 : ℝ) / (Nat.choose n (n / 2) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ ∑ A ∈ ℱ, (1 : ℝ) / (Nat.choose n A.card : ℝ) := by
            refine Finset.sum_le_sum fun A _ => ?_
            rcases le_or_gt A.card n with hAn | hAn
            · have hch : (0 : ℝ) < (Nat.choose n A.card : ℝ) :=
                Nat.cast_pos.mpr (Nat.choose_pos hAn)
              exact one_div_le_one_div_of_le hch (Nat.cast_le.mpr (choose_le_choose_half n A.card))
            · exfalso
              have hle : A.card ≤ n := by simpa using Finset.card_le_univ A
              omega
  have hle : (ℱ.card : ℝ) ≤ (Nat.choose n (n / 2) : ℝ) :=
    (div_le_one hpos).mp (le_trans hlow hlym)
  exact_mod_cast hle

/-! ### Section 2: Erdős–Ko–Rado Theorem (1961) via Katona's Cyclic Method -/

private noncomputable def cyclicArc {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) (s : Fin n) :
    Finset (Fin n) :=
  (Finset.range k).image (fun t => σ ⟨(s.1 + t) % n, Nat.mod_lt _ (Fin.pos s)⟩)

private lemma cyclicArc_disjoint {n k : ℕ} (hkn : 2 * k ≤ n) (_σ : Equiv.Perm (Fin n))
    (s₁ s₂ : Fin n) (hs₁ : s₁.1 < n) (_hs₂ : s₂.1 < n)
    (t₁ t₂ : ℕ) (ht₁ : t₁ < k) (ht₂ : t₂ < k) (hstep : (s₂.1 + k) % n = s₁.1) :
    (s₁.1 + t₁) % n ≠ (s₂.1 + t₂) % n := by
  have hn : 0 < n := by omega
  intro heq
  have hmod : (s₂.1 + k + t₁) % n = (s₂.1 + t₂) % n := by
    calc (s₂.1 + k + t₁) % n
        = ((s₂.1 + k) % n + t₁ % n) % n := by rw [Nat.add_mod]
      _ = (s₁.1 % n + t₁ % n) % n := by rw [hstep, Nat.mod_eq_of_lt hs₁]
      _ = (s₁.1 + t₁) % n := by rw [← Nat.add_mod]
      _ = (s₂.1 + t₂) % n := heq
  have hdiff : ((s₂.1 + k + t₁) - (s₂.1 + t₂)) % n = 0 := by
    have hge : s₂.1 + t₂ < s₂.1 + k + t₁ := by omega
    rw [Nat.mod_eq_zero_of_dvd]
    have hd : n ∣ (s₂.1 + k + t₁) - (s₂.1 + t₂) := by
      rw [← Nat.modEq_iff_dvd' hge.le]
      exact hmod.symm
    exact hd
  have hbd : 0 < (s₂.1 + k + t₁) - (s₂.1 + t₂) ∧ (s₂.1 + k + t₁) - (s₂.1 + t₂) < n := by omega
  have hlt_eq : ((s₂.1 + k + t₁) - (s₂.1 + t₂)) % n = (s₂.1 + k + t₁) - (s₂.1 + t₂) :=
    Nat.mod_eq_of_lt hbd.2
  omega

/-- Katona's cyclic lemma: for any `k`-uniform intersecting family `ℱ` (`1 ≤ k`, `2 * k ≤ n`) and
permutation `σ : Equiv.Perm (Fin n)`, at most `k` cyclic shifts `s : Fin n` satisfy `cyclicArc k σ s ∈ ℱ`. -/
private lemma katona_cyclic_le {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (ℱ : Finset (Finset (Fin n))) (hinter : ∀ A ∈ ℱ, ∀ B ∈ ℱ, ¬ Disjoint A B)
    (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun s : Fin n => cyclicArc k σ s ∈ ℱ)).card ≤ k := by
  classical
  let good : Finset (Fin n) := Finset.univ.filter (fun s : Fin n => cyclicArc k σ s ∈ ℱ)
  by_cases hne : good.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hne
    have hs₀_mem : cyclicArc k σ s₀ ∈ ℱ := (Finset.mem_filter.mp hs₀).2
    have hn : 0 < n := by omega
    let p₁ : ℕ → Fin n := fun j => ⟨(s₀.1 + j) % n, Nat.mod_lt _ hn⟩
    let p₂ : ℕ → Fin n := fun j => ⟨(s₀.1 + n + j - k) % n, Nat.mod_lt _ hn⟩
    have hp_disj : ∀ j ∈ Finset.Ico 1 k, Disjoint (cyclicArc k σ (p₁ j)) (cyclicArc k σ (p₂ j)) := by
      intro j hj
      rcases Finset.mem_Ico.mp hj with ⟨hj1, hjk⟩
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨t₁, ht₁, rfl⟩
      rcases Finset.mem_image.mp hx2 with ⟨t₂, ht₂, heq⟩
      have heq' := σ.injective heq
      have hval : ((p₁ j).1 + t₁) % n = ((p₂ j).1 + t₂) % n := (congrArg Fin.val heq').symm
      have hstep : ((p₂ j).1 + k) % n = (p₁ j).1 := by
        dsimp only [p₁, p₂]
        have heq_add : (s₀.1 + n + j - k) + k = (s₀.1 + j) + n := by omega
        rw [Nat.mod_add_mod, heq_add, Nat.add_mod_right]
      exact cyclicArc_disjoint hkn σ (p₁ j) (p₂ j) (p₁ j).isLt (p₂ j).isLt
        t₁ t₂ (Finset.mem_range.mp ht₁) (Finset.mem_range.mp ht₂) hstep hval
    have hcover : good ⊆ insert s₀ ((Finset.Ico 1 k).biUnion (fun j => ({p₁ j, p₂ j} ∩ good))) := by
      intro s hs
      by_cases hss₀ : s = s₀
      · subst hss₀; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        have hs_mem : cyclicArc k σ s ∈ ℱ := (Finset.mem_filter.mp hs).2
        have hnd : ¬ Disjoint (cyclicArc k σ s) (cyclicArc k σ s₀) :=
          hinter _ hs_mem _ hs₀_mem
        obtain ⟨x, hxs, hxs₀⟩ := Finset.not_disjoint_iff.mp hnd
        rcases Finset.mem_image.mp hxs with ⟨t₁, ht₁, rfl⟩
        rcases Finset.mem_image.mp hxs₀ with ⟨t₂, ht₂, heq⟩
        have ht₁k : t₁ < k := Finset.mem_range.mp ht₁
        have ht₂k : t₂ < k := Finset.mem_range.mp ht₂
        have hval : (s₀.1 + t₂) % n = (s.1 + t₁) % n := congrArg Fin.val (σ.injective heq)
        rcases le_or_gt t₁ t₂ with hle | hlt
        · let j := t₂ - t₁
          have hj_ne : j ≠ 0 := by
            intro hj0
            have ht_eq : t₁ = t₂ := by omega
            rw [ht_eq] at hval
            have hs_mod : s₀.1 % n = s.1 % n := by
              have hsub : (s₀.1 + t₂) - (s.1 + t₂) = s₀.1 - s.1 := by omega
              rcases le_or_gt s.1 s₀.1 with hsle | hslt
              · have hd : n ∣ (s₀.1 + t₂) - (s.1 + t₂) := by
                  rw [← Nat.modEq_iff_dvd' (by omega)]
                  exact hval.symm
                rw [hsub] at hd
                have hlt0 : s₀.1 - s.1 < n := by omega
                have h0 : s₀.1 - s.1 = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt0
                exact absurd (Fin.ext (by omega)) (Ne.symm hss₀)
              · have hd : n ∣ (s.1 + t₂) - (s₀.1 + t₂) := by
                  rw [← Nat.modEq_iff_dvd' (by omega)]
                  exact hval
                have hsub' : (s.1 + t₂) - (s₀.1 + t₂) = s.1 - s₀.1 := by omega
                rw [hsub'] at hd
                have hlt0 : s.1 - s₀.1 < n := by omega
                have h0 : s.1 - s₀.1 = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt0
                exact absurd (Fin.ext (by omega)) hss₀
            exact hss₀ (Fin.ext (by rw [← Nat.mod_eq_of_lt s.isLt, ← Nat.mod_eq_of_lt s₀.isLt, hs_mod]))
          have hj_mem : j ∈ Finset.Ico 1 k := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          have hs_eq : s = p₁ j := by
            apply Fin.ext
            dsimp only [p₁, j]
            have hm : (s₀.1 + (t₂ - t₁)) % n = s.1 % n := by
              rcases le_or_gt (s₀.1 + (t₂ - t₁)) s.1 with h1 | h2
              · have hdv : n ∣ (s.1 + t₁) - (s₀.1 + t₂) := by
                  rw [← Nat.modEq_iff_dvd' (by omega)]; exact hval
                have heq' : (s.1 + t₁) - (s₀.1 + t₂) = s.1 - (s₀.1 + (t₂ - t₁)) := by omega
                rw [heq', ← Nat.modEq_iff_dvd' h1] at hdv; exact hdv
              · have hdv : n ∣ (s₀.1 + t₂) - (s.1 + t₁) := by
                  rw [← Nat.modEq_iff_dvd' (by omega)]; exact hval.symm
                have heq' : (s₀.1 + t₂) - (s.1 + t₁) = (s₀.1 + (t₂ - t₁)) - s.1 := by omega
                rw [heq', ← Nat.modEq_iff_dvd' h2.le] at hdv; exact hdv.symm
            rw [hm, Nat.mod_eq_of_lt s.isLt]
          refine Finset.mem_biUnion.mpr ⟨j, hj_mem, Finset.mem_inter.mpr ⟨?_, hs⟩⟩
          rw [hs_eq]; exact Finset.mem_insert_self _ _
        · let j := k - (t₁ - t₂)
          have hj_mem : j ∈ Finset.Ico 1 k := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          have hs_eq : s = p₂ j := by
            apply Fin.ext
            dsimp only [p₂, j]
            have hadd : s₀.1 + n + (k - (t₁ - t₂)) - k = s₀.1 + n - (t₁ - t₂) := by omega
            rw [hadd]
            have hm : (s₀.1 + n - (t₁ - t₂)) % n = s.1 % n := by
              have hss₀_lt := s.isLt
              have hs₀_lt := s₀.isLt
              rcases le_or_gt s₀.1 (s.1 + (t₁ - t₂)) with hle_s | hlt_s
              · have h1 : n ∣ (s.1 + (t₁ - t₂)) - s₀.1 := by
                  have hdv1 : n ∣ (s.1 + t₁) - (s₀.1 + t₂) := by
                    rw [← Nat.modEq_iff_dvd' (by omega)]; exact hval
                  have heq' : (s.1 + t₁) - (s₀.1 + t₂) = (s.1 + (t₁ - t₂)) - s₀.1 := by omega
                  rwa [← heq']
                have hlt0 : (s.1 + (t₁ - t₂)) - s₀.1 < 2 * n := by omega
                have hcases : (s.1 + (t₁ - t₂)) - s₀.1 = 0 ∨ (s.1 + (t₁ - t₂)) - s₀.1 = n := by
                  obtain ⟨q, hq⟩ := h1
                  have : q = 0 ∨ q = 1 := by
                    rcases q with _ | _ | q
                    · left; rfl
                    · right; rfl
                    · exfalso; nlinarith
                  rcases this with rfl | rfl <;> omega
                rcases hcases with hc | hc
                · have hsub : s₀.1 + n - (t₁ - t₂) = s.1 + n := by omega
                  rw [hsub, Nat.add_mod_right]
                · have hsub : s₀.1 + n - (t₁ - t₂) = s.1 := by omega
                  rw [hsub]
              · have h2 : n ∣ s₀.1 - (s.1 + (t₁ - t₂)) := by
                  have hdv1 : n ∣ (s₀.1 + t₂) - (s.1 + t₁) := by
                    rw [← Nat.modEq_iff_dvd' (by omega)]; exact hval.symm
                  have heq' : (s₀.1 + t₂) - (s.1 + t₁) = s₀.1 - (s.1 + (t₁ - t₂)) := by omega
                  rwa [← heq']
                have hlt0 : s₀.1 - (s.1 + (t₁ - t₂)) < n := by omega
                have h0 : s₀.1 - (s.1 + (t₁ - t₂)) = 0 := Nat.eq_zero_of_dvd_of_lt h2 hlt0
                have hsub : s₀.1 + n - (t₁ - t₂) = s.1 + n := by omega
                rw [hsub, Nat.add_mod_right]
            rw [hm, Nat.mod_eq_of_lt s.isLt]
          refine Finset.mem_biUnion.mpr ⟨j, hj_mem, Finset.mem_inter.mpr ⟨?_, hs⟩⟩
          rw [hs_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hpair_le : ∀ j ∈ Finset.Ico 1 k, ({p₁ j, p₂ j} ∩ good).card ≤ 1 := by
      intro j hj
      by_contra hgt
      have hgt' : 1 < ({p₁ j, p₂ j} ∩ good).card := Nat.lt_of_not_le hgt
      have hp1 : p₁ j ∈ good := by
        by_contra hnot
        have hsub : ({p₁ j, p₂ j} ∩ good) ⊆ {p₂ j} := fun x hx => by
          rcases Finset.mem_inter.mp hx with ⟨h12, hxg⟩
          rcases Finset.mem_insert.mp h12 with rfl | h2
          · exact absurd hxg hnot
          · exact h2
        have hle := le_trans (Finset.card_le_card hsub) (Finset.card_singleton _).le
        omega
      have hp2 : p₂ j ∈ good := by
        by_contra hnot
        have hsub : ({p₁ j, p₂ j} ∩ good) ⊆ {p₁ j} := fun x hx => by
          rcases Finset.mem_inter.mp hx with ⟨h12, hxg⟩
          rcases Finset.mem_insert.mp h12 with rfl | h2
          · exact Finset.mem_singleton_self _
          · rw [Finset.mem_singleton.mp h2] at hxg; exact absurd hxg hnot
        have hle := le_trans (Finset.card_le_card hsub) (Finset.card_singleton _).le
        omega
      exact hinter _ (Finset.mem_filter.mp hp1).2 _ (Finset.mem_filter.mp hp2).2 (hp_disj j hj)
    have hle_bi : ((Finset.Ico 1 k).biUnion (fun j => ({p₁ j, p₂ j} ∩ good))).card ≤ k - 1 := by
      calc ((Finset.Ico 1 k).biUnion (fun j => ({p₁ j, p₂ j} ∩ good))).card
          ≤ ∑ j ∈ Finset.Ico 1 k, ({p₁ j, p₂ j} ∩ good).card := Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ Finset.Ico 1 k, 1 := Finset.sum_le_sum hpair_le
        _ = (Finset.Ico 1 k).card := by simp
        _ = k - 1 := by simp
    calc good.card
        ≤ (insert s₀ ((Finset.Ico 1 k).biUnion (fun j => ({p₁ j, p₂ j} ∩ good)))).card :=
            Finset.card_le_card hcover
      _ ≤ 1 + ((Finset.Ico 1 k).biUnion (fun j => ({p₁ j, p₂ j} ∩ good))).card := by
            have := Finset.card_insert_le s₀ ((Finset.Ico 1 k).biUnion (fun j => ({p₁ j, p₂ j} ∩ good)))
            omega
      _ ≤ 1 + (k - 1) := by omega
      _ = k := by omega
  · change good.card ≤ k
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le k

/-- Exact count of permutations mapping a fixed cyclic arc starting at `s` onto a `k`-set `A`. -/
private lemma cyclicArc_perm_count {n k : ℕ} (hkn : k ≤ n) (s : Fin n)
    {A : Finset (Fin n)} (hA : A.card = k) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => cyclicArc k σ s = A)).card *
      Nat.choose n k = Nat.factorial n := by
  classical
  let Is : Finset (Fin n) := (Finset.range k).image (fun t => ⟨(s.1 + t) % n, Nat.mod_lt _ (Fin.pos s)⟩)
  have hIs_card : Is.card = k := by
    have hinj : (Finset.range k : Set ℕ).InjOn (fun t => (⟨(s.1 + t) % n, Nat.mod_lt _ (Fin.pos s)⟩ : Fin n)) := by
      intro t₁ ht₁ t₂ ht₂ heq
      have h1 : t₁ < k := Finset.mem_coe.mp ht₁ |> Finset.mem_range.mp
      have h2 : t₂ < k := Finset.mem_coe.mp ht₂ |> Finset.mem_range.mp
      have hv : (s.1 + t₁) % n = (s.1 + t₂) % n := congrArg Fin.val heq
      rcases le_or_gt t₁ t₂ with hle | hlt
      · have hmod : s.1 + t₁ ≡ s.1 + t₂ [MOD n] := hv
        have hd : n ∣ (s.1 + t₂) - (s.1 + t₁) := (Nat.modEq_iff_dvd' (by omega)).mp hmod
        have hsub : (s.1 + t₂) - (s.1 + t₁) = t₂ - t₁ := by omega
        rw [hsub] at hd
        have h0 : t₂ - t₁ = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
        omega
      · have hmod : s.1 + t₂ ≡ s.1 + t₁ [MOD n] := hv.symm
        have hd : n ∣ (s.1 + t₁) - (s.1 + t₂) := (Nat.modEq_iff_dvd' (by omega)).mp hmod
        have hsub : (s.1 + t₁) - (s.1 + t₂) = t₁ - t₂ := by omega
        rw [hsub] at hd
        have h0 : t₁ - t₂ = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
        omega
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have harc_eq : ∀ σ : Equiv.Perm (Fin n), cyclicArc k σ s = Is.image σ := by
    intro σ
    simp only [cyclicArc, Is, Finset.image_image]
    rfl
  let bucket : Finset (Fin n) → Finset (Equiv.Perm (Fin n)) := fun B =>
    Finset.univ.filter (fun σ => Is.image σ = B)
  have hbucket_eq : ∀ B₁ B₂ : Finset (Fin n), B₁.card = k → B₂.card = k →
      (bucket B₁).card = (bucket B₂).card := by
    intro B₁ B₂ hB₁ hB₂
    let e₁ : B₁ ≃ B₂ := Fintype.equivOfCardEq (by simp [hB₁, hB₂])
    let e₂ : ↥(Finset.univ \ B₁) ≃ ↥(Finset.univ \ B₂) := Fintype.equivOfCardEq (by
      rw [Fintype.card_coe, Fintype.card_coe,
        Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_sdiff_of_subset (Finset.subset_univ _), hB₁, hB₂])
    let toFun : Fin n → Fin n := fun x =>
      if hx : x ∈ B₁ then (e₁ ⟨x, hx⟩).1
      else (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩).1
    let invFun : Fin n → Fin n := fun y =>
      if hy : y ∈ B₂ then (e₁.symm ⟨y, hy⟩).1
      else (e₂.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩⟩).1
    have hleft : Function.LeftInverse invFun toFun := by
      intro x; dsimp only [toFun, invFun]
      by_cases hx : x ∈ B₁
      · rw [dif_pos hx, dif_pos (e₁ ⟨x, hx⟩).2]; simp
      · have hy_not : (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩).1 ∉ B₂ :=
          (Finset.mem_sdiff.mp (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩).2).2
        rw [dif_neg hx, dif_neg hy_not]; simp
    have hright : Function.RightInverse invFun toFun := by
      intro y; dsimp only [toFun, invFun]
      by_cases hy : y ∈ B₂
      · rw [dif_pos hy, dif_pos (e₁.symm ⟨y, hy⟩).2]; simp
      · have hx_not : (e₂.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩⟩).1 ∉ B₁ :=
          (Finset.mem_sdiff.mp (e₂.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩⟩).2).2
        rw [dif_neg hy, dif_neg hx_not]; simp
    let φ : Equiv.Perm (Fin n) := ⟨toFun, invFun, hleft, hright⟩
    have hφ_im1 : B₁.image φ = B₂ := by
      ext y; simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        change toFun x ∈ B₂; dsimp only [toFun]; rw [dif_pos hx]; exact (e₁ ⟨x, hx⟩).2
      · intro hy
        refine ⟨invFun y, ?_, hright y⟩
        dsimp only [invFun]; rw [dif_pos hy]; exact (e₁.symm ⟨y, hy⟩).2
    have hφ_im2 : B₂.image φ.symm = B₁ := by
      rw [← hφ_im1, Finset.image_image]
      ext x; simp
    refine Finset.card_bij (fun σ _ => φ * σ) ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [show (Is.image ⇑(φ * σ)) = (Is.image σ).image φ by
        ext y; simp]
      rw [hσ.2, hφ_im1]
    · intro σ₁ _ σ₂ _ h; exact mul_left_cancel h
    · intro σ' hσ'
      refine ⟨φ.symm * σ', ?_, by ext x; simp⟩
      rw [Finset.mem_filter] at hσ' ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [show (Is.image ⇑(φ.symm * σ')) = (Is.image σ').image φ.symm by
        ext y; simp]
      rw [hσ'.2, hφ_im2]
  let powK := (Finset.univ : Finset (Fin n)).powersetCard k
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n))) = powK.biUnion bucket := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_biUnion, powK, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, bucket, Finset.mem_filter, true_iff]
    exact ⟨Is.image σ, Finset.card_image_of_injective Is σ.injective |>.trans hIs_card, rfl⟩
  have hdisj : (powK : Set (Finset (Fin n))).PairwiseDisjoint bucket := by
    intro B₁ _ B₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
  have hfact_card : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hfact : Nat.factorial n = ∑ B ∈ powK, (bucket B).card := by
    rw [← hfact_card, huniv, Finset.card_biUnion hdisj]
  have hconst : ∑ B ∈ powK, (bucket B).card = powK.card * (bucket A).card := by
    calc ∑ B ∈ powK, (bucket B).card
        = ∑ _B ∈ powK, (bucket A).card := by
            refine Finset.sum_congr rfl fun B hB => ?_
            exact hbucket_eq B A (Finset.mem_powersetCard.mp hB).2 hA
      _ = powK.card * (bucket A).card := by
            rw [Finset.sum_const, smul_eq_mul]
  have hpowK_card : powK.card = Nat.choose n k := by
    simp [powK]
  have hfil_eq : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => cyclicArc k σ s = A) = bucket A := by
    ext σ; simp [bucket, harc_eq]
  rw [hfil_eq, ← hpowK_card, mul_comm, ← hconst, ← hfact]

/-- **Erdős–Ko–Rado Theorem (1961)**: for `1 ≤ k` and `2 * k ≤ n`, every intersecting
`k`-uniform family `ℱ : Finset (Finset (Fin n))` satisfies `ℱ.card ≤ Nat.choose (n - 1) (k - 1)`. -/
theorem erdos_ko_rado {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (ℱ : Finset (Finset (Fin n)))
    (hunif : ∀ A ∈ ℱ, A.card = k)
    (hinter : ∀ A ∈ ℱ, ∀ B ∈ ℱ, ¬ Disjoint A B) :
    ℱ.card ≤ Nat.choose (n - 1) (k - 1) := by
  classical
  have hn : 0 < n := by omega
  have hk_le : k ≤ n := by omega
  let pairs : Finset (Equiv.Perm (Fin n) × Fin n) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun p => cyclicArc k p.1 p.2 ∈ ℱ)
  have h_upper : pairs.card ≤ k * Nat.factorial n := by
    have hsplit : pairs.card =
        ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun s : Fin n => cyclicArc k σ s ∈ ℱ)).card := by
      simp only [pairs, Finset.card_filter, Finset.sum_product]
    rw [hsplit]
    calc ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun s : Fin n => cyclicArc k σ s ∈ ℱ)).card
        ≤ ∑ _σ : Equiv.Perm (Fin n), k :=
            Finset.sum_le_sum fun σ _ => katona_cyclic_le hk hkn ℱ hinter σ
      _ = k * Nat.factorial n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
              smul_eq_mul, mul_comm]
  have h_lower : pairs.card * Nat.choose n k = ℱ.card * n * Nat.factorial n := by
    let emb : Fin n → (Equiv.Perm (Fin n) ↪ Equiv.Perm (Fin n) × Fin n) := fun s =>
      ⟨fun σ => (σ, s), fun _ _ h => (Prod.ext_iff.mp h).1⟩
    have hpart : pairs = (ℱ ×ˢ (Finset.univ : Finset (Fin n))).biUnion (fun q =>
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => cyclicArc k σ q.2 = q.1)).map
          (emb q.2)) := by
      ext ⟨σ, s⟩
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · intro hmem
        exact ⟨(cyclicArc k σ s, s), ⟨hmem, trivial⟩, σ, rfl, rfl⟩
      · rintro ⟨⟨A, s'⟩, ⟨hA, _⟩, σ', hσ', hpair⟩
        change (σ', s') = (σ, s) at hpair
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
        dsimp only at hσ' hA
        rw [hσ']; exact hA
    have hdisj : ((ℱ ×ˢ (Finset.univ : Finset (Fin n)) : Finset _) : Set (Finset (Fin n) × Fin n)).PairwiseDisjoint
        (fun q => (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => cyclicArc k σ q.2 = q.1)).map
          (emb q.2)) := by
      intro ⟨A₁, s₁⟩ _ ⟨A₂, s₂⟩ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨σ, s⟩ h1 h2
      rcases Finset.mem_map.mp h1 with ⟨σ₁, hσ₁, hp1⟩
      rcases Finset.mem_map.mp h2 with ⟨σ₂, hσ₂, hp2⟩
      change (σ₁, s₁) = (σ, s) at hp1
      change (σ₂, s₂) = (σ, s) at hp2
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hp1
      obtain ⟨hσeq, hseq⟩ := Prod.ext_iff.mp hp2
      subst hσeq hseq
      have hAeq : A₁ = A₂ := ((Finset.mem_filter.mp hσ₁).2).symm.trans (Finset.mem_filter.mp hσ₂).2
      exact hne (Prod.ext hAeq rfl)
    rw [hpart, Finset.card_biUnion hdisj, Finset.sum_mul]
    calc ∑ q ∈ ℱ ×ˢ (Finset.univ : Finset (Fin n)),
            ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => cyclicArc k σ q.2 = q.1)).map
              (emb q.2)).card * Nat.choose n k
        = ∑ q ∈ ℱ ×ˢ (Finset.univ : Finset (Fin n)),
            (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => cyclicArc k σ q.2 = q.1)).card *
              Nat.choose n k := by
            refine Finset.sum_congr rfl fun q _ => ?_; rw [Finset.card_map]
      _ = ∑ q ∈ ℱ ×ˢ (Finset.univ : Finset (Fin n)), Nat.factorial n := by
            refine Finset.sum_congr rfl fun q hq => ?_
            exact cyclicArc_perm_count hk_le q.2 (hunif q.1 (Finset.mem_product.mp hq).1)
      _ = (ℱ ×ˢ (Finset.univ : Finset (Fin n))).card * Nat.factorial n := by
            rw [Finset.sum_const, smul_eq_mul]
      _ = ℱ.card * n * Nat.factorial n := by
            rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hmul : ℱ.card * n * Nat.factorial n ≤ k * Nat.factorial n * Nat.choose n k := by
    rw [← h_lower]
    exact Nat.mul_le_mul_right _ h_upper
  have hmul2 : ℱ.card * n ≤ k * Nat.choose n k := by
    have hfpos : 0 < Nat.factorial n := Nat.factorial_pos n
    have h1 : (ℱ.card * n) * Nat.factorial n ≤ (k * Nat.choose n k) * Nat.factorial n := by
      linarith
    exact Nat.le_of_mul_le_mul_right h1 hfpos
  have hid : k * Nat.choose n k = n * Nat.choose (n - 1) (k - 1) := by
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simpa [Nat.succ_sub_one] using succ_mul_choose_succ n' k' (by omega)
  rw [hid] at hmul2
  exact Nat.le_of_mul_le_mul_right (by linarith) hn

/-! ### Section 3: Sauer–Shelah–Perles VC-Dimension Lemma (1972) -/

private lemma pascal_sum_range (m d : ℕ) :
    ∑ k ∈ Finset.range (d + 1), Nat.choose m k +
      ∑ k ∈ Finset.range d, Nat.choose m k =
        ∑ k ∈ Finset.range (d + 1), Nat.choose (m + 1) k := by
  induction d with
  | zero => simp
  | succ d ih =>
    linarith [ih, Finset.sum_range_succ (fun k => Nat.choose m k) d,
      Finset.sum_range_succ (fun k => Nat.choose m k) (d + 1),
      Finset.sum_range_succ (fun k => Nat.choose (m + 1) k) (d + 1),
      Nat.choose_succ_succ m d]

private lemma sauer_shelah_finset {α : Type*} [DecidableEq α] :
    ∀ (U : Finset α) (ℱ : Finset (Finset α)) (d : ℕ),
      (∀ A ∈ ℱ, A ⊆ U) →
      (∀ S ⊆ U, d < S.card → ¬ (∀ T ⊆ S, ∃ A ∈ ℱ, A ∩ S = T)) →
      ℱ.card ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose U.card k := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro ℱ d hsub _
    have hF_sub : ℱ ⊆ {∅} := fun A hA =>
      Finset.mem_singleton.mpr (Finset.subset_empty.mp (hsub A hA))
    have hle : ℱ.card ≤ 1 := le_trans (Finset.card_le_card hF_sub) (Finset.card_singleton ∅).le
    have hsum_ge : 1 ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose 0 k := by
      calc 1 = Nat.choose 0 0 := rfl
        _ ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose 0 k :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos d))
    exact le_trans hle hsum_ge
  | @insert x U' hxU' ih =>
    intro ℱ d hsub hno
    let P₀ : Finset (Finset α) := ℱ.filter (fun A => x ∉ A)
    let P₁ : Finset (Finset α) := (ℱ.filter (fun A => x ∈ A)).image (fun A => A.erase x)
    have hP₀_sub : ∀ B ∈ P₀, B ⊆ U' := by
      intro B hB
      rcases Finset.mem_filter.mp hB with ⟨hBF, hxB⟩
      intro y hyB
      rcases Finset.mem_insert.mp (hsub B hBF hyB) with rfl | hyU'
      · exact absurd hyB hxB
      · exact hyU'
    have hP₁_sub : ∀ B ∈ P₁, B ⊆ U' := by
      intro B hB
      rcases Finset.mem_image.mp hB with ⟨A, hAF, rfl⟩
      rcases Finset.mem_filter.mp hAF with ⟨hAF', _⟩
      intro y hy
      rcases Finset.mem_erase.mp hy with ⟨hyx, hyA⟩
      rcases Finset.mem_insert.mp (hsub A hAF' hyA) with rfl | hyU'
      · exact absurd rfl hyx
      · exact hyU'
    have hP₁_card : P₁.card = (ℱ.filter (fun A => x ∈ A)).card := by
      refine Finset.card_image_of_injOn fun A₁ h1 A₂ h2 heq => ?_
      have hx1 : x ∈ A₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
      have hx2 : x ∈ A₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
      rw [← Finset.insert_erase hx1, ← Finset.insert_erase hx2, heq]
    have hF_card : ℱ.card = P₀.card + P₁.card := by
      rw [hP₁_card, add_comm]
      exact (Finset.card_filter_add_card_filter_not (s := ℱ) (p := fun A => x ∈ A)).symm
    let ℱ₀ := P₀ ∪ P₁
    let ℱ₁ := P₀ ∩ P₁
    have hsum_card : ℱ.card = ℱ₀.card + ℱ₁.card := by
      rw [hF_card, ← Finset.card_union_add_card_inter]
    have hℱ₀_sub : ∀ B ∈ ℱ₀, B ⊆ U' := fun B hB => by
      rcases Finset.mem_union.mp hB with h0 | h1
      · exact hP₀_sub B h0
      · exact hP₁_sub B h1
    have hℱ₀_no : ∀ S ⊆ U', d < S.card → ¬ (∀ T ⊆ S, ∃ B ∈ ℱ₀, B ∩ S = T) := by
      intro S hSU' hdS hshat
      refine hno S (hSU'.trans (Finset.subset_insert x U')) hdS fun T hTS => ?_
      obtain ⟨B, hB, hBT⟩ := hshat T hTS
      rcases Finset.mem_union.mp hB with h0 | h1
      · exact ⟨B, (Finset.mem_filter.mp h0).1, hBT⟩
      · rcases Finset.mem_image.mp h1 with ⟨A, hAF, rfl⟩
        have hxS : x ∉ S := fun hx => hxU' (hSU' hx)
        refine ⟨A, (Finset.mem_filter.mp hAF).1, ?_⟩
        rw [← hBT]
        ext y
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨hyA, hyS⟩
          exact ⟨⟨fun heq => by subst heq; exact hxS hyS, hyA⟩, hyS⟩
        · rintro ⟨⟨_, hyA⟩, hyS⟩
          exact ⟨hyA, hyS⟩
    have hbd₀ : ℱ₀.card ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose U'.card k :=
      ih ℱ₀ d hℱ₀_sub hℱ₀_no
    rw [Finset.card_insert_of_notMem hxU']
    cases d with
    | zero =>
      have hℱ₁_empty : ℱ₁ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro B hB
        rcases Finset.mem_inter.mp hB with ⟨h0, h1⟩
        have hBF : B ∈ ℱ := (Finset.mem_filter.mp h0).1
        have hxB : x ∉ B := (Finset.mem_filter.mp h0).2
        rcases Finset.mem_image.mp h1 with ⟨A, hAF, hAB⟩
        have hAF' : A ∈ ℱ := (Finset.mem_filter.mp hAF).1
        have hxA : x ∈ A := (Finset.mem_filter.mp hAF).2
        refine hno {x} (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self x U'))
          (by simp) fun T hTx => ?_
        rcases Finset.subset_singleton_iff.mp hTx with rfl | rfl
        · refine ⟨B, hBF, ?_⟩
          exact Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_singleton_right.mpr hxB)
        · refine ⟨A, hAF', ?_⟩
          ext y
          simp only [Finset.mem_inter, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => by subst h; exact ⟨hxA, rfl⟩⟩
      rw [hℱ₁_empty, Finset.card_empty, add_zero] at hsum_card
      simpa using le_trans hsum_card.le hbd₀
    | succ d' =>
      have hℱ₁_sub : ∀ B ∈ ℱ₁, B ⊆ U' := fun B hB =>
        hP₀_sub B (Finset.mem_inter.mp hB).1
      have hℱ₁_no : ∀ S ⊆ U', d' < S.card → ¬ (∀ T ⊆ S, ∃ B ∈ ℱ₁, B ∩ S = T) := by
        intro S hSU' hdS hshat
        have hxS : x ∉ S := fun hx => hxU' (hSU' hx)
        refine hno (insert x S) (Finset.insert_subset (Finset.mem_insert_self x U')
          (hSU'.trans (Finset.subset_insert x U'))) ?_ ?_
        · rw [Finset.card_insert_of_notMem hxS]; omega
        · intro T hTxS
          let T' := T.erase x
          have hT'S : T' ⊆ S := by
            intro y hy
            rcases Finset.mem_erase.mp hy with ⟨hyx, hyT⟩
            rcases Finset.mem_insert.mp (hTxS hyT) with rfl | hyS
            · exact absurd rfl hyx
            · exact hyS
          obtain ⟨B, hB, hBT'⟩ := hshat T' hT'S
          rcases Finset.mem_inter.mp hB with ⟨h0, h1⟩
          have hBF : B ∈ ℱ := (Finset.mem_filter.mp h0).1
          have hxB : x ∉ B := (Finset.mem_filter.mp h0).2
          rcases Finset.mem_image.mp h1 with ⟨A, hAF, hAB⟩
          have hAF' : A ∈ ℱ := (Finset.mem_filter.mp hAF).1
          have hxA : x ∈ A := (Finset.mem_filter.mp hAF).2
          by_cases hxT : x ∈ T
          · refine ⟨A, hAF', ?_⟩
            ext y
            simp only [Finset.mem_inter, Finset.mem_insert]
            constructor
            · rintro ⟨hyA, rfl | hyS⟩
              · exact hxT
              · have hyB : y ∈ B := by
                  rw [← hAB]
                  exact Finset.mem_erase.mpr ⟨fun heq => by subst heq; exact hxS hyS, hyA⟩
                have hyT' : y ∈ T' := by rw [← hBT']; exact Finset.mem_inter.mpr ⟨hyB, hyS⟩
                exact (Finset.mem_erase.mp hyT').2
            · intro hyT
              by_cases hyx : y = x
              · subst hyx; exact ⟨hxA, Or.inl rfl⟩
              · have hyT' : y ∈ T' := Finset.mem_erase.mpr ⟨hyx, hyT⟩
                rw [← hBT'] at hyT'
                rcases Finset.mem_inter.mp hyT' with ⟨hyB, hyS⟩
                rw [← hAB] at hyB
                exact ⟨(Finset.mem_erase.mp hyB).2, Or.inr hyS⟩
          · refine ⟨B, hBF, ?_⟩
            have hTT' : T = T' := (Finset.erase_eq_of_notMem hxT).symm
            rw [hTT', ← hBT']
            ext y
            simp only [Finset.mem_inter, Finset.mem_insert]
            constructor
            · rintro ⟨hyB, rfl | hyS⟩
              · exact absurd hyB hxB
              · exact ⟨hyB, hyS⟩
            · rintro ⟨hyB, hyS⟩
              exact ⟨hyB, Or.inr hyS⟩
      have hbd₁ : ℱ₁.card ≤ ∑ k ∈ Finset.range (d' + 1), Nat.choose U'.card k :=
        ih ℱ₁ d' hℱ₁_sub hℱ₁_no
      rw [hsum_card, ← pascal_sum_range U'.card (d' + 1)]
      exact Nat.add_le_add hbd₀ hbd₁

/-- **Sauer–Shelah–Perles Lemma (1972)**: if `ℱ : Finset (Finset (Fin n))` shatters no subset of
size `> d`, then `ℱ.card ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose n k`. -/
theorem sauer_shelah {n d : ℕ} (ℱ : Finset (Finset (Fin n)))
    (hno : ∀ S : Finset (Fin n), d < S.card →
      ¬ (∀ T ⊆ S, ∃ A ∈ ℱ, A ∩ S = T)) :
    ℱ.card ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose n k := by
  have h := sauer_shelah_finset (Finset.univ : Finset (Fin n)) ℱ d
    (fun A _ => Finset.subset_univ A) (fun S _ hdS => hno S hdS)
  simpa using h

/-! ### Section 4: Ahlswede–Daykin Four-Functions Theorem (1978) -/

private lemma daykin_four_numbers {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (h00 : a₀ * b₀ ≤ c₀ * d₀) (h11 : a₁ * b₁ ≤ c₁ * d₁)
    (h01 : a₀ * b₁ ≤ c₁ * d₀) (h10 : a₁ * b₀ ≤ c₁ * d₀) :
    (a₀ + a₁) * (b₀ + b₁) ≤ (c₀ + c₁) * (d₀ + d₁) := by
  by_cases hcd : c₁ * d₀ = 0
  · have h01' : a₀ * b₁ = 0 := le_antisymm (h01.trans hcd.le) (mul_nonneg ha₀ hb₁)
    have h10' : a₁ * b₀ = 0 := le_antisymm (h10.trans hcd.le) (mul_nonneg ha₁ hb₀)
    rcases mul_eq_zero.mp h01' with rfl | rfl <;> rcases mul_eq_zero.mp h10' with rfl | rfl
    · simp; positivity
    · simp; nlinarith [mul_nonneg ha₁ hd₀, mul_nonneg hc₁ hb₁]
    · simp; nlinarith [mul_nonneg hc₀ hd₁, mul_nonneg ha₁ hb₀]
    · simp; nlinarith [mul_nonneg hc₀ hd₁, mul_nonneg hc₁ hd₀]
  · have hpos : 0 < c₁ * d₀ := lt_of_le_of_ne (mul_nonneg hc₁ hd₀) (Ne.symm hcd)
    have hid : c₁ * d₀ * ((c₀ + c₁) * (d₀ + d₁) - (a₀ + a₁) * (b₀ + b₁)) =
        c₁ * d₀ * (c₀ * d₀ - a₀ * b₀) + c₁ * d₀ * (c₁ * d₁ - a₁ * b₁) +
          (c₁ * d₀ - a₀ * b₁) * (c₁ * d₀ - a₁ * b₀) +
          (c₀ * d₀ * (c₁ * d₁) - a₀ * b₀ * (a₁ * b₁)) := by ring
    have h1 : 0 ≤ c₁ * d₀ * (c₀ * d₀ - a₀ * b₀) := mul_nonneg hpos.le (sub_nonneg.mpr h00)
    have h2 : 0 ≤ c₁ * d₀ * (c₁ * d₁ - a₁ * b₁) := mul_nonneg hpos.le (sub_nonneg.mpr h11)
    have h3 : 0 ≤ (c₁ * d₀ - a₀ * b₁) * (c₁ * d₀ - a₁ * b₀) :=
      mul_nonneg (sub_nonneg.mpr h01) (sub_nonneg.mpr h10)
    have h4 : 0 ≤ c₀ * d₀ * (c₁ * d₁) - a₀ * b₀ * (a₁ * b₁) :=
      sub_nonneg.mpr (mul_le_mul h00 h11 (mul_nonneg ha₁ hb₁) (mul_nonneg hc₀ hd₀))
    have hprod : 0 ≤ c₁ * d₀ * ((c₀ + c₁) * (d₀ + d₁) - (a₀ + a₁) * (b₀ + b₁)) := by linarith
    have hsub : 0 ≤ (c₀ + c₁) * (d₀ + d₁) - (a₀ + a₁) * (b₀ + b₁) :=
      nonneg_of_mul_nonneg_right hprod hpos
    linarith

private def finSuccEmb (n : ℕ) : Fin n ↪ Fin (n + 1) :=
  ⟨Fin.succ, @Fin.succ_injective n⟩

@[simp] private lemma finSuccEmb_apply (n : ℕ) (i : Fin n) :
    finSuccEmb n i = i.succ := rfl

private lemma finset_succ_sum_split {n : ℕ} (f : Finset (Fin (n + 1)) → ℝ) :
    ∑ A : Finset (Fin (n + 1)), f A =
      ∑ S : Finset (Fin n),
        (f (S.map (finSuccEmb n)) + f (insert 0 (S.map (finSuccEmb n)))) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin (n + 1)))) (fun A => (0 : Fin (n + 1)) ∈ A) f
  rw [← hsplit, add_comm]
  conv_rhs => rw [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_bij (fun A _ => (Finset.univ : Finset (Fin n)).filter (fun i => i.succ ∈ A))
      ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro A₁ h1 A₂ h2 heq
      have h1' : (0 : Fin (n + 1)) ∉ A₁ := (Finset.mem_filter.mp h1).2
      have h2' : (0 : Fin (n + 1)) ∉ A₂ := (Finset.mem_filter.mp h2).2
      ext x
      refine Fin.cases ?_ ?_ x
      · simp [h1', h2']
      · intro i
        have hi := Finset.ext_iff.mp heq i
        simpa using hi
    · intro S _
      refine ⟨S.map (finSuccEmb n), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, ?_⟩
      ext i; simp
    · intro A hA
      have hA0 : (0 : Fin (n + 1)) ∉ A := (Finset.mem_filter.mp hA).2
      congr 1
      ext x
      refine Fin.cases ?_ ?_ x
      · simp [hA0]
      · intro i; simp
  · refine Finset.sum_bij (fun A _ => (Finset.univ : Finset (Fin n)).filter (fun i => i.succ ∈ A))
      ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro A₁ h1 A₂ h2 heq
      have h1' : (0 : Fin (n + 1)) ∈ A₁ := (Finset.mem_filter.mp h1).2
      have h2' : (0 : Fin (n + 1)) ∈ A₂ := (Finset.mem_filter.mp h2).2
      ext x
      refine Fin.cases ?_ ?_ x
      · simp [h1', h2']
      · intro i
        have hi := Finset.ext_iff.mp heq i
        simpa using hi
    · intro S _
      refine ⟨insert 0 (S.map (finSuccEmb n)),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self _ _⟩, ?_⟩
      ext i; simp [Fin.succ_ne_zero]
    · intro A hA
      have hA0 : (0 : Fin (n + 1)) ∈ A := (Finset.mem_filter.mp hA).2
      congr 1
      ext x
      refine Fin.cases ?_ ?_ x
      · simp [hA0]
      · intro i; simp [Fin.succ_ne_zero]

/-- **Ahlswede–Daykin Four-Functions Theorem (1978)**: if nonnegative functions `α, β, γ, δ` on
`Finset (Fin n)` satisfy `α A * β B ≤ γ (A ∪ B) * δ (A ∩ B)` for all `A, B`, then
`(∑ A, α A) * (∑ B, β B) ≤ (∑ C, γ C) * (∑ D, δ D)`. -/
theorem ahlswede_daykin_four_functions {n : ℕ}
    (α β γ δ : Finset (Fin n) → ℝ)
    (hα : ∀ A, 0 ≤ α A) (hβ : ∀ B, 0 ≤ β B)
    (hγ : ∀ C, 0 ≤ γ C) (hδ : ∀ D, 0 ≤ δ D)
    (hcond : ∀ A B, α A * β B ≤ γ (A ∪ B) * δ (A ∩ B)) :
    (∑ A : Finset (Fin n), α A) * (∑ B : Finset (Fin n), β B) ≤
      (∑ C : Finset (Fin n), γ C) * (∑ D : Finset (Fin n), δ D) := by
  induction n with
  | zero =>
    have huniv : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
      ext A
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Finset.eq_empty_of_isEmpty A
    simp only [huniv, Finset.sum_singleton]
    exact hcond ∅ ∅
  | succ n ih =>
    let α' : Finset (Fin n) → ℝ := fun S =>
      α (S.map (finSuccEmb n)) + α (insert 0 (S.map (finSuccEmb n)))
    let β' : Finset (Fin n) → ℝ := fun S =>
      β (S.map (finSuccEmb n)) + β (insert 0 (S.map (finSuccEmb n)))
    let γ' : Finset (Fin n) → ℝ := fun S =>
      γ (S.map (finSuccEmb n)) + γ (insert 0 (S.map (finSuccEmb n)))
    let δ' : Finset (Fin n) → ℝ := fun S =>
      δ (S.map (finSuccEmb n)) + δ (insert 0 (S.map (finSuccEmb n)))
    have hcond' : ∀ A B : Finset (Fin n), α' A * β' B ≤ γ' (A ∪ B) * δ' (A ∩ B) := by
      intro A B
      have h00 := hcond (A.map (finSuccEmb n)) (B.map (finSuccEmb n))
      have h11 := hcond (insert 0 (A.map (finSuccEmb n))) (insert 0 (B.map (finSuccEmb n)))
      have h01 := hcond (A.map (finSuccEmb n)) (insert 0 (B.map (finSuccEmb n)))
      have h10 := hcond (insert 0 (A.map (finSuccEmb n))) (B.map (finSuccEmb n))
      have hun : A.map (finSuccEmb n) ∪ B.map (finSuccEmb n) = (A ∪ B).map (finSuccEmb n) := by
        rw [Finset.map_union]
      have hin : A.map (finSuccEmb n) ∩ B.map (finSuccEmb n) = (A ∩ B).map (finSuccEmb n) := by
        rw [Finset.map_inter]
      have h11_un : insert 0 (A.map (finSuccEmb n)) ∪ insert 0 (B.map (finSuccEmb n)) =
          insert 0 ((A ∪ B).map (finSuccEmb n)) := by
        rw [← hun]; ext x; simp [or_comm]
      have h11_in : insert 0 (A.map (finSuccEmb n)) ∩ insert 0 (B.map (finSuccEmb n)) =
          insert 0 ((A ∩ B).map (finSuccEmb n)) := by
        rw [← hin]; ext x; simp
      have h01_un : A.map (finSuccEmb n) ∪ insert 0 (B.map (finSuccEmb n)) =
          insert 0 ((A ∪ B).map (finSuccEmb n)) := by
        rw [← hun]; ext x; simp
      have h01_in : A.map (finSuccEmb n) ∩ insert 0 (B.map (finSuccEmb n)) =
          (A ∩ B).map (finSuccEmb n) := by
        rw [← hin]; ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_map, finSuccEmb_apply]
        constructor
        · rintro ⟨⟨i, hi, rfl⟩, hne | hB⟩
          · exact absurd hne (Fin.succ_ne_zero i)
          · exact ⟨⟨i, hi, rfl⟩, hB⟩
        · rintro ⟨hA, hB⟩; exact ⟨hA, Or.inr hB⟩
      have h10_un : insert 0 (A.map (finSuccEmb n)) ∪ B.map (finSuccEmb n) =
          insert 0 ((A ∪ B).map (finSuccEmb n)) := by
        rw [← hun]; ext x; simp
      have h10_in : insert 0 (A.map (finSuccEmb n)) ∩ B.map (finSuccEmb n) =
          (A ∩ B).map (finSuccEmb n) := by
        rw [← hin]; ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_map, finSuccEmb_apply]
        constructor
        · rintro ⟨hne | hA, ⟨i, hi, rfl⟩⟩
          · exact absurd hne (Fin.succ_ne_zero i)
          · exact ⟨hA, ⟨i, hi, rfl⟩⟩
        · rintro ⟨hA, hB⟩; exact ⟨Or.inr hA, hB⟩
      rw [hun, hin] at h00
      rw [h11_un, h11_in] at h11
      rw [h01_un, h01_in] at h01
      rw [h10_un, h10_in] at h10
      exact daykin_four_numbers (hα _) (hα _) (hβ _) (hβ _) (hγ _) (hγ _) (hδ _) (hδ _)
        h00 h11 h01 h10
    have hIH := ih α' β' γ' δ'
      (fun S => add_nonneg (hα _) (hα _)) (fun S => add_nonneg (hβ _) (hβ _))
      (fun S => add_nonneg (hγ _) (hγ _)) (fun S => add_nonneg (hδ _) (hδ _)) hcond'
    simpa only [finset_succ_sum_split] using hIH

/-! ### Section 5: Harris–Kleitman–FKG Correlation & Marica–Schönheim -/

private lemma prod_measure_sum_one {n : ℕ} (p : Fin n → ℝ) :
    ∑ A : Finset (Fin n),
      ((∏ i ∈ A, p i) * ∏ i ∈ Finset.univ \ A, (1 - p i)) = 1 := by
  have h1 : ∏ i : Fin n, (p i + (1 - p i)) = (1 : ℝ) := by
    simp [Finset.prod_const_one]
  calc ∑ A : Finset (Fin n), (∏ i ∈ A, p i) * ∏ i ∈ Finset.univ \ A, (1 - p i)
      = ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
          (∏ i ∈ t, p i) * ∏ i ∈ Finset.univ \ t, (1 - p i) := by
          refine Finset.sum_bij (fun A _ => A)
            (fun _ _ => Finset.mem_powerset.mpr (Finset.subset_univ _))
            (fun _ _ _ _ h => h) (fun A _ => ⟨A, Finset.mem_univ _, rfl⟩) ?_
          intro _ _; rfl
    _ = ∏ i : Fin n, (p i + (1 - p i)) :=
          (Finset.prod_add p (fun i => 1 - p i) (Finset.univ : Finset (Fin n))).symm
    _ = 1 := h1

private lemma prod_measure_mul {n : ℕ} (p : Fin n → ℝ) (A B : Finset (Fin n)) :
    ((∏ i ∈ A, p i) * ∏ i ∈ Finset.univ \ A, (1 - p i)) *
      ((∏ i ∈ B, p i) * ∏ i ∈ Finset.univ \ B, (1 - p i)) =
    ((∏ i ∈ A ∪ B, p i) * ∏ i ∈ Finset.univ \ (A ∪ B), (1 - p i)) *
      ((∏ i ∈ A ∩ B, p i) * ∏ i ∈ Finset.univ \ (A ∩ B), (1 - p i)) := by
  let fA : Fin n → ℝ := fun i => if i ∈ A then p i else 1 - p i
  let fB : Fin n → ℝ := fun i => if i ∈ B then p i else 1 - p i
  let fU : Fin n → ℝ := fun i => if i ∈ A ∪ B then p i else 1 - p i
  let fI : Fin n → ℝ := fun i => if i ∈ A ∩ B then p i else 1 - p i
  have hrew : ∀ S : Finset (Fin n),
      (∏ i ∈ S, p i) * ∏ i ∈ Finset.univ \ S, (1 - p i) =
        ∏ i : Fin n, (if i ∈ S then p i else 1 - p i) := by
    intro S
    rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (p := fun i => i ∈ S)
      (f := fun i => if i ∈ S then p i else 1 - p i)]
    congr 1
    · rw [show Finset.univ.filter (fun i => i ∈ S) = S by ext x; simp]
      refine Finset.prod_congr rfl fun i hi => by simp [hi]
    · rw [show Finset.univ.filter (fun i => i ∉ S) = Finset.univ \ S by ext x; simp]
      refine Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_sdiff.mp hi).2]
  rw [hrew A, hrew B, hrew (A ∪ B), hrew (A ∩ B), ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> (simp [hiA, hiB]; try ring)

/-- **Harris–Kleitman–FKG Correlation Inequality**: for any product measure on `𝒫(Fin n)` with
marginals `0 ≤ p i ≤ 1` and any nonnegative monotone functions `f, g : Finset (Fin n) → ℝ`,
`𝔼[f] * 𝔼[g] ≤ 𝔼[f * g]`. -/
theorem harris_kleitman_fkg {n : ℕ} (p : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (f g : Finset (Fin n) → ℝ)
    (hf_nonneg : ∀ A, 0 ≤ f A) (hg_nonneg : ∀ A, 0 ≤ g A)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    (∑ A : Finset (Fin n), f A * ((∏ i ∈ A, p i) * ∏ i ∈ Finset.univ \ A, (1 - p i))) *
      (∑ B : Finset (Fin n), g B * ((∏ i ∈ B, p i) * ∏ i ∈ Finset.univ \ B, (1 - p i))) ≤
    ∑ A : Finset (Fin n), f A * g A * ((∏ i ∈ A, p i) * ∏ i ∈ Finset.univ \ A, (1 - p i)) := by
  let μ : Finset (Fin n) → ℝ := fun A =>
    (∏ i ∈ A, p i) * ∏ i ∈ Finset.univ \ A, (1 - p i)
  have hμ_nonneg : ∀ A, 0 ≤ μ A := fun A =>
    mul_nonneg (Finset.prod_nonneg fun i _ => hp0 i)
      (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hp1 i))
  have had := ahlswede_daykin_four_functions
    (fun A => f A * μ A) (fun B => g B * μ B) (fun C => f C * g C * μ C) μ
    (fun A => mul_nonneg (hf_nonneg A) (hμ_nonneg A))
    (fun B => mul_nonneg (hg_nonneg B) (hμ_nonneg B))
    (fun C => mul_nonneg (mul_nonneg (hf_nonneg C) (hg_nonneg C)) (hμ_nonneg C))
    hμ_nonneg
    (fun A B => by
      have hfAB : f A ≤ f (A ∪ B) := hf_mono Finset.subset_union_left
      have hgAB : g B ≤ g (A ∪ B) := hg_mono Finset.subset_union_right
      have hfg : f A * g B ≤ f (A ∪ B) * g (A ∪ B) :=
        mul_le_mul hfAB hgAB (hg_nonneg B) (hf_nonneg (A ∪ B))
      have hμeq : μ A * μ B = μ (A ∪ B) * μ (A ∩ B) := prod_measure_mul p A B
      calc (f A * μ A) * (g B * μ B)
          = (f A * g B) * (μ A * μ B) := by ring
        _ = (f A * g B) * (μ (A ∪ B) * μ (A ∩ B)) := by rw [hμeq]
        _ ≤ (f (A ∪ B) * g (A ∪ B)) * (μ (A ∪ B) * μ (A ∩ B)) :=
            mul_le_mul_of_nonneg_right hfg (mul_nonneg (hμ_nonneg _) (hμ_nonneg _))
        _ = (f (A ∪ B) * g (A ∪ B) * μ (A ∪ B)) * μ (A ∩ B) := by ring)
  have hμ1 : ∑ D : Finset (Fin n), μ D = 1 := prod_measure_sum_one p
  rw [hμ1, mul_one] at had
  exact had

/-- **Harris–Kleitman Counting Correlation for Up-Sets (1960/1966)**: if `𝒰, 𝒱` are upward-closed
families in `𝒫(Fin n)`, then `𝒰.card * 𝒱.card ≤ 2 ^ n * (𝒰 ∩ 𝒱).card`. -/
theorem harris_kleitman_upsets {n : ℕ} (𝒰 𝒱 : Finset (Finset (Fin n)))
    (h𝒰 : ∀ A ∈ 𝒰, ∀ B, A ⊆ B → B ∈ 𝒰)
    (h𝒱 : ∀ A ∈ 𝒱, ∀ B, A ⊆ B → B ∈ 𝒱) :
    𝒰.card * 𝒱.card ≤ 2 ^ n * (𝒰 ∩ 𝒱).card := by
  classical
  have had := ahlswede_daykin_four_functions
    (fun A => if A ∈ 𝒰 then (1 : ℝ) else 0)
    (fun B => if B ∈ 𝒱 then (1 : ℝ) else 0)
    (fun C => if C ∈ 𝒰 ∩ 𝒱 then (1 : ℝ) else 0)
    (fun _ => (1 : ℝ))
    (fun A => by split_ifs <;> norm_num)
    (fun B => by split_ifs <;> norm_num)
    (fun C => by split_ifs <;> norm_num)
    (fun _ => zero_le_one)
    (fun A B => by
      by_cases hA : A ∈ 𝒰 <;> by_cases hB : B ∈ 𝒱
      · have hAB : A ∪ B ∈ 𝒰 ∩ 𝒱 := Finset.mem_inter.mpr
          ⟨h𝒰 A hA (A ∪ B) Finset.subset_union_left, h𝒱 B hB (A ∪ B) Finset.subset_union_right⟩
        simp [hA, hB, hAB]
      · simp [hA, hB]; split_ifs <;> norm_num
      · simp [hA, hB]; split_ifs <;> norm_num
      · simp [hA, hB]; split_ifs <;> norm_num)
  have hcard : ∀ S : Finset (Finset (Fin n)),
      ∑ A : Finset (Fin n), (if A ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
    intro S
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2n : ∑ _D : Finset (Fin n), (1 : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    simp [Fintype.card_finset]
  rw [hcard 𝒰, hcard 𝒱, hcard (𝒰 ∩ 𝒱), h2n] at had
  rw [mul_comm ((𝒰 ∩ 𝒱).card : ℝ)] at had
  exact_mod_cast had

/-- **Kleitman's Down-Down Correlation Inequality (1966)**: if `𝒜, ℬ` are downward-closed
families in `𝒫(Fin n)`, then `𝒜.card * ℬ.card ≤ 2 ^ n * (𝒜 ∩ ℬ).card`. -/
theorem kleitman_down_down {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n)))
    (h𝒜 : ∀ A ∈ 𝒜, ∀ B, B ⊆ A → B ∈ 𝒜)
    (hℬ : ∀ A ∈ ℬ, ∀ B, B ⊆ A → B ∈ ℬ) :
    𝒜.card * ℬ.card ≤ 2 ^ n * (𝒜 ∩ ℬ).card := by
  classical
  have had := ahlswede_daykin_four_functions
    (fun A => if A ∈ 𝒜 then (1 : ℝ) else 0)
    (fun B => if B ∈ ℬ then (1 : ℝ) else 0)
    (fun _ => (1 : ℝ))
    (fun D => if D ∈ 𝒜 ∩ ℬ then (1 : ℝ) else 0)
    (fun A => by split_ifs <;> norm_num)
    (fun B => by split_ifs <;> norm_num)
    (fun _ => zero_le_one)
    (fun D => by split_ifs <;> norm_num)
    (fun A B => by
      by_cases hA : A ∈ 𝒜 <;> by_cases hB : B ∈ ℬ
      · have hAB : A ∩ B ∈ 𝒜 ∩ ℬ := Finset.mem_inter.mpr
          ⟨h𝒜 A hA (A ∩ B) Finset.inter_subset_left, hℬ B hB (A ∩ B) Finset.inter_subset_right⟩
        simp [hA, hB, hAB]
      · simp [hA, hB]; split_ifs <;> norm_num
      · simp [hA, hB]; split_ifs <;> norm_num
      · simp [hA, hB]; split_ifs <;> norm_num)
  have hcard : ∀ S : Finset (Finset (Fin n)),
      ∑ A : Finset (Fin n), (if A ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
    intro S
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2n : ∑ _C : Finset (Fin n), (1 : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    simp [Fintype.card_finset]
  rw [hcard 𝒜, hcard ℬ, h2n, hcard (𝒜 ∩ ℬ)] at had
  exact_mod_cast had

/-- **Marica–Schönheim Theorem (1969)**: for any family `𝒜 : Finset (Finset (Fin n))`,
the difference family `{A \ B | A, B ∈ 𝒜}` has cardinality at least `𝒜.card`. -/
theorem marica_schonheim {n : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    𝒜.card ≤ ((𝒜 ×ˢ 𝒜).image (fun p => p.1 \ p.2)).card := by
  classical
  induction n with
  | zero =>
    by_cases hne : 𝒜.Nonempty
    · obtain ⟨A, hA⟩ := hne
      have hmem : A \ A ∈ (𝒜 ×ˢ 𝒜).image (fun p => p.1 \ p.2) :=
        Finset.mem_image.mpr ⟨(A, A), Finset.mem_product.mpr ⟨hA, hA⟩, rfl⟩
      have h1 : 1 ≤ ((𝒜 ×ˢ 𝒜).image (fun p => p.1 \ p.2)).card := Finset.one_le_card.mpr ⟨_, hmem⟩
      have hsub : 𝒜 ⊆ {∅} := fun B _ => Finset.mem_singleton.mpr (Finset.subset_empty.mp (Finset.subset_univ B))
      have hle : 𝒜.card ≤ 1 := le_trans (Finset.card_le_card hsub) (Finset.card_singleton ∅).le
      exact le_trans hle h1
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  | succ n ih =>
    let proj0 : Finset (Finset (Fin (n + 1))) → Finset (Finset (Fin n)) := fun ℱ =>
      (ℱ.filter (fun A => (0 : Fin (n + 1)) ∉ A)).image
        (fun A => (Finset.univ : Finset (Fin n)).filter (fun i => i.succ ∈ A))
    let proj1 : Finset (Finset (Fin (n + 1))) → Finset (Finset (Fin n)) := fun ℱ =>
      (ℱ.filter (fun A => (0 : Fin (n + 1)) ∈ A)).image
        (fun A => (Finset.univ : Finset (Fin n)).filter (fun i => i.succ ∈ A))
    have hproj0_mem : ∀ ℱ (S : Finset (Fin n)), S ∈ proj0 ℱ ↔ S.map (finSuccEmb n) ∈ ℱ := by
      intro ℱ S
      simp only [proj0, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨A, ⟨hA, hA0⟩, rfl⟩
        convert hA using 1
        ext x
        refine Fin.cases ?_ ?_ x
        · simp [hA0]
        · intro i; simp
      · intro hS
        refine ⟨S.map (finSuccEmb n), ⟨hS, by simp⟩, ?_⟩
        ext i; simp
    have hproj1_mem : ∀ ℱ (S : Finset (Fin n)),
        S ∈ proj1 ℱ ↔ insert 0 (S.map (finSuccEmb n)) ∈ ℱ := by
      intro ℱ S
      simp only [proj1, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨A, ⟨hA, hA0⟩, rfl⟩
        convert hA using 1
        ext x
        refine Fin.cases ?_ ?_ x
        · simp [hA0]
        · intro i; simp [Fin.succ_ne_zero]
      · intro hS
        refine ⟨insert 0 (S.map (finSuccEmb n)), ⟨hS, Finset.mem_insert_self _ _⟩, ?_⟩
        ext i; simp [Fin.succ_ne_zero]
    have hsplit_card : ∀ ℱ : Finset (Finset (Fin (n + 1))),
        ℱ.card = (proj0 ℱ).card + (proj1 ℱ).card := by
      intro ℱ
      rw [← Finset.card_filter_add_card_filter_not (s := ℱ) (p := fun A => (0 : Fin (n + 1)) ∉ A)]
      congr 1
      · refine (Finset.card_image_of_injOn fun A₁ h1 A₂ h2 heq => ?_).symm
        have h1' : (0 : Fin (n + 1)) ∉ A₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
        have h2' : (0 : Fin (n + 1)) ∉ A₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
        ext x
        refine Fin.cases ?_ ?_ x
        · simp [h1', h2']
        · intro i; have := Finset.ext_iff.mp heq i; simpa using this
      · have hnot : ℱ.filter (fun A => ¬ ((0 : Fin (n + 1)) ∉ A)) =
            ℱ.filter (fun A => (0 : Fin (n + 1)) ∈ A) := by
          ext A; simp
        rw [hnot]
        refine (Finset.card_image_of_injOn fun A₁ h1 A₂ h2 heq => ?_).symm
        have h1' : (0 : Fin (n + 1)) ∈ A₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
        have h2' : (0 : Fin (n + 1)) ∈ A₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
        ext x
        refine Fin.cases ?_ ?_ x
        · simp [h1', h2']
        · intro i
          have := Finset.ext_iff.mp heq i
          simpa using this
    let 𝒜₀ := proj0 𝒜
    let 𝒜₁ := proj1 𝒜
    let 𝒟 := (𝒜 ×ˢ 𝒜).image (fun p => p.1 \ p.2)
    let 𝒟₀ := proj0 𝒟
    let 𝒟₁ := proj1 𝒟
    have hsdiff_10 : ∀ S₁ S₂ : Finset (Fin n),
        insert 0 (S₁.map (finSuccEmb n)) \ S₂.map (finSuccEmb n) =
          insert 0 ((S₁ \ S₂).map (finSuccEmb n)) := by
      intro S₁ S₂; ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_map, finSuccEmb_apply]
      constructor
      · rintro ⟨rfl | ⟨i, hi, rfl⟩, hnot⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨i, ⟨hi, fun h => hnot ⟨i, h, rfl⟩⟩, rfl⟩
      · rintro (rfl | ⟨i, ⟨hi1, hi2⟩, rfl⟩)
        · exact ⟨Or.inl rfl, by rintro ⟨i, _, hi⟩; exact Fin.succ_ne_zero i hi⟩
        · refine ⟨Or.inr ⟨i, hi1, rfl⟩, ?_⟩
          rintro ⟨j, hj, hj_eq⟩
          exact hi2 (Fin.succ_injective _ hj_eq ▸ hj)
    have h_union_sub :
        ((𝒜₀ ∪ 𝒜₁) ×ˢ (𝒜₀ ∪ 𝒜₁)).image (fun p => p.1 \ p.2) ⊆ 𝒟₀ ∪ 𝒟₁ := by
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨⟨S₁, S₂⟩, hS, rfl⟩
      rcases Finset.mem_product.mp hS with ⟨hS1, hS2⟩
      rcases Finset.mem_union.mp hS1 with h10 | h11 <;>
        rcases Finset.mem_union.mp hS2 with h20 | h21
      · apply Finset.mem_union_left
        rw [hproj0_mem]
        refine Finset.mem_image.mpr ⟨(S₁.map (finSuccEmb n), S₂.map (finSuccEmb n)),
          Finset.mem_product.mpr ⟨(hproj0_mem _ _).mp h10, (hproj0_mem _ _).mp h20⟩, ?_⟩
        rw [Finset.map_sdiff]
      · apply Finset.mem_union_left
        rw [hproj0_mem]
        refine Finset.mem_image.mpr ⟨(S₁.map (finSuccEmb n), insert 0 (S₂.map (finSuccEmb n))),
          Finset.mem_product.mpr ⟨(hproj0_mem _ _).mp h10, (hproj1_mem _ _).mp h21⟩, ?_⟩
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_map, finSuccEmb_apply]
        constructor
        · rintro ⟨⟨i, hi, rfl⟩, hnot⟩
          exact ⟨i, ⟨hi, fun h => hnot (Or.inr ⟨i, h, rfl⟩)⟩, rfl⟩
        · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
          refine ⟨⟨i, hi1, rfl⟩, fun h => ?_⟩
          rcases h with h0 | ⟨j, hj, hj_eq⟩
          · exact Fin.succ_ne_zero i h0
          · exact hi2 (Fin.succ_injective _ hj_eq ▸ hj)
      · apply Finset.mem_union_right
        rw [hproj1_mem]
        exact Finset.mem_image.mpr ⟨(insert 0 (S₁.map (finSuccEmb n)), S₂.map (finSuccEmb n)),
          Finset.mem_product.mpr ⟨(hproj1_mem _ _).mp h11, (hproj0_mem _ _).mp h20⟩,
          hsdiff_10 S₁ S₂⟩
      · apply Finset.mem_union_left
        rw [hproj0_mem]
        refine Finset.mem_image.mpr
          ⟨(insert 0 (S₁.map (finSuccEmb n)), insert 0 (S₂.map (finSuccEmb n))),
          Finset.mem_product.mpr ⟨(hproj1_mem _ _).mp h11, (hproj1_mem _ _).mp h21⟩, ?_⟩
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_map, finSuccEmb_apply]
        constructor
        · rintro ⟨rfl | ⟨i, hi, rfl⟩, hnot⟩
          · exact absurd (Or.inl rfl) hnot
          · exact ⟨i, ⟨hi, fun h => hnot (Or.inr ⟨i, h, rfl⟩)⟩, rfl⟩
        · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
          refine ⟨Or.inr ⟨i, hi1, rfl⟩, ?_⟩
          rintro (h0 | ⟨j, hj, hj_eq⟩)
          · exact Fin.succ_ne_zero i h0
          · exact hi2 (Fin.succ_injective _ hj_eq ▸ hj)
    have h_inter_sub :
        ((𝒜₀ ∩ 𝒜₁) ×ˢ (𝒜₀ ∩ 𝒜₁)).image (fun p => p.1 \ p.2) ⊆ 𝒟₀ ∩ 𝒟₁ := by
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨⟨S₁, S₂⟩, hS, rfl⟩
      rcases Finset.mem_product.mp hS with ⟨hS1, hS2⟩
      rcases Finset.mem_inter.mp hS1 with ⟨h10, h11⟩
      rcases Finset.mem_inter.mp hS2 with ⟨h20, h21⟩
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · rw [hproj0_mem]
        refine Finset.mem_image.mpr ⟨(S₁.map (finSuccEmb n), S₂.map (finSuccEmb n)),
          Finset.mem_product.mpr ⟨(hproj0_mem _ _).mp h10, (hproj0_mem _ _).mp h20⟩, ?_⟩
        rw [Finset.map_sdiff]
      · rw [hproj1_mem]
        exact Finset.mem_image.mpr ⟨(insert 0 (S₁.map (finSuccEmb n)), S₂.map (finSuccEmb n)),
          Finset.mem_product.mpr ⟨(hproj1_mem _ _).mp h11, (hproj0_mem _ _).mp h20⟩,
          hsdiff_10 S₁ S₂⟩
    have h1 : (𝒜₀ ∪ 𝒜₁).card ≤ (𝒟₀ ∪ 𝒟₁).card :=
      le_trans (ih (𝒜₀ ∪ 𝒜₁)) (Finset.card_le_card h_union_sub)
    have h2 : (𝒜₀ ∩ 𝒜₁).card ≤ (𝒟₀ ∩ 𝒟₁).card :=
      le_trans (ih (𝒜₀ ∩ 𝒜₁)) (Finset.card_le_card h_inter_sub)
    calc 𝒜.card
        = 𝒜₀.card + 𝒜₁.card := hsplit_card 𝒜
      _ = (𝒜₀ ∪ 𝒜₁).card + (𝒜₀ ∩ 𝒜₁).card := (Finset.card_union_add_card_inter 𝒜₀ 𝒜₁).symm
      _ ≤ (𝒟₀ ∪ 𝒟₁).card + (𝒟₀ ∩ 𝒟₁).card := Nat.add_le_add h1 h2
      _ = 𝒟₀.card + 𝒟₁.card := Finset.card_union_add_card_inter 𝒟₀ 𝒟₁
      _ = 𝒟.card := (hsplit_card 𝒟).symm

end Arith4Ext.SetSystemsCorrelation
