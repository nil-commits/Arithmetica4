import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# PPL 038: Erdős Problem #20 — The Sunflower Conjecture ($1,000, Open)

**Honest Scope:** The Erdős–Rado Sunflower Conjecture (`f(n, r) < c_r ^ n`) remains
**OPEN** (Erdős Problem #20 / PPL 038). This file formalizes a pure-Mathlib landmark suite
covering both the classical Erdős–Rado (1960) and modern post-ALWZ (2019–2025) Sunflower
& Spread Lemmas, the `Ω((1/p) log n)` Spread-Lemma tightness barrier, exact small-`n`
values, and exponential lower bounds up to Abbott–Hanson (1974).
-/

namespace PPL038

open scoped BigOperators

/-! ### Section 1: Classical Erdős–Rado Sunflower Lemma (1960) -/

/-- Every family of nonempty finite sets has a maximal pairwise disjoint subfamily. -/
private lemma exists_maximal_pairwise_disjoint {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hne : ∀ S ∈ F, S.Nonempty) :
    ∃ M ⊆ F, (M : Set (Finset α)).PairwiseDisjoint id ∧
      ∀ S ∈ F, ∃ A ∈ M, ¬ Disjoint S A := by
  classical
  let P : Finset (Finset (Finset α)) :=
    F.powerset.filter (fun M => (M : Set (Finset α)).PairwiseDisjoint id)
  have hPne : P.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset F, by simp⟩⟩
  obtain ⟨M, hMP, hMmax⟩ := Finset.exists_max_image P Finset.card hPne
  have hMsub : M ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hMP).1
  have hMdisj : (M : Set (Finset α)).PairwiseDisjoint id := (Finset.mem_filter.mp hMP).2
  refine ⟨M, hMsub, hMdisj, ?_⟩
  intro S hSF
  by_contra hnone
  push Not at hnone
  have hSnotM : S ∉ M := by
    intro hSM
    have hdis := hnone S hSM
    have hSe : S = ∅ := disjoint_self.mp hdis
    exact (hne S hSF).ne_empty hSe
  have hinsP : insert S M ∈ P := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hSF hMsub), ?_⟩
    intro A hA B hB hAB
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hA hB
    rcases hA with rfl | hAM <;> rcases hB with rfl | hBM
    · exact (hAB rfl).elim
    · exact hnone B hBM
    · exact (hnone A hAM).symm
    · exact hMdisj hAM hBM hAB
  have hle := hMmax (insert S M) hinsP
  rw [Finset.card_insert_of_notMem hSnotM] at hle
  omega

/-- **Classical Erdős–Rado Sunflower Lemma (1960):**
Every `n`-uniform family `F` of cardinality strictly greater than `n! * (r - 1) ^ n`
(for `r ≥ 1`) contains an `r`-sunflower. Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl038_erdos_rado_sunflower_lemma
    {α : Type*} [DecidableEq α] :
    ∀ (n r : ℕ), 1 ≤ r →
      ∀ (F : Finset (Finset α)), (∀ S ∈ F, S.card = n) →
        n.factorial * (r - 1) ^ n < F.card →
        ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  intro n
  induction n with
  | zero =>
    intro r hr F hunif hcard
    simp only [Nat.factorial_zero, pow_zero, mul_one] at hcard
    have hFsub : F ⊆ {∅} := by
      intro S hS
      rw [Finset.mem_singleton]
      exact Finset.card_eq_zero.mp (hunif S hS)
    have hFle : F.card ≤ 1 := (Finset.card_le_card hFsub).trans (by simp)
    omega
  | succ n ih =>
    intro r hr F hunif hcard
    have hne : ∀ S ∈ F, S.Nonempty := fun S hS =>
      Finset.card_pos.mp (by rw [hunif S hS]; omega)
    obtain ⟨M, hMsub, hMdisj, hMmax⟩ := exists_maximal_pairwise_disjoint F hne
    by_cases hMge : r ≤ M.card
    · obtain ⟨G, hGM, hGcard⟩ := Finset.exists_subset_card_eq hMge
      refine ⟨G, hGM.trans hMsub, hGcard, ∅, ?_⟩
      intro A hA B hB hAB
      exact Finset.disjoint_iff_inter_eq_empty.mp (hMdisj (hGM hA) (hGM hB) hAB)
    · push Not at hMge
      have hMle : M.card ≤ r - 1 := by omega
      let U : Finset α := M.biUnion id
      have hUcard : U.card ≤ (r - 1) * (n + 1) := by
        calc U.card ≤ ∑ A ∈ M, A.card := Finset.card_biUnion_le
          _ = ∑ _A ∈ M, (n + 1) := Finset.sum_congr rfl (fun A hA => hunif A (hMsub hA))
          _ = M.card * (n + 1) := by simp
          _ ≤ (r - 1) * (n + 1) := Nat.mul_le_mul_right (n + 1) hMle
      have hcover : ∀ S ∈ F, ∃ x ∈ U, x ∈ S := by
        intro S hS
        obtain ⟨A, hAM, hndisj⟩ := hMmax S hS
        rw [Finset.not_disjoint_iff] at hndisj
        obtain ⟨x, hxS, hxA⟩ := hndisj
        exact ⟨x, Finset.mem_biUnion.mpr ⟨A, hAM, hxA⟩, hxS⟩
      have hUsum : F.card ≤ ∑ x ∈ U, (F.filter (fun S => x ∈ S)).card := by
        calc F.card = (F.filter (fun S => ∃ x ∈ U, x ∈ S)).card := by
              rw [Finset.filter_true_of_mem hcover]
          _ ≤ (U.biUnion (fun x => F.filter (fun S => x ∈ S))).card := by
              refine Finset.card_le_card (fun S hS => ?_)
              rcases Finset.mem_filter.mp hS with ⟨hSF, x, hxU, hxS⟩
              exact Finset.mem_biUnion.mpr ⟨x, hxU, Finset.mem_filter.mpr ⟨hSF, hxS⟩⟩
          _ ≤ ∑ x ∈ U, (F.filter (fun S => x ∈ S)).card := Finset.card_biUnion_le
      have hUpos : 0 < U.card := by
        by_contra hU0
        push Not at hU0
        have hUe : U = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hU0)
        rw [hUe, Finset.sum_empty] at hUsum
        omega
      have hex : ∃ x ∈ U, n.factorial * (r - 1) ^ n < (F.filter (fun S => x ∈ S)).card := by
        by_contra hall
        push Not at hall
        have hbound : ∑ x ∈ U, (F.filter (fun S => x ∈ S)).card ≤
            U.card * (n.factorial * (r - 1) ^ n) := by
          calc ∑ x ∈ U, (F.filter (fun S => x ∈ S)).card
              ≤ ∑ _x ∈ U, (n.factorial * (r - 1) ^ n) := Finset.sum_le_sum hall
            _ = U.card * (n.factorial * (r - 1) ^ n) := by simp
        have hcalc : U.card * (n.factorial * (r - 1) ^ n) ≤
            (n + 1).factorial * (r - 1) ^ (n + 1) := by
          calc U.card * (n.factorial * (r - 1) ^ n)
              ≤ ((r - 1) * (n + 1)) * (n.factorial * (r - 1) ^ n) :=
                Nat.mul_le_mul_right _ hUcard
            _ = ((n + 1) * n.factorial) * ((r - 1) ^ n * (r - 1)) := by ring
            _ = (n + 1).factorial * (r - 1) ^ (n + 1) := by
                rw [Nat.factorial_succ, pow_succ]
        omega
      obtain ⟨x, _hxU, hxcard⟩ := hex
      let Fx : Finset (Finset α) := F.filter (fun S => x ∈ S)
      let F' : Finset (Finset α) := Fx.image (fun S => S.erase x)
      have hinj : Set.InjOn (fun S : Finset α => S.erase x) (Fx : Set (Finset α)) := by
        intro A hA B hB hEq
        have hxA : x ∈ A := (Finset.mem_filter.mp hA).2
        have hxB : x ∈ B := (Finset.mem_filter.mp hB).2
        have := congrArg (insert x) hEq
        rwa [Finset.insert_erase hxA, Finset.insert_erase hxB] at this
      have hF'card : F'.card = Fx.card := Finset.card_image_of_injOn hinj
      have hF'unif : ∀ T ∈ F', T.card = n := by
        intro T hT
        rcases Finset.mem_image.mp hT with ⟨S, hSFx, rfl⟩
        have hSF : S ∈ F := (Finset.mem_filter.mp hSFx).1
        have hxS : x ∈ S := (Finset.mem_filter.mp hSFx).2
        rw [Finset.card_erase_of_mem hxS, hunif S hSF]
        omega
      obtain ⟨G', hG'sub, hG'card, K', hK'⟩ :=
        ih r hr F' hF'unif (by rw [hF'card]; exact hxcard)
      let G : Finset (Finset α) := G'.image (insert x)
      have hG'notx : ∀ T ∈ G', x ∉ T := by
        intro T hT
        rcases Finset.mem_image.mp (hG'sub hT) with ⟨S, _hS, rfl⟩
        exact Finset.notMem_erase x S
      have hGinj : Set.InjOn (insert x) (G' : Set (Finset α)) := by
        intro A hA B hB hEq
        have := congrArg (fun S => S.erase x) hEq
        rwa [Finset.erase_insert (hG'notx A hA), Finset.erase_insert (hG'notx B hB)] at this
      refine ⟨G, ?_, ?_, insert x K', ?_⟩
      · intro S hS
        rcases Finset.mem_image.mp hS with ⟨T, hTG', rfl⟩
        rcases Finset.mem_image.mp (hG'sub hTG') with ⟨S₀, hS₀Fx, rfl⟩
        rw [Finset.insert_erase (Finset.mem_filter.mp hS₀Fx).2]
        exact (Finset.mem_filter.mp hS₀Fx).1
      · rw [Finset.card_image_of_injOn hGinj, hG'card]
      · intro A hA B hB hAB
        rcases Finset.mem_image.mp hA with ⟨A', hA'G', rfl⟩
        rcases Finset.mem_image.mp hB with ⟨B', hB'G', rfl⟩
        have hne' : A' ≠ B' := fun h => hAB (by rw [h])
        have hinter : insert x A' ∩ insert x B' = insert x (A' ∩ B') := by
          ext y; simp; tauto
        rw [hinter, hK' A' hA'G' B' hB'G' hne']

/-! ### Section 2: Modern Spread Lemma & Sunflower Lemma via Elementary Bayesian Peeling -/

/-- Exact `q`-biased binomial product weight on subsets of `U`. -/
private def binomWeight {α : Type*} (U : Finset α) (q : ℚ) (W : Finset α) : ℚ :=
  q ^ W.card * (1 - q) ^ (U.card - W.card)

private lemma binomWeight_nonneg {α : Type*} (U : Finset α) {q : ℚ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (W : Finset α) :
    0 ≤ binomWeight U q W := by
  unfold binomWeight
  exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.mpr hq1) _)

private lemma sum_binomWeight_powerset {α : Type*} [DecidableEq α]
    (U : Finset α) (q : ℚ) :
    ∑ W ∈ U.powerset, binomWeight U q W = 1 := by
  induction U using Finset.induction_on with
  | empty => simp [binomWeight]
  | insert a s ha ih =>
    rw [Finset.powerset_insert]
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro W hW1 hW2
      rcases Finset.mem_image.mp hW2 with ⟨V, _hV, rfl⟩
      exact ha (Finset.mem_powerset.mp hW1 (Finset.mem_insert_self a V))
    rw [Finset.sum_union hdisj]
    have hinj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
      intro V₁ hV₁ V₂ hV₂ hEq
      have ha1 : a ∉ V₁ := fun h => ha (Finset.mem_powerset.mp hV₁ h)
      have ha2 : a ∉ V₂ := fun h => ha (Finset.mem_powerset.mp hV₂ h)
      have := congrArg (fun T => T.erase a) hEq
      rwa [Finset.erase_insert ha1, Finset.erase_insert ha2] at this
    rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    have h1 : ∑ W ∈ s.powerset, binomWeight (insert a s) q W =
        (1 - q) * ∑ W ∈ s.powerset, binomWeight s q W := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun W hW => ?_)
      have hle : W.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hW)
      unfold binomWeight
      rw [Finset.card_insert_of_notMem ha, Nat.succ_sub hle, pow_succ]
      ring
    have h2 : ∑ W ∈ s.powerset, binomWeight (insert a s) q (insert a W) =
        q * ∑ W ∈ s.powerset, binomWeight s q W := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun W hW => ?_)
      have haW : a ∉ W := fun h => ha (Finset.mem_powerset.mp hW h)
      unfold binomWeight
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haW,
          Nat.succ_sub_succ_eq_sub, pow_succ]
      ring
    rw [h1, h2, ih]
    ring

private lemma sum_binomWeight_superset {α : Type*} [DecidableEq α]
    (U A : Finset α) (hAU : A ⊆ U) (q : ℚ) :
    ∑ W ∈ U.powerset.filter (fun W => A ⊆ W), binomWeight U q W = q ^ A.card := by
  have himg : U.powerset.filter (fun W => A ⊆ W) = (U \ A).powerset.image (fun V => A ∪ V) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hWU, hAW⟩
      refine ⟨W \ A, ?_, Finset.union_sdiff_of_subset hAW⟩
      exact Finset.sdiff_subset_sdiff hWU (Finset.Subset.refl A)
    · rintro ⟨V, hV, rfl⟩
      refine ⟨Finset.union_subset hAU (hV.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  have hinj : Set.InjOn (fun V => A ∪ V) ((U \ A).powerset : Set (Finset α)) := by
    intro V₁ hV₁ V₂ hV₂ hEq
    have hd1 : Disjoint A V₁ :=
      Disjoint.mono_right (Finset.mem_powerset.mp hV₁) disjoint_sdiff_self_right
    have hd2 : Disjoint A V₂ :=
      Disjoint.mono_right (Finset.mem_powerset.mp hV₂) disjoint_sdiff_self_right
    have := congrArg (fun T => T \ A) hEq
    simpa [Finset.union_sdiff_cancel_left hd1, Finset.union_sdiff_cancel_left hd2] using this
  rw [himg, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  have hterm : ∑ V ∈ (U \ A).powerset, binomWeight U q (A ∪ V) =
      q ^ A.card * ∑ V ∈ (U \ A).powerset, binomWeight (U \ A) q V := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun V hV => ?_)
    have hVsub : V ⊆ U \ A := Finset.mem_powerset.mp hV
    have hdisj : Disjoint A V := Disjoint.mono_right hVsub disjoint_sdiff_self_right
    have hcard_union : (A ∪ V).card = A.card + V.card := Finset.card_union_of_disjoint hdisj
    have hcard_sdiff : (U \ A).card = U.card - A.card := Finset.card_sdiff_of_subset hAU
    unfold binomWeight
    rw [hcard_union, hcard_sdiff, pow_add, Nat.sub_add_eq]
    ring
  rw [hterm, sum_binomWeight_powerset, mul_one]

private lemma sum_binomWeight_union_eq {α : Type*} [DecidableEq α]
    (U A : Finset α) (hAU : A ⊆ U) {q : ℚ} (hq : q ≠ 0) (f : Finset α → ℚ) :
    ∑ W ∈ U.powerset, binomWeight U q W * f (A ∪ W) =
      ∑ y ∈ U.powerset.filter (fun y => A ⊆ y),
        binomWeight U q y * (q ^ A.card)⁻¹ * f y := by
  have hmaps : ∀ W ∈ U.powerset, A ∪ W ∈ U.powerset.filter (fun y => A ⊆ y) := by
    intro W hW
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.union_subset hAU (Finset.mem_powerset.mp hW)),
       Finset.subset_union_left⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  have hyU : y ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hy).1
  have hAy : A ⊆ y := (Finset.mem_filter.mp hy).2
  have hfib : U.powerset.filter (fun W => A ∪ W = y) =
      A.powerset.image (fun V => (y \ A) ∪ V) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨_hWU, hEq⟩
      refine ⟨W ∩ A, Finset.inter_subset_right, ?_⟩
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      have hx : x ∈ y ↔ x ∈ A ∨ x ∈ W := by rw [← hEq]; simp
      tauto
    · rintro ⟨V, hVA, rfl⟩
      refine ⟨Finset.union_subset (Finset.sdiff_subset.trans hyU) (hVA.trans hAU), ?_⟩
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hxA | ⟨hxy, _⟩ | hxV)
        · exact hAy hxA
        · exact hxy
        · exact hAy (hVA hxV)
      · intro hxy
        by_cases hxA : x ∈ A
        · exact Or.inl hxA
        · exact Or.inr (Or.inl ⟨hxy, hxA⟩)
  have hinj : Set.InjOn (fun V => (y \ A) ∪ V) (A.powerset : Set (Finset α)) := by
    intro V₁ hV₁ V₂ hV₂ hEq
    have hd1 : Disjoint (y \ A) V₁ :=
      Disjoint.mono_right (Finset.mem_powerset.mp hV₁) disjoint_sdiff_self_left
    have hd2 : Disjoint (y \ A) V₂ :=
      Disjoint.mono_right (Finset.mem_powerset.mp hV₂) disjoint_sdiff_self_left
    have := congrArg (fun T => T \ (y \ A)) hEq
    simpa [Finset.union_sdiff_cancel_left hd1, Finset.union_sdiff_cancel_left hd2] using this
  have hsum_congr : ∑ W ∈ U.powerset.filter (fun W => A ∪ W = y),
      binomWeight U q W * f (A ∪ W) =
      (∑ W ∈ U.powerset.filter (fun W => A ∪ W = y), binomWeight U q W) * f y := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun W hW => by rw [(Finset.mem_filter.mp hW).2])
  rw [hsum_congr, hfib, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  have hinner : ∑ V ∈ A.powerset, binomWeight U q ((y \ A) ∪ V) =
      binomWeight U q y * (q ^ A.card)⁻¹ * ∑ V ∈ A.powerset, binomWeight A q V := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun V hV => ?_)
    have hVA : V ⊆ A := Finset.mem_powerset.mp hV
    have hdisj : Disjoint (y \ A) V := Disjoint.mono_right hVA disjoint_sdiff_self_left
    have hcard_u : ((y \ A) ∪ V).card = (y.card - A.card) + V.card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hAy]
    have hAy_le : A.card ≤ y.card := Finset.card_le_card hAy
    have hyU_le : y.card ≤ U.card := Finset.card_le_card hyU
    have hVA_le : V.card ≤ A.card := Finset.card_le_card hVA
    have hsub_eq : U.card - ((y \ A) ∪ V).card = (U.card - y.card) + (A.card - V.card) := by
      rw [hcard_u]; omega
    have hpow_y : q ^ y.card = q ^ (y.card - A.card) * q ^ A.card := by
      rw [← pow_add, Nat.sub_add_cancel hAy_le]
    unfold binomWeight
    rw [hsub_eq, hcard_u, pow_add, pow_add, hpow_y]
    have hqpow : q ^ A.card ≠ 0 := pow_ne_zero A.card hq
    field_simp [hqpow]
  rw [hinner, sum_binomWeight_powerset, mul_one]

private lemma sum_binomWeight_union_indep {α : Type*} [DecidableEq α]
    (U : Finset α) (q₁ q₂ : ℚ) (f : Finset α → ℚ) :
    ∑ W₁ ∈ U.powerset, binomWeight U q₁ W₁ *
      (∑ W₂ ∈ U.powerset, binomWeight U q₂ W₂ * f (W₁ ∪ W₂)) =
    ∑ W ∈ U.powerset, binomWeight U (q₁ + q₂ - q₁ * q₂) W * f W := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp [binomWeight]
  | insert a s ha ih =>
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro W hW1 hW2
      rcases Finset.mem_image.mp hW2 with ⟨V, _hV, rfl⟩
      exact ha (Finset.mem_powerset.mp hW1 (Finset.mem_insert_self a V))
    have hinj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
      intro V₁ hV₁ V₂ hV₂ hEq
      have ha1 : a ∉ V₁ := fun h => ha (Finset.mem_powerset.mp hV₁ h)
      have ha2 : a ∉ V₂ := fun h => ha (Finset.mem_powerset.mp hV₂ h)
      have := congrArg (fun T => T.erase a) hEq
      rwa [Finset.erase_insert ha1, Finset.erase_insert ha2] at this
    have hbw0 : ∀ (q : ℚ) (W : Finset α), W ∈ s.powerset →
        binomWeight (insert a s) q W = (1 - q) * binomWeight s q W := by
      intro q W hW
      have hle : W.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hW)
      unfold binomWeight
      rw [Finset.card_insert_of_notMem ha, Nat.succ_sub hle, pow_succ]
      ring
    have hbw1 : ∀ (q : ℚ) (W : Finset α), W ∈ s.powerset →
        binomWeight (insert a s) q (insert a W) = q * binomWeight s q W := by
      intro q W hW
      have haW : a ∉ W := fun h => ha (Finset.mem_powerset.mp hW h)
      unfold binomWeight
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haW,
          Nat.succ_sub_succ_eq_sub, pow_succ]
      ring
    rw [Finset.powerset_insert, Finset.sum_union hdisj,
        Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    rw [Finset.sum_union hdisj, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    have hsplit_inner : ∀ (g : Finset α → ℚ),
        ∑ W₂ ∈ s.powerset ∪ s.powerset.image (insert a),
          binomWeight (insert a s) q₂ W₂ * g W₂ =
        (1 - q₂) * ∑ W₂ ∈ s.powerset, binomWeight s q₂ W₂ * g W₂ +
        q₂ * ∑ W₂ ∈ s.powerset, binomWeight s q₂ W₂ * g (insert a W₂) := by
      intro g
      rw [Finset.sum_union hdisj, Finset.sum_image (fun x hx y hy h => hinj hx hy h),
          Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl (fun W₂ hW₂ => ?_)
        rw [hbw0 q₂ W₂ hW₂]; ring
      · refine Finset.sum_congr rfl (fun W₂ hW₂ => ?_)
        rw [hbw1 q₂ W₂ hW₂]; ring
    have hL1 : ∑ W₁ ∈ s.powerset, binomWeight (insert a s) q₁ W₁ *
        (∑ W₂ ∈ s.powerset ∪ s.powerset.image (insert a),
          binomWeight (insert a s) q₂ W₂ * f (W₁ ∪ W₂)) =
        (1 - q₁) * (1 - q₂) * ∑ W ∈ s.powerset, binomWeight s (q₁ + q₂ - q₁ * q₂) W * f W +
        (1 - q₁) * q₂ * ∑ W ∈ s.powerset, binomWeight s (q₁ + q₂ - q₁ * q₂) W * f (insert a W) := by
      have hstep : ∀ W₁ ∈ s.powerset,
          binomWeight (insert a s) q₁ W₁ *
            (∑ W₂ ∈ s.powerset ∪ s.powerset.image (insert a),
              binomWeight (insert a s) q₂ W₂ * f (W₁ ∪ W₂)) =
          (1 - q₁) * (1 - q₂) * (binomWeight s q₁ W₁ *
              ∑ W₂ ∈ s.powerset, binomWeight s q₂ W₂ * f (W₁ ∪ W₂)) +
          (1 - q₁) * q₂ * (binomWeight s q₁ W₁ *
              ∑ W₂ ∈ s.powerset, binomWeight s q₂ W₂ * f (insert a (W₁ ∪ W₂))) := by
        intro W₁ hW₁
        rw [hbw0 q₁ W₁ hW₁, hsplit_inner (fun W₂ => f (W₁ ∪ W₂))]
        have hins : ∀ W₂ : Finset α, W₁ ∪ insert a W₂ = insert a (W₁ ∪ W₂) := fun W₂ => by
          ext x; simp
        simp_rw [hins]
        ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ih f, ih (fun W => f (insert a W))]
    have hL2 : ∑ W₁ ∈ s.powerset, binomWeight (insert a s) q₁ (insert a W₁) *
        (∑ W₂ ∈ s.powerset ∪ s.powerset.image (insert a),
          binomWeight (insert a s) q₂ W₂ * f (insert a W₁ ∪ W₂)) =
        q₁ * (1 - q₂) * ∑ W ∈ s.powerset, binomWeight s (q₁ + q₂ - q₁ * q₂) W * f (insert a W) +
        q₁ * q₂ * ∑ W ∈ s.powerset, binomWeight s (q₁ + q₂ - q₁ * q₂) W * f (insert a W) := by
      have hstep : ∀ W₁ ∈ s.powerset,
          binomWeight (insert a s) q₁ (insert a W₁) *
            (∑ W₂ ∈ s.powerset ∪ s.powerset.image (insert a),
              binomWeight (insert a s) q₂ W₂ * f (insert a W₁ ∪ W₂)) =
          q₁ * (1 - q₂) * (binomWeight s q₁ W₁ *
              ∑ W₂ ∈ s.powerset, binomWeight s q₂ W₂ * f (insert a (W₁ ∪ W₂))) +
          q₁ * q₂ * (binomWeight s q₁ W₁ *
              ∑ W₂ ∈ s.powerset, binomWeight s q₂ W₂ * f (insert a (W₁ ∪ W₂))) := by
        intro W₁ hW₁
        rw [hbw1 q₁ W₁ hW₁, hsplit_inner (fun W₂ => f (insert a W₁ ∪ W₂))]
        have hins1 : ∀ W₂ : Finset α, insert a W₁ ∪ W₂ = insert a (W₁ ∪ W₂) := fun W₂ => by
          ext x; simp
        have hins2 : ∀ W₂ : Finset α, insert a W₁ ∪ insert a W₂ = insert a (W₁ ∪ W₂) := fun W₂ => by
          ext x; simp
        simp_rw [hins2, hins1]
        ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ih (fun W => f (insert a W))]
    have hR1 : ∑ W ∈ s.powerset, binomWeight (insert a s) (q₁ + q₂ - q₁ * q₂) W * f W =
        (1 - (q₁ + q₂ - q₁ * q₂)) *
          ∑ W ∈ s.powerset, binomWeight s (q₁ + q₂ - q₁ * q₂) W * f W := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun W hW => by rw [hbw0 _ W hW]; ring)
    have hR2 : ∑ W ∈ s.powerset,
        binomWeight (insert a s) (q₁ + q₂ - q₁ * q₂) (insert a W) * f (insert a W) =
        (q₁ + q₂ - q₁ * q₂) *
          ∑ W ∈ s.powerset, binomWeight s (q₁ + q₂ - q₁ * q₂) W * f (insert a W) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun W hW => by rw [hbw1 _ W hW]; ring)
    rw [hL1, hL2, hR1, hR2]
    ring

private lemma binomWeight_mono_prob {α : Type*} [DecidableEq α]
    (U : Finset α) {p₁ p₂ : ℚ} (hp₁0 : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂1 : p₂ ≤ 1)
    (P : Finset α → Prop) [DecidablePred P]
    (hmono : ∀ A B, A ⊆ B → P A → P B) :
    ∑ W ∈ U.powerset, binomWeight U p₁ W * (if P W then (1 : ℚ) else 0) ≤
    ∑ W ∈ U.powerset, binomWeight U p₂ W * (if P W then (1 : ℚ) else 0) := by
  by_cases h1 : p₁ = 1
  · have h2 : p₂ = 1 := le_antisymm hp₂1 (h1 ▸ h12)
    rw [h1, h2]
  · have hden : 0 < 1 - p₁ := sub_pos.mpr (lt_of_le_of_ne (h12.trans hp₂1) h1)
    let q' : ℚ := (p₂ - p₁) / (1 - p₁)
    have hq'0 : 0 ≤ q' := div_nonneg (sub_nonneg.mpr h12) hden.le
    have hq'1 : q' ≤ 1 := (div_le_one hden).mpr (by linarith)
    have hp2_eq : p₁ + q' - p₁ * q' = p₂ := by
      dsimp only [q']
      field_simp [hden.ne']
      ring
    rw [← hp2_eq, ← sum_binomWeight_union_indep]
    refine Finset.sum_le_sum (fun W₁ _hW₁ => ?_)
    have hbw1 : 0 ≤ binomWeight U p₁ W₁ := binomWeight_nonneg U hp₁0 (h12.trans hp₂1) W₁
    refine mul_le_mul_of_nonneg_left ?_ hbw1
    calc (if P W₁ then (1 : ℚ) else 0)
        = (∑ W₂ ∈ U.powerset, binomWeight U q' W₂) * (if P W₁ then (1 : ℚ) else 0) := by
            rw [sum_binomWeight_powerset, one_mul]
      _ = ∑ W₂ ∈ U.powerset, binomWeight U q' W₂ * (if P W₁ then (1 : ℚ) else 0) := by
            rw [Finset.sum_mul]
      _ ≤ ∑ W₂ ∈ U.powerset, binomWeight U q' W₂ * (if P (W₁ ∪ W₂) then (1 : ℚ) else 0) := by
            refine Finset.sum_le_sum (fun W₂ _hW₂ => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (binomWeight_nonneg U hq'0 hq'1 W₂)
            split_ifs with hP1 hP2
            · exact le_rfl
            · exact (hP2 (hmono W₁ (W₁ ∪ W₂) Finset.subset_union_left hP1)).elim
            · norm_num
            · exact le_rfl

/-- Exact coloring marginal identity: averaging over uniform colorings `U → Fin M`
gives the exact `(1 / M)`-biased binomial sum for each color class `c`. -/
private lemma sum_colorings_eq_binomWeight {α : Type*} [DecidableEq α]
    (U : Finset α) {M : ℕ} (hM : 1 ≤ M) (c : Fin M) (g : Finset α → ℚ) :
    ∑ f : {x // x ∈ U} → Fin M,
        g ((U.attach.filter (fun x => f x = c)).image Subtype.val) =
      (M : ℚ) ^ U.card * ∑ W ∈ U.powerset, binomWeight U ((M : ℚ)⁻¹) W * g W := by
  induction U using Finset.induction_on generalizing g with
  | empty =>
    let _ : Unique ({x // x ∈ (∅ : Finset α)} → Fin M) := Pi.uniqueOfIsEmpty _
    rw [Fintype.sum_unique]
    simp [binomWeight]
  | insert a s ha ih =>
    let e : ({x // x ∈ insert a s} → Fin M) ≃ Fin M × ({x // x ∈ s} → Fin M) :=
      { toFun := fun f => (f ⟨a, Finset.mem_insert_self a s⟩,
          fun x => f ⟨x.1, Finset.mem_insert_of_mem x.2⟩)
        invFun := fun p x =>
          if h : x.1 = a then p.1
          else p.2 ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left h⟩
        left_inv := fun f => by
          funext ⟨x, hx⟩
          by_cases hxa : x = a
          · subst hxa; simp
          · simp [hxa]
        right_inv := fun ⟨v, f⟩ => by
          ext
          · simp
          · rename_i x
            have hxa : x.1 ≠ a := fun h => ha (h ▸ x.2)
            simp [hxa] }
    rw [Fintype.sum_equiv e _ (fun p =>
      g (if p.1 = c
         then insert a ((s.attach.filter (fun x => p.2 x = c)).image Subtype.val)
         else (s.attach.filter (fun x => p.2 x = c)).image Subtype.val))]
    · rw [Fintype.sum_prod_type]
      have hsplit : ∀ v : Fin M,
          ∑ f : {x // x ∈ s} → Fin M,
            g (if v = c
               then insert a ((s.attach.filter (fun x => f x = c)).image Subtype.val)
               else (s.attach.filter (fun x => f x = c)).image Subtype.val) =
          if v = c
          then (M : ℚ) ^ s.card * ∑ W ∈ s.powerset, binomWeight s (M : ℚ)⁻¹ W * g (insert a W)
          else (M : ℚ) ^ s.card * ∑ W ∈ s.powerset, binomWeight s (M : ℚ)⁻¹ W * g W := by
        intro v
        by_cases hvc : v = c
        · simp only [hvc, ↓reduceIte]
          exact ih (fun W => g (insert a W))
        · simp only [hvc, ↓reduceIte]
          exact ih g
      simp_rw [hsplit]
      have hcard_c : (Finset.univ.filter (fun v : Fin M => v = c)).card = 1 := by
        rw [Finset.filter_eq', if_pos (Finset.mem_univ c), Finset.card_singleton]
      have hcard_nc : (Finset.univ.filter (fun v : Fin M => v ≠ c)).card = M - 1 := by
        have hcompl : (Finset.univ.filter (fun v : Fin M => v ≠ c)) = Finset.univ.erase c := by
          ext v; simp
        rw [hcompl, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard_c, hcard_nc]
      simp only [nsmul_eq_mul, Nat.cast_one, one_mul]
      have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro W hW1 hW2
        rcases Finset.mem_image.mp hW2 with ⟨V, _hV, rfl⟩
        exact ha (Finset.mem_powerset.mp hW1 (Finset.mem_insert_self a V))
      have hinj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
        intro V₁ hV₁ V₂ hV₂ hEq
        have ha1 : a ∉ V₁ := fun h => ha (Finset.mem_powerset.mp hV₁ h)
        have ha2 : a ∉ V₂ := fun h => ha (Finset.mem_powerset.mp hV₂ h)
        have := congrArg (fun T => T.erase a) hEq
        rwa [Finset.erase_insert ha1, Finset.erase_insert ha2] at this
      rw [Finset.powerset_insert, Finset.sum_union hdisj,
          Finset.sum_image (fun x hx y hy h => hinj hx hy h),
          Finset.card_insert_of_notMem ha, pow_succ, mul_add]
      have hMne : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hM1 : ((M - 1 : ℕ) : ℚ) = (M : ℚ) * (1 - (M : ℚ)⁻¹) := by
        rw [Nat.cast_sub hM, Nat.cast_one]
        field_simp [hMne]
      have hR1 : (M : ℚ) ^ s.card * (M : ℚ) *
          ∑ W ∈ s.powerset, binomWeight (insert a s) (M : ℚ)⁻¹ W * g W =
          ((M - 1 : ℕ) : ℚ) * ((M : ℚ) ^ s.card *
            ∑ W ∈ s.powerset, binomWeight s (M : ℚ)⁻¹ W * g W) := by
        have hstep : ∑ W ∈ s.powerset, binomWeight (insert a s) (M : ℚ)⁻¹ W * g W =
            (1 - (M : ℚ)⁻¹) * ∑ W ∈ s.powerset, binomWeight s (M : ℚ)⁻¹ W * g W := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun W hW => ?_)
          have hle : W.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hW)
          unfold binomWeight
          rw [Finset.card_insert_of_notMem ha, Nat.succ_sub hle, pow_succ]
          ring
        rw [hstep, hM1]; ring
      have hR2 : (M : ℚ) ^ s.card * (M : ℚ) *
          ∑ W ∈ s.powerset, binomWeight (insert a s) (M : ℚ)⁻¹ (insert a W) * g (insert a W) =
          (M : ℚ) ^ s.card * ∑ W ∈ s.powerset, binomWeight s (M : ℚ)⁻¹ W * g (insert a W) := by
        have hstep : ∑ W ∈ s.powerset,
            binomWeight (insert a s) (M : ℚ)⁻¹ (insert a W) * g (insert a W) =
            (M : ℚ)⁻¹ * ∑ W ∈ s.powerset, binomWeight s (M : ℚ)⁻¹ W * g (insert a W) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun W hW => ?_)
          have haW : a ∉ W := fun h => ha (Finset.mem_powerset.mp hW h)
          unfold binomWeight
          rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haW,
              Nat.succ_sub_succ_eq_sub, pow_succ]
          ring
        rw [hstep]
        field_simp [hMne]
      rw [hR1, hR2]; ring
    · intro f
      congr 1
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists]
      by_cases hfc : f ⟨a, Finset.mem_insert_self a s⟩ = c
      · simp only [e, Equiv.coe_fn_mk, hfc, ↓reduceIte, Finset.mem_insert,
          Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists]
        constructor
        · rintro ⟨y, hy, hfy, rfl⟩
          rcases hy with rfl | hys
          · exact Or.inl rfl
          · exact Or.inr ⟨y, hys, hfy, rfl⟩
        · rintro (hx | ⟨y, hys, hfy, rfl⟩)
          · exact ⟨a, Or.inl rfl, hfc, hx.symm⟩
          · exact ⟨y, Or.inr hys, hfy, rfl⟩
      · simp only [e, Equiv.coe_fn_mk, hfc, ↓reduceIte, Finset.mem_insert,
          Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists]
        constructor
        · rintro ⟨y, hy, hfy, rfl⟩
          rcases hy with rfl | hys
          · exact (hfc hfy).elim
          · exact ⟨y, hys, hfy, rfl⟩
        · rintro ⟨y, hys, hfy, rfl⟩
          exact ⟨y, Or.inr hys, hfy, rfl⟩

/-- **8-Line Elementary Bayesian / Truncated Second-Moment One-Step Shrinkage Lemma:**
For any `R`-spread family `F` and residual assignment `A : G → P(U)` with `A i ⊆ i` and
`|A i| ≤ a`, the `q`-biased expected fraction of `m`-bad elements in `G` is bounded by
`τ + τ⁻¹ * ∑_{d = m}^a C(a, d) * (q * R)⁻¹ ^ d`. -/
private lemma one_step_bayesian_shrinkage {α : Type*} [DecidableEq α]
    (U : Finset α) (F G : Finset (Finset α)) (A : Finset α → Finset α)
    {a m : ℕ} {q R τ : ℚ}
    (hFne : F.Nonempty) (hGF : G ⊆ F)
    (hAsub : ∀ i ∈ G, A i ⊆ i)
    (hAU : ∀ i ∈ G, A i ⊆ U)
    (hAcard : ∀ i ∈ G, (A i).card ≤ a)
    (hspread : ∀ Z ⊆ U, ((F.filter (fun S => Z ⊆ S)).card : ℚ) ≤ (R : ℚ)⁻¹ ^ Z.card * F.card)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hR0 : 0 < R) (hτ0 : 0 < τ) :
    ∑ W ∈ U.powerset, binomWeight U q W *
      ((G.filter (fun i => ∀ j ∈ G, A j ⊆ A i ∪ W → m ≤ (A j \ W).card)).card : ℚ) /
        (F.card : ℚ) ≤
    τ + τ⁻¹ * ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d := by
  classical
  have hFpos : (0 : ℚ) < F.card := Nat.cast_pos.mpr hFne.card_pos
  let badPred (i W : Finset α) : Prop :=
    ∀ j ∈ G, A j ⊆ A i ∪ W → m ≤ (A j \ W).card
  let N (y : Finset α) : ℚ :=
    ∑ j ∈ G.filter (fun j => A j ⊆ y), (q ^ (A j).card)⁻¹
  have hN_nonneg : ∀ y, 0 ≤ N y := fun y =>
    Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (pow_nonneg hq0.le _))
  -- Step 1: Pointwise indicator bound on `badPred i W`
  have hpoint : ∀ i ∈ G, ∀ W ∈ U.powerset,
      (if badPred i W then (1 : ℚ) else 0) ≤
        (if N (A i ∪ W) < τ * F.card then (1 : ℚ) else 0) +
        (τ * F.card)⁻¹ *
          ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
            (q ^ (A j).card)⁻¹ := by
    intro i hi W _hW
    by_cases hbad : badPred i W
    · simp only [hbad, ↓reduceIte]
      by_cases hNlt : N (A i ∪ W) < τ * F.card
      · simp only [hNlt, ↓reduceIte]
        have h2 : 0 ≤ (τ * F.card)⁻¹ *
            ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
              (q ^ (A j).card)⁻¹ :=
          mul_nonneg (inv_nonneg.mpr (mul_pos hτ0 hFpos).le)
            (Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (pow_nonneg hq0.le _)))
        linarith
      · simp only [hNlt, ↓reduceIte, zero_add]
        push Not at hNlt
        have hfilt_eq :
            G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card) =
            G.filter (fun j => A j ⊆ A i ∪ W) := by
          ext j
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hjG, hsub, _⟩; exact ⟨hjG, hsub⟩
          · rintro ⟨hjG, hsub⟩
            refine ⟨hjG, hsub, ?_⟩
            have h1 : m ≤ (A j \ W).card := hbad j hjG hsub
            have h2 : A j \ W ⊆ A i ∩ A j := by
              intro x hx
              rcases Finset.mem_sdiff.mp hx with ⟨hxAj, hxW⟩
              have hxU := hsub hxAj
              rcases Finset.mem_union.mp hxU with hxAi | hxW'
              · exact Finset.mem_inter.mpr ⟨hxAi, hxAj⟩
              · exact (hxW hxW').elim
            exact h1.trans (Finset.card_le_card h2)
        rw [hfilt_eq]
        change 1 ≤ (τ * F.card)⁻¹ * N (A i ∪ W)
        have hτFpos : 0 < τ * F.card := mul_pos hτ0 hFpos
        rw [inv_mul_eq_div, le_div_iff₀ hτFpos, one_mul]
        exact hNlt
    · simp only [hbad, ↓reduceIte]
      have h1 : (0 : ℚ) ≤ if N (A i ∪ W) < τ * F.card then 1 else 0 := by
        split_ifs <;> norm_num
      have h2 : 0 ≤ (τ * F.card)⁻¹ *
          ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
            (q ^ (A j).card)⁻¹ :=
        mul_nonneg (inv_nonneg.mpr (mul_pos hτ0 hFpos).le)
          (Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (pow_nonneg hq0.le _)))
      linarith
  -- Step 2: Swap sums over `W` and `i ∈ G`, then apply `hpoint`
  have hlhs_eq :
      ∑ W ∈ U.powerset, binomWeight U q W *
        ((G.filter (fun i => badPred i W)).card : ℚ) / (F.card : ℚ) =
      (F.card : ℚ)⁻¹ * ∑ i ∈ G, ∑ W ∈ U.powerset,
        binomWeight U q W * (if badPred i W then (1 : ℚ) else 0) := by
    have hcard_sum : ∀ W : Finset α,
        ((G.filter (fun i => badPred i W)).card : ℚ) =
        ∑ i ∈ G, (if badPred i W then (1 : ℚ) else 0) := by
      intro W
      rw [Finset.sum_boole]
    have hstep : ∑ W ∈ U.powerset, binomWeight U q W *
        ((G.filter (fun i => badPred i W)).card : ℚ) / (F.card : ℚ) =
        (F.card : ℚ)⁻¹ * ∑ W ∈ U.powerset, ∑ i ∈ G,
          binomWeight U q W * (if badPred i W then (1 : ℚ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun W _ => ?_)
      rw [hcard_sum W, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hstep, Finset.sum_comm]
  rw [hlhs_eq]
  -- Apply pointwise bound inside the double sum
  have hsplit :
      (F.card : ℚ)⁻¹ * ∑ i ∈ G, ∑ W ∈ U.powerset,
        binomWeight U q W * (if badPred i W then (1 : ℚ) else 0) ≤
      (F.card : ℚ)⁻¹ * ∑ i ∈ G, ∑ W ∈ U.powerset,
        binomWeight U q W * (if N (A i ∪ W) < τ * F.card then (1 : ℚ) else 0) +
      (F.card : ℚ)⁻¹ * (τ * F.card)⁻¹ * ∑ i ∈ G, ∑ W ∈ U.powerset,
        binomWeight U q W *
          ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
            (q ^ (A j).card)⁻¹ := by
    have h1 : ∑ i ∈ G, ∑ W ∈ U.powerset,
          binomWeight U q W * (if badPred i W then (1 : ℚ) else 0) ≤
        ∑ i ∈ G, ∑ W ∈ U.powerset,
          (binomWeight U q W * (if N (A i ∪ W) < τ * F.card then (1 : ℚ) else 0) +
           binomWeight U q W * ((τ * F.card)⁻¹ *
            ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
              (q ^ (A j).card)⁻¹)) := by
      refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun W hW => ?_))
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hpoint i hi W hW) (binomWeight_nonneg U hq0.le hq1 W)
    calc (F.card : ℚ)⁻¹ * ∑ i ∈ G, ∑ W ∈ U.powerset,
            binomWeight U q W * (if badPred i W then (1 : ℚ) else 0)
        ≤ (F.card : ℚ)⁻¹ * ∑ i ∈ G, ∑ W ∈ U.powerset,
            (binomWeight U q W * (if N (A i ∪ W) < τ * F.card then (1 : ℚ) else 0) +
             binomWeight U q W * ((τ * F.card)⁻¹ *
              ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
                (q ^ (A j).card)⁻¹)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hFpos.le)
      _ = _ := by
          simp_rw [Finset.sum_add_distrib, mul_add]
          congr 1
          have hpull : ∀ i ∈ G,
              ∑ W ∈ U.powerset, binomWeight U q W *
                ((τ * F.card)⁻¹ *
                  ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
                    (q ^ (A j).card)⁻¹) =
              (τ * F.card)⁻¹ * ∑ W ∈ U.powerset, binomWeight U q W *
                ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
                  (q ^ (A j).card)⁻¹ := by
            intro i _
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun W _ => by ring)
          rw [Finset.sum_congr rfl hpull, ← Finset.mul_sum]
          ring
  -- Step 3: Bound Term 1 ≤ τ using `sum_binomWeight_union_eq`
  have hTerm1 :
      (F.card : ℚ)⁻¹ * ∑ i ∈ G, ∑ W ∈ U.powerset,
        binomWeight U q W * (if N (A i ∪ W) < τ * F.card then (1 : ℚ) else 0) ≤ τ := by
    have hrew : ∑ i ∈ G, ∑ W ∈ U.powerset,
          binomWeight U q W * (if N (A i ∪ W) < τ * F.card then (1 : ℚ) else 0) =
        ∑ i ∈ G, ∑ y ∈ U.powerset.filter (fun y => A i ⊆ y),
          binomWeight U q y * (q ^ (A i).card)⁻¹ * (if N y < τ * F.card then (1 : ℚ) else 0) :=
      Finset.sum_congr rfl (fun i hi =>
        sum_binomWeight_union_eq U (A i) (hAU i hi) hq0.ne'
          (fun y => if N y < τ * F.card then (1 : ℚ) else 0))
    rw [hrew]
    -- Rewrite filter as `if A i ⊆ y` and swap sums
    have hswap :
        ∑ i ∈ G, ∑ y ∈ U.powerset.filter (fun y => A i ⊆ y),
          binomWeight U q y * (q ^ (A i).card)⁻¹ * (if N y < τ * F.card then (1 : ℚ) else 0) =
        ∑ y ∈ U.powerset, binomWeight U q y * (if N y < τ * F.card then (1 : ℚ) else 0) * N y := by
      have h1 : ∀ i ∈ G,
          ∑ y ∈ U.powerset.filter (fun y => A i ⊆ y),
            binomWeight U q y * (q ^ (A i).card)⁻¹ * (if N y < τ * F.card then (1 : ℚ) else 0) =
          ∑ y ∈ U.powerset,
            (if A i ⊆ y then binomWeight U q y * (q ^ (A i).card)⁻¹ *
              (if N y < τ * F.card then (1 : ℚ) else 0) else 0) := fun i _ =>
        Finset.sum_filter _ _
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      have hNy : N y = ∑ i ∈ G, (if A i ⊆ y then (q ^ (A i).card)⁻¹ else 0) := by
        dsimp only [N]; exact Finset.sum_filter _ _
      rw [hNy, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs <;> ring
    rw [hswap]
    have hle : ∑ y ∈ U.powerset,
          binomWeight U q y * (if N y < τ * F.card then (1 : ℚ) else 0) * N y ≤
        ∑ y ∈ U.powerset, binomWeight U q y * (τ * F.card) := by
      refine Finset.sum_le_sum (fun y _ => ?_)
      have hbw : 0 ≤ binomWeight U q y := binomWeight_nonneg U hq0.le hq1 y
      by_cases hlt : N y < τ * F.card
      · simp only [hlt, ↓reduceIte, mul_one]
        exact mul_le_mul_of_nonneg_left hlt.le hbw
      · simp only [hlt, ↓reduceIte, mul_zero, zero_mul]
        exact mul_nonneg hbw (mul_pos hτ0 hFpos).le
    calc (F.card : ℚ)⁻¹ * ∑ y ∈ U.powerset,
            binomWeight U q y * (if N y < τ * F.card then (1 : ℚ) else 0) * N y
        ≤ (F.card : ℚ)⁻¹ * ∑ y ∈ U.powerset, binomWeight U q y * (τ * F.card) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hFpos.le)
      _ = (F.card : ℚ)⁻¹ * ((∑ y ∈ U.powerset, binomWeight U q y) * (τ * F.card)) := by
          rw [Finset.sum_mul]
      _ = τ := by
          rw [sum_binomWeight_powerset, one_mul]
          field_simp [hFpos.ne']
  -- Step 4: Bound Term 2 via `sum_binomWeight_union_eq`, `sum_binomWeight_superset`, and `hspread`
  have hTerm2 :
      (F.card : ℚ)⁻¹ * (τ * F.card)⁻¹ * ∑ i ∈ G, ∑ W ∈ U.powerset,
        binomWeight U q W *
          ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
            (q ^ (A j).card)⁻¹ ≤
      τ⁻¹ * ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d := by
    -- Re-index each inner sum over `W` to `y = A i ∪ W`
    have hrew : ∑ i ∈ G, ∑ W ∈ U.powerset,
          binomWeight U q W *
            ∑ j ∈ G.filter (fun j => A j ⊆ A i ∪ W ∧ m ≤ (A i ∩ A j).card),
              (q ^ (A j).card)⁻¹ =
        ∑ i ∈ G, ∑ j ∈ G.filter (fun j => m ≤ (A i ∩ A j).card),
          (q ^ (A i ∩ A j).card)⁻¹ := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [sum_binomWeight_union_eq U (A i) (hAU i hi) hq0.ne'
        (fun y => ∑ j ∈ G.filter (fun j => A j ⊆ y ∧ m ≤ (A i ∩ A j).card),
          (q ^ (A j).card)⁻¹)]
      -- Swap `y` and `j`
      have h1 : ∑ y ∈ U.powerset.filter (fun y => A i ⊆ y),
            binomWeight U q y * (q ^ (A i).card)⁻¹ *
              ∑ j ∈ G.filter (fun j => A j ⊆ y ∧ m ≤ (A i ∩ A j).card), (q ^ (A j).card)⁻¹ =
          ∑ y ∈ U.powerset,
            ∑ j ∈ G.filter (fun j => m ≤ (A i ∩ A j).card),
              (if A i ∪ A j ⊆ y then
                binomWeight U q y * (q ^ (A i).card)⁻¹ * (q ^ (A j).card)⁻¹
               else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        by_cases hAi : A i ⊆ y
        · simp only [hAi, ↓reduceIte, Finset.mul_sum]
          have hsub : G.filter (fun j => A j ⊆ y ∧ m ≤ (A i ∩ A j).card) =
              (G.filter (fun j => m ≤ (A i ∩ A j).card)).filter (fun j => A j ⊆ y) := by
            ext j; simp only [Finset.mem_filter]; tauto
          rw [hsub, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hiff : A j ⊆ y ↔ A i ∪ A j ⊆ y := by
            simp [Finset.union_subset_iff, hAi]
          simp only [hiff]
        · simp only [hAi, ↓reduceIte]
          symm
          refine Finset.sum_eq_zero (fun j _ => ?_)
          have hnot : ¬ (A i ∪ A j ⊆ y) := fun h => hAi (Finset.subset_union_left.trans h)
          simp [hnot]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjG : j ∈ G := (Finset.mem_filter.mp hj).1
      rw [← Finset.sum_filter]
      have hpull : ∑ y ∈ U.powerset.filter (fun y => A i ∪ A j ⊆ y),
            binomWeight U q y * (q ^ (A i).card)⁻¹ * (q ^ (A j).card)⁻¹ =
          (∑ y ∈ U.powerset.filter (fun y => A i ∪ A j ⊆ y), binomWeight U q y) *
            ((q ^ (A i).card)⁻¹ * (q ^ (A j).card)⁻¹) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun y _ => by ring)
      rw [hpull, sum_binomWeight_superset U (A i ∪ A j)
            (Finset.union_subset (hAU i hi) (hAU j hjG)) q]
      have hcard_ui : (A i ∪ A j).card + (A i ∩ A j).card = (A i).card + (A j).card :=
        Finset.card_union_add_card_inter (A i) (A j)
      have hpow_eq : q ^ (A i ∪ A j).card * q ^ (A i ∩ A j).card =
          q ^ (A i).card * q ^ (A j).card := by
        rw [← pow_add, ← pow_add, hcard_ui]
      have hqi : q ^ (A i).card ≠ 0 := pow_ne_zero _ hq0.ne'
      have hqj : q ^ (A j).card ≠ 0 := pow_ne_zero _ hq0.ne'
      have hqij : q ^ (A i ∩ A j).card ≠ 0 := pow_ne_zero _ hq0.ne'
      have hmul : q ^ (A i ∪ A j).card * ((q ^ (A i).card)⁻¹ * (q ^ (A j).card)⁻¹) *
          q ^ (A i ∩ A j).card = 1 := by
        calc q ^ (A i ∪ A j).card * ((q ^ (A i).card)⁻¹ * (q ^ (A j).card)⁻¹) *
              q ^ (A i ∩ A j).card
            = (q ^ (A i ∪ A j).card * q ^ (A i ∩ A j).card) *
              ((q ^ (A i).card)⁻¹ * (q ^ (A j).card)⁻¹) := by ring
          _ = (q ^ (A i).card * q ^ (A j).card) *
              ((q ^ (A i).card)⁻¹ * (q ^ (A j).card)⁻¹) := by rw [hpow_eq]
          _ = 1 := by field_simp [hqi, hqj]
      exact eq_inv_of_mul_eq_one_left hmul
    rw [hrew]
    -- Now bound each `i ∈ G` via `hspread`
    have hper_i : ∀ i ∈ G,
        ∑ j ∈ G.filter (fun j => m ≤ (A i ∩ A j).card), (q ^ (A i ∩ A j).card)⁻¹ ≤
        (F.card : ℚ) * ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d := by
      intro i hi
      have hmaps : ∀ j ∈ G.filter (fun j => m ≤ (A i ∩ A j).card),
          (A i ∩ A j).card ∈ Finset.Icc m a := by
        intro j hj
        exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_filter.mp hj).2,
           (Finset.card_le_card Finset.inter_subset_left).trans (hAcard i hi)⟩
      rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
      refine Finset.sum_le_sum (fun d _hd => ?_)
      have hfib_sum :
          ∑ j ∈ (G.filter (fun j => m ≤ (A i ∩ A j).card)).filter
              (fun j => (A i ∩ A j).card = d), (q ^ (A i ∩ A j).card)⁻¹ =
          ((G.filter (fun j => m ≤ (A i ∩ A j).card ∧ (A i ∩ A j).card = d)).card : ℚ) *
            (q ^ d)⁻¹ := by
        rw [Finset.filter_filter]
        have hconst : ∀ j ∈ G.filter (fun j => m ≤ (A i ∩ A j).card ∧ (A i ∩ A j).card = d),
            (q ^ (A i ∩ A j).card)⁻¹ = (q ^ d)⁻¹ := fun j hj => by
          rw [(Finset.mem_filter.mp hj).2.2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      rw [hfib_sum]
      -- Count `j ∈ G` with `|A i ∩ A j| = d` by summing over `Z ∈ powersetCard d (A i)`
      have hcnt :
          ((G.filter (fun j => m ≤ (A i ∩ A j).card ∧ (A i ∩ A j).card = d)).card : ℚ) ≤
          ∑ Z ∈ (A i).powersetCard d, ((F.filter (fun S => Z ⊆ S)).card : ℚ) := by
        rw [← Nat.cast_sum]
        norm_cast
        calc (G.filter (fun j => m ≤ (A i ∩ A j).card ∧ (A i ∩ A j).card = d)).card
            ≤ ((A i).powersetCard d |>.biUnion (fun Z => F.filter (fun S => Z ⊆ S))).card := by
              refine Finset.card_le_card (fun j hj => ?_)
              rcases Finset.mem_filter.mp hj with ⟨hjG, _, hcardd⟩
              refine Finset.mem_biUnion.mpr ⟨A i ∩ A j, ?_, ?_⟩
              · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hcardd⟩
              · exact Finset.mem_filter.mpr
                  ⟨hGF hjG, Finset.inter_subset_right.trans (hAsub j hjG)⟩
          _ ≤ ∑ Z ∈ (A i).powersetCard d, (F.filter (fun S => Z ⊆ S)).card :=
              Finset.card_biUnion_le
      have hsp_sum :
          ∑ Z ∈ (A i).powersetCard d, ((F.filter (fun S => Z ⊆ S)).card : ℚ) ≤
          (Nat.choose a d : ℚ) * ((R : ℚ)⁻¹ ^ d * F.card) := by
        calc ∑ Z ∈ (A i).powersetCard d, ((F.filter (fun S => Z ⊆ S)).card : ℚ)
            ≤ ∑ _Z ∈ (A i).powersetCard d, ((R : ℚ)⁻¹ ^ d * F.card) := by
              refine Finset.sum_le_sum (fun Z hZ => ?_)
              rcases Finset.mem_powersetCard.mp hZ with ⟨hZAi, hZd⟩
              have hZU : Z ⊆ U := hZAi.trans (hAU i hi)
              simpa [hZd] using hspread Z hZU
          _ = (((A i).powersetCard d).card : ℚ) * ((R : ℚ)⁻¹ ^ d * F.card) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = (Nat.choose (A i).card d : ℚ) * ((R : ℚ)⁻¹ ^ d * F.card) := by
              rw [Finset.card_powersetCard]
          _ ≤ (Nat.choose a d : ℚ) * ((R : ℚ)⁻¹ ^ d * F.card) := by
              refine mul_le_mul_of_nonneg_right ?_
                (mul_nonneg (pow_nonneg (inv_nonneg.mpr hR0.le) _) hFpos.le)
              exact_mod_cast Nat.choose_le_choose d (hAcard i hi)
      have hqinv : 0 ≤ (q ^ d)⁻¹ := inv_nonneg.mpr (pow_nonneg hq0.le _)
      calc ((G.filter (fun j => m ≤ (A i ∩ A j).card ∧ (A i ∩ A j).card = d)).card : ℚ) *
              (q ^ d)⁻¹
          ≤ ((Nat.choose a d : ℚ) * ((R : ℚ)⁻¹ ^ d * F.card)) * (q ^ d)⁻¹ :=
            mul_le_mul_of_nonneg_right (hcnt.trans hsp_sum) hqinv
        _ = (F.card : ℚ) * ((Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d) := by
            rw [mul_inv, mul_pow, inv_pow]
            ring
    have hsumG :
        ∑ i ∈ G, ∑ j ∈ G.filter (fun j => m ≤ (A i ∩ A j).card), (q ^ (A i ∩ A j).card)⁻¹ ≤
        (F.card : ℚ) * ((F.card : ℚ) *
          ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d) := by
      have hG_le_F : (G.card : ℚ) ≤ F.card := Nat.cast_le.mpr (Finset.card_le_card hGF)
      have hSnonneg : 0 ≤ (F.card : ℚ) *
          ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d :=
        mul_nonneg hFpos.le (Finset.sum_nonneg (fun d _ =>
          mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (mul_pos hq0 hR0).le) _)))
      calc ∑ i ∈ G, ∑ j ∈ G.filter (fun j => m ≤ (A i ∩ A j).card), (q ^ (A i ∩ A j).card)⁻¹
          ≤ ∑ _i ∈ G, ((F.card : ℚ) *
              ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d) :=
            Finset.sum_le_sum hper_i
        _ = (G.card : ℚ) * ((F.card : ℚ) *
              ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (F.card : ℚ) * ((F.card : ℚ) *
              ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d) :=
            mul_le_mul_of_nonneg_right hG_le_F hSnonneg
    have hcoef_nonneg : 0 ≤ (F.card : ℚ)⁻¹ * (τ * F.card)⁻¹ :=
      mul_nonneg (inv_nonneg.mpr hFpos.le) (inv_nonneg.mpr (mul_pos hτ0 hFpos).le)
    calc (F.card : ℚ)⁻¹ * (τ * F.card)⁻¹ *
            ∑ i ∈ G, ∑ j ∈ G.filter (fun j => m ≤ (A i ∩ A j).card), (q ^ (A i ∩ A j).card)⁻¹
        ≤ (F.card : ℚ)⁻¹ * (τ * F.card)⁻¹ *
            ((F.card : ℚ) * ((F.card : ℚ) *
              ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d)) :=
          mul_le_mul_of_nonneg_left hsumG hcoef_nonneg
      _ = τ⁻¹ * ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d := by
          field_simp [hFpos.ne', hτ0.ne']
  linarith

/-- Upper half of binomial coefficients sums to at most `2 ^ (a - 1)`. -/
private lemma sum_choose_upper_half_le (a : ℕ) (ha : 1 ≤ a) :
    ∑ d ∈ Finset.Icc (a / 2 + 1) a, Nat.choose a d ≤ 2 ^ (a - 1) := by
  have hsym : ∑ d ∈ Finset.Icc (a / 2 + 1) a, Nat.choose a d =
      ∑ d ∈ Finset.Icc 0 (a - (a / 2 + 1)), Nat.choose a d := by
    refine Finset.sum_bij (fun d _ => a - d) ?_ ?_ ?_ ?_
    · intro d hd
      rcases Finset.mem_Icc.mp hd with ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
    · intro d₁ hd₁ d₂ hd₂ hEq
      have h1 : d₁ ≤ a := (Finset.mem_Icc.mp hd₁).2
      have h2 : d₂ ≤ a := (Finset.mem_Icc.mp hd₂).2
      omega
    · intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨_, hk2⟩
      refine ⟨a - k, Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le a k⟩, by omega⟩
    · intro d hd
      exact (Nat.choose_symm (Finset.mem_Icc.mp hd).2).symm
  have hdisj : Disjoint (Finset.Icc 0 (a - (a / 2 + 1))) (Finset.Icc (a / 2 + 1) a) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_Icc.mp hx1).2
    have h2 := (Finset.mem_Icc.mp hx2).1
    omega
  have hsub : Finset.Icc 0 (a - (a / 2 + 1)) ∪ Finset.Icc (a / 2 + 1) a ⊆ Finset.range (a + 1) := by
    intro x hx
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hx with h1 | h2
    · have := (Finset.mem_Icc.mp h1).2; omega
    · have := (Finset.mem_Icc.mp h2).2; omega
  have h2sum : 2 * ∑ d ∈ Finset.Icc (a / 2 + 1) a, Nat.choose a d ≤ 2 ^ a := by
    calc 2 * ∑ d ∈ Finset.Icc (a / 2 + 1) a, Nat.choose a d
        = ∑ d ∈ Finset.Icc 0 (a - (a / 2 + 1)), Nat.choose a d +
          ∑ d ∈ Finset.Icc (a / 2 + 1) a, Nat.choose a d := by rw [← hsym]; ring
      _ = ∑ d ∈ Finset.Icc 0 (a - (a / 2 + 1)) ∪ Finset.Icc (a / 2 + 1) a, Nat.choose a d :=
          (Finset.sum_union hdisj).symm
      _ ≤ ∑ d ∈ Finset.range (a + 1), Nat.choose a d :=
          Finset.sum_le_sum_of_subset hsub
      _ = 2 ^ a := Nat.sum_range_choose a
  have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_succ']
  omega

/-- Clean rational bound for one halving step when `q * R ≥ 36`:
- For `a = 1`, error ≤ `1 / 3` (with `τ = 1 / 6`).
- For `a ≥ 2`, `m = a / 2 + 1`, error ≤ `(1 / 3) ^ m` (with `τ = (1 / 2) * (1 / 3) ^ m`). -/
private lemma halving_step_rational_bound (a : ℕ) (ha : 1 ≤ a) {q R : ℚ}
    (hq0 : 0 < q) (hR0 : 0 < R) (hqR : 36 ≤ q * R) :
    ∃ τ : ℚ, 0 < τ ∧
      τ + τ⁻¹ * ∑ d ∈ Finset.Icc (a / 2 + 1) a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d ≤
        (1 / 3 : ℚ) ^ (a / 2 + 1) := by
  have hqRinv_le : (q * R)⁻¹ ≤ (1 / 36 : ℚ) := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hqR
  have hqRinv_pos : 0 < (q * R)⁻¹ := inv_pos.mpr (mul_pos hq0 hR0)
  by_cases ha1 : a = 1
  · subst ha1
    refine ⟨1 / 6, by norm_num, ?_⟩
    have hIcc : Finset.Icc (1 / 2 + 1) 1 = {1} := by decide
    rw [hIcc, Finset.sum_singleton]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, pow_one]
    have hdiv : (1 / 2 + 1 : ℕ) = 1 := by decide
    rw [hdiv, pow_one]
    linarith
  · have ha2 : 2 ≤ a := by omega
    let m : ℕ := a / 2 + 1
    have h2m : a - 1 ≤ 2 * m - 2 := by omega
    have htail :
        ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d ≤
        (1 / 4 : ℚ) * (1 / 9 : ℚ) ^ m := by
      have h1 : ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d ≤
          ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (1 / 36 : ℚ) ^ m := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hdm : m ≤ d := (Finset.mem_Icc.mp hd).1
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc (q * R)⁻¹ ^ d ≤ (1 / 36 : ℚ) ^ d := pow_le_pow_left₀ hqRinv_pos.le hqRinv_le d
          _ ≤ (1 / 36 : ℚ) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hdm
      have h2 : ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) ≤ (2 : ℚ) ^ (a - 1) := by
        rw [← Nat.cast_sum]
        exact_mod_cast sum_choose_upper_half_le a ha
      have h3 : (2 : ℚ) ^ (a - 1) ≤ (1 / 4 : ℚ) * (4 : ℚ) ^ m := by
        have hm1 : 1 ≤ m := by omega
        have hpow4 : (4 : ℚ) ^ m = 4 * (2 : ℚ) ^ (2 * m - 2) := by
          have : (4 : ℚ) ^ m = 4 * (4 : ℚ) ^ (m - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel hm1, pow_succ']
          rw [this]
          congr 1
          rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, ← pow_mul,
              show 2 * (m - 1) = 2 * m - 2 by omega]
        rw [hpow4]
        have hpow2 : (2 : ℚ) ^ (a - 1) ≤ (2 : ℚ) ^ (2 * m - 2) :=
          pow_le_pow_right₀ (by norm_num) h2m
        linarith
      calc ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d
          ≤ (∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ)) * (1 / 36 : ℚ) ^ m := by
            rw [Finset.sum_mul]; exact h1
        _ ≤ ((1 / 4 : ℚ) * (4 : ℚ) ^ m) * (1 / 36 : ℚ) ^ m :=
            mul_le_mul_of_nonneg_right (h2.trans h3) (by positivity)
        _ = (1 / 4 : ℚ) * (1 / 9 : ℚ) ^ m := by
            rw [mul_assoc, ← mul_pow]
            norm_num
    refine ⟨(1 / 2 : ℚ) * (1 / 3 : ℚ) ^ m, by positivity, ?_⟩
    have hτinv : ((1 / 2 : ℚ) * (1 / 3 : ℚ) ^ m)⁻¹ * ((1 / 4 : ℚ) * (1 / 9 : ℚ) ^ m) =
        (1 / 2 : ℚ) * (1 / 3 : ℚ) ^ m := by
      have hne : (1 / 3 : ℚ) ^ m ≠ 0 := by positivity
      have h9 : (1 / 9 : ℚ) ^ m = (1 / 3 : ℚ) ^ m * (1 / 3 : ℚ) ^ m := by
        rw [← mul_pow]; norm_num
      rw [h9]
      field_simp [hne]
      ring
    have hmul : ((1 / 2 : ℚ) * (1 / 3 : ℚ) ^ m)⁻¹ *
          ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d ≤
        (1 / 2 : ℚ) * (1 / 3 : ℚ) ^ m := by
      calc ((1 / 2 : ℚ) * (1 / 3 : ℚ) ^ m)⁻¹ *
            ∑ d ∈ Finset.Icc m a, (Nat.choose a d : ℚ) * (q * R)⁻¹ ^ d
          ≤ ((1 / 2 : ℚ) * (1 / 3 : ℚ) ^ m)⁻¹ * ((1 / 4 : ℚ) * (1 / 9 : ℚ) ^ m) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ = (1 / 2 : ℚ) * (1 / 3 : ℚ) ^ m := hτinv
    linarith

/-- Number of halving rounds `a ↦ a / 2` to reach `0`: `0` if `a = 0`, else `Nat.log 2 a + 1`. -/
private def halvingSteps (a : ℕ) : ℕ :=
  if a = 0 then 0 else Nat.log 2 a + 1

private lemma halvingSteps_succ {a : ℕ} (ha : 1 ≤ a) :
    halvingSteps (a / 2) + 1 = halvingSteps a := by
  by_cases ha1 : a = 1
  · subst ha1; simp [halvingSteps]
  · have ha2 : 2 ≤ a := by omega
    have hdiv_pos : a / 2 ≠ 0 := by omega
    unfold halvingSteps
    simp only [hdiv_pos, ↓reduceIte, show a ≠ 0 by omega]
    have hlog : Nat.log 2 a = Nat.log 2 (a / 2) + 1 := Nat.log_of_one_lt_of_le (by omega) ha2
    omega

/-- Effective union probability of `t` independent `q`-biased layers: `1 - (1 - q)^t`. -/
private def unionProb (q : ℚ) (t : ℕ) : ℚ := 1 - (1 - q) ^ t

private lemma unionProb_succ (q : ℚ) (t : ℕ) :
    unionProb q t + q - unionProb q t * q = unionProb q (t + 1) := by
  unfold unionProb; rw [pow_succ]; ring

private lemma unionProb_le_mul {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t : ℕ) :
    unionProb q t ≤ (t : ℚ) * q := by
  induction t with
  | zero => simp [unionProb]
  | succ t ih =>
    rw [← unionProb_succ, Nat.cast_add, Nat.cast_one]
    have hnonneg : 0 ≤ unionProb q t := by
      unfold unionProb
      have h1 : (1 - q) ^ t ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hq1) (by linarith)
      linarith
    nlinarith

private lemma unionProb_bounds {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t : ℕ) :
    0 ≤ unionProb q t ∧ unionProb q t ≤ 1 := by
  unfold unionProb
  have h0 : 0 ≤ (1 - q) ^ t := pow_nonneg (sub_nonneg.mpr hq1) t
  have h1 : (1 - q) ^ t ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hq1) (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- **Inductive Halving Peeling Lemma:**
Given an `R`-spread family `F` and a good subfamily `G ⊆ F` with residual sets `A i ⊆ i`
of size `≤ a` (where `A i ∪ W₀` contains a member of `F` for every `i ∈ G`),
sampling `t = halvingSteps a` independent `q`-biased layers (`q * R ≥ 36`) produces
a random subset `W` (with marginal `unionProb q t`) such that the expected fraction of
sets failing to be covered by `W₀ ∪ W` is at most
`(F.card - G.card) / F.card + (if a = 0 then 0 else 1/2 - 1/(2 * 3^a))`. -/
private lemma iterated_halving_peeling {α : Type*} [DecidableEq α]
    (U : Finset α) (F : Finset (Finset α)) {q R : ℚ}
    (hFne : F.Nonempty)
    (hspread : ∀ Z ⊆ U, ((F.filter (fun S => Z ⊆ S)).card : ℚ) ≤ (R : ℚ)⁻¹ ^ Z.card * F.card)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hR0 : 0 < R) (hqR : 36 ≤ q * R) :
    ∀ a : ℕ, ∀ (G : Finset (Finset α)) (A : Finset α → Finset α) (W₀ : Finset α),
      G ⊆ F →
      (∀ i ∈ G, A i ⊆ i) →
      (∀ i ∈ G, A i ⊆ U) →
      (∀ i ∈ G, (A i).card ≤ a) →
      (∀ i ∈ G, ∃ S ∈ F, S ⊆ A i ∪ W₀) →
      ∑ W ∈ U.powerset, binomWeight U (unionProb q (halvingSteps a)) W *
          (if ∀ S ∈ F, ¬ (S ⊆ W₀ ∪ W) then (1 : ℚ) else 0) ≤
        ((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ) +
        (if a = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ a)) := by
  classical
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro G A W₀ hGF hAsub hAU hAcard hAcov
    have hFpos : (0 : ℚ) < F.card := Nat.cast_pos.mpr hFne.card_pos
    by_cases ha0 : a = 0
    · subst ha0
      simp only [halvingSteps, ↓reduceIte, unionProb, pow_zero, sub_self, add_zero]
      -- If G is nonempty, pick i ∈ G; then A i = ∅ so W₀ already contains some S ∈ F!
      by_cases hGne : G.Nonempty
      · obtain ⟨i, hiG⟩ := hGne
        have hAe : A i = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hAcard i hiG))
        obtain ⟨S, hSF, hSW₀⟩ := hAcov i hiG
        rw [hAe, Finset.empty_union] at hSW₀
        have hzero : ∑ W ∈ U.powerset, binomWeight U 0 W *
            (if ∀ S ∈ F, ¬ (S ⊆ W₀ ∪ W) then (1 : ℚ) else 0) = 0 := by
          refine Finset.sum_eq_zero (fun W _ => ?_)
          have hfalse : ¬ (∀ S' ∈ F, ¬ (S' ⊆ W₀ ∪ W)) := by
            push Not; exact ⟨S, hSF, hSW₀.trans Finset.subset_union_left⟩
          simp [hfalse]
        rw [hzero]
        positivity
      · rw [Finset.not_nonempty_iff_eq_empty] at hGne
        subst hGne
        simp only [Finset.card_empty, Nat.sub_zero, div_self hFpos.ne']
        calc ∑ W ∈ U.powerset, binomWeight U 0 W *
              (if ∀ S ∈ F, ¬ (S ⊆ W₀ ∪ W) then (1 : ℚ) else 0)
            ≤ ∑ W ∈ U.powerset, binomWeight U 0 W * 1 := by
              refine Finset.sum_le_sum (fun W _ => ?_)
              refine mul_le_mul_of_nonneg_left ?_ (binomWeight_nonneg U le_rfl (by norm_num) W)
              split_ifs <;> norm_num
          _ = 1 := by simp [sum_binomWeight_powerset]
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      let b : ℕ := a / 2
      have hba : b < a := Nat.div_lt_self ha1 (by norm_num)
      have hsteps : halvingSteps b + 1 = halvingSteps a := halvingSteps_succ ha1
      -- Split `unionProb q (halvingSteps a)` into `W₁ ~ Bin(U, q)` followed by `W₂ ~ Bin(U, unionProb q (halvingSteps b))`
      have hprob_eq : q + unionProb q (halvingSteps b) - q * unionProb q (halvingSteps b) =
          unionProb q (halvingSteps a) := by
        rw [← hsteps, ← unionProb_succ]; ring
      rw [← hprob_eq, ← sum_binomWeight_union_indep]
      -- For each W₁ ∈ U.powerset, define G₁(W₁) and A₁(W₁)
      let bad (W₁ : Finset α) : Finset (Finset α) :=
        G.filter (fun i => ∀ j ∈ G, A j ⊆ A i ∪ W₁ → b + 1 ≤ (A j \ W₁).card)
      let G₁ (W₁ : Finset α) : Finset (Finset α) :=
        G.filter (fun i => ∃ j ∈ G, A j ⊆ A i ∪ W₁ ∧ (A j \ W₁).card ≤ b)
      have hdisj_G : ∀ W₁, G₁ W₁ ∪ bad W₁ = G ∧ Disjoint (G₁ W₁) (bad W₁) := by
        intro W₁
        constructor
        · ext i
          simp only [G₁, bad, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
          · intro hi
            by_cases h : ∃ j ∈ G, A j ⊆ A i ∪ W₁ ∧ (A j \ W₁).card ≤ b
            · exact Or.inl ⟨hi, h⟩
            · refine Or.inr ⟨hi, fun j hj hsub => ?_⟩
              push Not at h
              have := h j hj hsub
              omega
        · rw [Finset.disjoint_left]
          intro i hi1 hi2
          rcases (Finset.mem_filter.mp hi1).2 with ⟨j, hj, hsub, hle⟩
          have hge := (Finset.mem_filter.mp hi2).2 j hj hsub
          omega
      have hG₁_card : ∀ W₁, ((F.card - (G₁ W₁).card : ℕ) : ℚ) / (F.card : ℚ) =
          ((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ) + ((bad W₁).card : ℚ) / (F.card : ℚ) := by
        intro W₁
        have hsum : (G₁ W₁).card + (bad W₁).card = G.card := by
          rw [← Finset.card_union_of_disjoint (hdisj_G W₁).2, (hdisj_G W₁).1]
        have hG_le_F : G.card ≤ F.card := Finset.card_le_card hGF
        have hG1_le_F : (G₁ W₁).card ≤ F.card := by omega
        have hnat : F.card - (G₁ W₁).card = (F.card - G.card) + (bad W₁).card := by omega
        rw [hnat, Nat.cast_add, add_div]
      -- Apply IH for each fixed W₁ ∈ U.powerset
      have hper_W1 : ∀ W₁ ∈ U.powerset,
          ∑ W₂ ∈ U.powerset, binomWeight U (unionProb q (halvingSteps b)) W₂ *
            (if ∀ S ∈ F, ¬ (S ⊆ W₀ ∪ (W₁ ∪ W₂)) then (1 : ℚ) else 0) ≤
          ((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ) +
          ((bad W₁).card : ℚ) / (F.card : ℚ) +
          (if b = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ b)) := by
        intro W₁ _hW₁
        let A₁ : Finset α → Finset α := fun i =>
          if h : ∃ j ∈ G, A j ⊆ A i ∪ W₁ ∧ (A j \ W₁).card ≤ b
          then A (Classical.choose h) \ W₁
          else ∅
        have hG₁F : G₁ W₁ ⊆ F := (Finset.filter_subset _ G).trans hGF
        have hA₁sub : ∀ i ∈ G₁ W₁, A₁ i ⊆ i := by
          intro i hi
          have hex : ∃ j ∈ G, A j ⊆ A i ∪ W₁ ∧ (A j \ W₁).card ≤ b :=
            (Finset.mem_filter.mp hi).2
          simp only [A₁, hex, ↓reduceDIte]
          have hspec := Classical.choose_spec hex
          have hsub1 : A (Classical.choose hex) \ W₁ ⊆ A i := by
            intro x hx
            rcases Finset.mem_sdiff.mp hx with ⟨hxAj, hxW₁⟩
            rcases Finset.mem_union.mp (hspec.2.1 hxAj) with hxAi | hxW₁'
            · exact hxAi
            · exact (hxW₁ hxW₁').elim
          exact hsub1.trans (hAsub i (Finset.mem_filter.mp hi).1)
        have hA₁U : ∀ i ∈ G₁ W₁, A₁ i ⊆ U := by
          intro i hi
          have hex : ∃ j ∈ G, A j ⊆ A i ∪ W₁ ∧ (A j \ W₁).card ≤ b :=
            (Finset.mem_filter.mp hi).2
          simp only [A₁, hex, ↓reduceDIte]
          have hspec := Classical.choose_spec hex
          exact Finset.sdiff_subset.trans (hAU _ hspec.1)
        have hA₁card : ∀ i ∈ G₁ W₁, (A₁ i).card ≤ b := by
          intro i hi
          have hex : ∃ j ∈ G, A j ⊆ A i ∪ W₁ ∧ (A j \ W₁).card ≤ b :=
            (Finset.mem_filter.mp hi).2
          simp only [A₁, hex, ↓reduceDIte]
          exact (Classical.choose_spec hex).2.2
        have hA₁cov : ∀ i ∈ G₁ W₁, ∃ S ∈ F, S ⊆ A₁ i ∪ (W₀ ∪ W₁) := by
          intro i hi
          have hex : ∃ j ∈ G, A j ⊆ A i ∪ W₁ ∧ (A j \ W₁).card ≤ b :=
            (Finset.mem_filter.mp hi).2
          simp only [A₁, hex, ↓reduceDIte]
          have hspec := Classical.choose_spec hex
          obtain ⟨S, hSF, hScov⟩ := hAcov (Classical.choose hex) hspec.1
          refine ⟨S, hSF, hScov.trans ?_⟩
          intro x hx
          rcases Finset.mem_union.mp hx with hxAj | hxW₀
          · by_cases hxW₁ : x ∈ W₁
            · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxW₁)
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxAj, hxW₁⟩)
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxW₀)
        have hIH := ih b hba (G₁ W₁) A₁ (W₀ ∪ W₁) hG₁F hA₁sub hA₁U hA₁card hA₁cov
        have hassoc : ∀ W₂ : Finset α, W₀ ∪ (W₁ ∪ W₂) = (W₀ ∪ W₁) ∪ W₂ :=
          fun W₂ => (Finset.union_assoc W₀ W₁ W₂).symm
        simp_rw [hassoc]
        rw [hG₁_card W₁] at hIH
        exact hIH
      -- Average `hper_W1` over `W₁ ∈ U.powerset`
      have havg :
          ∑ W₁ ∈ U.powerset, binomWeight U q W₁ *
            (∑ W₂ ∈ U.powerset, binomWeight U (unionProb q (halvingSteps b)) W₂ *
              (if ∀ S ∈ F, ¬ (S ⊆ W₀ ∪ (W₁ ∪ W₂)) then (1 : ℚ) else 0)) ≤
          ((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ) +
          (∑ W₁ ∈ U.powerset, binomWeight U q W₁ * ((bad W₁).card : ℚ) / (F.card : ℚ)) +
          (if b = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ b)) := by
        have h1 :
            ∑ W₁ ∈ U.powerset, binomWeight U q W₁ *
              (∑ W₂ ∈ U.powerset, binomWeight U (unionProb q (halvingSteps b)) W₂ *
                (if ∀ S ∈ F, ¬ (S ⊆ W₀ ∪ (W₁ ∪ W₂)) then (1 : ℚ) else 0)) ≤
            ∑ W₁ ∈ U.powerset, binomWeight U q W₁ *
              (((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ) +
               ((bad W₁).card : ℚ) / (F.card : ℚ) +
               (if b = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ b))) :=
          Finset.sum_le_sum (fun W₁ hW₁ =>
            mul_le_mul_of_nonneg_left (hper_W1 W₁ hW₁) (binomWeight_nonneg U hq0.le hq1 W₁))
        have h2 :
            ∑ W₁ ∈ U.powerset, binomWeight U q W₁ *
              (((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ) +
               ((bad W₁).card : ℚ) / (F.card : ℚ) +
               (if b = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ b))) =
            ((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ) +
            (∑ W₁ ∈ U.powerset, binomWeight U q W₁ * ((bad W₁).card : ℚ) / (F.card : ℚ)) +
            (if b = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ b)) := by
          have hexp : ∀ W₁ : Finset α,
              binomWeight U q W₁ *
                (((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ) +
                 ((bad W₁).card : ℚ) / (F.card : ℚ) +
                 (if b = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ b))) =
              binomWeight U q W₁ * (((F.card - G.card : ℕ) : ℚ) / (F.card : ℚ)) +
              binomWeight U q W₁ * ((bad W₁).card : ℚ) / (F.card : ℚ) +
              binomWeight U q W₁ * (if b = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ b)) := by
            intro W₁; ring
          simp_rw [hexp, Finset.sum_add_distrib, ← Finset.sum_mul, sum_binomWeight_powerset,
            one_mul]
        exact h1.trans_eq h2
      -- Bound the bad-fraction expectation by `(1 / 3) ^ (b + 1)`
      obtain ⟨τ, hτ0, hτbound⟩ := halving_step_rational_bound a ha1 hq0 hR0 hqR
      have hbad_bound :
          ∑ W₁ ∈ U.powerset, binomWeight U q W₁ * ((bad W₁).card : ℚ) / (F.card : ℚ) ≤
          (1 / 3 : ℚ) ^ (b + 1) :=
        (one_step_bayesian_shrinkage U F G A hFne hGF hAsub hAU hAcard hspread
          hq0 hq1 hR0 hτ0).trans hτbound
      -- Combine `(1/3)^(b+1)` with the IH budget!
      have hcomb :
          (1 / 3 : ℚ) ^ (b + 1) +
            (if b = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ b)) ≤
          (if a = 0 then (0 : ℚ) else 1 / 2 - 1 / (2 * (3 : ℚ) ^ a)) := by
        simp only [ha0, ↓reduceIte]
        by_cases hb0 : b = 0
        · have ha1' : a = 1 := by omega
          simp only [hb0, ha1', ↓reduceIte]
          norm_num
        · simp only [hb0, ↓reduceIte]
          have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
          have hab : b + 1 ≤ a := by omega
          have hpow_ge : (1 : ℚ) ≤ (3 : ℚ) ^ (a - (b + 1)) :=
            one_le_pow₀ (by norm_num)
          have h3a : (3 : ℚ) ^ a = (3 : ℚ) ^ (b + 1) * (3 : ℚ) ^ (a - (b + 1)) := by
            rw [← pow_add, Nat.add_sub_of_le hab]
          have h3b1 : (3 : ℚ) ^ (b + 1) = 3 * (3 : ℚ) ^ b := by rw [pow_succ']
          have hpos_b : (0 : ℚ) < (3 : ℚ) ^ b := by positivity
          have hpos_a : (0 : ℚ) < (3 : ℚ) ^ a := by positivity
          have hpos_ab : (0 : ℚ) < (3 : ℚ) ^ (a - (b + 1)) := by positivity
          -- Need: 1 / 3^(b+1) + 1/2 - 1/(2 * 3^b) ≤ 1/2 - 1/(2 * 3^a)
          -- i.e. 1 / (2 * 3^a) + 1 / (3 * 3^b) ≤ 1 / (2 * 3^b)
          -- i.e. 1 / (2 * 3^a) ≤ 1 / (6 * 3^b) <=> 3 * 3^b ≤ 3^a
          have hle3 : 3 * (3 : ℚ) ^ b ≤ (3 : ℚ) ^ a := by
            rw [h3a, h3b1]
            nlinarith
          have hfrac : 1 / (2 * (3 : ℚ) ^ a) ≤ 1 / (6 * (3 : ℚ) ^ b) := by
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
          have h13 : (1 / 3 : ℚ) ^ (b + 1) = 1 / (3 * (3 : ℚ) ^ b) := by
            rw [one_div_pow, h3b1]
          rw [h13]
          have hdiff : 1 / (2 * (3 : ℚ) ^ b) - 1 / (3 * (3 : ℚ) ^ b) = 1 / (6 * (3 : ℚ) ^ b) := by
            field_simp [hpos_b.ne']; ring
          linarith
      linarith

/-- **The Spread Lemma (Pure-Mathlib Elementary Bayesian Form):**
Let `F` be a nonempty `R`-spread family of subsets of a finite ground set `U`, each of size `≤ n`
(with `n ≥ 1`). For any rational `p ∈ (0, 1]` satisfying `36 * (Nat.log 2 n + 1) ≤ p * R`,
the `p`-biased probability that a random subset `W ⊆ U` contains a member of `F` is
strictly greater than `1 / 2` (in fact `≥ 1 / 2 + 1 / (2 * 3 ^ n)`). -/
theorem ppl038_spread_lemma {α : Type*} [DecidableEq α]
    (U : Finset α) (F : Finset (Finset α)) {n : ℕ} {p R : ℚ}
    (hn : 1 ≤ n) (hFne : F.Nonempty)
    (hFU : ∀ S ∈ F, S ⊆ U)
    (hFcard : ∀ S ∈ F, S.card ≤ n)
    (hspread : ∀ Z ⊆ U, ((F.filter (fun S => Z ⊆ S)).card : ℚ) ≤ (R : ℚ)⁻¹ ^ Z.card * F.card)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hR0 : 0 < R)
    (hpR : (36 * (Nat.log 2 n + 1) : ℚ) ≤ p * R) :
    (1 / 2 : ℚ) + 1 / (2 * (3 : ℚ) ^ n) ≤
      ∑ W ∈ U.powerset,
        p ^ W.card * (1 - p) ^ (U.card - W.card) *
          (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0) := by
  classical
  let t : ℕ := halvingSteps n
  have ht_eq : t = Nat.log 2 n + 1 := by
    simp [t, halvingSteps, show n ≠ 0 by omega]
  have ht_pos : (0 : ℚ) < t := by
    rw [ht_eq]; positivity
  let q : ℚ := p / (t : ℚ)
  have hq0 : 0 < q := div_pos hp0 ht_pos
  have ht_ge1 : (1 : ℚ) ≤ t := by
    rw [ht_eq]; norm_cast; omega
  have hq1 : q ≤ 1 := (div_le_one ht_pos).mpr (hp1.trans ht_ge1)
  have hqR : 36 ≤ q * R := by
    dsimp only [q]
    rw [div_mul_eq_mul_div, le_div_iff₀ ht_pos]
    rw [ht_eq]
    push_cast
    linarith
  have hpeel := iterated_halving_peeling U F hFne hspread hq0 hq1 hR0 hqR
    n F id ∅ (Finset.Subset.refl F) (fun _ _ => Finset.Subset.refl _) hFU hFcard
    (fun i hi => ⟨i, hi, by simp⟩)
  simp only [Nat.sub_self, Nat.cast_zero, zero_div, zero_add,
    show n ≠ 0 by omega, ↓reduceIte, Finset.empty_union] at hpeel
  -- Convert miss probability at `unionProb q t` to hit probability at `unionProb q t`
  have hhit_u :
      (1 / 2 : ℚ) + 1 / (2 * (3 : ℚ) ^ n) ≤
      ∑ W ∈ U.powerset, binomWeight U (unionProb q t) W *
        (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0) := by
    have hcomp :
        ∑ W ∈ U.powerset, binomWeight U (unionProb q t) W *
          (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0) +
        ∑ W ∈ U.powerset, binomWeight U (unionProb q t) W *
          (if ∀ S ∈ F, ¬ (S ⊆ W) then (1 : ℚ) else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ W ∈ U.powerset,
          binomWeight U (unionProb q t) W * (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0) +
          binomWeight U (unionProb q t) W * (if ∀ S ∈ F, ¬ (S ⊆ W) then (1 : ℚ) else 0) =
          binomWeight U (unionProb q t) W := by
        intro W _
        by_cases h : ∃ S ∈ F, S ⊆ W
        · have hnot : ¬ (∀ S ∈ F, ¬ (S ⊆ W)) := by push Not; exact h
          simp [h, hnot]
        · have hall : ∀ S ∈ F, ¬ (S ⊆ W) := by push Not at h; exact h
          simp [h]
      rw [Finset.sum_congr rfl hterm, sum_binomWeight_powerset]
    linarith
  -- Monotonicity from `unionProb q t ≤ t * q = p` up to `p`
  have hu_le_p : unionProb q t ≤ p := by
    calc unionProb q t ≤ (t : ℚ) * q := unionProb_le_mul hq0.le hq1 t
      _ = p := by dsimp only [q]; field_simp [ht_pos.ne']
  have hu0 : 0 ≤ unionProb q t := (unionProb_bounds hq0.le hq1 t).1
  have hmono := binomWeight_mono_prob U hu0 hu_le_p hp1
    (fun W => ∃ S ∈ F, S ⊆ W) (fun A B hAB ⟨S, hSF, hSA⟩ => ⟨S, hSF, hSA.trans hAB⟩)
  exact hhit_u.trans hmono

/-- From the Spread Lemma to `r` pairwise disjoint sets via `M`-coloring averaging.
Requires `r ≤ M` and `(M : ℚ) * (1 / 2) ≥ r - 1` (e.g., `M = 2 * r - 1`, or `M = 4` for `r = 3`). -/
private lemma spread_exists_disjoint_sets {α : Type*} [DecidableEq α]
    (U : Finset α) (F : Finset (Finset α)) {n r M : ℕ} {R : ℚ}
    (hn : 1 ≤ n) (hFne : F.Nonempty) (hMpos : 1 ≤ M) (hMr : 2 * (r - 1) ≤ M)
    (hFU : ∀ S ∈ F, S ⊆ U)
    (hFcard : ∀ S ∈ F, S.card ≤ n)
    (hFnonempty : ∀ S ∈ F, S.Nonempty)
    (hspread : ∀ Z ⊆ U, ((F.filter (fun S => Z ⊆ S)).card : ℚ) ≤ (R : ℚ)⁻¹ ^ Z.card * F.card)
    (hR0 : 0 < R)
    (hR : (36 * M * (Nat.log 2 n + 1) : ℚ) ≤ R) :
    ∃ G ⊆ F, G.card = r ∧ (G : Set (Finset α)).PairwiseDisjoint id := by
  classical
  have hMpos_q : (0 : ℚ) < M := Nat.cast_pos.mpr (by omega)
  have hp0 : (0 : ℚ) < (M : ℚ)⁻¹ := inv_pos.mpr hMpos_q
  have hp1 : (M : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hMpos)
  have hpR : (36 * (Nat.log 2 n + 1) : ℚ) ≤ (M : ℚ)⁻¹ * R := by
    rw [inv_mul_eq_div, le_div_iff₀ hMpos_q]
    linarith
  have hsp := ppl038_spread_lemma U F hn hFne hFU hFcard hspread hp0 hp1 hR0 hpR
  have hstrict : (1 / 2 : ℚ) <
      ∑ W ∈ U.powerset, binomWeight U (M : ℚ)⁻¹ W *
        (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0) := by
    have hpos : (0 : ℚ) < 1 / (2 * (3 : ℚ) ^ n) := by positivity
    unfold binomWeight
    linarith
  -- Sum over all colors `c : Fin M` and all colorings `f : U → Fin M`
  let hitCount (f : {x // x ∈ U} → Fin M) : ℕ :=
    (Finset.univ.filter (fun c : Fin M =>
      ∃ S ∈ F, S ⊆ (U.attach.filter (fun x => f x = c)).image Subtype.val)).card
  have htotal : ((r - 1 : ℕ) : ℚ) * (M : ℚ) ^ U.card <
      ∑ f : {x // x ∈ U} → Fin M, (hitCount f : ℚ) := by
    have hrewrite : ∑ f : {x // x ∈ U} → Fin M, (hitCount f : ℚ) =
        ∑ c : Fin M, ∑ f : {x // x ∈ U} → Fin M,
          (if ∃ S ∈ F, S ⊆ (U.attach.filter (fun x => f x = c)).image Subtype.val
           then (1 : ℚ) else 0) := by
      have hhc : ∀ f, (hitCount f : ℚ) =
          ∑ c : Fin M,
            (if ∃ S ∈ F, S ⊆ (U.attach.filter (fun x => f x = c)).image Subtype.val
             then (1 : ℚ) else 0) := fun f => by
        dsimp only [hitCount]; rw [Finset.sum_boole]
      simp_rw [hhc]
      rw [Finset.sum_comm]
    rw [hrewrite]
    have hper_c : ∀ c : Fin M,
        ∑ f : {x // x ∈ U} → Fin M,
          (if ∃ S ∈ F, S ⊆ (U.attach.filter (fun x => f x = c)).image Subtype.val
           then (1 : ℚ) else 0) =
        (M : ℚ) ^ U.card * ∑ W ∈ U.powerset, binomWeight U (M : ℚ)⁻¹ W *
          (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0) := fun c =>
      sum_colorings_eq_binomWeight U hMpos c (fun W => if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0)
    simp_rw [hper_c]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hMpow_pos : (0 : ℚ) < (M : ℚ) ^ U.card := by positivity
    have hMr_q : ((r - 1 : ℕ) : ℚ) ≤ (M : ℚ) * (1 / 2) := by
      have : (2 : ℚ) * ((r - 1 : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hMr
      linarith
    have hstep1 : (M : ℚ) * ((M : ℚ) ^ U.card * (1 / 2 : ℚ)) <
        (M : ℚ) * ((M : ℚ) ^ U.card * ∑ W ∈ U.powerset, binomWeight U (M : ℚ)⁻¹ W *
          (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0)) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hstrict hMpow_pos) hMpos_q
    nlinarith
  -- Pigeonhole: there exists a coloring `f` with `r ≤ hitCount f`
  have hex_f : ∃ f : {x // x ∈ U} → Fin M, r ≤ hitCount f := by
    by_contra hall
    push Not at hall
    have hle : ∑ f : {x // x ∈ U} → Fin M, (hitCount f : ℚ) ≤
        ((r - 1 : ℕ) : ℚ) * (M : ℚ) ^ U.card := by
      have hcard_fn : (Fintype.card ({x // x ∈ U} → Fin M) : ℚ) = (M : ℚ) ^ U.card := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
        push_cast; rfl
      calc ∑ f : {x // x ∈ U} → Fin M, (hitCount f : ℚ)
          ≤ ∑ _f : {x // x ∈ U} → Fin M, ((r - 1 : ℕ) : ℚ) := by
            refine Finset.sum_le_sum (fun f _ => ?_)
            exact_mod_cast Nat.le_sub_one_of_lt (hall f)
        _ = (Fintype.card ({x // x ∈ U} → Fin M) : ℚ) * ((r - 1 : ℕ) : ℚ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ((r - 1 : ℕ) : ℚ) * (M : ℚ) ^ U.card := by rw [hcard_fn]; ring
    linarith
  obtain ⟨f, hf⟩ := hex_f
  let goodColors := Finset.univ.filter (fun c : Fin M =>
    ∃ S ∈ F, S ⊆ (U.attach.filter (fun x => f x = c)).image Subtype.val)
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hf
  have hchoose : ∀ c ∈ C, ∃ S ∈ F, S ⊆ (U.attach.filter (fun x => f x = c)).image Subtype.val :=
    fun c hc => (Finset.mem_filter.mp (hCsub hc)).2
  let pick (c : Fin M) : Finset α :=
    if h : ∃ S ∈ F, S ⊆ (U.attach.filter (fun x => f x = c)).image Subtype.val
    then Classical.choose h
    else ∅
  have hpick_mem : ∀ c ∈ C, pick c ∈ F := fun c hc => by
    simp only [pick, hchoose c hc, ↓reduceDIte]
    exact (Classical.choose_spec (hchoose c hc)).1
  have hpick_sub : ∀ c ∈ C,
      pick c ⊆ (U.attach.filter (fun x => f x = c)).image Subtype.val := fun c hc => by
    simp only [pick, hchoose c hc, ↓reduceDIte]
    exact (Classical.choose_spec (hchoose c hc)).2
  have hpick_disj : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → Disjoint (pick c₁) (pick c₂) := by
    intro c₁ hc₁ c₂ hc₂ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := hpick_sub c₁ hc₁ hx1
    have h2 := hpick_sub c₂ hc₂ hx2
    rcases Finset.mem_image.mp h1 with ⟨⟨x1, hx1U⟩, hfilt1, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨⟨x2, hx2U⟩, hfilt2, hEq⟩
    dsimp only at hEq
    subst hEq
    have hf1 : f ⟨x2, hx1U⟩ = c₁ := (Finset.mem_filter.mp hfilt1).2
    have hf2 : f ⟨x2, hx2U⟩ = c₂ := (Finset.mem_filter.mp hfilt2).2
    exact hne (hf1.symm.trans hf2)
  have hpick_inj : Set.InjOn pick (C : Set (Fin M)) := by
    intro c₁ hc₁ c₂ hc₂ hEq
    by_contra hne
    have hd := hpick_disj c₁ hc₁ c₂ hc₂ hne
    rw [hEq] at hd
    exact (hFnonempty (pick c₂) (hpick_mem c₂ hc₂)).ne_empty (disjoint_self.mp hd)
  refine ⟨C.image pick, ?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨c, hc, rfl⟩
    exact hpick_mem c hc
  · rw [Finset.card_image_of_injOn hpick_inj, hCcard]
  · intro A hA B hB hAB
    rcases Finset.mem_image.mp hA with ⟨c₁, hc₁, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨c₂, hc₂, rfl⟩
    exact hpick_disj c₁ hc₁ c₂ hc₂ (fun h => hAB (by rw [h]))

/-- Maximal heavy core reduction: any `n`-uniform family with `R ^ n < F.card` and
`36 * M * (Nat.log 2 n + 1) ≤ R` (where `2 * (r - 1) ≤ M`) contains an `r`-sunflower. -/
private lemma modern_sunflower_of_color_param {α : Type*} [DecidableEq α]
    {n r M R : ℕ} (_hn : 1 ≤ n) (hMpos : 1 ≤ M) (hMr : 2 * (r - 1) ≤ M)
    (hR : 36 * M * (Nat.log 2 n + 1) ≤ R)
    (F : Finset (Finset α)) (hunif : ∀ S ∈ F, S.card = n)
    (hcard : R ^ n < F.card) :
    ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  classical
  let U : Finset α := F.biUnion id
  have hFU : ∀ S ∈ F, S ⊆ U := fun S hS => Finset.subset_biUnion_of_mem id hS
  let heavy : Finset (Finset α) :=
    U.powerset.filter (fun T => R ^ (n - T.card) < (F.filter (fun S => T ⊆ S)).card)
  have hempty_heavy : ∅ ∈ heavy := by
    refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset U, ?_⟩
    simpa using hcard
  obtain ⟨T, hTheavy, hTmax⟩ := Finset.exists_max_image heavy Finset.card ⟨∅, hempty_heavy⟩
  have hTU : T ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hTheavy).1
  have hTcard_gt : R ^ (n - T.card) < (F.filter (fun S => T ⊆ S)).card :=
    (Finset.mem_filter.mp hTheavy).2
  have hRpos : 0 < R := by
    have : 1 ≤ 36 * M * (Nat.log 2 n + 1) := by nlinarith
    omega
  -- Show `T.card < n`
  have hTlt : T.card < n := by
    by_contra hge
    push Not at hge
    have hsub0 : n - T.card = 0 := Nat.sub_eq_zero_of_le hge
    rw [hsub0, pow_zero] at hTcard_gt
    have hle1 : (F.filter (fun S => T ⊆ S)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro S₁ hS₁ S₂ hS₂
      have h1 := Finset.eq_of_subset_of_card_le (Finset.mem_filter.mp hS₁).2
        (by rw [hunif S₁ (Finset.mem_filter.mp hS₁).1]; exact hge)
      have h2 := Finset.eq_of_subset_of_card_le (Finset.mem_filter.mp hS₂).2
        (by rw [hunif S₂ (Finset.mem_filter.mp hS₂).1]; exact hge)
      exact h1.symm.trans h2
    omega
  let k' : ℕ := n - T.card
  have hk'pos : 1 ≤ k' := by omega
  have hk'le : k' ≤ n := Nat.sub_le n T.card
  let FT : Finset (Finset α) := F.filter (fun S => T ⊆ S)
  let F' : Finset (Finset α) := FT.image (fun S => S \ T)
  have hinj : Set.InjOn (fun S : Finset α => S \ T) (FT : Set (Finset α)) := by
    intro A hA B hB hEq
    have hTA : T ⊆ A := (Finset.mem_filter.mp hA).2
    have hTB : T ⊆ B := (Finset.mem_filter.mp hB).2
    have := congrArg (fun X => X ∪ T) hEq
    simpa [Finset.sdiff_union_of_subset hTA, Finset.sdiff_union_of_subset hTB] using this
  have hF'card : F'.card = FT.card := Finset.card_image_of_injOn hinj
  have hF'ne : F'.Nonempty :=
    Finset.card_pos.mp (by rw [hF'card]; exact lt_of_le_of_lt (Nat.zero_le _) hTcard_gt)
  let U' : Finset α := U \ T
  have hF'U' : ∀ A ∈ F', A ⊆ U' := by
    intro A hA
    rcases Finset.mem_image.mp hA with ⟨S, hSFT, rfl⟩
    exact Finset.sdiff_subset_sdiff (hFU S (Finset.mem_filter.mp hSFT).1) (Finset.Subset.refl T)
  have hF'unif : ∀ A ∈ F', A.card = k' := by
    intro A hA
    rcases Finset.mem_image.mp hA with ⟨S, hSFT, rfl⟩
    rw [Finset.card_sdiff_of_subset (Finset.mem_filter.mp hSFT).2,
        hunif S (Finset.mem_filter.mp hSFT).1]
  -- Prove `F'` is `R`-spread on `U'`
  have hspread : ∀ Z ⊆ U', ((F'.filter (fun A => Z ⊆ A)).card : ℚ) ≤
      (R : ℚ)⁻¹ ^ Z.card * F'.card := by
    intro Z hZU'
    by_cases hZe : Z = ∅
    · subst hZe
      simp only [Finset.empty_subset, Finset.filter_true, Finset.card_empty, pow_zero, one_mul,
        le_refl]
    · have hZpos : 0 < Z.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hZe)
      have hdisjTZ : Disjoint T Z :=
        Disjoint.mono_right hZU' disjoint_sdiff_self_right
      have hTZ_U : T ∪ Z ⊆ U := Finset.union_subset hTU (hZU'.trans Finset.sdiff_subset)
      have hTZ_card : (T ∪ Z).card = T.card + Z.card := Finset.card_union_of_disjoint hdisjTZ
      have hnot_heavy : T ∪ Z ∉ heavy := by
        intro hmem
        have := hTmax (T ∪ Z) hmem
        omega
      have hle_TZ : (F.filter (fun S => T ∪ Z ⊆ S)).card ≤ R ^ (n - (T ∪ Z).card) := by
        by_contra hgt
        push Not at hgt
        exact hnot_heavy (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTZ_U, hgt⟩)
      have hfilt_card : (F'.filter (fun A => Z ⊆ A)).card =
          (F.filter (fun S => T ∪ Z ⊆ S)).card := by
        have himg_eq : F'.filter (fun A => Z ⊆ A) =
            (F.filter (fun S => T ∪ Z ⊆ S)).image (fun S => S \ T) := by
          ext A
          simp only [F', FT, Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨S, ⟨hSF, hTS⟩, rfl⟩, hZsub⟩
            refine ⟨S, ⟨hSF, Finset.union_subset hTS (hZsub.trans Finset.sdiff_subset)⟩, rfl⟩
          · rintro ⟨S, ⟨hSF, hTZS⟩, rfl⟩
            have hTS : T ⊆ S := Finset.subset_union_left.trans hTZS
            have hZS : Z ⊆ S := Finset.subset_union_right.trans hTZS
            refine ⟨⟨S, ⟨hSF, hTS⟩, rfl⟩, ?_⟩
            intro x hxZ
            exact Finset.mem_sdiff.mpr ⟨hZS hxZ, Finset.disjoint_right.mp hdisjTZ hxZ⟩
        rw [himg_eq, Finset.card_image_of_injOn]
        intro S₁ hS₁ S₂ hS₂ hEq
        exact hinj
          (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS₁).1,
            Finset.subset_union_left.trans (Finset.mem_filter.mp hS₁).2⟩)
          (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS₂).1,
            Finset.subset_union_left.trans (Finset.mem_filter.mp hS₂).2⟩) hEq
      rw [hfilt_card]
      by_cases hZle : Z.card ≤ k'
      · have hmul_nat : R ^ Z.card * (F.filter (fun S => T ∪ Z ⊆ S)).card ≤ F'.card := by
          have hexp : Z.card + (n - (T ∪ Z).card) = n - T.card := by omega
          calc R ^ Z.card * (F.filter (fun S => T ∪ Z ⊆ S)).card
              ≤ R ^ Z.card * R ^ (n - (T ∪ Z).card) := Nat.mul_le_mul_left _ hle_TZ
            _ = R ^ (n - T.card) := by rw [← pow_add, hexp]
            _ ≤ FT.card := hTcard_gt.le
            _ = F'.card := hF'card.symm
        have hmul_q : (R : ℚ) ^ Z.card * ((F.filter (fun S => T ∪ Z ⊆ S)).card : ℚ) ≤ F'.card := by
          exact_mod_cast hmul_nat
        have hRpow_pos : (0 : ℚ) < (R : ℚ) ^ Z.card := by positivity
        rw [inv_pow, inv_mul_eq_div, le_div_iff₀ hRpow_pos, mul_comm]
        exact hmul_q
      · -- If `Z.card > k'`, no `k'`-element set in `F'` can contain `Z`, so count is 0!
        have hzero : (F.filter (fun S => T ∪ Z ⊆ S)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro S hSF hsub
          have hle := Finset.card_le_card hsub
          rw [hTZ_card, hunif S hSF] at hle
          omega
        rw [hzero, Nat.cast_zero]
        positivity
  have hlog_le : Nat.log 2 k' ≤ Nat.log 2 n := Nat.log_mono_right hk'le
  have hRq : (36 * M * (Nat.log 2 k' + 1) : ℚ) ≤ R := by
    have hnat : 36 * M * (Nat.log 2 k' + 1) ≤ R := by
      calc 36 * M * (Nat.log 2 k' + 1) ≤ 36 * M * (Nat.log 2 n + 1) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog_le 1)
        _ ≤ R := hR
    exact_mod_cast hnat
  obtain ⟨G', hG'sub, hG'card, hG'disj⟩ :=
    spread_exists_disjoint_sets U' F' hk'pos hF'ne hMpos hMr hF'U'
      (fun A hA => (hF'unif A hA).le)
      (fun A hA => Finset.card_pos.mp (by rw [hF'unif A hA]; omega))
      hspread (by exact_mod_cast hRpos) hRq
  -- Lift `G'` back to `F` by adding core `T`
  have hG'disjT : ∀ A ∈ G', Disjoint A T := fun A hA =>
    Disjoint.mono_left (hF'U' A (hG'sub hA)) disjoint_sdiff_self_left
  let G : Finset (Finset α) := G'.image (fun A => A ∪ T)
  have hGinj : Set.InjOn (fun A : Finset α => A ∪ T) (G' : Set (Finset α)) := by
    intro A hA B hB hEq
    have := congrArg (fun X => X \ T) hEq
    simpa [Finset.union_sdiff_cancel_right (hG'disjT A hA),
           Finset.union_sdiff_cancel_right (hG'disjT B hB)] using this
  refine ⟨G, ?_, ?_, T, ?_⟩
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨A, hAG', rfl⟩
    rcases Finset.mem_image.mp (hG'sub hAG') with ⟨S₀, hS₀FT, rfl⟩
    rw [Finset.sdiff_union_of_subset (Finset.mem_filter.mp hS₀FT).2]
    exact (Finset.mem_filter.mp hS₀FT).1
  · rw [Finset.card_image_of_injOn hGinj, hG'card]
  · intro S₁ hS₁ S₂ hS₂ hne
    rcases Finset.mem_image.mp hS₁ with ⟨A, hAG', rfl⟩
    rcases Finset.mem_image.mp hS₂ with ⟨B, hBG', rfl⟩
    have hAB : A ≠ B := fun h => hne (by rw [h])
    have hdisjAB : Disjoint A B := hG'disj hAG' hBG' hAB
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hxA | hxT, hxB | hxT'⟩
      · exact (Finset.disjoint_left.mp hdisjAB hxA hxB).elim
      · exact hxT'
      · exact hxT
      · exact hxT
    · intro hxT
      exact ⟨Or.inr hxT, Or.inr hxT⟩

/-- **Modern Sunflower Lemma (ALWZ / Rao / Bell–Chueluecha–Warnke / MNSZ Regime):**
For all `n ≥ 1` and `r ≥ 2`, every `n`-uniform family `F` with
`(36 * (2 * r - 1) * (Nat.log 2 n + 1)) ^ n < F.card` contains an `r`-sunflower.
This beats the classical Erdős–Rado `n! (r - 1)^n` bound super-exponentially.
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl038_modern_sunflower_lemma
    {α : Type*} [DecidableEq α] {n r : ℕ} (hn : 1 ≤ n) (hr : 2 ≤ r)
    (F : Finset (Finset α)) (hunif : ∀ S ∈ F, S.card = n)
    (hcard : (36 * (2 * r - 1) * (Nat.log 2 n + 1)) ^ n < F.card) :
    ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K :=
  modern_sunflower_of_color_param hn (by omega) (by omega) le_rfl F hunif hcard

/-- **Sharpened Modern Sunflower Lemma for `r = 3` (4-Color Averaging):**
For all `n ≥ 1`, every `n`-uniform family `F` with
`(144 * (Nat.log 2 n + 1)) ^ n < F.card` contains a `3`-sunflower. -/
theorem ppl038_modern_sunflower_lemma_r3
    {α : Type*} [DecidableEq α] {n : ℕ} (hn : 1 ≤ n)
    (F : Finset (Finset α)) (hunif : ∀ S ∈ F, S.card = n)
    (hcard : (144 * (Nat.log 2 n + 1)) ^ n < F.card) :
    ∃ G ⊆ F, G.card = 3 ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K :=
  modern_sunflower_of_color_param (M := 4) hn (by omega) (by omega) (by omega) F hunif hcard

/-- **Modern Sunflower Lemma (Real Natural-Logarithm Form):**
For all `n ≥ 2` and `r ≥ 2`, every `n`-uniform family `F` with
`(208 * r * Real.log n) ^ n < F.card` contains an `r`-sunflower. -/
theorem ppl038_modern_sunflower_lemma_real_log
    {α : Type*} [DecidableEq α] {n r : ℕ} (hn : 2 ≤ n) (hr : 2 ≤ r)
    (F : Finset (Finset α)) (hunif : ∀ S ∈ F, S.card = n)
    (hcard : ((208 * (r : ℝ) * Real.log (n : ℝ)) ^ n) < (F.card : ℝ)) :
    ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  have hlog2_le : ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hpow_r : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by exact_mod_cast hpow
    calc ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2
        = Real.log ((2 : ℝ) ^ Nat.log 2 n) := (Real.log_pow 2 (Nat.log 2 n)).symm
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) hpow_r
  have hlog2_pos : 1 ≤ Nat.log 2 n := by
    have h1 : Nat.log 2 2 ≤ Nat.log 2 n := Nat.log_mono_right hn
    have h2 : Nat.log 2 2 = 1 := by decide
    omega
  have hlog2_gt : (693 : ℝ) / 1000 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hnat_le_real : ((36 * (2 * r - 1) * (Nat.log 2 n + 1) : ℕ) : ℝ) ≤
      208 * (r : ℝ) * Real.log (n : ℝ) := by
    have h1 : (Nat.log 2 n + 1 : ℝ) ≤ 2 * (Nat.log 2 n : ℝ) := by
      have : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hlog2_pos
      linarith
    have h2 : (2 * r - 1 : ℕ) ≤ 2 * r := by omega
    have h2r : ((2 * r - 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast h2
    have hstep1 : ((36 * (2 * r - 1) * (Nat.log 2 n + 1) : ℕ) : ℝ) ≤
        144 * (r : ℝ) * (Nat.log 2 n : ℝ) := by
      push_cast
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    have hstep2 : 144 * (r : ℝ) * (Nat.log 2 n : ℝ) ≤
        208 * (r : ℝ) * ((Nat.log 2 n : ℝ) * Real.log 2) := by
      have h144 : (144 : ℝ) ≤ 208 * Real.log 2 := by linarith
      have hrn : (0 : ℝ) ≤ (r : ℝ) * (Nat.log 2 n : ℝ) := by positivity
      nlinarith
    have hstep3 : 208 * (r : ℝ) * ((Nat.log 2 n : ℝ) * Real.log 2) ≤
        208 * (r : ℝ) * Real.log (n : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlog2_le (by positivity)
    exact hstep1.trans (hstep2.trans hstep3)
  have hcard_nat : (36 * (2 * r - 1) * (Nat.log 2 n + 1)) ^ n < F.card := by
    have hpow_le : (((36 * (2 * r - 1) * (Nat.log 2 n + 1)) ^ n : ℕ) : ℝ) ≤
        (208 * (r : ℝ) * Real.log (n : ℝ)) ^ n := by
      rw [Nat.cast_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hnat_le_real n
    have hlt : (((36 * (2 * r - 1) * (Nat.log 2 n + 1)) ^ n : ℕ) : ℝ) < (F.card : ℝ) :=
      lt_of_le_of_lt hpow_le hcard
    exact_mod_cast hlt
  exact ppl038_modern_sunflower_lemma (by omega) hr F hunif hcard_nat

/-! ### Section 3: Tightness Barrier for the Spread Lemma (`Ω((1/p) log n)`) -/

/-- Elementary exponential bound `exp (-2 * x) ≤ 1 - x` on `[0, 1/2]`. -/
private lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 * x by linarith) 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  have hsum' : 1 + 2 * x + 2 * x ^ 2 ≤ Real.exp (2 * x) := by
    have hnorm : (0 : ℝ) + (2 * x) ^ 0 / (Nat.factorial 0 : ℝ) +
        (2 * x) ^ 1 / (Nat.factorial 1 : ℝ) + (2 * x) ^ 2 / (Nat.factorial 2 : ℝ) =
        1 + 2 * x + 2 * x ^ 2 := by
      norm_num [Nat.factorial]; ring
    linarith
  have hpoly : 1 ≤ (1 - x) * (1 + 2 * x + 2 * x ^ 2) := by
    have h1 : (1 - x) * (1 + 2 * x + 2 * x ^ 2) - 1 = x * (1 - 2 * x ^ 2) := by ring
    have h2 : 0 ≤ 1 - 2 * x ^ 2 := by nlinarith
    nlinarith
  have hprod : 1 ≤ (1 - x) * Real.exp (2 * x) :=
    hpoly.trans (mul_le_mul_of_nonneg_left hsum' (by linarith))
  have hexp_pos : 0 < Real.exp (-2 * x) := Real.exp_pos _
  calc Real.exp (-2 * x) = 1 * Real.exp (-2 * x) := (one_mul _).symm
    _ ≤ ((1 - x) * Real.exp (2 * x)) * Real.exp (-2 * x) :=
        mul_le_mul_of_nonneg_right hprod hexp_pos.le
    _ = (1 - x) * (Real.exp (2 * x) * Real.exp (-2 * x)) := by ring
    _ = 1 - x := by rw [← Real.exp_add]; simp

/-- **Spread-Lemma `Ω((1/p) log n)` Tightness Barrier:**
For every `n ≥ 3`, `R ≥ 1`, and rational `p ∈ (0, 1/2]` satisfying
`2 * (p : ℝ) * R ≤ Real.log (n / 2)`, there exists an `n`-uniform `R`-spread family `F`
of cardinality `R ^ n` on a finite ground set `U` of size `n * R` (the complete `n`-partite
product hypergraph) whose `p`-biased containment probability equals `(1 - (1 - p) ^ R) ^ n`
and is strictly less than `1 / 2` (in fact `≤ Real.exp (-2) < 1 / 2`).
Thus the `log n` factor in the Spread Lemma is sharp and cannot be removed. -/
theorem ppl038_spread_lemma_log_barrier
    {n R : ℕ} (hn : 3 ≤ n) (hR : 1 ≤ R) {p : ℚ}
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2)
    (hpR : 2 * (p : ℝ) * (R : ℝ) ≤ Real.log ((n : ℝ) / 2)) :
    let U : Finset (Fin n × Fin R) := Finset.univ
    ∃ F : Finset (Finset (Fin n × Fin R)),
      F.card = R ^ n ∧
      (∀ S ∈ F, S.card = n) ∧
      (∀ Z ⊆ U, ((F.filter (fun S => Z ⊆ S)).card : ℚ) ≤ (R : ℚ)⁻¹ ^ Z.card * F.card) ∧
      (∑ W ∈ U.powerset,
          p ^ W.card * (1 - p) ^ (U.card - W.card) *
            (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0)) = (1 - (1 - p) ^ R) ^ n ∧
      (((1 - (1 - p) ^ R) ^ n : ℚ) : ℝ) < 1 / 2 := by
  classical
  intro U
  let graphSet (f : Fin n → Fin R) : Finset (Fin n × Fin R) :=
    Finset.univ.image (fun i : Fin n => (i, f i))
  have hgraph_inj : Function.Injective graphSet := by
    intro f g hEq
    funext i
    have hmem : (i, f i) ∈ graphSet g := by
      rw [← hEq]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rcases Finset.mem_image.mp hmem with ⟨j, _, hpair⟩
    have hij : j = i := congrArg Prod.fst hpair
    subst hij
    exact (congrArg Prod.snd hpair).symm
  have hgraph_card : ∀ f : Fin n → Fin R, (graphSet f).card = n := by
    intro f
    have hinj : Function.Injective (fun i : Fin n => (i, f i)) :=
      fun i j h => congrArg Prod.fst h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let F : Finset (Finset (Fin n × Fin R)) := Finset.univ.image graphSet
  have hFcard : F.card = R ^ n := by
    rw [Finset.card_image_of_injective _ hgraph_inj, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin]
  have hFunif : ∀ S ∈ F, S.card = n := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨f, _, rfl⟩
    exact hgraph_card f
  -- Exact R-spreadness of F
  have hspread : ∀ Z ⊆ U, ((F.filter (fun S => Z ⊆ S)).card : ℚ) ≤
      (R : ℚ)⁻¹ ^ Z.card * F.card := by
    intro Z _hZU
    by_cases hfunc : ∀ x ∈ Z, ∀ y ∈ Z, x.1 = y.1 → x.2 = y.2
    · -- Z is a partial function on Fin n of domain size Z.card
      let dom : Finset (Fin n) := Z.image Prod.fst
      have hdom_card : dom.card = Z.card := by
        refine Finset.card_image_of_injOn (fun x hx y hy h1 => ?_)
        exact Prod.ext h1 (hfunc x hx y hy h1)
      have hZle : Z.card ≤ n := by
        rw [← hdom_card]
        exact (Finset.card_le_univ dom).trans_eq (Fintype.card_fin n)
      -- Count `f : Fin n → Fin R` with `Z ⊆ graphSet f`: fixed on `dom`, free on `domᶜ`
      have hfilt_eq : F.filter (fun S => Z ⊆ S) =
          (Finset.univ.filter (fun f : Fin n → Fin R => Z ⊆ graphSet f)).image graphSet := by
        ext S
        simp only [F, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨f, rfl⟩, hZ⟩; exact ⟨f, hZ, rfl⟩
        · rintro ⟨f, hZ, rfl⟩; exact ⟨⟨f, rfl⟩, hZ⟩
      have hcnt_le : (F.filter (fun S => Z ⊆ S)).card ≤ R ^ (n - Z.card) := by
        rw [hfilt_eq, Finset.card_image_of_injective _ hgraph_inj]
        -- Restriction to `{i : Fin n // i ∉ dom} → Fin R` is injective on the filtered set!
        let rest : (Fin n → Fin R) → ({i : Fin n // i ∉ dom} → Fin R) := fun f i => f i.1
        have hrest_inj : Set.InjOn rest
            ((Finset.univ.filter (fun f : Fin n → Fin R => Z ⊆ graphSet f)) :
              Set (Fin n → Fin R)) := by
          intro f hf g hg hEq
          have hZf : Z ⊆ graphSet f := (Finset.mem_filter.mp hf).2
          have hZg : Z ⊆ graphSet g := (Finset.mem_filter.mp hg).2
          funext i
          by_cases hid : i ∈ dom
          · rcases Finset.mem_image.mp hid with ⟨⟨i', j⟩, hmemZ, hi'⟩
            dsimp only at hi'
            have hmf := hZf hmemZ
            have hmg := hZg hmemZ
            rcases Finset.mem_image.mp hmf with ⟨k1, _, hk1⟩
            rcases Finset.mem_image.mp hmg with ⟨k2, _, hk2⟩
            have h1 : k1 = i := (congrArg Prod.fst hk1).trans hi'
            have h2 : k2 = i := (congrArg Prod.fst hk2).trans hi'
            have hf_eq : f i = j := h1 ▸ congrArg Prod.snd hk1
            have hg_eq : g i = j := h2 ▸ congrArg Prod.snd hk2
            exact hf_eq.trans hg_eq.symm
          · exact congrFun hEq ⟨i, hid⟩
        calc (Finset.univ.filter (fun f : Fin n → Fin R => Z ⊆ graphSet f)).card
            = ((Finset.univ.filter (fun f : Fin n → Fin R => Z ⊆ graphSet f)).image rest).card :=
              (Finset.card_image_of_injOn hrest_inj).symm
          _ ≤ Fintype.card ({i : Fin n // i ∉ dom} → Fin R) := Finset.card_le_univ _
          _ = R ^ (Finset.univ.filter (fun i : Fin n => i ∉ dom)).card := by
              rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype]
          _ = R ^ (n - Z.card) := by
              congr 1
              have hcomp : (Finset.univ.filter (fun i : Fin n => i ∉ dom)) = domᶜ := by
                ext i; simp
              rw [hcomp, Finset.card_compl, Fintype.card_fin, hdom_card]
      have hmul_nat : R ^ Z.card * (F.filter (fun S => Z ⊆ S)).card ≤ F.card := by
        calc R ^ Z.card * (F.filter (fun S => Z ⊆ S)).card
            ≤ R ^ Z.card * R ^ (n - Z.card) := Nat.mul_le_mul_left _ hcnt_le
          _ = R ^ n := by rw [← pow_add, Nat.add_sub_of_le hZle]
          _ = F.card := hFcard.symm
      have hRpos : (0 : ℚ) < (R : ℚ) ^ Z.card := by positivity
      have hmul_q : (R : ℚ) ^ Z.card * ((F.filter (fun S => Z ⊆ S)).card : ℚ) ≤ F.card := by
        exact_mod_cast hmul_nat
      rw [inv_pow, inv_mul_eq_div, le_div_iff₀ hRpos, mul_comm]
      exact hmul_q
    · -- Some coordinate has two distinct values in Z: no graphSet contains Z!
      push Not at hfunc
      rcases hfunc with ⟨x, hxZ, y, hyZ, h1, h2⟩
      have hempty : (F.filter (fun S => Z ⊆ S)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro S hSF hZS
        rcases Finset.mem_image.mp hSF with ⟨f, _, rfl⟩
        rcases Finset.mem_image.mp (hZS hxZ) with ⟨i, _, hi⟩
        rcases Finset.mem_image.mp (hZS hyZ) with ⟨j, _, hj⟩
        have hix : i = x.1 := congrArg Prod.fst hi
        have hjy : j = y.1 := congrArg Prod.fst hj
        have hfx : f i = x.2 := congrArg Prod.snd hi
        have hfy : f j = y.2 := congrArg Prod.snd hj
        have hij : i = j := hix.trans (h1.trans hjy.symm)
        rw [hij] at hfx
        exact h2 (hfx.symm.trans hfy)
      rw [hempty, Nat.cast_zero]
      positivity
  -- Exact p-biased hit probability = (1 - (1 - p)^R)^n
  have hprob_eq :
      ∑ W ∈ U.powerset,
        p ^ W.card * (1 - p) ^ (U.card - W.card) *
          (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0) =
      (1 - (1 - p) ^ R) ^ n := by
    let e : Finset (Fin n × Fin R) ≃ (Fin n → Finset (Fin R)) :=
      { toFun := fun W i => Finset.univ.filter (fun j : Fin R => (i, j) ∈ W)
        invFun := fun g => Finset.univ.biUnion (fun i : Fin n => (g i).image (fun j => (i, j)))
        left_inv := fun W => by
          ext ⟨i, j⟩
          simp
        right_inv := fun g => by
          funext i
          ext j
          simp }
    have hpow_univ : U.powerset = (Finset.univ : Finset (Finset (Fin n × Fin R))) := by
      ext W; simp [U]
    rw [hpow_univ]
    have hUcard : U.card = n * R := by
      simp [U, Fintype.card_prod, Fintype.card_fin]
    have hcard_W : ∀ W : Finset (Fin n × Fin R), W.card = ∑ i : Fin n, (e W i).card := by
      intro W
      have hW_eq : W = Finset.univ.biUnion (fun i : Fin n => (e W i).image (fun j => (i, j))) :=
        (e.left_inv W).symm
      conv_lhs => rw [hW_eq]
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Finset.card_image_of_injective _ (fun j₁ j₂ h => congrArg Prod.snd h)
      · intro i₁ _ i₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rcases Finset.mem_image.mp hx1 with ⟨j₁, _, rfl⟩
        rcases Finset.mem_image.mp hx2 with ⟨j₂, _, hEq⟩
        exact hne (congrArg Prod.fst hEq).symm
    have hhit_iff : ∀ W : Finset (Fin n × Fin R),
        (∃ S ∈ F, S ⊆ W) ↔ ∀ i : Fin n, (e W i).Nonempty := by
      intro W
      constructor
      · rintro ⟨S, hSF, hSW⟩ i
        rcases Finset.mem_image.mp hSF with ⟨f, _, rfl⟩
        refine ⟨f i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact hSW (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      · intro hall
        choose f hf using hall
        refine ⟨graphSet f, Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩, ?_⟩
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact (Finset.mem_filter.mp (hf i)).2
    have hprod_term : ∀ W : Finset (Fin n × Fin R),
        p ^ W.card * (1 - p) ^ (U.card - W.card) *
          (if ∃ S ∈ F, S ⊆ W then (1 : ℚ) else 0) =
        ∏ i : Fin n, (p ^ (e W i).card * (1 - p) ^ (R - (e W i).card) *
          (if (e W i).Nonempty then (1 : ℚ) else 0)) := by
      intro W
      have hsub_sum : U.card - W.card = ∑ i : Fin n, (R - (e W i).card) := by
        rw [hUcard, hcard_W W]
        have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (e W i).card ≤ R := fun i _ =>
          (Finset.card_le_univ _).trans_eq (Fintype.card_fin R)
        have hsum_add : ∑ i : Fin n, (R - (e W i).card) + ∑ i : Fin n, (e W i).card =
            ∑ _i : Fin n, R := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hle i hi))
        have hnR : ∑ _i : Fin n, R = n * R := by simp
        omega
      rw [hsub_sum, hcard_W W, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
      congr 1
      simp only [hhit_iff W]
      by_cases hall : ∀ i : Fin n, (e W i).Nonempty
      · simp [hall]
      · simp only [hall, ↓reduceIte]
        push Not at hall
        rcases hall with ⟨i₀, hi₀⟩
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
    simp_rw [hprod_term]
    rw [Fintype.sum_equiv e _ (fun g =>
        ∏ i : Fin n, (p ^ (g i).card * (1 - p) ^ (R - (g i).card) *
          (if (g i).Nonempty then (1 : ℚ) else 0))) (fun _ => rfl)]
    rw [← Fintype.prod_sum (fun (_ : Fin n) (V : Finset (Fin R)) =>
        p ^ V.card * (1 - p) ^ (R - V.card) * (if V.Nonempty then (1 : ℚ) else 0))]
    have hsingle :
        ∑ V : Finset (Fin R),
          p ^ V.card * (1 - p) ^ (R - V.card) * (if V.Nonempty then (1 : ℚ) else 0) =
        1 - (1 - p) ^ R := by
      have htot : ∑ V ∈ (Finset.univ : Finset (Fin R)).powerset,
          binomWeight (Finset.univ : Finset (Fin R)) p V = 1 :=
        sum_binomWeight_powerset Finset.univ p
      have hpow_R : (Finset.univ : Finset (Fin R)).powerset = Finset.univ := by
        ext V; simp
      rw [hpow_R] at htot
      have hsplit : ∑ V : Finset (Fin R),
            p ^ V.card * (1 - p) ^ (R - V.card) * (if V.Nonempty then (1 : ℚ) else 0) +
          (1 - p) ^ R =
          ∑ V : Finset (Fin R), binomWeight (Finset.univ : Finset (Fin R)) p V := by
        have hempty_mem : (∅ : Finset (Fin R)) ∈ (Finset.univ : Finset (Finset (Fin R))) :=
          Finset.mem_univ _
        have hleft : ∑ V : Finset (Fin R),
              p ^ V.card * (1 - p) ^ (R - V.card) * (if V.Nonempty then (1 : ℚ) else 0) =
            ∑ V ∈ Finset.univ.erase (∅ : Finset (Fin R)),
              binomWeight (Finset.univ : Finset (Fin R)) p V := by
          rw [← Finset.add_sum_erase _ _ hempty_mem]
          simp only [Finset.not_nonempty_empty, ↓reduceIte, mul_zero, zero_add]
          refine Finset.sum_congr rfl (fun V hV => ?_)
          have hne : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hV).1
          simp [hne, binomWeight, Fintype.card_fin]
        rw [hleft]
        conv_rhs => rw [← Finset.add_sum_erase _ _ hempty_mem]
        simp [binomWeight, Fintype.card_fin, add_comm]
      linarith
    simp only [hsingle, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Real upper bound: ((1 - (1 - p)^R)^n : ℝ) < 1/2
  have hreal_lt : (((1 - (1 - p) ^ R) ^ n : ℚ) : ℝ) < 1 / 2 := by
    push_cast
    have hp0_r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
    have hp1_r : (p : ℝ) ≤ 1 / 2 := by
      have : ((p : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hp1
      simpa using this
    have h1 : Real.exp (-2 * (p : ℝ)) ≤ 1 - (p : ℝ) :=
      exp_neg_two_mul_le_one_sub hp0_r.le hp1_r
    have h2 : Real.exp (-2 * (p : ℝ) * (R : ℝ)) ≤ (1 - (p : ℝ)) ^ R := by
      have hpow : (Real.exp (-2 * (p : ℝ))) ^ R ≤ (1 - (p : ℝ)) ^ R :=
        pow_le_pow_left₀ (Real.exp_pos _).le h1 R
      rw [← Real.exp_nat_mul] at hpow
      convert hpow using 2
      ring
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have h3 : (2 : ℝ) / (n : ℝ) ≤ (1 - (p : ℝ)) ^ R := by
      have hlog_eq : Real.exp (-Real.log ((n : ℝ) / 2)) = (2 : ℝ) / (n : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by linarith : (0 : ℝ) < (n : ℝ) / 2)]
        field_simp
      calc (2 : ℝ) / (n : ℝ) = Real.exp (-Real.log ((n : ℝ) / 2)) := hlog_eq.symm
        _ ≤ Real.exp (-2 * (p : ℝ) * (R : ℝ)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ ≤ (1 - (p : ℝ)) ^ R := h2
    have h4 : 0 ≤ 1 - (1 - (p : ℝ)) ^ R := by
      have : (1 - (p : ℝ)) ^ R ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    have h5 : 1 - (1 - (p : ℝ)) ^ R ≤ Real.exp (-(2 : ℝ) / (n : ℝ)) := by
      calc 1 - (1 - (p : ℝ)) ^ R ≤ 1 - (2 : ℝ) / (n : ℝ) := by linarith
        _ = -(2 : ℝ) / (n : ℝ) + 1 := by ring
        _ ≤ Real.exp (-(2 : ℝ) / (n : ℝ)) := Real.add_one_le_exp _
    have h6 : (1 - (1 - (p : ℝ)) ^ R) ^ n ≤ Real.exp (-2) := by
      have hpow := pow_le_pow_left₀ h4 h5 n
      rw [← Real.exp_nat_mul] at hpow
      have hmul : (n : ℝ) * (-(2 : ℝ) / (n : ℝ)) = -2 := by
        field_simp [hn_pos.ne']
      rwa [hmul] at hpow
    have h7 : Real.exp (-2) < 1 / 2 := by
      have he2 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        linarith
      rw [Real.exp_neg]
      have hpos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
      rw [inv_eq_one_div, div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
      linarith
    exact lt_of_le_of_lt h6 h7
  exact ⟨F, hFcard, hFunif, hspread, hprob_eq, hreal_lt⟩

/-! ### Section 4: Exact Small Values, Supermultiplicativity, Wreath Product & Abbott–Hanson (1974) -/

/-- **Supermultiplicativity of Sunflower-Free Uniform Families:**
If there exist an `a`-uniform `r`-sunflower-free family of size `M₁` and a `b`-uniform
`r`-sunflower-free family of size `M₂` (with `r ≥ 2`), then there exists an `(a + b)`-uniform
`r`-sunflower-free family of size `M₁ * M₂` on `ℕ`. -/
theorem ppl038_supermultiplicative_lower_bound
    {a b r M₁ M₂ : ℕ}
    (hA : ∃ A : Finset (Finset ℕ), A.card = M₁ ∧ (∀ S ∈ A, S.card = a) ∧
      ∀ G ⊆ A, G.card = r → ¬ ∃ K : Finset ℕ, ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → X ∩ Y = K)
    (hB : ∃ B : Finset (Finset ℕ), B.card = M₂ ∧ (∀ T ∈ B, T.card = b) ∧
      ∀ G ⊆ B, G.card = r → ¬ ∃ K : Finset ℕ, ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → X ∩ Y = K) :
    ∃ F : Finset (Finset ℕ), F.card = M₁ * M₂ ∧ (∀ S ∈ F, S.card = a + b) ∧
      ∀ G ⊆ F, G.card = r → ¬ ∃ K : Finset ℕ, ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → X ∩ Y = K := by
  classical
  rcases hA with ⟨A, hAcard, hAunif, hAsf⟩
  rcases hB with ⟨B, hBcard, hBunif, hBsf⟩
  let e0 : ℕ ↪ ℕ := ⟨fun x => 2 * x, fun x y h => by dsimp only at h; omega⟩
  let e1 : ℕ ↪ ℕ := ⟨fun y => 2 * y + 1, fun x y h => by dsimp only at h; omega⟩
  have he0 : ∀ x, e0 x = 2 * x := fun _ => rfl
  have he1 : ∀ y, e1 y = 2 * y + 1 := fun _ => rfl
  let combine : Finset ℕ × Finset ℕ → Finset ℕ := fun p => p.1.map e0 ∪ p.2.map e1
  have hdisj : ∀ S T : Finset ℕ, Disjoint (S.map e0) (T.map e1) := by
    intro S T
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rcases Finset.mem_map.mp hz1 with ⟨x, _, rfl⟩
    rcases Finset.mem_map.mp hz2 with ⟨y, _, hEq⟩
    rw [he0, he1] at hEq
    omega
  have hproj0 : ∀ S T : Finset ℕ,
      (combine (S, T)).filter Even = S.map e0 := by
    intro S T
    ext z
    simp only [combine, Finset.mem_filter, Finset.mem_union, Finset.mem_map, he0, he1]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩ | ⟨y, _, rfl⟩, hev⟩
      · exact ⟨x, hx, rfl⟩
      · rcases hev with ⟨k, hk⟩; omega
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Or.inl ⟨x, hx, rfl⟩, ⟨x, by omega⟩⟩
  have hproj1 : ∀ S T : Finset ℕ,
      (combine (S, T)).filter (fun z => ¬ Even z) = T.map e1 := by
    intro S T
    ext z
    simp only [combine, Finset.mem_filter, Finset.mem_union, Finset.mem_map, he0, he1]
    constructor
    · rintro ⟨⟨x, _, rfl⟩ | ⟨y, hy, rfl⟩, hodd⟩
      · exact (hodd ⟨x, by omega⟩).elim
      · exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Or.inr ⟨y, hy, rfl⟩, ?_⟩
      rintro ⟨k, hk⟩; omega
  have hcomb_inj : Function.Injective combine := by
    intro ⟨S₁, T₁⟩ ⟨S₂, T₂⟩ hEq
    have h0 : S₁.map e0 = S₂.map e0 := by
      rw [← hproj0 S₁ T₁, ← hproj0 S₂ T₂, hEq]
    have h1 : T₁.map e1 = T₂.map e1 := by
      rw [← hproj1 S₁ T₁, ← hproj1 S₂ T₂, hEq]
    exact Prod.ext (Finset.map_injective e0 h0) (Finset.map_injective e1 h1)
  let F : Finset (Finset ℕ) := (A ×ˢ B).image combine
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hcomb_inj, Finset.card_product, hAcard, hBcard]
  · intro X hX
    rcases Finset.mem_image.mp hX with ⟨⟨S, T⟩, hST, rfl⟩
    rcases Finset.mem_product.mp hST with ⟨hSA, hTB⟩
    dsimp only [combine]
    rw [Finset.card_union_of_disjoint (hdisj S T), Finset.card_map, Finset.card_map,
        hAunif S hSA, hBunif T hTB]
  · intro G hGF hGcard ⟨K, hK⟩
    -- Project every X ∈ G to its A-component `X.filter Even` (which is `S.map e0`)
    let projA (X : Finset ℕ) : Finset ℕ := (X.filter Even).image (· / 2)
    let projB (X : Finset ℕ) : Finset ℕ := (X.filter (fun z => ¬ Even z)).image (· / 2)
    have hprojA_eq : ∀ S T : Finset ℕ, projA (combine (S, T)) = S := by
      intro S T
      dsimp only [projA]
      rw [hproj0 S T]
      ext x
      simp only [Finset.mem_image, Finset.mem_map, he0]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        simpa [show 2 * y / 2 = y by omega] using hy
      · intro hx
        exact ⟨2 * x, ⟨x, hx, rfl⟩, by omega⟩
    have hprojB_eq : ∀ S T : Finset ℕ, projB (combine (S, T)) = T := by
      intro S T
      dsimp only [projB]
      rw [hproj1 S T]
      ext y
      simp only [Finset.mem_image, Finset.mem_map, he1]
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        simpa [show (2 * z + 1) / 2 = z by omega] using hz
      · intro hy
        exact ⟨2 * y + 1, ⟨y, hy, rfl⟩, by omega⟩
    have hreconstruct : ∀ X ∈ G, combine (projA X, projB X) = X := by
      intro X hX
      rcases Finset.mem_image.mp (hGF hX) with ⟨⟨S, T⟩, _, rfl⟩
      rw [hprojA_eq, hprojB_eq]
    have hprojA_mem : ∀ X ∈ G, projA X ∈ A := by
      intro X hX
      rcases Finset.mem_image.mp (hGF hX) with ⟨⟨S, T⟩, hST, rfl⟩
      rw [hprojA_eq]; exact (Finset.mem_product.mp hST).1
    have hprojB_mem : ∀ X ∈ G, projB X ∈ B := by
      intro X hX
      rcases Finset.mem_image.mp (hGF hX) with ⟨⟨S, T⟩, hST, rfl⟩
      rw [hprojB_eq]; exact (Finset.mem_product.mp hST).2
    have hprojA_inter : ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → projA X ∩ projA Y = projA K := by
      intro X hX Y hY hne
      rw [← hK X hX Y hY hne]
      ext x
      simp only [projA, Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨⟨z₁, ⟨hz₁X, hev₁⟩, hdiv₁⟩, ⟨z₂, ⟨hz₂Y, hev₂⟩, hdiv₂⟩⟩
        have hz_eq : z₁ = z₂ := by
          rcases hev₁ with ⟨k₁, hk₁⟩; rcases hev₂ with ⟨k₂, hk₂⟩; omega
        subst hz_eq
        exact ⟨z₁, ⟨⟨hz₁X, hz₂Y⟩, hev₁⟩, hdiv₁⟩
      · rintro ⟨z, ⟨⟨hzX, hzY⟩, hev⟩, rfl⟩
        exact ⟨⟨z, ⟨hzX, hev⟩, rfl⟩, ⟨z, ⟨hzY, hev⟩, rfl⟩⟩
    have hprojB_inter : ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → projB X ∩ projB Y = projB K := by
      intro X hX Y hY hne
      rw [← hK X hX Y hY hne]
      ext y
      simp only [projB, Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨⟨z₁, ⟨hz₁X, hodd₁⟩, hdiv₁⟩, ⟨z₂, ⟨hz₂Y, hodd₂⟩, hdiv₂⟩⟩
        have hz_eq : z₁ = z₂ := by
          have h1 : z₁ % 2 = 1 := by
            by_contra h0; exact hodd₁ ⟨z₁ / 2, by omega⟩
          have h2 : z₂ % 2 = 1 := by
            by_contra h0; exact hodd₂ ⟨z₂ / 2, by omega⟩
          omega
        subst hz_eq
        exact ⟨z₁, ⟨⟨hz₁X, hz₂Y⟩, hodd₁⟩, hdiv₁⟩
      · rintro ⟨z, ⟨⟨hzX, hzY⟩, hodd⟩, rfl⟩
        exact ⟨⟨z, ⟨hzX, hodd⟩, rfl⟩, ⟨z, ⟨hzY, hodd⟩, rfl⟩⟩
    by_cases hinjA : Set.InjOn projA (G : Set (Finset ℕ))
    · -- Case 1: projA is injective on G, giving an r-sunflower in A
      refine hAsf (G.image projA) ?_ (by rw [Finset.card_image_of_injOn hinjA, hGcard]) ⟨projA K, ?_⟩
      · intro S hS
        rcases Finset.mem_image.mp hS with ⟨X, hXG, rfl⟩
        exact hprojA_mem X hXG
      · intro S₁ hS₁ S₂ hS₂ hne
        rcases Finset.mem_image.mp hS₁ with ⟨X, hXG, rfl⟩
        rcases Finset.mem_image.mp hS₂ with ⟨Y, hYG, rfl⟩
        exact hprojA_inter X hXG Y hYG (fun h => hne (by rw [h]))
    · -- Case 2: Two distinct X₀, Y₀ ∈ G share the same projA => ALL X ∈ G share that projA!
      simp only [Set.InjOn, Finset.mem_coe] at hinjA
      push Not at hinjA
      rcases hinjA with ⟨X₀, hX₀, Y₀, hY₀, hpeq, hne0⟩
      have hKeq : projA K = projA X₀ := by
        have h := hprojA_inter X₀ hX₀ Y₀ hY₀ hne0
        rw [← hpeq, Finset.inter_self] at h
        exact h.symm
      have hallA : ∀ X ∈ G, projA X = projA X₀ := by
        intro X hX
        by_cases hXX₀ : X = X₀
        · rw [hXX₀]
        · have hi := hprojA_inter X hX X₀ hX₀ hXX₀
          rw [hKeq] at hi
          have hsub : projA X₀ ⊆ projA X := by
            intro z hz
            have : z ∈ projA X ∩ projA X₀ := by rw [hi]; exact hz
            exact (Finset.mem_inter.mp this).1
          exact (Finset.eq_of_subset_of_card_le hsub
            (by rw [hAunif _ (hprojA_mem X hX), hAunif _ (hprojA_mem X₀ hX₀)])).symm
      have hinjB : Set.InjOn projB (G : Set (Finset ℕ)) := by
        intro X hX Y hY hBeq
        rw [← hreconstruct X hX, ← hreconstruct Y hY, hallA X hX, hallA Y hY, hBeq]
      refine hBsf (G.image projB) ?_ (by rw [Finset.card_image_of_injOn hinjB, hGcard]) ⟨projB K, ?_⟩
      · intro T hT
        rcases Finset.mem_image.mp hT with ⟨X, hXG, rfl⟩
        exact hprojB_mem X hXG
      · intro T₁ hT₁ T₂ hT₂ hne
        rcases Finset.mem_image.mp hT₁ with ⟨X, hXG, rfl⟩
        rcases Finset.mem_image.mp hT₂ with ⟨Y, hYG, rfl⟩
        exact hprojB_inter X hXG Y hYG (fun h => hne (by rw [h]))

/-- **Classical Exponential Lower Bound (`(r - 1) ^ n`):**
For every `n ∈ ℕ` and `r ≥ 2`, there exists an `n`-uniform family of cardinality `(r - 1) ^ n`
containing no `r`-sunflower. -/
theorem ppl038_exponential_lower_bound (n : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    ∃ F : Finset (Finset ℕ), F.card = (r - 1) ^ n ∧ (∀ S ∈ F, S.card = n) ∧
      ∀ G ⊆ F, G.card = r → ¬ ∃ K : Finset ℕ, ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → X ∩ Y = K := by
  induction n with
  | zero =>
    refine ⟨{∅}, by simp, by simp, ?_⟩
    intro G hG hGcard _
    have hle : G.card ≤ 1 := (Finset.card_le_card hG).trans (by simp)
    omega
  | succ n ih =>
    have h1 : ∃ A : Finset (Finset ℕ), A.card = r - 1 ∧ (∀ S ∈ A, S.card = 1) ∧
        ∀ G ⊆ A, G.card = r → ¬ ∃ K : Finset ℕ, ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → X ∩ Y = K := by
      refine ⟨(Finset.range (r - 1)).image (fun x => ({x} : Finset ℕ)), ?_, ?_, ?_⟩
      · rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), Finset.card_range]
      · intro S hS
        rcases Finset.mem_image.mp hS with ⟨x, _, rfl⟩
        simp
      · intro G hG hGcard _
        have hle : G.card ≤ r - 1 :=
          (Finset.card_le_card hG).trans (by
            rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h),
                Finset.card_range])
        omega
    have hcomb := ppl038_supermultiplicative_lower_bound ih h1
    rcases hcomb with ⟨F, hFcard, hFunif, hFsf⟩
    refine ⟨F, ?_, hFunif, hFsf⟩
    rw [hFcard, pow_succ]

/-- **Exact Small-Case Upper Bound `f(2, 3) ≤ 7`:**
Every `2`-uniform family of cardinality at least `7` contains a `3`-sunflower. -/
theorem ppl038_exact_f_2_3_upper {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hunif : ∀ S ∈ F, S.card = 2) (hcard : 7 ≤ F.card) :
    ∃ G ⊆ F, G.card = 3 ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  classical
  by_cases hdeg : ∃ x : α, 3 ≤ (F.filter (fun S => x ∈ S)).card
  · rcases hdeg with ⟨x, hx⟩
    obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq hx
    refine ⟨G, hGsub.trans (Finset.filter_subset _ F), hGcard, {x}, ?_⟩
    intro A hA B hB hne
    have hAF : A ∈ F := (Finset.mem_filter.mp (hGsub hA)).1
    have hxA : x ∈ A := (Finset.mem_filter.mp (hGsub hA)).2
    have hBF : B ∈ F := (Finset.mem_filter.mp (hGsub hB)).1
    have hxB : x ∈ B := (Finset.mem_filter.mp (hGsub hB)).2
    have hsub : {x} ⊆ A ∩ B := Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
    have hlt : (A ∩ B).card < 2 := by
      by_contra hge
      push Not at hge
      have h1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by rw [hunif A hAF]; exact hge)
      have h2 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        (by rw [hunif B hBF]; exact hge)
      exact hne (h1.symm.trans h2)
    have hle1 : (A ∩ B).card ≤ ({x} : Finset α).card := by simp; omega
    exact (Finset.eq_of_subset_of_card_le hsub hle1).symm
  · push Not at hdeg
    have hne : ∀ S ∈ F, S.Nonempty := fun S hS =>
      Finset.card_pos.mp (by rw [hunif S hS]; omega)
    obtain ⟨M, hMsub, hMdisj, hMmax⟩ := exists_maximal_pairwise_disjoint F hne
    by_cases hM3 : 3 ≤ M.card
    · obtain ⟨G, hGM, hGcard⟩ := Finset.exists_subset_card_eq hM3
      refine ⟨G, hGM.trans hMsub, hGcard, ∅, ?_⟩
      intro A hA B hB hAB
      exact Finset.disjoint_iff_inter_eq_empty.mp (hMdisj (hGM hA) (hGM hB) hAB)
    · push Not at hM3
      -- Each `E ∈ M` has size 2, and each vertex has degree ≤ 2; since `E` itself is counted
      -- in both vertices of `E`, at most `3` sets of `F` intersect `E`!
      have hperE : ∀ E ∈ M, (F.filter (fun S => ¬ Disjoint S E)).card ≤ 3 := by
        intro E hEM
        have hEcard : E.card = 2 := hunif E (hMsub hEM)
        rcases Finset.card_eq_two.mp hEcard with ⟨u, v, huv, rfl⟩
        have hEF : ({u, v} : Finset α) ∈ F := hMsub hEM
        have hsub_u : F.filter (fun S => ¬ Disjoint S {u, v}) ⊆
            (F.filter (fun S => u ∈ S)) ∪ (F.filter (fun S => v ∈ S)) := by
          intro S hS
          rcases Finset.mem_filter.mp hS with ⟨hSF, hnd⟩
          rw [Finset.not_disjoint_iff] at hnd
          rcases hnd with ⟨w, hwS, hwE⟩
          rcases Finset.mem_insert.mp hwE with rfl | hwv
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hSF, hwS⟩)
          · rw [Finset.mem_singleton.mp hwv] at hwS
            exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hSF, hwS⟩)
        have hinter_mem : ({u, v} : Finset α) ∈
            (F.filter (fun S => u ∈ S)) ∩ (F.filter (fun S => v ∈ S)) := by
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_filter.mpr ⟨hEF, by simp⟩, Finset.mem_filter.mpr ⟨hEF, by simp⟩⟩
        have hinter_pos : 1 ≤ ((F.filter (fun S => u ∈ S)) ∩ (F.filter (fun S => v ∈ S))).card :=
          Finset.card_pos.mpr ⟨_, hinter_mem⟩
        have hcu := Finset.card_union_add_card_inter
          (F.filter (fun S => u ∈ S)) (F.filter (fun S => v ∈ S))
        have hdu : (F.filter (fun S => u ∈ S)).card ≤ 2 := by have := hdeg u; omega
        have hdv : (F.filter (fun S => v ∈ S)).card ≤ 2 := by have := hdeg v; omega
        have hle := Finset.card_le_card hsub_u
        omega
      have hFcover : F.card ≤ ∑ E ∈ M, (F.filter (fun S => ¬ Disjoint S E)).card := by
        calc F.card ≤ (M.biUnion (fun E => F.filter (fun S => ¬ Disjoint S E))).card := by
              refine Finset.card_le_card (fun S hSF => ?_)
              rcases hMmax S hSF with ⟨E, hEM, hnd⟩
              exact Finset.mem_biUnion.mpr ⟨E, hEM, Finset.mem_filter.mpr ⟨hSF, hnd⟩⟩
          _ ≤ ∑ E ∈ M, (F.filter (fun S => ¬ Disjoint S E)).card := Finset.card_biUnion_le
      have hsum_le : ∑ E ∈ M, (F.filter (fun S => ¬ Disjoint S E)).card ≤ M.card * 3 := by
        calc ∑ E ∈ M, (F.filter (fun S => ¬ Disjoint S E)).card
            ≤ ∑ _E ∈ M, 3 := Finset.sum_le_sum hperE
          _ = M.card * 3 := by simp
      omega

/-- **Exact Small-Case Lower Bound `m(2, 3) ≥ 6` (`2 K_3`):**
There exists a `2`-uniform family of cardinality `6` containing no `3`-sunflower
(together with `ppl038_exact_f_2_3_upper`, this establishes exact `f(2, 3) = 7`). -/
theorem ppl038_exact_f_2_3_lower :
    ∃ F : Finset (Finset ℕ), F.card = 6 ∧ (∀ S ∈ F, S.card = 2) ∧
      ∀ G ⊆ F, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  let F : Finset (Finset ℕ) := {{0, 1}, {1, 2}, {0, 2}, {3, 4}, {4, 5}, {3, 5}}
  refine ⟨F, by decide, by decide, ?_⟩
  have hno3 : ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F,
      A ≠ B → A ≠ C → B ≠ C → ¬ (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C) := by decide
  intro G hGF hGcard ⟨K, hK⟩
  rcases Finset.card_eq_three.mp hGcard with ⟨A, B, C, hAB, hAC, hBC, rfl⟩
  have hAF : A ∈ F := hGF (by simp)
  have hBF : B ∈ F := hGF (by simp)
  have hCF : C ∈ F := hGF (by simp)
  have h1 : A ∩ B = K := hK A (by simp) B (by simp) hAB
  have h2 : A ∩ C = K := hK A (by simp) C (by simp) hAC
  have h3 : B ∩ C = K := hK B (by simp) C (by simp) hBC
  exact hno3 A hAF B hBF C hCF hAB hAC hBC ⟨h1.trans h2.symm, h1.trans h3.symm⟩

/-- Helper: Any intersecting `n`-uniform `3`-sunflower-free family of size `M` yields a
`3`-sunflower-free family of size `2 * M` by taking two disjoint copies. -/
private lemma two_disjoint_copies_3sf {n M : ℕ}
    (H : Finset (Finset ℕ)) (hHcard : H.card = M) (hHunif : ∀ S ∈ H, S.card = n)
    (hHint : ∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty)
    (hHsf : ∀ G ⊆ H, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K) :
    ∃ F : Finset (Finset ℕ), F.card = 2 * M ∧ (∀ S ∈ F, S.card = n) ∧
      ∀ G ⊆ F, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  classical
  let e0 : ℕ ↪ ℕ := ⟨fun x => 2 * x, fun x y h => by dsimp only at h; omega⟩
  let e1 : ℕ ↪ ℕ := ⟨fun x => 2 * x + 1, fun x y h => by dsimp only at h; omega⟩
  have he0 : ∀ x, e0 x = 2 * x := fun _ => rfl
  have he1 : ∀ x, e1 x = 2 * x + 1 := fun _ => rfl
  let H0 : Finset (Finset ℕ) := H.image (fun S => S.map e0)
  let H1 : Finset (Finset ℕ) := H.image (fun S => S.map e1)
  have hdisj_elem : ∀ A B : Finset ℕ, Disjoint (A.map e0) (B.map e1) := by
    intro A B
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rcases Finset.mem_map.mp hz1 with ⟨x, _, rfl⟩
    rcases Finset.mem_map.mp hz2 with ⟨y, _, hEq⟩
    rw [he0, he1] at hEq
    omega
  have hHne : ∀ S ∈ H, S.Nonempty := fun S hS => by
    have := hHint S hS S hS
    simpa using this
  have hdisjH : Disjoint H0 H1 := by
    rw [Finset.disjoint_left]
    intro X hX0 hX1
    rcases Finset.mem_image.mp hX0 with ⟨A, hAH, rfl⟩
    rcases Finset.mem_image.mp hX1 with ⟨B, _hBH, hEq⟩
    obtain ⟨x, hxA⟩ := hHne A hAH
    have hmem : e0 x ∈ B.map e1 := by rw [hEq]; exact Finset.mem_map.mpr ⟨x, hxA, rfl⟩
    exact Finset.disjoint_left.mp (hdisj_elem A B) (Finset.mem_map.mpr ⟨x, hxA, rfl⟩) hmem
  refine ⟨H0 ∪ H1, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisjH,
        Finset.card_image_of_injective _ (Finset.map_injective e0),
        Finset.card_image_of_injective _ (Finset.map_injective e1), hHcard]
    ring
  · intro S hS
    rcases Finset.mem_union.mp hS with hS0 | hS1
    · rcases Finset.mem_image.mp hS0 with ⟨A, hAH, rfl⟩
      rw [Finset.card_map, hHunif A hAH]
    · rcases Finset.mem_image.mp hS1 with ⟨A, hAH, rfl⟩
      rw [Finset.card_map, hHunif A hAH]
  · intro G hG hGcard ⟨K, hK⟩
    rcases Finset.card_eq_three.mp hGcard with ⟨X, Y, Z, hXY, hXZ, hYZ, rfl⟩
    have hX : X ∈ H0 ∪ H1 := hG (by simp)
    have hY : Y ∈ H0 ∪ H1 := hG (by simp)
    have hZ : Z ∈ H0 ∪ H1 := hG (by simp)
    have hKXY : X ∩ Y = K := hK X (by simp) Y (by simp) hXY
    have hKXZ : X ∩ Z = K := hK X (by simp) Z (by simp) hXZ
    have hKYZ : Y ∩ Z = K := hK Y (by simp) Z (by simp) hYZ
    -- Helper: if two sets lie in the same copy and the third in the other copy, contradiction!
    have hmix : ∀ A ∈ H0, ∀ B ∈ H0, ∀ C ∈ H1, A ∩ B = A ∩ C → False := by
      intro A hA B hB C hC hEq
      rcases Finset.mem_image.mp hA with ⟨A', hA'H, rfl⟩
      rcases Finset.mem_image.mp hB with ⟨B', hB'H, rfl⟩
      rcases Finset.mem_image.mp hC with ⟨C', _hC'H, rfl⟩
      obtain ⟨x, hx⟩ := hHint A' hA'H B' hB'H
      have hmemAB : e0 x ∈ A'.map e0 ∩ B'.map e0 :=
        Finset.mem_inter.mpr
          ⟨Finset.mem_map.mpr ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩,
           Finset.mem_map.mpr ⟨x, (Finset.mem_inter.mp hx).2, rfl⟩⟩
      rw [hEq] at hmemAB
      exact Finset.disjoint_left.mp (hdisj_elem A' C')
        (Finset.mem_inter.mp hmemAB).1 (Finset.mem_inter.mp hmemAB).2
    have hmix' : ∀ A ∈ H1, ∀ B ∈ H1, ∀ C ∈ H0, A ∩ B = A ∩ C → False := by
      intro A hA B hB C hC hEq
      rcases Finset.mem_image.mp hA with ⟨A', hA'H, rfl⟩
      rcases Finset.mem_image.mp hB with ⟨B', hB'H, rfl⟩
      rcases Finset.mem_image.mp hC with ⟨C', _hC'H, rfl⟩
      obtain ⟨x, hx⟩ := hHint A' hA'H B' hB'H
      have hmemAB : e1 x ∈ A'.map e1 ∩ B'.map e1 :=
        Finset.mem_inter.mpr
          ⟨Finset.mem_map.mpr ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩,
           Finset.mem_map.mpr ⟨x, (Finset.mem_inter.mp hx).2, rfl⟩⟩
      rw [hEq] at hmemAB
      exact Finset.disjoint_right.mp (hdisj_elem C' A')
        (Finset.mem_inter.mp hmemAB).1 (Finset.mem_inter.mp hmemAB).2
    -- Helper: if all 3 lie in H0 (or H1), pull back to H
    have hpull0 : X ∈ H0 → Y ∈ H0 → Z ∈ H0 → False := by
      intro hX0 hY0 hZ0
      rcases Finset.mem_image.mp hX0 with ⟨A, hAH, rfl⟩
      rcases Finset.mem_image.mp hY0 with ⟨B, hBH, rfl⟩
      rcases Finset.mem_image.mp hZ0 with ⟨C, hCH, rfl⟩
      have hAB : A ≠ B := fun h => hXY (by rw [h])
      have hAC : A ≠ C := fun h => hXZ (by rw [h])
      have hBC : B ≠ C := fun h => hYZ (by rw [h])
      have h1 : A ∩ B = A ∩ C := Finset.map_injective e0 (by
        rw [Finset.map_inter, Finset.map_inter, hKXY, hKXZ])
      have h2 : A ∩ B = B ∩ C := Finset.map_injective e0 (by
        rw [Finset.map_inter, Finset.map_inter, hKXY, hKYZ])
      refine hHsf {A, B, C} ?_ (Finset.card_eq_three.mpr ⟨A, B, C, hAB, hAC, hBC, rfl⟩) ⟨A ∩ B, ?_⟩
      · intro S hS; simp only [Finset.mem_insert, Finset.mem_singleton] at hS
        rcases hS with rfl | rfl | rfl <;> assumption
      · intro U hU V hV hUV
        simp only [Finset.mem_insert, Finset.mem_singleton] at hU hV
        rcases hU with rfl | rfl | rfl <;> rcases hV with rfl | rfl | rfl
        · exact (hUV rfl).elim
        · rfl
        · exact h1.symm
        · rw [Finset.inter_comm]
        · exact (hUV rfl).elim
        · exact h2.symm
        · rw [Finset.inter_comm]; exact h1.symm
        · rw [Finset.inter_comm]; exact h2.symm
        · exact (hUV rfl).elim
    have hpull1 : X ∈ H1 → Y ∈ H1 → Z ∈ H1 → False := by
      intro hX1 hY1 hZ1
      rcases Finset.mem_image.mp hX1 with ⟨A, hAH, rfl⟩
      rcases Finset.mem_image.mp hY1 with ⟨B, hBH, rfl⟩
      rcases Finset.mem_image.mp hZ1 with ⟨C, hCH, rfl⟩
      have hAB : A ≠ B := fun h => hXY (by rw [h])
      have hAC : A ≠ C := fun h => hXZ (by rw [h])
      have hBC : B ≠ C := fun h => hYZ (by rw [h])
      have h1 : A ∩ B = A ∩ C := Finset.map_injective e1 (by
        rw [Finset.map_inter, Finset.map_inter, hKXY, hKXZ])
      have h2 : A ∩ B = B ∩ C := Finset.map_injective e1 (by
        rw [Finset.map_inter, Finset.map_inter, hKXY, hKYZ])
      refine hHsf {A, B, C} ?_ (Finset.card_eq_three.mpr ⟨A, B, C, hAB, hAC, hBC, rfl⟩) ⟨A ∩ B, ?_⟩
      · intro S hS; simp only [Finset.mem_insert, Finset.mem_singleton] at hS
        rcases hS with rfl | rfl | rfl <;> assumption
      · intro U hU V hV hUV
        simp only [Finset.mem_insert, Finset.mem_singleton] at hU hV
        rcases hU with rfl | rfl | rfl <;> rcases hV with rfl | rfl | rfl
        · exact (hUV rfl).elim
        · rfl
        · exact h1.symm
        · rw [Finset.inter_comm]
        · exact (hUV rfl).elim
        · exact h2.symm
        · rw [Finset.inter_comm]; exact h1.symm
        · rw [Finset.inter_comm]; exact h2.symm
        · exact (hUV rfl).elim
    rcases Finset.mem_union.mp hX with hX0 | hX1 <;>
    rcases Finset.mem_union.mp hY with hY0 | hY1 <;>
    rcases Finset.mem_union.mp hZ with hZ0 | hZ1
    · exact hpull0 hX0 hY0 hZ0
    · exact hmix X hX0 Y hY0 Z hZ1 (hKXY.trans hKXZ.symm)
    · exact hmix X hX0 Z hZ0 Y hY1 (hKXZ.trans hKXY.symm)
    · exact hmix' Y hY1 Z hZ1 X hX0 (by rw [hKYZ, ← hKXY, Finset.inter_comm])
    · exact hmix Y hY0 Z hZ0 X hX1 (by rw [hKYZ, ← hKXY, Finset.inter_comm])
    · exact hmix' X hX1 Z hZ1 Y hY0 (hKXZ.trans hKXY.symm)
    · exact hmix' X hX1 Y hY1 Z hZ0 (hKXY.trans hKXZ.symm)
    · exact hpull1 hX1 hY1 hZ1

/-- **Hemi-Icosahedron Intersecting Family (`10` Triples) & Exact `m(3, 3) ≥ 20`:**
The `10` faces of the hemi-icosahedron on `{0, 1, 2, 3, 4, 5}` form an intersecting `3`-uniform
`3`-sunflower-free family; two disjoint copies give a `3`-uniform `3`-sunflower-free family
of cardinality `20` (matching the exact known value `m(3, 3) = 20`, i.e., `f(3, 3) = 21`). -/
theorem ppl038_hemi_icosahedron_m_3_3 :
    (∃ H : Finset (Finset ℕ), H.card = 10 ∧ (∀ S ∈ H, S.card = 3) ∧
      (∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty) ∧
      ∀ G ⊆ H, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K) ∧
    (∃ F : Finset (Finset ℕ), F.card = 20 ∧ (∀ S ∈ F, S.card = 3) ∧
      ∀ G ⊆ F, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K) := by
  let H : Finset (Finset ℕ) :=
    {{5, 0, 1}, {5, 1, 2}, {5, 2, 3}, {5, 3, 4}, {5, 4, 0},
     {0, 1, 3}, {1, 2, 4}, {2, 3, 0}, {3, 4, 1}, {4, 0, 2}}
  have hHcard : H.card = 10 := by decide
  have hHunif : ∀ S ∈ H, S.card = 3 := by decide
  have hHint : ∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty := by decide
  have hno3 : ∀ A ∈ H, ∀ B ∈ H, ∀ C ∈ H,
      A ≠ B → A ≠ C → B ≠ C → ¬ (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C) := by decide
  have hHsf : ∀ G ⊆ H, G.card = 3 →
      ¬ ∃ K : Finset ℕ, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
    intro G hGH hGcard ⟨K, hK⟩
    rcases Finset.card_eq_three.mp hGcard with ⟨A, B, C, hAB, hAC, hBC, rfl⟩
    exact hno3 A (hGH (by simp)) B (hGH (by simp)) C (hGH (by simp)) hAB hAC hBC
      ⟨(hK A (by simp) B (by simp) hAB).trans (hK A (by simp) C (by simp) hAC).symm,
       (hK A (by simp) B (by simp) hAB).trans (hK B (by simp) C (by simp) hBC).symm⟩
  refine ⟨⟨H, hHcard, hHunif, hHint, hHsf⟩, ?_⟩
  simpa using two_disjoint_copies_3sf H hHcard hHunif hHint hHsf

/-- **Wreath-Product Substitution Theorem (`A ≀ B`) for Intersecting `3`-Sunflower-Free Families:**
If `A` is an `a`-uniform intersecting `3`-sunflower-free family of size `M₁` and `B` is a
`b`-uniform intersecting `3`-sunflower-free family of size `M₂` (`b ≥ 1`), then their wreath
product `A ≀ B` is an `(a * b)`-uniform intersecting `3`-sunflower-free family of size
`M₁ * M₂ ^ a`. -/
theorem ppl038_wreath_product_3sf {a b M₁ M₂ : ℕ} (hb : 1 ≤ b)
    (hA : ∃ A : Finset (Finset ℕ), A.card = M₁ ∧ (∀ S ∈ A, S.card = a) ∧
      (∀ X ∈ A, ∀ Y ∈ A, (X ∩ Y).Nonempty) ∧
      ∀ G ⊆ A, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → X ∩ Y = K)
    (hB : ∃ B : Finset (Finset ℕ), B.card = M₂ ∧ (∀ T ∈ B, T.card = b) ∧
      (∀ X ∈ B, ∀ Y ∈ B, (X ∩ Y).Nonempty) ∧
      ∀ G ⊆ B, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → X ∩ Y = K) :
    ∃ F : Finset (Finset ℕ), F.card = M₁ * M₂ ^ a ∧ (∀ S ∈ F, S.card = a * b) ∧
      (∀ X ∈ F, ∀ Y ∈ F, (X ∩ Y).Nonempty) ∧
      ∀ G ⊆ F, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → X ∩ Y = K := by
  classical
  rcases hA with ⟨A, hAcard, hAunif, hAint, hAsf⟩
  rcases hB with ⟨B, hBcard, hBunif, hBint, hBsf⟩
  let M : ℕ := (B.biUnion id).sup id + 1
  have hMpos : 0 < M := Nat.succ_pos _
  have hBlt : ∀ T ∈ B, ∀ y ∈ T, y < M := by
    intro T hTB y hyT
    have hyU : y ∈ B.biUnion id := Finset.mem_biUnion.mpr ⟨T, hTB, hyT⟩
    have hle : y ≤ (B.biUnion id).sup id := Finset.le_sup (f := id) hyU
    omega
  -- Encode each `(S ∈ A, φ : {v // v ∈ S} → {T // T ∈ B})` into `Finset ℕ` via `v * M + y`
  let mkSet (S : Finset ℕ) (φ : {v // v ∈ S} → {T // T ∈ B}) : Finset ℕ :=
    S.attach.biUnion (fun v => (φ v).1.image (fun y => v.1 * M + y))
  have hpair_eq : ∀ v₁ v₂ y₁ y₂ : ℕ, y₁ < M → y₂ < M →
      v₁ * M + y₁ = v₂ * M + y₂ → v₁ = v₂ ∧ y₁ = y₂ := by
    intro v₁ v₂ y₁ y₂ hy₁ hy₂ hEq
    have hdiv : (v₁ * M + y₁) / M = (v₂ * M + y₂) / M := congrArg (· / M) hEq
    rw [mul_comm v₁ M, mul_comm v₂ M, Nat.mul_add_div hMpos, Nat.mul_add_div hMpos,
        Nat.div_eq_of_lt hy₁, Nat.div_eq_of_lt hy₂, add_zero, add_zero] at hdiv
    exact ⟨hdiv, by nlinarith⟩
  have hmk_mem : ∀ S (φ : {v // v ∈ S} → {T // T ∈ B}) v y, y < M →
      (v * M + y ∈ mkSet S φ ↔ ∃ hv : v ∈ S, y ∈ (φ ⟨v, hv⟩).1) := by
    intro S φ v y hy
    simp only [mkSet, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image,
      Subtype.exists]
    constructor
    · rintro ⟨v', hv', y', hy', hEq⟩
      have hy'lt : y' < M := hBlt _ (φ ⟨v', hv'⟩).2 y' hy'
      obtain ⟨hv_eq, hy_eq⟩ := hpair_eq v' v y' y hy'lt hy hEq
      subst hv_eq; subst hy_eq
      exact ⟨hv', hy'⟩
    · rintro ⟨hv, hyφ⟩
      exact ⟨v, hv, y, hyφ, rfl⟩
  have hmk_card : ∀ S ∈ A, ∀ (φ : {v // v ∈ S} → {T // T ∈ B}), (mkSet S φ).card = a * b := by
    intro S hSA φ
    dsimp only [mkSet]
    rw [Finset.card_biUnion]
    · have hper : ∀ v ∈ S.attach, ((φ v).1.image (fun y => v.1 * M + y)).card = b := by
        intro v _
        rw [Finset.card_image_of_injective _ (fun y₁ y₂ h => by omega), hBunif _ (φ v).2]
      rw [Finset.sum_congr rfl hper, Finset.sum_const, Finset.card_attach, smul_eq_mul,
          hAunif S hSA]
    · intro v₁ _ v₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rcases Finset.mem_image.mp hz1 with ⟨y₁, hy₁, rfl⟩
      rcases Finset.mem_image.mp hz2 with ⟨y₂, hy₂, hEq⟩
      have h1 := hBlt _ (φ v₁).2 y₁ hy₁
      have h2 := hBlt _ (φ v₂).2 y₂ hy₂
      have hv := (hpair_eq v₁.1 v₂.1 y₁ y₂ h1 h2 hEq.symm).1
      exact hne (Subtype.ext hv)
  have hmk_quot : ∀ S (φ : {v // v ∈ S} → {T // T ∈ B}),
      (mkSet S φ).image (· / M) = S := by
    intro S φ
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [mkSet, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image,
        Subtype.exists] at hz
      rcases hz with ⟨v', hv', y', hy', rfl⟩
      have hy'lt : y' < M := hBlt _ (φ ⟨v', hv'⟩).2 y' hy'
      rw [mul_comm v' M, Nat.mul_add_div hMpos, Nat.div_eq_of_lt hy'lt, add_zero]
      exact hv'
    · intro hv
      have hne : (φ ⟨v, hv⟩).1.Nonempty :=
        Finset.card_pos.mp (by rw [hBunif _ (φ ⟨v, hv⟩).2]; omega)
      obtain ⟨y, hy⟩ := hne
      have hylt : y < M := hBlt _ (φ ⟨v, hv⟩).2 y hy
      refine ⟨v * M + y, (hmk_mem S φ v y hylt).mpr ⟨hv, hy⟩, ?_⟩
      rw [mul_comm v M, Nat.mul_add_div hMpos, Nat.div_eq_of_lt hylt, add_zero]
  have hmk_inj_phi : ∀ S (φ₁ φ₂ : {v // v ∈ S} → {T // T ∈ B}),
      mkSet S φ₁ = mkSet S φ₂ → φ₁ = φ₂ := by
    intro S φ₁ φ₂ hEq
    funext ⟨v, hv⟩
    apply Subtype.ext
    ext y
    constructor
    · intro hy
      have hylt : y < M := hBlt _ (φ₁ ⟨v, hv⟩).2 y hy
      have hmem : v * M + y ∈ mkSet S φ₂ := by
        rw [← hEq]; exact (hmk_mem S φ₁ v y hylt).mpr ⟨hv, hy⟩
      rcases (hmk_mem S φ₂ v y hylt).mp hmem with ⟨_, hy2⟩
      exact hy2
    · intro hy
      have hylt : y < M := hBlt _ (φ₂ ⟨v, hv⟩).2 y hy
      have hmem : v * M + y ∈ mkSet S φ₁ := by
        rw [hEq]; exact (hmk_mem S φ₂ v y hylt).mpr ⟨hv, hy⟩
      rcases (hmk_mem S φ₁ v y hylt).mp hmem with ⟨_, hy1⟩
      exact hy1
  -- Build the wreath product `F` as a disjoint union over `S ∈ A`
  let block (S : Finset ℕ) : Finset (Finset ℕ) :=
    (Finset.univ : Finset ({v // v ∈ S} → {T // T ∈ B})).image (mkSet S)
  let F : Finset (Finset ℕ) := A.biUnion block
  have hblock_card : ∀ S ∈ A, (block S).card = M₂ ^ a := by
    intro S hSA
    dsimp only [block]
    rw [Finset.card_image_of_injective _ (hmk_inj_phi S), Finset.card_univ,
        Fintype.card_fun, Fintype.card_coe, Fintype.card_coe, hAunif S hSA, hBcard]
  have hblock_disj : (A : Set (Finset ℕ)).PairwiseDisjoint block := by
    intro S₁ _ S₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro X hX1 hX2
    rcases Finset.mem_image.mp hX1 with ⟨φ₁, _, rfl⟩
    rcases Finset.mem_image.mp hX2 with ⟨φ₂, _, hEq⟩
    have hq : S₁ = S₂ := by
      rw [← hmk_quot S₁ φ₁, ← hmk_quot S₂ φ₂, hEq]
    exact hne hq
  -- Helper: given X ∈ F, unpack its unique (S ∈ A, φ)
  have hunpack : ∀ X ∈ F, ∃ (S : Finset ℕ) (_ : S ∈ A) (φ : {v // v ∈ S} → {T // T ∈ B}),
      X = mkSet S φ := by
    intro X hXF
    rcases Finset.mem_biUnion.mp hXF with ⟨S, hSA, hXb⟩
    rcases Finset.mem_image.mp hXb with ⟨φ, _, rfl⟩
    exact ⟨S, hSA, φ, rfl⟩
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · -- Cardinality = M₁ * M₂ ^ a
    dsimp only [F]
    rw [Finset.card_biUnion hblock_disj, Finset.sum_congr rfl hblock_card,
        Finset.sum_const, smul_eq_mul, hAcard]
  · -- Uniformity = a * b
    intro X hXF
    rcases hunpack X hXF with ⟨S, hSA, φ, rfl⟩
    exact hmk_card S hSA φ
  · -- Intersecting
    intro X hXF Y hYF
    rcases hunpack X hXF with ⟨S₁, hS₁A, φ₁, rfl⟩
    rcases hunpack Y hYF with ⟨S₂, hS₂A, φ₂, rfl⟩
    obtain ⟨v, hv⟩ := hAint S₁ hS₁A S₂ hS₂A
    rcases Finset.mem_inter.mp hv with ⟨hv1, hv2⟩
    obtain ⟨y, hy⟩ := hBint (φ₁ ⟨v, hv1⟩).1 (φ₁ ⟨v, hv1⟩).2 (φ₂ ⟨v, hv2⟩).1 (φ₂ ⟨v, hv2⟩).2
    rcases Finset.mem_inter.mp hy with ⟨hy1, hy2⟩
    have hylt : y < M := hBlt _ (φ₁ ⟨v, hv1⟩).2 y hy1
    refine ⟨v * M + y, Finset.mem_inter.mpr
      ⟨(hmk_mem S₁ φ₁ v y hylt).mpr ⟨hv1, hy1⟩, (hmk_mem S₂ φ₂ v y hylt).mpr ⟨hv2, hy2⟩⟩⟩
  · -- No 3-sunflower!
    intro G hGF hGcard ⟨K, hK⟩
    rcases Finset.card_eq_three.mp hGcard with ⟨X₁, X₂, X₃, h12, h13, h23, rfl⟩
    have hX1 : X₁ ∈ F := hGF (by simp)
    have hX2 : X₂ ∈ F := hGF (by simp)
    have hX3 : X₃ ∈ F := hGF (by simp)
    have hK12 : X₁ ∩ X₂ = K := hK X₁ (by simp) X₂ (by simp) h12
    have hK13 : X₁ ∩ X₃ = K := hK X₁ (by simp) X₃ (by simp) h13
    have hK23 : X₂ ∩ X₃ = K := hK X₂ (by simp) X₃ (by simp) h23
    rcases hunpack X₁ hX1 with ⟨S₁, hS₁A, φ₁, rfl⟩
    rcases hunpack X₂ hX2 with ⟨S₂, hS₂A, φ₂, rfl⟩
    rcases hunpack X₃ hX3 with ⟨S₃, hS₃A, φ₃, rfl⟩
    -- Key helper: no element `v` can belong to two of `S₁, S₂, S₃` and miss the third!
    have hno_two_of_three :
        ∀ (U₁ U₂ U₃ : Finset ℕ)
          (ψ₁ : {v // v ∈ U₁} → {T // T ∈ B})
          (ψ₂ : {v // v ∈ U₂} → {T // T ∈ B})
          (ψ₃ : {v // v ∈ U₃} → {T // T ∈ B}),
          mkSet U₁ ψ₁ ∩ mkSet U₂ ψ₂ = mkSet U₁ ψ₁ ∩ mkSet U₃ ψ₃ →
          ∀ v, v ∈ U₁ → v ∈ U₂ → v ∉ U₃ → False := by
      intro U₁ U₂ U₃ ψ₁ ψ₂ ψ₃ hEq v hv1 hv2 hv3
      obtain ⟨y, hy⟩ := hBint (ψ₁ ⟨v, hv1⟩).1 (ψ₁ ⟨v, hv1⟩).2 (ψ₂ ⟨v, hv2⟩).1 (ψ₂ ⟨v, hv2⟩).2
      rcases Finset.mem_inter.mp hy with ⟨hy1, hy2⟩
      have hylt : y < M := hBlt _ (ψ₁ ⟨v, hv1⟩).2 y hy1
      have hmem12 : v * M + y ∈ mkSet U₁ ψ₁ ∩ mkSet U₂ ψ₂ :=
        Finset.mem_inter.mpr
          ⟨(hmk_mem U₁ ψ₁ v y hylt).mpr ⟨hv1, hy1⟩,
           (hmk_mem U₂ ψ₂ v y hylt).mpr ⟨hv2, hy2⟩⟩
      rw [hEq] at hmem12
      rcases (hmk_mem U₃ ψ₃ v y hylt).mp (Finset.mem_inter.mp hmem12).2 with ⟨hv3', _⟩
      exact hv3 hv3'
    -- Therefore S₁ ∩ S₂ = S₁ ∩ S₃ = S₂ ∩ S₃!
    have hS12_eq_S13 : S₁ ∩ S₂ = S₁ ∩ S₃ := by
      ext v
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hv1, hv2⟩
        refine ⟨hv1, ?_⟩
        by_contra hv3
        exact hno_two_of_three S₁ S₂ S₃ φ₁ φ₂ φ₃ (hK12.trans hK13.symm) v hv1 hv2 hv3
      · rintro ⟨hv1, hv3⟩
        refine ⟨hv1, ?_⟩
        by_contra hv2
        exact hno_two_of_three S₁ S₃ S₂ φ₁ φ₃ φ₂ (hK13.trans hK12.symm) v hv1 hv3 hv2
    have hS12_eq_S23 : S₁ ∩ S₂ = S₂ ∩ S₃ := by
      ext v
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hv1, hv2⟩
        refine ⟨hv2, ?_⟩
        by_contra hv3
        exact hno_two_of_three S₁ S₂ S₃ φ₁ φ₂ φ₃ (hK12.trans hK13.symm) v hv1 hv2 hv3
      · rintro ⟨hv2, hv3⟩
        refine ⟨?_, hv2⟩
        by_contra hv1
        exact hno_two_of_three S₂ S₃ S₁ φ₂ φ₃ φ₁
          (by rw [hK23, ← hK12, Finset.inter_comm]) v hv2 hv3 hv1
    -- Case split on whether S₁, S₂, S₃ are all equal, two equal, or all distinct
    by_cases hS12 : S₁ = S₂
    · subst hS12
      have hS13 : S₁ = S₃ := by
        have hsub : S₁ ⊆ S₃ := by
          intro v hv
          have : v ∈ S₁ ∩ S₃ := by rw [← hS12_eq_S13]; exact Finset.mem_inter.mpr ⟨hv, hv⟩
          exact (Finset.mem_inter.mp this).2
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hAunif S₁ hS₁A, hAunif S₃ hS₃A])
      subst hS13
      -- All three have the same base S₁, so φ₁, φ₂, φ₃ are pairwise distinct!
      have hφ12 : φ₁ ≠ φ₂ := fun h => h12 (by rw [h])
      have hφ13 : φ₁ ≠ φ₃ := fun h => h13 (by rw [h])
      have hφ23 : φ₂ ≠ φ₃ := fun h => h23 (by rw [h])
      -- Pick a coordinate v ∈ S₁ where φ₁ v ≠ φ₂ v
      have hex_v : ∃ v : {x // x ∈ S₁}, φ₁ v ≠ φ₂ v := by
        by_contra hall
        push Not at hall
        exact hφ12 (funext hall)
      rcases hex_v with ⟨⟨v, hv⟩, hne12⟩
      -- Restrict the pairwise intersections to block v
      have hblock_inter :
          (φ₁ ⟨v, hv⟩).1 ∩ (φ₂ ⟨v, hv⟩).1 = (φ₁ ⟨v, hv⟩).1 ∩ (φ₃ ⟨v, hv⟩).1 ∧
          (φ₁ ⟨v, hv⟩).1 ∩ (φ₂ ⟨v, hv⟩).1 = (φ₂ ⟨v, hv⟩).1 ∩ (φ₃ ⟨v, hv⟩).1 := by
        constructor
        · ext y
          simp only [Finset.mem_inter]
          constructor
          · rintro ⟨hy1, hy2⟩
            have hylt : y < M := hBlt _ (φ₁ ⟨v, hv⟩).2 y hy1
            have hm : v * M + y ∈ mkSet S₁ φ₁ ∩ mkSet S₁ φ₃ := by
              rw [hK13, ← hK12]
              exact Finset.mem_inter.mpr
                ⟨(hmk_mem S₁ φ₁ v y hylt).mpr ⟨hv, hy1⟩, (hmk_mem S₁ φ₂ v y hylt).mpr ⟨hv, hy2⟩⟩
            rcases (hmk_mem S₁ φ₃ v y hylt).mp (Finset.mem_inter.mp hm).2 with ⟨_, hy3⟩
            exact ⟨hy1, hy3⟩
          · rintro ⟨hy1, hy3⟩
            have hylt : y < M := hBlt _ (φ₁ ⟨v, hv⟩).2 y hy1
            have hm : v * M + y ∈ mkSet S₁ φ₁ ∩ mkSet S₁ φ₂ := by
              rw [hK12, ← hK13]
              exact Finset.mem_inter.mpr
                ⟨(hmk_mem S₁ φ₁ v y hylt).mpr ⟨hv, hy1⟩, (hmk_mem S₁ φ₃ v y hylt).mpr ⟨hv, hy3⟩⟩
            rcases (hmk_mem S₁ φ₂ v y hylt).mp (Finset.mem_inter.mp hm).2 with ⟨_, hy2⟩
            exact ⟨hy1, hy2⟩
        · ext y
          simp only [Finset.mem_inter]
          constructor
          · rintro ⟨hy1, hy2⟩
            have hylt : y < M := hBlt _ (φ₁ ⟨v, hv⟩).2 y hy1
            have hm : v * M + y ∈ mkSet S₁ φ₂ ∩ mkSet S₁ φ₃ := by
              rw [hK23, ← hK12]
              exact Finset.mem_inter.mpr
                ⟨(hmk_mem S₁ φ₁ v y hylt).mpr ⟨hv, hy1⟩, (hmk_mem S₁ φ₂ v y hylt).mpr ⟨hv, hy2⟩⟩
            rcases (hmk_mem S₁ φ₃ v y hylt).mp (Finset.mem_inter.mp hm).2 with ⟨_, hy3⟩
            exact ⟨hy2, hy3⟩
          · rintro ⟨hy2, hy3⟩
            have hylt : y < M := hBlt _ (φ₂ ⟨v, hv⟩).2 y hy2
            have hm : v * M + y ∈ mkSet S₁ φ₁ ∩ mkSet S₁ φ₂ := by
              rw [hK12, ← hK23]
              exact Finset.mem_inter.mpr
                ⟨(hmk_mem S₁ φ₂ v y hylt).mpr ⟨hv, hy2⟩, (hmk_mem S₁ φ₃ v y hylt).mpr ⟨hv, hy3⟩⟩
            rcases (hmk_mem S₁ φ₁ v y hylt).mp (Finset.mem_inter.mp hm).1 with ⟨_, hy1⟩
            exact ⟨hy1, hy2⟩
      let T₁ := (φ₁ ⟨v, hv⟩).1
      let T₂ := (φ₂ ⟨v, hv⟩).1
      let T₃ := (φ₃ ⟨v, hv⟩).1
      change T₁ ∩ T₂ = T₁ ∩ T₃ ∧ T₁ ∩ T₂ = T₂ ∩ T₃ at hblock_inter
      have hT12 : T₁ ≠ T₂ := fun h => hne12 (Subtype.ext h)
      have hT13 : T₁ ≠ T₃ := by
        intro hEq
        have hsub : T₁ ⊆ T₂ := by
          intro y hy
          have : y ∈ T₁ ∩ T₂ := by
            rw [hblock_inter.1, ← hEq]; exact Finset.mem_inter.mpr ⟨hy, hy⟩
          exact (Finset.mem_inter.mp this).2
        exact hT12 (Finset.eq_of_subset_of_card_le hsub
          (by rw [hBunif _ (φ₁ ⟨v, hv⟩).2, hBunif _ (φ₂ ⟨v, hv⟩).2]))
      have hT23 : T₂ ≠ T₃ := by
        intro hEq
        have hsub : T₂ ⊆ T₁ := by
          intro y hy
          have : y ∈ T₁ ∩ T₂ := by
            rw [hblock_inter.2, ← hEq]; exact Finset.mem_inter.mpr ⟨hy, hy⟩
          exact (Finset.mem_inter.mp this).1
        exact hT12 (Finset.eq_of_subset_of_card_le hsub
          (by rw [hBunif _ (φ₂ ⟨v, hv⟩).2, hBunif _ (φ₁ ⟨v, hv⟩).2])).symm
      refine hBsf {T₁, T₂, T₃} ?_ (Finset.card_eq_three.mpr ⟨T₁, T₂, T₃, hT12, hT13, hT23, rfl⟩)
        ⟨T₁ ∩ T₂, ?_⟩
      · intro T hT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl | rfl
        · exact (φ₁ ⟨v, hv⟩).2
        · exact (φ₂ ⟨v, hv⟩).2
        · exact (φ₃ ⟨v, hv⟩).2
      · intro U hU V hV hUV
        simp only [Finset.mem_insert, Finset.mem_singleton] at hU hV
        rcases hU with rfl | rfl | rfl <;> rcases hV with rfl | rfl | rfl
        · exact (hUV rfl).elim
        · rfl
        · exact hblock_inter.1.symm
        · rw [Finset.inter_comm]
        · exact (hUV rfl).elim
        · exact hblock_inter.2.symm
        · rw [Finset.inter_comm]; exact hblock_inter.1.symm
        · rw [Finset.inter_comm]; exact hblock_inter.2.symm
        · exact (hUV rfl).elim
    · -- S₁ ≠ S₂ => show S₁ ≠ S₃ and S₂ ≠ S₃, then {S₁, S₂, S₃} is a 3-sunflower in A!
      have hS13 : S₁ ≠ S₃ := by
        intro hEq
        have hsub : S₁ ⊆ S₂ := by
          intro v hv
          have : v ∈ S₁ ∩ S₂ := by rw [hS12_eq_S13, ← hEq]; exact Finset.mem_inter.mpr ⟨hv, hv⟩
          exact (Finset.mem_inter.mp this).2
        exact hS12 (Finset.eq_of_subset_of_card_le hsub (by rw [hAunif S₁ hS₁A, hAunif S₂ hS₂A]))
      have hS23 : S₂ ≠ S₃ := by
        intro hEq
        have hsub : S₂ ⊆ S₁ := by
          intro v hv
          have : v ∈ S₁ ∩ S₂ := by rw [hS12_eq_S23, ← hEq]; exact Finset.mem_inter.mpr ⟨hv, hv⟩
          exact (Finset.mem_inter.mp this).1
        exact hS12 (Finset.eq_of_subset_of_card_le hsub
          (by rw [hAunif S₂ hS₂A, hAunif S₁ hS₁A])).symm
      refine hAsf {S₁, S₂, S₃} ?_ (Finset.card_eq_three.mpr ⟨S₁, S₂, S₃, hS12, hS13, hS23, rfl⟩)
        ⟨S₁ ∩ S₂, ?_⟩
      · intro S hS
        simp only [Finset.mem_insert, Finset.mem_singleton] at hS
        rcases hS with rfl | rfl | rfl <;> assumption
      · intro U hU V hV hUV
        simp only [Finset.mem_insert, Finset.mem_singleton] at hU hV
        rcases hU with rfl | rfl | rfl <;> rcases hV with rfl | rfl | rfl
        · exact (hUV rfl).elim
        · rfl
        · exact hS12_eq_S13.symm
        · rw [Finset.inter_comm]
        · exact (hUV rfl).elim
        · exact hS12_eq_S23.symm
        · rw [Finset.inter_comm]; exact hS12_eq_S13.symm
        · rw [Finset.inter_comm]; exact hS12_eq_S23.symm
        · exact (hUV rfl).elim

/-- **Abbott–Hanson (1974) Exponential Lower Bound (`2 * 10 ^ ((3 ^ t - 1) / 2)` for `r = 3`):**
For every `t ≥ 1`, there exists a `3 ^ t`-uniform family of cardinality
`2 * 10 ^ ((3 ^ t - 1) / 2)` containing no `3`-sunflower (asymptotic exponential base
`√10 ≈ 3.1623`, beating the classical `(r - 1) ^ n = 2 ^ n` bound exponentially). -/
theorem ppl038_abbott_hanson_lower_bound (t : ℕ) (ht : 1 ≤ t) :
    ∃ F : Finset (Finset ℕ),
      F.card = 2 * 10 ^ ((3 ^ t - 1) / 2) ∧
      (∀ S ∈ F, S.card = 3 ^ t) ∧
      ∀ G ⊆ F, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  -- First prove by induction on `k ≥ 1` that there is an intersecting `3 ^ k`-uniform
  -- `3`-sunflower-free family of cardinality `10 ^ ((3 ^ k - 1) / 2)`.
  have hbase := ppl038_hemi_icosahedron_m_3_3.1
  have hind : ∀ k : ℕ, 1 ≤ k →
      ∃ H : Finset (Finset ℕ), H.card = 10 ^ ((3 ^ k - 1) / 2) ∧ (∀ S ∈ H, S.card = 3 ^ k) ∧
        (∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty) ∧
        ∀ G ⊆ H, G.card = 3 → ¬ ∃ K : Finset ℕ, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro _
      by_cases hk0 : k = 0
      · subst hk0
        simpa using hbase
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hw := ppl038_wreath_product_3sf (by norm_num : 1 ≤ 3) (ih hk1) hbase
        rcases hw with ⟨H, hHcard, hHunif, hHint, hHsf⟩
        refine ⟨H, ?_, ?_, hHint, hHsf⟩
        · have hexp : (3 ^ k - 1) / 2 + 3 ^ k = (3 ^ (k + 1) - 1) / 2 := by
            have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
            have h2 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ']
            have hodd : 3 ^ k % 2 = 1 := by
              clear hHcard hHunif hHint hHsf ih hbase hk1 hk0
              induction k with
              | zero => simp
              | succ m ihm => rw [pow_succ]; omega
            omega
          rw [hHcard, ← pow_add, hexp]
        · intro S hS
          rw [hHunif S hS, pow_succ]
  rcases hind t ht with ⟨H, hHcard, hHunif, hHint, hHsf⟩
  exact two_disjoint_copies_3sf H hHcard hHunif hHint hHsf

end PPL038
