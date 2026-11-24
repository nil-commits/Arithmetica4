/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Arithmetica4 Extension: Matroids, Intersection & Poset Möbius Inversion (`Arith4Ext.MatroidsPosets`)

Reusable Tier A `Arithmetica4` library module built 100% from scratch on targeted Mathlib
imports (`0` monolithic `import Mathlib`, `0` Tier C imports, `0` custom axioms).

## Exported API (`namespace Arith4Ext.MatroidsPosets`)
1. **Finite Matroids, Rank Submodularity, Circuits & Strong Basis Exchange:**
   - `FinMatroid E`, `FinMatroid.rank`, `FinMatroid.IsBasis`, `FinMatroid.IsCircuit`
   - `FinMatroid.rank_mono`, `FinMatroid.rank_submodular`, `FinMatroid.exists_basis_extension`
   - `FinMatroid.basis_card_eq`, `FinMatroid.circuit_elimination`, `FinMatroid.circuit_unique_in_insert`
   - `FinMatroid.strong_basis_exchange`
2. **Rado–Edmonds Greedy, Rado Transversal & Edmonds Matroid Intersection:**
   - `matroid_greedy_exists`, `matroid_greedy_optimal`, `matroid_greedy_local_exchange_optimal`
   - `rado_transversal_theorem`
   - `edmonds_matroid_intersection`
3. **Finite Poset Möbius Function, Inversion, Weisner, Rota Cross-Cut & Specializations:**
   - `mobiusFn`, `mobiusFn_not_le`, `mobiusFn_self`, `mobiusFn_sum_left`, `mobiusFn_sum_right`
   - `poset_mobius_inversion_left`, `poset_mobius_inversion_right`
   - `weisner_theorem`, `weisner_theorem_dual`
   - `rota_crosscut_join`, `rota_crosscut_theorem`
   - `boolean_lattice_mobius`, `divisor_lattice_mobius`, `exists_divisor_poset`
-/

namespace Arith4Ext.MatroidsPosets

open scoped BigOperators

/-! ### Section 1: Finite Matroids, Rank Submodularity, Circuits & Strong Basis Exchange -/

/-- A finite matroid on ground type `E`, specified by its independent sets (`Finset E`). -/
structure FinMatroid (E : Type*) [DecidableEq E] where
  Indep : Finset E → Prop
  indep_empty : Indep ∅
  indep_subset : ∀ {I J : Finset E}, Indep J → I ⊆ J → Indep I
  indep_aug : ∀ {I J : Finset E}, Indep I → Indep J → I.card < J.card →
    ∃ e ∈ J \ I, Indep (insert e I)

namespace FinMatroid

/-- Rank of a finite subset `A : Finset E` in `M`, defined as the maximum cardinality of an
independent subset of `A`. -/
noncomputable def rank {E : Type*} [DecidableEq E] (M : FinMatroid E) (A : Finset E) : ℕ := by
  classical
  exact (A.powerset.filter M.Indep).sup Finset.card

/-- Maximal independent subset of the ground type `E`. -/
def IsBasis {E : Type*} [DecidableEq E] (M : FinMatroid E) (B : Finset E) : Prop :=
  M.Indep B ∧ ∀ e : E, M.Indep (insert e B) → e ∈ B

/-- Minimal dependent subset of `E`. -/
def IsCircuit {E : Type*} [DecidableEq E] (M : FinMatroid E) (C : Finset E) : Prop :=
  ¬ M.Indep C ∧ ∀ e ∈ C, M.Indep (C.erase e)

lemma le_rank {E : Type*} [DecidableEq E] (M : FinMatroid E) {I A : Finset E}
    (hIA : I ⊆ A) (hI : M.Indep I) : I.card ≤ M.rank A := by
  classical
  rw [rank]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hIA, hI⟩)

lemma exists_indep_card_eq_rank {E : Type*} [DecidableEq E] (M : FinMatroid E) (A : Finset E) :
    ∃ I ⊆ A, M.Indep I ∧ I.card = M.rank A := by
  classical
  have hne : (A.powerset.filter M.Indep).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset A), M.indep_empty⟩⟩
  obtain ⟨I, hImem, hIsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rcases Finset.mem_filter.mp hImem with ⟨hIA, hI⟩
  exact ⟨I, Finset.mem_powerset.mp hIA, hI, hIsup.symm⟩

lemma rank_le_card {E : Type*} [DecidableEq E] (M : FinMatroid E) (A : Finset E) :
    M.rank A ≤ A.card := by
  classical
  rw [rank]
  exact Finset.sup_le fun I hI =>
    Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1)

@[simp]
lemma rank_empty {E : Type*} [DecidableEq E] (M : FinMatroid E) : M.rank ∅ = 0 :=
  Nat.eq_zero_of_le_zero (M.rank_le_card ∅)

lemma rank_eq_card_iff_indep {E : Type*} [DecidableEq E] (M : FinMatroid E) (I : Finset E) :
    M.rank I = I.card ↔ M.Indep I := by
  constructor
  · intro heq
    obtain ⟨J, hJI, hJ, hJcard⟩ := M.exists_indep_card_eq_rank I
    have hEq : J = I := Finset.eq_of_subset_of_card_le hJI (by omega)
    exact hEq ▸ hJ
  · intro hI
    exact le_antisymm (M.rank_le_card I) (M.le_rank Finset.Subset.rfl hI)

lemma rank_mono {E : Type*} [DecidableEq E] (M : FinMatroid E) {A B : Finset E}
    (hAB : A ⊆ B) : M.rank A ≤ M.rank B := by
  obtain ⟨I, hIA, hI, hcard⟩ := M.exists_indep_card_eq_rank A
  rw [← hcard]
  exact M.le_rank (hIA.trans hAB) hI

lemma rank_insert_le {E : Type*} [DecidableEq E] (M : FinMatroid E) (e : E) (A : Finset E) :
    M.rank (insert e A) ≤ M.rank A + 1 := by
  obtain ⟨I, hI_sub, hI, hcard⟩ := M.exists_indep_card_eq_rank (insert e A)
  rw [← hcard]
  have hsub : I.erase e ⊆ A := fun x hx => by
    rcases Finset.mem_erase.mp hx with ⟨hxe, hxI⟩
    rcases Finset.mem_insert.mp (hI_sub hxI) with rfl | hxA
    · exact absurd rfl hxe
    · exact hxA
  have hle : (I.erase e).card ≤ M.rank A :=
    M.le_rank hsub (M.indep_subset hI (Finset.erase_subset _ _))
  by_cases heI : e ∈ I
  · have h := Finset.card_erase_add_one heI; omega
  · rw [Finset.erase_eq_of_notMem heI] at hle; omega

/-- Every independent subset `I ⊆ A` extends to a maximum-rank independent subset of `A`. -/
theorem exists_basis_extension {E : Type*} [DecidableEq E] (M : FinMatroid E)
    {I A : Finset E} (hIA : I ⊆ A) (hI : M.Indep I) :
    ∃ J : Finset E, I ⊆ J ∧ J ⊆ A ∧ M.Indep J ∧ J.card = M.rank A := by
  classical
  let cands : Finset (Finset E) := A.powerset.filter (fun J => I ⊆ J ∧ M.Indep J)
  have hne : cands.Nonempty :=
    ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hIA, Finset.Subset.rfl, hI⟩⟩
  obtain ⟨J, hJmem, hJmax⟩ := Finset.exists_max_image cands Finset.card hne
  rcases Finset.mem_filter.mp hJmem with ⟨hJA', hIJ, hJ⟩
  have hJA : J ⊆ A := Finset.mem_powerset.mp hJA'
  refine ⟨J, hIJ, hJA, hJ, le_antisymm (M.le_rank hJA hJ) ?_⟩
  by_contra hlt
  have hlt' : J.card < M.rank A := Nat.lt_of_not_le hlt
  obtain ⟨B, hBA, hB, hBcard⟩ := M.exists_indep_card_eq_rank A
  rw [← hBcard] at hlt'
  obtain ⟨e, he, hJe⟩ := M.indep_aug hJ hB hlt'
  rcases Finset.mem_sdiff.mp he with ⟨heB, heJ⟩
  have hmem : insert e J ∈ cands := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.insert_subset (hBA heB) hJA),
      hIJ.trans (Finset.subset_insert _ _), hJe⟩
  have hle := hJmax (insert e J) hmem
  rw [Finset.card_insert_of_notMem heJ] at hle
  omega

/-- **Matroid Rank Submodularity**: `r(A ∪ B) + r(A ∩ B) ≤ r(A) + r(B)`. -/
theorem rank_submodular {E : Type*} [DecidableEq E] (M : FinMatroid E) (A B : Finset E) :
    M.rank (A ∪ B) + M.rank (A ∩ B) ≤ M.rank A + M.rank B := by
  obtain ⟨I, hIAB, hI, hIcard⟩ := M.exists_indep_card_eq_rank (A ∩ B)
  obtain ⟨J, hIJ, hJ_un, hJ, hJcard⟩ :=
    M.exists_basis_extension (hIAB.trans Finset.inter_subset_union) hI
  have hJA_ind : M.Indep (J ∩ A) := M.indep_subset hJ Finset.inter_subset_left
  have hJB_ind : M.Indep (J ∩ B) := M.indep_subset hJ Finset.inter_subset_left
  have hJA_le : (J ∩ A).card ≤ M.rank A := M.le_rank Finset.inter_subset_right hJA_ind
  have hJB_le : (J ∩ B).card ≤ M.rank B := M.le_rank Finset.inter_subset_right hJB_ind
  have hun : (J ∩ A) ∪ (J ∩ B) = J := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hxJ, _⟩ | ⟨hxJ, _⟩) <;> exact hxJ
    · intro hxJ
      rcases Finset.mem_union.mp (hJ_un hxJ) with hxA | hxB
      · exact Or.inl ⟨hxJ, hxA⟩
      · exact Or.inr ⟨hxJ, hxB⟩
  have hin : I ⊆ (J ∩ A) ∩ (J ∩ B) := fun x hx =>
    Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hIJ hx, (Finset.mem_inter.mp (hIAB hx)).1⟩,
      Finset.mem_inter.mpr ⟨hIJ hx, (Finset.mem_inter.mp (hIAB hx)).2⟩⟩
  have hadd := Finset.card_union_add_card_inter (J ∩ A) (J ∩ B)
  rw [hun] at hadd
  have hin_le : I.card ≤ ((J ∩ A) ∩ (J ∩ B)).card := Finset.card_le_card hin
  rw [← hJcard, ← hIcard]
  omega

lemma rank_insert_eq_of_circuit {E : Type*} [DecidableEq E] (M : FinMatroid E)
    {C X : Finset E} {e : E} (hC : M.IsCircuit C) (heC : e ∈ C) (hsub : C.erase e ⊆ X) :
    M.rank (insert e X) = M.rank X := by
  refine le_antisymm ?_ (M.rank_mono (Finset.subset_insert e X))
  by_cases heX : e ∈ X
  · rw [Finset.insert_eq_of_mem heX]
  · have hsub_mod := M.rank_submodular X C
    have hun : X ∪ C = insert e X := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro (hx | hxC)
        · exact Or.inr hx
        · by_cases hxe : x = e
          · exact Or.inl hxe
          · exact Or.inr (hsub (Finset.mem_erase.mpr ⟨hxe, hxC⟩))
      · rintro (rfl | hx)
        · exact Or.inr heC
        · exact Or.inl hx
    have hin : X ∩ C = C.erase e := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨hxX, hxC⟩
        exact ⟨fun h => by subst h; exact heX hxX, hxC⟩
      · rintro ⟨hxe, hxC⟩
        exact ⟨hsub (Finset.mem_erase.mpr ⟨hxe, hxC⟩), hxC⟩
    have hrank_er : M.rank (C.erase e) = (C.erase e).card :=
      (M.rank_eq_card_iff_indep _).mpr (hC.2 e heC)
    have hrank_C : M.rank C = (C.erase e).card := by
      refine le_antisymm ?_ ?_
      · by_contra hgt
        have hge : (C.erase e).card + 1 ≤ M.rank C := Nat.lt_of_not_le hgt
        have hC_card : (C.erase e).card + 1 = C.card := Finset.card_erase_add_one heC
        have hC_eq : M.rank C = C.card := le_antisymm (M.rank_le_card C) (hC_card ▸ hge)
        exact hC.1 ((M.rank_eq_card_iff_indep C).mp hC_eq)
      · rw [← hrank_er]
        exact M.rank_mono (Finset.erase_subset _ _)
    rw [hun, hin, hrank_er, hrank_C] at hsub_mod
    omega

lemma rank_union_eq_of_subset_cl {E : Type*} [DecidableEq E] (M : FinMatroid E)
    {A B : Finset E} (hA : M.Indep A) (hB : M.Indep B) (hcard : A.card = B.card)
    (hcl : ∀ a ∈ A, M.rank (insert a B) = M.rank B) (S : Finset E) :
    M.rank (A ∪ S) = M.rank (B ∪ S) := by
  have hcl_gen : ∀ (T₁ T₂ : Finset E), (∀ t ∈ T₁, M.rank (insert t T₂) = M.rank T₂) →
      ∀ U : Finset E, M.rank (T₁ ∪ (T₂ ∪ U)) = M.rank (T₂ ∪ U) := by
    intro T₁ T₂ hT U
    induction T₁ using Finset.induction_on with
    | empty => simp
    | @insert a T₁' ha ih =>
      have h1 : insert a T₁' ∪ (T₂ ∪ U) = insert a (T₁' ∪ (T₂ ∪ U)) := Finset.insert_union _ _ _
      rw [h1]
      have hsub := M.rank_submodular (insert a T₂) (T₁' ∪ (T₂ ∪ U))
      have hun : insert a T₂ ∪ (T₁' ∪ (T₂ ∪ U)) = insert a (T₁' ∪ (T₂ ∪ U)) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      have hin : T₂ ⊆ insert a T₂ ∩ (T₁' ∪ (T₂ ∪ U)) := fun x hx =>
        Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx,
          Finset.mem_union_right _ (Finset.mem_union_left _ hx)⟩
      have hT₂_le : M.rank T₂ ≤ M.rank (insert a T₂ ∩ (T₁' ∪ (T₂ ∪ U))) := M.rank_mono hin
      have ha_cl : M.rank (insert a T₂) = M.rank T₂ := hT a (Finset.mem_insert_self _ _)
      have hih := ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
      rw [hun, ha_cl] at hsub
      have hge : M.rank (T₁' ∪ (T₂ ∪ U)) ≤ M.rank (insert a (T₁' ∪ (T₂ ∪ U))) :=
        M.rank_mono (Finset.subset_insert _ _)
      omega
  have h_AB : M.rank (A ∪ B) = M.rank B := by
    simpa using hcl_gen A B hcl ∅
  have hcl_rev : ∀ b ∈ B, M.rank (insert b A) = M.rank A := by
    intro b hb
    have h1 : M.rank (insert b A) ≤ M.rank (A ∪ B) :=
      M.rank_mono (Finset.insert_subset (Finset.mem_union_right _ hb) Finset.subset_union_left)
    rw [h_AB, (M.rank_eq_card_iff_indep B).mpr hB, ← hcard,
      ← (M.rank_eq_card_iff_indep A).mpr hA] at h1
    exact le_antisymm h1 (M.rank_mono (Finset.subset_insert _ _))
  have h1 : M.rank (A ∪ (B ∪ S)) = M.rank (B ∪ S) := hcl_gen A B hcl S
  have h2 : M.rank (B ∪ (A ∪ S)) = M.rank (A ∪ S) := hcl_gen B A hcl_rev S
  rw [Finset.union_left_comm] at h2
  rw [← h1, h2]

lemma basis_card_eq {E : Type*} [DecidableEq E] (M : FinMatroid E)
    {B₁ B₂ : Finset E} (h1 : M.IsBasis B₁) (h2 : M.IsBasis B₂) : B₁.card = B₂.card := by
  have hle : ∀ X Y : Finset E, M.IsBasis X → M.IsBasis Y → X.card ≤ Y.card := by
    intro X Y hX hY
    by_contra hlt
    have hlt' : Y.card < X.card := Nat.lt_of_not_le hlt
    obtain ⟨e, he, hYe⟩ := M.indep_aug hY.1 hX.1 hlt'
    exact (Finset.mem_sdiff.mp he).2 (hY.2 e hYe)
  exact le_antisymm (hle B₁ B₂ h1 h2) (hle B₂ B₁ h2 h1)

lemma exists_circuit_of_dep {E : Type*} [DecidableEq E] (M : FinMatroid E)
    {D : Finset E} (hD : ¬ M.Indep D) : ∃ C ⊆ D, M.IsCircuit C := by
  classical
  let deps : Finset (Finset E) := D.powerset.filter (fun C => ¬ M.Indep C)
  have hne : deps.Nonempty := ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hD⟩⟩
  obtain ⟨C, hCmem, hCmin⟩ := Finset.exists_min_image deps Finset.card hne
  rcases Finset.mem_filter.mp hCmem with ⟨hCD', hCdep⟩
  refine ⟨C, Finset.mem_powerset.mp hCD', hCdep, fun e heC => ?_⟩
  by_contra hdep
  have her_mem : C.erase e ∈ deps := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp hCD')), hdep⟩
  have hle := hCmin (C.erase e) her_mem
  have hlt := Finset.card_erase_lt_of_mem heC
  omega

/-- **Circuit Elimination Axiom**: for any two distinct circuits `C₁ ≠ C₂` with `e ∈ C₁ ∩ C₂`,
there exists a circuit `C₃ ⊆ (C₁ ∪ C₂).erase e`. -/
theorem circuit_elimination {E : Type*} [DecidableEq E] (M : FinMatroid E)
    {C₁ C₂ : Finset E} (h1 : M.IsCircuit C₁) (h2 : M.IsCircuit C₂)
    (hne : C₁ ≠ C₂) {e : E} (he1 : e ∈ C₁) (he2 : e ∈ C₂) :
    ∃ C₃ ⊆ (C₁ ∪ C₂).erase e, M.IsCircuit C₃ := by
  apply M.exists_circuit_of_dep
  intro hind
  have hle_rank : ((C₁ ∪ C₂).erase e).card ≤ M.rank (C₁ ∪ C₂) :=
    M.le_rank (Finset.erase_subset _ _) hind
  have h_sub : M.Indep (C₁ ∩ C₂) := by
    have hss : C₁ ∩ C₂ ⊂ C₁ ∨ C₁ ∩ C₂ ⊂ C₂ := by
      by_contra hnot
      push Not at hnot
      have hC1 : C₁ ⊆ C₂ := fun x hx =>
        if hC1eq : C₁ ∩ C₂ = C₁ then (Finset.inter_eq_left.mp hC1eq) hx
        else absurd (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hC1eq⟩) hnot.1
      have hC2 : C₂ ⊆ C₁ := fun x hx =>
        if hC2eq : C₁ ∩ C₂ = C₂ then (Finset.inter_eq_right.mp hC2eq) hx
        else absurd (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, hC2eq⟩) hnot.2
      exact hne (le_antisymm hC1 hC2)
    rcases hss with hs | hs
    · obtain ⟨x, hx1, hx12⟩ := (Finset.ssubset_iff_of_subset Finset.inter_subset_left).mp hs
      exact M.indep_subset (h1.2 x hx1) (Finset.subset_erase.mpr ⟨Finset.inter_subset_left, hx12⟩)
    · obtain ⟨x, hx2, hx12⟩ := (Finset.ssubset_iff_of_subset Finset.inter_subset_right).mp hs
      exact M.indep_subset (h2.2 x hx2) (Finset.subset_erase.mpr ⟨Finset.inter_subset_right, hx12⟩)
  have hrank_inter : M.rank (C₁ ∩ C₂) = (C₁ ∩ C₂).card := (M.rank_eq_card_iff_indep _).mpr h_sub
  have hrank_C1 : M.rank C₁ = C₁.card - 1 := by
    have hrer : M.rank (C₁.erase e) = (C₁.erase e).card := (M.rank_eq_card_iff_indep _).mpr (h1.2 e he1)
    rw [Finset.card_erase_of_mem he1] at hrer
    refine le_antisymm ?_ (hrer ▸ M.rank_mono (Finset.erase_subset _ _))
    by_contra hgt
    have hge : C₁.card ≤ M.rank C₁ := by omega
    exact h1.1 ((M.rank_eq_card_iff_indep C₁).mp (le_antisymm (M.rank_le_card C₁) hge))
  have hrank_C2 : M.rank C₂ = C₂.card - 1 := by
    have hrer : M.rank (C₂.erase e) = (C₂.erase e).card := (M.rank_eq_card_iff_indep _).mpr (h2.2 e he2)
    rw [Finset.card_erase_of_mem he2] at hrer
    refine le_antisymm ?_ (hrer ▸ M.rank_mono (Finset.erase_subset _ _))
    by_contra hgt
    have hge : C₂.card ≤ M.rank C₂ := by omega
    exact h2.1 ((M.rank_eq_card_iff_indep C₂).mp (le_antisymm (M.rank_le_card C₂) hge))
  have hsubmod := M.rank_submodular C₁ C₂
  rw [hrank_inter, hrank_C1, hrank_C2] at hsubmod
  have hadd := Finset.card_union_add_card_inter C₁ C₂
  have he_un : e ∈ C₁ ∪ C₂ := Finset.mem_union_left _ he1
  have h_er_card := Finset.card_erase_of_mem he_un
  have h1pos : 1 ≤ C₁.card := Finset.one_le_card.mpr ⟨e, he1⟩
  have h2pos : 1 ≤ C₂.card := Finset.one_le_card.mpr ⟨e, he2⟩
  omega

/-- Fundamental circuit uniqueness: if `M.Indep I` and `¬ M.Indep (insert e I)`, there exists a
unique circuit `C ⊆ insert e I`, and `e ∈ C`. -/
theorem circuit_unique_in_insert {E : Type*} [DecidableEq E] (M : FinMatroid E)
    {I : Finset E} {e : E} (hI : M.Indep I) (hdep : ¬ M.Indep (insert e I)) :
    ∃! C : Finset E, C ⊆ insert e I ∧ M.IsCircuit C := by
  obtain ⟨C, hCsub, hC⟩ := M.exists_circuit_of_dep hdep
  refine ⟨C, ⟨hCsub, hC⟩, ?_⟩
  rintro C' ⟨hC'sub, hC'⟩
  by_contra hne
  have heC : e ∈ C := by
    by_contra he
    exact hC.1 (M.indep_subset hI (fun x hx => by
      rcases Finset.mem_insert.mp (hCsub hx) with rfl | hxI
      · exact absurd hx he
      · exact hxI))
  have heC' : e ∈ C' := by
    by_contra he
    exact hC'.1 (M.indep_subset hI (fun x hx => by
      rcases Finset.mem_insert.mp (hC'sub hx) with rfl | hxI
      · exact absurd hx he
      · exact hxI))
  obtain ⟨C₃, hC₃sub, hC₃⟩ := M.circuit_elimination hC' hC hne heC' heC
  have hC₃I : C₃ ⊆ I := fun x hx => by
    rcases Finset.mem_erase.mp (hC₃sub hx) with ⟨hxe, hxun⟩
    rcases Finset.mem_union.mp hxun with hx' | hxC
    · rcases Finset.mem_insert.mp (hC'sub hx') with rfl | hxI
      · exact absurd rfl hxe
      · exact hxI
    · rcases Finset.mem_insert.mp (hCsub hxC) with rfl | hxI
      · exact absurd rfl hxe
      · exact hxI
  exact hC₃.1 (M.indep_subset hI hC₃I)

/-- **Strong Basis Exchange (Brualdi 1969)**: for any two bases `B₁, B₂` and any `e ∈ B₁ \ B₂`,
there exists `f ∈ B₂ \ B₁` such that both `insert f (B₁.erase e)` and `insert e (B₂.erase f)`
are bases. -/
theorem strong_basis_exchange {E : Type*} [DecidableEq E] (M : FinMatroid E)
    {B₁ B₂ : Finset E} (hB₁ : M.IsBasis B₁) (hB₂ : M.IsBasis B₂) {e : E} (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.IsBasis (insert f (B₁.erase e)) ∧ M.IsBasis (insert e (B₂.erase f)) := by
  rcases Finset.mem_sdiff.mp he with ⟨heB₁, heB₂⟩
  have hdep2 : ¬ M.Indep (insert e B₂) := fun h => heB₂ (hB₂.2 e h)
  obtain ⟨C, ⟨hCsub, hC⟩, hCuniq⟩ := M.circuit_unique_in_insert hB₂.1 hdep2
  have heC : e ∈ C := by
    by_contra he'
    exact hC.1 (M.indep_subset hB₂.1 (fun x hx => by
      rcases Finset.mem_insert.mp (hCsub hx) with rfl | hxB₂
      · exact absurd hx he'
      · exact hxB₂))
  let X : Finset E := (B₁ ∪ C).erase e
  have hB₁er_sub : B₁.erase e ⊆ X := fun x hx =>
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_union_left _ (Finset.mem_erase.mp hx).2⟩
  have hB₁er_ind : M.Indep (B₁.erase e) := M.indep_subset hB₁.1 (Finset.erase_subset _ _)
  have hX_rank : B₁.card ≤ M.rank X := by
    have hCer_sub : C.erase e ⊆ X := fun x hx =>
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_union_right _ (Finset.mem_erase.mp hx).2⟩
    have hreq := M.rank_insert_eq_of_circuit hC heC hCer_sub
    have hB₁_sub : B₁ ⊆ insert e X := fun x hx => by
      by_cases hxe : x = e
      · subst hxe; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxe, Finset.mem_union_left _ hx⟩)
    calc B₁.card = M.rank B₁ := ((M.rank_eq_card_iff_indep B₁).mpr hB₁.1).symm
      _ ≤ M.rank (insert e X) := M.rank_mono hB₁_sub
      _ = M.rank X := hreq
  obtain ⟨J, hB₁J, hJX, hJind, hJcard⟩ := M.exists_basis_extension hB₁er_sub hB₁er_ind
  have hJ_le_B₁ : J.card ≤ B₁.card := by
    by_contra hlt
    have hlt' : B₁.card < J.card := Nat.lt_of_not_le hlt
    obtain ⟨g, hg, hB₁g⟩ := M.indep_aug hB₁.1 hJind hlt'
    exact (Finset.mem_sdiff.mp hg).2 (hB₁.2 g hB₁g)
  have hJ_eq_card : J.card = B₁.card := le_antisymm hJ_le_B₁ (hJcard ▸ hX_rank)
  have hJ_basis : M.IsBasis J := ⟨hJind, fun x hx => by
    by_contra hxJ
    have hlt : B₁.card < (insert x J).card := by rw [Finset.card_insert_of_notMem hxJ]; omega
    obtain ⟨g, hg, hB₁g⟩ := M.indep_aug hB₁.1 hx hlt
    exact (Finset.mem_sdiff.mp hg).2 (hB₁.2 g hB₁g)⟩
  have hdiff_card : (J \ B₁.erase e).card = 1 := by
    rw [Finset.card_sdiff_of_subset hB₁J, hJ_eq_card, Finset.card_erase_of_mem heB₁]
    have hpos : 1 ≤ B₁.card := Finset.one_le_card.mpr ⟨e, heB₁⟩
    omega
  obtain ⟨f, hf_eq⟩ := Finset.card_eq_one.mp hdiff_card
  have hf_mem : f ∈ J \ B₁.erase e := hf_eq ▸ Finset.mem_singleton_self f
  rcases Finset.mem_sdiff.mp hf_mem with ⟨hfJ, hfB₁er⟩
  have hfX := hJX hfJ
  rcases Finset.mem_erase.mp hfX with ⟨hfe, hf_un⟩
  have hfB₁ : f ∉ B₁ := fun h => hfB₁er (Finset.mem_erase.mpr ⟨hfe, h⟩)
  have hfC : f ∈ C := (Finset.mem_union.mp hf_un).resolve_left hfB₁
  have hfB₂ : f ∈ B₂ := by
    rcases Finset.mem_insert.mp (hCsub hfC) with rfl | hf2
    · exact absurd rfl hfe
    · exact hf2
  have hJ_eq : J = insert f (B₁.erase e) := by
    ext x
    simp only [Finset.mem_insert]
    constructor
    · intro hxJ
      by_cases hx_er : x ∈ B₁.erase e
      · exact Or.inr hx_er
      · left
        have hx_diff : x ∈ J \ B₁.erase e := Finset.mem_sdiff.mpr ⟨hxJ, hx_er⟩
        rw [hf_eq] at hx_diff
        exact Finset.mem_singleton.mp hx_diff
    · rintro (rfl | hx_er)
      · exact hfJ
      · exact hB₁J hx_er
  have h2_ind : M.Indep (insert e (B₂.erase f)) := by
    by_contra hdep
    obtain ⟨C', hC'sub, hC'⟩ := M.exists_circuit_of_dep hdep
    have hC'_in : C' ⊆ insert e B₂ := hC'sub.trans (Finset.insert_subset_insert e (Finset.erase_subset _ _))
    have heqCC' : C' = C := hCuniq C' ⟨hC'_in, hC'⟩
    rw [heqCC'] at hC'sub
    have hf_ins := hC'sub hfC
    rcases Finset.mem_insert.mp hf_ins with rfl | hf_er
    · exact hfe rfl
    · exact (Finset.mem_erase.mp hf_er).1 rfl
  have h2_card : (insert e (B₂.erase f)).card = B₂.card := by
    have he_not : e ∉ B₂.erase f := fun h => heB₂ (Finset.erase_subset _ _ h)
    rw [Finset.card_insert_of_notMem he_not, Finset.card_erase_of_mem hfB₂]
    have hpos : 1 ≤ B₂.card := Finset.one_le_card.mpr ⟨f, hfB₂⟩
    omega
  have h2_basis : M.IsBasis (insert e (B₂.erase f)) := ⟨h2_ind, fun x hx => by
    by_contra hx2
    have hlt : B₂.card < (insert x (insert e (B₂.erase f))).card := by
      rw [Finset.card_insert_of_notMem hx2, h2_card]; omega
    obtain ⟨g, hg, hB₂g⟩ := M.indep_aug hB₂.1 hx hlt
    exact (Finset.mem_sdiff.mp hg).2 (hB₂.2 g hB₂g)⟩
  exact ⟨f, Finset.mem_sdiff.mpr ⟨hfB₂, hfB₁⟩, hJ_eq ▸ hJ_basis, h2_basis⟩

end FinMatroid

/-! ### Section 2: Rado–Edmonds Greedy, Rado Transversal & Edmonds Intersection -/

/-- **Rado–Edmonds Greedy Existence**: for any finite matroid `M` on `E` and weight `w : E → ℝ`,
there exists a basis `G` matching the rank of every upper-level set `{e | t ≤ w e}` and
satisfying the local-exchange optimality condition. -/
theorem matroid_greedy_exists {E : Type*} [Fintype E] [DecidableEq E]
    (M : FinMatroid E) (w : E → ℝ) :
    ∃ G : Finset E, M.IsBasis G ∧
      (∀ t : ℝ, (G.filter (fun e => t ≤ w e)).card =
        M.rank (Finset.univ.filter (fun e => t ≤ w e))) ∧
      (∀ g ∈ G, ∀ x : E, x ∉ G → M.Indep (insert x (G.erase g)) → w x ≤ w g) := by
  classical
  let W : Finset ℝ := (Finset.univ : Finset E).image w
  have hex_prefix : ∀ k : ℕ, ∀ T : Finset ℝ, T.card ≤ k → T ⊆ W →
      (∀ s ∈ T, ∀ t ∈ W, s ≤ t → t ∈ T) →
      ∃ G_T : Finset E, M.Indep G_T ∧
        G_T ⊆ Finset.univ.filter (fun e => w e ∈ T) ∧
        (∀ t ∈ T, (G_T.filter (fun e => t ≤ w e)).card =
          M.rank (Finset.univ.filter (fun e => t ≤ w e))) ∧
        G_T.card = M.rank (Finset.univ.filter (fun e => w e ∈ T)) := by
    intro k
    induction k with
    | zero =>
      intro T hT _ _
      rw [Nat.le_zero, Finset.card_eq_zero] at hT
      subst hT
      exact ⟨∅, M.indep_empty, by simp, fun t ht => by simp at ht, by simp⟩
    | succ k ihk =>
      intro T hTk hTW hT_up
      by_cases hTne : T.Nonempty
      · let tmin := T.min' hTne
        have htmin_mem : tmin ∈ T := Finset.min'_mem T hTne
        let T' := T.erase tmin
        have hT'k : T'.card ≤ k := by
          have h1 : T'.card < T.card := Finset.card_erase_lt_of_mem htmin_mem
          omega
        have hT'W : T' ⊆ W := (Finset.erase_subset _ _).trans hTW
        have hT'_up : ∀ s ∈ T', ∀ t ∈ W, s ≤ t → t ∈ T' := by
          intro s hs t ht hst
          rcases Finset.mem_erase.mp hs with ⟨hsne, hsT⟩
          have htT : t ∈ T := hT_up s hsT t ht hst
          have hle : tmin ≤ s := Finset.min'_le T s hsT
          exact Finset.mem_erase.mpr ⟨fun h => by subst h; exact hsne (le_antisymm hst hle), htT⟩
        obtain ⟨G', hG'_ind, hG'_sub, hG'_pref, hG'_card⟩ := ihk T' hT'k hT'W hT'_up
        let U_T : Finset E := Finset.univ.filter (fun e => w e ∈ T)
        have hG'_subU : G' ⊆ U_T := fun e he => by
          have he' := Finset.mem_filter.mp (hG'_sub he)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.erase_subset _ _ he'.2⟩
        obtain ⟨G, hG'G, hGU, hG_ind, hG_card⟩ := M.exists_basis_extension hG'_subU hG'_ind
        refine ⟨G, hG_ind, hGU, fun t ht => ?_, hG_card⟩
        by_cases hteq : t = tmin
        · subst hteq
          have h1 : G.filter (fun e => tmin ≤ w e) = G := by
            ext e; simp only [Finset.mem_filter, and_iff_left_iff_imp]
            intro he
            exact Finset.min'_le T (w e) (Finset.mem_filter.mp (hGU he)).2
          have h2 : Finset.univ.filter (fun e => tmin ≤ w e) = U_T := by
            ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, U_T]
            constructor
            · intro hle
              exact hT_up tmin htmin_mem (w e) (Finset.mem_image_of_mem w (Finset.mem_univ e)) hle
            · intro hmem; exact Finset.min'_le T (w e) hmem
          rw [h1, h2, hG_card]
        · have htT' : t ∈ T' := Finset.mem_erase.mpr ⟨hteq, ht⟩
          have hfil_eq : G.filter (fun e => t ≤ w e) = G'.filter (fun e => t ≤ w e) := by
            ext e
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨heG, htle⟩ => ⟨?_, htle⟩, fun ⟨heG', htle⟩ => ⟨hG'G heG', htle⟩⟩
            by_contra heG'
            have hweT' : w e ∈ T' := Finset.mem_erase.mpr
              ⟨(lt_of_lt_of_le (lt_of_le_of_ne (Finset.min'_le T t ht) (Ne.symm hteq)) htle).ne',
                hT_up t ht (w e) (Finset.mem_image_of_mem w (Finset.mem_univ e)) htle⟩
            have hins_sub : insert e G' ⊆ Finset.univ.filter (fun x => w x ∈ T') :=
              Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hweT'⟩) hG'_sub
            have hins_ind : M.Indep (insert e G') :=
              M.indep_subset hG_ind (Finset.insert_subset heG hG'G)
            have hle := M.le_rank hins_sub hins_ind
            rw [Finset.card_insert_of_notMem heG', hG'_card] at hle
            omega
          rw [hfil_eq]
          exact hG'_pref t htT'
      · rw [Finset.not_nonempty_iff_eq_empty.mp hTne]
        exact ⟨∅, M.indep_empty, by simp, fun t ht => by simp at ht, by simp⟩
  obtain ⟨G, hG_ind, _, hG_pref, hG_card⟩ :=
    hex_prefix W.card W le_rfl Finset.Subset.rfl (fun _ _ _ ht _ => ht)
  have hU_eq : Finset.univ.filter (fun e : E => w e ∈ W) = Finset.univ := by
    ext e; simp [W]
  rw [hU_eq] at hG_card
  have hG_basis : M.IsBasis G := ⟨hG_ind, fun x hx => by
    by_contra hxG
    have hle := M.le_rank (Finset.subset_univ (insert x G)) hx
    rw [Finset.card_insert_of_notMem hxG, hG_card] at hle
    omega⟩
  have hG_all : ∀ t : ℝ, (G.filter (fun e => t ≤ w e)).card =
      M.rank (Finset.univ.filter (fun e => t ≤ w e)) := by
    intro t
    by_cases hne : (W.filter (fun s => t ≤ s)).Nonempty
    · let t' := (W.filter (fun s => t ≤ s)).min' hne
      have ht'_mem : t' ∈ W := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
      have hiff : ∀ e : E, t ≤ w e ↔ t' ≤ w e := fun e =>
        ⟨fun h => Finset.min'_le _ (w e)
            (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem w (Finset.mem_univ e), h⟩),
          fun h => le_trans (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2 h⟩
      have h1 : G.filter (fun e => t ≤ w e) = G.filter (fun e => t' ≤ w e) := by
        ext e; simp only [Finset.mem_filter, hiff e]
      have h2 : Finset.univ.filter (fun e => t ≤ w e) = Finset.univ.filter (fun e => t' ≤ w e) := by
        ext e; simp only [Finset.mem_filter, hiff e]
      rw [h1, h2]
      exact hG_pref t' ht'_mem
    · have h_lt : ∀ e : E, w e < t := fun e => by
        by_contra hle
        exact hne ⟨w e, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem w (Finset.mem_univ e),
          le_of_not_gt hle⟩⟩
      have h1 : G.filter (fun e => t ≤ w e) = ∅ := by
        ext e; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_le]
        intro _; exact h_lt e
      have h2 : Finset.univ.filter (fun e => t ≤ w e) = ∅ := by
        ext e; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_le]
        intro _; exact h_lt e
      rw [h1, h2, Finset.card_empty, M.rank_empty]
  refine ⟨G, hG_basis, hG_all, fun g hg x hxG hx => ?_⟩
  by_contra hlt
  have hlt' : w g < w x := lt_of_not_ge hlt
  have hsub : insert x (G.filter (fun e => w x ≤ w e)) ⊆ insert x (G.erase g) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hyf
    · exact Finset.mem_insert_self _ _
    · rcases Finset.mem_filter.mp hyf with ⟨hyG, hyw⟩
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨fun h => by subst h; exact (lt_irrefl _ (lt_of_lt_of_le hlt' hyw)), hyG⟩)
  have hind : M.Indep (insert x (G.filter (fun e => w x ≤ w e))) := M.indep_subset hx hsub
  have hins_sub : insert x (G.filter (fun e => w x ≤ w e)) ⊆ Finset.univ.filter (fun e => w x ≤ w e) :=
    Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)
      (fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩)
  have hle := M.le_rank hins_sub hind
  have hx_not : x ∉ G.filter (fun e => w x ≤ w e) := fun h => hxG (Finset.mem_filter.mp h).1
  rw [Finset.card_insert_of_notMem hx_not, hG_all (w x)] at hle
  omega

/-- **Rado–Edmonds Greedy Optimality Theorem**: for any nonnegative weight function `w : E → ℝ`,
any independent set `G` attaining `M.rank {e | t ≤ w e}` on every threshold `t` achieves maximum
weight over all independent sets `I`. -/
theorem matroid_greedy_optimal {E : Type*} [Fintype E] [DecidableEq E]
    (M : FinMatroid E) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    (G : Finset E)
    (hG_greedy : ∀ t : ℝ, (G.filter (fun e => t ≤ w e)).card =
      M.rank (Finset.univ.filter (fun e => t ≤ w e))) :
    ∀ I : Finset E, M.Indep I → ∑ e ∈ I, w e ≤ ∑ e ∈ G, w e := by
  classical
  intro I hI
  let W : Finset ℝ := (Finset.univ : Finset E).image w
  let prev : ℝ → ℝ := fun t =>
    ((insert 0 (W.filter (fun s => s < t))).max' ⟨0, Finset.mem_insert_self _ _⟩)
  have hprev_lt : ∀ t ∈ W, 0 < t → prev t < t := by
    intro t _ ht0
    dsimp only [prev]
    exact (Finset.max'_lt_iff _ _).mpr fun s hs => by
      rcases Finset.mem_insert.mp hs with rfl | hsf
      · exact ht0
      · exact (Finset.mem_filter.mp hsf).2
  have hprev_nonneg : ∀ t : ℝ, 0 ≤ prev t := fun t =>
    Finset.le_max' _ 0 (Finset.mem_insert_self _ _)
  let gap : ℝ → ℝ := fun t => if 0 < t then t - prev t else 0
  have hgap_nonneg : ∀ t ∈ W, 0 ≤ gap t := by
    intro t ht
    dsimp only [gap]
    split_ifs with ht0
    · exact sub_nonneg.mpr (hprev_lt t ht ht0).le
    · exact le_rfl
  have hw_decomp : ∀ e : E, w e = ∑ t ∈ W, if t ≤ w e then gap t else 0 := by
    intro e
    have he_mem : w e ∈ W := Finset.mem_image_of_mem w (Finset.mem_univ e)
    have h_all : ∀ k : ℕ, ∀ v ∈ insert (0 : ℝ) W,
        (W.filter (fun s => s ≤ v)).card ≤ k →
        v = ∑ t ∈ W, if t ≤ v then gap t else 0 := by
      intro k
      induction k with
      | zero =>
        intro v hv hk
        rw [Nat.le_zero, Finset.card_eq_zero] at hk
        have hv_zero : v = 0 := by
          rcases Finset.mem_insert.mp hv with rfl | hvW
          · rfl
          · exfalso
            have hmem : v ∈ W.filter (fun s => s ≤ v) := Finset.mem_filter.mpr ⟨hvW, le_rfl⟩
            rw [hk] at hmem; simp at hmem
        subst hv_zero
        have hzero : ∀ t ∈ W, (if t ≤ (0 : ℝ) then gap t else 0) = 0 := fun t htW => by
          split_ifs with ht0
          · have ht_nonneg : 0 ≤ t := by
              rcases Finset.mem_image.mp htW with ⟨x, _, rfl⟩; exact hw x
            have hteq0 : t = 0 := le_antisymm ht0 ht_nonneg
            simp [gap, hteq0]
          · rfl
        rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
      | succ k ihk =>
        intro v hv hvk
        by_cases hv0 : v = 0
        · subst hv0
          have hzero : ∀ t ∈ W, (if t ≤ (0 : ℝ) then gap t else 0) = 0 := fun t htW => by
            split_ifs with ht0
            · have ht_nonneg : 0 ≤ t := by
                rcases Finset.mem_image.mp htW with ⟨x, _, rfl⟩; exact hw x
              have hteq0 : t = 0 := le_antisymm ht0 ht_nonneg
              simp [gap, hteq0]
            · rfl
          rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
        · have hvW : v ∈ W := (Finset.mem_insert.mp hv).resolve_left hv0
          have hv_pos : 0 < v := lt_of_le_of_ne (by
            rcases Finset.mem_image.mp hvW with ⟨x, _, rfl⟩; exact hw x) (Ne.symm hv0)
          let pv := prev v
          have hpv_lt : pv < v := hprev_lt v hvW hv_pos
          have hpv_mem : pv ∈ insert (0 : ℝ) W := by
            have hm := Finset.max'_mem (insert (0 : ℝ) (W.filter (fun s => s < v)))
              ⟨0, Finset.mem_insert_self _ _⟩
            rcases Finset.mem_insert.mp hm with h0 | hf
            · exact h0 ▸ Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mp hf).1
          have hpv_sub : W.filter (fun s => s ≤ pv) ⊂ W.filter (fun s => s ≤ v) := by
            rw [Finset.ssubset_iff_of_subset]
            · exact ⟨v, Finset.mem_filter.mpr ⟨hvW, le_rfl⟩,
                fun h => not_le_of_gt hpv_lt (Finset.mem_filter.mp h).2⟩
            · intro s hs
              rcases Finset.mem_filter.mp hs with ⟨hsW, hspv⟩
              exact Finset.mem_filter.mpr ⟨hsW, le_trans hspv hpv_lt.le⟩
          have hpv_card : (W.filter (fun s => s ≤ pv)).card ≤ k := by
            have hlt := Finset.card_lt_card hpv_sub; omega
          have hih := ihk pv hpv_mem hpv_card
          have hstep_eq : ∀ t ∈ W, (if t ≤ v then gap t else 0) =
              (if t ≤ pv then gap t else 0) + (if t = v then gap v else 0) := by
            intro t htW
            by_cases htv : t = v
            · subst htv
              simp [not_le_of_gt hpv_lt]
            · have hiff : t ≤ v ↔ t ≤ pv := by
                constructor
                · intro hle
                  have hlt_tv : t < v := lt_of_le_of_ne hle htv
                  exact Finset.le_max' _ t (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨htW, hlt_tv⟩))
                · intro hle; exact le_trans hle hpv_lt.le
              simp [htv, hiff]
          rw [Finset.sum_congr rfl hstep_eq, Finset.sum_add_distrib, ← hih]
          have h_single : ∑ t ∈ W, (if t = v then gap v else 0) = gap v := by
            simp [hvW]
          rw [h_single]
          simp [gap, hv_pos, pv]
    exact h_all W.card (w e) (Finset.mem_insert_of_mem he_mem)
      (Finset.card_le_card (Finset.filter_subset _ _))
  have hsum_eq : ∀ S : Finset E, ∑ e ∈ S, w e =
      ∑ t ∈ W, gap t * ((S.filter (fun e => t ≤ w e)).card : ℝ) := by
    intro S
    calc ∑ e ∈ S, w e
        = ∑ e ∈ S, ∑ t ∈ W, (if t ≤ w e then gap t else 0) :=
            Finset.sum_congr rfl fun e _ => hw_decomp e
      _ = ∑ t ∈ W, ∑ e ∈ S, (if t ≤ w e then gap t else 0) := Finset.sum_comm
      _ = ∑ t ∈ W, gap t * ((S.filter (fun e => t ≤ w e)).card : ℝ) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hsum_eq I, hsum_eq G]
  refine Finset.sum_le_sum fun t ht => ?_
  have hI_le : (I.filter (fun e => t ≤ w e)).card ≤
      M.rank (Finset.univ.filter (fun e => t ≤ w e)) :=
    M.le_rank (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
      (M.indep_subset hI (Finset.filter_subset _ _))
  rw [← hG_greedy t] at hI_le
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hI_le) (hgap_nonneg t ht)

/-- **Rado–Edmonds Local-Exchange Converse**: for any nonnegative weight function `w : E → ℝ`,
any basis `G` satisfying `∀ g ∈ G, ∀ x ∉ G, M.Indep (insert x (G.erase g)) → w x ≤ w g` achieves
maximum weight over all independent sets `I`. -/
theorem matroid_greedy_local_exchange_optimal {E : Type*} [Fintype E] [DecidableEq E]
    (M : FinMatroid E) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    (G : Finset E) (hG_basis : M.IsBasis G)
    (h_exch : ∀ g ∈ G, ∀ x : E, x ∉ G → M.Indep (insert x (G.erase g)) → w x ≤ w g) :
    ∀ I : Finset E, M.Indep I → ∑ e ∈ I, w e ≤ ∑ e ∈ G, w e := by
  classical
  refine matroid_greedy_optimal M w hw G (fun t => ?_)
  let Ut : Finset E := Finset.univ.filter (fun e => t ≤ w e)
  refine le_antisymm
    (M.le_rank (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
      (M.indep_subset hG_basis.1 (Finset.filter_subset _ _))) ?_
  by_contra hlt
  have hlt' : (G.filter (fun e => t ≤ w e)).card < M.rank Ut := Nat.lt_of_not_le hlt
  have hGt_sub : G.filter (fun e => t ≤ w e) ⊆ Ut := fun e he =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩
  obtain ⟨J, hGJ, hJUt, hJind, hJcard⟩ :=
    M.exists_basis_extension hGt_sub (M.indep_subset hG_basis.1 (Finset.filter_subset _ _))
  have hss : G.filter (fun e => t ≤ w e) ⊂ J :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hGJ, fun h => by rw [h, hJcard] at hlt'; exact lt_irrefl _ hlt'⟩
  obtain ⟨x, hxJ, hxGt⟩ := (Finset.ssubset_iff_of_subset hGJ).mp hss
  have hxUt := Finset.mem_filter.mp (hJUt hxJ)
  have hx_not_G : x ∉ G := fun h => hxGt (Finset.mem_filter.mpr ⟨h, hxUt.2⟩)
  have hdep : ¬ M.Indep (insert x G) := fun h => hx_not_G (hG_basis.2 x h)
  obtain ⟨C, ⟨hCsub, hC⟩, hCuniq⟩ := M.circuit_unique_in_insert hG_basis.1 hdep
  have hex_g : ∃ g ∈ C, g ∈ G ∧ w g < t := by
    by_contra hnone
    push Not at hnone
    have hC_sub_J : C ⊆ J := fun y hy => by
      rcases Finset.mem_insert.mp (hCsub hy) with rfl | hyG
      · exact hxJ
      · exact hGJ (Finset.mem_filter.mpr ⟨hyG, hnone y hy hyG⟩)
    exact hC.1 (M.indep_subset hJind hC_sub_J)
  obtain ⟨g, hgC, hgG, hgw⟩ := hex_g
  have h_ex_ind : M.Indep (insert x (G.erase g)) := by
    by_contra hdep_er
    obtain ⟨C', hC'sub, hC'⟩ := M.exists_circuit_of_dep hdep_er
    have heqCC' : C' = C :=
      hCuniq C' ⟨hC'sub.trans (Finset.insert_subset_insert x (Finset.erase_subset _ _)), hC'⟩
    rw [heqCC'] at hC'sub
    rcases Finset.mem_insert.mp (hC'sub hgC) with rfl | hger
    · exact hx_not_G hgG
    · exact (Finset.mem_erase.mp hger).1 rfl
  have hle := h_exch g hgG x hx_not_G h_ex_ind
  linarith [hxUt.2]

/-- **Rado's Matroid-Hall Transversal Theorem (1942)**: a family `(S i)_{i ∈ I}` admits an
injective `M`-independent transversal iff `∀ J ⊆ I, J.card ≤ M.rank (J.biUnion S)`. -/
theorem rado_transversal_theorem {ι E : Type*} [DecidableEq ι] [DecidableEq E]
    (M : FinMatroid E) (I : Finset ι) (S : ι → Finset E) :
    (∃ f : I → E, (∀ i : I, f i ∈ S i.1) ∧ Function.Injective f ∧
        M.Indep (Finset.univ.image f)) ↔
      (∀ J ⊆ I, J.card ≤ M.rank (J.biUnion S)) := by
  classical
  constructor
  · rintro ⟨f, hfS, hf_inj, hf_ind⟩ J hJI
    let fJ : J → E := fun i => f ⟨i.1, hJI i.2⟩
    have hfJ_inj : Function.Injective fJ := fun i₁ i₂ h => by
      have := hf_inj h; exact Subtype.ext (congrArg (Subtype.val : I → ι) this)
    have hsub : Finset.univ.image fJ ⊆ J.biUnion S := fun e he => by
      rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨i.1, i.2, hfS ⟨i.1, hJI i.2⟩⟩
    have hind : M.Indep (Finset.univ.image fJ) := by
      refine M.indep_subset hf_ind (fun e he => ?_)
      rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
      exact Finset.mem_image_of_mem f (Finset.mem_univ _)
    have hcard : (Finset.univ.image fJ).card = J.card := by
      rw [Finset.card_image_of_injective _ hfJ_inj, Finset.card_univ, Fintype.card_coe]
    rw [← hcard]
    exact M.le_rank hsub hind
  · intro hRado
    have hshrink : ∀ m : ℕ, ∀ T : ι → Finset E, (∑ i ∈ I, (T i).card) ≤ m →
        (∀ J ⊆ I, J.card ≤ M.rank (J.biUnion T)) →
        ∃ T' : ι → Finset E, (∀ i ∈ I, T' i ⊆ T i) ∧ (∀ i ∈ I, (T' i).card = 1) ∧
          (∀ J ⊆ I, J.card ≤ M.rank (J.biUnion T')) := by
      intro m
      induction m with
      | zero =>
        intro T hm hT
        refine ⟨T, fun _ _ => Finset.Subset.rfl, fun i hi => ?_, hT⟩
        have h1 : 1 ≤ M.rank (({i} : Finset ι).biUnion T) := by
          simpa using hT {i} (Finset.singleton_subset_iff.mpr hi)
        have h2 : M.rank (T i) ≤ (T i).card := M.rank_le_card (T i)
        have h3 : (T i).card ≤ ∑ j ∈ I, (T j).card :=
          Finset.single_le_sum (f := fun j => (T j).card) (fun _ _ => Nat.zero_le _) hi
        simp only [Finset.singleton_biUnion] at h1
        omega
      | succ m ihm =>
        intro T hm hT
        by_cases hall : ∀ i ∈ I, (T i).card ≤ 1
        · refine ⟨T, fun _ _ => Finset.Subset.rfl, fun i hi => ?_, hT⟩
          have h1 : 1 ≤ (T i).card := by
            have := hT {i} (Finset.singleton_subset_iff.mpr hi)
            simp only [Finset.card_singleton, Finset.singleton_biUnion] at this
            exact le_trans this (M.rank_le_card _)
          exact le_antisymm (hall i hi) h1
        · push Not at hall
          obtain ⟨i₀, hi₀I, hi₀_gt⟩ := hall
          have h2 : 1 < (T i₀).card := hi₀_gt
          obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp h2
          let T₁ : ι → Finset E := fun i => if i = i₀ then (T i₀).erase e₁ else T i
          let T₂ : ι → Finset E := fun i => if i = i₀ then (T i₀).erase e₂ else T i
          have hchoice : (∀ J ⊆ I, J.card ≤ M.rank (J.biUnion T₁)) ∨
              (∀ J ⊆ I, J.card ≤ M.rank (J.biUnion T₂)) := by
            by_contra hboth
            push Not at hboth
            rcases hboth with ⟨⟨J₁, hJ₁I, hJ₁_lt⟩, ⟨J₂, hJ₂I, hJ₂_lt⟩⟩
            have hi₀1 : i₀ ∈ J₁ := by
              by_contra hnot
              have heq : J₁.biUnion T₁ = J₁.biUnion T := Finset.biUnion_congr rfl fun i hi => by
                dsimp only [T₁]; rw [if_neg (fun h => by subst h; exact hnot hi)]
              rw [heq] at hJ₁_lt; exact absurd (hT J₁ hJ₁I) (not_le_of_gt hJ₁_lt)
            have hi₀2 : i₀ ∈ J₂ := by
              by_contra hnot
              have heq : J₂.biUnion T₂ = J₂.biUnion T := Finset.biUnion_congr rfl fun i hi => by
                dsimp only [T₂]; rw [if_neg (fun h => by subst h; exact hnot hi)]
              rw [heq] at hJ₂_lt; exact absurd (hT J₂ hJ₂I) (not_le_of_gt hJ₂_lt)
            let A₁ := J₁.biUnion T₁
            let A₂ := J₂.biUnion T₂
            have hun : A₁ ∪ A₂ = (J₁ ∪ J₂).biUnion T := by
              ext x
              simp only [A₁, A₂, Finset.mem_union, Finset.mem_biUnion]
              constructor
              · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
                · refine ⟨i, Or.inl hi, ?_⟩
                  by_cases hieq : i = i₀
                  · subst hieq; dsimp only [T₁] at hx; rw [if_pos rfl] at hx; exact Finset.erase_subset _ _ hx
                  · dsimp only [T₁] at hx; rw [if_neg hieq] at hx; exact hx
                · refine ⟨i, Or.inr hi, ?_⟩
                  by_cases hieq : i = i₀
                  · subst hieq; dsimp only [T₂] at hx; rw [if_pos rfl] at hx; exact Finset.erase_subset _ _ hx
                  · dsimp only [T₂] at hx; rw [if_neg hieq] at hx; exact hx
              · rintro ⟨i, hi1 | hi2, hx⟩
                · by_cases hieq : i = i₀
                  · subst hieq
                    by_cases hxe1 : x = e₁
                    · subst hxe1
                      exact Or.inr ⟨i, hi₀2, by dsimp only [T₂]; rw [if_pos rfl]; exact Finset.mem_erase.mpr ⟨hne, hx⟩⟩
                    · exact Or.inl ⟨i, hi1, by dsimp only [T₁]; rw [if_pos rfl]; exact Finset.mem_erase.mpr ⟨hxe1, hx⟩⟩
                  · exact Or.inl ⟨i, hi1, by dsimp only [T₁]; rw [if_neg hieq]; exact hx⟩
                · by_cases hieq : i = i₀
                  · subst hieq
                    by_cases hxe2 : x = e₂
                    · subst hxe2
                      exact Or.inl ⟨i, hi₀1, by dsimp only [T₁]; rw [if_pos rfl]; exact Finset.mem_erase.mpr ⟨hne.symm, hx⟩⟩
                    · exact Or.inr ⟨i, hi2, by dsimp only [T₂]; rw [if_pos rfl]; exact Finset.mem_erase.mpr ⟨hxe2, hx⟩⟩
                  · exact Or.inr ⟨i, hi2, by dsimp only [T₂]; rw [if_neg hieq]; exact hx⟩
            have hin : ((J₁ ∩ J₂).erase i₀).biUnion T ⊆ A₁ ∩ A₂ := fun x hx => by
              rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxT⟩
              rcases Finset.mem_erase.mp hi with ⟨hine, hi12⟩
              rcases Finset.mem_inter.mp hi12 with ⟨hi1, hi2⟩
              exact Finset.mem_inter.mpr
                ⟨Finset.mem_biUnion.mpr ⟨i, hi1, by dsimp only [T₁]; rw [if_neg hine]; exact hxT⟩,
                 Finset.mem_biUnion.mpr ⟨i, hi2, by dsimp only [T₂]; rw [if_neg hine]; exact hxT⟩⟩
            have hsubmod := M.rank_submodular A₁ A₂
            have h_un_ge : (J₁ ∪ J₂).card ≤ M.rank (A₁ ∪ A₂) := by
              rw [hun]; exact hT _ (Finset.union_subset hJ₁I hJ₂I)
            have h_in_ge : ((J₁ ∩ J₂).erase i₀).card ≤ M.rank (A₁ ∩ A₂) :=
              le_trans (hT _ ((Finset.erase_subset _ _).trans (Finset.inter_subset_left.trans hJ₁I)))
                (M.rank_mono hin)
            have h_in_er : ((J₁ ∩ J₂).erase i₀).card = (J₁ ∩ J₂).card - 1 :=
              Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hi₀1, hi₀2⟩)
            have h1lt : M.rank A₁ < J₁.card := hJ₁_lt
            have h2lt : M.rank A₂ < J₂.card := hJ₂_lt
            have h_add := Finset.card_union_add_card_inter J₁ J₂
            have h1pos : 1 ≤ J₁.card := Finset.one_le_card.mpr ⟨i₀, hi₀1⟩
            have h2pos : 1 ≤ J₂.card := Finset.one_le_card.mpr ⟨i₀, hi₀2⟩
            omega
          rcases hchoice with h1 | h2
          · have hsum1 : ∑ i ∈ I, (T₁ i).card ≤ m := by
              have hlt_sum : ∑ i ∈ I, (T₁ i).card < ∑ i ∈ I, (T i).card := by
                refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, hi₀I, ?_⟩
                · by_cases hieq : i = i₀
                  · subst hieq; dsimp only [T₁]; rw [if_pos rfl]; exact Finset.card_le_card (Finset.erase_subset _ _)
                  · dsimp only [T₁]; rw [if_neg hieq]
                · dsimp only [T₁]; rw [if_pos rfl]; exact Finset.card_erase_lt_of_mem he₁
              omega
            obtain ⟨T', hT'1, hT'card, hT'rado⟩ := ihm T₁ hsum1 h1
            refine ⟨T', fun i hi => (hT'1 i hi).trans ?_, hT'card, hT'rado⟩
            by_cases hieq : i = i₀
            · subst hieq; dsimp only [T₁]; rw [if_pos rfl]; exact Finset.erase_subset _ _
            · dsimp only [T₁]; rw [if_neg hieq]; try exact Finset.Subset.rfl
          · have hsum2 : ∑ i ∈ I, (T₂ i).card ≤ m := by
              have hlt_sum : ∑ i ∈ I, (T₂ i).card < ∑ i ∈ I, (T i).card := by
                refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, hi₀I, ?_⟩
                · by_cases hieq : i = i₀
                  · subst hieq; dsimp only [T₂]; rw [if_pos rfl]; exact Finset.card_le_card (Finset.erase_subset _ _)
                  · dsimp only [T₂]; rw [if_neg hieq]
                · dsimp only [T₂]; rw [if_pos rfl]; exact Finset.card_erase_lt_of_mem he₂
              omega
            obtain ⟨T', hT'2, hT'card, hT'rado⟩ := ihm T₂ hsum2 h2
            refine ⟨T', fun i hi => (hT'2 i hi).trans ?_, hT'card, hT'rado⟩
            by_cases hieq : i = i₀
            · subst hieq; dsimp only [T₂]; rw [if_pos rfl]; exact Finset.erase_subset _ _
            · dsimp only [T₂]; rw [if_neg hieq]; try exact Finset.Subset.rfl
    obtain ⟨T', hT'sub, hT'card, hT'rado⟩ := hshrink (∑ i ∈ I, (S i).card) S le_rfl hRado
    have hex_f : ∀ i : I, ∃ e, T' i.1 = {e} := fun i => Finset.card_eq_one.mp (hT'card i.1 i.2)
    choose f hf using hex_f
    have hf_S : ∀ i : I, f i ∈ S i.1 := fun i =>
      hT'sub i.1 i.2 ((hf i) ▸ Finset.mem_singleton_self (f i))
    have hbi_eq : I.biUnion T' = Finset.univ.image f := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, he⟩
        rw [hf ⟨i, hi⟩, Finset.mem_singleton] at he
        exact ⟨⟨i, hi⟩, he.symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.1, i.2, (hf i) ▸ Finset.mem_singleton_self _⟩
    have hR := hT'rado I Finset.Subset.rfl
    rw [hbi_eq] at hR
    have hcard_eq : (Finset.univ.image f).card = (Finset.univ : Finset I).card := by
      refine le_antisymm Finset.card_image_le ?_
      rw [Finset.card_univ, Fintype.card_coe]
      exact le_trans hR (M.rank_le_card _)
    have h_inj : Function.Injective f := fun i₁ i₂ h =>
      (Finset.card_image_iff.mp hcard_eq) (Finset.mem_univ i₁) (Finset.mem_univ i₂) h
    have h_ind : M.Indep (Finset.univ.image f) := by
      rw [← M.rank_eq_card_iff_indep]
      refine le_antisymm (M.rank_le_card _) ?_
      rw [hcard_eq, Finset.card_univ, Fintype.card_coe]
      exact hR
    exact ⟨f, hf_S, h_inj, h_ind⟩

/-- Shortcut-free augmenting chain independence lemma for Edmonds' Matroid Intersection. -/
private lemma matroid_chain_aug {E : Type*} [DecidableEq E]
    (M : FinMatroid E) (I : Finset E) (hI : M.Indep I)
    (k : ℕ) (X : Fin (k + 1) → E) (Y : Fin k → E)
    (hX_not : ∀ i, X i ∉ I) (hX_inj : Function.Injective X)
    (hY_mem : ∀ i, Y i ∈ I) (hY_inj : Function.Injective Y)
    (hX0 : M.Indep (insert (X 0) I))
    (hX_dep : ∀ i : Fin k, ¬ M.Indep (insert (X i.succ) I))
    (h_arc : ∀ i : Fin k, M.Indep (insert (X i.succ) (I.erase (Y i))))
    (h_no_short : ∀ i j : Fin k, i.1 < j.1 → ¬ M.Indep (insert (X j.succ) (I.erase (Y i)))) :
    M.Indep ((I \ Finset.univ.image Y) ∪ Finset.univ.image X) := by
  classical
  let Yset : Finset E := Finset.univ.image Y
  let Xm : ℕ → Finset E := fun m =>
    (Finset.univ.filter (fun j : Fin k => k - m ≤ j.1)).image (fun j => X j.succ)
  let Ym : ℕ → Finset E := fun m =>
    (Finset.univ.filter (fun i : Fin k => k - m ≤ i.1)).image Y
  let Am : ℕ → Finset E := fun m => (I \ Yset) ∪ Xm m
  let Bm : ℕ → Finset E := fun m => (I \ Yset) ∪ Ym m
  have hBm_sub_I : ∀ m, Bm m ⊆ I := fun m e he => by
    rcases Finset.mem_union.mp he with he1 | he2
    · exact (Finset.mem_sdiff.mp he1).1
    · rcases Finset.mem_image.mp he2 with ⟨i, _, rfl⟩; exact hY_mem i
  have hinv : ∀ m ≤ k,
      M.Indep (Am m) ∧ (Am m).card = (Bm m).card ∧
        (∀ a ∈ Am m, M.rank (insert a (Bm m)) = M.rank (Bm m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      have hX0_em : Xm 0 = ∅ := by
        ext e; simp only [Xm, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Nat.sub_zero, Finset.notMem_empty, iff_false, not_exists, not_and]
        intro j hle; omega
      have hY0_em : Ym 0 = ∅ := by
        ext e; simp only [Ym, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Nat.sub_zero, Finset.notMem_empty, iff_false, not_exists, not_and]
        intro i hle; omega
      have hA0 : Am 0 = I \ Yset := by simp [Am, hX0_em]
      have hB0 : Bm 0 = I \ Yset := by simp [Bm, hY0_em]
      rw [hA0, hB0]
      refine ⟨M.indep_subset hI Finset.sdiff_subset, rfl, fun a ha => ?_⟩
      rw [Finset.insert_eq_of_mem ha]
    | @succ m ih =>
      intro hm
      obtain ⟨hAm_ind, hAm_card, hAm_cl⟩ := ih (Nat.le_of_succ_le hm)
      let idx : Fin k := ⟨k - 1 - m, by omega⟩
      have hXm_succ : Xm (m + 1) = insert (X idx.succ) (Xm m) := by
        ext e
        simp only [Xm, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, hj, rfl⟩
          by_cases hjeq : j = idx
          · left; rw [hjeq]
          · right; exact ⟨j, by
              have hval : j.1 ≠ k - 1 - m := fun h => hjeq (Fin.ext h)
              omega, rfl⟩
        · rintro (rfl | ⟨j, hj, rfl⟩)
          · exact ⟨idx, by dsimp [idx]; omega, rfl⟩
          · exact ⟨j, by omega, rfl⟩
      have hYm_succ : Ym (m + 1) = insert (Y idx) (Ym m) := by
        ext e
        simp only [Ym, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hi, rfl⟩
          by_cases hieq : i = idx
          · left; rw [hieq]
          · right; exact ⟨i, by
              have hval : i.1 ≠ k - 1 - m := fun h => hieq (Fin.ext h)
              omega, rfl⟩
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨idx, by dsimp [idx]; omega, rfl⟩
          · exact ⟨i, by omega, rfl⟩
      have hAm_succ : Am (m + 1) = insert (X idx.succ) (Am m) := by
        simp only [Am, hXm_succ, Finset.union_insert]
      have hBm_succ : Bm (m + 1) = insert (Y idx) (Bm m) := by
        simp only [Bm, hYm_succ, Finset.union_insert]
      have hX_not_Am : X idx.succ ∉ Am m := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h1 | h2
        · exact hX_not idx.succ (Finset.mem_sdiff.mp h1).1
        · rcases Finset.mem_image.mp h2 with ⟨j, hj, heq⟩
          have hj_gt : k - m ≤ j.1 := (Finset.mem_filter.mp hj).2
          have hj_eq : j.succ = idx.succ := hX_inj heq
          have hj_eq' : j = idx := Fin.ext (by have := congrArg Fin.val hj_eq; simp at this; exact this)
          rw [hj_eq'] at hj_gt
          dsimp [idx] at hj_gt; omega
      have hY_not_Bm : Y idx ∉ Bm m := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h1 | h2
        · exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_image_of_mem Y (Finset.mem_univ idx))
        · rcases Finset.mem_image.mp h2 with ⟨i, hi, heq⟩
          have hi_gt : k - m ≤ i.1 := (Finset.mem_filter.mp hi).2
          have hi_eq : i = idx := hY_inj heq
          rw [hi_eq] at hi_gt
          dsimp [idx] at hi_gt; omega
      have hBm_ind : M.Indep (Bm m) := M.indep_subset hI (hBm_sub_I m)
      have hBm_er : Bm m ⊆ I.erase (Y idx) := fun e he =>
        Finset.mem_erase.mpr ⟨fun h => by subst h; exact hY_not_Bm he, hBm_sub_I m he⟩
      have hXBm_ind : M.Indep (insert (X idx.succ) (Bm m)) :=
        M.indep_subset (h_arc idx) (Finset.insert_subset_insert _ hBm_er)
      have hX_not_Bm : X idx.succ ∉ Bm m := fun h => hX_not idx.succ (hBm_sub_I m h)
      have hrank_eq := M.rank_union_eq_of_subset_cl hAm_ind hBm_ind hAm_card
        (fun a ha => hAm_cl a ha) {X idx.succ}
      have hAm_ins_eq : Am m ∪ {X idx.succ} = insert (X idx.succ) (Am m) := by
        ext e; simp [Finset.mem_insert]
      have hBm_ins_eq : Bm m ∪ {X idx.succ} = insert (X idx.succ) (Bm m) := by
        ext e; simp [Finset.mem_insert]
      rw [hAm_ins_eq, hBm_ins_eq] at hrank_eq
      have hXAm_rank : M.rank (insert (X idx.succ) (Am m)) = (insert (X idx.succ) (Am m)).card := by
        rw [hrank_eq, (M.rank_eq_card_iff_indep _).mpr hXBm_ind,
          Finset.card_insert_of_notMem hX_not_Bm, Finset.card_insert_of_notMem hX_not_Am, hAm_card]
      have hAm1_ind : M.Indep (Am (m + 1)) :=
        hAm_succ ▸ (M.rank_eq_card_iff_indep _).mp hXAm_rank
      have hAm1_card : (Am (m + 1)).card = (Bm (m + 1)).card := by
        rw [hAm_succ, hBm_succ, Finset.card_insert_of_notMem hX_not_Am,
          Finset.card_insert_of_notMem hY_not_Bm, hAm_card]
      refine ⟨hAm1_ind, hAm1_card, fun a ha => ?_⟩
      rw [hAm_succ] at ha
      rcases Finset.mem_insert.mp ha with rfl | haAm
      · obtain ⟨C, ⟨hCsub, hC⟩, hCuniq⟩ := M.circuit_unique_in_insert hI (hX_dep idx)
        have hC_sub_Bm1 : C ⊆ insert (X idx.succ) (Bm (m + 1)) := by
          intro e heC
          rcases Finset.mem_insert.mp (hCsub heC) with rfl | heI
          · exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            by_cases heY : e ∈ Yset
            · rcases Finset.mem_image.mp heY with ⟨i, _, rfl⟩
              apply Finset.mem_union_right
              refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
              by_contra hlt
              have hi_lt : i.1 < idx.1 := by dsimp [idx]; omega
              obtain ⟨C', hC'sub, hC'⟩ := M.exists_circuit_of_dep (h_no_short i idx hi_lt)
              have heqCC' : C' = C :=
                hCuniq C' ⟨hC'sub.trans (Finset.insert_subset_insert _ (Finset.erase_subset _ _)), hC'⟩
              rw [heqCC'] at hC'sub
              rcases Finset.mem_insert.mp (hC'sub heC) with heq | her
              · exact hX_not idx.succ (heq ▸ heI)
              · exact (Finset.mem_erase.mp her).1 rfl
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨heI, heY⟩)
        have hX_mem_C : X idx.succ ∈ C := by
          by_contra hnot
          exact hC.1 (M.indep_subset hI (fun e he => by
            rcases Finset.mem_insert.mp (hCsub he) with rfl | heI
            · exact absurd he hnot
            · exact heI))
        exact M.rank_insert_eq_of_circuit hC hX_mem_C (fun e he => by
          rcases Finset.mem_erase.mp he with ⟨hne, heC⟩
          exact (Finset.mem_insert.mp (hC_sub_Bm1 heC)).resolve_left hne)
      · have hsubmod := M.rank_submodular (insert a (Bm m)) (Bm (m + 1))
        have h1 : insert a (Bm m) ∪ Bm (m + 1) = insert a (Bm (m + 1)) := by
          rw [hBm_succ]; ext z; simp only [Finset.mem_union, Finset.mem_insert]; tauto
        have h2 : Bm m ⊆ insert a (Bm m) ∩ Bm (m + 1) := fun z hz =>
          Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hz, hBm_succ ▸ Finset.mem_insert_of_mem hz⟩
        have h2_le := M.rank_mono h2
        have hcl_a := hAm_cl a haAm
        rw [h1, hcl_a] at hsubmod
        have hge : M.rank (Bm (m + 1)) ≤ M.rank (insert a (Bm (m + 1))) :=
          M.rank_mono (Finset.subset_insert _ _)
        omega
  obtain ⟨hAk_ind, hAk_card, hAk_cl⟩ := hinv k le_rfl
  have hBk_eq : Bm k = I := by
    ext e
    simp only [Bm, Ym, Yset]
    constructor
    · intro he; exact hBm_sub_I k he
    · intro heI
      by_cases heY : e ∈ Finset.univ.image Y
      · rcases Finset.mem_image.mp heY with ⟨i, _, rfl⟩
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨heI, heY⟩)
  rw [hBk_eq] at hAk_card hAk_cl
  have hrank_eq := M.rank_union_eq_of_subset_cl hAk_ind hI hAk_card hAk_cl {X 0}
  have hA_ins : Am k ∪ {X 0} = insert (X 0) (Am k) := by ext e; simp
  have hI_ins : I ∪ {X 0} = insert (X 0) I := by ext e; simp
  rw [hA_ins, hI_ins] at hrank_eq
  have hX0_not_Ak : X 0 ∉ Am k := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h1 | h2
    · exact hX_not 0 (Finset.mem_sdiff.mp h1).1
    · rcases Finset.mem_image.mp h2 with ⟨j, _, heq⟩
      have h0 : j.succ = 0 := hX_inj heq
      exact Fin.succ_ne_zero j h0
  have hfinal_rank : M.rank (insert (X 0) (Am k)) = (insert (X 0) (Am k)).card := by
    rw [hrank_eq, (M.rank_eq_card_iff_indep _).mpr hX0,
      Finset.card_insert_of_notMem (hX_not 0), Finset.card_insert_of_notMem hX0_not_Ak, hAk_card]
  have hfinal_ind : M.Indep (insert (X 0) (Am k)) :=
    (M.rank_eq_card_iff_indep _).mp hfinal_rank
  have hset_eq : insert (X 0) (Am k) = (I \ Yset) ∪ Finset.univ.image X := by
    ext e
    simp only [Am, Xm, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Nat.sub_self, Nat.zero_le]
    constructor
    · rintro (rfl | (h1 | ⟨j, _, rfl⟩))
      · exact Or.inr ⟨0, rfl⟩
      · exact Or.inl h1
      · exact Or.inr ⟨j.succ, rfl⟩
    · rintro (h1 | ⟨i, rfl⟩)
      · exact Or.inr (Or.inl h1)
      · refine Fin.cases (Or.inl rfl) (fun j => Or.inr (Or.inr ⟨j, rfl⟩)) i
  exact hset_eq ▸ hfinal_ind

private lemma reflTransGen_to_finPath {E : Type*} (step : E → E → Prop) {a b : E}
    (h : Relation.ReflTransGen step a b) :
    ∃ (m : ℕ) (p : Fin (m + 1) → E), p 0 = a ∧ p (Fin.last m) = b ∧
      ∀ i : Fin m, step (p i.castSucc) (p i.succ) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i => Fin.elim0 i⟩
  | @tail b c _ hbc ih =>
    obtain ⟨m, p, hp0, hplast, hpstep⟩ := ih
    refine ⟨m + 1, fun r => if hr : r.1 ≤ m then p ⟨r.1, Nat.lt_succ_of_le hr⟩ else c, ?_, ?_, ?_⟩
    · simp [hp0]
    · simp [Fin.last]
    · intro i
      by_cases hi : i.1 + 1 ≤ m
      · have hi0 : i.1 ≤ m := by omega
        simp only [Fin.val_castSucc, Fin.val_succ, dif_pos hi0, dif_pos hi]
        exact hpstep ⟨i.1, by omega⟩
      · have hi_eq : i.1 = m := by omega
        have hi0 : i.1 ≤ m := by omega
        have hnot : ¬ (i.1 + 1 ≤ m) := hi
        simp only [Fin.val_castSucc, Fin.val_succ, dif_pos hi0, dif_neg hnot]
        convert hbc using 1
        rw [← hplast]
        congr 1
        exact Fin.ext hi_eq

/-- **Edmonds' Matroid Intersection Minimax Theorem (1970)**: for any two finite matroids `M₁, M₂`
on `E`, the maximum size of a common independent set equals `min_{A ⊆ E} (M₁.rank A + M₂.rank (univ \ A))`. -/
theorem edmonds_matroid_intersection {E : Type*} [Fintype E] [DecidableEq E]
    (M₁ M₂ : FinMatroid E) :
    ∃ (I A : Finset E), M₁.Indep I ∧ M₂.Indep I ∧
      I.card = M₁.rank A + M₂.rank (Finset.univ \ A) ∧
      (∀ J : Finset E, M₁.Indep J → M₂.Indep J → J.card ≤ I.card) ∧
      (∀ B : Finset E, I.card ≤ M₁.rank B + M₂.rank (Finset.univ \ B)) := by
  classical
  have hweak : ∀ (J B : Finset E), M₁.Indep J → M₂.Indep J →
      J.card ≤ M₁.rank B + M₂.rank (Finset.univ \ B) := by
    intro J B hJ1 hJ2
    have hcard : J.card = (J ∩ B).card + (J \ B).card := by
      rw [← Finset.card_sdiff_add_card_inter J B, add_comm]
    have h1 : (J ∩ B).card ≤ M₁.rank B :=
      M₁.le_rank Finset.inter_subset_right (M₁.indep_subset hJ1 Finset.inter_subset_left)
    have h2 : (J \ B).card ≤ M₂.rank (Finset.univ \ B) :=
      M₂.le_rank (Finset.sdiff_subset_sdiff (Finset.subset_univ J) Finset.Subset.rfl)
        (M₂.indep_subset hJ2 Finset.sdiff_subset)
    omega
  have hgap : ∀ d : ℕ, ∀ I : Finset E, Fintype.card E - I.card ≤ d →
      M₁.Indep I → M₂.Indep I →
      ∃ (I' A : Finset E), M₁.Indep I' ∧ M₂.Indep I' ∧
        I'.card = M₁.rank A + M₂.rank (Finset.univ \ A) := by
    intro d
    induction d with
    | zero =>
      intro I hd hI1 hI2
      have hfull : I.card = Fintype.card E :=
        le_antisymm (Finset.card_le_univ I) (by omega)
      have hI_univ : I = Finset.univ := Finset.eq_univ_of_card I hfull
      refine ⟨I, Finset.univ, hI1, hI2, ?_⟩
      rw [Finset.sdiff_self, M₂.rank_empty, add_zero, hI_univ,
        (M₁.rank_eq_card_iff_indep _).mpr (hI_univ ▸ hI1)]
    | succ d ih =>
      intro I hd hI1 hI2
      let S₁ : Finset E := Finset.univ.filter (fun e => e ∉ I ∧ M₁.Indep (insert e I))
      let S₂ : Finset E := Finset.univ.filter (fun e => e ∉ I ∧ M₂.Indep (insert e I))
      let step : E → E → Prop := fun u v =>
        (u ∈ I ∧ v ∉ I ∧ M₁.Indep (insert v (I.erase u))) ∨
        (u ∉ I ∧ v ∈ I ∧ M₂.Indep (insert u (I.erase v)))
      by_cases hpath : ∃ m : ℕ, ∃ p : Fin (m + 1) → E,
          p 0 ∈ S₁ ∧ p (Fin.last m) ∈ S₂ ∧ ∀ i : Fin m, step (p i.castSucc) (p i.succ)
      · let m := Nat.find hpath
        obtain ⟨p, hp0, hplast, hpstep⟩ := Nat.find_spec hpath
        have hm_min : ∀ m' : ℕ, ∀ p' : Fin (m' + 1) → E,
            p' 0 ∈ S₁ → p' (Fin.last m') ∈ S₂ →
            (∀ i : Fin m', step (p' i.castSucc) (p' i.succ)) → m ≤ m' :=
          fun m' p' h0 hl hs => Nat.find_min' hpath ⟨p', h0, hl, hs⟩
        have h_no_shortcut : ∀ i j : Fin (m + 1), i.1 + 1 < j.1 → ¬ step (p i) (p j) := by
          intro i j hij hst
          let m' := m - (j.1 - i.1 - 1)
          have hm'_lt : m' < m := by omega
          let p' : Fin (m' + 1) → E := fun r =>
            if hr : r.1 ≤ i.1 then p ⟨r.1, by omega⟩
            else p ⟨r.1 + (j.1 - i.1 - 1), by omega⟩
          have hp'0 : p' 0 ∈ S₁ := by
            simp only [p', Fin.val_zero, Nat.zero_le, ↓reduceDIte]; exact hp0
          have hp'last : p' (Fin.last m') ∈ S₂ := by
            dsimp only [p']
            have hnot : ¬ ((Fin.last m').1 ≤ i.1) := by simp [Fin.val_last]; omega
            rw [dif_neg hnot]
            convert hplast using 2
            exact Fin.ext (by simp [m', Fin.val_last]; omega)
          have hp'step : ∀ r : Fin m', step (p' r.castSucc) (p' r.succ) := by
            intro r
            have hr_lt := r.isLt
            dsimp only [p']
            by_cases hr1 : r.1 + 1 ≤ i.1
            · have hr0 : r.1 ≤ i.1 := by omega
              simp only [Fin.val_castSucc, Fin.val_succ, dif_pos hr0, dif_pos hr1]
              exact hpstep ⟨r.1, by omega⟩
            · by_cases hr0 : r.1 ≤ i.1
              · have hri : r.1 = i.1 := by omega
                have hj_lt := j.isLt
                simp only [Fin.val_castSucc, Fin.val_succ, dif_pos hr0, dif_neg hr1]
                have h1 : (⟨r.1, by omega⟩ : Fin (m + 1)) = i := Fin.ext hri
                have h2 : (⟨r.1 + 1 + (j.1 - i.1 - 1), by omega⟩ : Fin (m + 1)) = j :=
                  Fin.ext (by dsimp; omega)
                rw [h1, h2]; exact hst
              · simp only [Fin.val_castSucc, Fin.val_succ, dif_neg hr0, dif_neg hr1]
                have h_sub : r.1 + (j.1 - i.1 - 1) < m := by dsimp [m'] at hr_lt; omega
                have h1 : (⟨r.1 + (j.1 - i.1 - 1), by dsimp [m'] at hr_lt; omega⟩ : Fin (m + 1)) =
                    (⟨r.1 + (j.1 - i.1 - 1), h_sub⟩ : Fin m).castSucc := Fin.ext rfl
                have h2 : (⟨r.1 + 1 + (j.1 - i.1 - 1), by dsimp [m'] at hr_lt; omega⟩ : Fin (m + 1)) =
                    (⟨r.1 + (j.1 - i.1 - 1), h_sub⟩ : Fin m).succ := Fin.ext (by simp; omega)
                rw [h1, h2]
                exact hpstep ⟨r.1 + (j.1 - i.1 - 1), h_sub⟩
          exact Nat.not_le_of_gt hm'_lt (hm_min m' p' hp'0 hp'last hp'step)
        have h_not_S₁ : ∀ i : Fin (m + 1), 0 < i.1 → p i ∉ S₁ := by
          intro i hi hS₁
          let m' := m - i.1
          have hm'_lt : m' < m := by omega
          let p' : Fin (m' + 1) → E := fun r => p ⟨r.1 + i.1, by omega⟩
          have hp'0 : p' 0 ∈ S₁ := by simpa [p'] using hS₁
          have hp'last : p' (Fin.last m') ∈ S₂ := by
            convert hplast using 2; exact Fin.ext (by simp [m']; omega)
          have hp'step : ∀ r : Fin m', step (p' r.castSucc) (p' r.succ) := fun r => by
            have hr_lt := r.isLt
            have h_sub : r.1 + i.1 < m := by dsimp [m'] at hr_lt; omega
            have h1 : (⟨r.castSucc.1 + i.1, by dsimp [m'] at hr_lt; omega⟩ : Fin (m + 1)) =
                (⟨r.1 + i.1, h_sub⟩ : Fin m).castSucc := Fin.ext (by simp)
            have h2 : (⟨r.succ.1 + i.1, by dsimp [m'] at hr_lt; omega⟩ : Fin (m + 1)) =
                (⟨r.1 + i.1, h_sub⟩ : Fin m).succ := Fin.ext (by simp; omega)
            dsimp only [p']; rw [h1, h2]
            exact hpstep ⟨r.1 + i.1, h_sub⟩
          exact Nat.not_le_of_gt hm'_lt (hm_min m' p' hp'0 hp'last hp'step)
        have h_not_S₂ : ∀ i : Fin (m + 1), i.1 < m → p i ∉ S₂ := by
          intro i hi hS₂
          let p' : Fin (i.1 + 1) → E := fun r => p ⟨r.1, by omega⟩
          have hp'0 : p' 0 ∈ S₁ := by simpa [p'] using hp0
          have hp'last : p' (Fin.last i.1) ∈ S₂ := by
            convert hS₂ using 2; exact Fin.ext (by simp)
          have hp'step : ∀ r : Fin i.1, step (p' r.castSucc) (p' r.succ) := fun r => by
            have hr_lt := r.isLt
            have h_sub : r.1 < m := by omega
            have h1 : (⟨r.castSucc.1, by omega⟩ : Fin (m + 1)) = (⟨r.1, h_sub⟩ : Fin m).castSucc :=
              Fin.ext (by simp)
            have h2 : (⟨r.succ.1, by omega⟩ : Fin (m + 1)) = (⟨r.1, h_sub⟩ : Fin m).succ :=
              Fin.ext (by simp)
            dsimp only [p']; rw [h1, h2]
            exact hpstep ⟨r.1, h_sub⟩
          exact Nat.not_le_of_gt hi (hm_min i.1 p' hp'0 hp'last hp'step)
        have hp_inj : Function.Injective p := by
          intro i j hij
          by_contra hne
          have hi_lt := i.isLt
          have hj_lt := j.isLt
          rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
          · by_cases hjm : j.1 < m
            · have hst : step (p i) (p ⟨j.1 + 1, by omega⟩) := by
                rw [hij]; exact hpstep ⟨j.1, hjm⟩
              exact h_no_shortcut i ⟨j.1 + 1, by omega⟩ (by simp; omega) hst
            · have hjm' : j.1 = m := by omega
              have hjeq : j = Fin.last m := Fin.ext (by simpa [Fin.val_last] using hjm')
              rw [hjeq] at hij
              exact h_not_S₂ i (by omega) (hij ▸ hplast)
          · by_cases him : i.1 < m
            · have hst : step (p j) (p ⟨i.1 + 1, by omega⟩) := by
                rw [← hij]; exact hpstep ⟨i.1, him⟩
              exact h_no_shortcut j ⟨i.1 + 1, by omega⟩ (by simp; omega) hst
            · have him' : i.1 = m := by omega
              have hieq : i = Fin.last m := Fin.ext (by simpa [Fin.val_last] using him')
              rw [hieq] at hij
              exact h_not_S₂ j (by omega) (hij.symm ▸ hplast)
        have h_parity : ∀ i : Fin (m + 1), p i ∈ I ↔ i.1 % 2 = 1 := by
          intro i
          induction i using Fin.inductionOn with
          | zero =>
            simp [(Finset.mem_filter.mp hp0).2.1]
          | succ i ih =>
            have hst := hpstep i
            simp only [Fin.val_succ]
            rcases hst with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
            · simp only [Fin.val_castSucc] at ih h1
              have hodd : i.1 % 2 = 1 := ih.mp h1
              have heven : (i.1 + 1) % 2 ≠ 1 := by omega
              simp [h2, heven]
            · simp only [Fin.val_castSucc] at ih h1
              have heven : ¬ (i.1 % 2 = 1) := fun h => h1 (ih.mpr h)
              have hodd : (i.1 + 1) % 2 = 1 := by omega
              simp [h2, hodd]
        have hm_even : m % 2 = 0 := by
          have hnot : p (Fin.last m) ∉ I := (Finset.mem_filter.mp hplast).2.1
          have hmod := (h_parity (Fin.last m)).not.mp hnot
          simp [Fin.last] at hmod; omega
        let k := m / 2
        have hmk : m = 2 * k := by omega
        let X : Fin (k + 1) → E := fun i => p ⟨2 * i.1, by omega⟩
        let Y : Fin k → E := fun i => p ⟨2 * i.1 + 1, by omega⟩
        have hX_not : ∀ i, X i ∉ I := fun i => by
          rw [h_parity]; simp
        have hY_mem : ∀ i, Y i ∈ I := fun i => by
          rw [h_parity]; simp
        have hX_inj : Function.Injective X := fun i₁ i₂ h => by
          have := hp_inj h; exact Fin.ext (by have hv := congrArg Fin.val this; simp at hv; omega)
        have hY_inj : Function.Injective Y := fun i₁ i₂ h => by
          have := hp_inj h; exact Fin.ext (by have hv := congrArg Fin.val this; simp at hv; omega)
        have hX0_ind : M₁.Indep (insert (X 0) I) := by
          have heq : X 0 = p 0 := rfl
          rw [heq]; exact (Finset.mem_filter.mp hp0).2.2
        have hX_dep1 : ∀ i : Fin k, ¬ M₁.Indep (insert (X i.succ) I) := fun i h =>
          h_not_S₁ ⟨2 * i.succ.1, by omega⟩ (by simp)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX_not i.succ, h⟩)
        have h_arc1 : ∀ i : Fin k, M₁.Indep (insert (X i.succ) (I.erase (Y i))) := fun i => by
          have hst := hpstep ⟨2 * i.1 + 1, by omega⟩
          have h1 : p ⟨2 * i.1 + 1, by omega⟩ = Y i := rfl
          have h2 : p ⟨2 * i.1 + 1 + 1, by omega⟩ = X i.succ := rfl
          rcases hst with ⟨_, _, hind⟩ | ⟨hnot, _, _⟩
          · simpa [Fin.val_castSucc, Fin.val_succ, h1, h2] using hind
          · exact absurd (hY_mem i) hnot
        have h_noshort1 : ∀ i j : Fin k, i.1 < j.1 →
            ¬ M₁.Indep (insert (X j.succ) (I.erase (Y i))) := fun i j hij hind =>
          h_no_shortcut ⟨2 * i.1 + 1, by omega⟩ ⟨2 * j.succ.1, by omega⟩ (by simp; omega)
            (Or.inl ⟨hY_mem i, hX_not j.succ, hind⟩)
        have hI'_1 : M₁.Indep ((I \ Finset.univ.image Y) ∪ Finset.univ.image X) :=
          matroid_chain_aug M₁ I hI1 k X Y hX_not hX_inj hY_mem hY_inj
            hX0_ind hX_dep1 h_arc1 h_noshort1
        let X' : Fin (k + 1) → E := fun i => X (Fin.rev i)
        let Y' : Fin k → E := fun i => Y (Fin.rev i)
        have hX'_not : ∀ i, X' i ∉ I := fun i => hX_not _
        have hY'_mem : ∀ i, Y' i ∈ I := fun i => hY_mem _
        have hX'_inj : Function.Injective X' := fun i₁ i₂ h => Fin.rev_injective (hX_inj h)
        have hY'_inj : Function.Injective Y' := fun i₁ i₂ h => Fin.rev_injective (hY_inj h)
        have hX'0_ind : M₂.Indep (insert (X' 0) I) := by
          have heq : X' 0 = p (Fin.last m) := by
            dsimp [X', X]; congr 1; exact Fin.ext (by simp [Fin.last]; omega)
          rw [heq]; exact (Finset.mem_filter.mp hplast).2.2
        have hX'_dep2 : ∀ i : Fin k, ¬ M₂.Indep (insert (X' i.succ) I) := fun i h => by
          exact h_not_S₂ ⟨2 * (Fin.rev i.succ).1, by omega⟩ (by simp; omega)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX'_not i.succ, h⟩)
        have h_arc2 : ∀ i : Fin k, M₂.Indep (insert (X' i.succ) (I.erase (Y' i))) := fun i => by
          have hidx : 2 * (k - 1 - i.1) < m := by omega
          have hst := hpstep ⟨2 * (k - 1 - i.1), hidx⟩
          have h1 : p (⟨2 * (k - 1 - i.1), hidx⟩ : Fin m).castSucc = X' i.succ := by
            dsimp [X', X]; congr 1; exact Fin.ext (by simp; omega)
          have h2 : p (⟨2 * (k - 1 - i.1), hidx⟩ : Fin m).succ = Y' i := by
            dsimp [Y', Y]; congr 1; exact Fin.ext (by simp; omega)
          rcases hst with ⟨hmem, _, _⟩ | ⟨_, _, hind⟩
          · exact absurd (hX'_not i.succ) (by rw [← h1]; exact fun h => h hmem)
          · rwa [h1, h2] at hind
        have h_noshort2 : ∀ i j : Fin k, i.1 < j.1 →
            ¬ M₂.Indep (insert (X' j.succ) (I.erase (Y' i))) := fun i j hij hind => by
          exact h_no_shortcut ⟨2 * (Fin.rev j.succ).1, by omega⟩
            ⟨2 * (Fin.rev i).1 + 1, by omega⟩ (by simp; omega)
            (Or.inr ⟨hX'_not j.succ, hY'_mem i, hind⟩)
        have hI'_2_rev : M₂.Indep ((I \ Finset.univ.image Y') ∪ Finset.univ.image X') :=
          matroid_chain_aug M₂ I hI2 k X' Y' hX'_not hX'_inj hY'_mem hY'_inj
            hX'0_ind hX'_dep2 h_arc2 h_noshort2
        have hY_img : Finset.univ.image Y' = Finset.univ.image Y := by
          ext e; simp only [Finset.mem_image, Finset.mem_univ, true_and, Y']
          exact ⟨fun ⟨i, hi⟩ => ⟨Fin.rev i, hi⟩, fun ⟨i, hi⟩ => ⟨Fin.rev i, by simp [hi]⟩⟩
        have hX_img : Finset.univ.image X' = Finset.univ.image X := by
          ext e; simp only [Finset.mem_image, Finset.mem_univ, true_and, X']
          exact ⟨fun ⟨i, hi⟩ => ⟨Fin.rev i, hi⟩, fun ⟨i, hi⟩ => ⟨Fin.rev i, by simp [hi]⟩⟩
        rw [hY_img, hX_img] at hI'_2_rev
        let I' := (I \ Finset.univ.image Y) ∪ Finset.univ.image X
        have hdisj : Disjoint (I \ Finset.univ.image Y) (Finset.univ.image X) := by
          rw [Finset.disjoint_left]
          intro e he1 he2
          rcases Finset.mem_image.mp he2 with ⟨i, _, rfl⟩
          exact hX_not i (Finset.mem_sdiff.mp he1).1
        have hY_sub : Finset.univ.image Y ⊆ I := fun e he => by
          rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩; exact hY_mem i
        have hI'_card : I'.card = I.card + 1 := by
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hY_sub,
            Finset.card_image_of_injective _ hY_inj, Finset.card_image_of_injective _ hX_inj,
            Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
          have hk_le : k ≤ I.card := by
            have := Finset.card_le_card hY_sub
            rw [Finset.card_image_of_injective _ hY_inj, Finset.card_univ, Fintype.card_fin] at this
            exact this
          omega
        exact ih I' (by omega) hI'_1 hI'_2_rev
      · let R : Finset E := Finset.univ.filter (fun v =>
          ∃ s₁ ∈ S₁, Relation.ReflTransGen step s₁ v)
        have hR_closed : ∀ u ∈ R, ∀ v, step u v → v ∈ R := by
          intro u hu v huv
          rcases Finset.mem_filter.mp hu with ⟨_, s₁, hs₁, hreach⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s₁, hs₁, hreach.tail huv⟩
        have hR_no_S₂ : ∀ v ∈ R, v ∉ S₂ := by
          intro v hv hvS₂
          rcases Finset.mem_filter.mp hv with ⟨_, s₁, hs₁, hreach⟩
          obtain ⟨m, p, hp0, hplast, hpstep⟩ := reflTransGen_to_finPath step hreach
          exact hpath ⟨m, p, hp0 ▸ hs₁, hplast ▸ hvS₂, hpstep⟩
        have hS₁_sub_R : S₁ ⊆ R := fun s₁ hs₁ =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, s₁, hs₁, Relation.ReflTransGen.refl⟩
        have hrank1 : M₁.rank (Finset.univ \ R) = (I \ R).card := by
          refine le_antisymm ?_ (M₁.le_rank (Finset.sdiff_subset_sdiff (Finset.subset_univ _) Finset.Subset.rfl)
            (M₁.indep_subset hI1 Finset.sdiff_subset))
          by_contra hlt
          have hlt' : (I \ R).card < M₁.rank (Finset.univ \ R) := Nat.lt_of_not_le hlt
          obtain ⟨J, hIJ, hJA, hJind, hJcard⟩ := M₁.exists_basis_extension
            (Finset.sdiff_subset_sdiff (Finset.subset_univ _) Finset.Subset.rfl)
            (M₁.indep_subset hI1 Finset.sdiff_subset)
          have hss : I \ R ⊂ J :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hIJ, fun h => by rw [h, hJcard] at hlt'; exact lt_irrefl _ hlt'⟩
          obtain ⟨x, hxJ, hxIR⟩ := (Finset.ssubset_iff_of_subset hIJ).mp hss
          have hxA := Finset.mem_sdiff.mp (hJA hxJ)
          have hxR : x ∉ R := hxA.2
          have hxI : x ∉ I := fun h => hxIR (Finset.mem_sdiff.mpr ⟨h, hxR⟩)
          have hx_not_S₁ : x ∉ S₁ := fun h => hxR (hS₁_sub_R h)
          have hdep : ¬ M₁.Indep (insert x I) := fun h =>
            hx_not_S₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxI, h⟩)
          obtain ⟨C, ⟨hCsub, hC⟩, hCuniq⟩ := M₁.circuit_unique_in_insert hI1 hdep
          have hC_sub_J : C ⊆ J := fun y hyC => by
            rcases Finset.mem_insert.mp (hCsub hyC) with rfl | hyI
            · exact hxJ
            · by_cases hyR : y ∈ R
              · exfalso
                have h_er_ind : M₁.Indep (insert x (I.erase y)) := by
                  by_contra hdep_er
                  obtain ⟨C', hC'sub, hC'⟩ := M₁.exists_circuit_of_dep hdep_er
                  have heq := hCuniq C' ⟨hC'sub.trans (Finset.insert_subset_insert _ (Finset.erase_subset _ _)), hC'⟩
                  rw [heq] at hC'sub
                  rcases Finset.mem_insert.mp (hC'sub hyC) with rfl | hy_er
                  · exact hxI hyI
                  · exact (Finset.mem_erase.mp hy_er).1 rfl
                exact hxR (hR_closed y hyR x (Or.inl ⟨hyI, hxI, h_er_ind⟩))
              · exact hIJ (Finset.mem_sdiff.mpr ⟨hyI, hyR⟩)
          exact hC.1 (M₁.indep_subset hJind hC_sub_J)
        have hrank2 : M₂.rank R = (I ∩ R).card := by
          refine le_antisymm ?_ (M₂.le_rank Finset.inter_subset_right
            (M₂.indep_subset hI2 Finset.inter_subset_left))
          by_contra hlt
          have hlt' : (I ∩ R).card < M₂.rank R := Nat.lt_of_not_le hlt
          obtain ⟨J, hIJ, hJR, hJind, hJcard⟩ := M₂.exists_basis_extension
            Finset.inter_subset_right (M₂.indep_subset hI2 Finset.inter_subset_left)
          have hss : I ∩ R ⊂ J :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hIJ, fun h => by rw [h, hJcard] at hlt'; exact lt_irrefl _ hlt'⟩
          obtain ⟨x, hxJ, hxIR⟩ := (Finset.ssubset_iff_of_subset hIJ).mp hss
          have hxR : x ∈ R := hJR hxJ
          have hxI : x ∉ I := fun h => hxIR (Finset.mem_inter.mpr ⟨h, hxR⟩)
          have hx_not_S₂ : x ∉ S₂ := hR_no_S₂ x hxR
          have hdep : ¬ M₂.Indep (insert x I) := fun h =>
            hx_not_S₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxI, h⟩)
          obtain ⟨C, ⟨hCsub, hC⟩, hCuniq⟩ := M₂.circuit_unique_in_insert hI2 hdep
          have hC_sub_J : C ⊆ J := fun y hyC => by
            rcases Finset.mem_insert.mp (hCsub hyC) with rfl | hyI
            · exact hxJ
            · by_cases hyR : y ∈ R
              · exact hIJ (Finset.mem_inter.mpr ⟨hyI, hyR⟩)
              · exfalso
                have h_er_ind : M₂.Indep (insert x (I.erase y)) := by
                  by_contra hdep_er
                  obtain ⟨C', hC'sub, hC'⟩ := M₂.exists_circuit_of_dep hdep_er
                  have heq := hCuniq C' ⟨hC'sub.trans (Finset.insert_subset_insert _ (Finset.erase_subset _ _)), hC'⟩
                  rw [heq] at hC'sub
                  rcases Finset.mem_insert.mp (hC'sub hyC) with rfl | hy_er
                  · exact hxI hyI
                  · exact (Finset.mem_erase.mp hy_er).1 rfl
                exact hyR (hR_closed x hxR y (Or.inr ⟨hxI, hyI, h_er_ind⟩))
          exact hC.1 (M₂.indep_subset hJind hC_sub_J)
        refine ⟨I, Finset.univ \ R, hI1, hI2, ?_⟩
        have hcomp : Finset.univ \ (Finset.univ \ R) = R := by ext e; simp
        rw [hcomp, hrank1, hrank2, add_comm, Finset.card_inter_add_card_sdiff]
  obtain ⟨I, A, hI1, hI2, hcard⟩ := hgap (Fintype.card E) ∅ (Nat.sub_le _ _) M₁.indep_empty M₂.indep_empty
  exact ⟨I, A, hI1, hI2, hcard, fun J hJ1 hJ2 => hcard ▸ hweak J A hJ1 hJ2,
    fun B => hweak I B hI1 hI2⟩

/-! ### Section 3: Finite Poset Möbius Function, Inversion, Weisner & Rota Cross-Cut -/

section Mobius

open Classical

/-- Möbius function `μ(x, y)` on any finite poset `P`, defined recursively on interval size. -/
noncomputable def mobiusFn {P : Type*} [Fintype P] [PartialOrder P] (x y : P) : ℤ :=
  if _hxy : x ≤ y then
    if _heq : x = y then 1
    else - ∑ z ∈ (Finset.univ.filter (fun z : P => x ≤ z ∧ z < y)).attach,
      mobiusFn x z.1
  else 0
termination_by (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).card
decreasing_by
  have hz := Finset.mem_filter.mp z.2
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.mpr ?_)
  · intro w hw
    rcases Finset.mem_filter.mp hw with ⟨_, hxw, hwz⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxw, le_trans hwz hz.2.2.le⟩
  · exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, _hxy, le_rfl⟩, fun h =>
      not_le_of_gt hz.2.2 (Finset.mem_filter.mp h).2.2⟩

lemma mobiusFn_not_le {P : Type*} [Fintype P] [PartialOrder P] {x y : P} (h : ¬ x ≤ y) :
    mobiusFn x y = 0 := by
  rw [mobiusFn, dif_neg h]

@[simp]
lemma mobiusFn_self {P : Type*} [Fintype P] [PartialOrder P] (x : P) :
    mobiusFn x x = 1 := by
  rw [mobiusFn, dif_pos le_rfl, dif_pos rfl]

/-- Left defining recurrence: `∑ z ∈ [x, y], mobiusFn x z = if x = y then 1 else 0` for `x ≤ y`. -/
theorem mobiusFn_sum_left {P : Type*} [Fintype P] [PartialOrder P] {x y : P} (hxy : x ≤ y) :
    ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y), mobiusFn x z =
      if x = y then 1 else 0 := by
  by_cases heq : x = y
  · subst heq
    have hsing : Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ x) = {x} := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun ⟨h1, h2⟩ => le_antisymm h2 h1, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩
    rw [hsing, Finset.sum_singleton, mobiusFn_self, if_pos rfl]
  · rw [if_neg heq]
    have hsplit : Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y) =
        insert y (Finset.univ.filter (fun z : P => x ≤ z ∧ z < y)) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      exact ⟨fun ⟨h1, h2⟩ => (eq_or_lt_of_le h2).elim Or.inl (fun h => Or.inr ⟨h1, h⟩),
        fun h => h.elim (fun hz => by subst hz; exact ⟨hxy, le_rfl⟩) (fun ⟨h1, h2⟩ => ⟨h1, h2.le⟩)⟩
    have hy_not : y ∉ Finset.univ.filter (fun z : P => x ≤ z ∧ z < y) := by
      simp
    rw [hsplit, Finset.sum_insert hy_not]
    have hdef : mobiusFn x y = - ∑ z ∈ (Finset.univ.filter (fun z : P => x ≤ z ∧ z < y)).attach,
        mobiusFn x z.1 := by
      conv_lhs => rw [mobiusFn]
      rw [dif_pos hxy, dif_neg heq]
    have hattach : ∑ z ∈ (Finset.univ.filter (fun z : P => x ≤ z ∧ z < y)).attach, mobiusFn x z.1 =
        ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z ∧ z < y), mobiusFn x z :=
      Finset.sum_attach _ (fun z => mobiusFn x z)
    rw [hdef, hattach, neg_add_cancel]

/-- Right dual recurrence: `∑ z ∈ [x, y], mobiusFn z y = if x = y then 1 else 0` for `x ≤ y`. -/
theorem mobiusFn_sum_right {P : Type*} [Fintype P] [PartialOrder P] {x y : P} (hxy : x ≤ y) :
    ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y), mobiusFn z y =
      if x = y then 1 else 0 := by
  have hind : ∀ k : ℕ, ∀ x y : P, x ≤ y →
      (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).card ≤ k →
      ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y), mobiusFn z y =
        if x = y then 1 else 0 := by
    intro k
    induction k with
    | zero =>
      intro x y hxy hk
      exfalso
      have hpos : 0 < (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).card :=
        Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hxy⟩⟩
      omega
    | succ k ih =>
      intro x y hxy hk
      by_cases heq : x = y
      · subst heq
        have hsing : Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ x) = {x} := by
          ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨fun ⟨h1, h2⟩ => le_antisymm h2 h1, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩
        rw [hsing, Finset.sum_singleton, mobiusFn_self, if_pos rfl]
      · rw [if_neg heq]
        let Ixy := Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)
        let S : ℤ := ∑ z ∈ Ixy, mobiusFn z y
        have hd1 : ∑ w ∈ Ixy, mobiusFn x w * (∑ z ∈ Finset.univ.filter (fun z => w ≤ z ∧ z ≤ y), mobiusFn z y) =
            S + mobiusFn x y := by
          have hx_mem : x ∈ Ixy := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hxy⟩
          rw [← Finset.add_sum_erase Ixy _ hx_mem, mobiusFn_self, one_mul]
          have hx_eq : ∑ z ∈ Finset.univ.filter (fun z => x ≤ z ∧ z ≤ y), mobiusFn z y = S := rfl
          rw [hx_eq]
          congr 1
          have h_er_sum : ∑ w ∈ Ixy.erase x, mobiusFn x w *
              (∑ z ∈ Finset.univ.filter (fun z => w ≤ z ∧ z ≤ y), mobiusFn z y) =
              ∑ w ∈ Ixy.erase x, if w = y then mobiusFn x y else 0 := by
            refine Finset.sum_congr rfl fun w hw => ?_
            rcases Finset.mem_erase.mp hw with ⟨hwx, hwI⟩
            have hwy : w ≤ y := (Finset.mem_filter.mp hwI).2.2
            have hsub : Finset.univ.filter (fun z => w ≤ z ∧ z ≤ y) ⊂ Ixy := by
              rw [Finset.ssubset_iff_of_subset]
              · exact ⟨x, hx_mem, fun h => hwx (le_antisymm (Finset.mem_filter.mp h).2.1 (Finset.mem_filter.mp hwI).2.1)⟩
              · intro z hz
                rcases Finset.mem_filter.mp hz with ⟨_, hwz, hzy⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans (Finset.mem_filter.mp hwI).2.1 hwz, hzy⟩
            have hcard_lt : (Finset.univ.filter (fun z => w ≤ z ∧ z ≤ y)).card ≤ k := by
              have hlt : (Finset.univ.filter (fun z => w ≤ z ∧ z ≤ y)).card < Ixy.card :=
                Finset.card_lt_card hsub
              have hle : Ixy.card ≤ k + 1 := hk
              omega
            rw [ih w y hwy hcard_lt]
            split_ifs with hwy_eq <;> simp [hwy_eq]
          rw [h_er_sum]
          have hy_mem : y ∈ Ixy.erase x := Finset.mem_erase.mpr ⟨Ne.symm heq,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy, le_rfl⟩⟩
          simp [hy_mem]
        have hd2 : ∑ w ∈ Ixy, mobiusFn x w * (∑ z ∈ Finset.univ.filter (fun z => w ≤ z ∧ z ≤ y), mobiusFn z y) =
            mobiusFn x y := by
          have hpair : ∑ w ∈ Ixy, mobiusFn x w * (∑ z ∈ Finset.univ.filter (fun z => w ≤ z ∧ z ≤ y), mobiusFn z y) =
              ∑ z ∈ Ixy, mobiusFn z y * (∑ w ∈ Finset.univ.filter (fun w => x ≤ w ∧ w ≤ z), mobiusFn x w) := by
            simp_rw [Finset.mul_sum]
            have h_lhs : ∑ w ∈ Ixy, ∑ z ∈ Finset.univ.filter (fun z => w ≤ z ∧ z ≤ y), mobiusFn x w * mobiusFn z y =
                ∑ w ∈ Ixy, ∑ z ∈ Ixy, if w ≤ z then mobiusFn x w * mobiusFn z y else 0 := by
              refine Finset.sum_congr rfl fun w hw => ?_
              rw [← Finset.sum_filter]
              refine Finset.sum_congr (by ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ixy]; exact ⟨fun ⟨hwz, hzy⟩ => ⟨⟨le_trans (Finset.mem_filter.mp hw).2.1 hwz, hzy⟩, hwz⟩, fun ⟨⟨_, hzy⟩, hwz⟩ => ⟨hwz, hzy⟩⟩) fun _ _ => rfl
            have h_rhs : ∑ z ∈ Ixy, ∑ w ∈ Finset.univ.filter (fun w => x ≤ w ∧ w ≤ z), mobiusFn z y * mobiusFn x w =
                ∑ z ∈ Ixy, ∑ w ∈ Ixy, if w ≤ z then mobiusFn x w * mobiusFn z y else 0 := by
              refine Finset.sum_congr rfl fun z hz => ?_
              rw [← Finset.sum_filter]
              refine Finset.sum_congr (by ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ixy]; exact ⟨fun ⟨hxw, hwz⟩ => ⟨⟨hxw, le_trans hwz (Finset.mem_filter.mp hz).2.2⟩, hwz⟩, fun ⟨⟨hxw, _⟩, hwz⟩ => ⟨hxw, hwz⟩⟩) fun _ _ => by ring
            rw [h_lhs, h_rhs, Finset.sum_comm]
          rw [hpair]
          have hsum_z : ∑ z ∈ Ixy, mobiusFn z y * (∑ w ∈ Finset.univ.filter (fun w => x ≤ w ∧ w ≤ z), mobiusFn x w) =
              ∑ z ∈ Ixy, if x = z then mobiusFn x y else 0 := by
            refine Finset.sum_congr rfl fun z hz => ?_
            rw [mobiusFn_sum_left (Finset.mem_filter.mp hz).2.1]
            split_ifs with hxz <;> simp [hxz]
          rw [hsum_z]
          have hx_mem : x ∈ Ixy := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hxy⟩
          simp [hx_mem]
        change S = 0
        linarith
  exact hind (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).card x y hxy le_rfl

/-- Uniqueness of left Möbius inverse on a finite poset. -/
lemma mobiusFn_eq_of_sum_left {P : Type*} [Fintype P] [PartialOrder P]
    (f : P → P → ℤ) (hf : ∀ x y : P, x ≤ y →
      ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y), f x z = if x = y then 1 else 0)
    {x y : P} (hxy : x ≤ y) : mobiusFn x y = f x y := by
  have hind : ∀ k : ℕ, ∀ x y : P, x ≤ y →
      (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).card ≤ k →
      mobiusFn x y = f x y := by
    intro k
    induction k with
    | zero =>
      intro x y hxy hk
      exfalso
      have hpos : 0 < (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).card :=
        Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hxy⟩⟩
      omega
    | succ k ih =>
      intro x y hxy hk
      have h1 := mobiusFn_sum_left hxy
      have h2 := hf x y hxy
      have hy_mem : y ∈ Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy, le_rfl⟩
      rw [← Finset.add_sum_erase _ _ hy_mem] at h1 h2
      have h_er : ∑ z ∈ (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).erase y, mobiusFn x z =
          ∑ z ∈ (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).erase y, f x z := by
        refine Finset.sum_congr rfl fun z hz => ?_
        rcases Finset.mem_erase.mp hz with ⟨hzy, hzI⟩
        have hxz : x ≤ z := (Finset.mem_filter.mp hzI).2.1
        have hsub : Finset.univ.filter (fun w => x ≤ w ∧ w ≤ z) ⊂
            Finset.univ.filter (fun w => x ≤ w ∧ w ≤ y) := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨y, hy_mem, fun h => hzy (le_antisymm (Finset.mem_filter.mp hzI).2.2 (Finset.mem_filter.mp h).2.2)⟩
          · intro w hw
            rcases Finset.mem_filter.mp hw with ⟨_, hxw, hwz⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxw, le_trans hwz (Finset.mem_filter.mp hzI).2.2⟩
        have hcard_lt : (Finset.univ.filter (fun w => x ≤ w ∧ w ≤ z)).card ≤ k := by
          have := Finset.card_lt_card hsub; omega
        exact ih x z hxz hcard_lt
      linarith
  exact hind (Finset.univ.filter (fun z : P => x ≤ z ∧ z ≤ y)).card x y hxy le_rfl

private lemma sum_filter_comm_le {P G : Type*} [Fintype P] [PartialOrder P] [AddCommGroup G]
    (h : P → P → G) (y : P) :
    (∑ x ∈ Finset.univ.filter (fun x : P => x ≤ y),
      ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ x), h x z) =
    ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ y),
      ∑ x ∈ Finset.univ.filter (fun x : P => z ≤ x ∧ x ≤ y), h x z := by
  have hlhs : (∑ x ∈ Finset.univ.filter (fun x : P => x ≤ y),
        ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ x), h x z) =
      ∑ x : P, ∑ z : P, if z ≤ x ∧ x ≤ y then h x z else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hxy : x ≤ y
    · rw [if_pos hxy, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => by simp [hxy]
    · rw [if_neg hxy, Finset.sum_eq_zero]
      intro z _; rw [if_neg (fun h => hxy h.2)]
  have hrhs : (∑ z ∈ Finset.univ.filter (fun z : P => z ≤ y),
        ∑ x ∈ Finset.univ.filter (fun x : P => z ≤ x ∧ x ≤ y), h x z) =
      ∑ z : P, ∑ x : P, if z ≤ x ∧ x ≤ y then h x z else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hzy : z ≤ y
    · rw [if_pos hzy, Finset.sum_filter]
    · rw [if_neg hzy, Finset.sum_eq_zero]
      intro x _; rw [if_neg (fun ⟨hzx, hxy⟩ => hzy (le_trans hzx hxy))]
  rw [hlhs, hrhs, Finset.sum_comm]

private lemma sum_filter_comm_ge {P G : Type*} [Fintype P] [PartialOrder P] [AddCommGroup G]
    (h : P → P → G) (x : P) :
    (∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y),
      ∑ z ∈ Finset.univ.filter (fun z : P => y ≤ z), h y z) =
    ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z),
      ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y ∧ y ≤ z), h y z := by
  have hlhs : (∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y),
        ∑ z ∈ Finset.univ.filter (fun z : P => y ≤ z), h y z) =
      ∑ y : P, ∑ z : P, if x ≤ y ∧ y ≤ z then h y z else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hxy : x ≤ y
    · rw [if_pos hxy, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => by simp [hxy]
    · rw [if_neg hxy, Finset.sum_eq_zero]
      intro z _; rw [if_neg (fun h => hxy h.1)]
  have hrhs : (∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z),
        ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y ∧ y ≤ z), h y z) =
      ∑ z : P, ∑ y : P, if x ≤ y ∧ y ≤ z then h y z else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hxz : x ≤ z
    · rw [if_pos hxz, Finset.sum_filter]
    · rw [if_neg hxz, Finset.sum_eq_zero]
      intro y _; rw [if_neg (fun ⟨hxy, hyz⟩ => hxz (le_trans hxy hyz))]
  rw [hlhs, hrhs, Finset.sum_comm]

/-- **Finite Poset Möbius Inversion (Left / Downward-Interval Form)**:
`g y = ∑ x ≤ y, f x` for all `y` iff `f y = ∑ x ≤ y, mobiusFn x y • g x` for all `y`. -/
theorem poset_mobius_inversion_left {P G : Type*} [Fintype P] [PartialOrder P]
    [AddCommGroup G] (f g : P → G) :
    (∀ y : P, g y = ∑ x ∈ Finset.univ.filter (fun x : P => x ≤ y), f x) ↔
      (∀ y : P, f y = ∑ x ∈ Finset.univ.filter (fun x : P => x ≤ y), mobiusFn x y • g x) := by
  constructor
  · intro hg y
    symm
    calc ∑ x ∈ Finset.univ.filter (fun x : P => x ≤ y), mobiusFn x y • g x
        = ∑ x ∈ Finset.univ.filter (fun x : P => x ≤ y),
            ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ x), mobiusFn x y • f z := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hg x, Finset.smul_sum]
      _ = ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ y),
            ∑ x ∈ Finset.univ.filter (fun x : P => z ≤ x ∧ x ≤ y), mobiusFn x y • f z :=
            sum_filter_comm_le (fun x z => mobiusFn x y • f z) y
      _ = ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ y), if z = y then f y else 0 := by
            refine Finset.sum_congr rfl fun z hz => ?_
            rw [← Finset.sum_smul, mobiusFn_sum_right (Finset.mem_filter.mp hz).2]
            split_ifs with hzy <;> simp [hzy]
      _ = f y := by simp
  · intro hf y
    symm
    calc ∑ x ∈ Finset.univ.filter (fun x : P => x ≤ y), f x
        = ∑ x ∈ Finset.univ.filter (fun x : P => x ≤ y),
            ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ x), mobiusFn z x • g z := by
            refine Finset.sum_congr rfl fun x _ => hf x
      _ = ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ y),
            ∑ x ∈ Finset.univ.filter (fun x : P => z ≤ x ∧ x ≤ y), mobiusFn z x • g z :=
            sum_filter_comm_le (fun x z => mobiusFn z x • g z) y
      _ = ∑ z ∈ Finset.univ.filter (fun z : P => z ≤ y), if z = y then g y else 0 := by
            refine Finset.sum_congr rfl fun z hz => ?_
            rw [← Finset.sum_smul, mobiusFn_sum_left (Finset.mem_filter.mp hz).2]
            split_ifs with hzy <;> simp [hzy]
      _ = g y := by simp

/-- **Finite Poset Möbius Inversion (Right / Upward-Interval Form)**:
`g x = ∑ y ≥ x, f y` for all `x` iff `f x = ∑ y ≥ x, mobiusFn x y • g y` for all `x`. -/
theorem poset_mobius_inversion_right {P G : Type*} [Fintype P] [PartialOrder P]
    [AddCommGroup G] (f g : P → G) :
    (∀ x : P, g x = ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y), f y) ↔
      (∀ x : P, f x = ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y), mobiusFn x y • g y) := by
  constructor
  · intro hg x
    symm
    calc ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y), mobiusFn x y • g y
        = ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y),
            ∑ z ∈ Finset.univ.filter (fun z : P => y ≤ z), mobiusFn x y • f z := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hg y, Finset.smul_sum]
      _ = ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z),
            ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y ∧ y ≤ z), mobiusFn x y • f z :=
            sum_filter_comm_ge (fun y z => mobiusFn x y • f z) x
      _ = ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z), if x = z then f x else 0 := by
            refine Finset.sum_congr rfl fun z hz => ?_
            rw [← Finset.sum_smul, mobiusFn_sum_left (Finset.mem_filter.mp hz).2]
            split_ifs with hxz <;> simp [hxz]
      _ = f x := by simp
  · intro hf x
    symm
    calc ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y), f y
        = ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y),
            ∑ z ∈ Finset.univ.filter (fun z : P => y ≤ z), mobiusFn y z • g z := by
            refine Finset.sum_congr rfl fun y _ => hf y
      _ = ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z),
            ∑ y ∈ Finset.univ.filter (fun y : P => x ≤ y ∧ y ≤ z), mobiusFn y z • g z :=
            sum_filter_comm_ge (fun y z => mobiusFn y z • g z) x
      _ = ∑ z ∈ Finset.univ.filter (fun z : P => x ≤ z), if x = z then g x else 0 := by
            refine Finset.sum_congr rfl fun z hz => ?_
            rw [← Finset.sum_smul, mobiusFn_sum_right (Finset.mem_filter.mp hz).2]
            split_ifs with hxz <;> simp [hxz]
      _ = g x := by simp

/-- **Weisner's Theorem (1935)**: in any finite bounded lattice `L`, for any `a < ⊤`,
`∑_{x : x ⊓ a = ⊥} μ(x, ⊤) = 0`. -/
theorem weisner_theorem {L : Type*} [Fintype L] [Lattice L] [BoundedOrder L]
    (a : L) (ha : a < ⊤) :
    ∑ x ∈ Finset.univ.filter (fun x : L => x ⊓ a = ⊥), mobiusFn x ⊤ = 0 := by
  have hlhs : ∑ z ∈ Finset.univ.filter (fun z : L => z ≤ a),
      mobiusFn (⊥ : L) z * ∑ x ∈ Finset.univ.filter (fun x : L => z ≤ x), mobiusFn x ⊤ = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have hza : z ≤ a := (Finset.mem_filter.mp hz).2
    have hzt : z ≤ ⊤ := le_top
    have hne : z ≠ ⊤ := (lt_of_le_of_lt hza ha).ne
    have hsum : ∑ x ∈ Finset.univ.filter (fun x : L => z ≤ x), mobiusFn x ⊤ = 0 := by
      have h1 := mobiusFn_sum_right hzt
      rw [if_neg hne] at h1
      convert h1 using 2
      ext x; simp [le_top]
    rw [hsum, mul_zero]
  have hswap : ∑ z ∈ Finset.univ.filter (fun z : L => z ≤ a),
      mobiusFn (⊥ : L) z * ∑ x ∈ Finset.univ.filter (fun x : L => z ≤ x), mobiusFn x ⊤ =
      ∑ x : L, mobiusFn x ⊤ * ∑ z ∈ Finset.univ.filter (fun z : L => z ≤ x ⊓ a), mobiusFn ⊥ z := by
    simp_rw [Finset.mul_sum]
    have h1 : (∑ z ∈ Finset.univ.filter (fun z : L => z ≤ a),
          ∑ x ∈ Finset.univ.filter (fun x : L => z ≤ x), mobiusFn ⊥ z * mobiusFn x ⊤) =
        ∑ z : L, ∑ x : L, if z ≤ a ∧ z ≤ x then mobiusFn ⊥ z * mobiusFn x ⊤ else 0 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hza : z ≤ a
      · rw [if_pos hza, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => by simp [hza]
      · rw [if_neg hza, Finset.sum_eq_zero]
        intro x _; rw [if_neg (fun h => hza h.1)]
    have h2 : (∑ x : L, ∑ z ∈ Finset.univ.filter (fun z : L => z ≤ x ⊓ a),
          mobiusFn x ⊤ * mobiusFn ⊥ z) =
        ∑ x : L, ∑ z : L, if z ≤ a ∧ z ≤ x then mobiusFn ⊥ z * mobiusFn x ⊤ else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [le_inf_iff, and_comm, mul_comm]
    rw [h1, h2, Finset.sum_comm]
  rw [hlhs] at hswap
  have heval : ∑ x : L, mobiusFn x ⊤ * ∑ z ∈ Finset.univ.filter (fun z : L => z ≤ x ⊓ a), mobiusFn ⊥ z =
      ∑ x ∈ Finset.univ.filter (fun x : L => x ⊓ a = ⊥), mobiusFn x ⊤ := by
    have hterm : ∀ x : L, mobiusFn x ⊤ *
        ∑ z ∈ Finset.univ.filter (fun z : L => z ≤ x ⊓ a), mobiusFn ⊥ z =
        if x ⊓ a = ⊥ then mobiusFn x ⊤ else 0 := by
      intro x
      have hsum : ∑ z ∈ Finset.univ.filter (fun z : L => z ≤ x ⊓ a), mobiusFn ⊥ z =
          if ⊥ = x ⊓ a then 1 else 0 := by
        convert mobiusFn_sum_left (bot_le : (⊥ : L) ≤ x ⊓ a) using 2
        ext z; simp [bot_le]
      rw [hsum]
      by_cases hbot : x ⊓ a = ⊥
      · simp [hbot]
      · have hbot' : ⊥ ≠ x ⊓ a := Ne.symm hbot
        simp [hbot, hbot']
    simp_rw [hterm, ← Finset.sum_filter]
  rw [heval] at hswap
  exact hswap.symm

/-- **Weisner's Theorem (Dual Form)**: in any finite bounded lattice `L`, for any `⊥ < a`,
`∑_{x : x ⊔ a = ⊤} μ(⊥, x) = 0`. -/
theorem weisner_theorem_dual {L : Type*} [Fintype L] [Lattice L] [BoundedOrder L]
    (a : L) (ha : ⊥ < a) :
    ∑ x ∈ Finset.univ.filter (fun x : L => x ⊔ a = ⊤), mobiusFn ⊥ x = 0 := by
  have hlhs : ∑ z ∈ Finset.univ.filter (fun z : L => a ≤ z),
      mobiusFn z (⊤ : L) * ∑ x ∈ Finset.univ.filter (fun x : L => x ≤ z), mobiusFn ⊥ x = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have haz : a ≤ z := (Finset.mem_filter.mp hz).2
    have hne : (⊥ : L) ≠ z := (lt_of_lt_of_le ha haz).ne
    have hsum : ∑ x ∈ Finset.univ.filter (fun x : L => x ≤ z), mobiusFn ⊥ x = 0 := by
      have h1 := mobiusFn_sum_left (bot_le : (⊥ : L) ≤ z)
      rw [if_neg hne] at h1
      convert h1 using 2
      ext x; simp [bot_le]
    rw [hsum, mul_zero]
  have hswap : ∑ z ∈ Finset.univ.filter (fun z : L => a ≤ z),
      mobiusFn z (⊤ : L) * ∑ x ∈ Finset.univ.filter (fun x : L => x ≤ z), mobiusFn ⊥ x =
      ∑ x : L, mobiusFn ⊥ x * ∑ z ∈ Finset.univ.filter (fun z : L => x ⊔ a ≤ z), mobiusFn z ⊤ := by
    simp_rw [Finset.mul_sum]
    have h1 : (∑ z ∈ Finset.univ.filter (fun z : L => a ≤ z),
          ∑ x ∈ Finset.univ.filter (fun x : L => x ≤ z), mobiusFn z ⊤ * mobiusFn ⊥ x) =
        ∑ z : L, ∑ x : L, if a ≤ z ∧ x ≤ z then mobiusFn z ⊤ * mobiusFn ⊥ x else 0 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases haz : a ≤ z
      · rw [if_pos haz, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => by simp [haz]
      · rw [if_neg haz, Finset.sum_eq_zero]
        intro x _; rw [if_neg (fun h => haz h.1)]
    have h2 : (∑ x : L, ∑ z ∈ Finset.univ.filter (fun z : L => x ⊔ a ≤ z),
          mobiusFn ⊥ x * mobiusFn z ⊤) =
        ∑ x : L, ∑ z : L, if a ≤ z ∧ x ≤ z then mobiusFn z ⊤ * mobiusFn ⊥ x else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [sup_le_iff, and_comm, mul_comm]
    rw [h1, h2, Finset.sum_comm]
  rw [hlhs] at hswap
  have heval : ∑ x : L, mobiusFn ⊥ x * ∑ z ∈ Finset.univ.filter (fun z : L => x ⊔ a ≤ z), mobiusFn z ⊤ =
      ∑ x ∈ Finset.univ.filter (fun x : L => x ⊔ a = ⊤), mobiusFn ⊥ x := by
    have hterm : ∀ x : L, mobiusFn ⊥ x *
        ∑ z ∈ Finset.univ.filter (fun z : L => x ⊔ a ≤ z), mobiusFn z ⊤ =
        if x ⊔ a = ⊤ then mobiusFn ⊥ x else 0 := by
      intro x
      have hsum : ∑ z ∈ Finset.univ.filter (fun z : L => x ⊔ a ≤ z), mobiusFn z ⊤ =
          if x ⊔ a = ⊤ then 1 else 0 := by
        convert mobiusFn_sum_right (le_top : x ⊔ a ≤ ⊤) using 2
        ext z; simp [le_top]
      rw [hsum]
      split_ifs <;> simp
    simp_rw [hterm, ← Finset.sum_filter]
  rw [heval] at hswap
  exact hswap.symm

private lemma sum_powerset_neg_one {α : Type*} [DecidableEq α] (T : Finset α) :
    ∑ S ∈ T.powerset, (-1 : ℤ) ^ S.card = if T = ∅ then 1 else 0 := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T' ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · have himg : ∑ S ∈ T'.powerset.image (insert a), (-1 : ℤ) ^ S.card =
          - ∑ S ∈ T'.powerset, (-1 : ℤ) ^ S.card := by
        rw [Finset.sum_image]
        · rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun S hS => ?_
          have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
          rw [Finset.card_insert_of_notMem haS, pow_succ, mul_neg_one]
        · intro S₁ h1 S₂ h2 heq
          have ha1 : a ∉ S₁ := fun h => ha (Finset.mem_powerset.mp h1 h)
          have ha2 : a ∉ S₂ := fun h => ha (Finset.mem_powerset.mp h2 h)
          rw [← Finset.erase_insert ha1, ← Finset.erase_insert ha2, heq]
      rw [himg, add_neg_cancel, if_neg (Finset.insert_ne_empty a T')]
    · rw [Finset.disjoint_left]
      intro S h1 h2
      rcases Finset.mem_image.mp h2 with ⟨S', _, rfl⟩
      exact ha (Finset.mem_powerset.mp h1 (Finset.mem_insert_self a S'))

/-- **Rota's Join-Spanning Cross-Cut Theorem**: if `C : Finset L` omits `⊥` and every `z > ⊥`
lies above some `c ∈ C`, then `μ(⊥, ⊤) = ∑_{S ⊆ C, S.sup id = ⊤} (-1)^{|S|}`. -/
theorem rota_crosscut_join {L : Type*} [Fintype L] [Lattice L] [BoundedOrder L]
    (C : Finset L) (hbot : (⊥ : L) ∉ C) (hspan : ∀ z : L, ⊥ < z → ∃ c ∈ C, c ≤ z) :
    mobiusFn (⊥ : L) ⊤ =
      ∑ S ∈ C.powerset.filter (fun S => S.sup id = ⊤), (-1 : ℤ) ^ S.card := by
  let f : L → ℤ := fun x => ∑ S ∈ C.powerset.filter (fun S => S.sup id = x), (-1 : ℤ) ^ S.card
  let g : L → ℤ := fun z => ∑ x ∈ Finset.univ.filter (fun x : L => x ≤ z), f x
  have hg_eval : ∀ z : L, g z = if z = ⊥ then 1 else 0 := by
    intro z
    have hpart : g z = ∑ S ∈ (C.filter (fun c => c ≤ z)).powerset, (-1 : ℤ) ^ S.card := by
      have h1 : g z = ∑ S ∈ C.powerset.filter (fun S => S.sup id ≤ z), (-1 : ℤ) ^ S.card := by
        simp only [g, f]
        have hbi : (Finset.univ.filter (fun x : L => x ≤ z)).biUnion
              (fun x => C.powerset.filter (fun S => S.sup id = x)) =
            C.powerset.filter (fun S => S.sup id ≤ z) := by
          ext S
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨x, hxz, hSC, hSx⟩ => ⟨hSC, hSx ▸ hxz⟩,
            fun ⟨hSC, hSz⟩ => ⟨S.sup id, hSz, hSC, rfl⟩⟩
        have hdisj : ((Finset.univ.filter (fun x : L => x ≤ z) : Finset L) : Set L).PairwiseDisjoint
            (fun x => C.powerset.filter (fun S => S.sup id = x)) := by
          intro x₁ _ x₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro S h1 h2
          exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
        rw [← Finset.sum_biUnion hdisj, hbi]
      rw [h1]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.sup_le_iff, id_eq]
      exact ⟨fun ⟨hSC, hSz⟩ c hc => Finset.mem_filter.mpr ⟨hSC hc, hSz c hc⟩,
        fun hS => ⟨fun c hc => (Finset.mem_filter.mp (hS hc)).1,
          fun c hc => (Finset.mem_filter.mp (hS hc)).2⟩⟩
    rw [hpart, sum_powerset_neg_one]
    by_cases hz : z = ⊥
    · subst hz
      have hemp : C.filter (fun c => c ≤ (⊥ : L)) = ∅ := by
        ext c; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hc hle; rw [le_bot_iff.mp hle] at hc; exact hbot hc
      rw [hemp]; simp
    · have hne : (C.filter (fun c => c ≤ z)).Nonempty := by
        obtain ⟨c, hcC, hcz⟩ := hspan z (bot_lt_iff_ne_bot.mpr hz)
        exact ⟨c, Finset.mem_filter.mpr ⟨hcC, hcz⟩⟩
      simp [hz, hne.ne_empty]
  have hinv := (poset_mobius_inversion_left f g).mp (fun _ => rfl) ⊤
  have hf_top : f ⊤ = mobiusFn (⊥ : L) ⊤ := by
    rw [hinv]
    have hterm : ∀ z : L, mobiusFn z ⊤ • g z = if z = ⊥ then mobiusFn (⊥ : L) ⊤ else 0 := fun z => by
      rw [hg_eval z]
      split_ifs with hz
      · subst hz; simp
      · simp
    simp_rw [hterm]
    simp [le_top]
  exact hf_top.symm

/-- **Rota's Cross-Cut Theorem (1964)**: if `⊥ < ⊤` in a finite bounded lattice `L` and `C` is
an antichain omitting `⊥, ⊤` that intersects every maximal chain, then
`μ(⊥, ⊤) = ∑_{S ⊆ C, S.Nonempty, S.sup id = ⊤, S.inf id = ⊥} (-1)^{|S|}`. -/
theorem rota_crosscut_theorem {L : Type*} [Fintype L] [Lattice L] [BoundedOrder L]
    (_hbt : (⊥ : L) < ⊤) (C : Finset L)
    (hanti : IsAntichain (· ≤ ·) (C : Set L))
    (hbot : (⊥ : L) ∉ C) (htop : (⊤ : L) ∉ C)
    (hmax : ∀ M : Finset L, IsChain (· ≤ ·) (M : Set L) →
      (∀ x : L, (∀ m ∈ M, m ≤ x ∨ x ≤ m) → x ∈ M) → (M ∩ C).Nonempty) :
    mobiusFn (⊥ : L) ⊤ =
      ∑ S ∈ C.powerset.filter (fun S => S.Nonempty ∧ S.sup id = ⊤ ∧ S.inf id = ⊥),
        (-1 : ℤ) ^ S.card := by
  have h_max_ext : ∀ M₀ : Finset L, IsChain (· ≤ ·) (M₀ : Set L) →
      ∃ M : Finset L, M₀ ⊆ M ∧ IsChain (· ≤ ·) (M : Set L) ∧
        (∀ x : L, (∀ m ∈ M, m ≤ x ∨ x ≤ m) → x ∈ M) := by
    intro M₀ hM₀
    have hex : ∀ k : ℕ, ∀ M : Finset L, IsChain (· ≤ ·) (M : Set L) →
        Fintype.card L - M.card ≤ k →
        ∃ M' : Finset L, M ⊆ M' ∧ IsChain (· ≤ ·) (M' : Set L) ∧
          (∀ x : L, (∀ m ∈ M', m ≤ x ∨ x ≤ m) → x ∈ M') := by
      intro k
      induction k with
      | zero =>
        intro M hM hk
        have hfull : M = Finset.univ := Finset.eq_univ_of_card M
          (le_antisymm (Finset.card_le_univ M) (by omega))
        exact ⟨M, Finset.Subset.rfl, hM, fun x _ => hfull ▸ Finset.mem_univ x⟩
      | succ k ih =>
        intro M hM hk
        by_cases hdone : ∀ x : L, (∀ m ∈ M, m ≤ x ∨ x ≤ m) → x ∈ M
        · exact ⟨M, Finset.Subset.rfl, hM, hdone⟩
        · push Not at hdone
          obtain ⟨x, hxcomp, hxM⟩ := hdone
          have hMx : IsChain (· ≤ ·) ((insert x M : Finset L) : Set L) := by
            intro a ha b hb hab
            simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
            rcases ha with rfl | haM <;> rcases hb with rfl | hbM
            · exact absurd rfl hab
            · exact (hxcomp b hbM).symm
            · exact hxcomp a haM
            · exact hM haM hbM hab
          have hk' : Fintype.card L - (insert x M).card ≤ k := by
            rw [Finset.card_insert_of_notMem hxM]
            have hle : M.card < Fintype.card L := by
              rw [← Finset.card_univ]
              exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => hxM (h ▸ Finset.mem_univ x))
            omega
          obtain ⟨M', hsub, hM', hmax'⟩ := ih (insert x M) hMx hk'
          exact ⟨M', (Finset.subset_insert x M).trans hsub, hM', hmax'⟩
    exact hex (Fintype.card L) M₀ hM₀ (Nat.sub_le _ _)
  have hC_ne : C.Nonempty := by
    obtain ⟨M, _, hM, hMm⟩ := h_max_ext ∅ (by simp)
    obtain ⟨c, hc⟩ := hmax M hM hMm
    exact ⟨c, (Finset.mem_inter.mp hc).2⟩
  let g : L → L → ℤ := fun u v =>
    ∑ S ∈ C.powerset.filter (fun S => S.Nonempty ∧ u ≤ S.inf id ∧ S.sup id ≤ v), (-1 : ℤ) ^ S.card
  have hg_eval : ∀ u v : L, u ≤ v →
      g u v = (if C.filter (fun c => u ≤ c ∧ c ≤ v) = ∅ then 1 else 0) - 1 := by
    intro u v huv
    let Cuv := C.filter (fun c => u ≤ c ∧ c ≤ v)
    have hsub : C.powerset.filter (fun S => S.Nonempty ∧ u ≤ S.inf id ∧ S.sup id ≤ v) =
        Cuv.powerset.erase ∅ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, Finset.nonempty_iff_ne_empty,
        Finset.le_inf_iff, Finset.sup_le_iff, id_eq, Cuv]
      constructor
      · rintro ⟨hSC, hSne, huS, hSv⟩
        exact ⟨hSne, fun c hc => Finset.mem_filter.mpr ⟨hSC hc, huS c hc, hSv c hc⟩⟩
      · rintro ⟨hSne, hSC⟩
        exact ⟨fun c hc => (Finset.mem_filter.mp (hSC hc)).1, hSne,
          fun c hc => (Finset.mem_filter.mp (hSC hc)).2.1,
          fun c hc => (Finset.mem_filter.mp (hSC hc)).2.2⟩
    have hem_mem : (∅ : Finset L) ∈ Cuv.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
    have hsum_er : ∑ S ∈ Cuv.powerset.erase ∅, (-1 : ℤ) ^ S.card =
        (∑ S ∈ Cuv.powerset, (-1 : ℤ) ^ S.card) - 1 := by
      have h1 := Finset.add_sum_erase Cuv.powerset (fun S => (-1 : ℤ) ^ S.card) hem_mem
      simp only [Finset.card_empty, pow_zero] at h1
      linarith
    rw [show g u v = ∑ S ∈ Cuv.powerset.erase ∅, (-1 : ℤ) ^ S.card by dsimp only [g]; rw [hsub],
      hsum_er, sum_powerset_neg_one]
  have h_double_lhs : ∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
      mobiusFn ⊥ u * g u v * mobiusFn v ⊤ =
      ∑ S ∈ C.powerset.filter (fun S => S.Nonempty ∧ S.sup id = ⊤ ∧ S.inf id = ⊥),
        (-1 : ℤ) ^ S.card := by
    let P_S := C.powerset.filter (fun S => S.Nonempty)
    have h_inner : ∀ u v : L, u ≤ v →
        mobiusFn ⊥ u * g u v * mobiusFn v ⊤ =
          ∑ S ∈ P_S, if u ≤ S.inf id ∧ S.sup id ≤ v then
            mobiusFn ⊥ u * (-1 : ℤ) ^ S.card * mobiusFn v ⊤ else 0 := by
      intro u v _
      dsimp only [g, P_S]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_filter]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun S hS => ?_
      by_cases hSne : S.Nonempty <;> by_cases huvS : u ≤ S.inf id ∧ S.sup id ≤ v <;>
        simp [hSne, huvS, mul_assoc, mul_left_comm]
    have h1 : (∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
          mobiusFn ⊥ u * g u v * mobiusFn v ⊤) =
        ∑ u : L, ∑ v : L, ∑ S ∈ P_S,
          if u ≤ S.inf id ∧ S.sup id ≤ v then
            mobiusFn ⊥ u * (-1 : ℤ) ^ S.card * mobiusFn v ⊤ else 0 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases huv : u ≤ v
      · rw [if_pos huv, h_inner u v huv]
      · rw [if_neg huv, Finset.sum_eq_zero]
        intro S hS
        have hSne : S.Nonempty := (Finset.mem_filter.mp hS).2
        obtain ⟨c, hc⟩ := hSne
        have hle : S.inf id ≤ S.sup id := le_trans (Finset.inf_le hc) (Finset.le_sup hc)
        rw [if_neg (fun ⟨h1, h2⟩ => huv (le_trans h1 (le_trans hle h2)))]
    rw [h1]
    conv_lhs =>
      arg 2; ext u
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    have h_each : ∀ S ∈ P_S,
        (∑ v : L, ∑ u : L, if u ≤ S.inf id ∧ S.sup id ≤ v then
          mobiusFn ⊥ u * (-1 : ℤ) ^ S.card * mobiusFn v ⊤ else 0) =
        if S.sup id = ⊤ ∧ S.inf id = ⊥ then (-1 : ℤ) ^ S.card else 0 := by
      intro S hS
      have h_factor : (∑ v : L, ∑ u : L, if u ≤ S.inf id ∧ S.sup id ≤ v then
            mobiusFn ⊥ u * (-1 : ℤ) ^ S.card * mobiusFn v ⊤ else 0) =
          (-1 : ℤ) ^ S.card *
            (∑ u ∈ Finset.univ.filter (fun u : L => u ≤ S.inf id), mobiusFn ⊥ u) *
            (∑ v ∈ Finset.univ.filter (fun v : L => S.sup id ≤ v), mobiusFn v ⊤) := by
        have h_lhs : (∑ v : L, ∑ u : L, if u ≤ S.inf id ∧ S.sup id ≤ v then
              mobiusFn ⊥ u * (-1 : ℤ) ^ S.card * mobiusFn v ⊤ else 0) =
            ∑ v ∈ Finset.univ.filter (fun v : L => S.sup id ≤ v),
              ∑ u ∈ Finset.univ.filter (fun u : L => u ≤ S.inf id),
                (-1 : ℤ) ^ S.card * mobiusFn ⊥ u * mobiusFn v ⊤ := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases hSv : S.sup id ≤ v
          · rw [if_pos hSv, Finset.sum_filter]
            refine Finset.sum_congr rfl fun u _ => by
              simp only [hSv, and_true]
              split_ifs
              · ring
              · rfl
          · rw [if_neg hSv, Finset.sum_eq_zero]
            intro u _; rw [if_neg (fun h => hSv h.2)]
        rw [h_lhs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
      rw [h_factor]
      have hsum_u : ∑ u ∈ Finset.univ.filter (fun u : L => u ≤ S.inf id), mobiusFn ⊥ u =
          if ⊥ = S.inf id then 1 else 0 := by
        convert mobiusFn_sum_left (bot_le : (⊥ : L) ≤ S.inf id) using 2
        ext u; simp [bot_le]
      have hsum_v : ∑ v ∈ Finset.univ.filter (fun v : L => S.sup id ≤ v), mobiusFn v ⊤ =
          if S.sup id = ⊤ then 1 else 0 := by
        convert mobiusFn_sum_right (le_top : S.sup id ≤ ⊤) using 2
        ext v; simp [le_top]
      rw [hsum_u, hsum_v]
      by_cases hsup : S.sup id = ⊤ <;> by_cases hinf : S.inf id = ⊥
      · simp [hsup, hinf]
      · simp [hsup, hinf, Ne.symm hinf]
      · simp [hsup, hinf]
      · simp [hsup, hinf]
    calc ∑ S ∈ P_S, ∑ u : L, ∑ v : L,
          (if u ≤ S.inf id ∧ S.sup id ≤ v then mobiusFn ⊥ u * (-1 : ℤ) ^ S.card * mobiusFn v ⊤ else 0)
        = ∑ S ∈ P_S, ∑ v : L, ∑ u : L,
          (if u ≤ S.inf id ∧ S.sup id ≤ v then mobiusFn ⊥ u * (-1 : ℤ) ^ S.card * mobiusFn v ⊤ else 0) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ S ∈ P_S, if S.sup id = ⊤ ∧ S.inf id = ⊥ then (-1 : ℤ) ^ S.card else 0 :=
          Finset.sum_congr rfl h_each
      _ = ∑ S ∈ P_S.filter (fun S => S.sup id = ⊤ ∧ S.inf id = ⊥), (-1 : ℤ) ^ S.card :=
          (Finset.sum_filter _ _).symm
      _ = _ := by
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext S
          simp only [P_S, Finset.mem_filter, Finset.mem_powerset]
          tauto
  have h_double_rhs : ∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
      mobiusFn ⊥ u * g u v * mobiusFn v ⊤ = mobiusFn (⊥ : L) ⊤ := by
    have hsplit : (∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
          mobiusFn ⊥ u * g u v * mobiusFn v ⊤) =
        (∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
          if C.filter (fun c => u ≤ c ∧ c ≤ v) = ∅ then mobiusFn ⊥ u * mobiusFn v ⊤ else 0) -
        (∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
          mobiusFn ⊥ u * mobiusFn v ⊤) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [hg_eval u v (Finset.mem_filter.mp hv).2]
      split_ifs <;> ring
    have h_all : ∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
        mobiusFn ⊥ u * mobiusFn v ⊤ = mobiusFn (⊥ : L) ⊤ := by
      have hterm : ∀ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
          mobiusFn ⊥ u * mobiusFn v ⊤ = if u = ⊤ then mobiusFn (⊥ : L) ⊤ else 0 := by
        intro u
        rw [← Finset.mul_sum]
        have hsum : ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v), mobiusFn v ⊤ =
            if u = ⊤ then 1 else 0 := by
          convert mobiusFn_sum_right (le_top : u ≤ ⊤) using 2
          ext v; simp [le_top]
        rw [hsum]
        split_ifs with hu
        · rw [hu, mul_one]
        · rw [mul_zero]
      rw [Finset.sum_congr rfl fun u _ => hterm u]
      simp
    have h_empty_split : ∀ u v : L, u ≤ v → C.filter (fun c => u ≤ c ∧ c ≤ v) = ∅ →
        (∃ c ∈ C, c < u) ∨ (∃ c ∈ C, v < c) := by
      intro u v huv hemp
      have hch : IsChain (· ≤ ·) (({u, v} : Finset L) : Set L) := by
        intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · exact Or.inl huv
        · exact Or.inr huv
        · exact absurd rfl hab
      obtain ⟨M, hsub, hM, hMm⟩ := h_max_ext {u, v} hch
      obtain ⟨c, hc⟩ := hmax M hM hMm
      rcases Finset.mem_inter.mp hc with ⟨hcM, hcC⟩
      have huM : u ∈ M := hsub (Finset.mem_insert_self _ _)
      have hvM : v ∈ M := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hcu : c ≤ u ∨ u ≤ c := by
        by_cases heq : c = u
        · exact Or.inl (le_of_eq heq)
        · exact hM hcM huM heq
      have hcv : c ≤ v ∨ v ≤ c := by
        by_cases heq : c = v
        · exact Or.inr (le_of_eq heq.symm)
        · exact hM hcM hvM heq
      have hc_not : ¬ (u ≤ c ∧ c ≤ v) := fun ⟨h1, h2⟩ => by
        have hmem : c ∈ C.filter (fun x => u ≤ x ∧ x ≤ v) := Finset.mem_filter.mpr ⟨hcC, h1, h2⟩
        rw [hemp] at hmem; simp at hmem
      rcases hcu with h1 | h1
      · by_cases hcu_eq : c = u
        · subst hcu_eq; exact absurd ⟨le_rfl, huv⟩ hc_not
        · exact Or.inl ⟨c, hcC, lt_of_le_of_ne h1 hcu_eq⟩
      · rcases hcv with h2 | h2
        · exact absurd ⟨h1, h2⟩ hc_not
        · by_cases hcv_eq : v = c
          · subst hcv_eq; exact absurd ⟨huv, le_rfl⟩ hc_not
          · exact Or.inr ⟨c, hcC, lt_of_le_of_ne h2 hcv_eq⟩
    let AboveC : Finset L := Finset.univ.filter (fun u : L => ∃ c ∈ C, c < u)
    let BelowC : Finset L := Finset.univ.filter (fun v : L => ∃ c ∈ C, v < c)
    have h_disj_AB : ∀ u v : L, u ≤ v → ¬ (u ∈ AboveC ∧ v ∈ BelowC) := by
      intro u v huv ⟨hu, hv⟩
      rcases Finset.mem_filter.mp hu with ⟨_, c₁, hc₁, hcu⟩
      rcases Finset.mem_filter.mp hv with ⟨_, c₂, hc₂, hvc⟩
      have hlt : c₁ < c₂ := lt_of_lt_of_le hcu (le_trans huv hvc.le)
      exact hanti hc₁ hc₂ hlt.ne hlt.le
    have h_above_empty : ∀ u v : L, u ∈ AboveC → u ≤ v → C.filter (fun c => u ≤ c ∧ c ≤ v) = ∅ := by
      intro u v hu _
      rcases Finset.mem_filter.mp hu with ⟨_, c₁, hc₁, hcu⟩
      ext c; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hcC huc _
      have hlt : c₁ < c := lt_of_lt_of_le hcu huc
      exact hanti hc₁ hcC hlt.ne hlt.le
    have h_below_empty : ∀ u v : L, v ∈ BelowC → u ≤ v → C.filter (fun c => u ≤ c ∧ c ≤ v) = ∅ := by
      intro u v hv _
      rcases Finset.mem_filter.mp hv with ⟨_, c₂, hc₂, hvc⟩
      ext c; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hcC _ hcv
      have hlt : c < c₂ := lt_of_le_of_lt hcv hvc
      exact hanti hcC hc₂ hlt.ne hlt.le
    have h_empty_eq : (∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
          if C.filter (fun c => u ≤ c ∧ c ≤ v) = ∅ then mobiusFn ⊥ u * mobiusFn v ⊤ else 0) =
        (∑ u ∈ AboveC, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v), mobiusFn ⊥ u * mobiusFn v ⊤) +
        (∑ v ∈ BelowC, ∑ u ∈ Finset.univ.filter (fun u : L => u ≤ v), mobiusFn ⊥ u * mobiusFn v ⊤) := by
      have h_rhs_swap : (∑ v ∈ BelowC, ∑ u ∈ Finset.univ.filter (fun u : L => u ≤ v),
            mobiusFn ⊥ u * mobiusFn v ⊤) =
          ∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
            if v ∈ BelowC then mobiusFn ⊥ u * mobiusFn v ⊤ else 0 := by
        have h1 : (∑ v ∈ BelowC, ∑ u ∈ Finset.univ.filter (fun u : L => u ≤ v),
              mobiusFn ⊥ u * mobiusFn v ⊤) =
            ∑ v : L, ∑ u : L, if v ∈ BelowC ∧ u ≤ v then mobiusFn ⊥ u * mobiusFn v ⊤ else 0 := by
          have hB : BelowC = Finset.univ.filter (· ∈ BelowC) := by ext; simp
          conv_lhs => rw [hB, Finset.sum_filter]
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases hv : v ∈ BelowC
          · rw [if_pos hv, Finset.sum_filter]
            refine Finset.sum_congr rfl fun u _ => by simp [hv]
          · rw [if_neg hv, Finset.sum_eq_zero]
            intro u _; rw [if_neg (fun h => hv h.1)]
        have h2 : (∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
              if v ∈ BelowC then mobiusFn ⊥ u * mobiusFn v ⊤ else 0) =
            ∑ u : L, ∑ v : L, if v ∈ BelowC ∧ u ≤ v then mobiusFn ⊥ u * mobiusFn v ⊤ else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases huv : u ≤ v
          · by_cases hvB : v ∈ BelowC
            · simp [huv, hvB]
            · simp [huv, hvB]
          · rw [if_neg huv, if_neg (fun h => huv h.2)]
        rw [h1, h2, Finset.sum_comm]
      have h_lhs_above : (∑ u ∈ AboveC, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
            mobiusFn ⊥ u * mobiusFn v ⊤) =
          ∑ u : L, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
            if u ∈ AboveC then mobiusFn ⊥ u * mobiusFn v ⊤ else 0 := by
        have hA : AboveC = Finset.univ.filter (· ∈ AboveC) := by ext; simp
        conv_lhs => rw [hA, Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        split_ifs with h
        · rfl
        · rw [Finset.sum_eq_zero]; intro _ _; rfl
      rw [h_lhs_above, h_rhs_swap, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v hv => ?_
      have huv : u ≤ v := (Finset.mem_filter.mp hv).2
      by_cases hu : u ∈ AboveC <;> by_cases hvB : v ∈ BelowC
      · exact absurd ⟨hu, hvB⟩ (h_disj_AB u v huv)
      · simp [hu, hvB, h_above_empty u v hu huv]
      · simp [hu, hvB, h_below_empty u v hvB huv]
      · have hne : C.filter (fun c => u ≤ c ∧ c ≤ v) ≠ ∅ := fun hemp => by
          rcases h_empty_split u v huv hemp with ⟨c, hc, hcu⟩ | ⟨c, hc, hvc⟩
          · exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, hcu⟩)
          · exact hvB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, hvc⟩)
        simp [hu, hvB, hne]
    have h_above_sum : ∑ u ∈ AboveC, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
        mobiusFn ⊥ u * mobiusFn v ⊤ = mobiusFn (⊥ : L) ⊤ := by
      have htop_mem : ⊤ ∈ AboveC := by
        obtain ⟨c, hc⟩ := hC_ne
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, lt_of_le_of_ne le_top ?_⟩
        intro hct; subst hct; exact htop hc
      have hterm : ∀ u ∈ AboveC, ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v),
          mobiusFn ⊥ u * mobiusFn v ⊤ = if u = ⊤ then mobiusFn (⊥ : L) ⊤ else 0 := by
        intro u _
        rw [← Finset.mul_sum]
        have hsum : ∑ v ∈ Finset.univ.filter (fun v : L => u ≤ v), mobiusFn v ⊤ =
            if u = ⊤ then 1 else 0 := by
          convert mobiusFn_sum_right (le_top : u ≤ ⊤) using 2
          ext v; simp [le_top]
        rw [hsum]
        split_ifs with hu
        · rw [hu, mul_one]
        · rw [mul_zero]
      rw [Finset.sum_congr rfl hterm]
      simp [htop_mem]
    have h_below_sum : ∑ v ∈ BelowC, ∑ u ∈ Finset.univ.filter (fun u : L => u ≤ v),
        mobiusFn ⊥ u * mobiusFn v ⊤ = mobiusFn (⊥ : L) ⊤ := by
      have hbot_mem : ⊥ ∈ BelowC := by
        obtain ⟨c, hc⟩ := hC_ne
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, lt_of_le_of_ne bot_le ?_⟩
        intro hbc; subst hbc; exact hbot hc
      have hterm : ∀ v ∈ BelowC, ∑ u ∈ Finset.univ.filter (fun u : L => u ≤ v),
          mobiusFn ⊥ u * mobiusFn v ⊤ = if v = ⊥ then mobiusFn (⊥ : L) ⊤ else 0 := by
        intro v _
        rw [← Finset.sum_mul]
        have hsum : ∑ u ∈ Finset.univ.filter (fun u : L => u ≤ v), mobiusFn ⊥ u =
            if ⊥ = v then 1 else 0 := by
          convert mobiusFn_sum_left (bot_le : (⊥ : L) ≤ v) using 2
          ext u; simp [bot_le]
        rw [hsum]
        by_cases hv : v = ⊥
        · rw [if_pos hv.symm, one_mul, if_pos hv, hv]
        · rw [if_neg (Ne.symm hv), zero_mul, if_neg hv]
      rw [Finset.sum_congr rfl hterm]
      simp [hbot_mem]
    rw [hsplit, h_empty_eq, h_above_sum, h_below_sum, h_all]
    ring
  rw [← h_double_rhs, h_double_lhs]

/-- **Boolean Lattice Specialization**: for `A ⊆ B` in `Finset (Fin n)`,
`mobiusFn A B = (-1 : ℤ) ^ (B \ A).card`. -/
theorem boolean_lattice_mobius {n : ℕ} {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    mobiusFn A B = (-1 : ℤ) ^ (B \ A).card := by
  refine mobiusFn_eq_of_sum_left (fun X Y => (-1 : ℤ) ^ (Y \ X).card) (fun X Y hXY => ?_) hAB
  have hbij : ∑ Z ∈ Finset.univ.filter (fun Z : Finset (Fin n) => X ≤ Z ∧ Z ≤ Y), (-1 : ℤ) ^ (Z \ X).card =
      ∑ T ∈ (Y \ X).powerset, (-1 : ℤ) ^ T.card := by
    refine Finset.sum_bij (fun Z _ => Z \ X) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro Z hZ
      rcases Finset.mem_filter.mp hZ with ⟨_, _, hZY⟩
      exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hZY Finset.Subset.rfl)
    · intro Z₁ h1 Z₂ h2 heq
      have hX1 : X ⊆ Z₁ := (Finset.mem_filter.mp h1).2.1
      have hX2 : X ⊆ Z₂ := (Finset.mem_filter.mp h2).2.1
      rw [← Finset.sdiff_union_of_subset hX1, ← Finset.sdiff_union_of_subset hX2, heq]
    · intro T hT
      have hTYX : T ⊆ Y \ X := Finset.mem_powerset.mp hT
      refine ⟨X ∪ T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left,
        Finset.union_subset hXY (hTYX.trans Finset.sdiff_subset)⟩, ?_⟩
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left h2,
        fun heT => ⟨Or.inr heT, (Finset.mem_sdiff.mp (hTYX heT)).2⟩⟩
  trans ∑ T ∈ (Y \ X).powerset, (-1 : ℤ) ^ T.card
  · convert hbij
  rw [sum_powerset_neg_one]
  by_cases h1 : Y \ X = ∅ <;> by_cases h2 : X = Y
  · subst h2; simp
  · exact absurd (le_antisymm hXY (Finset.sdiff_eq_empty_iff_subset.mp h1)) h2
  · subst h2; simp at h1
  · simp [h2]; exact fun h => h1 (Finset.sdiff_eq_empty_iff_subset.mpr h)

/-- **Divisor Lattice Specialization**: on any finite poset `P` order-isomorphic to divisors of
`N > 0`, `mobiusFn x y = ArithmeticFunction.moebius ((e y).1 / (e x).1)` whenever `x ≤ y`. -/
theorem divisor_lattice_mobius {N : ℕ} (hN : 0 < N) {P : Type*} [Fintype P] [PartialOrder P]
    (e : P ≃ {d : ℕ // d ∣ N}) (he : ∀ x y : P, x ≤ y ↔ (e x).1 ∣ (e y).1)
    {x y : P} (hxy : x ≤ y) :
    mobiusFn x y = ArithmeticFunction.moebius ((e y).1 / (e x).1) := by
  refine mobiusFn_eq_of_sum_left (fun u v => ArithmeticFunction.moebius ((e v).1 / (e u).1))
    (fun u v huv => ?_) hxy
  have huv_dvd : (e u).1 ∣ (e v).1 := (he u v).mp huv
  have hu_pos : 0 < (e u).1 := Nat.pos_of_dvd_of_pos (e u).2 hN
  have hv_pos : 0 < (e v).1 := Nat.pos_of_dvd_of_pos (e v).2 hN
  let q := (e v).1 / (e u).1
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hv_pos huv_dvd) hu_pos
  have hv_eq : (e v).1 = (e u).1 * q := (Nat.mul_div_cancel' huv_dvd).symm
  have hbij : ∑ z ∈ Finset.univ.filter (fun z : P => u ≤ z ∧ z ≤ v),
        ArithmeticFunction.moebius ((e z).1 / (e u).1) =
      ∑ d ∈ q.divisors, ArithmeticFunction.moebius d := by
    refine Finset.sum_bij (fun z _ => (e z).1 / (e u).1) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro z hz
      rcases Finset.mem_filter.mp hz with ⟨_, huz, hzv⟩
      have hu_z : (e u).1 ∣ (e z).1 := (he u z).mp huz
      have hz_v : (e z).1 ∣ (e v).1 := (he z v).mp hzv
      rw [hv_eq, ← Nat.mul_div_cancel' hu_z] at hz_v
      exact Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left hu_pos).mp hz_v, hq_pos.ne'⟩
    · intro z₁ h1 z₂ h2 heq
      have h1' : (e u).1 ∣ (e z₁).1 := (he u z₁).mp (Finset.mem_filter.mp h1).2.1
      have h2' : (e u).1 ∣ (e z₂).1 := (he u z₂).mp (Finset.mem_filter.mp h2).2.1
      apply e.injective
      apply Subtype.ext
      rw [← Nat.mul_div_cancel' h1', ← Nat.mul_div_cancel' h2', heq]
    · intro d hd
      rcases Nat.mem_divisors.mp hd with ⟨hdq, _⟩
      have hd_N : (e u).1 * d ∣ N :=
        dvd_trans (mul_dvd_mul_left _ hdq) (hv_eq ▸ (e v).2)
      refine ⟨e.symm ⟨(e u).1 * d, hd_N⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · rw [he]; simp [dvd_mul_right]
      · rw [he, hv_eq]; simp [mul_dvd_mul_left _ hdq]
      · simp [Nat.mul_div_cancel_left d hu_pos]
  rw [hbij]
  have hsum_m : ∑ d ∈ q.divisors, ArithmeticFunction.moebius d = if q = 1 then 1 else 0 := by
    have h1 : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) q =
        (1 : ArithmeticFunction ℤ) q := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h1
    rw [Nat.sum_divisorsAntidiagonal (f := fun d y => ArithmeticFunction.moebius d * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) y)] at h1
    have hq_div : ∑ d ∈ q.divisors, ArithmeticFunction.moebius d *
        (ArithmeticFunction.zeta : ArithmeticFunction ℤ) (q / d) =
        ∑ d ∈ q.divisors, ArithmeticFunction.moebius d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_dvd := (Nat.mem_divisors.mp hd).1
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hq_pos
      have hqd_ne : q / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hq_pos hd_dvd) hd_pos).ne'
      simp [hqd_ne]
    rw [hq_div] at h1
    exact h1
  rw [hsum_m]
  have hiff : u = v ↔ q = 1 := by
    constructor
    · rintro rfl; exact Nat.div_self hu_pos
    · intro hq1
      apply e.injective; apply Subtype.ext
      rw [hv_eq, hq1, mul_one]
  by_cases heq : u = v
  · rw [if_pos heq, if_pos (hiff.mp heq)]
  · rw [if_neg heq, if_neg (fun h => heq (hiff.mpr h))]

/-- Non-vacuity witness: for every `N > 0`, there exists a finite poset isomorphic to the divisor
lattice of `N`. -/
theorem exists_divisor_poset {N : ℕ} (hN : 0 < N) :
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (e : P ≃ {d : ℕ // d ∣ N}),
      ∀ x y : P, x ≤ y ↔ (e x).1 ∣ (e y).1 := by
  let instFintype : Fintype {d : ℕ // d ∣ N} :=
    Fintype.ofFinset (N.divisors) (fun d => Nat.mem_divisors.trans ⟨And.left, fun h => ⟨h, hN.ne'⟩⟩)
  let instPO : PartialOrder {d : ℕ // d ∣ N} :=
    { le := fun a b => a.1 ∣ b.1
      lt := fun a b => a.1 ∣ b.1 ∧ a.1 ≠ b.1
      le_refl := fun a => dvd_rfl
      le_trans := fun _ _ _ => dvd_trans
      lt_iff_le_not_ge := fun a b => ⟨fun ⟨h, hne⟩ => ⟨h, fun hba => hne (Nat.dvd_antisymm h hba)⟩,
        fun ⟨h, hna⟩ => ⟨h, fun heq => hna (heq ▸ dvd_rfl)⟩⟩
      le_antisymm := fun _ _ hab hba => Subtype.ext (Nat.dvd_antisymm hab hba) }
  exact ⟨{d : ℕ // d ∣ N}, instFintype, instPO, Equiv.refl _, fun _ _ => Iff.rfl⟩

end Mobius

end Arith4Ext.MatroidsPosets
