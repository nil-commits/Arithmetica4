import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# PPL 057: Sun's Disjoint Cosets Conjecture (Conjecture 4.2)

This file formalizes structural reductions and proved cases of Zhi-Wei Sun's Disjoint Cosets
Conjecture (2004):

> If `a_1 H_1, ..., a_k H_k` (`k ≥ 2`) are pairwise disjoint left cosets of finite-index subgroups
> of a group `G`, then `∃ i < j, k ≤ Nat.gcd (H i).index (H j).index`.

## Main verified theorems (0 `sorry`, pure Mathlib statements)
1. `ppl057_finite_reduction`: Reduces the conjecture from any group `G` to a finite quotient
   `Q = G ⧸ N`, preserving pairwise disjointness and subgroup indices.
2. `ppl057_density_bound`: `∑ i, (1 : ℚ) / (H i).index ≤ 1`.
3. `ppl057_pairwise_gcd_ge_two`: Every pair of disjoint left cosets satisfies
   `2 ≤ Nat.gcd (H i).index (H j).index`.
4. `ppl057_k_eq_two`: Full Sun Conjecture 4.2 for `k = 2` (arbitrary group `G`).
5. `ppl057_divisibility_chain`: Full Sun Conjecture 4.2 for all `k ≥ 2` when the indices are
   totally ordered by divisibility.
6. `ppl057_pgroup`: Full Sun Conjecture 4.2 for all `k ≥ 2` on any finite `p`-group (Sun 2004).
7. `ppl057_k_eq_three`: Full Sun Conjecture 4.2 for `k = 3` (arbitrary group `G`, Zhu 2008).
8. `ppl057_k_eq_four`: Full Sun Conjecture 4.2 for `k = 4` (arbitrary group `G`, Zhu 2008).
-/

namespace PPL057

section FiniteReduction

/-- Membership in the left coset `a H` written as `(fun y => a * y) '' (H : Set G)`. -/
private lemma mem_leftCoset_image {G : Type*} [Group G] (a : G) (H : Subgroup G) (x : G) :
    x ∈ (fun y => a * y) '' (H : Set G) ↔ a⁻¹ * x ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa using hh
  · intro hx
    exact ⟨a⁻¹ * x, hx, by simp⟩

/-- Every finite-index subgroup `H` contains a finite-index normal subgroup (kernel of left
multiplication on `G ⧸ H`). -/
private lemma exists_normal_le_finite {G : Type*} [Group G] (H : Subgroup G)
    [Finite (G ⧸ H)] :
    ∃ (K : Subgroup G), K.Normal ∧ K ≤ H ∧ Finite (G ⧸ K) := by
  let φ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  refine ⟨φ.ker, φ.normal_ker, ?_, ?_⟩
  · intro g hg
    have h1 : φ g ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      rw [MonoidHom.mem_ker] at hg
      simp [hg]
    have h2 : ((g * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      simpa [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply] using h1
    rw [mul_one, QuotientGroup.eq] at h2
    simpa using H.inv_mem h2
  · exact Finite.of_injective _ (QuotientGroup.kerLift_injective φ)

/-- **Finite-Group Reduction**: Any instance of Sun's Conjecture 4.2 in an arbitrary (possibly
infinite) group `G` descends to a finite quotient group `Q = G ⧸ N` preserving pairwise
disjointness and all subgroup indices. -/
theorem ppl057_finite_reduction
    {G : Type*} [Group G] {k : ℕ}
    (a : Fin k → G) (H : Fin k → Subgroup G)
    (hfin : ∀ i, Finite (G ⧸ H i))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    ∃ (N : Subgroup G) (_ : N.Normal),
      Finite (G ⧸ N) ∧
      let π := QuotientGroup.mk' N
      let a' : Fin k → G ⧸ N := fun i => π (a i)
      let H' : Fin k → Subgroup (G ⧸ N) := fun i => (H i).map π
      (∀ i, (H' i).index = (H i).index) ∧
      Pairwise fun i j =>
        Disjoint ((fun x => a' i * x) '' (H' i : Set (G ⧸ N)))
                 ((fun x => a' j * x) '' (H' j : Set (G ⧸ N))) := by
  classical
  choose K hKnorm hKle hKfin using fun i => @exists_normal_le_finite G _ (H i) (hfin i)
  let N : Subgroup G := ⨅ i : Fin k, K i
  have hN : N.Normal := Subgroup.normal_iInf_normal hKnorm
  have hN_le : ∀ i, N ≤ H i := fun i =>
    le_trans (iInf_le K i) (hKle i)
  have hfinN : Finite (G ⧸ N) := by
    let f : G ⧸ N → ∀ i : Fin k, G ⧸ K i :=
      fun q i => QuotientGroup.map N (K i) (MonoidHom.id G)
        (by simpa using iInf_le K i) q
    have hf : Function.Injective f := by
      intro q1 q2 hq
      induction q1 using QuotientGroup.induction_on with
      | H x =>
        induction q2 using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq, Subgroup.mem_iInf]
          intro i
          have hi := congr_fun hq i
          simpa [f, QuotientGroup.map_mk, QuotientGroup.eq] using hi
    exact Finite.of_injective f hf
  refine ⟨N, hN, hfinN, ?_, ?_⟩
  · intro i
    have hker : (QuotientGroup.mk' N).ker ≤ H i := by
      simpa [QuotientGroup.ker_mk'] using hN_le i
    exact Subgroup.index_map_eq (H i) (QuotientGroup.mk'_surjective N) hker
  · intro i j hij
    change Disjoint ((fun x => QuotientGroup.mk' N (a i) * x) ''
                      ((H i).map (QuotientGroup.mk' N) : Set (G ⧸ N)))
                    ((fun x => QuotientGroup.mk' N (a j) * x) ''
                      ((H j).map (QuotientGroup.mk' N) : Set (G ⧸ N)))
    rw [Set.disjoint_left]
    intro q hqi hqj
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [mem_leftCoset_image] at hqi hqj
    have hker_i : (QuotientGroup.mk' N).ker ≤ H i := by
      simpa [QuotientGroup.ker_mk'] using hN_le i
    have hker_j : (QuotientGroup.mk' N).ker ≤ H j := by
      simpa [QuotientGroup.ker_mk'] using hN_le j
    have hxi : (a i)⁻¹ * x ∈ H i := by
      rw [← map_inv, ← map_mul] at hqi
      have hcomap : (a i)⁻¹ * x ∈ ((H i).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := hqi
      rwa [Subgroup.comap_map_eq_self hker_i] at hcomap
    have hxj : (a j)⁻¹ * x ∈ H j := by
      rw [← map_inv, ← map_mul] at hqj
      have hcomap : (a j)⁻¹ * x ∈ ((H j).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := hqj
      rwa [Subgroup.comap_map_eq_self hker_j] at hcomap
    have hdisj_ij : Disjoint ((fun y => a i * y) '' (H i : Set G))
                             ((fun y => a j * y) '' (H j : Set G)) := hdisj hij
    rw [Set.disjoint_left] at hdisj_ij
    exact hdisj_ij ((mem_leftCoset_image (a i) (H i) x).mpr hxi)
                   ((mem_leftCoset_image (a j) (H j) x).mpr hxj)

end FiniteReduction

section FiniteGroupTools

open Classical

variable {G : Type*} [Group G] [Fintype G]

/-- Index of a subgroup in a finite group is positive. -/
private lemma index_pos_of_fintype (H : Subgroup G) : 0 < H.index := by
  have h := Subgroup.index_mul_card H
  have hG : 0 < Nat.card G := Nat.card_pos
  have hmul : 0 < H.index * Nat.card H := by rw [h]; exact hG
  exact Nat.pos_of_mul_pos_right hmul

/-- Cardinality of the left coset finset `a H` equals `Nat.card H`. -/
private lemma card_leftCoset_finset (a : G) (H : Subgroup G) :
    (Finset.univ.filter (fun x : G => a⁻¹ * x ∈ H)).card = Nat.card H := by
  rw [Nat.card_eq_fintype_card]
  refine Finset.card_bij
    (fun x hx => (⟨a⁻¹ * x, (Finset.mem_filter.mp hx).2⟩ : H)) ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro x1 _ x2 _ heq
    exact mul_left_cancel (congr_arg Subtype.val heq)
  · intro ⟨h, hh⟩ _
    exact ⟨a * h, by simp [hh], by ext; simp⟩

/-- In a finite group, pairwise disjoint left cosets satisfy `∑ |H_i| ≤ |G|`. -/
private lemma sum_card_le_card {k : ℕ} (a : Fin k → G) (H : Fin k → Subgroup G)
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    ∑ i : Fin k, Nat.card (H i) ≤ Nat.card G := by
  let S : Fin k → Finset G := fun i => Finset.univ.filter (fun x => (a i)⁻¹ * x ∈ H i)
  have hSdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin k)) S := by
    intro i _ j _ hij
    change Disjoint (S i) (S j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    have hd : Disjoint ((fun y => a i * y) '' (H i : Set G))
                       ((fun y => a j * y) '' (H j : Set G)) := hdisj hij
    rw [Set.disjoint_left] at hd
    exact hd ((mem_leftCoset_image (a i) (H i) x).mpr hxi)
             ((mem_leftCoset_image (a j) (H j) x).mpr hxj)
  have hcard : (Finset.univ.biUnion S).card = ∑ i : Fin k, (S i).card :=
    Finset.card_biUnion hSdisj
  have hle : (Finset.univ.biUnion S).card ≤ Fintype.card G :=
    Finset.card_le_univ _
  rw [hcard] at hle
  rw [Nat.card_eq_fintype_card]
  simpa [S, card_leftCoset_finset] using hle

/-- **Density Bound (Finite Group)**: `∑ i, (1 : ℚ) / (H i).index ≤ 1`. -/
private lemma density_bound_finite {k : ℕ} (a : Fin k → G) (H : Fin k → Subgroup G)
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    ∑ i : Fin k, (1 : ℚ) / ((H i).index : ℚ) ≤ 1 := by
  have hGpos : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos (α := G)
  have hsumQ : (∑ i : Fin k, (Nat.card (H i) : ℚ)) ≤ (Nat.card G : ℚ) := by
    exact_mod_cast sum_card_le_card a H hdisj
  have hterm : ∀ i : Fin k,
      (1 : ℚ) / ((H i).index : ℚ) = (Nat.card (H i) : ℚ) / (Nat.card G : ℚ) := by
    intro i
    have hind : ((H i).index : ℚ) * (Nat.card (H i) : ℚ) = (Nat.card G : ℚ) := by
      exact_mod_cast Subgroup.index_mul_card (H i)
    have hi_ne : ((H i).index : ℚ) ≠ 0 := by
      exact_mod_cast (index_pos_of_fintype (H i)).ne'
    rw [div_eq_div_iff hi_ne hGpos.ne', one_mul, mul_comm, hind]
  calc
    ∑ i : Fin k, (1 : ℚ) / ((H i).index : ℚ)
        = ∑ i : Fin k, (Nat.card (H i) : ℚ) / (Nat.card G : ℚ) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i : Fin k, (Nat.card (H i) : ℚ)) / (Nat.card G : ℚ) := by rw [Finset.sum_div]
    _ ≤ (Nat.card G : ℚ) / (Nat.card G : ℚ) := div_le_div_of_nonneg_right hsumQ hGpos.le
    _ = 1 := div_self hGpos.ne'

/-- The product set `H₁ H₂` as a `Finset G`. -/
private noncomputable def prodFinset (H₁ H₂ : Subgroup G) : Finset G :=
  Finset.univ.filter (fun x => ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, x = h₁ * h₂)

private lemma mem_prodFinset {H₁ H₂ : Subgroup G} {x : G} :
    x ∈ prodFinset H₁ H₂ ↔ ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, x = h₁ * h₂ := by
  simp [prodFinset]

/-- Product-set cardinality: `|H₁ H₂| * |H₁ ∩ H₂| = |H₁| * |H₂|`. -/
private lemma card_prodFinset_mul_inf (H₁ H₂ : Subgroup G) :
    (prodFinset H₁ H₂).card * Nat.card (H₁ ⊓ H₂ : Subgroup G) =
      Nat.card H₁ * Nat.card H₂ := by
  let f : (H₁ × H₂) → G := fun p => (p.1 : G) * (p.2 : G)
  have hf_mem : ∀ p : H₁ × H₂, f p ∈ prodFinset H₁ H₂ := fun p =>
    mem_prodFinset.mpr ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩
  have hfiber : ∀ x ∈ prodFinset H₁ H₂,
      (Finset.univ.filter (fun p : H₁ × H₂ => f p = x)).card =
        Nat.card (H₁ ⊓ H₂ : Subgroup G) := by
    intro x hx
    rcases mem_prodFinset.mp hx with ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    rw [Nat.card_eq_fintype_card]
    refine Finset.card_bij
      (fun p hp => (⟨(p.1 : G)⁻¹ * h₁, ?_⟩ : (H₁ ⊓ H₂ : Subgroup G))) ?_ ?_ ?_
    · have hp' : (p.1 : G) * (p.2 : G) = h₁ * h₂ := (Finset.mem_filter.mp hp).2
      have h1 : (p.1 : G)⁻¹ * h₁ ∈ H₁ := H₁.mul_mem (H₁.inv_mem p.1.2) hh₁
      have h2eq : (p.1 : G)⁻¹ * h₁ = (p.2 : G) * h₂⁻¹ := by
        calc (p.1 : G)⁻¹ * h₁
            = (p.1 : G)⁻¹ * ((h₁ * h₂) * h₂⁻¹) := by simp
          _ = (p.1 : G)⁻¹ * (((p.1 : G) * (p.2 : G)) * h₂⁻¹) := by rw [hp']
          _ = (p.2 : G) * h₂⁻¹ := by group
      exact ⟨h1, by rw [h2eq]; exact H₂.mul_mem p.2.2 (H₂.inv_mem hh₂)⟩
    · intro _ _; exact Finset.mem_univ _
    · intro p hp q hq heq
      have hp' : (p.1 : G) * (p.2 : G) = h₁ * h₂ := (Finset.mem_filter.mp hp).2
      have hq' : (q.1 : G) * (q.2 : G) = h₁ * h₂ := (Finset.mem_filter.mp hq).2
      have hval : (p.1 : G)⁻¹ * h₁ = (q.1 : G)⁻¹ * h₁ := congr_arg Subtype.val heq
      have hp1 : (p.1 : G) = (q.1 : G) := inv_injective (mul_right_cancel hval)
      have hp2 : (p.2 : G) = (q.2 : G) := mul_left_cancel (by rw [hp', ← hq', hp1])
      exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)
    · intro ⟨u, hu₁, hu₂⟩ _
      refine ⟨(⟨h₁ * u⁻¹, H₁.mul_mem hh₁ (H₁.inv_mem hu₁)⟩,
               ⟨u * h₂, H₂.mul_mem hu₂ hh₂⟩), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
        group
      · ext; simp only [mul_inv_rev, inv_inv]; group
  have hsum := Finset.card_eq_sum_card_fiberwise (f := f)
    (s := (Finset.univ : Finset (H₁ × H₂))) (t := prodFinset H₁ H₂) (fun p _ => hf_mem p)
  rw [Finset.card_univ, Fintype.card_prod] at hsum
  have hsum2 : ∑ x ∈ prodFinset H₁ H₂, (Finset.univ.filter (fun p : H₁ × H₂ => f p = x)).card =
      (prodFinset H₁ H₂).card * Nat.card (H₁ ⊓ H₂ : Subgroup G) := by
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
  rw [hsum2] at hsum
  simpa [Nat.card_eq_fintype_card] using hsum.symm

/-- Exact product-set cardinality identity in terms of indices:
`|H₁ H₂| * ([G:H₁] * [G:H₂]) = |G| * [G : H₁ ⊓ H₂]`. -/
private lemma card_prodFinset_mul_index (H₁ H₂ : Subgroup G) :
    (prodFinset H₁ H₂).card * (H₁.index * H₂.index) = Nat.card G * (H₁ ⊓ H₂).index := by
  have hPeq := card_prodFinset_mul_inf H₁ H₂
  have h1 := Subgroup.index_mul_card H₁
  have h2 := Subgroup.index_mul_card H₂
  have h12 := Subgroup.index_mul_card (H₁ ⊓ H₂)
  have hGpos : 0 < Nat.card (H₁ ⊓ H₂ : Subgroup G) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hGpos
  calc
    (prodFinset H₁ H₂).card * (H₁.index * H₂.index) * Nat.card (H₁ ⊓ H₂ : Subgroup G)
        = ((prodFinset H₁ H₂).card * Nat.card (H₁ ⊓ H₂ : Subgroup G)) *
            (H₁.index * H₂.index) := by ring
    _ = (Nat.card H₁ * Nat.card H₂) * (H₁.index * H₂.index) := by rw [hPeq]
    _ = (H₁.index * Nat.card H₁) * (H₂.index * Nat.card H₂) := by ring
    _ = Nat.card G * Nat.card G := by rw [h1, h2]
    _ = Nat.card G * ((H₁ ⊓ H₂).index * Nat.card (H₁ ⊓ H₂ : Subgroup G)) := by rw [h12]
    _ = Nat.card G * (H₁ ⊓ H₂).index * Nat.card (H₁ ⊓ H₂ : Subgroup G) := by ring

/-- Disjoint left cosets `a₁ H₁` and `a₂ H₂` imply `a₁⁻¹ * a₂ ∉ H₁ H₂`, so `|H₁ H₂| < |G|`. -/
private lemma not_mem_prodFinset_of_disjoint {a₁ a₂ : G} {H₁ H₂ : Subgroup G}
    (hdisj : Disjoint ((fun x => a₁ * x) '' (H₁ : Set G))
                      ((fun x => a₂ * x) '' (H₂ : Set G))) :
    a₁⁻¹ * a₂ ∉ prodFinset H₁ H₂ := by
  intro hmem
  rcases mem_prodFinset.mp hmem with ⟨h₁, hh₁, h₂, hh₂, heq⟩
  have hpt : a₁ * h₁ = a₂ * h₂⁻¹ := by
    calc a₁ * h₁
        = a₁ * ((h₁ * h₂) * h₂⁻¹) := by simp
      _ = a₁ * ((a₁⁻¹ * a₂) * h₂⁻¹) := by rw [← heq]
      _ = a₂ * h₂⁻¹ := by group
  rw [Set.disjoint_left] at hdisj
  exact hdisj ⟨h₁, hh₁, rfl⟩ ⟨h₂⁻¹, H₂.inv_mem hh₂, hpt.symm⟩

private lemma card_prodFinset_lt_of_disjoint (a₁ a₂ : G) (H₁ H₂ : Subgroup G)
    (hdisj : Disjoint ((fun x => a₁ * x) '' (H₁ : Set G))
                      ((fun x => a₂ * x) '' (H₂ : Set G))) :
    (prodFinset H₁ H₂).card < Nat.card G := by
  have hnotmem := not_mem_prodFinset_of_disjoint hdisj
  have hss : prodFinset H₁ H₂ ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨a₁⁻¹ * a₂, Finset.mem_univ _, hnotmem⟩
  rw [Nat.card_eq_fintype_card]
  simpa using Finset.card_lt_card hss

/-- Key divisibility and strict inequality for disjoint left cosets:
`lcm([G:H₁], [G:H₂]) ∣ [G : H₁ ⊓ H₂]` and `[G : H₁ ⊓ H₂] < [G:H₁] * [G:H₂]`. -/
private lemma index_inf_bounds_of_disjoint (a₁ a₂ : G) (H₁ H₂ : Subgroup G)
    (hdisj : Disjoint ((fun x => a₁ * x) '' (H₁ : Set G))
                      ((fun x => a₂ * x) '' (H₂ : Set G))) :
    Nat.lcm H₁.index H₂.index ∣ (H₁ ⊓ H₂).index ∧
    (H₁ ⊓ H₂).index < H₁.index * H₂.index := by
  constructor
  · exact Nat.lcm_dvd (Subgroup.index_dvd_of_le inf_le_left)
                      (Subgroup.index_dvd_of_le inf_le_right)
  · have hPlt := card_prodFinset_lt_of_disjoint a₁ a₂ H₁ H₂ hdisj
    have hkey := card_prodFinset_mul_index H₁ H₂
    have hlt : Nat.card G * (H₁ ⊓ H₂).index < Nat.card G * (H₁.index * H₂.index) := by
      rw [← hkey]
      exact Nat.mul_lt_mul_of_pos_right hPlt
        (Nat.mul_pos (index_pos_of_fintype H₁) (index_pos_of_fintype H₂))
    exact Nat.lt_of_mul_lt_mul_left hlt

/-- **Pairwise Non-Coprimality (Finite Group)**: Disjoint left cosets have `2 ≤ gcd([G:H₁], [G:H₂])`. -/
private lemma pairwise_gcd_ge_two_finite (a₁ a₂ : G) (H₁ H₂ : Subgroup G)
    (hdisj : Disjoint ((fun x => a₁ * x) '' (H₁ : Set G))
                      ((fun x => a₂ * x) '' (H₂ : Set G))) :
    2 ≤ Nat.gcd H₁.index H₂.index := by
  obtain ⟨hdvd, hlt⟩ := index_inf_bounds_of_disjoint a₁ a₂ H₁ H₂ hdisj
  have hinf_pos : 0 < (H₁ ⊓ H₂).index := index_pos_of_fintype (H₁ ⊓ H₂)
  have hlcm_le : Nat.lcm H₁.index H₂.index ≤ (H₁ ⊓ H₂).index := Nat.le_of_dvd hinf_pos hdvd
  have hlcm_lt : Nat.lcm H₁.index H₂.index < H₁.index * H₂.index := lt_of_le_of_lt hlcm_le hlt
  have hprod : Nat.gcd H₁.index H₂.index * Nat.lcm H₁.index H₂.index = H₁.index * H₂.index :=
    Nat.gcd_mul_lcm H₁.index H₂.index
  by_contra h
  push Not at h
  have hg_pos : 0 < Nat.gcd H₁.index H₂.index :=
    Nat.gcd_pos_of_pos_left _ (index_pos_of_fintype H₁)
  have hg1 : Nat.gcd H₁.index H₂.index = 1 := by omega
  rw [hg1, one_mul] at hprod
  omega

/-- Index of intersection of two subgroups is at most the product of their indices. -/
private lemma index_inf_le_mul (H₁ H₂ : Subgroup G) :
    (H₁ ⊓ H₂).index ≤ H₁.index * H₂.index := by
  have hkey := card_prodFinset_mul_index H₁ H₂
  have hPle : (prodFinset H₁ H₂).card ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
  have hle : Nat.card G * (H₁ ⊓ H₂).index ≤ Nat.card G * (H₁.index * H₂.index) := by
    rw [← hkey]
    exact Nat.mul_le_mul_right _ hPle
  exact Nat.le_of_mul_le_mul_left hle Nat.card_pos

/-- If two subgroups have coprime indices, their intersection has index equal to the product
of their indices, and their product equals the whole group `G`. -/
private lemma index_inf_eq_mul_of_coprime {H₁ H₂ : Subgroup G}
    (hcop : Nat.Coprime H₁.index H₂.index) :
    (H₁ ⊓ H₂).index = H₁.index * H₂.index := by
  have hdvd : H₁.index * H₂.index ∣ (H₁ ⊓ H₂).index :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.index_dvd_of_le inf_le_left)
                               (Subgroup.index_dvd_of_le inf_le_right)
  have hle1 : H₁.index * H₂.index ≤ (H₁ ⊓ H₂).index :=
    Nat.le_of_dvd (index_pos_of_fintype (H₁ ⊓ H₂)) hdvd
  exact le_antisymm (index_inf_le_mul H₁ H₂) hle1

private lemma prodFinset_eq_univ_of_coprime {H₁ H₂ : Subgroup G}
    (hcop : Nat.Coprime H₁.index H₂.index) :
    prodFinset H₁ H₂ = Finset.univ := by
  have hkey := card_prodFinset_mul_index H₁ H₂
  rw [index_inf_eq_mul_of_coprime hcop] at hkey
  have hpos : 0 < H₁.index * H₂.index :=
    Nat.mul_pos (index_pos_of_fintype H₁) (index_pos_of_fintype H₂)
  have hcard : (prodFinset H₁ H₂).card = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.eq_of_mul_eq_mul_right hpos hkey
  exact Finset.eq_univ_of_card _ hcard

omit [Fintype G] in
/-- If `K ≤ H`, then `[G : H] * [H : K] = [G : K]`. -/
private lemma index_mul_relIndex {K H : Subgroup G} (hKH : K ≤ H) :
    H.index * K.relIndex H = K.index := by
  have h := Subgroup.relIndex_mul_index hKH
  simpa [mul_comm] using h

/-- Relative index of an intersection in `H` is bounded by the product of relative indices
and divisible by their lcm. -/
private lemma relIndex_inf_le_mul (H K₁ K₂ : Subgroup G) :
    (K₁ ⊓ K₂).relIndex H ≤ K₁.relIndex H * K₂.relIndex H := by
  change ((K₁ ⊓ K₂).subgroupOf H).index ≤ (K₁.subgroupOf H).index * (K₂.subgroupOf H).index
  exact index_inf_le_mul (K₁.subgroupOf H) (K₂.subgroupOf H)

omit [Fintype G] in
private lemma relIndex_inf_lcm_dvd (H K₁ K₂ : Subgroup G) :
    Nat.lcm (K₁.relIndex H) (K₂.relIndex H) ∣ (K₁ ⊓ K₂).relIndex H := by
  change Nat.lcm (K₁.subgroupOf H).index (K₂.subgroupOf H).index ∣
    ((K₁.subgroupOf H) ⊓ (K₂.subgroupOf H)).index
  exact Nat.lcm_dvd (Subgroup.index_dvd_of_le inf_le_left)
                    (Subgroup.index_dvd_of_le inf_le_right)

/-- Coprime relative indices inside a subgroup `H` multiply in `H`, hence their product fills `H`. -/
private lemma relIndex_inf_eq_mul_of_coprime {H K₁ K₂ : Subgroup G}
    (hcop : Nat.Coprime (K₁.relIndex H) (K₂.relIndex H)) :
    (K₁ ⊓ K₂).relIndex H = K₁.relIndex H * K₂.relIndex H := by
  change ((K₁.subgroupOf H) ⊓ (K₂.subgroupOf H)).index =
    (K₁.subgroupOf H).index * (K₂.subgroupOf H).index
  exact index_inf_eq_mul_of_coprime hcop

private lemma mem_prod_of_coprime_relIndex {H K₁ K₂ : Subgroup G}
    (hcop : Nat.Coprime (K₁.relIndex H) (K₂.relIndex H))
    {x : G} (hx : x ∈ H) :
    ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, x = k₁ * k₂ := by
  have huniv : prodFinset (K₁.subgroupOf H) (K₂.subgroupOf H) = Finset.univ :=
    prodFinset_eq_univ_of_coprime hcop
  have hmem : (⟨x, hx⟩ : H) ∈ prodFinset (K₁.subgroupOf H) (K₂.subgroupOf H) := by
    rw [huniv]; exact Finset.mem_univ _
  rcases mem_prodFinset.mp hmem with ⟨⟨u, hu⟩, hu1, ⟨v, hv⟩, hv2, heq⟩
  exact ⟨u, hu1, v, hv2, congr_arg Subtype.val heq⟩

/-- If a finset `S` is right-invariant under `H₁` and `H₂`, then it is right-invariant under
`M = H₁ ⊔ H₂`, and `Nat.card M ∣ S.card`. -/
private lemma right_invariant_sup_dvd {S : Finset G} {H₁ H₂ : Subgroup G}
    (hinv1 : ∀ x ∈ S, ∀ h ∈ H₁, x * h ∈ S)
    (hinv2 : ∀ x ∈ S, ∀ h ∈ H₂, x * h ∈ S) :
    (∀ x ∈ S, ∀ m ∈ (H₁ ⊔ H₂ : Subgroup G), x * m ∈ S) ∧
    Nat.card (H₁ ⊔ H₂ : Subgroup G) ∣ S.card := by
  let M : Subgroup G := H₁ ⊔ H₂
  have hinvM : ∀ m ∈ M, ∀ x ∈ S, x * m ∈ S := by
    intro m hm
    have hcl : m ∈ Subgroup.closure ((H₁ : Set G) ∪ (H₂ : Set G)) := by
      rwa [← Subgroup.sup_eq_closure]
    refine Subgroup.closure_induction
      (p := fun m _ => ∀ x ∈ S, x * m ∈ S) ?_ ?_ ?_ ?_ hcl
    · rintro y (hy | hy) x hx
      · exact hinv1 x hx y hy
      · exact hinv2 x hx y hy
    · intro x hx; simpa using hx
    · intro u v _ _ hu hv x hx
      rw [← mul_assoc]
      exact hv (x * u) (hu x hx)
    · intro u _ ih
      have hbij : Finset.image (fun x => x * u) S = S := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          exact ih x hx
        · rw [Finset.card_image_of_injective S (mul_left_injective u)]
      intro x hx
      rw [← hbij] at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      simpa using hy
  refine ⟨fun x hx m hm => hinvM m hm x hx, ?_⟩
  let π : G → G ⧸ M := fun x => (x : G ⧸ M)
  let Q : Finset (G ⧸ M) := S.image π
  have hfiber : ∀ q ∈ Q, (S.filter (fun x => π x = q)).card = Nat.card M := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨a, ha, rfl⟩
    have hfilt : S.filter (fun x => π x = π a) =
        Finset.univ.filter (fun x => a⁻¹ * x ∈ M) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, π, QuotientGroup.eq]
      constructor
      · rintro ⟨_, hxa⟩
        simpa [mul_inv_rev] using M.inv_mem hxa
      · intro hax
        refine ⟨?_, ?_⟩
        · have hx' : x = a * (a⁻¹ * x) := by group
          rw [hx']
          exact hinvM (a⁻¹ * x) hax a ha
        · simpa [mul_inv_rev] using M.inv_mem hax
    rw [hfilt]
    exact card_leftCoset_finset a M
  have hsum := Finset.card_eq_sum_card_fiberwise (f := π) (s := S) (t := Q)
    (fun x hx => Finset.mem_image_of_mem π hx)
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul] at hsum
  exact ⟨Q.card, by rw [hsum, mul_comm]⟩

/-- Conjugate-inverse duality for left cosets:
replacing `(a_i, H_i)` by `(a_i⁻¹, a_i H_i a_i⁻¹)` preserves indices and pairwise disjointness,
and satisfies `|H_i H_j| + |H'_i H'_j| ≤ |G|` for all `i ≠ j`. -/
private lemma conjugate_inverse_dual {k : ℕ} (a : Fin k → G) (H : Fin k → Subgroup G)
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    let a' : Fin k → G := fun i => (a i)⁻¹
    let H' : Fin k → Subgroup G := fun i => (H i).map (MulAut.conj (a i)).toMonoidHom
    (∀ i, (H' i).index = (H i).index) ∧
    (Pairwise fun i j =>
      Disjoint ((fun x => a' i * x) '' (H' i : Set G))
               ((fun x => a' j * x) '' (H' j : Set G))) ∧
    (∀ i j, i ≠ j →
      (prodFinset (H i) (H j)).card + (prodFinset (H' i) (H' j)).card ≤ Nat.card G) := by
  intro a' H'
  have hmemH' : ∀ i x, x ∈ H' i ↔ (a i)⁻¹ * x * a i ∈ H i := by
    intro i x
    simp only [H', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨h, hh, rfl⟩; simpa [mul_assoc] using hh
    · intro hx; exact ⟨(a i)⁻¹ * x * a i, hx, by group⟩
  have hcoset : ∀ i x, x ∈ (fun y => a' i * y) '' (H' i : Set G) ↔
      x⁻¹ ∈ (fun y => a i * y) '' (H i : Set G) := by
    intro i x
    rw [mem_leftCoset_image, mem_leftCoset_image, hmemH']
    simp only [a', inv_inv]
    constructor
    · intro hx
      have hinv := (H i).inv_mem hx
      simpa [mul_inv_rev, mul_assoc] using hinv
    · intro hx
      have hinv := (H i).inv_mem hx
      simpa [mul_inv_rev, mul_assoc] using hinv
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Subgroup.index_map_equiv (H i) (MulAut.conj (a i))
  · intro i j hij
    change Disjoint ((fun y => a' i * y) '' (H' i : Set G))
                    ((fun y => a' j * y) '' (H' j : Set G))
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hd : Disjoint ((fun y => a i * y) '' (H i : Set G))
                       ((fun y => a j * y) '' (H j : Set G)) := hdisj hij
    rw [Set.disjoint_left] at hd
    exact hd ((hcoset i x).mp hxi) ((hcoset j x).mp hxj)
  · intro i j hij
    let f : G → G := fun x => (a i)⁻¹ * x * a j
    have hfinj : Function.Injective f := fun x y hxy =>
      mul_left_cancel (mul_right_cancel hxy)
    let Q : Finset G := (prodFinset (H' i) (H' j)).image f
    have hQcard : Q.card = (prodFinset (H' i) (H' j)).card :=
      Finset.card_image_of_injective _ hfinj
    have hdisjPQ : Disjoint (prodFinset (H i) (H j)) Q := by
      rw [Finset.disjoint_left]
      intro y hyP hyQ
      rcases mem_prodFinset.mp hyP with ⟨h1, hh1, h2, hh2, hy1⟩
      rcases Finset.mem_image.mp hyQ with ⟨x, hx, hy2⟩
      rcases mem_prodFinset.mp hx with ⟨u1, hu1, u2, hu2, rfl⟩
      rw [hmemH'] at hu1 hu2
      have hbad : (a i)⁻¹ * a j ∈ prodFinset (H i) (H j) := by
        refine mem_prodFinset.mpr ⟨((a i)⁻¹ * u1 * a i)⁻¹ * h1,
          (H i).mul_mem ((H i).inv_mem hu1) hh1,
          h2 * ((a j)⁻¹ * u2 * a j)⁻¹,
          (H j).mul_mem hh2 ((H j).inv_mem hu2), ?_⟩
        have hEq : h1 * h2 = (a i)⁻¹ * (u1 * u2) * a j := by
          rw [← hy1, ← hy2]
        calc (a i)⁻¹ * a j
            = ((a i)⁻¹ * u1 * a i)⁻¹ * ((a i)⁻¹ * (u1 * u2) * a j) *
                ((a j)⁻¹ * u2 * a j)⁻¹ := by group
          _ = ((a i)⁻¹ * u1 * a i)⁻¹ * (h1 * h2) * ((a j)⁻¹ * u2 * a j)⁻¹ := by rw [← hEq]
          _ = (((a i)⁻¹ * u1 * a i)⁻¹ * h1) * (h2 * ((a j)⁻¹ * u2 * a j)⁻¹) := by group
      exact not_mem_prodFinset_of_disjoint (hdisj hij) hbad
    have hunion : (prodFinset (H i) (H j) ∪ Q).card ≤ Fintype.card G :=
      Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisjPQ, hQcard, ← Nat.card_eq_fintype_card] at hunion
    exact hunion

/-- Number of distinct left cosets of `M` met by `a H` equals `(M ⊓ H).relIndex H`. -/
private lemma card_cosets_met_eq_relIndex (M H : Subgroup G) (a : G) :
    (Finset.univ.image (fun h : H => ((a * (h : G) : G) : G ⧸ M))).card =
      (M ⊓ H).relIndex H := by
  let f : H → G ⧸ M := fun h => ((a * (h : G) : G) : G ⧸ M)
  let Q : Finset (G ⧸ M) := Finset.univ.image f
  have hfiber : ∀ q ∈ Q, (Finset.univ.filter (fun h : H => f h = q)).card =
      Nat.card ((M ⊓ H).subgroupOf H) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨h₀, _, rfl⟩
    have hfilt : Finset.univ.filter (fun h : H => f h = f h₀) =
        Finset.univ.filter (fun h : H => h₀⁻¹ * h ∈ (M ⊓ H).subgroupOf H) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hmul
        have h1 : (h₀ : G)⁻¹ * (h : G) ∈ M := by
          have := M.inv_mem hmul
          simpa [mul_inv_rev, mul_assoc] using this
        exact ⟨h1, H.mul_mem (H.inv_mem h₀.2) h.2⟩
      · rintro ⟨hm, _⟩
        have h1 : (a * (h : G))⁻¹ * (a * (h₀ : G)) = ((h₀ : G)⁻¹ * (h : G))⁻¹ := by group
        rw [h1]
        exact M.inv_mem hm
    rw [hfilt]
    exact card_leftCoset_finset h₀ ((M ⊓ H).subgroupOf H)
  have hsum := Finset.card_eq_sum_card_fiberwise (f := f) (s := (Finset.univ : Finset H))
    (t := Q) (fun h _ => Finset.mem_image_of_mem f (Finset.mem_univ h))
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, ← Nat.card_eq_fintype_card] at hsum
  have hind : ((M ⊓ H).subgroupOf H).index * Nat.card ((M ⊓ H).subgroupOf H) = Nat.card H :=
    Subgroup.index_mul_card ((M ⊓ H).subgroupOf H)
  have hpos : 0 < Nat.card ((M ⊓ H).subgroupOf H) := Nat.card_pos
  have heq : Q.card * Nat.card ((M ⊓ H).subgroupOf H) =
      ((M ⊓ H).subgroupOf H).index * Nat.card ((M ⊓ H).subgroupOf H) := by
    rw [← hsum, hind]
  exact Nat.eq_of_mul_eq_mul_right hpos heq

/-- If `a₂ H₂` meets `a₁ M` (where `H₁ ≤ M`) and `[M : H₁]` is coprime to `[M : M ⊓ H₂]`,
then `a₁ H₁` and `a₂ H₂` MUST intersect! -/
private lemma not_disjoint_of_meet_coset_coprime {M H₁ H₂ : Subgroup G} {a₁ a₂ : G}
    (_h1M : H₁ ≤ M)
    (hcop : Nat.Coprime (H₁.relIndex M) ((M ⊓ H₂).relIndex M))
    (hmeet : ∃ h₂ ∈ H₂, ((a₂ * h₂ : G) : G ⧸ M) = ((a₁ : G) : G ⧸ M)) :
    ¬ Disjoint ((fun x => a₁ * x) '' (H₁ : Set G))
               ((fun x => a₂ * x) '' (H₂ : Set G)) := by
  rcases hmeet with ⟨h₂, hh₂, hq⟩
  rw [QuotientGroup.eq] at hq
  have hmemM : a₁⁻¹ * (a₂ * h₂) ∈ M := by
    have := M.inv_mem hq
    simpa [mul_inv_rev, mul_assoc] using this
  obtain ⟨h₁, hh₁, u, hu, heq⟩ := mem_prod_of_coprime_relIndex hcop hmemM
  intro hdisj
  rw [Set.disjoint_left] at hdisj
  have hpt : a₁ * h₁ = a₂ * (h₂ * u⁻¹) := by
    calc a₁ * h₁
        = a₁ * ((h₁ * u) * u⁻¹) := by simp
      _ = a₁ * ((a₁⁻¹ * (a₂ * h₂)) * u⁻¹) := by rw [← heq]
      _ = a₂ * (h₂ * u⁻¹) := by group
  exact hdisj ⟨h₁, hh₁, rfl⟩ ⟨h₂ * u⁻¹, H₂.mul_mem hh₂ (H₂.inv_mem hu.2), hpt.symm⟩

/-- Key `k = 3` impossibility lemma (finite group): three pairwise disjoint left cosets cannot
all have pairwise index gcd equal to `2`. -/
private lemma no_three_pairwise_gcd_two
    (a : Fin 3 → G) (H : Fin 3 → Subgroup G)
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G)))
    (hgcd : ∀ i j : Fin 3, i < j → Nat.gcd (H i).index (H j).index = 2) : False := by
  have hdvd2 : ∀ i : Fin 3, 2 ∣ (H i).index := by
    intro i
    fin_cases i
    · rw [← hgcd 0 1 (by decide)]; exact Nat.gcd_dvd_left _ _
    · rw [← hgcd 0 1 (by decide)]; exact Nat.gcd_dvd_right _ _
    · rw [← hgcd 0 2 (by decide)]; exact Nat.gcd_dvd_right _ _
  choose e he using hdvd2
  have he_pos : ∀ i : Fin 3, 0 < e i := fun i => by
    have hp := index_pos_of_fintype (H i); rw [he i] at hp; omega
  have he_cop : ∀ i j : Fin 3, i ≠ j → Nat.Coprime (e i) (e j) := by
    intro i j hij
    have hg : Nat.gcd (H i).index (H j).index = 2 := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact hgcd i j hlt
      · rw [Nat.gcd_comm]; exact hgcd j i hgt
    rw [he i, he j, Nat.gcd_mul_left] at hg
    have h1 : Nat.gcd (e i) (e j) = 1 := by omega
    exact h1
  have hinf2 : ∀ i j : Fin 3, i ≠ j → (H i ⊓ H j).index = 2 * e i * e j := by
    intro i j hij
    obtain ⟨hdvd, hlt⟩ := index_inf_bounds_of_disjoint (a i) (a j) (H i) (H j) (hdisj hij)
    have hg : Nat.gcd (H i).index (H j).index = 2 := by
      rcases lt_or_gt_of_ne hij with hlt' | hgt'
      · exact hgcd i j hlt'
      · rw [Nat.gcd_comm]; exact hgcd j i hgt'
    have hlcm : Nat.lcm (H i).index (H j).index = 2 * e i * e j := by
      have hp := Nat.gcd_mul_lcm (H i).index (H j).index
      rw [hg] at hp
      rw [he i, he j] at hp
      have hp' : 2 * Nat.lcm (H i).index (H j).index = 2 * (2 * e i * e j) := by
        rw [he i, he j]; linarith
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hp'
    rw [hlcm] at hdvd
    rw [he i, he j] at hlt
    rcases hdvd with ⟨m, hm⟩
    have hm_pos : 0 < m := by
      have hp := index_pos_of_fintype (H i ⊓ H j); rw [hm] at hp
      exact Nat.pos_of_mul_pos_left hp
    have hm1 : m = 1 := by
      have h1 : 2 * e i * e j * m < 2 * e i * e j * 2 := by
        calc 2 * e i * e j * m = (H i ⊓ H j).index := hm.symm
          _ < 2 * e i * (2 * e j) := hlt
          _ = 2 * e i * e j * 2 := by ring
      have h2 : m < 2 := Nat.lt_of_mul_lt_mul_left h1
      omega
    rw [hm, hm1, mul_one]
  have hprod_card : ∀ i j : Fin 3, i ≠ j → (prodFinset (H i) (H j)).card * 2 = Nat.card G := by
    intro i j hij
    have hkey := card_prodFinset_mul_index (H i) (H j)
    rw [hinf2 i j hij, he i, he j] at hkey
    have hpos : 0 < 2 * e i * e j := Nat.mul_pos (Nat.mul_pos (by decide) (he_pos i)) (he_pos j)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      (prodFinset (H i) (H j)).card * 2 * (2 * e i * e j)
          = (prodFinset (H i) (H j)).card * (2 * e i * (2 * e j)) := by ring
      _ = Nat.card G * (2 * e i * e j) := hkey
  have hrel01 : (H 0 ⊓ H 1).relIndex (H 0) = e 1 := by
    have h := index_mul_relIndex (inf_le_left : H 0 ⊓ H 1 ≤ H 0)
    rw [hinf2 0 1 (by decide), he 0] at h
    have hpos : 0 < 2 * e 0 := Nat.mul_pos (by decide) (he_pos 0)
    apply Nat.eq_of_mul_eq_mul_left hpos
    linarith
  have hrel02 : (H 0 ⊓ H 2).relIndex (H 0) = e 2 := by
    have h := index_mul_relIndex (inf_le_left : H 0 ⊓ H 2 ≤ H 0)
    rw [hinf2 0 2 (by decide), he 0] at h
    have hpos : 0 < 2 * e 0 := Nat.mul_pos (by decide) (he_pos 0)
    apply Nat.eq_of_mul_eq_mul_left hpos
    linarith
  have hinf012 : (H 0 ⊓ (H 1 ⊓ H 2)).index = 2 * e 0 * e 1 * e 2 := by
    have heq_sub : H 0 ⊓ (H 1 ⊓ H 2) = (H 0 ⊓ H 1) ⊓ (H 0 ⊓ H 2) := by
      ext x; simp only [Subgroup.mem_inf]; tauto
    rw [heq_sub, ← index_mul_relIndex (le_trans inf_le_left inf_le_left :
        (H 0 ⊓ H 1) ⊓ (H 0 ⊓ H 2) ≤ H 0)]
    rw [relIndex_inf_eq_mul_of_coprime (by rw [hrel01, hrel02]; exact he_cop 1 2 (by decide))]
    rw [hrel01, hrel02, he 0]
    ring
  have hcard0_12 : (prodFinset (H 0) (H 1 ⊓ H 2)).card * 2 = Nat.card G := by
    have hkey := card_prodFinset_mul_index (H 0) (H 1 ⊓ H 2)
    rw [hinf012, he 0, hinf2 1 2 (by decide)] at hkey
    have hpos : 0 < 2 * e 0 * e 1 * e 2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (he_pos 0)) (he_pos 1)) (he_pos 2)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      (prodFinset (H 0) (H 1 ⊓ H 2)).card * 2 * (2 * e 0 * e 1 * e 2)
          = (prodFinset (H 0) (H 1 ⊓ H 2)).card * (2 * e 0 * (2 * e 1 * e 2)) := by ring
      _ = Nat.card G * (2 * e 0 * e 1 * e 2) := hkey
  have hsub01 : prodFinset (H 0) (H 1 ⊓ H 2) ⊆ prodFinset (H 0) (H 1) := by
    intro x hx
    rcases mem_prodFinset.mp hx with ⟨h0, hh0, h12, ⟨hh1, _⟩, rfl⟩
    exact mem_prodFinset.mpr ⟨h0, hh0, h12, hh1, rfl⟩
  have hsub02 : prodFinset (H 0) (H 1 ⊓ H 2) ⊆ prodFinset (H 0) (H 2) := by
    intro x hx
    rcases mem_prodFinset.mp hx with ⟨h0, hh0, h12, ⟨_, hh2⟩, rfl⟩
    exact mem_prodFinset.mpr ⟨h0, hh0, h12, hh2, rfl⟩
  have heq01 : prodFinset (H 0) (H 1 ⊓ H 2) = prodFinset (H 0) (H 1) :=
    Finset.eq_of_subset_of_card_le hsub01 (by have h1 := hprod_card 0 1 (by decide); omega)
  have heq02 : prodFinset (H 0) (H 1 ⊓ H 2) = prodFinset (H 0) (H 2) :=
    Finset.eq_of_subset_of_card_le hsub02 (by have h2 := hprod_card 0 2 (by decide); omega)
  have hS_eq : prodFinset (H 0) (H 1) = prodFinset (H 0) (H 2) := heq01.symm.trans heq02
  let M : Subgroup G := H 1 ⊔ H 2
  have hinvM := right_invariant_sup_dvd (S := prodFinset (H 0) (H 1)) (H₁ := H 1) (H₂ := H 2)
    (fun x hx h hh => by
      rcases mem_prodFinset.mp hx with ⟨h0, hh0, h1, hh1, rfl⟩
      exact mem_prodFinset.mpr ⟨h0, hh0, h1 * h, (H 1).mul_mem hh1 hh, by group⟩)
    (fun x hx h hh => by
      rw [hS_eq] at hx ⊢
      rcases mem_prodFinset.mp hx with ⟨h0, hh0, h2, hh2, rfl⟩
      exact mem_prodFinset.mpr ⟨h0, hh0, h2 * h, (H 2).mul_mem hh2 hh, by group⟩)
  have h1S : (1 : G) ∈ prodFinset (H 0) (H 1) :=
    mem_prodFinset.mpr ⟨1, (H 0).one_mem, 1, (H 1).one_mem, by simp⟩
  have hM_sub_S : ∀ m ∈ M, m ∈ prodFinset (H 0) (H 1) := fun m hm => by
    simpa using hinvM.1 1 h1S m hm
  have h12_sub_M : ∀ x ∈ prodFinset (H 1) (H 2), x ∈ M := by
    intro x hx
    rcases mem_prodFinset.mp hx with ⟨h1, hh1, h2, hh2, rfl⟩
    exact M.mul_mem ((le_sup_left : H 1 ≤ M) hh1) ((le_sup_right : H 2 ≤ M) hh2)
  have hM_card_filt : (Finset.univ.filter (fun x : G => x ∈ M)).card = Nat.card M := by
    simpa using card_leftCoset_finset (1 : G) M
  have hM_card_le : Nat.card M ≤ (prodFinset (H 0) (H 1)).card := by
    rw [← hM_card_filt]
    exact Finset.card_le_card (fun x hx => hM_sub_S x (Finset.mem_filter.mp hx).2)
  have hM_card_ge : (prodFinset (H 1) (H 2)).card ≤ Nat.card M := by
    rw [← hM_card_filt]
    exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12_sub_M x hx⟩)
  have hM_eq_card : Nat.card M = (prodFinset (H 0) (H 1)).card := by
    have h01 := hprod_card 0 1 (by decide)
    have h12 := hprod_card 1 2 (by decide)
    omega
  have hM_index : M.index = 2 := by
    have hm := Subgroup.index_mul_card M
    have h01 := hprod_card 0 1 (by decide)
    rw [hM_eq_card] at hm
    have hpos : 0 < (prodFinset (H 0) (H 1)).card := Finset.card_pos.mpr ⟨1, h1S⟩
    apply Nat.eq_of_mul_eq_mul_right hpos
    linarith
  have hM_eq_S : ∀ x, x ∈ M ↔ x ∈ prodFinset (H 0) (H 1) := by
    have hfilt : Finset.univ.filter (fun x : G => x ∈ M) = prodFinset (H 0) (H 1) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; exact hM_sub_S x (Finset.mem_filter.mp hx).2
      · rw [hM_card_filt, hM_eq_card]
    intro x
    simpa using Finset.ext_iff.mp hfilt x
  have hM_eq_12 : ∀ x, x ∈ prodFinset (H 1) (H 2) ↔ x ∈ M := by
    have hfilt : prodFinset (H 1) (H 2) = Finset.univ.filter (fun x : G => x ∈ M) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12_sub_M x hx⟩
      · have h01 := hprod_card 0 1 (by decide)
        have h12 := hprod_card 1 2 (by decide)
        rw [hM_card_filt, hM_eq_card]; omega
    intro x
    simpa using Finset.ext_iff.mp hfilt x
  have hne01 : (a 0 : G ⧸ M) ≠ (a 1 : G ⧸ M) := by
    intro heq
    rw [QuotientGroup.eq] at heq
    exact not_mem_prodFinset_of_disjoint (hdisj (by decide : (0 : Fin 3) ≠ 1))
      ((hM_eq_S _).mp heq)
  have hne02 : (a 0 : G ⧸ M) ≠ (a 2 : G ⧸ M) := by
    intro heq
    rw [QuotientGroup.eq] at heq
    exact not_mem_prodFinset_of_disjoint (hdisj (by decide : (0 : Fin 3) ≠ 2))
      (by rw [← hS_eq]; exact (hM_eq_S _).mp heq)
  have hne12 : (a 1 : G ⧸ M) ≠ (a 2 : G ⧸ M) := by
    intro heq
    rw [QuotientGroup.eq] at heq
    exact not_mem_prodFinset_of_disjoint (hdisj (by decide : (1 : Fin 3) ≠ 2))
      ((hM_eq_12 _).mpr heq)
  have hcard_q : Fintype.card (G ⧸ M) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hM_index]
  have hinj : Function.Injective (fun i : Fin 3 => (a i : G ⧸ M)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  have h3le2 : Fintype.card (Fin 3) ≤ Fintype.card (G ⧸ M) :=
    Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, hcard_q] at h3le2
  omega

/-- **Core Lemma for `k = 4`**: If `H 0, H 1, H 2` all lie inside a common index-3 subgroup `M`,
with `[G : H i] = 3 * e i`, `e_i` pairwise coprime and `e 0, e 1, e 2` odd, then `a_0 H_0, ..., a_3 H_3`
cannot be pairwise disjoint. -/
private lemma k4_core_index3_subgroup
    (a : Fin 4 → G) (H : Fin 4 → Subgroup G) (e : Fin 4 → ℕ)
    (he : ∀ i, (H i).index = 3 * e i)
    (he_cop : ∀ i j, i ≠ j → Nat.Coprime (e i) (e j))
    (he_odd : Odd (e 0) ∧ Odd (e 1) ∧ Odd (e 2))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G)))
    (M : Subgroup G) (hM_idx : M.index = 3)
    (h0M : H 0 ≤ M) (h1M : H 1 ≤ M) (h2M : H 2 ≤ M) : False := by
  have hrel : ∀ i : Fin 3, (H i.castSucc).relIndex M = e i.castSucc := by
    intro i
    have hle : H i.castSucc ≤ M := by fin_cases i <;> assumption
    have hm := index_mul_relIndex hle
    rw [hM_idx, he i.castSucc] at hm
    omega
  -- a 0 M, a 1 M, a 2 M are 3 pairwise distinct left cosets of M, hence cover all of G ⧸ M
  have hne : ∀ i j : Fin 3, i ≠ j → (a i.castSucc : G ⧸ M) ≠ (a j.castSucc : G ⧸ M) := by
    intro i j hij heq
    have hle_i : H i.castSucc ≤ M := by fin_cases i <;> assumption
    have hle_j : H j.castSucc ≤ M := by fin_cases j <;> assumption
    have hcop_ij : Nat.Coprime ((H i.castSucc).relIndex M) ((H j.castSucc).relIndex M) := by
      rw [hrel i, hrel j]
      exact he_cop i.castSucc j.castSucc (by simpa using hij)
    rw [QuotientGroup.eq] at heq
    obtain ⟨h1, hh1, h2, hh2, hmul⟩ := mem_prod_of_coprime_relIndex hcop_ij heq
    exact not_mem_prodFinset_of_disjoint (hdisj (by simpa using hij))
      (mem_prodFinset.mpr ⟨h1, hh1, h2, hh2, hmul⟩)
  have hcard_q : Fintype.card (G ⧸ M) = 3 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hM_idx]
  have hsurj : Function.Surjective (fun i : Fin 3 => (a i.castSucc : G ⧸ M)) := by
    have hinj : Function.Injective (fun i : Fin 3 => (a i.castSucc : G ⧸ M)) := by
      intro i j hij
      by_contra h
      exact hne i j h hij
    exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp [hcard_q]⟩ |>.2
  -- Let t = [H 3 : M ⊓ H 3]; then t ∈ {1, 2, 3} and [M : M ⊓ H 3] = t * e 3
  let t : ℕ := (M ⊓ H 3).relIndex (H 3)
  let Q : Finset (G ⧸ M) := Finset.univ.image (fun h : H 3 => ((a 3 * (h : G) : G) : G ⧸ M))
  have hQcard : Q.card = t := card_cosets_met_eq_relIndex M (H 3) (a 3)
  have ht_pos : 0 < t := by
    rw [← hQcard]
    exact Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (1 : H 3))⟩
  have ht_le : t ≤ 3 := by
    rw [← hQcard, ← hcard_q]
    exact Finset.card_le_univ Q
  have hrel3 : (M ⊓ H 3).relIndex M = t * e 3 := by
    have h1 := index_mul_relIndex (inf_le_left : M ⊓ H 3 ≤ M)
    have h2 := index_mul_relIndex (inf_le_right : M ⊓ H 3 ≤ H 3)
    rw [hM_idx] at h1
    rw [he 3] at h2
    have heq : 3 * (M ⊓ H 3).relIndex M = 3 * (t * e 3) := by
      calc 3 * (M ⊓ H 3).relIndex M = (M ⊓ H 3).index := h1
        _ = 3 * e 3 * t := h2.symm
        _ = 3 * (t * e 3) := by ring
    omega
  have h_kill : ∀ i : Fin 3, (a i.castSucc : G ⧸ M) ∈ Q →
      Nat.Coprime (e i.castSucc) (t * e 3) → False := by
    intro i hiQ hcop_it
    rcases Finset.mem_image.mp hiQ with ⟨⟨h3, hh3⟩, _, hq⟩
    have hle_i : H i.castSucc ≤ M := by fin_cases i <;> assumption
    have hcop_rel : Nat.Coprime ((H i.castSucc).relIndex M) ((M ⊓ H 3).relIndex M) := by
      rw [hrel i, hrel3]; exact hcop_it
    exact not_disjoint_of_meet_coset_coprime hle_i hcop_rel ⟨h3, hh3, hq⟩
      (hdisj (by fin_cases i <;> decide))
  have ht_cases : t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases ht_cases with ht1 | ht2 | ht3
  · -- t = 1: pick the coset a_i M containing a_3
    obtain ⟨i, hi⟩ := hsurj ((a 3 : G) : G ⧸ M)
    dsimp only at hi
    have hiQ : (a i.castSucc : G ⧸ M) ∈ Q := by
      rw [hi]
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩
    have hcop_it : Nat.Coprime (e i.castSucc) (t * e 3) := by
      rw [ht1, one_mul]
      exact he_cop i.castSucc 3 (by fin_cases i <;> decide)
    exact h_kill i hiQ hcop_it
  · -- t = 2: pick the coset a_i M containing a_3; since e_i is odd, gcd(e_i, 2 * e_3) = 1
    obtain ⟨i, hi⟩ := hsurj ((a 3 : G) : G ⧸ M)
    dsimp only at hi
    have hiQ : (a i.castSucc : G ⧸ M) ∈ Q := by
      rw [hi]
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩
    have hodd_i : Odd (e i.castSucc) := by
      fin_cases i
      · exact he_odd.1
      · exact he_odd.2.1
      · exact he_odd.2.2
    have hcop2 : Nat.Coprime (e i.castSucc) 2 := Nat.coprime_two_right.mpr hodd_i
    have hcop_it : Nat.Coprime (e i.castSucc) (t * e 3) := by
      rw [ht2]
      exact hcop2.mul_right (he_cop i.castSucc 3 (by fin_cases i <;> decide))
    exact h_kill i hiQ hcop_it
  · -- t = 3: Q = Finset.univ, so a_3 H_3 meets ALL 3 cosets; pick i with ¬ 3 ∣ e_i!
    have hQuniv : Q = Finset.univ := Finset.eq_univ_of_card Q (by rw [hQcard, ht3, hcard_q])
    have hex_ndvd3 : ∃ i : Fin 3, ¬ 3 ∣ e i.castSucc := by
      by_contra hall
      push Not at hall
      have h0 := hall 0
      have h1 := hall 1
      have h3dvd : 3 ∣ Nat.gcd (e 0) (e 1) := Nat.dvd_gcd h0 h1
      rw [he_cop 0 1 (by decide)] at h3dvd
      omega
    obtain ⟨i, hndvd3⟩ := hex_ndvd3
    have hcop3 : Nat.Coprime (e i.castSucc) 3 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd3 |>.symm
    have hcop_it : Nat.Coprime (e i.castSucc) (t * e 3) := by
      rw [ht3]
      exact hcop3.mul_right (he_cop i.castSucc 3 (by fin_cases i <;> decide))
    exact h_kill i (by rw [hQuniv]; exact Finset.mem_univ _) hcop_it

/-- **Key `k = 4` triple analysis**: Rules out 4 pairwise disjoint left cosets whose indices are
`3 * e_i` with `e_i` pairwise coprime and `e 0, e 1, e 2` odd. -/
private lemma k4_all_gcd_three_ordered
    (a : Fin 4 → G) (H : Fin 4 → Subgroup G) (e : Fin 4 → ℕ)
    (he : ∀ i, (H i).index = 3 * e i)
    (he_cop : ∀ i j, i ≠ j → Nat.Coprime (e i) (e j))
    (he_odd : Odd (e 0) ∧ Odd (e 1) ∧ Odd (e 2))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) : False := by
  have he_pos : ∀ i : Fin 4, 0 < e i := fun i => by
    have hp := index_pos_of_fintype (H i); rw [he i] at hp; omega
  -- Helper: for any distinct i, j, define m(i, j) ∈ {1, 2} with [G : H_i ⊓ H_j] = 3 * m * e_i * e_j
  -- and |H_i H_j| * 3 = m * |G|
  have hm_exists : ∀ i j : Fin 4, i ≠ j →
      ∃ m : ℕ, (m = 1 ∨ m = 2) ∧
        (H i ⊓ H j).index = 3 * m * e i * e j ∧
        (prodFinset (H i) (H j)).card * 3 = m * Nat.card G := by
    intro i j hij
    obtain ⟨hdvd, hlt⟩ := index_inf_bounds_of_disjoint (a i) (a j) (H i) (H j) (hdisj hij)
    have hg : Nat.gcd (H i).index (H j).index = 3 := by
      rw [he i, he j, Nat.gcd_mul_left, he_cop i j hij, mul_one]
    have hlcm : Nat.lcm (H i).index (H j).index = 3 * e i * e j := by
      have hp := Nat.gcd_mul_lcm (H i).index (H j).index
      rw [hg, he i, he j] at hp
      have hp' : 3 * Nat.lcm (H i).index (H j).index = 3 * (3 * e i * e j) := by
        rw [he i, he j]; linarith
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) hp'
    rw [hlcm] at hdvd
    rw [he i, he j] at hlt
    rcases hdvd with ⟨m, hm⟩
    have hm_pos : 0 < m := by
      have hp := index_pos_of_fintype (H i ⊓ H j); rw [hm] at hp
      exact Nat.pos_of_mul_pos_left hp
    have hm_lt : m < 3 := by
      have h1 : 3 * e i * e j * m < 3 * e i * e j * 3 := by
        calc 3 * e i * e j * m = (H i ⊓ H j).index := hm.symm
          _ < 3 * e i * (3 * e j) := hlt
          _ = 3 * e i * e j * 3 := by ring
      exact Nat.lt_of_mul_lt_mul_left h1
    have hinf_eq : (H i ⊓ H j).index = 3 * m * e i * e j := by rw [hm]; ring
    have hcard_eq : (prodFinset (H i) (H j)).card * 3 = m * Nat.card G := by
      have hkey := card_prodFinset_mul_index (H i) (H j)
      rw [hinf_eq, he i, he j] at hkey
      have hpos : 0 < 3 * e i * e j := Nat.mul_pos (Nat.mul_pos (by decide) (he_pos i)) (he_pos j)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        (prodFinset (H i) (H j)).card * 3 * (3 * e i * e j)
            = (prodFinset (H i) (H j)).card * (3 * e i * (3 * e j)) := by ring
        _ = Nat.card G * (3 * m * e i * e j) := hkey
        _ = m * Nat.card G * (3 * e i * e j) := by ring
    exact ⟨m, by omega, hinf_eq, hcard_eq⟩
  -- Helper Case 1: if for some triple (p, q, r) permuting {0,1,2} we have m(p,q)=1 and m(p,r)=1
  have hcase_two_ones : ∀ (p q r : Fin 4),
      ({p, q, r} : Finset (Fin 4)) = {0, 1, 2} → p ≠ q → p ≠ r → q ≠ r →
      (H p ⊓ H q).index = 3 * e p * e q →
      (H p ⊓ H r).index = 3 * e p * e r → False := by
    intro p q r hset hpq hpr hqr hpq_idx hpr_idx
    have hodd_p : Odd (e p) := by
      have hp_mem : p ∈ ({0, 1, 2} : Finset (Fin 4)) := by rw [← hset]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      rcases hp_mem with rfl | rfl | rfl
      · exact he_odd.1
      · exact he_odd.2.1
      · exact he_odd.2.2
    obtain ⟨mqr, hmqr_val, hqr_idx, hqr_card⟩ := hm_exists q r hqr
    -- [H p : H p ⊓ H q] = e q, [H p : H p ⊓ H r] = e r, coprime -> [G : H p ⊓ H q ⊓ H r] = 3 e_p e_q e_r
    have hrel_pq : (H p ⊓ H q).relIndex (H p) = e q := by
      have h := index_mul_relIndex (inf_le_left : H p ⊓ H q ≤ H p)
      rw [hpq_idx, he p] at h
      have hpos : 0 < 3 * e p := Nat.mul_pos (by decide) (he_pos p)
      apply Nat.eq_of_mul_eq_mul_left hpos; linarith
    have hrel_pr : (H p ⊓ H r).relIndex (H p) = e r := by
      have h := index_mul_relIndex (inf_le_left : H p ⊓ H r ≤ H p)
      rw [hpr_idx, he p] at h
      have hpos : 0 < 3 * e p := Nat.mul_pos (by decide) (he_pos p)
      apply Nat.eq_of_mul_eq_mul_left hpos; linarith
    have hinf_pqr : (H p ⊓ (H q ⊓ H r)).index = 3 * e p * e q * e r := by
      have heq_sub : H p ⊓ (H q ⊓ H r) = (H p ⊓ H q) ⊓ (H p ⊓ H r) := by
        ext x; simp only [Subgroup.mem_inf]; tauto
      rw [heq_sub, ← index_mul_relIndex (le_trans inf_le_left inf_le_left :
          (H p ⊓ H q) ⊓ (H p ⊓ H r) ≤ H p)]
      rw [relIndex_inf_eq_mul_of_coprime (by rw [hrel_pq, hrel_pr]; exact he_cop q r hqr)]
      rw [hrel_pq, hrel_pr, he p]; ring
    -- Since [G : H q ⊓ H r] ∣ [G : H p ⊓ (H q ⊓ H r)] and e p is odd, mqr = 1!
    have hmqr1 : mqr = 1 := by
      have hdvd : (H q ⊓ H r).index ∣ (H p ⊓ (H q ⊓ H r)).index :=
        Subgroup.index_dvd_of_le inf_le_right
      rw [hqr_idx, hinf_pqr] at hdvd
      have hdvd' : (3 * e q * e r) * mqr ∣ (3 * e q * e r) * e p := by
        have h1 : 3 * mqr * e q * e r = (3 * e q * e r) * mqr := by ring
        have h2 : 3 * e p * e q * e r = (3 * e q * e r) * e p := by ring
        rwa [← h1, ← h2]
      have hmdvd : mqr ∣ e p :=
        (Nat.mul_dvd_mul_iff_left (Nat.mul_pos (Nat.mul_pos (by decide) (he_pos q)) (he_pos r))).mp hdvd'
      rcases hmqr_val with h1 | h2
      · exact h1
      · rw [h2] at hmdvd
        exact absurd hmdvd (Nat.odd_iff.mp hodd_p |> fun h => by omega)
    rw [hmqr1] at hqr_idx hqr_card
    -- Now |H_p (H_q ⊓ H_r)| * 3 = |G| = |H_p H_q| * 3 = |H_p H_r| * 3!
    have hpq_card : (prodFinset (H p) (H q)).card * 3 = Nat.card G := by
      have hkey := card_prodFinset_mul_index (H p) (H q)
      rw [hpq_idx, he p, he q] at hkey
      have hpos : 0 < 3 * e p * e q := Nat.mul_pos (Nat.mul_pos (by decide) (he_pos p)) (he_pos q)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (prodFinset (H p) (H q)).card * 3 * (3 * e p * e q)
          = (prodFinset (H p) (H q)).card * (3 * e p * (3 * e q)) := by ring
        _ = Nat.card G * (3 * e p * e q) := hkey
    have hpr_card : (prodFinset (H p) (H r)).card * 3 = Nat.card G := by
      have hkey := card_prodFinset_mul_index (H p) (H r)
      rw [hpr_idx, he p, he r] at hkey
      have hpos : 0 < 3 * e p * e r := Nat.mul_pos (Nat.mul_pos (by decide) (he_pos p)) (he_pos r)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (prodFinset (H p) (H r)).card * 3 * (3 * e p * e r)
          = (prodFinset (H p) (H r)).card * (3 * e p * (3 * e r)) := by ring
        _ = Nat.card G * (3 * e p * e r) := hkey
    have hp_qr_card : (prodFinset (H p) (H q ⊓ H r)).card * 3 = Nat.card G := by
      have hkey := card_prodFinset_mul_index (H p) (H q ⊓ H r)
      rw [hinf_pqr, he p, hqr_idx] at hkey
      have hpos : 0 < 3 * e p * e q * e r :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (he_pos p)) (he_pos q)) (he_pos r)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (prodFinset (H p) (H q ⊓ H r)).card * 3 * (3 * e p * e q * e r)
          = (prodFinset (H p) (H q ⊓ H r)).card * (3 * e p * (3 * 1 * e q * e r)) := by ring
        _ = Nat.card G * (3 * e p * e q * e r) := hkey
    have heq_pq : prodFinset (H p) (H q ⊓ H r) = prodFinset (H p) (H q) :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => by
          rcases mem_prodFinset.mp hx with ⟨hp, hhp, hqr', ⟨hhq, _⟩, rfl⟩
          exact mem_prodFinset.mpr ⟨hp, hhp, hqr', hhq, rfl⟩)
        (by omega)
    have heq_pr : prodFinset (H p) (H q ⊓ H r) = prodFinset (H p) (H r) :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => by
          rcases mem_prodFinset.mp hx with ⟨hp, hhp, hqr', ⟨_, hhr⟩, rfl⟩
          exact mem_prodFinset.mpr ⟨hp, hhp, hqr', hhr, rfl⟩)
        (by omega)
    have hS_eq : prodFinset (H p) (H q) = prodFinset (H p) (H r) := heq_pq.symm.trans heq_pr
    -- M = H q ⊔ H r has index 3 and contains H p, H q, H r!
    let M : Subgroup G := H q ⊔ H r
    have hinvM := right_invariant_sup_dvd (S := prodFinset (H p) (H q)) (H₁ := H q) (H₂ := H r)
      (fun x hx h hh => by
        rcases mem_prodFinset.mp hx with ⟨hp, hhp, hq, hhq, rfl⟩
        exact mem_prodFinset.mpr ⟨hp, hhp, hq * h, (H q).mul_mem hhq hh, by group⟩)
      (fun x hx h hh => by
        rw [hS_eq] at hx ⊢
        rcases mem_prodFinset.mp hx with ⟨hp, hhp, hr, hhr, rfl⟩
        exact mem_prodFinset.mpr ⟨hp, hhp, hr * h, (H r).mul_mem hhr hh, by group⟩)
    have h1S : (1 : G) ∈ prodFinset (H p) (H q) :=
      mem_prodFinset.mpr ⟨1, (H p).one_mem, 1, (H q).one_mem, by simp⟩
    have hM_sub_S : ∀ m ∈ M, m ∈ prodFinset (H p) (H q) := fun m hm => by
      simpa using hinvM.1 1 h1S m hm
    have hqr_sub_M : ∀ x ∈ prodFinset (H q) (H r), x ∈ M := by
      intro x hx
      rcases mem_prodFinset.mp hx with ⟨hq, hhq, hr, hhr, rfl⟩
      exact M.mul_mem ((le_sup_left : H q ≤ M) hhq) ((le_sup_right : H r ≤ M) hhr)
    have hM_card_filt : (Finset.univ.filter (fun x : G => x ∈ M)).card = Nat.card M := by
      simpa using card_leftCoset_finset (1 : G) M
    have hM_card_le : Nat.card M ≤ (prodFinset (H p) (H q)).card := by
      rw [← hM_card_filt]
      exact Finset.card_le_card (fun x hx => hM_sub_S x (Finset.mem_filter.mp hx).2)
    have hM_card_ge : (prodFinset (H q) (H r)).card ≤ Nat.card M := by
      rw [← hM_card_filt]
      exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqr_sub_M x hx⟩)
    have hM_eq_card : Nat.card M = (prodFinset (H p) (H q)).card := by omega
    have hM_idx : M.index = 3 := by
      have hm := Subgroup.index_mul_card M
      rw [hM_eq_card] at hm
      have hpos : 0 < (prodFinset (H p) (H q)).card := Finset.card_pos.mpr ⟨1, h1S⟩
      apply Nat.eq_of_mul_eq_mul_right hpos; linarith
    have hM_eq_S : Finset.univ.filter (fun x : G => x ∈ M) = prodFinset (H p) (H q) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; exact hM_sub_S x (Finset.mem_filter.mp hx).2
      · rw [hM_card_filt, hM_eq_card]
    have hpM : H p ≤ M := by
      intro x hx
      have hxS : x ∈ prodFinset (H p) (H q) :=
        mem_prodFinset.mpr ⟨x, hx, 1, (H q).one_mem, by simp⟩
      rw [← hM_eq_S] at hxS
      exact (Finset.mem_filter.mp hxS).2
    have hqM : H q ≤ M := le_sup_left
    have hrM : H r ≤ M := le_sup_right
    have hallM : ∀ i ∈ ({0, 1, 2} : Finset (Fin 4)), H i ≤ M := by
      intro i hi
      rw [← hset] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact hpM
      · exact hqM
      · exact hrM
    exact k4_core_index3_subgroup a H e he he_cop he_odd hdisj M hM_idx
      (hallM 0 (by simp)) (hallM 1 (by simp)) (hallM 2 (by simp))
  -- Helper Case 2: if for some triple (p, q, r) permuting {0,1,2} we have m(p,q)=2, m(p,r)=2, m(q,r)=1
  have hcase_one_one : ∀ (p q r : Fin 4),
      ({p, q, r} : Finset (Fin 4)) = {0, 1, 2} → p ≠ q → p ≠ r → q ≠ r →
      (H p ⊓ H q).index = 6 * e p * e q →
      (H p ⊓ H r).index = 6 * e p * e r →
      (H q ⊓ H r).index = 3 * e q * e r → False := by
    intro p q r hset hpq hpr hqr hpq_idx hpr_idx hqr_idx
    have hodd_q : Odd (e q) := by
      have hq_mem : q ∈ ({0, 1, 2} : Finset (Fin 4)) := by rw [← hset]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq_mem
      rcases hq_mem with rfl | rfl | rfl <;> [exact he_odd.1; exact he_odd.2.1; exact he_odd.2.2]
    have hodd_r : Odd (e r) := by
      have hr_mem : r ∈ ({0, 1, 2} : Finset (Fin 4)) := by rw [← hset]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr_mem
      rcases hr_mem with rfl | rfl | rfl <;> [exact he_odd.1; exact he_odd.2.1; exact he_odd.2.2]
    have hrel_pq : (H p ⊓ H q).relIndex (H p) = 2 * e q := by
      have h := index_mul_relIndex (inf_le_left : H p ⊓ H q ≤ H p)
      rw [hpq_idx, he p] at h
      have hpos : 0 < 3 * e p := Nat.mul_pos (by decide) (he_pos p)
      apply Nat.eq_of_mul_eq_mul_left hpos; linarith
    have hrel_pr : (H p ⊓ H r).relIndex (H p) = 2 * e r := by
      have h := index_mul_relIndex (inf_le_left : H p ⊓ H r ≤ H p)
      rw [hpr_idx, he p] at h
      have hpos : 0 < 3 * e p := Nat.mul_pos (by decide) (he_pos p)
      apply Nat.eq_of_mul_eq_mul_left hpos; linarith
    -- Inside H_p: lcm(2 e_q, 2 e_r) = 2 e_q e_r ∣ relIndex ≤ 4 e_q e_r, so relIndex = c * e_q * e_r with c ∈ {2, 4}
    have heq_sub : H p ⊓ (H q ⊓ H r) = (H p ⊓ H q) ⊓ (H p ⊓ H r) := by
      ext x; simp only [Subgroup.mem_inf]; tauto
    have hlcm_rel : Nat.lcm ((H p ⊓ H q).relIndex (H p)) ((H p ⊓ H r).relIndex (H p)) = 2 * e q * e r := by
      rw [hrel_pq, hrel_pr]
      have h1 := Nat.gcd_mul_lcm (2 * e q) (2 * e r)
      have hg2 : Nat.gcd (2 * e q) (2 * e r) = 2 := by
        rw [Nat.gcd_mul_left, he_cop q r hqr, mul_one]
      rw [hg2] at h1
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
      linarith
    have hdvd_rel : 2 * e q * e r ∣ ((H p ⊓ H q) ⊓ (H p ⊓ H r)).relIndex (H p) := by
      rw [← hlcm_rel]
      exact relIndex_inf_lcm_dvd (H p) (H p ⊓ H q) (H p ⊓ H r)
    have hle_rel : ((H p ⊓ H q) ⊓ (H p ⊓ H r)).relIndex (H p) ≤ 4 * e q * e r := by
      have h := relIndex_inf_le_mul (H p) (H p ⊓ H q) (H p ⊓ H r)
      rw [hrel_pq, hrel_pr] at h; linarith
    rcases hdvd_rel with ⟨t, ht⟩
    have ht_pos : 0 < t := by
      have hidx_pos := index_pos_of_fintype ((H p ⊓ H q) ⊓ (H p ⊓ H r))
      have hm := index_mul_relIndex (le_trans inf_le_left inf_le_left :
          (H p ⊓ H q) ⊓ (H p ⊓ H r) ≤ H p)
      rw [ht] at hm
      have hpos_rel : 0 < 2 * e q * e r * t := by
        by_contra h0; push Not at h0
        have : 2 * e q * e r * t = 0 := by omega
        rw [this, mul_zero] at hm; omega
      exact Nat.pos_of_mul_pos_left hpos_rel
    have ht_le : t ≤ 2 := by
      have h1 : 2 * e q * e r * t ≤ 2 * e q * e r * 2 := by linarith
      exact Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos (Nat.mul_pos (by decide) (he_pos q)) (he_pos r))
    have hinf_pqr : (H p ⊓ (H q ⊓ H r)).index = 6 * t * e p * e q * e r := by
      rw [heq_sub, ← index_mul_relIndex (le_trans inf_le_left inf_le_left :
          (H p ⊓ H q) ⊓ (H p ⊓ H r) ≤ H p), ht, he p]; ring
    -- Compute |H_p (H_q ⊓ H_r)| * 3 = 2 * t * |G|; since ≤ |G|, t CANNOT be 2!
    have hp_qr_card : (prodFinset (H p) (H q ⊓ H r)).card * 3 = 2 * t * Nat.card G := by
      have hkey := card_prodFinset_mul_index (H p) (H q ⊓ H r)
      rw [hinf_pqr, he p, hqr_idx] at hkey
      have hpos : 0 < 3 * e p * e q * e r :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (he_pos p)) (he_pos q)) (he_pos r)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (prodFinset (H p) (H q ⊓ H r)).card * 3 * (3 * e p * e q * e r)
          = (prodFinset (H p) (H q ⊓ H r)).card * (3 * e p * (3 * e q * e r)) := by ring
        _ = Nat.card G * (6 * t * e p * e q * e r) := hkey
        _ = 2 * t * Nat.card G * (3 * e p * e q * e r) := by ring
    have ht1 : t = 1 := by
      have hle_G : (prodFinset (H p) (H q ⊓ H r)).card ≤ Nat.card G := by
        rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
      have hGpos : 0 < Nat.card G := Nat.card_pos
      have : 2 * t * Nat.card G ≤ 3 * Nat.card G := by linarith
      have : 2 * t ≤ 3 := Nat.le_of_mul_le_mul_right this hGpos
      omega
    rw [ht1, mul_one] at hp_qr_card
    -- Now |H_p (H_q ⊓ H_r)| * 3 = 2 * |G| = |H_p H_q| * 3 = |H_p H_r| * 3!
    have hpq_card : (prodFinset (H p) (H q)).card * 3 = 2 * Nat.card G := by
      have hkey := card_prodFinset_mul_index (H p) (H q)
      rw [hpq_idx, he p, he q] at hkey
      have hpos : 0 < 3 * e p * e q := Nat.mul_pos (Nat.mul_pos (by decide) (he_pos p)) (he_pos q)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (prodFinset (H p) (H q)).card * 3 * (3 * e p * e q)
          = (prodFinset (H p) (H q)).card * (3 * e p * (3 * e q)) := by ring
        _ = Nat.card G * (6 * e p * e q) := hkey
        _ = 2 * Nat.card G * (3 * e p * e q) := by ring
    have hpr_card : (prodFinset (H p) (H r)).card * 3 = 2 * Nat.card G := by
      have hkey := card_prodFinset_mul_index (H p) (H r)
      rw [hpr_idx, he p, he r] at hkey
      have hpos : 0 < 3 * e p * e r := Nat.mul_pos (Nat.mul_pos (by decide) (he_pos p)) (he_pos r)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (prodFinset (H p) (H r)).card * 3 * (3 * e p * e r)
          = (prodFinset (H p) (H r)).card * (3 * e p * (3 * e r)) := by ring
        _ = Nat.card G * (6 * e p * e r) := hkey
        _ = 2 * Nat.card G * (3 * e p * e r) := by ring
    have hqr_card : (prodFinset (H q) (H r)).card * 3 = Nat.card G := by
      have hkey := card_prodFinset_mul_index (H q) (H r)
      rw [hqr_idx, he q, he r] at hkey
      have hpos : 0 < 3 * e q * e r := Nat.mul_pos (Nat.mul_pos (by decide) (he_pos q)) (he_pos r)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (prodFinset (H q) (H r)).card * 3 * (3 * e q * e r)
          = (prodFinset (H q) (H r)).card * (3 * e q * (3 * e r)) := by ring
        _ = Nat.card G * (3 * e q * e r) := hkey
    have heq_pq : prodFinset (H p) (H q ⊓ H r) = prodFinset (H p) (H q) :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => by
          rcases mem_prodFinset.mp hx with ⟨hp, hhp, hqr', ⟨hhq, _⟩, rfl⟩
          exact mem_prodFinset.mpr ⟨hp, hhp, hqr', hhq, rfl⟩)
        (by omega)
    have heq_pr : prodFinset (H p) (H q ⊓ H r) = prodFinset (H p) (H r) :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => by
          rcases mem_prodFinset.mp hx with ⟨hp, hhp, hqr', ⟨_, hhr⟩, rfl⟩
          exact mem_prodFinset.mpr ⟨hp, hhp, hqr', hhr, rfl⟩)
        (by omega)
    have hS_eq : prodFinset (H p) (H q) = prodFinset (H p) (H r) := heq_pq.symm.trans heq_pr
    -- S = H_p H_q is right-invariant under M = H_q ⊔ H_r!
    -- Therefore |M| ∣ |S| = 2|G|/3 AND |M| ∣ |G|, while |M| ≥ |H_q H_r| = |G|/3 -> |M| = |G|/3!
    let M : Subgroup G := H q ⊔ H r
    have hinvM := right_invariant_sup_dvd (S := prodFinset (H p) (H q)) (H₁ := H q) (H₂ := H r)
      (fun x hx h hh => by
        rcases mem_prodFinset.mp hx with ⟨hp, hhp, hq, hhq, rfl⟩
        exact mem_prodFinset.mpr ⟨hp, hhp, hq * h, (H q).mul_mem hhq hh, by group⟩)
      (fun x hx h hh => by
        rw [hS_eq] at hx ⊢
        rcases mem_prodFinset.mp hx with ⟨hp, hhp, hr, hhr, rfl⟩
        exact mem_prodFinset.mpr ⟨hp, hhp, hr * h, (H r).mul_mem hhr hh, by group⟩)
    have hM_dvd_S : Nat.card M ∣ (prodFinset (H p) (H q)).card := hinvM.2
    have hM_idx_mul : M.index * Nat.card M = Nat.card G := Subgroup.index_mul_card M
    rcases hM_dvd_S with ⟨cS, hcS⟩
    have hqr_sub_M : ∀ x ∈ prodFinset (H q) (H r), x ∈ M := by
      intro x hx
      rcases mem_prodFinset.mp hx with ⟨hq, hhq, hr, hhr, rfl⟩
      exact M.mul_mem ((le_sup_left : H q ≤ M) hhq) ((le_sup_right : H r ≤ M) hhr)
    have hM_card_filt : (Finset.univ.filter (fun x : G => x ∈ M)).card = Nat.card M := by
      simpa using card_leftCoset_finset (1 : G) M
    have hM_card_ge : (prodFinset (H q) (H r)).card ≤ Nat.card M := by
      rw [← hM_card_filt]
      exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqr_sub_M x hx⟩)
    -- From cS * |M| * 3 = 2 * M.index * |M| -> 3 * cS = 2 * M.index, and M.index ≤ 3!
    have hM_pos : 0 < Nat.card M := Nat.card_pos
    have h3cS : 3 * cS = 2 * M.index := by
      apply Nat.eq_of_mul_eq_mul_right hM_pos
      calc 3 * cS * Nat.card M = (Nat.card M * cS) * 3 := by ring
        _ = (prodFinset (H p) (H q)).card * 3 := by rw [← hcS]
        _ = 2 * Nat.card G := hpq_card
        _ = 2 * (M.index * Nat.card M) := by rw [← hM_idx_mul]
        _ = 2 * M.index * Nat.card M := by ring
    have hM_le3 : M.index ≤ 3 := by
      have : M.index * Nat.card M ≤ 3 * Nat.card M := by linarith
      exact Nat.le_of_mul_le_mul_right this hM_pos
    have hM_idx_pos : 0 < M.index := index_pos_of_fintype M
    have hM_idx : M.index = 3 := by omega
    have hM_eq_qr : Nat.card M = (prodFinset (H q) (H r)).card := by
      rw [hM_idx] at hM_idx_mul; omega
    have hM_eq_qr_set : ∀ x, x ∈ prodFinset (H q) (H r) ↔ x ∈ M := by
      have hfilt : prodFinset (H q) (H r) = Finset.univ.filter (fun x : G => x ∈ M) := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqr_sub_M x hx⟩
        · rw [hM_card_filt, hM_eq_qr]
      intro x; simpa using Finset.ext_iff.mp hfilt x
    -- S = H_p H_q = H_p M has size 2|M|, so [H_p : M ⊓ H_p] = 2!
    have hHpM_sub_S : prodFinset (H p) M ⊆ prodFinset (H p) (H q) := by
      intro x hx
      rcases mem_prodFinset.mp hx with ⟨hp, hhp, m, hm, rfl⟩
      have hhpS : hp ∈ prodFinset (H p) (H q) :=
        mem_prodFinset.mpr ⟨hp, hhp, 1, (H q).one_mem, by simp⟩
      exact hinvM.1 hp hhpS m hm
    have hS_sub_HpM : prodFinset (H p) (H q) ⊆ prodFinset (H p) M := by
      intro x hx
      rcases mem_prodFinset.mp hx with ⟨hp, hhp, hq, hhq, rfl⟩
      exact mem_prodFinset.mpr ⟨hp, hhp, hq, (le_sup_left : H q ≤ M) hhq, rfl⟩
    have hHpM_card : (prodFinset (H p) M).card = (prodFinset (H p) (H q)).card :=
      congr_arg Finset.card (Finset.Subset.antisymm hHpM_sub_S hS_sub_HpM)
    have hrel_p_M : (M ⊓ H p).relIndex (H p) = 2 := by
      have hkey := card_prodFinset_mul_index (H p) M
      rw [hHpM_card, hM_idx, he p] at hkey
      have hinf_comm : H p ⊓ M = M ⊓ H p := inf_comm _ _
      rw [hinf_comm, ← index_mul_relIndex (inf_le_right : M ⊓ H p ≤ H p), he p] at hkey
      have hGpos : 0 < Nat.card G := Nat.card_pos
      have hepos : 0 < 3 * e p := Nat.mul_pos (by decide) (he_pos p)
      have h1 : 2 * Nat.card G * (3 * e p) = Nat.card G * (3 * e p * (M ⊓ H p).relIndex (H p)) := by
        calc 2 * Nat.card G * (3 * e p)
            = (prodFinset (H p) (H q)).card * 3 * (3 * e p) := by rw [hpq_card]
          _ = (prodFinset (H p) (H q)).card * (3 * e p * 3) := by ring
          _ = Nat.card G * (3 * e p * (M ⊓ H p).relIndex (H p)) := hkey
      have h2 : 2 * (3 * e p) = 3 * e p * (M ⊓ H p).relIndex (H p) :=
        Nat.eq_of_mul_eq_mul_left hGpos (by linarith)
      apply Nat.eq_of_mul_eq_mul_left hepos; linarith
    have hrel_Mp_in_M : (M ⊓ H p).relIndex M = 2 * e p := by
      have h1 := index_mul_relIndex (inf_le_left : M ⊓ H p ≤ M)
      have h2 := index_mul_relIndex (inf_le_right : M ⊓ H p ≤ H p)
      rw [hM_idx] at h1
      rw [he p, hrel_p_M] at h2
      omega
    -- a_q M ≠ a_r M (since a_q⁻¹ a_r ∉ H_q H_r = M), and a_p H_p meets 2 of the 3 cosets of M!
    have hne_qr : (a q : G ⧸ M) ≠ (a r : G ⧸ M) := by
      intro heq
      rw [QuotientGroup.eq] at heq
      exact not_mem_prodFinset_of_disjoint (hdisj hqr) ((hM_eq_qr_set _).mpr heq)
    let Qp : Finset (G ⧸ M) := Finset.univ.image (fun h : H p => ((a p * (h : G) : G) : G ⧸ M))
    have hQp_card : Qp.card = 2 := by
      rw [card_cosets_met_eq_relIndex, hrel_p_M]
    have hcard_qM : Fintype.card (G ⧸ M) = 3 := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hM_idx]
    -- Since |Qp| = 2, |{a_q M, a_r M}| = 2, and |G ⧸ M| = 3, Qp meets {a_q M, a_r M}!
    have hmeet_qr : (a q : G ⧸ M) ∈ Qp ∨ (a r : G ⧸ M) ∈ Qp := by
      by_contra hno
      push Not at hno
      have hdisj_set : Disjoint Qp {(a q : G ⧸ M), (a r : G ⧸ M)} := by
        rw [Finset.disjoint_right]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> [exact hno.1; exact hno.2]
      have hunion_le : (Qp ∪ {(a q : G ⧸ M), (a r : G ⧸ M)}).card ≤ 3 := by
        rw [← hcard_qM]; exact Finset.card_le_univ _
      rw [Finset.card_union_of_disjoint hdisj_set, hQp_card,
        Finset.card_pair hne_qr] at hunion_le
      omega
    rcases hmeet_qr with hmq | hmr
    · rcases Finset.mem_image.mp hmq with ⟨⟨hp, hhp⟩, _, hq_eq⟩
      have hrel_q : (H q).relIndex M = e q := by
        have h := index_mul_relIndex (le_sup_left : H q ≤ M)
        rw [hM_idx, he q] at h
        exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h
      have hcop_qp : Nat.Coprime ((H q).relIndex M) ((M ⊓ H p).relIndex M) := by
        rw [hrel_q, hrel_Mp_in_M]
        exact (Nat.coprime_two_right.mpr hodd_q).mul_right (he_cop q p hpq.symm)
      exact not_disjoint_of_meet_coset_coprime (le_sup_left : H q ≤ M) hcop_qp
        ⟨hp, hhp, hq_eq⟩ (hdisj hpq.symm)
    · rcases Finset.mem_image.mp hmr with ⟨⟨hp, hhp⟩, _, hr_eq⟩
      have hrel_r : (H r).relIndex M = e r := by
        have h := index_mul_relIndex (le_sup_right : H r ≤ M)
        rw [hM_idx, he r] at h
        exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h
      have hcop_rp : Nat.Coprime ((H r).relIndex M) ((M ⊓ H p).relIndex M) := by
        rw [hrel_r, hrel_Mp_in_M]
        exact (Nat.coprime_two_right.mpr hodd_r).mul_right (he_cop r p hpr.symm)
      exact not_disjoint_of_meet_coset_coprime (le_sup_right : H r ≤ M) hcop_rp
        ⟨hp, hhp, hr_eq⟩ (hdisj hpr.symm)
  -- Now split on (m01, m02, m12) ∈ {1, 2}^3!
  obtain ⟨m01, hm01, h01_idx, h01_card⟩ := hm_exists 0 1 (by decide)
  obtain ⟨m02, hm02, h02_idx, h02_card⟩ := hm_exists 0 2 (by decide)
  obtain ⟨m12, hm12, h12_idx, h12_card⟩ := hm_exists 1 2 (by decide)
  rcases hm01 with rfl | rfl <;> rcases hm02 with rfl | rfl <;> rcases hm12 with rfl | rfl
  · -- (1, 1, 1)
    exact hcase_two_ones 0 1 2 (by decide) (by decide) (by decide) (by decide)
      (by simpa using h01_idx) (by simpa using h02_idx)
  · -- (1, 1, 2)
    exact hcase_two_ones 0 1 2 (by decide) (by decide) (by decide) (by decide)
      (by simpa using h01_idx) (by simpa using h02_idx)
  · -- (1, 2, 1): m(1,0)=1, m(1,2)=1
    have h10_idx : (H 1 ⊓ H 0).index = 3 * e 1 * e 0 := by
      rw [inf_comm, h01_idx]; ring
    exact hcase_two_ones 1 0 2 (by decide) (by decide) (by decide) (by decide)
      h10_idx (by simpa using h12_idx)
  · -- (1, 2, 2): m(2,0)=2, m(2,1)=2, m(0,1)=1
    have h20_idx : (H 2 ⊓ H 0).index = 6 * e 2 * e 0 := by
      rw [inf_comm, h02_idx]; ring
    have h21_idx : (H 2 ⊓ H 1).index = 6 * e 2 * e 1 := by
      rw [inf_comm, h12_idx]; ring
    exact hcase_one_one 2 0 1 (by decide) (by decide) (by decide) (by decide)
      h20_idx h21_idx (by simpa using h01_idx)
  · -- (2, 1, 1): m(2,0)=1, m(2,1)=1
    have h20_idx : (H 2 ⊓ H 0).index = 3 * e 2 * e 0 := by
      rw [inf_comm, h02_idx]; ring
    have h21_idx : (H 2 ⊓ H 1).index = 3 * e 2 * e 1 := by
      rw [inf_comm, h12_idx]; ring
    exact hcase_two_ones 2 0 1 (by decide) (by decide) (by decide) (by decide)
      h20_idx h21_idx
  · -- (2, 1, 2): m(1,0)=2, m(1,2)=2, m(0,2)=1
    have h10_idx : (H 1 ⊓ H 0).index = 6 * e 1 * e 0 := by
      rw [inf_comm, h01_idx]; ring
    exact hcase_one_one 1 0 2 (by decide) (by decide) (by decide) (by decide)
      h10_idx h12_idx (by simpa using h02_idx)
  · -- (2, 2, 1): m(0,1)=2, m(0,2)=2, m(1,2)=1
    exact hcase_one_one 0 1 2 (by decide) (by decide) (by decide) (by decide)
      h01_idx h02_idx (by simpa using h12_idx)
  · -- (2, 2, 2): apply conjugate-inverse duality to get m'(0,1) = m'(0,2) = 1!
    obtain ⟨hidx', hdisj', hsum_le⟩ := conjugate_inverse_dual a H hdisj
    let a' : Fin 4 → G := fun i => (a i)⁻¹
    let H' : Fin 4 → Subgroup G := fun i => (H i).map (MulAut.conj (a i)).toMonoidHom
    have he' : ∀ i, (H' i).index = 3 * e i := fun i => (hidx' i).trans (he i)
    -- Show |H'_0 H'_1| * 3 ≤ |G| and |H'_0 H'_2| * 3 ≤ |G|, hence [G : H'_0 ⊓ H'_1] = 3 e_0 e_1
    have hdual_one : ∀ i j : Fin 4, i ≠ j →
        (prodFinset (H i) (H j)).card * 3 = 2 * Nat.card G →
        (H' i ⊓ H' j).index = 3 * e i * e j := by
      intro i j hij h2G
      have hle_sum := hsum_le i j hij
      have hcard'_le : (prodFinset (H' i) (H' j)).card * 3 ≤ Nat.card G := by linarith
      have hkey' := card_prodFinset_mul_index (H' i) (H' j)
      rw [he' i, he' j] at hkey'
      obtain ⟨hdvd', _⟩ := index_inf_bounds_of_disjoint (a' i) (a' j) (H' i) (H' j) (hdisj' hij)
      have hg' : Nat.gcd (H' i).index (H' j).index = 3 := by
        rw [he' i, he' j, Nat.gcd_mul_left, he_cop i j hij, mul_one]
      have hlcm' : Nat.lcm (H' i).index (H' j).index = 3 * e i * e j := by
        have hp := Nat.gcd_mul_lcm (H' i).index (H' j).index
        rw [hg', he' i, he' j] at hp
        have hp' : 3 * Nat.lcm (H' i).index (H' j).index = 3 * (3 * e i * e j) := by
          rw [he' i, he' j]; linarith
        exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) hp'
      rw [hlcm'] at hdvd'
      have hge' : 3 * e i * e j ≤ (H' i ⊓ H' j).index :=
        Nat.le_of_dvd (index_pos_of_fintype (H' i ⊓ H' j)) hdvd'
      have hle' : (H' i ⊓ H' j).index ≤ 3 * e i * e j := by
        have hposG : 0 < Nat.card G := Nat.card_pos
        have h1 : Nat.card G * (H' i ⊓ H' j).index ≤ Nat.card G * (3 * e i * e j) := by
          calc Nat.card G * (H' i ⊓ H' j).index
              = (prodFinset (H' i) (H' j)).card * (3 * e i * (3 * e j)) := hkey'.symm
            _ = ((prodFinset (H' i) (H' j)).card * 3) * (3 * e i * e j) := by ring
            _ ≤ Nat.card G * (3 * e i * e j) := Nat.mul_le_mul_right _ hcard'_le
        exact Nat.le_of_mul_le_mul_left h1 hposG
      exact le_antisymm hle' hge'
    have h01'_idx : (H' 0 ⊓ H' 1).index = 3 * e 0 * e 1 := hdual_one 0 1 (by decide) h01_card
    have h02'_idx : (H' 0 ⊓ H' 2).index = 3 * e 0 * e 2 := hdual_one 0 2 (by decide) h02_card
    have h12'_idx : (H' 1 ⊓ H' 2).index = 3 * e 1 * e 2 := hdual_one 1 2 (by decide) h12_card
    -- Reuse Case (1,1,1) directly on (a', H')!
    have hrel01' : (H' 0 ⊓ H' 1).relIndex (H' 0) = e 1 := by
      have h := index_mul_relIndex (inf_le_left : H' 0 ⊓ H' 1 ≤ H' 0)
      rw [h01'_idx, he' 0] at h
      apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by decide : 0 < 3) (he_pos 0)); linarith
    have hrel02' : (H' 0 ⊓ H' 2).relIndex (H' 0) = e 2 := by
      have h := index_mul_relIndex (inf_le_left : H' 0 ⊓ H' 2 ≤ H' 0)
      rw [h02'_idx, he' 0] at h
      apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by decide : 0 < 3) (he_pos 0)); linarith
    have hinf012' : (H' 0 ⊓ (H' 1 ⊓ H' 2)).index = 3 * e 0 * e 1 * e 2 := by
      have heq_sub : H' 0 ⊓ (H' 1 ⊓ H' 2) = (H' 0 ⊓ H' 1) ⊓ (H' 0 ⊓ H' 2) := by
        ext x; simp only [Subgroup.mem_inf]; tauto
      rw [heq_sub, ← index_mul_relIndex (le_trans inf_le_left inf_le_left :
          (H' 0 ⊓ H' 1) ⊓ (H' 0 ⊓ H' 2) ≤ H' 0)]
      rw [relIndex_inf_eq_mul_of_coprime (by rw [hrel01', hrel02']; exact he_cop 1 2 (by decide))]
      rw [hrel01', hrel02', he' 0]; ring
    have hcard01' : (prodFinset (H' 0) (H' 1)).card * 3 = Nat.card G := by
      have hkey := card_prodFinset_mul_index (H' 0) (H' 1)
      rw [h01'_idx, he' 0, he' 1] at hkey
      apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 3) (he_pos 0)) (he_pos 1))
      calc (prodFinset (H' 0) (H' 1)).card * 3 * (3 * e 0 * e 1)
          = (prodFinset (H' 0) (H' 1)).card * (3 * e 0 * (3 * e 1)) := by ring
        _ = Nat.card G * (3 * e 0 * e 1) := hkey
    have hcard02' : (prodFinset (H' 0) (H' 2)).card * 3 = Nat.card G := by
      have hkey := card_prodFinset_mul_index (H' 0) (H' 2)
      rw [h02'_idx, he' 0, he' 2] at hkey
      apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 3) (he_pos 0)) (he_pos 2))
      calc (prodFinset (H' 0) (H' 2)).card * 3 * (3 * e 0 * e 2)
          = (prodFinset (H' 0) (H' 2)).card * (3 * e 0 * (3 * e 2)) := by ring
        _ = Nat.card G * (3 * e 0 * e 2) := hkey
    have hcard12' : (prodFinset (H' 1) (H' 2)).card * 3 = Nat.card G := by
      have hkey := card_prodFinset_mul_index (H' 1) (H' 2)
      rw [h12'_idx, he' 1, he' 2] at hkey
      apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 3) (he_pos 1)) (he_pos 2))
      calc (prodFinset (H' 1) (H' 2)).card * 3 * (3 * e 1 * e 2)
          = (prodFinset (H' 1) (H' 2)).card * (3 * e 1 * (3 * e 2)) := by ring
        _ = Nat.card G * (3 * e 1 * e 2) := hkey
    have hcard0_12' : (prodFinset (H' 0) (H' 1 ⊓ H' 2)).card * 3 = Nat.card G := by
      have hkey := card_prodFinset_mul_index (H' 0) (H' 1 ⊓ H' 2)
      rw [hinf012', he' 0, h12'_idx] at hkey
      apply Nat.eq_of_mul_eq_mul_right
        (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 3) (he_pos 0)) (he_pos 1)) (he_pos 2))
      calc (prodFinset (H' 0) (H' 1 ⊓ H' 2)).card * 3 * (3 * e 0 * e 1 * e 2)
          = (prodFinset (H' 0) (H' 1 ⊓ H' 2)).card * (3 * e 0 * (3 * e 1 * e 2)) := by ring
        _ = Nat.card G * (3 * e 0 * e 1 * e 2) := hkey
    have heq01' : prodFinset (H' 0) (H' 1 ⊓ H' 2) = prodFinset (H' 0) (H' 1) :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => by
          rcases mem_prodFinset.mp hx with ⟨h0, hh0, h12, ⟨hh1, _⟩, rfl⟩
          exact mem_prodFinset.mpr ⟨h0, hh0, h12, hh1, rfl⟩) (by omega)
    have heq02' : prodFinset (H' 0) (H' 1 ⊓ H' 2) = prodFinset (H' 0) (H' 2) :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => by
          rcases mem_prodFinset.mp hx with ⟨h0, hh0, h12, ⟨_, hh2⟩, rfl⟩
          exact mem_prodFinset.mpr ⟨h0, hh0, h12, hh2, rfl⟩) (by omega)
    have hS_eq' : prodFinset (H' 0) (H' 1) = prodFinset (H' 0) (H' 2) := heq01'.symm.trans heq02'
    let M' : Subgroup G := H' 1 ⊔ H' 2
    have hinvM' := right_invariant_sup_dvd (S := prodFinset (H' 0) (H' 1)) (H₁ := H' 1) (H₂ := H' 2)
      (fun x hx h hh => by
        rcases mem_prodFinset.mp hx with ⟨h0, hh0, h1, hh1, rfl⟩
        exact mem_prodFinset.mpr ⟨h0, hh0, h1 * h, (H' 1).mul_mem hh1 hh, by group⟩)
      (fun x hx h hh => by
        rw [hS_eq'] at hx ⊢
        rcases mem_prodFinset.mp hx with ⟨h0, hh0, h2, hh2, rfl⟩
        exact mem_prodFinset.mpr ⟨h0, hh0, h2 * h, (H' 2).mul_mem hh2 hh, by group⟩)
    have h1S' : (1 : G) ∈ prodFinset (H' 0) (H' 1) :=
      mem_prodFinset.mpr ⟨1, (H' 0).one_mem, 1, (H' 1).one_mem, by simp⟩
    have hM'_sub_S : ∀ m ∈ M', m ∈ prodFinset (H' 0) (H' 1) := fun m hm => by
      simpa using hinvM'.1 1 h1S' m hm
    have h12'_sub_M : ∀ x ∈ prodFinset (H' 1) (H' 2), x ∈ M' := by
      intro x hx
      rcases mem_prodFinset.mp hx with ⟨h1, hh1, h2, hh2, rfl⟩
      exact M'.mul_mem ((le_sup_left : H' 1 ≤ M') hh1) ((le_sup_right : H' 2 ≤ M') hh2)
    have hM'_card_filt : (Finset.univ.filter (fun x : G => x ∈ M')).card = Nat.card M' := by
      simpa using card_leftCoset_finset (1 : G) M'
    have hM'_card_le : Nat.card M' ≤ (prodFinset (H' 0) (H' 1)).card := by
      rw [← hM'_card_filt]
      exact Finset.card_le_card (fun x hx => hM'_sub_S x (Finset.mem_filter.mp hx).2)
    have hM'_card_ge : (prodFinset (H' 1) (H' 2)).card ≤ Nat.card M' := by
      rw [← hM'_card_filt]
      exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12'_sub_M x hx⟩)
    have hM'_eq_card : Nat.card M' = (prodFinset (H' 0) (H' 1)).card := by omega
    have hM'_idx : M'.index = 3 := by
      have hm := Subgroup.index_mul_card M'
      rw [hM'_eq_card] at hm
      apply Nat.eq_of_mul_eq_mul_right (Finset.card_pos.mpr ⟨1, h1S'⟩); linarith
    have hM'_eq_S : Finset.univ.filter (fun x : G => x ∈ M') = prodFinset (H' 0) (H' 1) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; exact hM'_sub_S x (Finset.mem_filter.mp hx).2
      · rw [hM'_card_filt, hM'_eq_card]
    have h0M' : H' 0 ≤ M' := by
      intro x hx
      have hxS : x ∈ prodFinset (H' 0) (H' 1) :=
        mem_prodFinset.mpr ⟨x, hx, 1, (H' 1).one_mem, by simp⟩
      rw [← hM'_eq_S] at hxS
      exact (Finset.mem_filter.mp hxS).2
    exact k4_core_index3_subgroup a' H' e he' he_cop he_odd hdisj' M' hM'_idx
      h0M' le_sup_left le_sup_right

/-- **Key `k = 4` impossibility lemma (finite group)**: four pairwise disjoint left cosets cannot
all have pairwise index gcd in `{2, 3}`. -/
private lemma no_four_pairwise_gcd_lt_four
    (a : Fin 4 → G) (H : Fin 4 → Subgroup G)
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G)))
    (hgcd : ∀ i j : Fin 4, i < j → Nat.gcd (H i).index (H j).index < 4) : False := by
  have hgcd23 : ∀ i j : Fin 4, i ≠ j →
      Nat.gcd (H i).index (H j).index = 2 ∨ Nat.gcd (H i).index (H j).index = 3 := by
    intro i j hij
    have hge := pairwise_gcd_ge_two_finite (a i) (a j) (H i) (H j) (hdisj hij)
    have hlt : Nat.gcd (H i).index (H j).index < 4 := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hgcd i j h
      · rw [Nat.gcd_comm]; exact hgcd j i h
    omega
  -- Either all four indices are divisible by 2, or all four are divisible by 3!
  have hall2_or_3 : (∀ i : Fin 4, 2 ∣ (H i).index) ∨ (∀ i : Fin 4, 3 ∣ (H i).index) := by
    by_cases h2 : ∀ i : Fin 4, 2 ∣ (H i).index
    · exact Or.inl h2
    · right
      push Not at h2
      obtain ⟨i₀, hi₀⟩ := h2
      have h3_other : ∀ j : Fin 4, j ≠ i₀ → 3 ∣ (H j).index ∧ 3 ∣ (H i₀).index := by
        intro j hji
        rcases hgcd23 i₀ j hji.symm with h2g | h3g
        · exfalso
          have h2dvd : 2 ∣ (H i₀).index := by rw [← h2g]; exact Nat.gcd_dvd_left _ _
          exact hi₀ h2dvd
        · exact ⟨by rw [← h3g]; exact Nat.gcd_dvd_right _ _,
                 by rw [← h3g]; exact Nat.gcd_dvd_left _ _⟩
      intro j
      by_cases hji : j = i₀
      · subst hji
        obtain ⟨k, hk⟩ : ∃ k : Fin 4, k ≠ j := by
          by_cases hj0 : j = 0
          · exact ⟨1, by omega⟩
          · exact ⟨0, Ne.symm hj0⟩
        exact (h3_other k hk).2
      · exact (h3_other j hji).1
  rcases hall2_or_3 with hall2 | hall3
  · -- All four divisible by 2 -> all pairwise gcds = 2 -> contradict k = 3 on {0, 1, 2}!
    have hgcd2 : ∀ i j : Fin 3, i < j →
        Nat.gcd (H i.castSucc).index (H j.castSucc).index = 2 := by
      intro i j hij
      have h2d : 2 ∣ Nat.gcd (H i.castSucc).index (H j.castSucc).index :=
        Nat.dvd_gcd (hall2 i.castSucc) (hall2 j.castSucc)
      have hlt := hgcd i.castSucc j.castSucc (by simpa using hij)
      have hge := pairwise_gcd_ge_two_finite (a i.castSucc) (a j.castSucc)
        (H i.castSucc) (H j.castSucc) (hdisj (by simpa using ne_of_lt hij))
      omega
    exact no_three_pairwise_gcd_two (fun i => a i.castSucc) (fun i => H i.castSucc)
      (fun i j hij => hdisj (by simpa using hij)) hgcd2
  · -- All four divisible by 3 -> all pairwise gcds = 3!
    choose e he using hall3
    have he_cop : ∀ i j : Fin 4, i ≠ j → Nat.Coprime (e i) (e j) := by
      intro i j hij
      have h3d : 3 ∣ Nat.gcd (H i).index (H j).index :=
        Nat.dvd_gcd ⟨e i, he i⟩ ⟨e j, he j⟩
      have hpos : 0 < Nat.gcd (H i).index (H j).index :=
        Nat.gcd_pos_of_pos_left _ (index_pos_of_fintype (H i))
      have hlt : Nat.gcd (H i).index (H j).index < 4 := by
        rcases lt_or_gt_of_ne hij with h | h
        · exact hgcd i j h
        · rw [Nat.gcd_comm]; exact hgcd j i h
      have hg3 : Nat.gcd (H i).index (H j).index = 3 := by
        rcases h3d with ⟨k, hk⟩
        rw [hk] at hpos hlt ⊢
        omega
      rw [he i, he j, Nat.gcd_mul_left] at hg3
      exact (by omega : Nat.gcd (e i) (e j) = 1)
    -- At most one e_i is even; permute Fin 4 via a swap so e(σ 0), e(σ 1), e(σ 2) are all odd!
    have hodd_pair : ∀ i j : Fin 4, i ≠ j → Odd (e i) ∨ Odd (e j) := by
      intro i j hij
      by_contra h
      push Not at h
      rw [Nat.not_odd_iff_even, Nat.not_odd_iff_even] at h
      have h2d : 2 ∣ Nat.gcd (e i) (e j) :=
        Nat.dvd_gcd (even_iff_two_dvd.mp h.1) (even_iff_two_dvd.mp h.2)
      rw [he_cop i j hij] at h2d
      omega
    have hex_perm : ∃ σ : Equiv.Perm (Fin 4),
        Odd (e (σ 0)) ∧ Odd (e (σ 1)) ∧ Odd (e (σ 2)) := by
      by_cases h0 : Odd (e 0)
      · by_cases h1 : Odd (e 1)
        · by_cases h2 : Odd (e 2)
          · exact ⟨Equiv.refl _, h0, h1, h2⟩
          · exact ⟨Equiv.swap 2 3,
              by rw [show (Equiv.swap (2 : Fin 4) 3) 0 = 0 from by decide]; exact h0,
              by rw [show (Equiv.swap (2 : Fin 4) 3) 1 = 1 from by decide]; exact h1,
              by rw [show (Equiv.swap (2 : Fin 4) 3) 2 = 3 from by decide]
                 exact (hodd_pair 2 3 (by decide)).resolve_left h2⟩
        · exact ⟨Equiv.swap 1 3,
            by rw [show (Equiv.swap (1 : Fin 4) 3) 0 = 0 from by decide]; exact h0,
            by rw [show (Equiv.swap (1 : Fin 4) 3) 1 = 3 from by decide]
               exact (hodd_pair 1 3 (by decide)).resolve_left h1,
            by rw [show (Equiv.swap (1 : Fin 4) 3) 2 = 2 from by decide]
               exact (hodd_pair 1 2 (by decide)).resolve_left h1⟩
      · exact ⟨Equiv.swap 0 3,
          by rw [show (Equiv.swap (0 : Fin 4) 3) 0 = 3 from by decide]
             exact (hodd_pair 0 3 (by decide)).resolve_left h0,
          by rw [show (Equiv.swap (0 : Fin 4) 3) 1 = 1 from by decide]
             exact (hodd_pair 0 1 (by decide)).resolve_left h0,
          by rw [show (Equiv.swap (0 : Fin 4) 3) 2 = 2 from by decide]
             exact (hodd_pair 0 2 (by decide)).resolve_left h0⟩
    obtain ⟨σ, hodd_σ⟩ := hex_perm
    exact k4_all_gcd_three_ordered (fun i => a (σ i)) (fun i => H (σ i)) (fun i => e (σ i))
      (fun i => he (σ i))
      (fun i j hij => he_cop (σ i) (σ j) (σ.injective.ne hij))
      hodd_σ
      (fun i j hij => hdisj (σ.injective.ne hij))

end FiniteGroupTools

section MainResults

/-- **Density Bound (Arbitrary Group)**: For any pairwise disjoint left cosets of finite-index
subgroups in an arbitrary group `G`, `∑ i, (1 : ℚ) / (H i).index ≤ 1`. -/
theorem ppl057_density_bound
    {G : Type*} [Group G] {k : ℕ}
    (a : Fin k → G) (H : Fin k → Subgroup G)
    (hfin : ∀ i, Finite (G ⧸ H i))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    ∑ i : Fin k, (1 : ℚ) / ((H i).index : ℚ) ≤ 1 := by
  obtain ⟨N, hN, hfinN, hidx, hdisj'⟩ := ppl057_finite_reduction a H hfin hdisj
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  have h := density_bound_finite (fun i => QuotientGroup.mk' N (a i))
    (fun i => (H i).map (QuotientGroup.mk' N)) hdisj'
  simpa [hidx] using h

/-- **Pairwise Non-Coprimality (Arbitrary Group)**: Any two disjoint left cosets of finite-index
subgroups have `2 ≤ Nat.gcd (H i).index (H j).index`. -/
theorem ppl057_pairwise_gcd_ge_two
    {G : Type*} [Group G] {k : ℕ}
    (a : Fin k → G) (H : Fin k → Subgroup G)
    (hfin : ∀ i, Finite (G ⧸ H i))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G)))
    {i j : Fin k} (hij : i ≠ j) :
    2 ≤ Nat.gcd (H i).index (H j).index := by
  obtain ⟨N, hN, hfinN, hidx, hdisj'⟩ := ppl057_finite_reduction a H hfin hdisj
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  have h := pairwise_gcd_ge_two_finite (QuotientGroup.mk' N (a i)) (QuotientGroup.mk' N (a j))
    ((H i).map (QuotientGroup.mk' N)) ((H j).map (QuotientGroup.mk' N)) (hdisj' hij)
  simpa [hidx] using h

/-- **Sun Conjecture 4.2 for `k = 2` (Arbitrary Group)**. -/
theorem ppl057_k_eq_two
    {G : Type*} [Group G]
    (a : Fin 2 → G) (H : Fin 2 → Subgroup G)
    (hfin : ∀ i, Finite (G ⧸ H i))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    ∃ i j : Fin 2, i < j ∧ 2 ≤ Nat.gcd (H i).index (H j).index := by
  refine ⟨0, 1, by decide, ?_⟩
  exact ppl057_pairwise_gcd_ge_two a H hfin hdisj (by decide)

/-- **Sun Conjecture 4.2 for `k = 3` (Arbitrary Group, Zhu 2008)**. -/
theorem ppl057_k_eq_three
    {G : Type*} [Group G]
    (a : Fin 3 → G) (H : Fin 3 → Subgroup G)
    (hfin : ∀ i, Finite (G ⧸ H i))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    ∃ i j : Fin 3, i < j ∧ 3 ≤ Nat.gcd (H i).index (H j).index := by
  obtain ⟨N, hN, hfinN, hidx, hdisj'⟩ := ppl057_finite_reduction a H hfin hdisj
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  by_contra h
  push Not at h
  have hgcd2 : ∀ i j : Fin 3, i < j →
      Nat.gcd ((H i).map (QuotientGroup.mk' N)).index
              ((H j).map (QuotientGroup.mk' N)).index = 2 := by
    intro i j hij
    rw [hidx i, hidx j]
    have hge := ppl057_pairwise_gcd_ge_two a H hfin hdisj (ne_of_lt hij)
    have hlt := h i j hij
    omega
  exact no_three_pairwise_gcd_two (fun i => QuotientGroup.mk' N (a i))
    (fun i => (H i).map (QuotientGroup.mk' N)) hdisj' hgcd2

/-- **Sun Conjecture 4.2 for `k = 4` (Arbitrary Group, Zhu 2008)**. -/
theorem ppl057_k_eq_four
    {G : Type*} [Group G]
    (a : Fin 4 → G) (H : Fin 4 → Subgroup G)
    (hfin : ∀ i, Finite (G ⧸ H i))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    ∃ i j : Fin 4, i < j ∧ 4 ≤ Nat.gcd (H i).index (H j).index := by
  obtain ⟨N, hN, hfinN, hidx, hdisj'⟩ := ppl057_finite_reduction a H hfin hdisj
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  by_contra h
  push Not at h
  have hgcd_lt : ∀ i j : Fin 4, i < j →
      Nat.gcd ((H i).map (QuotientGroup.mk' N)).index
              ((H j).map (QuotientGroup.mk' N)).index < 4 := by
    intro i j hij
    rw [hidx i, hidx j]
    exact h i j hij
  exact no_four_pairwise_gcd_lt_four (fun i => QuotientGroup.mk' N (a i))
    (fun i => (H i).map (QuotientGroup.mk' N)) hdisj' hgcd_lt

/-- **Sun Conjecture 4.2 for Divisibility Chains (Arbitrary Group, All `k ≥ 2`)**:
Whenever the subgroup indices are totally ordered by divisibility (e.g. prime powers in a
`p`-group), Sun's conjecture holds for all `k ≥ 2`. -/
theorem ppl057_divisibility_chain
    {G : Type*} [Group G] {k : ℕ} (hk : 2 ≤ k)
    (a : Fin k → G) (H : Fin k → Subgroup G)
    (hfin : ∀ i, Finite (G ⧸ H i))
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G)))
    (hchain : ∀ i j : Fin k, (H i).index ∣ (H j).index ∨ (H j).index ∣ (H i).index) :
    ∃ i j : Fin k, i < j ∧ k ≤ Nat.gcd (H i).index (H j).index := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  obtain ⟨m, _, hm_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
    (fun i => (H i).index) Finset.univ_nonempty
  by_contra hcontra
  push Not at hcontra
  have hpos_all : ∀ i : Fin k, 0 < (H i).index := by
    obtain ⟨N, _, hfinN, hidx, _⟩ := ppl057_finite_reduction a H hfin hdisj
    letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
    intro i; rw [← hidx i]; exact index_pos_of_fintype _
  have hle_km1 : ∀ i : Fin k, i ≠ m → (H i).index ≤ k - 1 := by
    intro i him
    have hlt_gcd : Nat.gcd (H i).index (H m).index < k := by
      rcases lt_or_gt_of_ne him with hlt | hgt
      · exact hcontra i m hlt
      · rw [Nat.gcd_comm]; exact hcontra m i hgt
    have hi_le : (H i).index ≤ (H m).index := hm_max i (Finset.mem_univ i)
    have hdvd : (H i).index ∣ (H m).index := by
      rcases hchain i m with h1 | h2
      · exact h1
      · have hm_le : (H m).index ≤ (H i).index := Nat.le_of_dvd (hpos_all i) h2
        have heq : (H i).index = (H m).index := le_antisymm hi_le hm_le
        rw [heq]
    rw [Nat.gcd_eq_left hdvd] at hlt_gcd
    omega
  have hdens := ppl057_density_bound a H hfin hdisj
  have hkm1_pos : (0 : ℚ) < ((k - 1 : ℕ) : ℚ) := by
    have : 0 < k - 1 := by omega
    exact_mod_cast this
  have hsum_split : ∑ i : Fin k, (1 : ℚ) / ((H i).index : ℚ) =
      (1 : ℚ) / ((H m).index : ℚ) +
      ∑ i ∈ Finset.univ.erase m, (1 : ℚ) / ((H i).index : ℚ) :=
    (Finset.add_sum_erase Finset.univ (fun i => (1 : ℚ) / ((H i).index : ℚ))
      (Finset.mem_univ m)).symm
  have hsum_erase : 1 ≤ ∑ i ∈ Finset.univ.erase m, (1 : ℚ) / ((H i).index : ℚ) := by
    have hterm : ∀ i ∈ Finset.univ.erase m,
        (1 : ℚ) / ((k - 1 : ℕ) : ℚ) ≤ (1 : ℚ) / ((H i).index : ℚ) := by
      intro i hi
      have him : i ≠ m := Finset.ne_of_mem_erase hi
      have h1 : ((H i).index : ℚ) ≤ ((k - 1 : ℕ) : ℚ) := by exact_mod_cast hle_km1 i him
      have h2 : (0 : ℚ) < ((H i).index : ℚ) := by exact_mod_cast hpos_all i
      exact one_div_le_one_div_of_le h2 h1
    calc
      (1 : ℚ) = ((k - 1 : ℕ) : ℚ) * ((1 : ℚ) / ((k - 1 : ℕ) : ℚ)) := by
            field_simp [hkm1_pos.ne']
      _ = ((Finset.univ.erase m).card : ℚ) * ((1 : ℚ) / ((k - 1 : ℕ) : ℚ)) := by
            simp [Finset.card_erase_of_mem (Finset.mem_univ m)]
      _ = ∑ _i ∈ Finset.univ.erase m, (1 : ℚ) / ((k - 1 : ℕ) : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.univ.erase m, (1 : ℚ) / ((H i).index : ℚ) :=
            Finset.sum_le_sum hterm
  have hm_pos : (0 : ℚ) < (1 : ℚ) / ((H m).index : ℚ) := by
    have : (0 : ℚ) < ((H m).index : ℚ) := by exact_mod_cast hpos_all m
    exact one_div_pos.mpr this
  linarith

/-- **Sun Conjecture 4.2 for Finite `p`-Groups (Sun 2004, All `k ≥ 2`)**. -/
theorem ppl057_pgroup
    {G : Type*} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) {k : ℕ} (hk : 2 ≤ k)
    (a : Fin k → G) (H : Fin k → Subgroup G)
    (hdisj : Pairwise fun i j =>
      Disjoint ((fun x => a i * x) '' (H i : Set G))
               ((fun x => a j * x) '' (H j : Set G))) :
    ∃ i j : Fin k, i < j ∧ k ≤ Nat.gcd (H i).index (H j).index := by
  have hfin : ∀ i, Finite (G ⧸ H i) := fun _ => inferInstance
  refine ppl057_divisibility_chain hk a H hfin hdisj ?_
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hpow : ∀ i : Fin k, ∃ e : ℕ, (H i).index = p ^ e := by
    intro i
    have hdvd : (H i).index ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.index_dvd_card (H := H i)
    obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    exact ⟨e, he⟩
  intro i j
  obtain ⟨ei, hei⟩ := hpow i
  obtain ⟨ej, hej⟩ := hpow j
  rw [hei, hej]
  rcases le_total ei ej with hle | hle
  · left; exact pow_dvd_pow p hle
  · right; exact pow_dvd_pow p hle

end MainResults

end PPL057
