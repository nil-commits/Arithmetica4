import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# PPL 030 — Erdős Problem #165: Off-Diagonal Ramsey Numbers `R(3, k)`

**Open Problem Reference:** Erdős Problem #165 (`erdosproblems.com/165`, PPL 030, $250, VERIFIED OPEN):
> Give an asymptotic formula for `R(3, k)`.

**Honest Scope Statement:** This file does **NOT** solve the $250 open prize problem of determining
the exact asymptotic constant `c = lim_{k → ∞} R(3, k) * log k / k^2` (currently bounded in `[1/2, 1]`
by Hefty–Horn–King–Pfender 2025 and Shearer 1983). Instead, it formalizes from scratch in pure Mathlib
(0 custom definitions in public theorem signatures, 0 `sorry`, 0 custom axioms, 0 `native_decide`):

1. **Shearer's (1991) Degree-Sequence Independence Number Theorem** (`α(G) ≥ ∑_v g(d(v))`, strictly
   sharper than Shearer 1983 for every finite degree `d ≥ 2`).
2. **Exact Classical Off-Diagonal Ramsey Numbers** `R(3, 3) = 6`, `R(3, 4) = 9`, `R(3, 5) = 14`
   (upper bounds derived directly from Shearer 1991; lower bounds via explicit circulant graphs
   `C_5`, `Cay(Z/8Z, {±1, 4})`, `Cay(Z/13Z, {±1, ±5})`, with zero `native_decide`).
3. **Shearer's (1983) Independence Number Theorem** (`α(G) ≥ n * (d log d - d + 1) / (d - 1)^2`)
   and its **Variance-Enhanced Refinement** (`+ (2/n) ∑_v (d(v) - d)^2 |f'(d)|`).
4. **Standing 43-Year World-Record Ramsey Upper Bound**: explicit finite-`k` bound and the asymptotic
   bound `R(3, k) ≤ (1 + ε) k^2 / log k` (matching `FormalConjectures/ErdosProblems/165.lean`).
5. **Exact 1-Step Deletion Optimality / Barrier Theorem**: any differentiable `φ` satisfying Shearer's
   1-step neighborhood-deletion differential inequality `(x + 1) φ(x) + (x^2 - x) φ'(x) ≤ 1` on `(1, ∞)`
   satisfies `φ(x) ≤ (x log x - x + 1) / (x - 1)^2` pointwise on `(1, ∞)`.
6. **Finite Asymmetric Lovász Local Lemma** and **Spencer's (1977) Probabilistic Lower Bound**
   `R(3, k) ≥ c (k / log k)^2`.
-/

namespace PPL030

open scoped BigOperators
open Filter

/-! ## Section 1: Triangle-Free Graph & Independence Number Preliminaries -/

section GraphPrelims

private lemma no_triangle_of_cliqueFree {V : Type*} {G : SimpleGraph V}
    (hG : G.CliqueFree 3) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) :
    ¬ G.Adj a c := by
  classical
  intro hac
  have hne_ab : a ≠ b := hab.ne
  have hne_bc : b ≠ c := hbc.ne
  have hne_ac : a ≠ c := hac.ne
  let t : Finset V := {a, b, c}
  have ht_card : t.card = 3 := by
    simp [t, hne_ab, hne_ac, hne_bc]
  have ht_clique : G.IsClique (t : Set V) := by
    intro x hx y hy hxy
    simp only [t, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact hab
    · exact hac
    · exact hab.symm
    · exact (hxy rfl).elim
    · exact hbc
    · exact hac.symm
    · exact hbc.symm
    · exact (hxy rfl).elim
  exact hG t ⟨ht_clique, ht_card⟩

private lemma isIndepSet_neighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (v : V) :
    G.IsIndepSet (G.neighborFinset v : Set V) := by
  intro x hx y hy _hxy hadj
  rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hx hy
  exact no_triangle_of_cliqueFree hG hx hadj hy

private lemma degree_le_indepNum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (v : V) :
    G.degree v ≤ G.indepNum := by
  rw [← G.card_neighborFinset_eq_degree v]
  exact (isIndepSet_neighborFinset G hG v).card_le_indepNum

private lemma indepNum_lt_of_indepSetFree {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hfree : G.IndepSetFree k) :
    G.indepNum < k := by
  by_contra h
  push Not at h
  obtain ⟨s, hs_indep, hs_card⟩ := G.exists_isNIndepSet_indepNum
  have hle : k ≤ s.card := by omega
  obtain ⟨t, hts, ht_card⟩ := Finset.exists_subset_card_eq hle
  have ht_indep : G.IsIndepSet (t : Set V) :=
    fun x hx y hy hxy => hs_indep (hts hx) (hts hy) hxy
  exact hfree t ⟨ht_indep, ht_card⟩

private lemma indepSetFree_of_indepNum_lt {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hlt : G.indepNum < k) :
    G.IndepSetFree k := by
  intro t ⟨ht_indep, ht_card⟩
  have hle : t.card ≤ G.indepNum := ht_indep.card_le_indepNum
  omega

private lemma induce_cliqueFree {V : Type*} {G : SimpleGraph V} (s : Set V)
    (hG : G.CliqueFree 3) : (G.induce s).CliqueFree 3 := by
  classical
  intro t ⟨ht_clq, ht_card⟩
  let t' : Finset V := t.image Subtype.val
  have ht'_card : t'.card = 3 := by
    rw [Finset.card_image_of_injective t Subtype.val_injective, ht_card]
  have ht'_clq : G.IsClique (t' : Set V) := by
    intro x hx y hy hxy
    simp only [t', Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
    exact ht_clq ha hb hab
  exact hG t' ⟨ht'_clq, ht'_card⟩

/-- Deleting `v` and its neighborhood `N(v)` leaves a graph `G_v` with `1 + α(G_v) ≤ α(G)`. -/
private lemma succ_indepNum_deleteClosedNbd_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    let S : Finset V := Finset.univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)
    1 + (G.induce (S : Set V)).indepNum ≤ G.indepNum := by
  intro S
  obtain ⟨t, ht_indep, ht_card⟩ := (G.induce (S : Set V)).exists_isNIndepSet_indepNum
  let t' : Finset V := insert v (t.image Subtype.val)
  have hv_not_mem : v ∉ t.image Subtype.val := by
    intro hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨a, _, ha_eq⟩
    have haS : a.1 ∈ S := a.2
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at haS
    exact haS.1 ha_eq
  have ht'_card : t'.card = 1 + t.card := by
    rw [Finset.card_insert_of_notMem hv_not_mem,
      Finset.card_image_of_injective t Subtype.val_injective]
    omega
  have ht'_indep : G.IsIndepSet (t' : Set V) := by
    intro x hx y hy hxy hadj
    simp only [t', Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff,
      Set.mem_image, Finset.mem_coe] at hx hy
    rcases hx with rfl | ⟨a, ha, rfl⟩
    · rcases hy with rfl | ⟨b, hb, rfl⟩
      · exact hxy rfl
      · have hbS : b.1 ∈ S := b.2
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hbS
        exact hbS.2 hadj
    · rcases hy with rfl | ⟨b, hb, rfl⟩
      · have haS : a.1 ∈ S := a.2
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at haS
        exact haS.2 hadj.symm
      · have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
        exact ht_indep ha hb hab hadj
  have hle : t'.card ≤ G.indepNum := ht'_indep.card_le_indepNum
  omega

/-- Exact cardinality of `S = V \ ({v} ∪ N(v))`: `|S| + 1 + d(v) = |V|`. -/
private lemma card_deleteClosedNbd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (Finset.univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card + 1 + G.degree v =
      Fintype.card V := by
  let S : Finset V := Finset.univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)
  let C : Finset V := insert v (G.neighborFinset v)
  have hdisj : Disjoint S C := by
    rw [Finset.disjoint_left]
    intro w hwS hwC
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hwS
    simp only [C, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hwC
    rcases hwC with rfl | hadj
    · exact hwS.1 rfl
    · exact hwS.2 hadj
  have hunion : S ∪ C = Finset.univ := by
    ext w
    simp only [Finset.mem_union, S, C, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, SimpleGraph.mem_neighborFinset, iff_true]
    by_cases h1 : w = v
    · exact Or.inr (Or.inl h1)
    · by_cases h2 : G.Adj v w
      · exact Or.inr (Or.inr h2)
      · exact Or.inl ⟨h1, h2⟩
  have hv_not_nb : v ∉ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    exact G.loopless.irrefl v
  have hcard : S.card + C.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hC : C.card = 1 + G.degree v := by
    rw [Finset.card_insert_of_notMem hv_not_nb, G.card_neighborFinset_eq_degree v]
    omega
  change S.card + 1 + G.degree v = Fintype.card V
  omega

/-- Exact degree of `w ∈ S = V \ N[v]` in the induced subgraph `G[S]`:
`deg_{G[S]}(w) + |N(v) ∩ N(w)| = deg_G(w)`. -/
private lemma degree_induce_deleteClosedNbd_add_common {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (w : {x : V // x ∈ Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)}) :
    (G.induce (Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) : Set V)).degree w +
      (G.neighborFinset v ∩ G.neighborFinset w.1).card = G.degree w.1 := by
  let S : Finset V := Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
  let H := G.induce (S : Set V)
  have hwS : w.1 ≠ v ∧ ¬ G.Adj v w.1 := by
    have h := w.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hcard_H : H.degree w = (G.neighborFinset w.1 ∩ S).card := by
    rw [← H.card_neighborFinset_eq_degree w]
    refine Finset.card_bij (fun (x : {u : V // u ∈ S}) _ => x.1) ?_ ?_ ?_
    · intro x hx
      rw [SimpleGraph.mem_neighborFinset] at hx
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hx, x.2⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro u hu
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu
      refine ⟨⟨u, hu.2⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hu.1
  rw [hcard_H, ← G.card_neighborFinset_eq_degree w.1]
  have hdisj : Disjoint (G.neighborFinset w.1 ∩ S) (G.neighborFinset v ∩ G.neighborFinset w.1) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    rw [Finset.mem_inter] at hu1 hu2
    have huS := hu1.2
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at huS
    rw [SimpleGraph.mem_neighborFinset] at hu2
    exact huS.2 hu2.1
  have hunion : (G.neighborFinset w.1 ∩ S) ∪ (G.neighborFinset v ∩ G.neighborFinset w.1) =
      G.neighborFinset w.1 := by
    ext u
    simp only [Finset.mem_union, Finset.mem_inter, S, Finset.mem_filter, Finset.mem_univ,
      true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩) <;> assumption
    · intro hwu
      have huv_ne : u ≠ v := by
        rintro rfl
        exact hwS.2 hwu.symm
      by_cases hvu : G.Adj v u
      · exact Or.inr ⟨hvu, hwu⟩
      · exact Or.inl ⟨hwu, huv_ne, hvu⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- Sum of common neighbors `|N(v) ∩ N(w)|` over `w ∈ V \ N[v]` equals `∑_{u ∈ N(v)} (d(u) - 1)`
in any triangle-free graph. -/
private lemma sum_common_deleteClosedNbd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (v : V) :
    ∑ w ∈ Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u),
        (G.neighborFinset v ∩ G.neighborFinset w).card =
      ∑ u ∈ G.neighborFinset v, (G.degree u - 1) := by
  let S : Finset V := Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
  have h1 : ∀ w : V, (G.neighborFinset v ∩ G.neighborFinset w).card =
      ∑ u ∈ G.neighborFinset v, if G.Adj u w then 1 else 0 := by
    intro w
    rw [Finset.card_eq_sum_ones]
    rw [← Finset.sum_filter]
    congr 1
    ext u
    simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
  calc
    ∑ w ∈ S, (G.neighborFinset v ∩ G.neighborFinset w).card
        = ∑ w ∈ S, ∑ u ∈ G.neighborFinset v, if G.Adj u w then 1 else 0 := by
          refine Finset.sum_congr rfl (fun w _ => h1 w)
    _ = ∑ u ∈ G.neighborFinset v, ∑ w ∈ S, if G.Adj u w then 1 else 0 := Finset.sum_comm
    _ = ∑ u ∈ G.neighborFinset v, (G.degree u - 1) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          rw [SimpleGraph.mem_neighborFinset] at hu
          have hfilter : S.filter (fun w => G.Adj u w) = (G.neighborFinset u).erase v := by
            ext w
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
              SimpleGraph.mem_neighborFinset]
            constructor
            · rintro ⟨⟨hwv, _⟩, huw⟩
              exact ⟨hwv, huw⟩
            · rintro ⟨hwv, huw⟩
              exact ⟨⟨hwv, no_triangle_of_cliqueFree hG hu huw⟩, huw⟩
          rw [← Finset.card_filter, hfilter, Finset.card_erase_of_mem,
            G.card_neighborFinset_eq_degree u]
          rw [SimpleGraph.mem_neighborFinset]
          exact hu.symm

end GraphPrelims

/-! ## Section 2: Shearer's (1991) Rational Degree-Sequence Theorem -/

section Shearer1991

/-- Shearer's (1991) rational degree-sequence function:
`g(0) = 1`, `g(d) = (1 + (d^2 - d) g(d - 1)) / (d^2 + 1)`. -/
private def shearerG : ℕ → ℚ
  | 0 => 1
  | d + 1 =>
    let x : ℚ := (d + 1 : ℚ)
    (1 + (x ^ 2 - x) * shearerG d) / (x ^ 2 + 1)

private lemma shearerG_rec (d : ℕ) :
    (((d + 1 : ℚ) ^ 2 + 1) * shearerG (d + 1)) =
      1 + (((d + 1 : ℚ) ^ 2 - (d + 1 : ℚ)) * shearerG d) := by
  simp only [shearerG]
  have hpos : (d + 1 : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  field_simp [hpos]

private lemma shearerG_lower (d : ℕ) : (3 : ℚ) / (2 * d + 4) ≤ shearerG d := by
  induction d with
  | zero =>
    simp [shearerG]
    norm_num
  | succ d ih =>
    have hrec := shearerG_rec d
    have hden1 : (0 : ℚ) < (d + 1 : ℚ) ^ 2 + 1 := by positivity
    have hden2 : (0 : ℚ) < 2 * (d : ℚ) + 4 := by positivity
    have hden3 : (0 : ℚ) < 2 * ((d + 1 : ℕ) : ℚ) + 4 := by positivity
    have hnonneg : (0 : ℚ) ≤ (d + 1 : ℚ) ^ 2 - (d + 1 : ℚ) := by
      have : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
      nlinarith
    have h1 : 1 + ((d + 1 : ℚ) ^ 2 - (d + 1 : ℚ)) * (3 / (2 * d + 4)) ≤
        ((d + 1 : ℚ) ^ 2 + 1) * shearerG (d + 1) := by
      rw [hrec]
      gcongr
    rw [div_le_iff₀ hden3]
    have h2 : 3 * ((d + 1 : ℚ) ^ 2 + 1) ≤
        (1 + ((d + 1 : ℚ) ^ 2 - (d + 1 : ℚ)) * (3 / (2 * d + 4))) * (2 * ((d + 1 : ℕ) : ℚ) + 4) := by
      push_cast
      rw [← sub_nonneg]
      have hne : (2 * (d : ℚ) + 4) ≠ 0 := ne_of_gt hden2
      have hident :
          (1 + ((d + 1 : ℚ) ^ 2 - (d + 1 : ℚ)) * (3 / (2 * d + 4))) * (2 * (d + 1 : ℚ) + 4) -
            3 * ((d + 1 : ℚ) ^ 2 + 1) =
          (4 * (d : ℚ) ^ 2 + 2 * (d : ℚ)) / (2 * (d : ℚ) + 4) := by
        field_simp [hne]
        ring
      rw [hident]
      positivity
    have h3 : 3 * ((d + 1 : ℚ) ^ 2 + 1) ≤
        ((d + 1 : ℚ) ^ 2 + 1) * shearerG (d + 1) * (2 * ((d + 1 : ℕ) : ℚ) + 4) := by
      calc 3 * ((d + 1 : ℚ) ^ 2 + 1)
          ≤ (1 + ((d + 1 : ℚ) ^ 2 - (d + 1 : ℚ)) * (3 / (2 * d + 4))) *
              (2 * ((d + 1 : ℕ) : ℚ) + 4) := h2
        _ ≤ ((d + 1 : ℚ) ^ 2 + 1) * shearerG (d + 1) * (2 * ((d + 1 : ℕ) : ℚ) + 4) := by
              gcongr
    nlinarith

private lemma shearerG_diff_eq (d : ℕ) :
    ((d + 1 : ℚ) ^ 2 + 1) * (shearerG d - shearerG (d + 1)) =
      (d + 2 : ℚ) * shearerG d - 1 := by
  have hrec := shearerG_rec d
  linarith

private lemma shearerG_diff_nonneg (d : ℕ) : 0 ≤ shearerG d - shearerG (d + 1) := by
  have hpos : (0 : ℚ) < (d + 1 : ℚ) ^ 2 + 1 := by positivity
  have heq := shearerG_diff_eq d
  have hlow := shearerG_lower d
  have hden : (0 : ℚ) < 2 * (d : ℚ) + 4 := by positivity
  have h1 : (1 : ℚ) ≤ (d + 2 : ℚ) * shearerG d := by
    calc (1 : ℚ) ≤ (d + 2 : ℚ) * (3 / (2 * d + 4)) := by
          rw [mul_div_assoc', le_div_iff₀ hden]
          linarith
      _ ≤ (d + 2 : ℚ) * shearerG d := by gcongr
  nlinarith

private lemma shearerG_antitone : Antitone shearerG := by
  refine antitone_nat_of_succ_le ?_
  intro d
  linarith [shearerG_diff_nonneg d]

private lemma shearerG_diff_antitone :
    Antitone (fun d : ℕ => shearerG d - shearerG (d + 1)) := by
  refine antitone_nat_of_succ_le ?_
  intro d
  have h1 := shearerG_diff_eq d
  have h2 := shearerG_diff_eq (d + 1)
  have hlow := shearerG_lower d
  have hpos1 : (0 : ℚ) < (d + 1 : ℚ) ^ 2 + 1 := by positivity
  have hpos2 : (0 : ℚ) < (d + 2 : ℚ) ^ 2 + 1 := by positivity
  have hden : (0 : ℚ) < 2 * (d : ℚ) + 4 := by positivity
  have hkey : ((d + 1 : ℚ) ^ 2 + 1) * ((d + 2 : ℚ) ^ 2 + 1) *
      ((shearerG d - shearerG (d + 1)) - (shearerG (d + 1) - shearerG (d + 2))) =
      (2 * (d + 1 : ℚ) ^ 2 + 6 * (d + 1 : ℚ) + 2) * shearerG d - 3 * (d + 2 : ℚ) := by
    have h2' : ((d + 2 : ℚ) ^ 2 + 1) * (shearerG (d + 1) - shearerG (d + 2)) =
        (d + 3 : ℚ) * shearerG (d + 1) - 1 := by
      push_cast at h2
      linarith
    have hsub : shearerG (d + 1) = shearerG d - (shearerG d - shearerG (d + 1)) := by ring
    nlinarith
  have hrhs : 0 ≤ (2 * (d + 1 : ℚ) ^ 2 + 6 * (d + 1 : ℚ) + 2) * shearerG d - 3 * (d + 2 : ℚ) := by
    have hcoeff : (0 : ℚ) ≤ 2 * (d + 1 : ℚ) ^ 2 + 6 * (d + 1 : ℚ) + 2 := by positivity
    have h3 : 3 * (d + 2 : ℚ) ≤
        (2 * (d + 1 : ℚ) ^ 2 + 6 * (d + 1 : ℚ) + 2) * (3 / (2 * d + 4)) := by
      rw [mul_div_assoc', le_div_iff₀ hden]
      nlinarith
    have h4 : (2 * (d + 1 : ℚ) ^ 2 + 6 * (d + 1 : ℚ) + 2) * (3 / (2 * d + 4)) ≤
        (2 * (d + 1 : ℚ) ^ 2 + 6 * (d + 1 : ℚ) + 2) * shearerG d := by
      gcongr
    linarith
  have hprod : (0 : ℚ) < ((d + 1 : ℚ) ^ 2 + 1) * ((d + 2 : ℚ) ^ 2 + 1) := mul_pos hpos1 hpos2
  nlinarith

/-- Discrete convexity of `shearerG`: for `c ≤ d`,
`g(d - c) ≥ g(d) + c * (g(d - 1) - g(d))`. -/
private lemma shearerG_sub_ge (d c : ℕ) (hcd : c ≤ d) :
    shearerG d + (c : ℚ) * (shearerG (d - 1) - shearerG d) ≤ shearerG (d - c) := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hc_le : c ≤ d := Nat.le_of_succ_le hcd
    have ih' := ih hc_le
    have hpos_dc : 1 ≤ d - c := by omega
    have hsub_eq : d - c = (d - (c + 1)) + 1 := by omega
    have hstep : shearerG (d - 1) - shearerG d ≤ shearerG (d - (c + 1)) - shearerG (d - c) := by
      have hle : d - (c + 1) ≤ d - 1 := by omega
      have hanti := shearerG_diff_antitone hle
      dsimp only at hanti
      have h1 : (d - (c + 1)) + 1 = d - c := by omega
      have h2 : (d - 1) + 1 = d := by omega
      rw [h1, h2] at hanti
      exact hanti
    push_cast
    linarith

/-- **Shearer's (1991) Degree-Sequence Theorem**:
Every triangle-free graph `G` satisfies `∑ v, shearerG (G.degree v) ≤ G.indepNum`. -/
private lemma shearer_1991_aux : ∀ n : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n → G.CliqueFree 3 →
    (∑ v : V, shearerG (G.degree v)) ≤ (G.indepNum : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hcard hG
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard
      simp
    · -- For each vertex `v`, deleting `N[v]` gives a lower bound `Δ(v)` on `α(G) - ∑_w g(d(w))`.
      -- Summing over all `v` yields `n * (α(G) - ∑_w g(d(w))) ≥ 0`.
      let S : V → Finset V := fun v => Finset.univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)
      have hstep_v : ∀ v : V,
          (1 : ℚ) + (∑ w ∈ S v,
            (shearerG (G.degree w) +
              ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
                (shearerG (G.degree w - 1) - shearerG (G.degree w)))) ≤ (G.indepNum : ℚ) := by
        intro v
        let H := G.induce (S v : Set V)
        have hSv_lt : Fintype.card (S v : Set V) < n := by
          have hceq : Fintype.card (S v : Set V) = (S v).card := Fintype.card_coe (S v)
          rw [hceq]
          have hcd : (S v).card + 1 + G.degree v = Fintype.card V := card_deleteClosedNbd G v
          omega
        have hH_ih := ih (Fintype.card (S v : Set V)) hSv_lt H rfl (induce_cliqueFree _ hG)
        have halpha : (1 : ℚ) + (H.indepNum : ℚ) ≤ (G.indepNum : ℚ) := by
          exact_mod_cast succ_indepNum_deleteClosedNbd_le G v
        have hsum_eq : ∑ w : (S v : Set V), shearerG (H.degree w) =
            ∑ w ∈ S v, shearerG (G.degree w - (G.neighborFinset v ∩ G.neighborFinset w).card) := by
          refine Finset.sum_bij (fun (w : (S v : Set V)) _ => w.1) ?_ ?_ ?_ ?_
          · intro w _; exact w.2
          · intro a _ b _ hab; exact Subtype.ext hab
          · intro w hw; exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
          · intro w _
            have hdeg : H.degree w + (G.neighborFinset v ∩ G.neighborFinset w.1).card = G.degree w.1 :=
              degree_induce_deleteClosedNbd_add_common G v w
            congr 1
            omega
        have hconv : ∑ w ∈ S v,
            (shearerG (G.degree w) +
              ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
                (shearerG (G.degree w - 1) - shearerG (G.degree w))) ≤
            ∑ w ∈ S v, shearerG (G.degree w - (G.neighborFinset v ∩ G.neighborFinset w).card) := by
          refine Finset.sum_le_sum ?_
          intro w hw
          have hle : (G.neighborFinset v ∩ G.neighborFinset w).card ≤ G.degree w := by
            rw [← G.card_neighborFinset_eq_degree w]
            exact Finset.card_le_card Finset.inter_subset_right
          exact shearerG_sub_ge (G.degree w) _ hle
        linarith
      -- Sum `hstep_v` over all `v : V`
      have hsum_all :
          ∑ v : V, ((1 : ℚ) + (∑ w ∈ S v,
            (shearerG (G.degree w) +
              ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
                (shearerG (G.degree w - 1) - shearerG (G.degree w))))) ≤
          (n : ℚ) * (G.indepNum : ℚ) := by
        calc _ ≤ ∑ _v : V, (G.indepNum : ℚ) := Finset.sum_le_sum (fun v _ => hstep_v v)
          _ = (n : ℚ) * (G.indepNum : ℚ) := by
              rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      -- Now evaluate the three parts of the LHS sum!
      have hpart1 : ∑ v : V, ∑ w ∈ S v, shearerG (G.degree w) =
          ∑ w : V, ((n : ℚ) - 1 - (G.degree w : ℚ)) * shearerG (G.degree w) := by
        have hrewrite : ∀ v : V, ∑ w ∈ S v, shearerG (G.degree w) =
            ∑ w : V, if w ≠ v ∧ ¬ G.Adj v w then shearerG (G.degree w) else 0 := by
          intro v
          rw [← Finset.sum_filter]
        simp_rw [hrewrite]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro w _
        have hsymm : ∀ v : V, (w ≠ v ∧ ¬ G.Adj v w) ↔ (v ≠ w ∧ ¬ G.Adj w v) := by
          intro v
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, fun h => h2 h.symm⟩,
                 fun ⟨h1, h2⟩ => ⟨h1.symm, fun h => h2 h.symm⟩⟩
        simp_rw [hsymm]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        congr 1
        have hcd := card_deleteClosedNbd G w
        have hcd' : ((Finset.univ.filter (fun v => v ≠ w ∧ ¬ G.Adj w v)).card : ℚ) + 1 +
            (G.degree w : ℚ) = (n : ℚ) := by
          rw [← hcard]
          exact_mod_cast hcd
        linarith
      have hpart2 :
          ∑ v : V, ∑ w ∈ S v,
            ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
              (shearerG (G.degree w - 1) - shearerG (G.degree w)) =
          ∑ w : V, (∑ u ∈ G.neighborFinset w, ((G.degree u - 1 : ℕ) : ℚ)) *
              (shearerG (G.degree w - 1) - shearerG (G.degree w)) := by
        have hrewrite : ∀ v : V,
            ∑ w ∈ S v,
              ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
                (shearerG (G.degree w - 1) - shearerG (G.degree w)) =
            ∑ w : V, if w ≠ v ∧ ¬ G.Adj v w then
              ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
                (shearerG (G.degree w - 1) - shearerG (G.degree w)) else 0 := by
          intro v
          rw [← Finset.sum_filter]
        simp_rw [hrewrite]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro w _
        have hsymm : ∀ v : V, (w ≠ v ∧ ¬ G.Adj v w) ↔ (v ≠ w ∧ ¬ G.Adj w v) := by
          intro v
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, fun h => h2 h.symm⟩,
                 fun ⟨h1, h2⟩ => ⟨h1.symm, fun h => h2 h.symm⟩⟩
        simp_rw [hsymm]
        rw [← Finset.sum_filter, ← Finset.sum_mul]
        congr 1
        have hcomm : ∀ v : V,
            (G.neighborFinset v ∩ G.neighborFinset w).card =
            (G.neighborFinset w ∩ G.neighborFinset v).card := by
          intro v; rw [Finset.inter_comm]
        simp_rw [hcomm]
        have hsum_nat := sum_common_deleteClosedNbd G hG w
        exact_mod_cast hsum_nat
      -- Rearrangement inequality over directed edges `(w, u)` with `G.Adj w u`:
      -- `(d(u) - 1) * Δ(w) + (d(w) - 1) * Δ(u) ≥ (d(u) - 1) * Δ(u) + (d(w) - 1) * Δ(w)`
      have hrearr :
          ∑ w : V, ((G.degree w : ℚ) * ((G.degree w - 1 : ℕ) : ℚ)) *
              (shearerG (G.degree w - 1) - shearerG (G.degree w)) ≤
          ∑ w : V, (∑ u ∈ G.neighborFinset w, ((G.degree u - 1 : ℕ) : ℚ)) *
              (shearerG (G.degree w - 1) - shearerG (G.degree w)) := by
        let A : V → ℚ := fun x => ((G.degree x - 1 : ℕ) : ℚ)
        let B : V → ℚ := fun x => shearerG (G.degree x - 1) - shearerG (G.degree x)
        have hpair : ∀ w u : V, G.Adj w u →
            A w * B w + A u * B u ≤ A u * B w + A w * B u := by
          intro w u hwu
          have hdw : 1 ≤ G.degree w := by
            rw [← G.card_neighborFinset_eq_degree w]
            exact Finset.card_pos.mpr ⟨u, (G.mem_neighborFinset w u).mpr hwu⟩
          have hdu : 1 ≤ G.degree u := by
            rw [← G.card_neighborFinset_eq_degree u]
            exact Finset.card_pos.mpr ⟨w, (G.mem_neighborFinset u w).mpr hwu.symm⟩
          have hprod : (A w - A u) * (B w - B u) ≤ 0 := by
            by_cases hle : G.degree w ≤ G.degree u
            · have hA : A w ≤ A u := by
                dsimp [A]
                exact_mod_cast Nat.sub_le_sub_right hle 1
              have hB : B u ≤ B w := by
                dsimp [B]
                have hanti := shearerG_diff_antitone (Nat.sub_le_sub_right hle 1)
                dsimp only at hanti
                have hw1 : G.degree w - 1 + 1 = G.degree w := Nat.sub_add_cancel hdw
                have hu1 : G.degree u - 1 + 1 = G.degree u := Nat.sub_add_cancel hdu
                rw [hw1, hu1] at hanti
                exact hanti
              nlinarith
            · push Not at hle
              have hle' : G.degree u ≤ G.degree w := Nat.le_of_lt hle
              have hA : A u ≤ A w := by
                dsimp [A]
                exact_mod_cast Nat.sub_le_sub_right hle' 1
              have hB : B w ≤ B u := by
                dsimp [B]
                have hanti := shearerG_diff_antitone (Nat.sub_le_sub_right hle' 1)
                dsimp only at hanti
                have hw1 : G.degree w - 1 + 1 = G.degree w := Nat.sub_add_cancel hdw
                have hu1 : G.degree u - 1 + 1 = G.degree u := Nat.sub_add_cancel hdu
                rw [hw1, hu1] at hanti
                exact hanti
              nlinarith
          linarith
        -- Sum `hpair` over all `(w, u)` with `G.Adj w u`
        have hsum_dir :
            ∑ w : V, ∑ u ∈ G.neighborFinset w, (A w * B w + A u * B u) ≤
            ∑ w : V, ∑ u ∈ G.neighborFinset w, (A u * B w + A w * B u) := by
          refine Finset.sum_le_sum (fun w _ => Finset.sum_le_sum (fun u hu => ?_))
          exact hpair w u ((G.mem_neighborFinset w u).mp hu)
        -- Symmetry helper: `∑ w, ∑ u ∈ N(w), f u w = ∑ w, ∑ u ∈ N(w), f w u`
        have hswap : ∀ f : V → V → ℚ,
            ∑ w : V, ∑ u ∈ G.neighborFinset w, f u w =
            ∑ w : V, ∑ u ∈ G.neighborFinset w, f w u := by
          intro f
          have h1 : ∀ w : V, ∑ u ∈ G.neighborFinset w, f u w =
              ∑ u : V, if G.Adj w u then f u w else 0 := by
            intro w
            rw [← Finset.sum_filter]
            congr 1; ext u; simp [SimpleGraph.mem_neighborFinset]
          have h2 : ∀ w : V, ∑ u ∈ G.neighborFinset w, f w u =
              ∑ u : V, if G.Adj w u then f w u else 0 := by
            intro w
            rw [← Finset.sum_filter]
            congr 1; ext u; simp [SimpleGraph.mem_neighborFinset]
          simp_rw [h1, h2]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun u _ => ?_))
          by_cases hadj : G.Adj u w
          · simp [hadj, hadj.symm]
          · have hna : ¬ G.Adj w u := fun h => hadj h.symm
            simp [hadj, hna]
        have hlhs : ∑ w : V, ∑ u ∈ G.neighborFinset w, (A w * B w + A u * B u) =
            2 * ∑ w : V, (G.degree w : ℚ) * A w * B w := by
          simp_rw [Finset.sum_add_distrib]
          rw [hswap (fun u _ => A u * B u)]
          have heq : ∑ w : V, ∑ _u ∈ G.neighborFinset w, A w * B w =
              ∑ w : V, (G.degree w : ℚ) * A w * B w := by
            refine Finset.sum_congr rfl (fun w _ => ?_)
            rw [Finset.sum_const, G.card_neighborFinset_eq_degree w, nsmul_eq_mul]
            ring
          rw [heq]; ring
        have hrhs : ∑ w : V, ∑ u ∈ G.neighborFinset w, (A u * B w + A w * B u) =
            2 * ∑ w : V, (∑ u ∈ G.neighborFinset w, A u) * B w := by
          simp_rw [Finset.sum_add_distrib]
          rw [← hswap (fun u w => A u * B w)]
          have heq : ∑ w : V, ∑ u ∈ G.neighborFinset w, A u * B w =
              ∑ w : V, (∑ u ∈ G.neighborFinset w, A u) * B w := by
            refine Finset.sum_congr rfl (fun w _ => (Finset.sum_mul ..).symm)
          rw [heq]; ring
        have hgoal : ∑ w : V, (G.degree w : ℚ) * A w * B w ≤
            ∑ w : V, (∑ u ∈ G.neighborFinset w, A u) * B w := by
          linarith
        simpa only [A, B, mul_assoc] using hgoal
      -- Exact per-vertex identity: `1 + (n - 1 - d) g(d) + d(d - 1)(g(d - 1) - g(d)) = n * g(d)`!
      have hterm_eq : ∀ w : V,
          (1 : ℚ) + ((n : ℚ) - 1 - (G.degree w : ℚ)) * shearerG (G.degree w) +
            ((G.degree w : ℚ) * ((G.degree w - 1 : ℕ) : ℚ)) *
              (shearerG (G.degree w - 1) - shearerG (G.degree w)) =
          (n : ℚ) * shearerG (G.degree w) := by
        intro w
        cases hd : G.degree w with
        | zero =>
          simp [shearerG]
        | succ d =>
          have hrec := shearerG_rec d
          have hsub : d + 1 - 1 = d := Nat.add_sub_cancel d 1
          rw [hsub]
          push_cast
          linarith
      -- Assemble everything!
      have hLHS_ge : (n : ℚ) * (∑ w : V, shearerG (G.degree w)) ≤
          ∑ v : V, ((1 : ℚ) + (∑ w ∈ S v,
            (shearerG (G.degree w) +
              ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
                (shearerG (G.degree w - 1) - shearerG (G.degree w))))) := by
        have hsplit :
            ∑ v : V, ((1 : ℚ) + (∑ w ∈ S v,
              (shearerG (G.degree w) +
                ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
                  (shearerG (G.degree w - 1) - shearerG (G.degree w))))) =
            (∑ _v : V, (1 : ℚ)) +
              (∑ v : V, ∑ w ∈ S v, shearerG (G.degree w)) +
              (∑ v : V, ∑ w ∈ S v,
                ((G.neighborFinset v ∩ G.neighborFinset w).card : ℚ) *
                  (shearerG (G.degree w - 1) - shearerG (G.degree w))) := by
          simp_rw [Finset.sum_add_distrib]
          ring
        rw [hsplit, hpart1, hpart2]
        have hsum_ident :
            (n : ℚ) * (∑ w : V, shearerG (G.degree w)) =
            (∑ _v : V, (1 : ℚ)) +
              (∑ w : V, ((n : ℚ) - 1 - (G.degree w : ℚ)) * shearerG (G.degree w)) +
              (∑ w : V, ((G.degree w : ℚ) * ((G.degree w - 1 : ℕ) : ℚ)) *
                (shearerG (G.degree w - 1) - shearerG (G.degree w))) := by
          rw [Finset.mul_sum]
          simp_rw [← hterm_eq]
          simp_rw [Finset.sum_add_distrib]
        linarith
      have hn_qpos : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr hn_pos
      nlinarith

/-- Explicit numerical corollary of Shearer (1991) for `G.IndepSetFree k`:
no custom definitions in the statement! -/
private lemma shearer_1991_ramsey_ub {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k)
    (hG : G.CliqueFree 3) (hI : G.IndepSetFree k) :
    (Fintype.card V : ℚ) * shearerG (k - 1) ≤ (k - 1 : ℚ) := by
  have hlt : G.indepNum < k := indepNum_lt_of_indepSetFree hI
  have hle_deg : ∀ v : V, G.degree v ≤ k - 1 := by
    intro v
    have h1 := degree_le_indepNum G hG v
    omega
  have h1 : (Fintype.card V : ℚ) * shearerG (k - 1) ≤ ∑ v : V, shearerG (G.degree v) := by
    calc (Fintype.card V : ℚ) * shearerG (k - 1)
        = ∑ _v : V, shearerG (k - 1) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ v : V, shearerG (G.degree v) :=
          Finset.sum_le_sum (fun v _ => shearerG_antitone (hle_deg v))
  have h2 := shearer_1991_aux (Fintype.card V) G rfl hG
  have h3 : (G.indepNum : ℚ) ≤ (k - 1 : ℚ) := by
    have : G.indepNum ≤ k - 1 := by omega
    have h4 : ((G.indepNum : ℕ) : ℚ) ≤ ((k - 1 : ℕ) : ℚ) := Nat.cast_le.mpr this
    rw [Nat.cast_sub hk, Nat.cast_one] at h4
    exact h4
  linarith

end Shearer1991

/-! ## Section 3: Exact Classical Off-Diagonal Ramsey Numbers `R(3,3)=6`, `R(3,4)=9`, `R(3,5)=14` -/

section ExactRamsey

private lemma shearerG_two : shearerG 2 = 2 / 5 := by
  simp [shearerG]; norm_num

private lemma shearerG_three : shearerG 3 = 17 / 50 := by
  simp [shearerG]; norm_num

private lemma shearerG_four : shearerG 4 = 127 / 425 := by
  simp [shearerG]; norm_num

/-- Upper bound `R(3, 3) ≤ 6`: immediate 1-line corollary of Shearer (1991) (`6 * 2/5 = 12/5 > 2`). -/
theorem ppl030_R33_upper (G : SimpleGraph (Fin 6)) :
    ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 3 := by
  classical
  by_contra h
  push Not at h
  have hub := shearer_1991_ramsey_ub G (by norm_num : 1 ≤ 3) h.1 h.2
  rw [Fintype.card_fin] at hub
  norm_num [shearerG_two] at hub

/-- Upper bound `R(3, 4) ≤ 9`: immediate 1-line corollary of Shearer (1991) (`9 * 17/50 = 153/50 > 3`). -/
theorem ppl030_R34_upper (G : SimpleGraph (Fin 9)) :
    ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 4 := by
  classical
  by_contra h
  push Not at h
  have hub := shearer_1991_ramsey_ub G (by norm_num : 1 ≤ 4) h.1 h.2
  rw [Fintype.card_fin] at hub
  norm_num [shearerG_three] at hub

/-- Upper bound `R(3, 5) ≤ 14`: immediate 1-line corollary of Shearer (1991) (`14 * 127/425 > 4`). -/
theorem ppl030_R35_upper (G : SimpleGraph (Fin 14)) :
    ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 5 := by
  classical
  by_contra h
  push Not at h
  have hub := shearer_1991_ramsey_ub G (by norm_num : 1 ≤ 5) h.1 h.2
  rw [Fintype.card_fin] at hub
  norm_num [shearerG_four] at hub

/-- Circulant graph on `ZMod n` with connection set `S ⊆ ZMod n`. -/
private def circulantZMod (n : ℕ) (S : Finset (ZMod n))
    (hsym : ∀ x ∈ S, -x ∈ S) (h0 : (0 : ZMod n) ∉ S) : SimpleGraph (ZMod n) where
  Adj a b := (b - a) ∈ S
  symm := ⟨fun a b h => by
    have := hsym (b - a) h
    simpa [neg_sub] using this⟩
  loopless := ⟨fun a h => by
    rw [sub_self] at h
    exact h0 h⟩

/-- Translation invariance: any `k`-clique or `k`-independent set in a circulant graph can be
shifted to contain `0`. -/
private lemma circulant_shift_indep {n : ℕ} [NeZero n] {S : Finset (ZMod n)}
    {hsym h0} {G : SimpleGraph (ZMod n)} (hG : G = circulantZMod n S hsym h0)
    {t : Finset (ZMod n)} (ht : G.IsIndepSet (t : Set (ZMod n))) (a : ZMod n) :
    G.IsIndepSet ((t.image (fun x => x - a) : Finset (ZMod n)) : Set (ZMod n)) := by
  subst hG
  intro x hx y hy hxy hadj
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  have huv : u ≠ v := fun h => hxy (congrArg (fun z => z - a) h)
  apply ht hu hv huv
  change (v - u) ∈ S
  have : (v - a) - (u - a) = v - u := by ring
  rw [← this]
  exact hadj

/-- Helper: if `S` is sum-free (`∀ x ∈ S, ∀ y ∈ S, x + y ∉ S`), then `circulantZMod n S` is
triangle-free (`CliqueFree 3`). -/
private lemma circulant_cliqueFree_three {n : ℕ} {S : Finset (ZMod n)}
    {hsym h0} (hsumfree : ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S) :
    (circulantZMod n S hsym h0).CliqueFree 3 := by
  intro t ⟨ht_clq, ht_card⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht_card
  have h1 : (b - a) ∈ S := ht_clq (by simp) (by simp) hab
  have h2 : (c - b) ∈ S := ht_clq (by simp) (by simp) hbc
  have h3 : (c - a) ∈ S := ht_clq (by simp) (by simp) hac
  have hadd : (b - a) + (c - b) = c - a := by ring
  exact hsumfree (b - a) h1 (c - b) h2 (hadd ▸ h3)

/-- Lower bound `R(3, 3) > 5`: `C_5 = Cay(Z/5Z, {1, 4})` is triangle-free with no 3-independent set. -/
theorem ppl030_R33_lower :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ G.IndepSetFree 3 := by
  let S : Finset (ZMod 5) := {1, 4}
  have hsym : ∀ x ∈ S, -x ∈ S := by decide
  have h0 : (0 : ZMod 5) ∉ S := by decide
  let G := circulantZMod 5 S hsym h0
  have hclq : G.CliqueFree 3 := circulant_cliqueFree_three (by decide)
  have hind : G.IndepSetFree 3 := by
    intro t ⟨ht_ind, ht_card⟩
    have hne : t.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hne
    let t' := t.image (fun x => x - a)
    have ht'_card : t'.card = 3 := by
      rw [Finset.card_image_of_injective t (sub_left_injective), ht_card]
    have ht'_ind : G.IsIndepSet (t' : Set (ZMod 5)) := circulant_shift_indep rfl ht_ind a
    have h0_mem : (0 : ZMod 5) ∈ t' := Finset.mem_image.mpr ⟨a, ha, sub_self a⟩
    -- Non-neighbors of `0` other than `0` are `{2, 3}`, which form an edge (`3 - 2 = 1 ∈ S`)!
    have hsub : t'.erase 0 ⊆ ({2, 3} : Finset (ZMod 5)) := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have hna : ¬ G.Adj 0 x := fun hadj => ht'_ind h0_mem hx.2 hx.1.symm hadj
      change ¬ (x - 0) ∈ S at hna
      rw [sub_zero] at hna
      have hdec : ∀ z : ZMod 5, z ≠ 0 → z ∉ S → z ∈ ({2, 3} : Finset (ZMod 5)) := by decide
      exact hdec x hx.1 hna
    have hcard_er : (t'.erase 0).card = 2 := by
      rw [Finset.card_erase_of_mem h0_mem, ht'_card]
    have heq : t'.erase 0 = {2, 3} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard_er]; decide)
    have h2 : (2 : ZMod 5) ∈ t' := by
      apply Finset.mem_of_mem_erase
      rw [heq]; decide
    have h3 : (3 : ZMod 5) ∈ t' := by
      apply Finset.mem_of_mem_erase
      rw [heq]; decide
    exact ht'_ind h2 h3 (by decide) (by decide : ((3 : ZMod 5) - 2) ∈ S)
  -- Transport along `ZMod 5 ≃ Fin 5` (definitionally identical since `ZMod 5 = Fin 5`)
  exact ⟨G, hclq, hind⟩

/-- Lower bound `R(3, 4) > 8`: `Cay(Z/8Z, {1, 4, 7})` is triangle-free with no 4-independent set. -/
theorem ppl030_R34_lower :
    ∃ G : SimpleGraph (Fin 8), G.CliqueFree 3 ∧ G.IndepSetFree 4 := by
  let S : Finset (ZMod 8) := {1, 4, 7}
  have hsym : ∀ x ∈ S, -x ∈ S := by decide
  have h0 : (0 : ZMod 8) ∉ S := by decide
  let G := circulantZMod 8 S hsym h0
  have hclq : G.CliqueFree 3 := circulant_cliqueFree_three (by decide)
  have hind : G.IndepSetFree 4 := by
    intro t ⟨ht_ind, ht_card⟩
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
    let t' := t.image (fun x => x - a)
    have ht'_card : t'.card = 4 := by
      rw [Finset.card_image_of_injective t (sub_left_injective), ht_card]
    have ht'_ind : G.IsIndepSet (t' : Set (ZMod 8)) := circulant_shift_indep rfl ht_ind a
    have h0_mem : (0 : ZMod 8) ∈ t' := Finset.mem_image.mpr ⟨a, ha, sub_self a⟩
    -- Non-neighbors of `0` other than `0` are `{2, 3, 5, 6}`, which partition into 2 edges:
    -- `{2, 3}` (diff 1) and `{5, 6}` (diff 1)!
    -- So `t'.erase 0` has at most 2 elements (1 from each edge), contradicting card 3!
    have hsub : t'.erase 0 ⊆ ({2, 3} : Finset (ZMod 8)) ∪ ({5, 6} : Finset (ZMod 8)) := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have hna : ¬ G.Adj 0 x := fun hadj => ht'_ind h0_mem hx.2 hx.1.symm hadj
      change ¬ (x - 0) ∈ S at hna
      rw [sub_zero] at hna
      have hdec : ∀ z : ZMod 8, z ≠ 0 → z ∉ S →
          z ∈ ({2, 3} : Finset (ZMod 8)) ∪ ({5, 6} : Finset (ZMod 8)) := by decide
      exact hdec x hx.1 hna
    have hpair1 : ((t'.erase 0) ∩ ({2, 3} : Finset (ZMod 8))).card ≤ 1 := by
      by_contra h
      push Not at h
      have hc2 : ({2, 3} : Finset (ZMod 8)).card = 2 := by decide
      have heq : (t'.erase 0) ∩ ({2, 3} : Finset (ZMod 8)) = {2, 3} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      have h2 : (2 : ZMod 8) ∈ t' := by
        have hm : (2 : ZMod 8) ∈ (t'.erase 0) ∩ ({2, 3} : Finset (ZMod 8)) := by rw [heq]; decide
        exact Finset.mem_of_mem_erase (Finset.mem_inter.mp hm).1
      have h3 : (3 : ZMod 8) ∈ t' := by
        have hm : (3 : ZMod 8) ∈ (t'.erase 0) ∩ ({2, 3} : Finset (ZMod 8)) := by rw [heq]; decide
        exact Finset.mem_of_mem_erase (Finset.mem_inter.mp hm).1
      exact ht'_ind h2 h3 (by decide) (by decide : ((3 : ZMod 8) - 2) ∈ S)
    have hpair2 : ((t'.erase 0) ∩ ({5, 6} : Finset (ZMod 8))).card ≤ 1 := by
      by_contra h
      push Not at h
      have hc2 : ({5, 6} : Finset (ZMod 8)).card = 2 := by decide
      have heq : (t'.erase 0) ∩ ({5, 6} : Finset (ZMod 8)) = {5, 6} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      have h5 : (5 : ZMod 8) ∈ t' := by
        have hm : (5 : ZMod 8) ∈ (t'.erase 0) ∩ ({5, 6} : Finset (ZMod 8)) := by rw [heq]; decide
        exact Finset.mem_of_mem_erase (Finset.mem_inter.mp hm).1
      have h6 : (6 : ZMod 8) ∈ t' := by
        have hm : (6 : ZMod 8) ∈ (t'.erase 0) ∩ ({5, 6} : Finset (ZMod 8)) := by rw [heq]; decide
        exact Finset.mem_of_mem_erase (Finset.mem_inter.mp hm).1
      exact ht'_ind h5 h6 (by decide) (by decide : ((6 : ZMod 8) - 5) ∈ S)
    have hle : (t'.erase 0).card ≤
        ((t'.erase 0) ∩ ({2, 3} : Finset (ZMod 8))).card +
        ((t'.erase 0) ∩ ({5, 6} : Finset (ZMod 8))).card := by
      calc (t'.erase 0).card
          = ((t'.erase 0) ∩ (({2, 3} : Finset (ZMod 8)) ∪ {5, 6})).card := by
              rw [Finset.inter_eq_left.mpr hsub]
        _ = (((t'.erase 0) ∩ {2, 3}) ∪ ((t'.erase 0) ∩ {5, 6})).card := by
              rw [Finset.inter_union_distrib_left]
        _ ≤ _ := Finset.card_union_le _ _
    have hcard_er : (t'.erase 0).card = 3 := by
      rw [Finset.card_erase_of_mem h0_mem, ht'_card]
    omega
  exact ⟨G, hclq, hind⟩

/-- Lower bound `R(3, 5) > 13`: `Cay(Z/13Z, {1, 5, 8, 12})` is triangle-free with no
5-independent set. Proved cleanly via 4-edge decomposition `{2,3}, {4,9}, {6,7}, {10,11}`
with zero `native_decide`. -/
theorem ppl030_R35_lower :
    ∃ G : SimpleGraph (Fin 13), G.CliqueFree 3 ∧ G.IndepSetFree 5 := by
  let S : Finset (ZMod 13) := {1, 5, 8, 12}
  have hsym : ∀ x ∈ S, -x ∈ S := by decide
  have h0 : (0 : ZMod 13) ∉ S := by decide
  let G := circulantZMod 13 S hsym h0
  have hclq : G.CliqueFree 3 := circulant_cliqueFree_three (by decide)
  have hind : G.IndepSetFree 5 := by
    intro t ⟨ht_ind, ht_card⟩
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
    let t' := t.image (fun x => x - a)
    have ht'_card : t'.card = 5 := by
      rw [Finset.card_image_of_injective t (sub_left_injective), ht_card]
    have ht'_ind : G.IsIndepSet (t' : Set (ZMod 13)) := circulant_shift_indep rfl ht_ind a
    have h0_mem : (0 : ZMod 13) ∈ t' := Finset.mem_image.mpr ⟨a, ha, sub_self a⟩
    let U := t'.erase 0
    have hU_card : U.card = 4 := by
      rw [Finset.card_erase_of_mem h0_mem, ht'_card]
    -- Helper: any adjacent pair `{x, y}` intersects `U` in at most 1 element.
    have hpair : ∀ x y : ZMod 13, x ≠ y → (y - x) ∈ S → (U ∩ {x, y}).card ≤ 1 := by
      intro x y hxy hadj
      by_contra h
      push Not at h
      have hcard2 : ({x, y} : Finset (ZMod 13)).card = 2 := Finset.card_pair hxy
      have heq : U ∩ {x, y} = {x, y} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      have hxU : x ∈ U := (Finset.mem_inter.mp (heq ▸ Finset.mem_insert_self x {y})).1
      have hyU : y ∈ U :=
        (Finset.mem_inter.mp (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y))).1
      exact ht'_ind (Finset.mem_of_mem_erase hxU) (Finset.mem_of_mem_erase hyU) hxy hadj
    let P1 : Finset (ZMod 13) := {2, 3}
    let P2 : Finset (ZMod 13) := {4, 9}
    let P3 : Finset (ZMod 13) := {6, 7}
    let P4 : Finset (ZMod 13) := {10, 11}
    have h1 : (U ∩ P1).card ≤ 1 := hpair 2 3 (by decide) (by decide)
    have h2 : (U ∩ P2).card ≤ 1 := hpair 4 9 (by decide) (by decide)
    have h3 : (U ∩ P3).card ≤ 1 := hpair 6 7 (by decide) (by decide)
    have h4 : (U ∩ P4).card ≤ 1 := hpair 10 11 (by decide) (by decide)
    have hsub : U ⊆ P1 ∪ P2 ∪ P3 ∪ P4 := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have hna : ¬ G.Adj 0 x := fun hadj => ht'_ind h0_mem hx.2 hx.1.symm hadj
      change ¬ (x - 0) ∈ S at hna
      rw [sub_zero] at hna
      have hdec : ∀ z : ZMod 13, z ≠ 0 → z ∉ S → z ∈ P1 ∪ P2 ∪ P3 ∪ P4 := by decide
      exact hdec x hx.1 hna
    have hcov : U.card ≤ (U ∩ P1).card + (U ∩ P2).card + (U ∩ P3).card + (U ∩ P4).card := by
      have hu : U = (U ∩ P1) ∪ (U ∩ P2) ∪ (U ∩ P3) ∪ (U ∩ P4) := by
        rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left,
          ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hsub]
      calc U.card
          = (((U ∩ P1) ∪ (U ∩ P2) ∪ (U ∩ P3)) ∪ (U ∩ P4)).card := by rw [← hu]
        _ ≤ ((U ∩ P1) ∪ (U ∩ P2) ∪ (U ∩ P3)).card + (U ∩ P4).card := Finset.card_union_le _ _
        _ ≤ ((U ∩ P1) ∪ (U ∩ P2)).card + (U ∩ P3).card + (U ∩ P4).card := by
              have := Finset.card_union_le ((U ∩ P1) ∪ (U ∩ P2)) (U ∩ P3); omega
        _ ≤ (U ∩ P1).card + (U ∩ P2).card + (U ∩ P3).card + (U ∩ P4).card := by
              have := Finset.card_union_le (U ∩ P1) (U ∩ P2); omega
    -- Since `U.card = 4` and each `(U ∩ Pi).card ≤ 1`, EVERY `(U ∩ Pi).card = 1`!
    have hne1 : (U ∩ P1).Nonempty := Finset.card_pos.mp (by omega)
    have hne2 : (U ∩ P2).Nonempty := Finset.card_pos.mp (by omega)
    have hne3 : (U ∩ P3).Nonempty := Finset.card_pos.mp (by omega)
    have hne4 : (U ∩ P4).Nonempty := Finset.card_pos.mp (by omega)
    -- Helper: if `x, y ∈ U`, then `x` and `y` cannot be adjacent!
    have hnaU : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (y - x) ∉ S := fun x hx y hy hxy hadj =>
      ht'_ind (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy hadj
    -- Extract one element from each of P1, P2, P3, P4 and rule out all cases cleanly!
    obtain ⟨x2, hx2⟩ := hne2
    rw [Finset.mem_inter] at hx2
    simp only [P2, Finset.mem_insert, Finset.mem_singleton] at hx2
    obtain ⟨x1, hx1⟩ := hne1; rw [Finset.mem_inter] at hx1
    simp only [P1, Finset.mem_insert, Finset.mem_singleton] at hx1
    obtain ⟨x3, hx3⟩ := hne3; rw [Finset.mem_inter] at hx3
    simp only [P3, Finset.mem_insert, Finset.mem_singleton] at hx3
    obtain ⟨x4, hx4⟩ := hne4; rw [Finset.mem_inter] at hx4
    simp only [P4, Finset.mem_insert, Finset.mem_singleton] at hx4
    rcases hx2.2 with rfl | rfl
    · -- Case `4 ∈ U`: forces `2 ∈ U` (since `4-3=1`), then `6 ∈ U` (since `7-2=5`)
      -- and `11 ∈ U` (since `10-2=8`), contradicting `11 - 6 = 5 ∈ S`!
      rcases hx1.2 with rfl | rfl
      · rcases hx3.2 with rfl | rfl
        · rcases hx4.2 with rfl | rfl
          · exact hnaU 2 hx1.1 10 hx4.1 (by decide) (by decide)
          · exact hnaU 6 hx3.1 11 hx4.1 (by decide) (by decide)
        · exact hnaU 2 hx1.1 7 hx3.1 (by decide) (by decide)
      · exact hnaU 3 hx1.1 4 hx2.1 (by decide) (by decide)
    · -- Case `9 ∈ U`: forces `11 ∈ U` (since `10-9=1`), then `7 ∈ U` (since `11-6=5`)
      -- and `2 ∈ U` (since `11-3=8`), contradicting `7 - 2 = 5 ∈ S`!
      rcases hx4.2 with rfl | rfl
      · exact hnaU 9 hx2.1 10 hx4.1 (by decide) (by decide)
      · rcases hx3.2 with rfl | rfl
        · exact hnaU 6 hx3.1 11 hx4.1 (by decide) (by decide)
        · rcases hx1.2 with rfl | rfl
          · exact hnaU 2 hx1.1 7 hx3.1 (by decide) (by decide)
          · exact hnaU 3 hx1.1 11 hx4.1 (by decide) (by decide)
  exact ⟨G, hclq, hind⟩

/-- Exact classical Ramsey number `R(3, 3) = 6` (pure Mathlib `sInf` characterization). -/
theorem ppl030_exact_R33 :
    sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 3} = 6 := by
  refine le_antisymm ?_ ?_
  · exact Nat.sInf_le ppl030_R33_upper
  · refine le_csInf ⟨6, ppl030_R33_upper⟩ ?_
    intro n hn
    by_contra hlt
    push Not at hlt
    obtain ⟨G, hclq, hind⟩ := ppl030_R33_lower
    let emb : Fin n ↪ Fin 5 := ⟨fun i => ⟨i.1, by omega⟩, fun a b h => Fin.ext (by simpa using h)⟩
    let G' : SimpleGraph (Fin n) := G.comap emb
    have hclq' : G'.CliqueFree 3 := by
      intro t ⟨ht_clq, ht_card⟩
      refine hclq (t.map emb) ⟨?_, by simp [ht_card]⟩
      intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact ht_clq ha hb (fun h => hxy (congrArg emb h))
    have hind' : G'.IndepSetFree 3 := by
      intro t ⟨ht_ind, ht_card⟩
      refine hind (t.map emb) ⟨?_, by simp [ht_card]⟩
      intro x hx y hy hxy hadj
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact ht_ind ha hb (fun h => hxy (congrArg emb h)) hadj
    rcases hn G' with h1 | h2
    · exact h1 hclq'
    · exact h2 hind'

/-- Exact classical Ramsey number `R(3, 4) = 9` (pure Mathlib `sInf` characterization). -/
theorem ppl030_exact_R34 :
    sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 4} = 9 := by
  refine le_antisymm ?_ ?_
  · exact Nat.sInf_le ppl030_R34_upper
  · refine le_csInf ⟨9, ppl030_R34_upper⟩ ?_
    intro n hn
    by_contra hlt
    push Not at hlt
    obtain ⟨G, hclq, hind⟩ := ppl030_R34_lower
    let emb : Fin n ↪ Fin 8 := ⟨fun i => ⟨i.1, by omega⟩, fun a b h => Fin.ext (by simpa using h)⟩
    let G' : SimpleGraph (Fin n) := G.comap emb
    have hclq' : G'.CliqueFree 3 := by
      intro t ⟨ht_clq, ht_card⟩
      refine hclq (t.map emb) ⟨?_, by simp [ht_card]⟩
      intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact ht_clq ha hb (fun h => hxy (congrArg emb h))
    have hind' : G'.IndepSetFree 4 := by
      intro t ⟨ht_ind, ht_card⟩
      refine hind (t.map emb) ⟨?_, by simp [ht_card]⟩
      intro x hx y hy hxy hadj
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact ht_ind ha hb (fun h => hxy (congrArg emb h)) hadj
    rcases hn G' with h1 | h2
    · exact h1 hclq'
    · exact h2 hind'

/-- Exact classical Ramsey number `R(3, 5) = 14` (pure Mathlib `sInf` characterization). -/
theorem ppl030_exact_R35 :
    sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 5} = 14 := by
  refine le_antisymm ?_ ?_
  · exact Nat.sInf_le ppl030_R35_upper
  · refine le_csInf ⟨14, ppl030_R35_upper⟩ ?_
    intro n hn
    by_contra hlt
    push Not at hlt
    obtain ⟨G, hclq, hind⟩ := ppl030_R35_lower
    let emb : Fin n ↪ Fin 13 := ⟨fun i => ⟨i.1, by omega⟩, fun a b h => Fin.ext (by simpa using h)⟩
    let G' : SimpleGraph (Fin n) := G.comap emb
    have hclq' : G'.CliqueFree 3 := by
      intro t ⟨ht_clq, ht_card⟩
      refine hclq (t.map emb) ⟨?_, by simp [ht_card]⟩
      intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact ht_clq ha hb (fun h => hxy (congrArg emb h))
    have hind' : G'.IndepSetFree 5 := by
      intro t ⟨ht_ind, ht_card⟩
      refine hind (t.map emb) ⟨?_, by simp [ht_card]⟩
      intro x hx y hy hxy hadj
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact ht_ind ha hb (fun h => hxy (congrArg emb h)) hadj
    rcases hn G' with h1 | h2
    · exact h1 hclq'
    · exact h2 hind'

end ExactRamsey

/-! ## Section 4: Public Pure-Mathlib Statement of Shearer (1991) -/

section Shearer1991Public

/-- **Shearer's (1991) Degree-Sequence Independence Number Theorem** (pure-Mathlib signature,
0 custom definitions): for any finite triangle-free graph `G` and the rational sequence
`g(0) = 1`, `(d^2 + 1) g(d) = 1 + (d^2 - d) g(d - 1)`, we have `∑ v, g(deg v) ≤ α(G)`.
This strictly improves Shearer's (1983) average-degree bound for every finite degree `d ≥ 2`. -/
theorem ppl030_shearer_1991_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (g : ℕ → ℚ) (hg0 : g 0 = 1)
    (hgrec : ∀ d : ℕ, (((d + 1 : ℚ) ^ 2 + 1) * g (d + 1)) =
      1 + (((d + 1 : ℚ) ^ 2 - (d + 1 : ℚ)) * g d)) :
    (∑ v : V, g (G.degree v)) ≤ (G.indepNum : ℚ) := by
  have hgeq : ∀ d : ℕ, g d = shearerG d := by
    intro d
    induction d with
    | zero => simpa [shearerG] using hg0
    | succ d ih =>
      have h1 := hgrec d
      have h2 := shearerG_rec d
      rw [ih] at h1
      have hpos : (0 : ℚ) < (d + 1 : ℚ) ^ 2 + 1 := by positivity
      nlinarith
  simp_rw [hgeq]
  exact shearer_1991_aux (Fintype.card V) G rfl hG

end Shearer1991Public

/-! ## Section 5: Shearer's (1983) Integral Representation, Variance Refinement, & Ramsey Upper Bound -/

section Shearer1983

/-- Singularity-free integral representation of Shearer's (1983) function:
`f(x) = ∫_0^1 (1 - u) / ((1 - u) + u x) du`.
Equals `1` at `x = 0`, `1/2` at `x = 1`, and `(x log x - x + 1) / (x - 1)^2` for `x > 0, x ≠ 1`. -/
private noncomputable def shearerF (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, (1 - u) / ((1 - u) + u * x)

/-- Integral representation of `f'(x)` for `x > 0`:
`D(x) = - ∫_0^1 u (1 - u) / ((1 - u) + u x)^2 du`. -/
private noncomputable def shearerD (x : ℝ) : ℝ :=
  - ∫ u in (0 : ℝ)..1, (u * (1 - u)) / ((1 - u) + u * x) ^ 2

private lemma denom_pos {x u : ℝ} (hx : 0 < x) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < (1 - u) + u * x := by
  by_cases h : u = 1
  · subst h; linarith
  · have h1 : 0 < 1 - u := sub_pos.mpr (lt_of_le_of_ne hu1 h)
    have h2 : 0 ≤ u * x := mul_nonneg hu0 (le_of_lt hx)
    linarith

private lemma hasDerivAt_affine (x u : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - t) + t * x) (x - 1) u := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) u := by
    have := (hasDerivAt_id' u).const_sub (1 : ℝ)
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => t * x) x u := by
    have := (hasDerivAt_id' u).mul_const x
    simpa using this
  have h3 := h1.add h2
  have heq : (-1 : ℝ) + x = x - 1 := by ring
  rw [heq] at h3
  exact h3

private lemma denom_ne_zero_uIcc {x u : ℝ} (hx : 0 < x) (hu : u ∈ Set.uIcc (0 : ℝ) 1) :
    (1 - u) + u * x ≠ 0 := by
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
  exact ne_of_gt (denom_pos hx hu.1 hu.2)

private lemma shearerF_integrable {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun u : ℝ => (1 - u) / ((1 - u) + u * x)) MeasureTheory.volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1) ?_
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro u hu
  exact ne_of_gt (denom_pos hx hu.1 hu.2)

private lemma shearerD_integrable {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun u : ℝ => (u * (1 - u)) / ((1 - u) + u * x) ^ 2)
      MeasureTheory.volume 0 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1) ?_
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro u hu
  exact pow_ne_zero 2 (ne_of_gt (denom_pos hx hu.1 hu.2))

private lemma shearerF_zero : shearerF 0 = 1 := by
  unfold shearerF
  have hae : ∀ᵐ u ∂MeasureTheory.volume, u ∈ Set.uIoc (0 : ℝ) 1 →
      (1 - u) / ((1 - u) + u * 0) = (1 : ℝ) := by
    have hne1 : ∀ᵐ u ∂MeasureTheory.volume, u ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne1] with u hu hmem
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
    have h1u : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    simp [div_self h1u]
  rw [intervalIntegral.integral_congr_ae hae]
  simp

private lemma shearerF_one : shearerF 1 = 1 / 2 := by
  unfold shearerF
  have heq : (fun u : ℝ => (1 - u) / ((1 - u) + u * 1)) = (fun u : ℝ => 1 - u) := by
    ext u; ring_nf
  rw [heq]
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - u) u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => t) 1 u := hasDerivAt_id' u
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) u u := by
      have := (hasDerivAt_pow 2 u).div_const 2
      simpa [mul_comm] using this
    exact h1.sub h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.sub continuous_id).intervalIntegrable 0 1)]
  norm_num

private lemma shearerF_eq_closed {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    shearerF x = (x * Real.log x - x + 1) / (x - 1) ^ 2 := by
  unfold shearerF
  have hxm1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  let F : ℝ → ℝ := fun u => -u / (x - 1) + (x / (x - 1) ^ 2) * Real.log ((1 - u) + u * x)
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F ((1 - u) / ((1 - u) + u * x)) u := by
    intro u hu
    have ha : (1 - u) + u * x ≠ 0 := denom_ne_zero_uIcc hx hu
    have hlin : HasDerivAt (fun t : ℝ => (1 - t) + t * x) (x - 1) u := hasDerivAt_affine x u
    have hlog : HasDerivAt (fun t : ℝ => Real.log ((1 - t) + t * x))
        ((x - 1) / ((1 - u) + u * x)) u := hlin.log ha
    have hterm1 : HasDerivAt (fun t : ℝ => -t / (x - 1)) (-1 / (x - 1)) u :=
      (hasDerivAt_id' u).neg.div_const (x - 1)
    have hterm2 : HasDerivAt (fun t : ℝ => (x / (x - 1) ^ 2) * Real.log ((1 - t) + t * x))
        ((x / (x - 1) ^ 2) * ((x - 1) / ((1 - u) + u * x))) u :=
      hlog.const_mul (x / (x - 1) ^ 2)
    have hsum : HasDerivAt F
        (-1 / (x - 1) + (x / (x - 1) ^ 2) * ((x - 1) / ((1 - u) + u * x))) u :=
      hterm1.add hterm2
    have hval : -1 / (x - 1) + (x / (x - 1) ^ 2) * ((x - 1) / ((1 - u) + u * x)) =
        (1 - u) / ((1 - u) + u * x) := by
      set a : ℝ := (1 - u) + u * x
      have h1 : (-1 / (x - 1) + (x / (x - 1) ^ 2) * ((x - 1) / a)) * ((x - 1) ^ 2 * a) =
          (1 - u) / a * ((x - 1) ^ 2 * a) := by
        have ha2 : a ≠ 0 := ha
        field_simp [hxm1, ha2]
        dsimp [a]; ring
      have hmul_ne : (x - 1) ^ 2 * a ≠ 0 := mul_ne_zero (pow_ne_zero 2 hxm1) ha
      exact mul_right_cancel₀ hmul_ne h1
    rwa [hval] at hsum
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (shearerF_integrable hx)]
  simp only [F]
  have h1 : (1 - (1 : ℝ)) + 1 * x = x := by ring
  have h0 : (1 - (0 : ℝ)) + 0 * x = 1 := by ring
  rw [h1, h0, Real.log_one]
  field_simp [hxm1]
  ring

private lemma shearerD_eq_closed {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    shearerD x = -(((x + 1) * Real.log x - 2 * (x - 1)) / (x - 1) ^ 3) := by
  unfold shearerD
  congr 1
  have hxm1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  let H : ℝ → ℝ := fun u =>
    (1 / (x - 1) ^ 2) * (-u + ((x + 1) / (x - 1)) * Real.log ((1 - u) + u * x) +
      (x / (x - 1)) * ((1 - u) + u * x)⁻¹)
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt H ((u * (1 - u)) / ((1 - u) + u * x) ^ 2) u := by
    intro u hu
    have ha : (1 - u) + u * x ≠ 0 := denom_ne_zero_uIcc hx hu
    have hlin : HasDerivAt (fun t : ℝ => (1 - t) + t * x) (x - 1) u := hasDerivAt_affine x u
    have hlog : HasDerivAt (fun t : ℝ => Real.log ((1 - t) + t * x))
        ((x - 1) / ((1 - u) + u * x)) u := hlin.log ha
    have hinv : HasDerivAt (fun t : ℝ => ((1 - t) + t * x)⁻¹)
        (-(x - 1) / ((1 - u) + u * x) ^ 2) u := hlin.inv ha
    have h3 : HasDerivAt (fun t : ℝ => (x / (x - 1)) * ((1 - t) + t * x)⁻¹)
        ((x / (x - 1)) * (-(x - 1) / ((1 - u) + u * x) ^ 2)) u :=
      hinv.const_mul (x / (x - 1))
    have h1 : HasDerivAt (fun t : ℝ => -t) (-1) u := (hasDerivAt_id' u).neg
    have h2 : HasDerivAt (fun t : ℝ => ((x + 1) / (x - 1)) * Real.log ((1 - t) + t * x))
        (((x + 1) / (x - 1)) * ((x - 1) / ((1 - u) + u * x))) u :=
      hlog.const_mul ((x + 1) / (x - 1))
    have htot : HasDerivAt H
        ((1 / (x - 1) ^ 2) * (-1 + ((x + 1) / (x - 1)) * ((x - 1) / ((1 - u) + u * x)) +
          (x / (x - 1)) * (-(x - 1) / ((1 - u) + u * x) ^ 2))) u :=
      ((h1.add h2).add h3).const_mul (1 / (x - 1) ^ 2)
    have hval : (1 / (x - 1) ^ 2) * (-1 + ((x + 1) / (x - 1)) * ((x - 1) / ((1 - u) + u * x)) +
          (x / (x - 1)) * (-(x - 1) / ((1 - u) + u * x) ^ 2)) =
        (u * (1 - u)) / ((1 - u) + u * x) ^ 2 := by
      set a : ℝ := (1 - u) + u * x
      have hmul_ne : (x - 1) ^ 2 * a ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hxm1) (pow_ne_zero 2 ha)
      refine mul_right_cancel₀ hmul_ne ?_
      have h1 : (1 / (x - 1) ^ 2) * (-1 + ((x + 1) / (x - 1)) * ((x - 1) / a) +
          (x / (x - 1)) * (-(x - 1) / a ^ 2)) * ((x - 1) ^ 2 * a ^ 2) =
          -a ^ 2 + (x + 1) * a - x := by
        field_simp [hxm1, ha]
        ring
      have h2 : (u * (1 - u)) / a ^ 2 * ((x - 1) ^ 2 * a ^ 2) = u * (1 - u) * (x - 1) ^ 2 := by
        field_simp [ha]
      rw [h1, h2]
      dsimp [a]; ring
    rwa [hval] at htot
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (shearerD_integrable hx)]
  simp only [H]
  have h1 : (1 - (1 : ℝ)) + 1 * x = x := by ring
  have h0 : (1 - (0 : ℝ)) + 0 * x = 1 := by ring
  rw [h1, h0, Real.log_one]
  have hxne : x ≠ 0 := ne_of_gt hx
  field_simp [hxm1, hxne]
  ring

private lemma shearerD_nonpos {x : ℝ} (_hx : 0 < x) : shearerD x ≤ 0 := by
  unfold shearerD
  have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..1, (u * (1 - u)) / ((1 - u) + u * x) ^ 2 := by
    refine intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1) ?_
    intro u hu
    have h1 : 0 ≤ u := hu.1
    have h2 : 0 ≤ 1 - u := by linarith [hu.2]
    positivity
  linarith

/-- Uniform exact ODE for Shearer's function on all `x > 0` (including `x = 1` with zero case split):
`(x + 1) f(x) + (x^2 - x) D(x) = 1`. -/
private lemma shearerF_ode {x : ℝ} (hx : 0 < x) :
    (x + 1) * shearerF x + (x ^ 2 - x) * shearerD x = 1 := by
  let K : ℝ → ℝ := fun u => (x * (u * (1 - u))) / ((1 - u) + u * x)
  let g : ℝ → ℝ := fun u =>
    (x + 1) * ((1 - u) / ((1 - u) + u * x)) -
      (x ^ 2 - x) * ((u * (1 - u)) / ((1 - u) + u * x) ^ 2) - 1
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt K (g u) u := by
    intro u hu
    have ha : (1 - u) + u * x ≠ 0 := denom_ne_zero_uIcc hx hu
    have hnum : HasDerivAt (fun t : ℝ => x * (t * (1 - t))) (x * (1 - 2 * u)) u := by
      have h1 : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * u) u := by
        have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) u := by
          simpa using (hasDerivAt_id' u).const_sub (1 : ℝ)
        have hprod := (hasDerivAt_id' u).mul hsub
        have heq : 1 * (1 - u) + u * (-1) = 1 - 2 * u := by ring
        rwa [heq] at hprod
      exact h1.const_mul x
    have hden : HasDerivAt (fun t : ℝ => (1 - t) + t * x) (x - 1) u := hasDerivAt_affine x u
    have hq := hnum.div hden ha
    have hval : (x * (1 - 2 * u) * ((1 - u) + u * x) - x * (u * (1 - u)) * (x - 1)) /
        ((1 - u) + u * x) ^ 2 = g u := by
      dsimp [g]
      set a : ℝ := (1 - u) + u * x
      have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
      refine mul_right_cancel₀ ha2 ?_
      have h1 : (x * (1 - 2 * u) * a - x * (u * (1 - u)) * (x - 1)) / a ^ 2 * a ^ 2 =
          x * (1 - 2 * u) * a - x * (u * (1 - u)) * (x - 1) := div_mul_cancel₀ _ ha2
      have h2 : ((x + 1) * ((1 - u) / a) - (x ^ 2 - x) * (u * (1 - u) / a ^ 2) - 1) * a ^ 2 =
          (x + 1) * (1 - u) * a - (x ^ 2 - x) * (u * (1 - u)) - a ^ 2 := by
        field_simp [ha]
      rw [h1, h2]
      dsimp [a]; ring
    rwa [hval] at hq
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    (((shearerF_integrable hx).const_mul (x + 1)).sub
      ((shearerD_integrable hx).const_mul (x ^ 2 - x))).sub intervalIntegrable_const
  have hint0 : ∫ u in (0 : ℝ)..1, g u = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hg_int]
    simp [K]
  have hint_eq : ∫ u in (0 : ℝ)..1, g u =
      (x + 1) * shearerF x + (x ^ 2 - x) * shearerD x - 1 := by
    dsimp [g]
    rw [intervalIntegral.integral_sub
      (((shearerF_integrable hx).const_mul (x + 1)).sub
        ((shearerD_integrable hx).const_mul (x ^ 2 - x)))
      intervalIntegrable_const]
    rw [intervalIntegral.integral_sub
      ((shearerF_integrable hx).const_mul (x + 1))
      ((shearerD_integrable hx).const_mul (x ^ 2 - x))]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul,
      shearerF, shearerD]
    ring
  linarith

/-- Uniform tangent-line convexity inequality for Shearer's function:
for all `x > 0` and `y ≥ 0`, `f(x) + D(x) * (y - x) ≤ f(y)`. -/
private lemma shearerF_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    shearerF x + shearerD x * (y - x) ≤ shearerF y := by
  rcases eq_or_lt_of_le hy with rfl | hy_pos
  · -- Case `y = 0`: `f(0) = 1`, and pointwise `(1-u)/a + x*u*(1-u)/a^2 = 1 - (ux/a)^2 ≤ 1`.
    rw [shearerF_zero]
    have hlhs : shearerF x + shearerD x * (0 - x) =
        ∫ u in (0 : ℝ)..1, ((1 - u) / ((1 - u) + u * x) +
          x * ((u * (1 - u)) / ((1 - u) + u * x) ^ 2)) := by
      rw [intervalIntegral.integral_add (shearerF_integrable hx)
        ((shearerD_integrable hx).const_mul x),
        intervalIntegral.integral_const_mul]
      simp only [shearerF, shearerD]
      ring
    rw [hlhs]
    calc ∫ u in (0 : ℝ)..1, ((1 - u) / ((1 - u) + u * x) +
          x * ((u * (1 - u)) / ((1 - u) + u * x) ^ 2))
        ≤ ∫ _u in (0 : ℝ)..1, (1 : ℝ) := by
          refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
            ((shearerF_integrable hx).add ((shearerD_integrable hx).const_mul x))
            intervalIntegrable_const ?_
          intro u hu
          have ha : 0 < (1 - u) + u * x := denom_pos hx hu.1 hu.2
          have hane : (1 - u) + u * x ≠ 0 := ne_of_gt ha
          rw [← sub_nonneg]
          have hident : 1 - ((1 - u) / ((1 - u) + u * x) +
              x * ((u * (1 - u)) / ((1 - u) + u * x) ^ 2)) =
              (u * x) ^ 2 / ((1 - u) + u * x) ^ 2 := by
            field_simp [hane]
            ring
          rw [hident]
          positivity
      _ = 1 := by simp
  · -- Case `y > 0`: pointwise `(1-u)/b - ((1-u)/a - u(1-u)/a^2 * (y-x)) = (1-u)*(a-b)^2/(a^2*b) ≥ 0`.
    have hlhs : shearerF x + shearerD x * (y - x) =
        ∫ u in (0 : ℝ)..1, ((1 - u) / ((1 - u) + u * x) -
          (y - x) * ((u * (1 - u)) / ((1 - u) + u * x) ^ 2)) := by
      rw [intervalIntegral.integral_sub (shearerF_integrable hx)
        ((shearerD_integrable hx).const_mul (y - x)),
        intervalIntegral.integral_const_mul]
      simp only [shearerF, shearerD]
      ring
    rw [hlhs]
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      ((shearerF_integrable hx).sub ((shearerD_integrable hx).const_mul (y - x)))
      (shearerF_integrable hy_pos) ?_
    intro u hu
    have ha : 0 < (1 - u) + u * x := denom_pos hx hu.1 hu.2
    have hb : 0 < (1 - u) + u * y := denom_pos hy_pos hu.1 hu.2
    have hane : (1 - u) + u * x ≠ 0 := ne_of_gt ha
    have hbne : (1 - u) + u * y ≠ 0 := ne_of_gt hb
    have h1u : 0 ≤ 1 - u := by linarith [hu.2]
    rw [← sub_nonneg]
    have hident : (1 - u) / ((1 - u) + u * y) -
        ((1 - u) / ((1 - u) + u * x) -
          (y - x) * ((u * (1 - u)) / ((1 - u) + u * x) ^ 2)) =
        (1 - u) * (u * (y - x)) ^ 2 / (((1 - u) + u * x) ^ 2 * ((1 - u) + u * y)) := by
      field_simp [hane, hbne]
      ring
    rw [hident]
    positivity

/-- Antitonicity of `shearerF` on `[0, ∞)`: `0 ≤ x ≤ y → f(y) ≤ f(x)`. -/
private lemma shearerF_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    shearerF y ≤ shearerF x := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · rw [shearerF_zero]
    rcases eq_or_lt_of_le hxy with rfl | hy_pos
    · rw [shearerF_zero]
    · unfold shearerF
      calc ∫ u in (0 : ℝ)..1, (1 - u) / ((1 - u) + u * y)
          ≤ ∫ _u in (0 : ℝ)..1, (1 : ℝ) := by
            refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
              (shearerF_integrable hy_pos) intervalIntegrable_const ?_
            intro u hu
            have hb : 0 < (1 - u) + u * y := denom_pos hy_pos hu.1 hu.2
            rw [div_le_one hb]
            nlinarith [hu.1]
        _ = 1 := by simp
  · have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
    unfold shearerF
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (shearerF_integrable hy_pos) (shearerF_integrable hx_pos) ?_
    intro u hu
    have ha : 0 < (1 - u) + u * x := denom_pos hx_pos hu.1 hu.2
    have h1u : 0 ≤ 1 - u := by linarith [hu.2]
    have hden_le : (1 - u) + u * x ≤ (1 - u) + u * y := by nlinarith [hu.1]
    exact div_le_div_of_nonneg_left h1u ha hden_le

/-- Exact degree sum of `G - N[v]` in a triangle-free graph:
`∑_{w ∈ S v} deg_{G[S v]}(w) = (∑_{w ∈ V} deg_G(w)) - 2 ∑_{u ∈ N(v)} deg_G(u)`. -/
private lemma sum_degrees_deleteClosedNbd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) (v : V) :
    let S : Finset V := Finset.univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)
    (∑ w : (S : Set V), ((G.induce (S : Set V)).degree w : ℝ)) =
      (∑ w : V, (G.degree w : ℝ)) - 2 * ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) := by
  intro S
  let H := G.induce (S : Set V)
  have hsum_H : (∑ w : (S : Set V), (H.degree w : ℝ)) +
      (∑ w ∈ S, ((G.neighborFinset v ∩ G.neighborFinset w).card : ℝ)) =
      ∑ w ∈ S, (G.degree w : ℝ) := by
    have h1 : (∑ w : (S : Set V), (H.degree w : ℝ)) =
        ∑ w ∈ S, ((G.degree w : ℝ) - ((G.neighborFinset v ∩ G.neighborFinset w).card : ℝ)) := by
      refine Finset.sum_bij (fun (w : (S : Set V)) _ => w.1) ?_ ?_ ?_ ?_
      · intro w _; exact w.2
      · intro a _ b _ hab; exact Subtype.ext hab
      · intro w hw; exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
      · intro w _
        have hdeg := degree_induce_deleteClosedNbd_add_common G v ⟨w.1, w.2⟩
        have hdegR : (H.degree w : ℝ) +
            ((G.neighborFinset v ∩ G.neighborFinset w.1).card : ℝ) = (G.degree w.1 : ℝ) := by
          exact_mod_cast hdeg
        linarith
    rw [h1, Finset.sum_sub_distrib]
    ring
  have hsum_common : (∑ w ∈ S, ((G.neighborFinset v ∩ G.neighborFinset w).card : ℝ)) =
      (∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) - (G.degree v : ℝ) := by
    have hnat := sum_common_deleteClosedNbd G hG v
    have hcast : (∑ w ∈ S, ((G.neighborFinset v ∩ G.neighborFinset w).card : ℝ)) =
        ∑ u ∈ G.neighborFinset v, ((G.degree u - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [hcast]
    have hge1 : ∀ u ∈ G.neighborFinset v, ((G.degree u - 1 : ℕ) : ℝ) = (G.degree u : ℝ) - 1 := by
      intro u hu
      have hpos : 1 ≤ G.degree u := by
        rw [← G.card_neighborFinset_eq_degree u]
        exact Finset.card_pos.mpr ⟨v, (G.mem_neighborFinset u v).mpr
          ((G.mem_neighborFinset v u).mp hu).symm⟩
      rw [Nat.cast_sub hpos, Nat.cast_one]
    rw [Finset.sum_congr rfl hge1, Finset.sum_sub_distrib, Finset.sum_const,
      G.card_neighborFinset_eq_degree v, nsmul_eq_mul, mul_one]
  -- Partition `V` into `S`, `{v}`, and `N(v)`
  have hpart : (∑ w ∈ S, (G.degree w : ℝ)) + (G.degree v : ℝ) +
      (∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) = ∑ w : V, (G.degree w : ℝ) := by
    let C : Finset V := insert v (G.neighborFinset v)
    have hdisj : Disjoint S C := by
      rw [Finset.disjoint_left]
      intro w hwS hwC
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hwS
      simp only [C, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hwC
      rcases hwC with rfl | hadj
      · exact hwS.1 rfl
      · exact hwS.2 hadj
    have hunion : S ∪ C = Finset.univ := by
      ext w
      simp only [Finset.mem_union, S, C, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, SimpleGraph.mem_neighborFinset, iff_true]
      by_cases h1 : w = v
      · exact Or.inr (Or.inl h1)
      · by_cases h2 : G.Adj v w
        · exact Or.inr (Or.inr h2)
        · exact Or.inl ⟨h1, h2⟩
    have hv_nb : v ∉ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]; exact G.loopless.irrefl v
    have hsum_u : (∑ w ∈ S, (G.degree w : ℝ)) + (∑ w ∈ C, (G.degree w : ℝ)) =
        ∑ w : V, (G.degree w : ℝ) := by
      rw [← Finset.sum_union hdisj, hunion]
    have hsum_C : (∑ w ∈ C, (G.degree w : ℝ)) =
        (G.degree v : ℝ) + ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) := by
      exact Finset.sum_insert hv_nb
    linarith
  linarith

/-- Core **Variance-Enhanced Shearer (1983) Theorem** (in integral form, uniform over all `d > 0`):
for any nonempty finite triangle-free graph `G` with average degree `d > 0`,
`n * f(d) + (2 / n) * (∑ v, (deg v - d)^2) * (-D(d)) ≤ α(G)`. -/
private lemma shearer_1983_variance_integral : ∀ n : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n → 0 < n → G.CliqueFree 3 →
    let d : ℝ := (∑ v : V, (G.degree v : ℝ)) / (n : ℝ)
    (n : ℝ) * shearerF d +
      (if d = 0 then 0
       else (2 / (n : ℝ)) * (∑ v : V, ((G.degree v : ℝ) - d) ^ 2) * (-shearerD d)) ≤
      (G.indepNum : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hcard hn_pos hG d
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hd_nonneg : 0 ≤ d := by
      dsimp [d]
      exact div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)) (le_of_lt hnR)
    rcases eq_or_lt_of_le hd_nonneg with hd0 | hd_pos
    · -- Case `d = 0`: every vertex has degree 0, so all of `V` is independent!
      have hd0' : d = 0 := hd0.symm
      rw [if_pos hd0', add_zero, hd0', shearerF_zero, mul_one]
      have hsum0 : ∑ v : V, (G.degree v : ℝ) = 0 := by
        dsimp [d] at hd0'
        exact (div_eq_zero_iff.mp hd0').resolve_right (ne_of_gt hnR)
      have hdeg0 : ∀ v : V, G.degree v = 0 := by
        intro v
        have hle := Finset.single_le_sum (fun w _ => (Nat.cast_nonneg (G.degree w) : (0 : ℝ) ≤ _))
          (Finset.mem_univ v)
        have h0 : (G.degree v : ℝ) = 0 := le_antisymm (by linarith) (Nat.cast_nonneg _)
        exact Nat.cast_eq_zero.mp h0
      have hind_univ : G.IsIndepSet (Finset.univ : Finset V) := by
        intro x _ y _ _ hadj
        have hpos : 0 < G.degree x := by
          rw [← G.card_neighborFinset_eq_degree x]
          exact Finset.card_pos.mpr ⟨y, (G.mem_neighborFinset x y).mpr hadj⟩
        have hx0 := hdeg0 x
        omega
      have hle : (Finset.univ : Finset V).card ≤ G.indepNum := hind_univ.card_le_indepNum
      rw [Finset.card_univ, hcard] at hle
      exact_mod_cast hle
    · -- Case `d > 0`
      have hdne : d ≠ 0 := ne_of_gt hd_pos
      rw [if_neg hdne]
      let S : V → Finset V := fun v => Finset.univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)
      -- For each `v`, `1 + n_v * f(d) + (sumDeg(G_v) - n_v * d) * D(d) ≤ α(G)`
      have hstep_v : ∀ v : V,
          (1 : ℝ) + ((S v).card : ℝ) * shearerF d +
            ((∑ w : (S v : Set V), ((G.induce (S v : Set V)).degree w : ℝ)) -
              ((S v).card : ℝ) * d) * shearerD d ≤ (G.indepNum : ℝ) := by
        intro v
        let H := G.induce (S v : Set V)
        have halpha : (1 : ℝ) + (H.indepNum : ℝ) ≤ (G.indepNum : ℝ) := by
          exact_mod_cast succ_indepNum_deleteClosedNbd_le G v
        have hcard_H : Fintype.card (S v : Set V) = (S v).card := Fintype.card_coe (S v)
        rcases Nat.eq_zero_or_pos (S v).card with hSv0 | hSv_pos
        · -- `S v` is empty, so `sumDeg(H) = 0` and `(S v).card = 0`
          have hEmpty : IsEmpty (S v : Set V) := by
            rw [← Fintype.card_eq_zero_iff, hcard_H]; exact hSv0
          have hsum0 : ∑ w : (S v : Set V), (H.degree w : ℝ) = 0 := by simp
          rw [hSv0, hsum0]
          simp only [Nat.cast_zero, zero_mul, sub_zero, add_zero]
          have hH0 : (0 : ℝ) ≤ (H.indepNum : ℝ) := Nat.cast_nonneg _
          linarith
        · have hSv_lt : (S v).card < n := by
            have hcd : (S v).card + 1 + G.degree v = Fintype.card V := card_deleteClosedNbd G v
            omega
          have hH_ih := ih (S v).card hSv_lt H hcard_H hSv_pos (induce_cliqueFree _ hG)
          let dH : ℝ := (∑ w : (S v : Set V), (H.degree w : ℝ)) / ((S v).card : ℝ)
          have hdH_nonneg : 0 ≤ dH := by
            dsimp [dH]
            exact div_nonneg (Finset.sum_nonneg (fun w _ => Nat.cast_nonneg _))
              (Nat.cast_nonneg _)
          have hvar_nonneg : (0 : ℝ) ≤
              if dH = 0 then 0
              else (2 / ((S v).card : ℝ)) *
                (∑ w : (S v : Set V), ((H.degree w : ℝ) - dH) ^ 2) * (-shearerD dH) := by
            split_ifs with h0
            · exact le_rfl
            · have hdH_pos : 0 < dH := lt_of_le_of_ne hdH_nonneg (Ne.symm h0)
              have hD := shearerD_nonpos hdH_pos
              have hsum_nn : 0 ≤ ∑ w : (S v : Set V), ((H.degree w : ℝ) - dH) ^ 2 :=
                Finset.sum_nonneg (fun _ _ => sq_nonneg _)
              have hnv_nn : (0 : ℝ) ≤ 2 / ((S v).card : ℝ) := by positivity
              have hnegD : 0 ≤ -shearerD dH := by linarith
              exact mul_nonneg (mul_nonneg hnv_nn hsum_nn) hnegD
          have hH_base : ((S v).card : ℝ) * shearerF dH ≤ (H.indepNum : ℝ) := by
            linarith
          have htan := shearerF_tangent hd_pos hdH_nonneg
          have hnvR : (0 : ℝ) < ((S v).card : ℝ) := Nat.cast_pos.mpr hSv_pos
          have hmul : ((S v).card : ℝ) * (shearerF d + shearerD d * (dH - d)) ≤
              ((S v).card : ℝ) * shearerF dH :=
            mul_le_mul_of_nonneg_left htan (le_of_lt hnvR)
          have hsimp : ((S v).card : ℝ) * (shearerF d + shearerD d * (dH - d)) =
              ((S v).card : ℝ) * shearerF d +
                ((∑ w : (S v : Set V), (H.degree w : ℝ)) - ((S v).card : ℝ) * d) * shearerD d := by
            dsimp [dH]
            have hne : ((S v).card : ℝ) ≠ 0 := ne_of_gt hnvR
            field_simp [hne]
          linarith
      -- Sum `hstep_v` over all `v : V`
      have hsum_all :
          ∑ v : V, ((1 : ℝ) + ((S v).card : ℝ) * shearerF d +
            ((∑ w : (S v : Set V), ((G.induce (S v : Set V)).degree w : ℝ)) -
              ((S v).card : ℝ) * d) * shearerD d) ≤
          (n : ℝ) * (G.indepNum : ℝ) := by
        calc _ ≤ ∑ _v : V, (G.indepNum : ℝ) := Finset.sum_le_sum (fun v _ => hstep_v v)
          _ = (n : ℝ) * (G.indepNum : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      -- Compute the exact sums over `v : V`!
      have hsum_deg : ∑ v : V, (G.degree v : ℝ) = (n : ℝ) * d := by
        dsimp [d]
        have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
        field_simp [hne]
      have hsum_Sv : ∑ v : V, ((S v).card : ℝ) = (n : ℝ) * ((n : ℝ) - 1 - d) := by
        have hv_eq : ∀ v : V, ((S v).card : ℝ) = (n : ℝ) - 1 - (G.degree v : ℝ) := by
          intro v
          have hcd : (S v).card + 1 + G.degree v = n := hcard ▸ card_deleteClosedNbd G v
          have hcdR : ((S v).card : ℝ) + 1 + (G.degree v : ℝ) = (n : ℝ) := by exact_mod_cast hcd
          linarith
        simp_rw [hv_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard,
          nsmul_eq_mul, hsum_deg]
        ring
      have hsum_nb_deg : ∑ v : V, ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) =
          ∑ u : V, (G.degree u : ℝ) ^ 2 := by
        have h1 : ∀ v : V, ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) =
            ∑ u : V, if G.Adj v u then (G.degree u : ℝ) else 0 := by
          intro v
          rw [← Finset.sum_filter]
          congr 1; ext u; simp [SimpleGraph.mem_neighborFinset]
        simp_rw [h1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro u _
        have hsym : ∀ v : V, G.Adj v u ↔ G.Adj u v := fun v => ⟨fun h => h.symm, fun h => h.symm⟩
        simp_rw [hsym]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hfilt : (Finset.univ.filter (fun v => G.Adj u v)) = G.neighborFinset u := by
          ext v; simp [SimpleGraph.mem_neighborFinset]
        rw [hfilt, G.card_neighborFinset_eq_degree u]
        ring
      have hsum_Hdeg :
          ∑ v : V, ∑ w : (S v : Set V), ((G.induce (S v : Set V)).degree w : ℝ) =
          (n : ℝ) ^ 2 * d - 2 * ∑ u : V, (G.degree u : ℝ) ^ 2 := by
        have h1 : ∀ v : V,
            (∑ w : (S v : Set V), ((G.induce (S v : Set V)).degree w : ℝ)) =
              (n : ℝ) * d - 2 * ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) := by
          intro v
          rw [sum_degrees_deleteClosedNbd G hG v, hsum_deg]
        simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard,
          nsmul_eq_mul, ← Finset.mul_sum, hsum_nb_deg]
        ring
      -- Variance identity: `∑ u, d(u)^2 = n * d^2 + ∑ u, (d(u) - d)^2`
      have hvar_id : ∑ u : V, (G.degree u : ℝ) ^ 2 =
          (n : ℝ) * d ^ 2 + ∑ u : V, ((G.degree u : ℝ) - d) ^ 2 := by
        have hexp : ∀ u : V, ((G.degree u : ℝ) - d) ^ 2 =
            (G.degree u : ℝ) ^ 2 - 2 * d * (G.degree u : ℝ) + d ^ 2 := fun u => by ring
        simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hsum_deg, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        ring
      -- Simplify the total LHS of `hsum_all` using the exact ODE!
      have hlhs_eval :
          ∑ v : V, ((1 : ℝ) + ((S v).card : ℝ) * shearerF d +
            ((∑ w : (S v : Set V), ((G.induce (S v : Set V)).degree w : ℝ)) -
              ((S v).card : ℝ) * d) * shearerD d) =
          (n : ℝ) * ((n : ℝ) * shearerF d +
            (2 / (n : ℝ)) * (∑ u : V, ((G.degree u : ℝ) - d) ^ 2) * (-shearerD d)) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one,
          hsum_Sv, hsum_Hdeg, hvar_id]
        have hode := shearerF_ode hd_pos
        have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
        have hkey : (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1 - d) * shearerF d +
            ((n : ℝ) ^ 2 * d - 2 * ((n : ℝ) * d ^ 2 + ∑ u : V, ((G.degree u : ℝ) - d) ^ 2) -
              (n : ℝ) * ((n : ℝ) - 1 - d) * d) * shearerD d =
            (n : ℝ) ^ 2 * shearerF d +
              (n : ℝ) * (1 - ((d + 1) * shearerF d + (d ^ 2 - d) * shearerD d)) +
              2 * (∑ u : V, ((G.degree u : ℝ) - d) ^ 2) * (-shearerD d) := by ring
        rw [hkey, hode]
        field_simp [hne]
        ring
      rw [hlhs_eval] at hsum_all
      exact le_of_mul_le_mul_left hsum_all hnR

/-- **Variance-Enhanced Shearer (1983) Independence Number Theorem** (pure-Mathlib signature,
0 custom definitions): for any nonempty finite triangle-free graph `G` with average degree
`d > 0`, `d ≠ 1`,
`n * (d log d - d + 1) / (d - 1)^2 + (2 / n) * (∑ v, (deg v - d)^2) * ((d + 1) log d - 2(d - 1)) / (d - 1)^3 ≤ α(G)`. -/
theorem ppl030_shearer_1983_variance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 0 < Fintype.card V) (hG : G.CliqueFree 3)
    (hd0 : 0 < (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ))
    (hd1 : (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ) ≠ 1) :
    let n : ℝ := (Fintype.card V : ℝ)
    let d : ℝ := (∑ v : V, (G.degree v : ℝ)) / n
    n * ((d * Real.log d - d + 1) / (d - 1) ^ 2) +
      (2 / n) * (∑ v : V, ((G.degree v : ℝ) - d) ^ 2) *
        (((d + 1) * Real.log d - 2 * (d - 1)) / (d - 1) ^ 3) ≤
      (G.indepNum : ℝ) := by
  intro n d
  have hmain := shearer_1983_variance_integral (Fintype.card V) G rfl hn hG
  dsimp only at hmain
  rw [if_neg (ne_of_gt hd0)] at hmain
  rw [shearerF_eq_closed hd0 hd1, shearerD_eq_closed hd0 hd1, neg_neg] at hmain
  exact hmain

/-- **Shearer's (1983) Independence Number Theorem** (pure-Mathlib signature, 0 custom defs):
for any nonempty finite triangle-free graph `G` with average degree `d > 0`, `d ≠ 1`,
`n * (d log d - d + 1) / (d - 1)^2 ≤ α(G)`. -/
theorem ppl030_shearer_1983_independence {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 0 < Fintype.card V) (hG : G.CliqueFree 3)
    (hd0 : 0 < (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ))
    (hd1 : (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ) ≠ 1) :
    let n : ℝ := (Fintype.card V : ℝ)
    let d : ℝ := (∑ v : V, (G.degree v : ℝ)) / n
    n * ((d * Real.log d - d + 1) / (d - 1) ^ 2) ≤ (G.indepNum : ℝ) := by
  intro n d
  have hvar := ppl030_shearer_1983_variance G hn hG hd0 hd1
  dsimp only at hvar
  have hD_nonpos := shearerD_nonpos hd0
  rw [shearerD_eq_closed hd0 hd1] at hD_nonpos
  have hpos_coeff : 0 ≤ ((d + 1) * Real.log d - 2 * (d - 1)) / (d - 1) ^ 3 := by linarith
  have hterm_nn : 0 ≤ (2 / n) * (∑ v : V, ((G.degree v : ℝ) - d) ^ 2) *
      (((d + 1) * Real.log d - 2 * (d - 1)) / (d - 1) ^ 3) := by
    have hn_nn : (0 : ℝ) ≤ 2 / n := by dsimp [n]; positivity
    have hsq_nn : 0 ≤ ∑ v : V, ((G.degree v : ℝ) - d) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact mul_nonneg (mul_nonneg hn_nn hsq_nn) hpos_coeff
  linarith

/-- **Shearer's (1983) Explicit Non-Asymptotic Ramsey Upper Bound** (pure-Mathlib, 0 custom defs):
for all `k ≥ 3`, every triangle-free graph `G` with no `k`-independent set satisfies
`|V| ≤ (k - 1) * (k - 2)^2 / ((k - 1) log(k - 1) - (k - 1) + 1)`. -/
theorem ppl030_shearer_1983_ramsey_explicit {V : Type*} [Fintype V]
    (G : SimpleGraph V) {k : ℕ} (hk : 3 ≤ k)
    (hG : G.CliqueFree 3) (hI : G.IndepSetFree k) :
    (Fintype.card V : ℝ) ≤
      ((k - 1 : ℝ) * (k - 2 : ℝ) ^ 2) /
        ((k - 1 : ℝ) * Real.log (k - 1 : ℝ) - (k - 1 : ℝ) + 1) := by
  classical
  have hk1_gt1 : (1 : ℝ) < (k - 1 : ℝ) := by
    have : (3 : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    linarith
  have hk1_pos : (0 : ℝ) < (k - 1 : ℝ) := by linarith
  have hk1_ne1 : (k - 1 : ℝ) ≠ 1 := ne_of_gt hk1_gt1
  have hf_pos : 0 < shearerF (k - 1 : ℝ) := by
    unfold shearerF
    have hpos : (0 : ℝ) < ∫ u in (0 : ℝ)..1, (1 - u) / ((1 - u) + u * (k - 1 : ℝ)) := by
      refine intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1) ?_ ?_ ⟨0, by norm_num, ?_⟩
      · refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
        intro u hu; exact ne_of_gt (denom_pos hk1_pos hu.1 hu.2)
      · intro u hu
        have hden := denom_pos hk1_pos (le_of_lt hu.1) hu.2
        have h1u : 0 ≤ 1 - u := by linarith [hu.2]
        exact div_nonneg h1u (le_of_lt hden)
      · norm_num
    exact hpos
  have hf_eq := shearerF_eq_closed hk1_pos hk1_ne1
  have hden_pos : 0 < (k - 1 : ℝ) * Real.log (k - 1 : ℝ) - (k - 1 : ℝ) + 1 := by
    rw [hf_eq] at hf_pos
    have hsq : 0 < ((k - 1 : ℝ) - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hk1_ne1)
    exact (div_pos_iff_of_pos_right hsq).mp hf_pos
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hn_pos
  · rw [h0, Nat.cast_zero]
    have hnum_nn : 0 ≤ (k - 1 : ℝ) * (k - 2 : ℝ) ^ 2 := by positivity
    exact div_nonneg hnum_nn (le_of_lt hden_pos)
  · have hlt : G.indepNum < k := indepNum_lt_of_indepSetFree hI
    have hdeg_le : ∀ v : V, (G.degree v : ℝ) ≤ (k - 1 : ℝ) := by
      intro v
      have h1 := degree_le_indepNum G hG v
      have h2 : G.degree v ≤ k - 1 := by omega
      have h3 : (G.degree v : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_le.mpr h2
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at h3
      exact h3
    let d : ℝ := (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ)
    have hnR : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr hn_pos
    have hd_nonneg : 0 ≤ d :=
      div_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (le_of_lt hnR)
    have hd_le : d ≤ (k - 1 : ℝ) := by
      dsimp [d]
      rw [div_le_iff₀ hnR]
      calc ∑ v : V, (G.degree v : ℝ)
          ≤ ∑ _v : V, (k - 1 : ℝ) := Finset.sum_le_sum (fun v _ => hdeg_le v)
        _ = (k - 1 : ℝ) * (Fintype.card V : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    have hmain := shearer_1983_variance_integral (Fintype.card V) G rfl hn_pos hG
    dsimp only at hmain
    have hvar_nn : 0 ≤ (if d = 0 then 0
        else (2 / (Fintype.card V : ℝ)) * (∑ v : V, ((G.degree v : ℝ) - d) ^ 2) *
          (-shearerD d)) := by
      split_ifs with h0
      · exact le_rfl
      · have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm h0)
        have hD := shearerD_nonpos hd_pos
        have hsq : 0 ≤ ∑ v : V, ((G.degree v : ℝ) - d) ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have h2n : 0 ≤ 2 / (Fintype.card V : ℝ) := by positivity
        exact mul_nonneg (mul_nonneg h2n hsq) (by linarith)
    have hbase : (Fintype.card V : ℝ) * shearerF d ≤ (G.indepNum : ℝ) := by linarith
    have hanti : shearerF (k - 1 : ℝ) ≤ shearerF d := shearerF_anti hd_nonneg hd_le
    have hind_le : (G.indepNum : ℝ) ≤ (k - 1 : ℝ) := by
      have : G.indepNum ≤ k - 1 := by omega
      have h3 : (G.indepNum : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_le.mpr this
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at h3
      exact h3
    have hmul : (Fintype.card V : ℝ) * shearerF (k - 1 : ℝ) ≤ (k - 1 : ℝ) := by
      calc (Fintype.card V : ℝ) * shearerF (k - 1 : ℝ)
          ≤ (Fintype.card V : ℝ) * shearerF d :=
            mul_le_mul_of_nonneg_left hanti (le_of_lt hnR)
        _ ≤ (G.indepNum : ℝ) := hbase
        _ ≤ (k - 1 : ℝ) := hind_le
    rw [hf_eq] at hmul
    have hsub2 : (k - 1 : ℝ) - 1 = (k - 2 : ℝ) := by ring
    rw [hsub2] at hmul
    rw [le_div_iff₀ hden_pos]
    have hsq_pos : 0 < (k - 2 : ℝ) ^ 2 := by nlinarith
    rw [← mul_div_assoc, div_le_iff₀ hsq_pos] at hmul
    linarith

/-- **Shearer's (1983) Standing 43-Year World-Record Asymptotic Upper Bound on `R(3, k)`**
(pure-Mathlib statement directly matching `FormalConjectures/ErdosProblems/165.lean`
`erdos_165.variants.upper`):
for every `ε > 0`, eventually as `k → ∞`,
`R(3, k) ≤ (1 + ε) * k^2 / log k`,
where `R(3, k) = sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k}`. -/
theorem ppl030_shearer_1983_ramsey_asymptotic :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k} : ℕ) : ℝ) ≤
        (1 + ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ) := by
  intro ε hε
  rw [Filter.eventually_atTop]
  -- Choose `K₀` large enough that `log k ≥ max (6 / ε + 6) 6` and `k ≥ 16`.
  let M : ℝ := max (6 / ε + 6) 6
  let K₀ : ℕ := Nat.ceil (Real.exp M) + 16
  refine ⟨K₀, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := by omega
  have hk16 : (16 : ℝ) ≤ (k : ℝ) := by
    have : 16 ≤ k := by omega
    exact_mod_cast this
  have hlog_ge : M ≤ Real.log (k : ℝ) := by
    have hexp_le : Real.exp M ≤ (k : ℝ) := by
      calc Real.exp M ≤ (Nat.ceil (Real.exp M) : ℝ) := Nat.le_ceil _
        _ ≤ (K₀ : ℝ) := by dsimp [K₀]; push_cast; linarith
        _ ≤ (k : ℝ) := Nat.cast_le.mpr hk
    calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
      _ ≤ Real.log (k : ℝ) := Real.log_le_log (Real.exp_pos M) hexp_le
  have hlog_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < 6)
    (le_trans (le_max_right _ _) hlog_ge)
  have hlog_6 : 6 ≤ Real.log (k : ℝ) := le_trans (le_max_right _ _) hlog_ge
  have hlog_eps : 6 / ε + 6 ≤ Real.log (k : ℝ) := le_trans (le_max_left _ _) hlog_ge
  -- First, bound `((k - 1) * (k - 2)^2) / ((k - 1) * log(k - 1) - (k - 1) + 1) + 1`
  -- by `(1 + ε) * k^2 / log k`, and then pick `N = floor(bound) + 1` in the Ramsey set!
  let B : ℝ := ((k - 1 : ℝ) * (k - 2 : ℝ) ^ 2) /
      ((k - 1 : ℝ) * Real.log (k - 1 : ℝ) - (k - 1 : ℝ) + 1)
  have hk1_pos : (0 : ℝ) < (k - 1 : ℝ) := by linarith
  have hlog_k1_ge : Real.log (k : ℝ) - 1 ≤ Real.log (k - 1 : ℝ) := by
    have hhalf : (k : ℝ) / 2 ≤ (k - 1 : ℝ) := by linarith
    have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
        _ = 1 := Real.log_exp 1
    calc Real.log (k : ℝ) - 1
        ≤ Real.log (k : ℝ) - Real.log 2 := by linarith
      _ = Real.log ((k : ℝ) / 2) := (Real.log_div (ne_of_gt hk_pos) (by norm_num)).symm
      _ ≤ Real.log (k - 1 : ℝ) := Real.log_le_log (by positivity) hhalf
  have hden_ge : (k - 1 : ℝ) * (Real.log (k : ℝ) - 2) ≤
      (k - 1 : ℝ) * Real.log (k - 1 : ℝ) - (k - 1 : ℝ) + 1 := by
    nlinarith
  have hden_pos : 0 < (k - 1 : ℝ) * Real.log (k - 1 : ℝ) - (k - 1 : ℝ) + 1 := by
    have : 0 < (k - 1 : ℝ) * (Real.log (k : ℝ) - 2) := by nlinarith
    linarith
  have hB_le : B ≤ (k : ℝ) ^ 2 / (Real.log (k : ℝ) - 2) := by
    dsimp [B]
    have hlog2_pos : 0 < Real.log (k : ℝ) - 2 := by linarith
    rw [div_le_div_iff₀ hden_pos hlog2_pos]
    have hnum_le : (k - 2 : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
    calc (k - 1 : ℝ) * (k - 2 : ℝ) ^ 2 * (Real.log (k : ℝ) - 2)
        ≤ (k - 1 : ℝ) * (k : ℝ) ^ 2 * (Real.log (k : ℝ) - 2) := by gcongr
      _ = (k : ℝ) ^ 2 * ((k - 1 : ℝ) * (Real.log (k : ℝ) - 2)) := by ring
      _ ≤ (k : ℝ) ^ 2 * ((k - 1 : ℝ) * Real.log (k - 1 : ℝ) - (k - 1 : ℝ) + 1) := by
          gcongr
  have hB_plus1 : B + 1 ≤ (1 + ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ) := by
    have hlog2_pos : 0 < Real.log (k : ℝ) - 2 := by linarith
    -- Show `k^2 / (log k - 2) + 1 ≤ (1 + ε) * k^2 / log k`:
    -- Multiply by `log k * (log k - 2) > 0`:
    -- Need `k^2 * log k + log k * (log k - 2) ≤ (1 + ε) * k^2 * (log k - 2)`
    -- i.e. `2 * k^2 + log k * (log k - 2) ≤ ε * k^2 * (log k - 2)`.
    -- Since `log k ≤ k` (`Real.log_le_sub_one_of_pos`), `log k * (log k - 2) ≤ k^2`,
    -- so LHS ≤ `3 * k^2`, while RHS ≥ `ε * k^2 * (6 / ε + 4) ≥ 6 * k^2`!
    have hlog_le_k : Real.log (k : ℝ) ≤ (k : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (k : ℝ))
      linarith
    have hprod_pos : 0 < Real.log (k : ℝ) * (Real.log (k : ℝ) - 2) :=
      mul_pos hlog_pos hlog2_pos
    have h3 : (k : ℝ) ^ 2 / (Real.log (k : ℝ) - 2) + 1 ≤
        (1 + ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ) := by
      rw [div_add_one (ne_of_gt hlog2_pos), div_le_div_iff₀ hlog2_pos hlog_pos]
      have hlog_sq : Real.log (k : ℝ) * (Real.log (k : ℝ) - 2) ≤ (k : ℝ) ^ 2 := by nlinarith
      have heps_mul : 6 ≤ ε * (Real.log (k : ℝ) - 2) := by
        have h1 : 6 / ε ≤ Real.log (k : ℝ) - 2 := by linarith
        have := (div_le_iff₀ hε).mp h1
        linarith
      nlinarith
    linarith
  -- Now let `N := Nat.floor B + 1`. Since `B < N`, every `G : SimpleGraph (Fin N)` has
  -- `¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k`, and `(N : ℝ) ≤ B + 1`!
  let N : ℕ := Nat.floor B + 1
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hnum_nn : 0 ≤ (k - 1 : ℝ) * (k - 2 : ℝ) ^ 2 := by positivity
    exact div_nonneg hnum_nn (le_of_lt hden_pos)
  have hN_gt : B < (N : ℝ) := by
    dsimp [N]; push_cast
    exact Nat.lt_floor_add_one B
  have hN_le : (N : ℝ) ≤ B + 1 := by
    dsimp [N]; push_cast
    linarith [Nat.floor_le hB_nonneg]
  have hN_mem : N ∈ {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k} := by
    intro G
    by_contra h
    push Not at h
    have hub := ppl030_shearer_1983_ramsey_explicit G hk3 h.1 h.2
    rw [Fintype.card_fin] at hub
    linarith
  have hsInf_le : sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k} ≤ N :=
    Nat.sInf_le hN_mem
  have hsInf_R : ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n),
      ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k} : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hsInf_le
  linarith

end Shearer1983

/-! ## Section 6: Exact 1-Step Deletion Optimality / Barrier Theorem -/

section Barrier

/-- **Exact 1-Step Deletion Optimality / Barrier Theorem** (pure-Mathlib, 0 custom defs):
ANY function `φ : ℝ → ℝ` continuous on `[1, ∞)` and differentiable on `(1, ∞)` satisfying
Shearer's 1-step neighborhood-deletion differential inequality
`(x + 1) φ(x) + (x^2 - x) φ'(x) ≤ 1` for all `x > 1`
MUST satisfy `φ(x) ≤ (x log x - x + 1) / (x - 1)^2` for EVERY `x > 1`.
This formally proves that 1-step average-degree deletion cannot improve Shearer's 1983 constant
`c = 1` (or even lower-order terms) for any `x > 1`. -/
theorem ppl030_shearer_1983_ode_barrier (φ : ℝ → ℝ)
    (hcont : ContinuousOn φ (Set.Ici 1))
    (hdiff : DifferentiableOn ℝ φ (Set.Ioi 1))
    (hode : ∀ x : ℝ, 1 < x → (x + 1) * φ x + (x ^ 2 - x) * deriv φ x ≤ 1) :
    ∀ x : ℝ, 1 < x → φ x ≤ (x * Real.log x - x + 1) / (x - 1) ^ 2 := by
  let ψ : ℝ → ℝ := fun x => ((x - 1) ^ 2 / x) * φ x - (Real.log x + 1 / x - 1)
  have hψ_cont : ContinuousOn ψ (Set.Ici 1) := by
    have hxne : ∀ x ∈ Set.Ici (1 : ℝ), x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
    have h1 : ContinuousOn (fun x : ℝ => (x - 1) ^ 2 / x) (Set.Ici 1) :=
      ContinuousOn.div (by fun_prop) continuousOn_id hxne
    have h2 : ContinuousOn (fun x : ℝ => Real.log x) (Set.Ici 1) :=
      Real.continuousOn_log.mono (fun x hx => hxne x hx)
    have h3 : ContinuousOn (fun x : ℝ => 1 / x) (Set.Ici 1) :=
      ContinuousOn.div continuousOn_const continuousOn_id hxne
    exact (h1.mul hcont).sub ((h2.add h3).sub continuousOn_const)
  have hψ_deriv : ∀ x ∈ Set.Ioi (1 : ℝ),
      HasDerivAt ψ (((x - 1) / x ^ 2) * ((x + 1) * φ x + (x ^ 2 - x) * deriv φ x - 1)) x := by
    intro x hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hφ_at : HasDerivAt φ (deriv φ x) x :=
      (hdiff.differentiableAt (IsOpen.mem_nhds isOpen_Ioi hx)).hasDerivAt
    have hcoeff : HasDerivAt (fun t : ℝ => (t - 1) ^ 2 / t) ((x ^ 2 - 1) / x ^ 2) x := by
      have hnum : HasDerivAt (fun t : ℝ => (t - 1) ^ 2) (2 * (x - 1)) x := by
        have h := ((hasDerivAt_id' x).sub_const 1).pow 2
        have heq : (2 : ℕ) * (x - 1) ^ (2 - 1) * 1 = 2 * (x - 1) := by norm_num
        rwa [heq] at h
      have hq := hnum.div (hasDerivAt_id' x) hx_ne
      have heq : (2 * (x - 1) * x - (x - 1) ^ 2 * 1) / x ^ 2 = (x ^ 2 - 1) / x ^ 2 := by ring
      rwa [heq] at hq
    have hmul := hcoeff.mul hφ_at
    have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx_ne
    have hinv : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
      have h := (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id' x) hx_ne
      have heq : (0 * x - 1 * 1) / x ^ 2 = -1 / x ^ 2 := by ring
      rwa [heq] at h
    have hsub := hmul.sub ((hlog.add hinv).sub_const 1)
    have hval : ((x ^ 2 - 1) / x ^ 2 * φ x + (x - 1) ^ 2 / x * deriv φ x) - (x⁻¹ + -1 / x ^ 2) =
        ((x - 1) / x ^ 2) * ((x + 1) * φ x + (x ^ 2 - x) * deriv φ x - 1) := by
      field_simp [hx_ne]
      ring
    rwa [hval] at hsub
  have hψ_diff : DifferentiableOn ℝ ψ (interior (Set.Ici (1 : ℝ))) := by
    rw [interior_Ici]
    intro x hx
    exact (hψ_deriv x hx).differentiableAt.differentiableWithinAt
  have hψ_nonpos : ∀ x ∈ interior (Set.Ici (1 : ℝ)), deriv ψ x ≤ 0 := by
    rw [interior_Ici]
    intro x hx
    rw [(hψ_deriv x hx).deriv]
    have h1 : 0 ≤ (x - 1) / x ^ 2 := by
      have : 0 < x - 1 := sub_pos.mpr hx
      have : 0 < x := lt_trans zero_lt_one hx
      positivity
    have h2 : (x + 1) * φ x + (x ^ 2 - x) * deriv φ x - 1 ≤ 0 := by linarith [hode x hx]
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  have hanti : AntitoneOn ψ (Set.Ici 1) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 1) hψ_cont hψ_diff hψ_nonpos
  intro x hx
  have hle : ψ x ≤ ψ 1 := hanti (le_refl (1 : ℝ)) (le_of_lt hx) (le_of_lt hx)
  have hψ1 : ψ 1 = 0 := by simp [ψ]
  rw [hψ1] at hle
  dsimp [ψ] at hle
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hxm1_sq : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hx))
  have hfrac_pos : 0 < (x - 1) ^ 2 / x := div_pos hxm1_sq hx_pos
  have h1 : ((x - 1) ^ 2 / x) * φ x ≤ (x * Real.log x - x + 1) / x := by
    have heq : Real.log x + 1 / x - 1 = (x * Real.log x - x + 1) / x := by
      field_simp [ne_of_gt hx_pos]
      ring
    linarith
  have h2 : (x - 1) ^ 2 * φ x ≤ x * Real.log x - x + 1 := by
    have hmul := mul_le_mul_of_nonneg_right h1 (le_of_lt hx_pos)
    have hxne : x ≠ 0 := ne_of_gt hx_pos
    have hl : ((x - 1) ^ 2 / x) * φ x * x = (x - 1) ^ 2 * φ x := by field_simp [hxne]
    have hr : (x * Real.log x - x + 1) / x * x = x * Real.log x - x + 1 := by field_simp [hxne]
    linarith
  rw [le_div_iff₀ hxm1_sq]
  linarith

end Barrier

/-! ## Section 7: Finite Asymmetric Lovász Local Lemma & Spencer's (1977) Lower Bound -/

section SpencerLLL

/-- Product Bernoulli(`p`) weight on `{0, 1}^α = (α → Bool)`. -/
private def bernWeight {α : Type*} [Fintype α] (p : ℝ) (ω : α → Bool) : ℝ :=
  ∏ e : α, if ω e then p else 1 - p

/-- Product Bernoulli(`p`) probability of a predicate `E : (α → Bool) → Prop`. -/
private noncomputable def bernProb {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ)
    (E : (α → Bool) → Prop) : ℝ :=
  ∑ ω : α → Bool, @ite ℝ (E ω) (Classical.propDecidable _) (bernWeight p ω) 0

private lemma bernWeight_nonneg {α : Type*} [Fintype α] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : α → Bool) : 0 ≤ bernWeight p ω := by
  unfold bernWeight
  refine Finset.prod_nonneg (fun e _ => ?_)
  cases ω e <;> simp <;> linarith

private lemma bernProb_nonneg {α : Type*} [Fintype α] [DecidableEq α] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : (α → Bool) → Prop) : 0 ≤ bernProb p E := by
  classical
  unfold bernProb
  refine Finset.sum_nonneg (fun ω _ => ?_)
  split_ifs
  · exact bernWeight_nonneg hp0 hp1 ω
  · exact le_rfl

private lemma bernProb_mono {α : Type*} [Fintype α] [DecidableEq α] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {E₁ E₂ : (α → Bool) → Prop}
    (himp : ∀ ω, E₁ ω → E₂ ω) : bernProb p E₁ ≤ bernProb p E₂ := by
  classical
  unfold bernProb
  refine Finset.sum_le_sum (fun ω _ => ?_)
  split_ifs with h1 h2
  · exact le_rfl
  · exact (h2 (himp ω h1)).elim
  · exact bernWeight_nonneg hp0 hp1 ω
  · exact le_rfl

private lemma bernProb_congr {α : Type*} [Fintype α] [DecidableEq α] {p : ℝ}
    {E₁ E₂ : (α → Bool) → Prop} (hiff : ∀ ω, E₁ ω ↔ E₂ ω) :
    bernProb p E₁ = bernProb p E₂ := by
  classical
  unfold bernProb
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp [hiff ω]

private lemma bernProb_and_not_eq_sub {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ)
    (A B : (α → Bool) → Prop) :
    bernProb p (fun ω => ¬ A ω ∧ B ω) = bernProb p B - bernProb p (fun ω => A ω ∧ B ω) := by
  classical
  unfold bernProb
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB]

private lemma bernProb_true {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ) :
    bernProb p (fun (_ : α → Bool) => True) = 1 := by
  unfold bernProb bernWeight
  let f : α → Bool → ℝ := fun _ b => if b then p else 1 - p
  have hsum : (∑ ω : α → Bool,
      @ite ℝ True (Classical.propDecidable _) (∏ e : α, if ω e then p else 1 - p) 0) =
      ∑ ω : α → Bool, ∏ e : α, f e (ω e) :=
    Finset.sum_congr rfl (fun ω _ => if_pos trivial)
  rw [hsum, ← Fintype.prod_sum f]
  have h1 : ∀ e : α, (∑ b : Bool, f e b) = 1 := by
    intro _; simp [f]
  simp_rw [h1]
  simp

private lemma bernProb_cyl_true {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ)
    (S : Finset α) :
    bernProb p (fun ω => ∀ e ∈ S, ω e = true) = p ^ S.card := by
  unfold bernProb bernWeight
  let f : α → Bool → ℝ := fun e b =>
    if e ∈ S then (if b then p else 0) else (if b then p else 1 - p)
  have hterm : ∀ ω : α → Bool,
      @ite ℝ (∀ e ∈ S, ω e = true) (Classical.propDecidable _)
        (∏ e : α, if ω e then p else 1 - p) 0 =
        ∏ e : α, f e (ω e) := by
    intro ω
    split_ifs with h
    · refine Finset.prod_congr rfl (fun e _ => ?_)
      dsimp [f]
      by_cases he : e ∈ S
      · simp [he, h e he]
      · simp [he]
    · push Not at h
      rcases h with ⟨e₀, he₀S, he₀f⟩
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ e₀) ?_
      have hfalse : ω e₀ = false := Bool.eq_false_iff.mpr he₀f
      dsimp [f]
      rw [if_pos he₀S, hfalse]
      rfl
  calc (∑ ω : α → Bool,
        @ite ℝ (∀ e ∈ S, ω e = true) (Classical.propDecidable _)
          (∏ e : α, if ω e then p else 1 - p) 0)
      = ∑ ω : α → Bool, ∏ e : α, f e (ω e) := Finset.sum_congr rfl (fun ω _ => hterm ω)
    _ = ∏ e : α, ∑ b : Bool, f e b := (Fintype.prod_sum f).symm
    _ = p ^ S.card := by
        have hfac : ∀ e : α, (∑ b : Bool, f e b) = if e ∈ S then p else 1 := by
          intro e
          dsimp [f]
          by_cases he : e ∈ S <;> simp [he]
        simp_rw [hfac]
        simp

private lemma bernProb_cyl_false {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ)
    (S : Finset α) :
    bernProb p (fun ω => ∀ e ∈ S, ω e = false) = (1 - p) ^ S.card := by
  unfold bernProb bernWeight
  let f : α → Bool → ℝ := fun e b =>
    if e ∈ S then (if b then 0 else 1 - p) else (if b then p else 1 - p)
  have hterm : ∀ ω : α → Bool,
      @ite ℝ (∀ e ∈ S, ω e = false) (Classical.propDecidable _)
        (∏ e : α, if ω e then p else 1 - p) 0 =
        ∏ e : α, f e (ω e) := by
    intro ω
    split_ifs with h
    · refine Finset.prod_congr rfl (fun e _ => ?_)
      dsimp [f]
      by_cases he : e ∈ S
      · simp [he, h e he]
      · simp [he]
    · push Not at h
      rcases h with ⟨e₀, he₀S, he₀t⟩
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ e₀) ?_
      have htrue : ω e₀ = true := by cases hv : ω e₀ <;> simp_all
      dsimp [f]
      rw [if_pos he₀S, htrue]
      rfl
  calc (∑ ω : α → Bool,
        @ite ℝ (∀ e ∈ S, ω e = false) (Classical.propDecidable _)
          (∏ e : α, if ω e then p else 1 - p) 0)
      = ∑ ω : α → Bool, ∏ e : α, f e (ω e) := Finset.sum_congr rfl (fun ω _ => hterm ω)
    _ = ∏ e : α, ∑ b : Bool, f e b := (Fintype.prod_sum f).symm
    _ = (1 - p) ^ S.card := by
        have hfac : ∀ e : α, (∑ b : Bool, f e b) = if e ∈ S then 1 - p else 1 := by
          intro e
          dsimp [f]
          by_cases he : e ∈ S <;> simp [he]
        simp_rw [hfac]
        simp

/-- Exact independence of events supported on disjoint coordinate subsets in `{0, 1}^α`. -/
private lemma bernProb_indep_of_disjoint {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ)
    {S₁ S₂ : Finset α} (hdisj : Disjoint S₁ S₂)
    {E₁ E₂ : (α → Bool) → Prop}
    (h₁ : ∀ ω ω', (∀ e ∈ S₁, ω e = ω' e) → (E₁ ω ↔ E₁ ω'))
    (h₂ : ∀ ω ω', (∀ e ∈ S₂, ω e = ω' e) → (E₂ ω ↔ E₂ ω')) :
    bernProb p (fun ω => E₁ ω ∧ E₂ ω) = bernProb p E₁ * bernProb p E₂ := by
  classical
  -- Split `α` into `A := {e : α // e ∈ S₁}` and `B := {e : α // e ∉ S₁}`
  let A := {e : α // e ∈ S₁}
  let B := {e : α // e ∉ S₁}
  let combine : (A → Bool) × (B → Bool) → (α → Bool) :=
    fun ⟨ω₁, ω₂⟩ e => if h : e ∈ S₁ then ω₁ ⟨e, h⟩ else ω₂ ⟨e, h⟩
  let split : (α → Bool) → (A → Bool) × (B → Bool) :=
    fun ω => (fun a => ω a.1, fun b => ω b.1)
  have hcomb_split : ∀ ω, combine (split ω) = ω := by
    intro ω; ext e; dsimp [combine, split]; split_ifs <;> rfl
  have hsplit_comb : ∀ x, split (combine x) = x := by
    rintro ⟨ω₁, ω₂⟩
    ext a
    · simp [combine, split, a.2]
    · simp [combine, split, a.2]
  let eEquiv : ((A → Bool) × (B → Bool)) ≃ (α → Bool) :=
    ⟨combine, split, hsplit_comb, hcomb_split⟩
  -- Weight factors multiplicatively under `combine`
  have hweight : ∀ (ω₁ : A → Bool) (ω₂ : B → Bool),
      bernWeight p (combine (ω₁, ω₂)) = bernWeight p ω₁ * bernWeight p ω₂ := by
    intro ω₁ ω₂
    unfold bernWeight
    have hsplit_prod : (∏ e : α, if combine (ω₁, ω₂) e then p else 1 - p) =
        (∏ e ∈ S₁, if combine (ω₁, ω₂) e then p else 1 - p) *
        (∏ e ∈ Finset.univ.filter (fun e => e ∉ S₁), if combine (ω₁, ω₂) e then p else 1 - p) := by
      rw [← Finset.prod_union]
      · congr 1; ext e; simp [em]
      · rw [Finset.disjoint_left]; intro e he1 he2; simp at he2; exact he2 he1
    rw [hsplit_prod]
    congr 1
    · refine Finset.prod_bij (fun e he => (⟨e, he⟩ : A)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro a _; exact ⟨a.1, a.2, rfl⟩
      · intro e he; simp [combine, he]
    · refine Finset.prod_bij (fun e he => (⟨e, (Finset.mem_filter.mp he).2⟩ : B)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro b _; exact ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, rfl⟩
      · intro e he
        have hnot : e ∉ S₁ := (Finset.mem_filter.mp he).2
        simp [combine, hnot]
  -- Define projected predicates on `A → Bool` and `B → Bool`
  let E₁' : (A → Bool) → Prop := fun ω₁ => E₁ (combine (ω₁, fun _ => false))
  let E₂' : (B → Bool) → Prop := fun ω₂ => E₂ (combine (fun _ => false, ω₂))
  have hE₁ : ∀ ω₁ ω₂, E₁ (combine (ω₁, ω₂)) ↔ E₁' ω₁ := by
    intro ω₁ ω₂
    refine h₁ _ _ (fun e he => ?_)
    simp [combine, he]
  have hE₂ : ∀ ω₁ ω₂, E₂ (combine (ω₁, ω₂)) ↔ E₂' ω₂ := by
    intro ω₁ ω₂
    refine h₂ _ _ (fun e he => ?_)
    have hnot : e ∉ S₁ := Finset.disjoint_right.mp hdisj he
    simp [combine, hnot]
  -- General factoring lemma for `bernProb p (fun ω => P₁ (split ω).1 ∧ P₂ (split ω).2)`
  have hfact : ∀ (P₁ : (A → Bool) → Prop) (P₂ : (B → Bool) → Prop),
      bernProb p (fun ω => P₁ (split ω).1 ∧ P₂ (split ω).2) =
        bernProb p P₁ * bernProb p P₂ := by
    intro P₁ P₂
    unfold bernProb
    dsimp only
    let g : (α → Bool) → ℝ := fun ω =>
      @ite ℝ (P₁ (split ω).1 ∧ P₂ (split ω).2) (Classical.propDecidable _) (bernWeight p ω) 0
    have hcomp : (∑ ω : α → Bool, g ω) = ∑ x : (A → Bool) × (B → Bool), g (eEquiv x) :=
      (Equiv.sum_comp eEquiv g).symm
    change (∑ ω : α → Bool, g ω) = _
    rw [hcomp, Fintype.sum_prod_type]
    have hrew : ∀ ω₁ ω₂, g (eEquiv (ω₁, ω₂)) =
        (@ite ℝ (P₁ ω₁) (Classical.propDecidable _) (bernWeight p ω₁) 0) *
        (@ite ℝ (P₂ ω₂) (Classical.propDecidable _) (bernWeight p ω₂) 0) := by
      intro ω₁ ω₂
      dsimp [g, eEquiv]
      have hs : split (combine (ω₁, ω₂)) = (ω₁, ω₂) := hsplit_comb (ω₁, ω₂)
      by_cases hA : P₁ ω₁ <;> by_cases hB : P₂ ω₂ <;> simp [hs, hweight, hA, hB]
    simp_rw [hrew, ← Finset.mul_sum, ← Finset.sum_mul]
  have h12 : bernProb p (fun ω => E₁ ω ∧ E₂ ω) = bernProb p E₁' * bernProb p E₂' := by
    rw [← hfact E₁' E₂']
    refine bernProb_congr (fun ω => ?_)
    have h1 := hE₁ (split ω).1 (split ω).2
    have h2 := hE₂ (split ω).1 (split ω).2
    rw [hcomb_split ω] at h1 h2
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  have h1_eq : bernProb p E₁ = bernProb p E₁' := by
    have := hfact E₁' (fun _ => True)
    rw [bernProb_true, mul_one] at this
    rw [← this]
    refine bernProb_congr (fun ω => ?_)
    have h1 := hE₁ (split ω).1 (split ω).2
    rw [hcomb_split ω] at h1
    simp [h1]
  have h2_eq : bernProb p E₂ = bernProb p E₂' := by
    have := hfact (fun _ => True) E₂'
    rw [bernProb_true, one_mul] at this
    rw [← this]
    refine bernProb_congr (fun ω => ?_)
    have h2 := hE₂ (split ω).1 (split ω).2
    rw [hcomb_split ω] at h2
    simp [h2]
  rw [h12, h1_eq, h2_eq]

/-- **Finite Asymmetric Lovász Local Lemma** on `{0, 1}^α`:
if each bad event `E i` depends only on coordinates in `supp i`, and `x : ι → [0, 1)` satisfies
`P(E i) ≤ x i * ∏_{j ∈ dep i} (1 - x j)`, then `P(∀ i, ¬ E i) > 0` (so a good configuration exists). -/
private lemma asymmetric_lll {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : ι → (α → Bool) → Prop) (supp : ι → Finset α)
    (hsupp : ∀ i ω ω', (∀ e ∈ supp i, ω e = ω' e) → (E i ω ↔ E i ω'))
    (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hlll : ∀ i : ι, bernProb p (E i) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (supp i) (supp j)), (1 - x j)) :
    ∃ ω : α → Bool, ∀ i : ι, ¬ E i ω := by
  classical
  let dep : ι → Finset ι := fun i =>
    Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (supp i) (supp j))
  -- Strong induction on `m`: for all `S` with `S.card ≤ m`,
  -- (1) `P(∀ j ∈ S, ¬ E j) > 0`, and
  -- (2) `∀ i ∉ S, P(E i ∧ ∀ j ∈ S, ¬ E j) ≤ x i * P(∀ j ∈ S, ¬ E j)`.
  have hind : ∀ m : ℕ, ∀ S : Finset ι, S.card ≤ m →
      0 < bernProb p (fun ω => ∀ j ∈ S, ¬ E j ω) ∧
      ∀ i ∉ S, bernProb p (fun ω => E i ω ∧ ∀ j ∈ S, ¬ E j ω) ≤
        x i * bernProb p (fun ω => ∀ j ∈ S, ¬ E j ω) := by
    intro m
    induction m with
    | zero =>
      intro S hS
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
      subst hS0
      have hT : bernProb p (fun ω => ∀ j ∈ (∅ : Finset ι), ¬ E j ω) = 1 := by
        rw [bernProb_congr (E₂ := fun _ => True) (fun _ => by simp), bernProb_true]
      refine ⟨by linarith, fun i _ => ?_⟩
      rw [hT, mul_one, bernProb_congr (E₂ := E i) (fun _ => by simp)]
      have hprod_le : (∏ j ∈ dep i, (1 - x j)) ≤ 1 := by
        refine Finset.prod_le_one (fun j _ => by linarith [hx1 j]) (fun j _ => by linarith [hx0 j])
      calc bernProb p (E i) ≤ x i * ∏ j ∈ dep i, (1 - x j) := hlll i
        _ ≤ x i * 1 := mul_le_mul_of_nonneg_left hprod_le (hx0 i)
        _ = x i := mul_one _
    | succ m ih =>
      intro S hS
      have hpos : 0 < bernProb p (fun ω => ∀ j ∈ S, ¬ E j ω) := by
        rcases S.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
        · rw [bernProb_congr (E₂ := fun _ => True) (fun _ => by simp), bernProb_true]; norm_num
        · let S' := S.erase j₀
          have hS'_card : S'.card ≤ m := by
            have hc : (S.erase j₀).card = S.card - 1 := Finset.card_erase_of_mem hj₀
            have hne0 : 1 ≤ S.card := Finset.card_pos.mpr ⟨j₀, hj₀⟩
            change (S.erase j₀).card ≤ m
            omega
          have ⟨hS'_pos, hS'_cond⟩ := ih S' hS'_card
          have hj₀_not : j₀ ∉ S' := Finset.notMem_erase j₀ S
          have hsub : bernProb p (fun ω => ∀ j ∈ S, ¬ E j ω) =
              bernProb p (fun ω => ∀ j ∈ S', ¬ E j ω) -
                bernProb p (fun ω => E j₀ ω ∧ ∀ j ∈ S', ¬ E j ω) := by
            rw [← bernProb_and_not_eq_sub]
            refine bernProb_congr (fun ω => ?_)
            constructor
            · intro h; exact ⟨h j₀ hj₀, fun j hj => h j (Finset.mem_of_mem_erase hj)⟩
            · rintro ⟨h1, h2⟩ j hj
              by_cases hje : j = j₀
              · subst hje; exact h1
              · exact h2 j (Finset.mem_erase.mpr ⟨hje, hj⟩)
          have hle := hS'_cond j₀ hj₀_not
          have h1x : 0 < 1 - x j₀ := by linarith [hx1 j₀]
          nlinarith
      refine ⟨hpos, fun i hi => ?_⟩
      let S₁ := S ∩ dep i
      let S₂ := S \ dep i
      -- Step 1: `E i` is independent of `∀ j ∈ S₂, ¬ E j`
      have hdisj_supp : Disjoint (supp i) (S₂.biUnion supp) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        have hjS : j ∈ S := (Finset.mem_sdiff.mp hj).1
        have hjnot : j ∉ dep i := (Finset.mem_sdiff.mp hj).2
        have hji : j ≠ i := fun h => hi (h ▸ hjS)
        simp only [dep, Finset.mem_filter, Finset.mem_univ, true_and] at hjnot
        tauto
      have hS₂_dep : ∀ ω ω', (∀ e ∈ S₂.biUnion supp, ω e = ω' e) →
          ((∀ j ∈ S₂, ¬ E j ω) ↔ (∀ j ∈ S₂, ¬ E j ω')) := by
        intro ω ω' heq
        constructor <;> intro h j hj
        · rw [← hsupp j ω ω' (fun e he => heq e (Finset.mem_biUnion.mpr ⟨j, hj, he⟩))]
          exact h j hj
        · rw [hsupp j ω ω' (fun e he => heq e (Finset.mem_biUnion.mpr ⟨j, hj, he⟩))]
          exact h j hj
      have hindep : bernProb p (fun ω => E i ω ∧ ∀ j ∈ S₂, ¬ E j ω) =
          bernProb p (E i) * bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω) :=
        bernProb_indep_of_disjoint p hdisj_supp (hsupp i) hS₂_dep
      have hmono : bernProb p (fun ω => E i ω ∧ ∀ j ∈ S, ¬ E j ω) ≤
          bernProb p (E i) * bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω) := by
        rw [← hindep]
        refine bernProb_mono hp0 hp1 (fun ω ⟨h1, h2⟩ => ⟨h1, fun j hj => h2 j (Finset.sdiff_subset hj)⟩)
      -- Step 2: By induction on `T ⊆ S₁`, `(∏ j ∈ T, (1 - x j)) * P(S₂) ≤ P(S₂ ∪ T)`
      have htele : ∀ T : Finset ι, T ⊆ S₁ →
          (∏ j ∈ T, (1 - x j)) * bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω) ≤
            bernProb p (fun ω => ∀ j ∈ S₂ ∪ T, ¬ E j ω) := by
        intro T
        induction T using Finset.induction_on with
        | empty =>
          intro _; simp
        | @insert j₀ T hj₀_not ihT =>
          intro hsub
          have hT_sub : T ⊆ S₁ := Finset.Subset.trans (Finset.subset_insert j₀ T) hsub
          have hj₀_S₁ : j₀ ∈ S₁ := hsub (Finset.mem_insert_self j₀ T)
          have hj₀_not_S₂ : j₀ ∉ S₂ := by
            intro h2
            exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp hj₀_S₁).2
          have hj₀_not_U : j₀ ∉ S₂ ∪ T := by
            simp [hj₀_not_S₂, hj₀_not]
          have hU_sub_S : S₂ ∪ T ⊆ S := by
            refine Finset.union_subset Finset.sdiff_subset ?_
            exact Finset.Subset.trans hT_sub Finset.inter_subset_left
          have hU_lt : (S₂ ∪ T).card < S.card := by
            refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hU_sub_S, ?_⟩)
            intro heq
            exact hj₀_not_U (heq ▸ (Finset.mem_inter.mp hj₀_S₁).1)
          have hU_le : (S₂ ∪ T).card ≤ m := by omega
          have ⟨_, hU_cond⟩ := ih (S₂ ∪ T) hU_le
          have hstep : (1 - x j₀) * bernProb p (fun ω => ∀ j ∈ S₂ ∪ T, ¬ E j ω) ≤
              bernProb p (fun ω => ∀ j ∈ S₂ ∪ insert j₀ T, ¬ E j ω) := by
            have hdiff : bernProb p (fun ω => ∀ j ∈ S₂ ∪ insert j₀ T, ¬ E j ω) =
                bernProb p (fun ω => ∀ j ∈ S₂ ∪ T, ¬ E j ω) -
                  bernProb p (fun ω => E j₀ ω ∧ ∀ j ∈ S₂ ∪ T, ¬ E j ω) := by
              rw [← bernProb_and_not_eq_sub]
              refine bernProb_congr (fun ω => ?_)
              simp only [Finset.mem_union, Finset.mem_insert]
              constructor
              · intro h
                exact ⟨h j₀ (Or.inr (Or.inl rfl)), fun j hj => h j (by tauto)⟩
              · rintro ⟨h1, h2⟩ j (hj | rfl | hj)
                · exact h2 j (Or.inl hj)
                · exact h1
                · exact h2 j (Or.inr hj)
            have hle := hU_cond j₀ hj₀_not_U
            linarith
          rw [Finset.prod_insert hj₀_not, mul_assoc]
          calc (1 - x j₀) * ((∏ j ∈ T, (1 - x j)) * bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω))
              ≤ (1 - x j₀) * bernProb p (fun ω => ∀ j ∈ S₂ ∪ T, ¬ E j ω) :=
                mul_le_mul_of_nonneg_left (ihT hT_sub) (by linarith [hx1 j₀])
            _ ≤ bernProb p (fun ω => ∀ j ∈ S₂ ∪ insert j₀ T, ¬ E j ω) := hstep
      have htele_S₁ := htele S₁ (Finset.Subset.refl _)
      have hunion_eq : S₂ ∪ S₁ = S := by
        ext j; simp only [S₁, S₂, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [hunion_eq] at htele_S₁
      have hprod_mono : (∏ j ∈ dep i, (1 - x j)) ≤ ∏ j ∈ S₁, (1 - x j) := by
        have hS₁_sub : S₁ ⊆ dep i := Finset.inter_subset_right
        rw [← Finset.prod_sdiff hS₁_sub]
        have hrest_le : (∏ j ∈ dep i \ S₁, (1 - x j)) ≤ 1 :=
          Finset.prod_le_one (fun j _ => by linarith [hx1 j]) (fun j _ => by linarith [hx0 j])
        have hS₁_nn : 0 ≤ ∏ j ∈ S₁, (1 - x j) :=
          Finset.prod_nonneg (fun j _ => by linarith [hx1 j])
        nlinarith
      have hP₂_nn : 0 ≤ bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω) := bernProb_nonneg hp0 hp1 _
      calc bernProb p (fun ω => E i ω ∧ ∀ j ∈ S, ¬ E j ω)
          ≤ bernProb p (E i) * bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω) := hmono
        _ ≤ (x i * ∏ j ∈ dep i, (1 - x j)) * bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω) :=
            mul_le_mul_of_nonneg_right (hlll i) hP₂_nn
        _ ≤ (x i * ∏ j ∈ S₁, (1 - x j)) * bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod_mono (hx0 i)) hP₂_nn
        _ = x i * ((∏ j ∈ S₁, (1 - x j)) * bernProb p (fun ω => ∀ j ∈ S₂, ¬ E j ω)) := by ring
        _ ≤ x i * bernProb p (fun ω => ∀ j ∈ S, ¬ E j ω) :=
            mul_le_mul_of_nonneg_left htele_S₁ (hx0 i)
  -- Apply `hind` to `S = Finset.univ`!
  have hpos_all : 0 < bernProb p (fun ω => ∀ j ∈ (Finset.univ : Finset ι), ¬ E j ω) :=
    (hind (Finset.univ : Finset ι).card Finset.univ le_rfl).1
  by_contra hnone
  push Not at hnone
  have hzero : bernProb p (fun ω => ∀ j ∈ (Finset.univ : Finset ι), ¬ E j ω) = 0 := by
    unfold bernProb
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    have ⟨i, hi⟩ := hnone ω
    rw [if_neg]
    intro hall
    exact hall i (Finset.mem_univ i) hi
  linarith

/-- Elementary inequality: `exp (-2 * t) ≤ 1 - t` for `0 ≤ t ≤ 1 / 2`. -/
private lemma exp_neg_two_mul_le_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-2 * t) ≤ 1 - t := by
  have h1 : 1 ≤ (1 - t) * (1 + 2 * t) := by nlinarith
  have h2 : 1 + 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
  have h3 : 1 ≤ (1 - t) * Real.exp (2 * t) :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))
  have h4 : Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (2 * t) := Real.exp_pos _
  nlinarith

/-- Helper: pairs `{e : Fin n × Fin n // e.1 < e.2}` inside a vertex subset `t : Finset (Fin n)`. -/
private def pairsIn {n : ℕ} (t : Finset (Fin n)) : Finset {e : Fin n × Fin n // e.1 < e.2} :=
  Finset.univ.filter (fun e => e.1.1 ∈ t ∧ e.1.2 ∈ t)

private lemma card_pairsIn {n : ℕ} (t : Finset (Fin n)) :
    (pairsIn t).card = t.card.choose 2 := by
  have hbij : (pairsIn t).card = (t.powersetCard 2).card := by
    refine Finset.card_bij (fun e _ => ({e.1.1, e.1.2} : Finset (Fin n))) ?_ ?_ ?_
    · intro e he
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (ne_of_lt e.2)⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> tauto
    · intro e₁ _ e₂ _ hEq
      have h1_mem : e₁.1.1 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin n)) := by
        rw [← hEq]; simp
      have h2_mem : e₁.1.2 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin n)) := by
        rw [← hEq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1_mem h2_mem
      have hlt1 : e₁.1.1 < e₁.1.2 := e₁.2
      have hlt2 : e₂.1.1 < e₂.1.2 := e₂.2
      apply Subtype.ext
      rcases h1_mem with ha | ha <;> rcases h2_mem with hb | hb
      · exact (ne_of_lt hlt1 (ha.trans hb.symm)).elim
      · exact Prod.ext ha hb
      · exact (not_lt_of_gt hlt2 (hb ▸ ha ▸ hlt1)).elim
      · exact (ne_of_lt hlt1 (ha.trans hb.symm)).elim
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs.2
      have ha : a ∈ t := hs.1 (by simp)
      have hb : b ∈ t := hs.1 (by simp)
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · refine ⟨⟨(a, b), hlt⟩, ?_, rfl⟩
        simp [pairsIn, ha, hb]
      · refine ⟨⟨(b, a), hgt⟩, ?_, by ext x; simp [or_comm]⟩
        simp [pairsIn, ha, hb]
  rw [hbij, Finset.card_powersetCard]

/-- Counting 3-subsets sharing an edge with a given vertex subset `s`:
at most `(pairsIn s).card * n` such 3-subsets! -/
private lemma card_triples_sharing_edge_le {n : ℕ} (s : Finset (Fin n)) :
    (Finset.univ.filter (fun t : {t : Finset (Fin n) // t.card = 3} =>
      ¬ Disjoint (pairsIn s) (pairsIn t.1))).card ≤ (pairsIn s).card * n := by
  let L := Finset.univ.filter (fun t : {t : Finset (Fin n) // t.card = 3} =>
    ¬ Disjoint (pairsIn s) (pairsIn t.1))
  let R := pairsIn s ×ˢ (Finset.univ : Finset (Fin n))
  have hsub : L.image (fun t => t.1) ⊆
      R.image (fun p => ({p.1.1.1, p.1.1.2, p.2} : Finset (Fin n))) := by
    intro u hu
    rw [Finset.mem_image] at hu
    rcases hu with ⟨t, htL, rfl⟩
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at htL
    rw [Finset.not_disjoint_iff] at htL
    rcases htL with ⟨e, he_s, he_t⟩
    simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at he_t
    have hcard_er : ((t.1.erase e.1.1).erase e.1.2).card = 1 := by
      have hne : e.1.2 ≠ e.1.1 := ne_of_gt e.2
      have hm2 : e.1.2 ∈ t.1.erase e.1.1 := Finset.mem_erase.mpr ⟨hne, he_t.2⟩
      rw [Finset.card_erase_of_mem hm2, Finset.card_erase_of_mem he_t.1, t.2]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard_er
    have hw_mem : w ∈ (t.1.erase e.1.1).erase e.1.2 := by rw [hw]; simp
    have hw_t : w ∈ t.1 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw_mem)
    rw [Finset.mem_image]
    refine ⟨(e, w), Finset.mem_product.mpr ⟨he_s, Finset.mem_univ w⟩, ?_⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact he_t.1
      · exact he_t.2
      · exact hw_t
    · intro hx
      by_cases h1 : x = e.1.1
      · exact Or.inl h1
      · by_cases h2 : x = e.1.2
        · exact Or.inr (Or.inl h2)
        · have hm : x ∈ (t.1.erase e.1.1).erase e.1.2 :=
            Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hx⟩⟩
          rw [hw, Finset.mem_singleton] at hm
          exact Or.inr (Or.inr hm)
  calc L.card = (L.image (fun t => t.1)).card :=
        (Finset.card_image_of_injective L Subtype.val_injective).symm
    _ ≤ (R.image (fun p => ({p.1.1.1, p.1.1.2, p.2} : Finset (Fin n)))).card :=
        Finset.card_le_card hsub
    _ ≤ R.card := Finset.card_image_le
    _ = (pairsIn s).card * n := by simp [R, Finset.card_product]

/-- **Spencer's (1977) Probabilistic Lower Bound on `R(3, k)`** (explicit for all `k ≥ 10`,
pure-Mathlib statement, 0 custom defs):
for every `k ≥ 10` and `n = ⌊k^2 / (2000 * (log k)^2)⌋`, there exists a triangle-free graph
on `Fin n` with no independent set of size `k`. -/
theorem ppl030_spencer_1977_ramsey_lower_explicit (k : ℕ) (hk : 10 ≤ k) :
    let n : ℕ := Nat.floor ((k : ℝ) ^ 2 / (2000 * (Real.log (k : ℝ)) ^ 2))
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.IndepSetFree k := by
  intro n
  -- Easy case `n < k`: the empty graph `⊥` is triangle-free and has no `k`-subset!
  by_cases hnk : n < k
  · refine ⟨⊥, ?_, ?_⟩
    · intro t ⟨ht_clq, ht_card⟩
      obtain ⟨a, b, c, hab, _, _, rfl⟩ := Finset.card_eq_three.mp ht_card
      exact ht_clq (by simp) (by simp) hab
    · intro t ⟨_, ht_card⟩
      have hle : t.card ≤ Fintype.card (Fin n) := Finset.card_le_univ t
      rw [Fintype.card_fin] at hle
      omega
  · -- Main case `k ≤ n` (so `10 ≤ k ≤ n`): apply our Finite Asymmetric LLL!
    push Not at hnk
    have hn10 : 10 ≤ n := le_trans hk hnk
    have hkR : (10 : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    have hnR : (10 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn10
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
    have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
    have hlogk_ge2 : (2 : ℝ) ≤ Real.log (k : ℝ) := by
      have he2 : Real.exp 2 ≤ (10 : ℝ) := by
        have hq : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
          linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
        have h14 : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
          have hmul : Real.exp (-(1 / 4 : ℝ)) * Real.exp (1 / 4 : ℝ) = 1 := by
            rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos (1 / 4 : ℝ)]
        have hpow : Real.exp 2 = Real.exp (1 / 4 : ℝ) ^ 8 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [hpow]
        calc Real.exp (1 / 4 : ℝ) ^ 8 ≤ (4 / 3 : ℝ) ^ 8 :=
              pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h14 8
          _ ≤ 10 := by norm_num
      calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log (k : ℝ) := Real.log_le_log (Real.exp_pos 2) (by linarith)
    have hlogk_pos : 0 < Real.log (k : ℝ) := by linarith
    have hn_le_real : (n : ℝ) ≤ (k : ℝ) ^ 2 / (2000 * (Real.log (k : ℝ)) ^ 2) :=
      Nat.floor_le (by positivity)
    -- Parameters: `p = 1 / (4 √n)`, `x_T = 2 p^3`, `x_I = 1 / (8 * n^k)`
    let α := {e : Fin n × Fin n // e.1 < e.2}
    let Tri := {t : Finset (Fin n) // t.card = 3}
    let KSet := {s : Finset (Fin n) // s.card = k}
    let ι := Tri ⊕ KSet
    let p : ℝ := 1 / (4 * Real.sqrt (n : ℝ))
    have hsqn_ge3 : (3 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (le_of_lt hn_pos)]
      linarith
    have hsqn_pos : 0 < Real.sqrt (n : ℝ) := by linarith
    have hp0 : 0 ≤ p := by dsimp [p]; positivity
    have hp_le : p ≤ 1 / 12 := by
      dsimp [p]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hp1 : p ≤ 1 := by linarith
    let xT : ℝ := 2 * p ^ 3
    let xI : ℝ := 1 / (8 * (n : ℝ) ^ k)
    have hxT_nn : 0 ≤ xT := by dsimp [xT]; positivity
    have hxT_le_half : xT ≤ 1 / 2 := by
      dsimp [xT]
      have : p ^ 3 ≤ (1 / 12 : ℝ) ^ 3 := pow_le_pow_left₀ hp0 hp_le 3
      linarith
    have hnk_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ k := one_le_pow₀ (by linarith)
    have hxI_nn : 0 ≤ xI := by dsimp [xI]; positivity
    have hxI_le_half : xI ≤ 1 / 2 := by
      dsimp [xI]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    -- Define events `E` and supports `supp`
    let E : ι → (α → Bool) → Prop
      | Sum.inl t => fun ω => ∀ e ∈ pairsIn t.1, ω e = true
      | Sum.inr s => fun ω => ∀ e ∈ pairsIn s.1, ω e = false
    let supp : ι → Finset α
      | Sum.inl t => pairsIn t.1
      | Sum.inr s => pairsIn s.1
    let x : ι → ℝ
      | Sum.inl _ => xT
      | Sum.inr _ => xI
    have hsupp : ∀ i ω ω', (∀ e ∈ supp i, ω e = ω' e) → (E i ω ↔ E i ω') := by
      intro i ω ω' heq
      cases i with
      | inl t =>
        dsimp [E, supp] at heq ⊢
        constructor <;> intro h e he
        · rw [← heq e he]; exact h e he
        · rw [heq e he]; exact h e he
      | inr s =>
        dsimp [E, supp] at heq ⊢
        constructor <;> intro h e he
        · rw [← heq e he]; exact h e he
        · rw [heq e he]; exact h e he
    -- Cardinality of `KSet` is `n.choose k ≤ n ^ k`
    have hcard_KSet : (Fintype.card KSet : ℝ) ≤ (n : ℝ) ^ k := by
      have h1 : Fintype.card KSet = n.choose k := by
        have hbij : Fintype.card KSet = ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
          rw [← Finset.card_univ]
          refine Finset.card_bij (fun (s : KSet) _ => s.1) ?_ ?_ ?_
          · intro s _; rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, s.2⟩
          · intro a _ b _ h; exact Subtype.ext h
          · intro s hs
            rw [Finset.mem_powersetCard] at hs
            exact ⟨⟨s, hs.2⟩, Finset.mem_univ _, rfl⟩
        rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      rw [h1]
      exact_mod_cast Nat.choose_le_pow n k
    -- Verify the Asymmetric LLL condition for EVERY event `i : ι`!
    have hlll : ∀ i : ι, bernProb p (E i) ≤
        x i * ∏ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (supp i) (supp j)),
          (1 - x j) := by
      intro i
      let D := Finset.univ.filter (fun j : ι => j ≠ i ∧ ¬ Disjoint (supp i) (supp j))
      let D_T : Finset Tri := Finset.univ.filter (fun t : Tri => ¬ Disjoint (supp i) (pairsIn t.1))
      -- Bound `∏ j ∈ D, (1 - x j)` from below by `(1 - xT)^D_T.card * (1 - xI)^(Fintype.card KSet)`
      have hprod_lb : (1 - xT) ^ D_T.card * (1 - xI) ^ Fintype.card KSet ≤
          ∏ j ∈ D, (1 - x j) := by
        let DT_inj : Finset ι := D_T.image Sum.inl
        let DK_inj : Finset ι := (Finset.univ : Finset KSet).image Sum.inr
        have hD_sub : D ⊆ DT_inj ∪ DK_inj := by
          intro j hj
          simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          cases j with
          | inl t =>
            exact Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hj.2⟩, rfl⟩)
          | inr s =>
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩)
        have hdisj_TK : Disjoint DT_inj DK_inj := by
          rw [Finset.disjoint_left]
          intro j h1 h2
          rw [Finset.mem_image] at h1 h2
          rcases h1 with ⟨_, _, rfl⟩
          rcases h2 with ⟨_, _, h⟩
          exact Sum.inl_ne_inr h.symm
        have h1_sub : ∏ j ∈ DT_inj ∪ DK_inj, (1 - x j) ≤ ∏ j ∈ D, (1 - x j) := by
          rw [← Finset.prod_sdiff hD_sub]
          have hle1 : ∏ j ∈ (DT_inj ∪ DK_inj) \ D, (1 - x j) ≤ 1 := by
            refine Finset.prod_le_one (fun j _ => ?_) (fun j _ => ?_)
            · cases j <;> dsimp [x] <;> linarith
            · cases j <;> dsimp [x] <;> linarith
          have hnn : 0 ≤ ∏ j ∈ D, (1 - x j) :=
            Finset.prod_nonneg (fun j _ => by cases j <;> dsimp [x] <;> linarith)
          nlinarith
        have h2_eq : ∏ j ∈ DT_inj ∪ DK_inj, (1 - x j) =
            (1 - xT) ^ D_T.card * (1 - xI) ^ Fintype.card KSet := by
          rw [Finset.prod_union hdisj_TK]
          rw [Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h)]
          rw [Finset.prod_image (fun _ _ _ _ h => Sum.inr.inj h)]
          simp [x, Finset.prod_const]
        linarith
      -- Lower-bound `(1 - xT)^D_T.card * (1 - xI)^card(KSet)` using `exp(-2*t) ≤ 1 - t`!
      have hexp_lb : Real.exp (-(2 * (D_T.card : ℝ) * xT + 1 / 4)) ≤
          (1 - xT) ^ D_T.card * (1 - xI) ^ Fintype.card KSet := by
        have hT : Real.exp (-(2 * (D_T.card : ℝ) * xT)) ≤ (1 - xT) ^ D_T.card := by
          have h1 := pow_le_pow_left₀ (le_of_lt (Real.exp_pos _))
            (exp_neg_two_mul_le_one_sub hxT_nn hxT_le_half) D_T.card
          rw [← Real.exp_nat_mul] at h1
          have heq : (D_T.card : ℝ) * (-2 * xT) = -(2 * (D_T.card : ℝ) * xT) := by ring
          rwa [heq] at h1
        have hI : Real.exp (-(1 / 4 : ℝ)) ≤ (1 - xI) ^ Fintype.card KSet := by
          have h1 := pow_le_pow_left₀ (le_of_lt (Real.exp_pos _))
            (exp_neg_two_mul_le_one_sub hxI_nn hxI_le_half) (Fintype.card KSet)
          rw [← Real.exp_nat_mul] at h1
          have h2 : -(1 / 4 : ℝ) ≤ (Fintype.card KSet : ℝ) * (-2 * xI) := by
            have hmul : (Fintype.card KSet : ℝ) * xI ≤ 1 / 8 := by
              dsimp [xI]
              rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith
            linarith
          exact le_trans (Real.exp_le_exp.mpr h2) h1
        have hmul := mul_le_mul hT hI (le_of_lt (Real.exp_pos _))
          (pow_nonneg (by linarith) _)
        rw [← Real.exp_add] at hmul
        have heq : -(2 * (D_T.card : ℝ) * xT) + -(1 / 4 : ℝ) = -(2 * (D_T.card : ℝ) * xT + 1 / 4) := by ring
        rwa [heq] at hmul
      cases i with
      | inl t =>
        -- Triangle event: `P(E t) = p^3`, `x t = 2 p^3`, `D_T.card ≤ 3 * n`
        have hprob : bernProb p (E (Sum.inl t)) = p ^ 3 := by
          dsimp [E]
          rw [bernProb_cyl_true, card_pairsIn, t.2]
          norm_num
        rw [hprob]
        have hDT_le : (D_T.card : ℝ) ≤ 3 * (n : ℝ) := by
          have hnat := card_triples_sharing_edge_le t.1
          rw [card_pairsIn, t.2] at hnat
          have h3 : Nat.choose 3 2 = 3 := by decide
          rw [h3] at hnat
          exact_mod_cast hnat
        -- `exp (1/2) ≤ 2` directly from `1/2 = -1/2 + 1 ≤ exp (-1/2)`!
        have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
          have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
            linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
          have hmul : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ) = 1 := by
            rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos (1 / 2 : ℝ)]
        have harg : 2 * (D_T.card : ℝ) * xT + 1 / 4 ≤ 1 / 2 := by
          have hxT_eq : (n : ℝ) * xT = 1 / (32 * Real.sqrt (n : ℝ)) := by
            dsimp [xT, p]
            have hsq2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
            have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqn_pos
            field_simp [hne]
            nlinarith
          have h1 : 2 * (D_T.card : ℝ) * xT ≤ 6 * ((n : ℝ) * xT) := by
            have := mul_le_mul_of_nonneg_right hDT_le hxT_nn
            linarith
          rw [hxT_eq] at h1
          have h2 : 6 * (1 / (32 * Real.sqrt (n : ℝ))) ≤ 1 / 4 := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
          linarith
        have hhalf_le : (1 / 2 : ℝ) ≤ Real.exp (-(2 * (D_T.card : ℝ) * xT + 1 / 4)) := by
          have h1 : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(2 * (D_T.card : ℝ) * xT + 1 / 4)) :=
            Real.exp_le_exp.mpr (by linarith)
          have h2 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
            linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
          linarith
        have hprod_ge : (1 / 2 : ℝ) ≤ ∏ j ∈ D, (1 - x j) :=
          le_trans hhalf_le (le_trans hexp_lb hprod_lb)
        dsimp [x, xT]
        have hp3_nn : 0 ≤ p ^ 3 := pow_nonneg hp0 3
        nlinarith
      | inr s =>
        -- Independent-set event: `P(E s) = (1 - p)^(k.choose 2)`, `x s = 1 / (8 * n^k)`
        have hprob : bernProb p (E (Sum.inr s)) = (1 - p) ^ (k.choose 2) := by
          dsimp [E]
          rw [bernProb_cyl_false, card_pairsIn, s.2]
        rw [hprob]
        have hDT_le : (D_T.card : ℝ) ≤ (k.choose 2 : ℝ) * (n : ℝ) := by
          have hnat := card_triples_sharing_edge_le s.1
          rw [card_pairsIn, s.2] at hnat
          exact_mod_cast hnat
        have hch2 : (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
          rw [Nat.choose_two_right]
          have hdvd : 2 ∣ k * (k - 1) := by
            rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
            · exact ⟨m * (m + m - 1), by ring⟩
            · exact ⟨(2 * m + 1) * m, by simp only [Nat.add_sub_cancel]; ring⟩
          rw [Nat.cast_div hdvd (by norm_num), Nat.cast_mul,
            Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
          norm_num
        -- Upper bound `(1 - p)^(k.choose 2) ≤ exp (-p * k.choose 2)`
        have hlhs_le : (1 - p) ^ (k.choose 2) ≤ Real.exp (-(p * (k.choose 2 : ℝ))) := by
          have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
          have h2 := pow_le_pow_left₀ (by linarith) h1 (k.choose 2)
          rw [← Real.exp_nat_mul] at h2
          have heq : (k.choose 2 : ℝ) * -p = -(p * (k.choose 2 : ℝ)) := by ring
          rwa [heq] at h2
        -- Express `xI = exp (-log(8 * n^k))` and compare exponents!
        have hxI_eq : xI = Real.exp (-(Real.log 8 + (k : ℝ) * Real.log (n : ℝ))) := by
          dsimp [xI]
          rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num),
            mul_comm (k : ℝ) (Real.log (n : ℝ)), ← Real.rpow_def_of_pos hn_pos,
            Real.rpow_natCast, one_div]
        -- Exponent comparison:
        -- `Real.log 8 + k * log n + 2 * D_T.card * xT + 1/4 ≤ p * (k.choose 2)`
        have hexp_cmp : Real.log 8 + (k : ℝ) * Real.log (n : ℝ) +
            (2 * (D_T.card : ℝ) * xT + 1 / 4) ≤ p * (k.choose 2 : ℝ) := by
          -- 1. `2 * D_T.card * xT ≤ (1/4) * p * (k.choose 2)`
          have h1 : 2 * (D_T.card : ℝ) * xT ≤ (1 / 4) * (p * (k.choose 2 : ℝ)) := by
            have hn_xT : (n : ℝ) * xT = p / 8 := by
              dsimp [xT, p]
              have hsq2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
              have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqn_pos
              field_simp [hne]
              nlinarith
            have hDT_mul : 2 * (D_T.card : ℝ) * xT ≤ 2 * ((k.choose 2 : ℝ) * (n : ℝ)) * xT := by
              have := mul_le_mul_of_nonneg_right hDT_le hxT_nn
              linarith
            calc 2 * (D_T.card : ℝ) * xT
                ≤ 2 * ((k.choose 2 : ℝ) * (n : ℝ)) * xT := hDT_mul
              _ = 2 * (k.choose 2 : ℝ) * ((n : ℝ) * xT) := by ring
              _ = 2 * (k.choose 2 : ℝ) * (p / 8) := by rw [hn_xT]
              _ = (1 / 4) * (p * (k.choose 2 : ℝ)) := by ring
          -- 2. `3/4 * p * (k.choose 2) ≥ 2.5 * k * log k`:
          --    Since `n ≤ k^2 / (2000 * (log k)^2)`, `√n ≤ k / (40 * log k)` (`40^2 = 1600 ≤ 2000`),
          --    so `p = 1/(4 √n) ≥ 10 * log k / k`,
          --    and `k.choose 2 = k(k-1)/2 ≥ (9/20) k^2` (for `k ≥ 10`),
          --    giving `(3/4) * p * (k.choose 2) ≥ (3/4) * 10 * (9/20) * k log k = (27/8) * k log k`!
          have hsqn_le : Real.sqrt (n : ℝ) ≤ (k : ℝ) / (40 * Real.log (k : ℝ)) := by
            rw [Real.sqrt_le_left (by positivity)]
            rw [div_pow]
            have hden : 1600 * (Real.log (k : ℝ)) ^ 2 ≤ 2000 * (Real.log (k : ℝ)) ^ 2 := by
              nlinarith
            calc (n : ℝ) ≤ (k : ℝ) ^ 2 / (2000 * (Real.log (k : ℝ)) ^ 2) := hn_le_real
              _ ≤ (k : ℝ) ^ 2 / (1600 * (Real.log (k : ℝ)) ^ 2) :=
                  div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
              _ = (k : ℝ) ^ 2 / (40 * Real.log (k : ℝ)) ^ 2 := by ring
          have hp_ge : 10 * Real.log (k : ℝ) / (k : ℝ) ≤ p := by
            dsimp [p]
            rw [div_le_div_iff₀ hk_pos (by positivity)]
            have hmul := mul_le_mul_of_nonneg_left hsqn_le (by positivity : 0 ≤ 40 * Real.log (k : ℝ))
            have hne : 40 * Real.log (k : ℝ) ≠ 0 := by positivity
            rw [mul_div_cancel₀ _ hne] at hmul
            linarith
          have hch2_ge : (9 / 20 : ℝ) * (k : ℝ) ^ 2 ≤ (k.choose 2 : ℝ) := by
            rw [hch2]; nlinarith
          have hmain_lb : (27 / 8 : ℝ) * ((k : ℝ) * Real.log (k : ℝ)) ≤
              (3 / 4) * (p * (k.choose 2 : ℝ)) := by
            have hmul := mul_le_mul hp_ge hch2_ge (by positivity) hp0
            have hsimp : (10 * Real.log (k : ℝ) / (k : ℝ)) * ((9 / 20 : ℝ) * (k : ℝ) ^ 2) =
                (9 / 2 : ℝ) * ((k : ℝ) * Real.log (k : ℝ)) := by
              field_simp [ne_of_gt hk_pos]
              ring
            linarith
          -- 3. `log n ≤ 2 * log k` (since `n ≤ k^2`) and `log 8 ≤ 3` (since `8 ≤ exp 3`)
          have hlogn_le : Real.log (n : ℝ) ≤ 2 * Real.log (k : ℝ) := by
            have hn_le_k2 : (n : ℝ) ≤ (k : ℝ) ^ 2 := by
              have hden_ge1 : (1 : ℝ) ≤ 2000 * (Real.log (k : ℝ)) ^ 2 := by nlinarith
              calc (n : ℝ) ≤ (k : ℝ) ^ 2 / (2000 * (Real.log (k : ℝ)) ^ 2) := hn_le_real
                _ ≤ (k : ℝ) ^ 2 / 1 := div_le_div_of_nonneg_left (sq_nonneg _) zero_lt_one hden_ge1
                _ = (k : ℝ) ^ 2 := div_one _
            calc Real.log (n : ℝ) ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log hn_pos hn_le_k2
              _ = 2 * Real.log (k : ℝ) := by rw [Real.log_pow]; norm_num
          have hlog8_le : Real.log 8 ≤ 3 := by
            have h8e : (8 : ℝ) ≤ Real.exp 3 := by
              have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
              have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
                rw [← Real.exp_nat_mul]; norm_num
              rw [h3]
              calc (8 : ℝ) = 2 ^ 3 := by norm_num
                _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
            calc Real.log 8 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) h8e
              _ = 3 := Real.log_exp 3
          have hklog_ge20 : 20 ≤ (k : ℝ) * Real.log (k : ℝ) := by nlinarith
          nlinarith
        dsimp [x]
        calc (1 - p) ^ k.choose 2
            ≤ Real.exp (-(p * (k.choose 2 : ℝ))) := hlhs_le
          _ ≤ Real.exp (-(Real.log 8 + (k : ℝ) * Real.log (n : ℝ) +
                (2 * (D_T.card : ℝ) * xT + 1 / 4))) := Real.exp_le_exp.mpr (by linarith)
          _ = xI * Real.exp (-(2 * (D_T.card : ℝ) * xT + 1 / 4)) := by
              rw [hxI_eq, ← Real.exp_add]; congr 1; ring
          _ ≤ xI * ((1 - xT) ^ D_T.card * (1 - xI) ^ Fintype.card KSet) :=
              mul_le_mul_of_nonneg_left hexp_lb hxI_nn
          _ ≤ xI * ∏ j ∈ D, (1 - x j) :=
              mul_le_mul_of_nonneg_left hprod_lb hxI_nn
    -- Invoke our Finite Asymmetric LLL!
    obtain ⟨ω, hω⟩ := asymmetric_lll hp0 hp1 E supp hsupp x
      (fun i => match i with | Sum.inl _ => hxT_nn | Sum.inr _ => hxI_nn)
      (fun i => by cases i <;> dsimp [x] <;> linarith)
      hlll
    -- Build the graph `G : SimpleGraph (Fin n)` from `ω : α → Bool`!
    let G : SimpleGraph (Fin n) :=
      { Adj := fun u v =>
          if h : u < v then ω ⟨(u, v), h⟩ = true
          else if h' : v < u then ω ⟨(v, u), h'⟩ = true
          else False
        symm := ⟨fun u v hadj => by
          by_cases h1 : u < v
          · have h2 : ¬ v < u := not_lt.mpr (le_of_lt h1)
            simp only [h1, dite_true] at hadj
            simp only [h2, dite_false, h1, dite_true]
            exact hadj
          · by_cases h2 : v < u
            · simp only [h1, dite_false, h2, dite_true] at hadj
              simp only [h2, dite_true]
              exact hadj
            · simp only [h1, h2, dite_false] at hadj⟩
        loopless := ⟨fun u h => by simp at h⟩ }
    refine ⟨G, ?_, ?_⟩
    · -- Triangle-free (`CliqueFree 3`)
      intro t ⟨ht_clq, ht_card⟩
      have hbad := hω (Sum.inl ⟨t, ht_card⟩)
      apply hbad
      intro e he
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at he
      have hadj : G.Adj e.1.1 e.1.2 := ht_clq he.1 he.2 (ne_of_lt e.2)
      dsimp [G] at hadj
      simpa [e.2] using hadj
    · -- Independent-set-free (`IndepSetFree k`)
      intro s ⟨hs_ind, hs_card⟩
      have hbad := hω (Sum.inr ⟨s, hs_card⟩)
      apply hbad
      intro e he
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at he
      have hna : ¬ G.Adj e.1.1 e.1.2 := fun hadj => hs_ind he.1 he.2 (ne_of_lt e.2) hadj
      dsimp [G] at hna
      simp only [e.2, dite_true] at hna
      exact Bool.eq_false_iff.mpr hna

/-- **Spencer's (1977) Asymptotic Probabilistic Lower Bound on `R(3, k)`**
(pure-Mathlib `sInf` characterization, 0 custom definitions):
for every `k ≥ 10`,
`(1 / 2000) * (k / log k)^2 ≤ R(3, k)`. -/
theorem ppl030_spencer_1977_ramsey_lower :
    ∀ k : ℕ, 10 ≤ k →
      (k : ℝ) ^ 2 / (2000 * (Real.log (k : ℝ)) ^ 2) ≤
        ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k} : ℕ) : ℝ) := by
  intro k hk
  let m : ℕ := Nat.floor ((k : ℝ) ^ 2 / (2000 * (Real.log (k : ℝ)) ^ 2))
  obtain ⟨G, hclq, hind⟩ := ppl030_spencer_1977_ramsey_lower_explicit k hk
  -- First, show the Ramsey set is nonempty (by Shearer 1983 explicit bound!)
  have hnonempty :
      {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k}.Nonempty := by
    let B : ℝ := ((k - 1 : ℝ) * (k - 2 : ℝ) ^ 2) /
      ((k - 1 : ℝ) * Real.log (k - 1 : ℝ) - (k - 1 : ℝ) + 1)
    refine ⟨Nat.floor B + 1, fun H => ?_⟩
    by_contra h
    push Not at h
    have hub := ppl030_shearer_1983_ramsey_explicit H (by omega : 3 ≤ k) h.1 h.2
    rw [Fintype.card_fin] at hub
    have hlt : B < ((Nat.floor B + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one B
    linarith
  -- Every `n` in the Ramsey set satisfies `m < n`, hence `m + 1 ≤ sInf ...`!
  have hle_sInf : m + 1 ≤
      sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k} := by
    refine le_csInf hnonempty ?_
    intro n hn
    by_contra hlt
    push Not at hlt
    have hnm : n ≤ m := by omega
    let emb : Fin n ↪ Fin m := ⟨fun i => ⟨i.1, lt_of_lt_of_le i.2 hnm⟩,
      fun a b h => Fin.ext (by simpa using h)⟩
    let G' : SimpleGraph (Fin n) := G.comap emb
    have hclq' : G'.CliqueFree 3 := by
      intro t ⟨ht_clq, ht_card⟩
      refine hclq (t.map emb) ⟨?_, by simp [ht_card]⟩
      intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact ht_clq ha hb (fun h => hxy (congrArg emb h))
    have hind' : G'.IndepSetFree k := by
      intro t ⟨ht_ind, ht_card⟩
      refine hind (t.map emb) ⟨?_, by simp [ht_card]⟩
      intro x hx y hy hxy hadj
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      exact ht_ind ha hb (fun h => hxy (congrArg emb h)) hadj
    rcases hn G' with h1 | h2
    · exact h1 hclq'
    · exact h2 hind'
  have hm1_R : ((m + 1 : ℕ) : ℝ) ≤
      ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree k} : ℕ) : ℝ) :=
    Nat.cast_le.mpr hle_sInf
  have hlt_floor : (k : ℝ) ^ 2 / (2000 * (Real.log (k : ℝ)) ^ 2) < ((m + 1 : ℕ) : ℝ) := by
    dsimp [m]; push_cast; exact Nat.lt_floor_add_one _
  linarith

end SpencerLLL

end PPL030
