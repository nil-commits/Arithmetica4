import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Hom.Basic
import Mathlib.Order.WellFoundedSet
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic

/-!
# PPL 035: Erdős Problem #592 — Countable Ordinal Partition Relation `α → (α, 3)^2` ($1,000, Open)

**Honest Scope:** Erdős Problem #592 (PPL 035, $1,000) — classifying all countable ordinals `β`
such that `ω^β → (ω^β, 3)^2` — remains **OPEN** (specifically at exponents `β = ω^γ` where `γ` is
a sum of three additively indecomposable ordinals, starting at `α = ω^(ω^3)`).

This module formalizes from scratch, with `0` custom or `private` definitions in any public
theorem signature (100% native Mathlib `Ordinal`, `Sym2`, and `OrderEmbedding` signatures):
1. **Infinite Ramsey Theorem** `ω → (ω, ω)^2` and `ω → (ω, k)^2` (on `ℕ` and on any well-ordered
   type of order type `Ordinal.omega0`), plus the 1-tuple indecomposable partition theorem
   `ω^β → (ω^β)^1_2`.
2. **Specker's Positive Theorem (1957):** `ω^2 → (ω^2, k)^2` for all `k : ℕ`, and in particular
   `ω^2 → (ω^2, 3)^2`.
3. **Specker's Negative Theorem (1957):** `ω^n ↛ (ω^n, 3)^2` for all finite `n ≥ 3`.
4. **Galvin–Larson Necessary Condition (1974):** Every countable ordinal `α > 2` (indeed `α ≠ 0`)
   satisfying `α → (α, 3)^2` is additively indecomposable (`α = ω^β`) with either `β ∈ {0, 1, 2}`
   or `β` itself additively indecomposable (`∃ γ, β = ω^γ`).
5. **Complete Finite-Exponent Classification & Hypergraph Ramsey Engine:** Exact `↔` classification
   `ω^n → (ω^n, 3)^2 ↔ n ≤ 2` for all finite `n : ℕ`, plus the full Infinite Hypergraph Ramsey
   Theorem `ω → (ω)^r_2` for all `r : ℕ` (foundational engine for Chang 1972 / Larson 1973).
-/

namespace PPL035

open Ordinal

/-! ### Helper Bridges for Well-Orders and Order Isomorphisms -/

private noncomputable def orderIsoOfRelIsoLT {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : α ≃o β where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [RelIso.coe_fn_toEquiv]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact le_of_lt (e.map_rel_iff.mp hlt)
      · exact le_of_eq (e.injective heq)
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact le_of_lt (e.map_rel_iff.mpr hlt)
      · rw [heq]

private noncomputable def orderIsoOfTypeEq {α β : Type} [LinearOrder α] [LinearOrder β]
    [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)]
    (h : Ordinal.type ((· < ·) : α → α → Prop) = Ordinal.type ((· < ·) : β → β → Prop)) :
    α ≃o β :=
  orderIsoOfRelIsoLT (Classical.choice (Ordinal.type_eq.mp h))

private lemma type_lex_prod {α β : Type} [LinearOrder α] [LinearOrder β]
    [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] :
    Ordinal.type ((· < ·) : Lex (α × β) → Lex (α × β) → Prop) =
      Ordinal.type ((· < ·) : β → β → Prop) * Ordinal.type ((· < ·) : α → α → Prop) := by
  exact Ordinal.type_prod_lex ((· < ·) : β → β → Prop) ((· < ·) : α → α → Prop)

private lemma exists_strictMono_of_infinite_nat {S : Set ℕ} (hS : S.Infinite) :
    ∃ f : ℕ ↪o ℕ, ∀ n, f n ∈ S := by
  classical
  have hne : ∀ m : ℕ, ∃ x ∈ S, m < x := fun m => hS.exists_gt m
  let step : ℕ → ℕ := Nat.rec
    (Classical.choose (hne 0))
    (fun _ prev => Classical.choose (hne prev))
  have hmem : ∀ n, step n ∈ S := by
    intro n
    cases n with
    | zero => exact (Classical.choose_spec (hne 0)).1
    | succ k => exact (Classical.choose_spec (hne (step k))).1
  have hlt : ∀ n, step n < step (n + 1) := fun n => (Classical.choose_spec (hne (step n))).2
  exact ⟨OrderEmbedding.ofStrictMono step (strictMono_nat_of_lt_succ hlt), hmem⟩

/-! ### Section 1: Infinite Ramsey Theorem `ω → (ω, ω)^2` and `ω → (ω, k)^2` -/

/-- **Infinite Ramsey Theorem on `ℕ` (`ω → (ω, ω)^2`):**
Every 2-coloring of unordered pairs of `ℕ` admits a strictly increasing monochromatic sequence.
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_infinite_ramsey_nat (c : Sym2 ℕ → Bool) :
    (∃ f : ℕ ↪o ℕ, ∀ i j, i < j → c s(f i, f j) = true) ∨
    (∃ g : ℕ ↪o ℕ, ∀ i j, i < j → c s(g i, g j) = false) := by
  classical
  by_cases hred : ∀ A : Set ℕ, A.Infinite →
      ∃ x ∈ A, {y ∈ A | x < y ∧ c s(x, y) = true}.Infinite
  · left
    let RedState := { p : ℕ × Set ℕ // p.1 ∈ p.2 ∧ p.2.Infinite ∧
      ∀ y ∈ p.2, p.1 < y → c s(p.1, y) = true }
    have hstep : ∀ st : RedState, ∃ st' : RedState,
        st'.1.2 ⊆ {y ∈ st.1.2 | st.1.1 < y} := by
      intro st
      let B : Set ℕ := {y ∈ st.1.2 | st.1.1 < y}
      have hBinf : B.Infinite := by
        have hfin : {y ∈ st.1.2 | y ≤ st.1.1}.Finite :=
          (Set.finite_le_nat st.1.1).subset (fun y hy => hy.2)
        have hdiff : st.1.2 \ {y ∈ st.1.2 | y ≤ st.1.1} ⊆ B := by
          intro y ⟨hyA, hyn⟩
          refine ⟨hyA, ?_⟩
          by_contra hle
          exact hyn ⟨hyA, le_of_not_gt hle⟩
        exact (st.2.2.1.sdiff hfin).mono hdiff
      obtain ⟨x1, hx1B, hx1inf⟩ := hred B hBinf
      let A1 : Set ℕ := insert x1 {y ∈ B | x1 < y ∧ c s(x1, y) = true}
      refine ⟨⟨(x1, A1), Set.mem_insert x1 _, hx1inf.mono (Set.subset_insert _ _), ?_⟩, ?_⟩
      · intro y hy hlt
        rcases Set.mem_insert_iff.mp hy with rfl | hy'
        · exact (lt_irrefl _ hlt).elim
        · exact hy'.2.2
      · intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hy'
        · exact hx1B
        · exact hy'.1
    have h0 : ∃ st0 : RedState, True := by
      obtain ⟨x0, _, hx0inf⟩ := hred Set.univ Set.infinite_univ
      let A0 : Set ℕ := insert x0 {y ∈ (Set.univ : Set ℕ) | x0 < y ∧ c s(x0, y) = true}
      refine ⟨⟨(x0, A0), Set.mem_insert x0 _, hx0inf.mono (Set.subset_insert _ _), ?_⟩, trivial⟩
      intro y hy hlt
      rcases Set.mem_insert_iff.mp hy with rfl | hy'
      · exact (lt_irrefl _ hlt).elim
      · exact hy'.2.2
    let P : ℕ → RedState := Nat.rec (Classical.choose h0) (fun _ prev => Classical.choose (hstep prev))
    have hsub : ∀ k, (P (k + 1)).1.2 ⊆ {y ∈ (P k).1.2 | (P k).1.1 < y} :=
      fun k => Classical.choose_spec (hstep (P k))
    have hsub_le : ∀ a b, a ≤ b → (P b).1.2 ⊆ (P a).1.2 := by
      intro a b hab
      induction hab with
      | refl => exact Set.Subset.rfl
      | @step c _ ihc =>
        intro z hz
        exact ihc (hsub c hz).1
    have hlt_mem : ∀ {i j}, i < j → (P j).1.1 ∈ (P i).1.2 ∧ (P i).1.1 < (P j).1.1 := by
      intro i j hij
      induction hij with
      | refl =>
        have hmem := hsub i (P (i + 1)).2.1
        exact ⟨hmem.1, hmem.2⟩
      | @step m hm ih =>
        have hmem := hsub m (P (m + 1)).2.1
        exact ⟨hsub_le i m (le_of_lt hm) hmem.1, lt_trans ih.2 hmem.2⟩
    have hmono : StrictMono (fun n => (P n).1.1) := fun i j hij => (hlt_mem hij).2
    refine ⟨OrderEmbedding.ofStrictMono (fun n => (P n).1.1) hmono, ?_⟩
    intro i j hij
    have h := hlt_mem hij
    exact (P i).2.2.2 (P j).1.1 h.1 h.2
  · right
    push Not at hred
    obtain ⟨A, hAinf, hA⟩ := hred
    have hblue : ∀ (F : Finset ℕ), (∀ x ∈ F, x ∈ A) →
        ∃ y ∈ A, (∀ x ∈ F, x < y ∧ c s(x, y) = false) := by
      intro F hFA
      let bad : Set ℕ :=
        (⋃ x ∈ F, {y ∈ A | x < y ∧ c s(x, y) = true}) ∪
        (⋃ x ∈ F, {y : ℕ | y ≤ x})
      have hbad : bad.Finite := by
        refine Set.Finite.union ?_ ?_
        · exact F.finite_toSet.biUnion (fun x hx => hA x (hFA x hx))
        · exact F.finite_toSet.biUnion (fun x _ => Set.finite_le_nat x)
      obtain ⟨y, hyA, hynot⟩ := (hAinf.sdiff hbad).nonempty
      refine ⟨y, hyA, ?_⟩
      intro x hxF
      have hnotle : ¬ y ≤ x := fun hle => hynot (Or.inr (Set.mem_biUnion hxF hle))
      have hlt : x < y := lt_of_not_ge hnotle
      have hnotred : c s(x, y) ≠ true := fun htr =>
        hynot (Or.inl (Set.mem_biUnion hxF ⟨hyA, hlt, htr⟩))
      exact ⟨hlt, Bool.eq_false_iff.mpr hnotred⟩
    let BlueSeq (n : ℕ) :=
      { l : List ℕ // l.length = n ∧ (∀ x ∈ l, x ∈ A) ∧
        l.Pairwise (fun x y => x < y ∧ c s(x, y) = false) }
    have hstepB : ∀ n (s : BlueSeq n), ∃ s' : BlueSeq (n + 1),
        ∀ (i : ℕ) (hi : i < n),
          s'.1[i]'(by rw [s'.2.1]; omega) = s.1[i]'(by rw [s.2.1]; exact hi) := by
      intro n s
      obtain ⟨y, hyA, hyF⟩ := hblue s.1.toFinset (fun x hx => s.2.2.1 x (List.mem_toFinset.mp hx))
      refine ⟨⟨s.1 ++ [y], by simp [s.2.1], ?_, ?_⟩, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact s.2.2.1 x hx'
        · rw [List.mem_singleton.mp hx']; exact hyA
      · refine List.pairwise_append.mpr ⟨s.2.2.2, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton.mp hb]
        exact hyF a (List.mem_toFinset.mpr ha)
      · intro i hi
        exact List.getElem_append_left (by rw [s.2.1]; exact hi)
    let seq : (n : ℕ) → BlueSeq n :=
      Nat.rec ⟨[], rfl, by simp, List.Pairwise.nil⟩
        (fun n prev => Classical.choose (hstepB n prev))
    have hpref : ∀ n (i : ℕ) (hi : i < n),
        (seq (n + 1)).1[i]'(by rw [(seq (n + 1)).2.1]; omega) =
        (seq n).1[i]'(by rw [(seq n).2.1]; exact hi) :=
      fun n => Classical.choose_spec (hstepB n (seq n))
    let gfun : ℕ → ℕ := fun i => (seq (i + 1)).1[i]'(by rw [(seq (i + 1)).2.1]; omega)
    have hg_eq : ∀ {i k}, (hik : i < k) →
        (seq k).1[i]'(by rw [(seq k).2.1]; exact hik) = gfun i := by
      intro i k hik
      induction hik with
      | refl => rfl
      | @step m hm ih =>
        rw [hpref m i hm, ih]
    have hg_pw : ∀ i j, i < j → gfun i < gfun j ∧ c s(gfun i, gfun j) = false := by
      intro i j hij
      have hpw := List.pairwise_iff_getElem.mp (seq (j + 1)).2.2.2
      have hi : i < (seq (j + 1)).1.length := by rw [(seq (j + 1)).2.1]; omega
      have hj : j < (seq (j + 1)).1.length := by rw [(seq (j + 1)).2.1]; omega
      have h := hpw i j hi hj hij
      rw [hg_eq (by omega : i < j + 1), hg_eq (by omega : j < j + 1)] at h
      exact h
    exact ⟨OrderEmbedding.ofStrictMono gfun (fun i j hij => (hg_pw i j hij).1),
      fun i j hij => (hg_pw i j hij).2⟩

/-- **Infinite Ramsey Theorem `ω → (ω, k)^2` on `ℕ`:**
Every 2-coloring of unordered pairs of `ℕ` yields either a red copy of `ω` or a blue `K_k`.
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_infinite_ramsey_nat_k (k : ℕ) (c : Sym2 ℕ → Bool) :
    (∃ f : ℕ ↪o ℕ, ∀ i j, i < j → c s(f i, f j) = true) ∨
    (∃ g : Fin k ↪o ℕ, ∀ i j, i < j → c s(g i, g j) = false) := by
  rcases ppl035_infinite_ramsey_nat c with ⟨f, hf⟩ | ⟨g, hg⟩
  · exact Or.inl ⟨f, hf⟩
  · right
    let emb : Fin k ↪o ℕ :=
      (OrderEmbedding.ofStrictMono (fun i : Fin k => (i : ℕ)) (fun _ _ h => h)).trans g
    exact ⟨emb, fun i j hij => hg i j hij⟩

/-- **Infinite Ramsey Theorem on `Ordinal.omega0` (`ω → (ω, k)^2`):**
For any well-ordered type `τ` of order type `Ordinal.omega0`, every 2-coloring of `Sym2 τ`
yields either a red order-isomorphic copy of `τ` or a blue `K_k`.
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_infinite_ramsey_omega0 {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    (hτ : Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0)
    (k : ℕ) (c : Sym2 τ → Bool) :
    (∃ f : τ ↪o τ, ∀ x y, x < y → c s(f x, f y) = true) ∨
    (∃ g : Fin k ↪o τ, ∀ i j, i < j → c s(g i, g j) = false) := by
  let e : ℕ ≃o τ := orderIsoOfTypeEq (Ordinal.type_nat_lt.trans hτ.symm)
  let c' : Sym2 ℕ → Bool := fun p => c (Sym2.map e p)
  rcases ppl035_infinite_ramsey_nat_k k c' with ⟨f, hf⟩ | ⟨g, hg⟩
  · left
    refine ⟨e.symm.toOrderEmbedding.trans (f.trans e.toOrderEmbedding), ?_⟩
    intro x y hxy
    have hlt : e.symm x < e.symm y := e.symm.lt_iff_lt.mpr hxy
    have h := hf (e.symm x) (e.symm y) hlt
    simpa [c'] using h
  · right
    refine ⟨g.trans e.toOrderEmbedding, ?_⟩
    intro i j hij
    have h := hg i j hij
    simpa [c'] using h

/-- **1-Tuple Indecomposable Ordinal Partition Theorem (`ω^β → (ω^β)^1_2`):**
For every ordinal `β`, if the union `S₁ ∪ S₂` of two subsets of a well-ordered type has order
type at least `ω^β`, then at least one of `S₁` or `S₂` has order type at least `ω^β`.
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_opow_omega0_union_partition (β : Ordinal.{0}) :
    ∀ {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)] (S₁ S₂ : Set τ),
      Ordinal.omega0 ^ β ≤ Ordinal.type ((· < ·) : ↑(S₁ ∪ S₂) → ↑(S₁ ∪ S₂) → Prop) →
      Ordinal.omega0 ^ β ≤ Ordinal.type ((· < ·) : ↑S₁ → ↑S₁ → Prop) ∨
      Ordinal.omega0 ^ β ≤ Ordinal.type ((· < ·) : ↑S₂ → ↑S₂ → Prop) := by
  refine Ordinal.limitRecOn (motive := fun β =>
    ∀ {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)] (S₁ S₂ : Set τ),
      Ordinal.omega0 ^ β ≤ Ordinal.type ((· < ·) : ↑(S₁ ∪ S₂) → ↑(S₁ ∪ S₂) → Prop) →
      Ordinal.omega0 ^ β ≤ Ordinal.type ((· < ·) : ↑S₁ → ↑S₁ → Prop) ∨
      Ordinal.omega0 ^ β ≤ Ordinal.type ((· < ·) : ↑S₂ → ↑S₂ → Prop)) β ?_ ?_ ?_
  · intro τ _ _ S₁ S₂ hle
    rw [opow_zero] at hle ⊢
    have hne : Nonempty ↑(S₁ ∪ S₂) := by
      by_contra hempty
      have : IsEmpty ↑(S₁ ∪ S₂) := not_nonempty_iff.mp hempty
      rw [Ordinal.type_eq_zero_of_empty] at hle
      exact not_le_of_gt zero_lt_one hle
    obtain ⟨⟨x, hx⟩⟩ := hne
    rcases hx with hx₁ | hx₂
    · left
      rw [show (1 : Ordinal) = ((1 : ℕ) : Ordinal) by norm_num, ← Ordinal.type_fin 1]
      refine Ordinal.type_le_iff'.mpr ⟨⟨⟨fun _ => ⟨x, hx₁⟩, fun a b _ => Subsingleton.elim a b⟩, ?_⟩⟩
      intro a b; simp [Subsingleton.elim a b]
    · right
      rw [show (1 : Ordinal) = ((1 : ℕ) : Ordinal) by norm_num, ← Ordinal.type_fin 1]
      refine Ordinal.type_le_iff'.mpr ⟨⟨⟨fun _ => ⟨x, hx₂⟩, fun a b _ => Subsingleton.elim a b⟩, ?_⟩⟩
      intro a b; simp [Subsingleton.elim a b]
  · intro γ ih τ _ _ S₁ S₂ hle
    rw [Ordinal.opow_add, opow_one] at hle ⊢
    have hprod : Ordinal.type ((· < ·) : Lex (ℕ × (Ordinal.omega0 ^ γ).ToType) → _ → Prop) =
        Ordinal.omega0 ^ γ * Ordinal.omega0 := by
      rw [type_lex_prod, Ordinal.type_toType, Ordinal.type_nat_lt]
    rw [← hprod] at hle
    obtain ⟨emb⟩ := Ordinal.type_le_iff'.mp hle
    let B : ℕ → Set τ := fun n => Set.range (fun a : (Ordinal.omega0 ^ γ).ToType => (emb (toLex (n, a))).1)
    have hBsub : ∀ n, B n ⊆ S₁ ∪ S₂ := by
      rintro n _ ⟨a, rfl⟩
      exact (emb (toLex (n, a))).2
    have hBle : ∀ n, Ordinal.omega0 ^ γ ≤
        Ordinal.type ((· < ·) : ↑(B n ∩ S₁ ∪ B n ∩ S₂) → _ → Prop) := by
      intro n
      have heq : B n ∩ S₁ ∪ B n ∩ S₂ = B n := by
        ext x
        constructor
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        · intro hx
          rcases hBsub n hx with h1 | h2
          · exact Or.inl ⟨hx, h1⟩
          · exact Or.inr ⟨hx, h2⟩
      rw [heq, ← Ordinal.type_toType (Ordinal.omega0 ^ γ)]
      refine Ordinal.type_le_iff'.mpr ⟨?_⟩
      refine ⟨⟨fun a => ⟨(emb (toLex (n, a))).1, ⟨a, rfl⟩⟩, ?_⟩, ?_⟩
      · intro a b hab
        dsimp only at hab
        have h1 : (emb (toLex (n, a))).1 = (emb (toLex (n, b))).1 := Subtype.mk.inj hab
        have h2 : emb (toLex (n, a)) = emb (toLex (n, b)) := Subtype.ext h1
        have h3 := emb.injective h2
        exact (Prod.mk.inj h3).2
      · intro a b
        show (emb (toLex (n, a))).1 < (emb (toLex (n, b))).1 ↔ a < b
        change emb (toLex (n, a)) < emb (toLex (n, b)) ↔ a < b
        rw [emb.map_rel_iff]
        show Prod.Lex (· < ·) (· < ·) (n, a) (n, b) ↔ a < b
        rw [Prod.lex_def]
        simp
    have hblock : ∀ n : ℕ,
        Ordinal.omega0 ^ γ ≤ Ordinal.type ((· < ·) : ↑(B n ∩ S₁) → _ → Prop) ∨
        Ordinal.omega0 ^ γ ≤ Ordinal.type ((· < ·) : ↑(B n ∩ S₂) → _ → Prop) :=
      fun n => ih (B n ∩ S₁) (B n ∩ S₂) (hBle n)
    let I₁ : Set ℕ := {n | Ordinal.omega0 ^ γ ≤ Ordinal.type ((· < ·) : ↑(B n ∩ S₁) → _ → Prop)}
    let I₂ : Set ℕ := {n | Ordinal.omega0 ^ γ ≤ Ordinal.type ((· < ·) : ↑(B n ∩ S₂) → _ → Prop)}
    have huniv : I₁ ∪ I₂ = Set.univ := Set.eq_univ_of_forall hblock
    have hinf : I₁.Infinite ∨ I₂.Infinite := by
      by_contra h
      push Not at h
      have hfin : (Set.univ : Set ℕ).Finite := by
        rw [← huniv]
        exact h.1.union h.2
      exact Set.infinite_univ hfin
    have assemble : ∀ (S : Set τ) (I : Set ℕ), I.Infinite →
        (∀ n ∈ I, Ordinal.omega0 ^ γ ≤ Ordinal.type ((· < ·) : ↑(B n ∩ S) → _ → Prop)) →
        Ordinal.omega0 ^ γ * Ordinal.omega0 ≤ Ordinal.type ((· < ·) : ↑S → ↑S → Prop) := by
      intro S I hIinf hI
      obtain ⟨idx, hidx⟩ := exists_strictMono_of_infinite_nat hIinf
      have hslice : ∀ k : ℕ, Nonempty (((· < ·) : (Ordinal.omega0 ^ γ).ToType → _ → Prop) ↪r
          ((· < ·) : ↑(B (idx k) ∩ S) → _ → Prop)) := fun k => by
        have hle' := hI (idx k) (hidx k)
        rw [← Ordinal.type_toType (Ordinal.omega0 ^ γ)] at hle'
        exact Ordinal.type_le_iff'.mp hle'
      let φ : (k : ℕ) → ((· < ·) : (Ordinal.omega0 ^ γ).ToType → _ → Prop) ↪r
          ((· < ·) : ↑(B (idx k) ∩ S) → _ → Prop) := fun k => Classical.choice (hslice k)
      rw [← hprod]
      refine Ordinal.type_le_iff'.mpr ⟨?_⟩
      have hsep : ∀ {k₁ k₂ : ℕ} (a₁ a₂ : (Ordinal.omega0 ^ γ).ToType),
          k₁ < k₂ → (φ k₁ a₁).1 < (φ k₂ a₂).1 := by
        intro k₁ k₂ a₁ a₂ hk
        obtain ⟨u₁, hu₁⟩ := (φ k₁ a₁).2.1
        obtain ⟨u₂, hu₂⟩ := (φ k₂ a₂).2.1
        rw [← hu₁, ← hu₂]
        change emb (toLex (idx k₁, u₁)) < emb (toLex (idx k₂, u₂))
        rw [emb.map_rel_iff]
        exact Prod.Lex.left _ _ (idx.strictMono hk)
      refine ⟨⟨fun p => ⟨(φ (ofLex p).1 (ofLex p).2).1, (φ (ofLex p).1 (ofLex p).2).2.2⟩, ?_⟩, ?_⟩
      · intro p q heq
        rcases p with ⟨k₁, a₁⟩
        rcases q with ⟨k₂, a₂⟩
        have hval : (φ k₁ a₁).1 = (φ k₂ a₂).1 := congrArg Subtype.val heq
        rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
        · exact (ne_of_lt (hsep a₁ a₂ hlt) hval).elim
        · have ha : φ k₁ a₁ = φ k₁ a₂ := Subtype.ext hval
          rw [(φ k₁).injective ha]
        · exact (ne_of_gt (hsep a₂ a₁ hgt) hval).elim
      · intro p q
        rcases p with ⟨k₁, a₁⟩
        rcases q with ⟨k₂, a₂⟩
        show (φ k₁ a₁).1 < (φ k₂ a₂).1 ↔ Prod.Lex (· < ·) (· < ·) (k₁, a₁) (k₂, a₂)
        constructor
        · intro hlt
          rcases lt_trichotomy k₁ k₂ with hk | rfl | hk
          · exact Prod.Lex.left _ _ hk
          · exact Prod.Lex.right _ ((φ k₁).map_rel_iff.mp hlt)
          · exact (not_lt_of_gt (hsep a₂ a₁ hk) hlt).elim
        · intro hlex
          rcases Prod.lex_def.mp hlex with hk | ⟨rfl, ha⟩
          · exact hsep a₁ a₂ hk
          · exact (φ k₁).map_rel_iff.mpr ha
    rcases hinf with h1 | h2
    · exact Or.inl (assemble S₁ I₁ h1 (fun n hn => hn))
    · exact Or.inr (assemble S₂ I₂ h2 (fun n hn => hn))
  · intro l hl ih τ _ _ S₁ S₂ hle
    by_contra hnot
    push Not at hnot
    have hsup : Ordinal.omega0 ^ l = ⨆ γ : Set.Iio l, Ordinal.omega0 ^ (γ : Ordinal) := by
      have hnorm := Ordinal.isNormal_opow (a := Ordinal.omega0) (by norm_num)
      exact hnorm.apply_of_isSuccLimit hl
    have hlt_ex : ∀ o : Ordinal, o < Ordinal.omega0 ^ l → ∃ γ < l, o < Ordinal.omega0 ^ γ := by
      intro o ho
      rw [hsup] at ho
      obtain ⟨⟨γ, hγ⟩, hlt⟩ := Ordinal.lt_iSup_iff.mp ho
      exact ⟨γ, hγ, hlt⟩
    obtain ⟨γ₁, hγ₁, h1⟩ := hlt_ex _ hnot.1
    obtain ⟨γ₂, hγ₂, h2⟩ := hlt_ex _ hnot.2
    let γ := max γ₁ γ₂
    have hγl : γ < l := max_lt hγ₁ hγ₂
    have h1' : Ordinal.type ((· < ·) : ↑S₁ → ↑S₁ → Prop) < Ordinal.omega0 ^ γ :=
      lt_of_lt_of_le h1 (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_left _ _))
    have h2' : Ordinal.type ((· < ·) : ↑S₂ → ↑S₂ → Prop) < Ordinal.omega0 ^ γ :=
      lt_of_lt_of_le h2 (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_right _ _))
    have hle' : Ordinal.omega0 ^ γ ≤ Ordinal.type ((· < ·) : ↑(S₁ ∪ S₂) → ↑(S₁ ∪ S₂) → Prop) :=
      le_trans (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_of_lt hγl)) hle
    rcases ih γ hγl S₁ S₂ hle' with h | h
    · exact not_lt_of_ge h h1'
    · exact not_lt_of_ge h h2'

/-! ### Section 2: Specker's Positive Theorem (1957): `ω^2 → (ω^2, k)^2` and `ω^2 → (ω^2, 3)^2` -/

/-- Helper: Any subset of `Lex (ℕ × ℕ)` with infinitely many infinite rows embeds `Lex (ℕ × ℕ)`. -/
private lemma exists_lex_emb_of_inf_rows (S : Set (Lex (ℕ × ℕ)))
    (hS : {r : ℕ | {a : ℕ | toLex (r, a) ∈ S}.Infinite}.Infinite) :
    ∃ f : Lex (ℕ × ℕ) ↪o Lex (ℕ × ℕ), ∀ p, f p ∈ S := by
  obtain ⟨rows, hrows⟩ := exists_strictMono_of_infinite_nat hS
  have hcol : ∀ i : ℕ, ∃ g : ℕ ↪o ℕ, ∀ m, toLex (rows i, g m) ∈ S :=
    fun i => exists_strictMono_of_infinite_nat (hrows i)
  let cols : ℕ → (ℕ ↪o ℕ) := fun i => Classical.choose (hcol i)
  have hcols : ∀ i m, toLex (rows i, cols i m) ∈ S :=
    fun i => Classical.choose_spec (hcol i)
  refine ⟨OrderEmbedding.ofStrictMono
    (fun p => toLex (rows (ofLex p).1, cols (ofLex p).1 (ofLex p).2)) ?_, ?_⟩
  · intro p q hpq
    rcases p with ⟨p1, p2⟩
    rcases q with ⟨q1, q2⟩
    rcases Prod.lex_def.mp hpq with h1 | ⟨rfl, h2⟩
    · exact Prod.Lex.left _ _ (rows.strictMono h1)
    · exact Prod.Lex.right _ ((cols p1).strictMono h2)
  · intro p
    exact hcols (ofLex p).1 (ofLex p).2

/-- **Specker's Positive Theorem (1957) on `Lex (ℕ × ℕ)` (`ω^2 → (ω^2, k)^2` for all `k : ℕ`):**
Every 2-coloring of unordered pairs of `Lex (ℕ × ℕ)` yields either a red order-isomorphic copy
of `Lex (ℕ × ℕ)` or a blue `K_k`. Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_specker_positive_lex (k : ℕ) :
    ∀ (c : Sym2 (Lex (ℕ × ℕ)) → Bool),
      (∃ f : Lex (ℕ × ℕ) ↪o Lex (ℕ × ℕ), ∀ p q, p < q → c s(f p, f q) = true) ∨
      (∃ g : Fin k ↪o Lex (ℕ × ℕ), ∀ i j, i < j → c s(g i, g j) = false) := by
  classical
  induction k with
  | zero =>
    intro c
    right
    exact ⟨OrderEmbedding.ofStrictMono (fun i : Fin 0 => i.elim0) (fun i => i.elim0),
      fun i => i.elim0⟩
  | succ k ih =>
    intro c
    by_cases hblue : ∃ g : Fin (k + 1) ↪o Lex (ℕ × ℕ), ∀ i j, i < j → c s(g i, g j) = false
    · exact Or.inr hblue
    · left
      -- Step 1: Thin each row to an all-red infinite copy of `ℕ`.
      have hrow : ∀ r : ℕ, ∃ fr : ℕ ↪o ℕ, ∀ a b, a < b →
          c s(toLex (r, fr a), toLex (r, fr b)) = true := by
        intro r
        let cr : Sym2 ℕ → Bool := fun p => c (Sym2.map (fun a => toLex (r, a)) p)
        rcases ppl035_infinite_ramsey_nat_k (k + 1) cr with ⟨fr, hfr⟩ | ⟨gr, hgr⟩
        · exact ⟨fr, fun a b hab => by simpa [cr] using hfr a b hab⟩
        · exfalso
          apply hblue
          let g : Fin (k + 1) ↪o Lex (ℕ × ℕ) :=
            OrderEmbedding.ofStrictMono (fun i => toLex (r, gr i))
              (fun i j hij => Prod.Lex.right _ (gr.strictMono hij))
          refine ⟨g, fun i j hij => ?_⟩
          have h := hgr i j hij
          exact h
      let rowF : ℕ → (ℕ ↪o ℕ) := fun r => Classical.choose (hrow r)
      have hrowF : ∀ r a b, a < b →
          c s(toLex (r, rowF r a), toLex (r, rowF r b)) = true :=
        fun r => Classical.choose_spec (hrow r)
      let rowEmb : Lex (ℕ × ℕ) ↪o Lex (ℕ × ℕ) :=
        OrderEmbedding.ofStrictMono
          (fun q => toLex ((ofLex q).1, rowF (ofLex q).1 (ofLex q).2))
          (by
            intro p q hpq
            rcases p with ⟨p1, p2⟩
            rcases q with ⟨q1, q2⟩
            rcases Prod.lex_def.mp hpq with h1 | ⟨rfl, h2⟩
            · exact Prod.Lex.left _ _ h1
            · exact Prod.Lex.right _ ((rowF p1).strictMono h2))
      let c1 : Sym2 (Lex (ℕ × ℕ)) → Bool := fun p => c (Sym2.map rowEmb p)
      have hc1_row : ∀ r a b, a < b → c1 s(toLex (r, a), toLex (r, b)) = true :=
        fun r a b hab => hrowF r a b hab
      have hc1_noblue : ¬ ∃ g : Fin (k + 1) ↪o Lex (ℕ × ℕ),
          ∀ i j, i < j → c1 s(g i, g j) = false := by
        rintro ⟨g, hg⟩
        apply hblue
        exact ⟨g.trans rowEmb, fun i j hij => by simpa [c1] using hg i j hij⟩
      suffices hred1 : ∃ f : Lex (ℕ × ℕ) ↪o Lex (ℕ × ℕ), ∀ p q, p < q → c1 s(f p, f q) = true by
        obtain ⟨f, hf⟩ := hred1
        exact ⟨f.trans rowEmb, fun p q hpq => by simpa [c1] using hf p q hpq⟩
      -- Fix the non-principal ultrafilter `𝒰 = Filter.hyperfilter ℕ`.
      let 𝒰 : Ultrafilter ℕ := Filter.hyperfilter ℕ
      have hU_inf : ∀ {s : Set ℕ}, s ∈ 𝒰 → s.Infinite := by
        intro s hs
        by_contra hfin
        rw [Set.not_infinite] at hfin
        have hcof : sᶜ ∈ Filter.cofinite := by
          rw [Filter.mem_cofinite, compl_compl]
          exact hfin
        have hsc : sᶜ ∈ 𝒰 := Filter.hyperfilter_le_cofinite hcof
        exact 𝒰.compl_notMem_iff.mpr hs hsc
      have hU_tail : ∀ m : ℕ, {a : ℕ | m < a} ∈ 𝒰 := fun m =>
        Filter.hyperfilter_le_cofinite (by
          rw [Filter.mem_cofinite]
          have hsub : {a : ℕ | m < a}ᶜ ⊆ {a : ℕ | a ≤ m} := fun a ha =>
            le_of_not_gt (by simpa using ha)
          exact (Set.finite_le_nat m).subset hsub)
      -- Step 2: Check whether some vertex has infinitely many rows with `𝒰`-large blue neighborhood.
      by_cases hv : ∃ v : Lex (ℕ × ℕ),
          {s : ℕ | {b : ℕ | c1 s(v, toLex (s, b)) = false} ∈ 𝒰}.Infinite
      · obtain ⟨v, hvinf⟩ := hv
        let S : Set (Lex (ℕ × ℕ)) := {q | q ≠ v ∧ c1 s(v, q) = false}
        have hSrows : {s : ℕ | {b : ℕ | toLex (s, b) ∈ S}.Infinite}.Infinite := by
          have hdiff : ({s : ℕ | {b : ℕ | c1 s(v, toLex (s, b)) = false} ∈ 𝒰} \ {(ofLex v).1}).Infinite :=
            hvinf.sdiff (Set.finite_singleton _)
          refine hdiff.mono ?_
          intro s ⟨hsU, hsne⟩
          have hinf := hU_inf hsU
          refine hinf.mono ?_
          intro b hb
          refine ⟨?_, hb⟩
          intro heq
          have h1 : s = (ofLex v).1 := congrArg (fun p : Lex (ℕ × ℕ) => (ofLex p).1) heq
          exact hsne h1
        obtain ⟨eS, heS⟩ := exists_lex_emb_of_inf_rows S hSrows
        let cS : Sym2 (Lex (ℕ × ℕ)) → Bool := fun p => c1 (Sym2.map eS p)
        rcases ih cS with ⟨fS, hfS⟩ | ⟨gS, hgS⟩
        · exact ⟨fS.trans eS, fun p q hpq => by simpa [cS] using hfS p q hpq⟩
        · exfalso
          apply hc1_noblue
          let pts : Finset (Lex (ℕ × ℕ)) :=
            insert v (Finset.univ.image (fun i : Fin k => eS (gS i)))
          have hvnot : v ∉ Finset.univ.image (fun i : Fin k => eS (gS i)) := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
            exact (heS (gS i)).1 hi
          have hcard : pts.card = k + 1 := by
            rw [Finset.card_insert_of_notMem hvnot,
              Finset.card_image_of_injective _ (fun a b h => gS.injective (eS.injective h)),
              Finset.card_fin]
          let iso := pts.orderIsoOfFin hcard
          refine ⟨iso.toOrderEmbedding.trans (OrderEmbedding.subtype _), ?_⟩
          intro i j hij
          change c1 s((iso i).1, (iso j).1) = false
          have hne : (iso i).1 ≠ (iso j).1 := ne_of_lt (iso.strictMono hij)
          have hi := (iso i).2
          have hj := (iso j).2
          rcases Finset.mem_insert.mp hi with hi_eq | hi_img <;>
          rcases Finset.mem_insert.mp hj with hj_eq | hj_img
          · exact (hne (hi_eq.trans hj_eq.symm)).elim
          · rcases Finset.mem_image.mp hj_img with ⟨b, _, hb⟩
            rw [hi_eq, ← hb]
            exact (heS (gS b)).2
          · rcases Finset.mem_image.mp hi_img with ⟨a, _, ha⟩
            rw [hj_eq, ← ha, Sym2.eq_swap]
            exact (heS (gS a)).2
          · rcases Finset.mem_image.mp hi_img with ⟨a, _, ha⟩
            rcases Finset.mem_image.mp hj_img with ⟨b, _, hb⟩
            rw [← ha, ← hb]
            rcases lt_trichotomy a b with hab | rfl | hba
            · simpa [cS] using hgS a b hab
            · exact (hne (ha.symm.trans hb)).elim
            · rw [Sym2.eq_swap]; simpa [cS] using hgS b a hba
      · -- Step 3: For every `v`, `∃ M(v), ∀ s ≥ M(v), N_R(v) ∩ R_s ∈ 𝒰`.
        push Not at hv
        have hM : ∀ v : Lex (ℕ × ℕ), ∃ M : ℕ, ∀ s, M ≤ s →
            {b : ℕ | c1 s(v, toLex (s, b)) = true} ∈ 𝒰 := by
          intro v
          have hfin : {s : ℕ | {b : ℕ | c1 s(v, toLex (s, b)) = false} ∈ 𝒰}.Finite := hv v
          obtain ⟨M, hMbound⟩ := hfin.bddAbove
          refine ⟨M + 1, fun s hs => ?_⟩
          have hnot : {b : ℕ | c1 s(v, toLex (s, b)) = false} ∉ 𝒰 := by
            intro hmem
            have hle : s ≤ M := hMbound hmem
            omega
          have hc : {b : ℕ | c1 s(v, toLex (s, b)) = false}ᶜ ∈ 𝒰 :=
            𝒰.compl_mem_iff_notMem.mpr hnot
          refine 𝒰.sets_of_superset hc ?_
          intro b hb
          change ¬ c1 s(v, toLex (s, b)) = false at hb
          exact Bool.eq_true_of_not_eq_false hb
        let Mfun : Lex (ℕ × ℕ) → ℕ := fun v => Classical.choose (hM v)
        have hMfun : ∀ v s, Mfun v ≤ s → {b : ℕ | c1 s(v, toLex (s, b)) = true} ∈ 𝒰 :=
          fun v => Classical.choose_spec (hM v)
        -- Step 4: Directed ultrafilter graph on rows.
        let E : ℕ → ℕ → Set ℕ :=
          fun r s => {a : ℕ | {b : ℕ | c1 s(toLex (r, a), toLex (s, b)) = false} ∈ 𝒰}
        let arr : ℕ → ℕ → Prop := fun r s => E r s ∈ 𝒰
        have hno_clique : ∀ rs : Fin (k + 1) → ℕ, Function.Injective rs →
            ¬ ∀ i j : Fin (k + 1), i < j → arr (rs i) (rs j) := by
          intro rs hrinj harr
          have hbuild : ∀ m : ℕ, (hm : m ≤ k + 1) →
              ∃ a : Fin m → ℕ,
                (∀ i j : Fin m, i < j →
                  c1 s(toLex (rs ⟨i.1, by omega⟩, a i), toLex (rs ⟨j.1, by omega⟩, a j)) = false) ∧
                (∀ j : Fin (k + 1), m ≤ j.1 →
                  (⋂ i : Fin m, {b : ℕ | c1 s(toLex (rs ⟨i.1, by omega⟩, a i), toLex (rs j, b)) = false}) ∈ 𝒰) := by
            intro m
            induction m with
            | zero =>
              intro _
              refine ⟨fun i => i.elim0, fun i => i.elim0, fun j _ => ?_⟩
              have heq : (⋂ i : Fin 0, {b : ℕ | c1 s(toLex (rs ⟨i.1, by omega⟩, i.elim0), toLex (rs j, b)) = false}) = Set.univ := by
                ext b; simp
              rw [heq]
              exact Filter.univ_mem
            | succ m ihm =>
              intro hm
              obtain ⟨a, ha_blue, ha_U⟩ := ihm (by omega)
              let j0 : Fin (k + 1) := ⟨m, by omega⟩
              have hS0 : (⋂ i : Fin m, {b : ℕ | c1 s(toLex (rs ⟨i.1, by omega⟩, a i), toLex (rs j0, b)) = false}) ∈ 𝒰 :=
                ha_U j0 (le_refl m)
              have hE_all : (⋂ j : {j : Fin (k + 1) // m < j.1}, E (rs j0) (rs j.1)) ∈ (𝒰 : Filter ℕ) := by
                rw [Filter.iInter_mem]
                intro j
                exact harr j0 j.1 j.2
              have hinter : ((⋂ i : Fin m, {b : ℕ | c1 s(toLex (rs ⟨i.1, by omega⟩, a i), toLex (rs j0, b)) = false}) ∩
                  (⋂ j : {j : Fin (k + 1) // m < j.1}, E (rs j0) (rs j.1))) ∈ 𝒰 :=
                𝒰.inter_sets hS0 hE_all
              obtain ⟨am, ham1, ham2⟩ := (hU_inf hinter).nonempty
              let a' : Fin (m + 1) → ℕ := fun i =>
                if hi : i.1 < m then a ⟨i.1, hi⟩ else am
              refine ⟨a', ?_, ?_⟩
              · intro i j hij
                by_cases hj : j.1 < m
                · have hi : i.1 < m := lt_trans hij hj
                  simp only [a', dif_pos hi, dif_pos hj]
                  exact ha_blue ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij
                · have hjm : j.1 = m := by omega
                  have hi : i.1 < m := by omega
                  simp only [a', dif_pos hi, dif_neg hj]
                  have hmem := Set.mem_iInter.mp ham1 ⟨i.1, hi⟩
                  have hj_eq : (⟨j.1, by omega⟩ : Fin (k + 1)) = j0 := Fin.ext hjm
                  rw [hj_eq]
                  exact hmem
              · intro j hmj
                change (⋂ i : Fin (m + 1), _) ∈ (𝒰 : Filter ℕ)
                rw [Filter.iInter_mem]
                intro i
                by_cases hi : i.1 < m
                · simp only [a', dif_pos hi]
                  have hU_prev : (⋂ i : Fin m, _) ∈ (𝒰 : Filter ℕ) := ha_U j (by omega)
                  exact (Filter.iInter_mem.mp hU_prev) ⟨i.1, hi⟩
                · have him : i.1 = m := by omega
                  simp only [a', dif_neg hi]
                  have hi_eq : (⟨i.1, by omega⟩ : Fin (k + 1)) = j0 := Fin.ext him
                  rw [hi_eq]
                  exact Set.mem_iInter.mp ham2 ⟨j, by omega⟩
          obtain ⟨a, ha_blue, _⟩ := hbuild (k + 1) (le_refl _)
          apply hc1_noblue
          let pts : Finset (Lex (ℕ × ℕ)) := Finset.univ.image (fun i : Fin (k + 1) => toLex (rs i, a i))
          have hinj : Function.Injective (fun i : Fin (k + 1) => toLex (rs i, a i)) := by
            intro i j heq
            exact hrinj (congrArg (fun p : Lex (ℕ × ℕ) => (ofLex p).1) heq)
          have hcard : pts.card = k + 1 := by
            rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
          let iso := pts.orderIsoOfFin hcard
          refine ⟨iso.toOrderEmbedding.trans (OrderEmbedding.subtype _), ?_⟩
          intro i j hij
          change c1 s((iso i).1, (iso j).1) = false
          obtain ⟨i', _, hi'⟩ := Finset.mem_image.mp (iso i).2
          obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp (iso j).2
          rw [← hi', ← hj']
          rcases lt_trichotomy i' j' with hlt | rfl | hgt
          · exact ha_blue i' j' hlt
          · exact (ne_of_lt (iso.strictMono hij) (Subtype.ext (hi'.symm.trans hj'))).elim
          · rw [Sym2.eq_swap]; exact ha_blue j' i' hgt
        let c_fwd : Sym2 ℕ → Bool := Sym2.lift ⟨fun r s => decide (¬ arr (min r s) (max r s)),
          by intro r s; simp [min_comm, max_comm]⟩
        have hI1 : ∃ f1 : ℕ ↪o ℕ, ∀ i j, i < j → ¬ arr (f1 i) (f1 j) := by
          rcases ppl035_infinite_ramsey_nat_k (k + 1) c_fwd with ⟨f1, hf1⟩ | ⟨g1, hg1⟩
          · refine ⟨f1, fun i j hij => ?_⟩
            have h := hf1 i j hij
            have hlt : f1 i < f1 j := f1.strictMono hij
            simp only [c_fwd, Sym2.lift_mk, min_eq_left (le_of_lt hlt),
              max_eq_right (le_of_lt hlt), decide_eq_true_eq] at h
            exact h
          · exfalso
            refine hno_clique g1 g1.injective ?_
            intro i j hij
            have h := hg1 i j hij
            have hlt : g1 i < g1 j := g1.strictMono hij
            simp only [c_fwd, Sym2.lift_mk, min_eq_left (le_of_lt hlt),
              max_eq_right (le_of_lt hlt), decide_eq_false_iff_not, not_not] at h
            exact h
        obtain ⟨f1, hf1⟩ := hI1
        let c_bwd : Sym2 ℕ → Bool := Sym2.lift ⟨fun i j => decide (¬ arr (f1 (max i j)) (f1 (min i j))),
          by intro i j; simp [min_comm, max_comm]⟩
        have hI2 : ∃ f2 : ℕ ↪o ℕ, ∀ i j, i ≠ j → ¬ arr (f2 i) (f2 j) := by
          rcases ppl035_infinite_ramsey_nat_k (k + 1) c_bwd with ⟨f2, hf2⟩ | ⟨g2, hg2⟩
          · refine ⟨f2.trans f1, fun i j hij => ?_⟩
            rcases lt_or_gt_of_ne hij with hlt | hgt
            · exact hf1 (f2 i) (f2 j) (f2.strictMono hlt)
            · have h := hf2 j i hgt
              have hlt' : f2 j < f2 i := f2.strictMono hgt
              simp only [c_bwd, Sym2.lift_mk, min_eq_left (le_of_lt hlt'),
                max_eq_right (le_of_lt hlt'), decide_eq_true_eq] at h
              exact h
          · exfalso
            let rev : Fin (k + 1) → ℕ := fun i => f1 (g2 i.rev)
            have hrevinj : Function.Injective rev :=
              f1.injective.comp (g2.injective.comp Fin.rev_injective)
            refine hno_clique rev hrevinj ?_
            intro i j hij
            have hlt : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
            have h := hg2 j.rev i.rev hlt
            have hglt : g2 j.rev < g2 i.rev := g2.strictMono hlt
            simp only [c_bwd, Sym2.lift_mk, min_eq_left (le_of_lt hglt),
              max_eq_right (le_of_lt hglt), decide_eq_false_iff_not, not_not] at h
            exact h
        obtain ⟨fI, hfI⟩ := hI2
        let G : ℕ → ℕ → Set ℕ :=
          fun r s => {a : ℕ | {b : ℕ | c1 s(toLex (r, a), toLex (s, b)) = true} ∈ 𝒰}
        have hG : ∀ i j : ℕ, i ≠ j → G (fI i) (fI j) ∈ 𝒰 := by
          intro i j hij
          have hnot : E (fI i) (fI j) ∉ 𝒰 := hfI i j hij
          have hc : (E (fI i) (fI j))ᶜ ∈ 𝒰 := 𝒰.compl_mem_iff_notMem.mpr hnot
          refine 𝒰.sets_of_superset hc ?_
          intro a ha
          change {b : ℕ | c1 s(toLex (fI i, a), toLex (fI j, b)) = false} ∉ 𝒰 at ha
          have hbc : {b : ℕ | c1 s(toLex (fI i, a), toLex (fI j, b)) = false}ᶜ ∈ 𝒰 :=
            𝒰.compl_mem_iff_notMem.mpr ha
          exact 𝒰.sets_of_superset hbc (fun b hb => Bool.eq_true_of_not_eq_false hb)
        -- Step 5: Clean non-dependent dynamic diagonalization!
        -- `State n` stores `(rIdx : ℕ → ℕ, pts : ℕ → ℕ → ℕ)` valid on `i < n` and `i + m < n`.
        let State (n : ℕ) :=
          { st : (ℕ → ℕ) × (ℕ → ℕ → ℕ) //
            (∀ i j, i < j → j < n → st.1 i < st.1 j) ∧
            (∀ i m₁ m₂, m₁ < m₂ → i + m₂ < n → st.2 i m₁ < st.2 i m₂) ∧
            (∀ i₁ i₂ m₁ m₂, i₁ + m₁ < n → i₂ + m₂ < n → i₁ ≠ i₂ →
              c1 s(toLex (fI (st.1 i₁), st.2 i₁ m₁), toLex (fI (st.1 i₂), st.2 i₂ m₂)) = true) ∧
            (∀ i j m, i + m < n → j < n → i ≠ j →
              {b : ℕ | c1 s(toLex (fI (st.1 i), st.2 i m), toLex (fI (st.1 j), b)) = true} ∈ 𝒰) }
        have hstep : ∀ n (st : State n), ∃ st' : State (n + 1),
            (∀ i, i < n → st'.1.1 i = st.1.1 i) ∧
            (∀ i m, i + m < n → st'.1.2 i m = st.1.2 i m) := by
          intro n st
          let rn : ℕ :=
            ((Finset.range n).sup st.1.1) +
            ((Finset.range n).sup (fun i =>
              (Finset.range n).sup (fun m => Mfun (toLex (fI (st.1.1 i), st.1.2 i m))))) + 1
          let rIdx' : ℕ → ℕ := fun i => if i < n then st.1.1 i else rn
          have hrIdx'_mono : ∀ i j, i < j → j < n + 1 → rIdx' i < rIdx' j := by
            intro i j hij hjn
            by_cases hj : j < n
            · have hi : i < n := lt_trans hij hj
              simp only [rIdx', if_pos hi, if_pos hj]
              exact st.2.1 i j hij hj
            · have hi : i < n := by omega
              simp only [rIdx', if_pos hi, if_neg hj]
              have hle : st.1.1 i ≤ (Finset.range n).sup st.1.1 :=
                Finset.le_sup (Finset.mem_range.mpr hi)
              omega
          have hrIdx'_inj : ∀ i j, i < n + 1 → j < n + 1 → rIdx' i = rIdx' j → i = j := by
            intro i j hi hj heq
            rcases lt_trichotomy i j with h | h | h
            · exact (ne_of_lt (hrIdx'_mono i j h hj) heq).elim
            · exact h
            · exact (ne_of_gt (hrIdx'_mono j i h hi) heq).elim
          -- Inner induction over `t ≤ n + 1`: active pairs are `Act t i m := i + m < n ∨ (i < t ∧ i + m = n)`.
          let Act (t i m : ℕ) : Prop := i + m < n ∨ (i < t ∧ i + m = n)
          have hinner : ∀ t, t ≤ n + 1 →
              ∃ pts : ℕ → ℕ → ℕ,
                (∀ i m, i + m < n → pts i m = st.1.2 i m) ∧
                (∀ i m₁ m₂, m₁ < m₂ → Act t i m₂ → pts i m₁ < pts i m₂) ∧
                (∀ i₁ i₂ m₁ m₂, Act t i₁ m₁ → Act t i₂ m₂ → i₁ ≠ i₂ →
                  c1 s(toLex (fI (rIdx' i₁), pts i₁ m₁), toLex (fI (rIdx' i₂), pts i₂ m₂)) = true) ∧
                (∀ i j m, Act t i m → j < n + 1 → i ≠ j →
                  {b : ℕ | c1 s(toLex (fI (rIdx' i), pts i m), toLex (fI (rIdx' j), b)) = true} ∈ 𝒰) := by
            intro t
            induction t with
            | zero =>
              intro _
              refine ⟨st.1.2, fun _ _ _ => rfl, ?_, ?_, ?_⟩
              · intro i m₁ m₂ hlt hact
                rcases hact with h | ⟨h, _⟩
                · exact st.2.2.1 i m₁ m₂ hlt h
                · omega
              · intro i₁ i₂ m₁ m₂ h1 h2 hne
                rcases h1 with h1 | ⟨h1, _⟩
                · rcases h2 with h2 | ⟨h2, _⟩
                  · simp only [rIdx', if_pos (by omega : i₁ < n), if_pos (by omega : i₂ < n)]
                    exact st.2.2.2.1 i₁ i₂ m₁ m₂ h1 h2 hne
                  · omega
                · omega
              · intro i j m hact hjn hij
                rcases hact with h | ⟨h, _⟩
                · have hi : i < n := by omega
                  simp only [rIdx', if_pos hi]
                  by_cases hj : j < n
                  · simp only [if_pos hj]
                    exact st.2.2.2.2 i j m h hj hij
                  · simp only [if_neg hj]
                    apply hMfun
                    have hle1 : Mfun (toLex (fI (st.1.1 i), st.1.2 i m)) ≤
                        (Finset.range n).sup (fun m' => Mfun (toLex (fI (st.1.1 i), st.1.2 i m'))) :=
                      Finset.le_sup (f := fun m' => Mfun (toLex (fI (st.1.1 i), st.1.2 i m')))
                        (Finset.mem_range.mpr (by omega : m < n))
                    have hle2 : ((Finset.range n).sup (fun m' => Mfun (toLex (fI (st.1.1 i), st.1.2 i m')))) ≤
                        (Finset.range n).sup (fun i' =>
                          (Finset.range n).sup (fun m' => Mfun (toLex (fI (st.1.1 i'), st.1.2 i' m')))) :=
                      Finset.le_sup (f := fun i' =>
                        (Finset.range n).sup (fun m' => Mfun (toLex (fI (st.1.1 i'), st.1.2 i' m'))))
                        (Finset.mem_range.mpr hi)
                    have hle_id : rn ≤ fI rn := fI.strictMono.id_le rn
                    omega
                · omega
            | succ t iht =>
              intro ht
              obtain ⟨pts, hpts_ext, hpts_mono, hpts_red, hpts_inv⟩ := iht (by omega)
              -- Add point `(t, n - t)` in row `t`!
              let S_tail : Set ℕ := {b : ℕ | ((Finset.range (n - t)).sup (fun m => pts t m)) < b}
              have hS_tail : S_tail ∈ 𝒰 := hU_tail _
              let S_red : Set ℕ :=
                ⋂ (j : Fin (n + 1)), ⋂ (m : Fin (n + 1)),
                  if Act t j.1 m.1 ∧ j.1 ≠ t then
                    {b : ℕ | c1 s(toLex (fI (rIdx' j.1), pts j.1 m.1), toLex (fI (rIdx' t), b)) = true}
                  else Set.univ
              have hS_red : S_red ∈ (𝒰 : Filter ℕ) := by
                change (⋂ (j : Fin (n + 1)), _) ∈ (𝒰 : Filter ℕ)
                rw [Filter.iInter_mem]
                intro j
                rw [Filter.iInter_mem]
                intro m
                by_cases h : Act t j.1 m.1 ∧ j.1 ≠ t
                · rw [if_pos h]
                  exact hpts_inv j.1 t m.1 h.1 (by omega) h.2
                · rw [if_neg h]
                  exact Filter.univ_mem
              let S_G : Set ℕ :=
                ⋂ (j : Fin (n + 1)),
                  if j.1 ≠ t then G (fI (rIdx' t)) (fI (rIdx' j.1)) else Set.univ
              have hS_G : S_G ∈ (𝒰 : Filter ℕ) := by
                change (⋂ (j : Fin (n + 1)), _) ∈ (𝒰 : Filter ℕ)
                rw [Filter.iInter_mem]
                intro j
                by_cases h : j.1 ≠ t
                · rw [if_pos h]
                  exact hG (rIdx' t) (rIdx' j.1)
                    (fun heq => h (hrIdx'_inj t j.1 (by omega) j.isLt heq).symm)
                · rw [if_neg h]
                  exact Filter.univ_mem
              have hall : (S_tail ∩ S_red ∩ S_G) ∈ 𝒰 :=
                𝒰.inter_sets (𝒰.inter_sets hS_tail hS_red) hS_G
              obtain ⟨aNew, ⟨ha_tail, ha_red⟩, ha_G⟩ := (hU_inf hall).nonempty
              let pts' : ℕ → ℕ → ℕ := fun i m => if i = t ∧ m = n - t then aNew else pts i m
              refine ⟨pts', ?_, ?_, ?_, ?_⟩
              · intro i m him
                have hne : ¬ (i = t ∧ m = n - t) := by omega
                simp only [pts', if_neg hne]
                exact hpts_ext i m him
              · intro i m₁ m₂ hm hact
                by_cases hnew2 : i = t ∧ m₂ = n - t
                · have hne1 : ¬ (i = t ∧ m₁ = n - t) := by omega
                  simp only [pts', if_pos hnew2, if_neg hne1]
                  rw [hnew2.1]
                  have hm1_lt : m₁ < n - t := by omega
                  exact lt_of_le_of_lt (Finset.le_sup (Finset.mem_range.mpr hm1_lt)) ha_tail
                · have hact2 : Act t i m₂ := by
                    rcases hact with h | ⟨hi, heq⟩
                    · exact Or.inl h
                    · refine Or.inr ⟨?_, heq⟩
                      by_contra hge
                      have hit : i = t := by omega
                      exact hnew2 ⟨hit, by omega⟩
                  have hne1 : ¬ (i = t ∧ m₁ = n - t) := by
                    rintro ⟨rfl, rfl⟩
                    rcases hact2 with h | ⟨h, _⟩ <;> omega
                  simp only [pts', if_neg hne1, if_neg hnew2]
                  exact hpts_mono i m₁ m₂ hm hact2
              · intro i₁ i₂ m₁ m₂ h1 h2 hne
                have hsplit : ∀ i m, Act (t + 1) i m → (i = t ∧ m = n - t) ∨ Act t i m := by
                  intro i m ha
                  rcases ha with h | ⟨hi, heq⟩
                  · exact Or.inr (Or.inl h)
                  · by_cases hit : i = t
                    · exact Or.inl ⟨hit, by omega⟩
                    · exact Or.inr (Or.inr ⟨by omega, heq⟩)
                rcases hsplit i₁ m₁ h1 with h1new | h1old <;>
                rcases hsplit i₂ m₂ h2 with h2new | h2old
                · exact (hne (h1new.1.trans h2new.1.symm)).elim
                · have h2not : ¬ (i₂ = t ∧ m₂ = n - t) := fun h => hne (h1new.1.trans h.1.symm)
                  simp only [pts', if_pos h1new, if_neg h2not]
                  rw [h1new.1, Sym2.eq_swap]
                  have hi2_lt : i₂ < n + 1 := by rcases h2old with h | ⟨_, h⟩ <;> omega
                  have hm2_lt : m₂ < n + 1 := by rcases h2old with h | ⟨_, h⟩ <;> omega
                  have hmem := Set.mem_iInter.mp (Set.mem_iInter.mp ha_red ⟨i₂, hi2_lt⟩) ⟨m₂, hm2_lt⟩
                  have hcond : Act t i₂ m₂ ∧ i₂ ≠ t := ⟨h2old, by rw [← h1new.1]; exact hne.symm⟩
                  simpa [hcond] using hmem
                · have h1not : ¬ (i₁ = t ∧ m₁ = n - t) := fun h => hne (h.1.trans h2new.1.symm)
                  simp only [pts', if_neg h1not, if_pos h2new]
                  rw [h2new.1]
                  have hi1_lt : i₁ < n + 1 := by rcases h1old with h | ⟨_, h⟩ <;> omega
                  have hm1_lt : m₁ < n + 1 := by rcases h1old with h | ⟨_, h⟩ <;> omega
                  have hmem := Set.mem_iInter.mp (Set.mem_iInter.mp ha_red ⟨i₁, hi1_lt⟩) ⟨m₁, hm1_lt⟩
                  have hcond : Act t i₁ m₁ ∧ i₁ ≠ t := ⟨h1old, by rw [← h2new.1]; exact hne⟩
                  simpa [hcond] using hmem
                · have h1not : ¬ (i₁ = t ∧ m₁ = n - t) := by
                    rintro ⟨rfl, rfl⟩; rcases h1old with h | ⟨h, _⟩ <;> omega
                  have h2not : ¬ (i₂ = t ∧ m₂ = n - t) := by
                    rintro ⟨rfl, rfl⟩; rcases h2old with h | ⟨h, _⟩ <;> omega
                  simp only [pts', if_neg h1not, if_neg h2not]
                  exact hpts_red i₁ i₂ m₁ m₂ h1old h2old hne
              · intro i j m hact hjn hij
                by_cases hnew : i = t ∧ m = n - t
                · simp only [pts', if_pos hnew]
                  rw [hnew.1]
                  have hmem := Set.mem_iInter.mp ha_G ⟨j, hjn⟩
                  have hjne : j ≠ t := by rw [← hnew.1]; exact hij.symm
                  simp only [if_pos hjne] at hmem
                  exact hmem
                · have hold : Act t i m := by
                    rcases hact with h | ⟨hi, heq⟩
                    · exact Or.inl h
                    · refine Or.inr ⟨?_, heq⟩
                      by_contra hge
                      have hit : i = t := by omega
                      exact hnew ⟨hit, by omega⟩
                  simp only [pts', if_neg hnew]
                  exact hpts_inv i j m hold hjn hij
          obtain ⟨ptsF, hptsF_ext, hptsF_mono, hptsF_red, hptsF_inv⟩ := hinner (n + 1) (le_refl _)
          have hact_full : ∀ i m, i + m < n + 1 → Act (n + 1) i m := by
            intro i m him
            by_cases h : i + m < n
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          refine ⟨⟨(rIdx', ptsF), hrIdx'_mono,
            fun i m₁ m₂ hm h2 => hptsF_mono i m₁ m₂ hm (hact_full i m₂ h2),
            fun i₁ i₂ m₁ m₂ h1 h2 hne => hptsF_red i₁ i₂ m₁ m₂ (hact_full _ _ h1) (hact_full _ _ h2) hne,
            fun i j m hm hjn hij => hptsF_inv i j m (hact_full _ _ hm) hjn hij⟩,
            fun i hi => by simp [rIdx', hi],
            hptsF_ext⟩
        let st0 : State 0 := ⟨(fun _ => 0, fun _ _ => 0),
          fun _ _ _ h => by omega, fun _ _ _ _ h => by omega,
          fun _ _ _ _ h => by omega, fun _ _ _ h => by omega⟩
        let tower : (n : ℕ) → State n :=
          Nat.rec st0 (fun n prev => Classical.choose (hstep n prev))
        have htower_r : ∀ n i, i < n → (tower (n + 1)).1.1 i = (tower n).1.1 i :=
          fun n => (Classical.choose_spec (hstep n (tower n))).1
        have htower_p : ∀ n i m, i + m < n → (tower (n + 1)).1.2 i m = (tower n).1.2 i m :=
          fun n => (Classical.choose_spec (hstep n (tower n))).2
        have htower_r_le : ∀ {n₁ n₂ : ℕ}, n₁ ≤ n₂ → ∀ i, i < n₁ →
            (tower n₂).1.1 i = (tower n₁).1.1 i := by
          intro n₁ n₂ h i hi
          induction h with
          | refl => rfl
          | @step k hk ih => rw [htower_r k i (lt_of_lt_of_le hi hk), ih]
        have htower_p_le : ∀ {n₁ n₂ : ℕ}, n₁ ≤ n₂ → ∀ i m, i + m < n₁ →
            (tower n₂).1.2 i m = (tower n₁).1.2 i m := by
          intro n₁ n₂ h i m him
          induction h with
          | refl => rfl
          | @step k hk ih => rw [htower_p k i m (lt_of_lt_of_le him hk), ih]
        let R : ℕ → ℕ := fun i => fI ((tower (i + 1)).1.1 i)
        let A : ℕ → ℕ → ℕ := fun i m => (tower (i + m + 1)).1.2 i m
        have hR_eq : ∀ {i N : ℕ}, i < N → fI ((tower N).1.1 i) = R i := by
          intro i N hi
          simp only [R]
          rw [htower_r_le (by omega : i + 1 ≤ N) i (by omega)]
        have hA_eq : ∀ {i m N : ℕ}, i + m < N → (tower N).1.2 i m = A i m := by
          intro i m N him
          simp only [A]
          rw [htower_p_le (by omega : i + m + 1 ≤ N) i m (by omega)]
        have hR_mono : StrictMono R := by
          intro i j hij
          rw [← hR_eq (by omega : i < j + 1), ← hR_eq (by omega : j < j + 1)]
          exact fI.strictMono ((tower (j + 1)).2.1 i j hij (by omega))
        have hA_mono : ∀ i, StrictMono (A i) := by
          intro i m₁ m₂ hm
          let N := i + m₂ + 1
          rw [← hA_eq (by omega : i + m₁ < N), ← hA_eq (by omega : i + m₂ < N)]
          exact (tower N).2.2.1 i m₁ m₂ hm (by omega)
        refine ⟨OrderEmbedding.ofStrictMono
          (fun p => toLex (R (ofLex p).1, A (ofLex p).1 (ofLex p).2)) ?_, ?_⟩
        · intro p q hpq
          rcases p with ⟨p1, p2⟩
          rcases q with ⟨q1, q2⟩
          rcases Prod.lex_def.mp hpq with h1 | ⟨rfl, h2⟩
          · exact Prod.Lex.left _ _ (hR_mono h1)
          · exact Prod.Lex.right _ (hA_mono p1 h2)
        · intro p q hpq
          rcases p with ⟨p1, p2⟩
          rcases q with ⟨q1, q2⟩
          change c1 s(toLex (R p1, A p1 p2), toLex (R q1, A q1 q2)) = true
          rcases Prod.lex_def.mp hpq with h1 | ⟨rfl, h2⟩
          · let N := max (p1 + p2 + 1) (q1 + q2 + 1)
            have hp : p1 + p2 < N := by omega
            have hq : q1 + q2 < N := by omega
            rw [← hR_eq (by omega : p1 < N), ← hR_eq (by omega : q1 < N),
                ← hA_eq hp, ← hA_eq hq]
            exact (tower N).2.2.2.1 p1 q1 p2 q2 hp hq (ne_of_lt h1)
          · exact hc1_row (R p1) _ _ (hA_mono p1 h2)

/-- **Specker's Positive Theorem (1957) on `Ordinal.omega0 ^ 2` (`ω^2 → (ω^2, k)^2`):**
For any well-ordered type `τ` of order type `Ordinal.omega0 ^ 2` and any `k : ℕ`, every
2-coloring of `Sym2 τ` yields either a red copy of `τ` or a blue `K_k`.
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_specker_positive_omega0_sq_k {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    (hτ : Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 ^ (2 : Ordinal))
    (k : ℕ) (c : Sym2 τ → Bool) :
    (∃ f : τ ↪o τ, ∀ x y, x < y → c s(f x, f y) = true) ∨
    (∃ g : Fin k ↪o τ, ∀ i j, i < j → c s(g i, g j) = false) := by
  have hlex : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
      Ordinal.omega0 ^ (2 : Ordinal) := by
    rw [type_lex_prod, Ordinal.type_nat_lt,
      show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast, sq]
  let e : Lex (ℕ × ℕ) ≃o τ := orderIsoOfTypeEq (hlex.trans hτ.symm)
  let c' : Sym2 (Lex (ℕ × ℕ)) → Bool := fun p => c (Sym2.map e p)
  rcases ppl035_specker_positive_lex k c' with ⟨f, hf⟩ | ⟨g, hg⟩
  · left
    refine ⟨e.symm.toOrderEmbedding.trans (f.trans e.toOrderEmbedding), ?_⟩
    intro x y hxy
    have h := hf (e.symm x) (e.symm y) (e.symm.lt_iff_lt.mpr hxy)
    simpa [c'] using h
  · right
    refine ⟨g.trans e.toOrderEmbedding, ?_⟩
    intro i j hij
    have h := hg i j hij
    simpa [c'] using h

/-- **Specker's Positive Theorem (1957): `ω^2 → (ω^2, 3)^2`.**
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_specker_positive_omega0_sq {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    (hτ : Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 ^ (2 : Ordinal))
    (c : Sym2 τ → Bool) :
    (∃ f : τ ↪o τ, ∀ x y, x < y → c s(f x, f y) = true) ∨
    (∃ g : Fin 3 ↪o τ, ∀ i j, i < j → c s(g i, g j) = false) :=
  ppl035_specker_positive_omega0_sq_k hτ 3 c

/-! ### Section 3: Specker's Negative Theorem (1957): `ω^n ↛ (ω^n, 3)^2` for all finite `n ≥ 3` -/

/-- **Pinning Pullback Principle:**
If `π : τ₁ → τ₂` sends every subset of `τ₁` order-isomorphic to `τ₁` to a set containing an
order-isomorphic copy of `τ₂`, then any counterexample coloring on `τ₂` pulls back to `τ₁`. -/
private lemma pinning_pullback {τ₁ τ₂ : Type*} [LinearOrder τ₁] [LinearOrder τ₂]
    (k : ℕ) (π : τ₁ → τ₂)
    (hpin : ∀ f : τ₁ ↪o τ₁, ∃ h : τ₂ ↪o τ₂, ∀ y, h y ∈ Set.range (π ∘ f))
    (c₂ : Sym2 τ₂ → Bool)
    (hno_red : ∀ h : τ₂ ↪o τ₂, ∃ u v, u < v ∧ c₂ s(h u, h v) = false)
    (hno_blue : ∀ g : Fin k ↪o τ₂, ∃ i j, i < j ∧ c₂ s(g i, g j) = true) :
    ∃ c₁ : Sym2 τ₁ → Bool,
      (∀ f : τ₁ ↪o τ₁, ∃ x y, x < y ∧ c₁ s(f x, f y) = false) ∧
      (∀ g : Fin k ↪o τ₁, ∃ i j, i < j ∧ c₁ s(g i, g j) = true) := by
  classical
  let c₁ : Sym2 τ₁ → Bool := Sym2.lift ⟨fun x y => if π x = π y then true else c₂ s(π x, π y),
    by
      intro x y
      by_cases h : π x = π y
      · simp [h]
      · have h' : π y ≠ π x := Ne.symm h
        simp [h, h', Sym2.eq_swap]⟩
  refine ⟨c₁, ?_, ?_⟩
  · intro f
    obtain ⟨h, hh⟩ := hpin f
    obtain ⟨u, v, huv, hblue⟩ := hno_red h
    obtain ⟨x, hx⟩ := hh u
    obtain ⟨y, hy⟩ := hh v
    dsimp only [Function.comp] at hx hy
    have hne : π (f x) ≠ π (f y) := by
      rw [hx, hy]; exact ne_of_lt (h.strictMono huv)
    have hxy_ne : x ≠ y := fun hxy => hne (by rw [hxy])
    rcases lt_or_gt_of_ne hxy_ne with hlt | hgt
    · refine ⟨x, y, hlt, ?_⟩
      simp only [c₁, Sym2.lift_mk, if_neg hne]
      rw [hx, hy]
      exact hblue
    · refine ⟨y, x, hgt, ?_⟩
      simp only [c₁, Sym2.lift_mk, if_neg (Ne.symm hne)]
      rw [Sym2.eq_swap, hx, hy]
      exact hblue
  · intro g
    by_contra hall
    push Not at hall
    have hall' : ∀ i j : Fin k, i < j → c₁ s(g i, g j) = false :=
      fun i j hij => Bool.eq_false_iff.mpr (hall i j hij)
    have hinj : Function.Injective (fun i : Fin k => π (g i)) := by
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := hall' i j hlt
        simp [c₁, hij] at h
      · have h := hall' j i hgt
        simp [c₁, hij.symm] at h
    let pts : Finset τ₂ := Finset.univ.image (fun i : Fin k => π (g i))
    have hcard : pts.card = k := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    let iso := pts.orderIsoOfFin hcard
    obtain ⟨i, j, hij, hred⟩ := hno_blue (iso.toOrderEmbedding.trans (OrderEmbedding.subtype _))
    obtain ⟨i', _, hi'⟩ := Finset.mem_image.mp (iso i).2
    obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp (iso j).2
    have hne' : π (g i') ≠ π (g j') := by
      rw [hi', hj']; exact ne_of_lt (iso.strictMono hij)
    have hne_idx : i' ≠ j' := fun h => hne' (by rw [h])
    rcases lt_or_gt_of_ne hne_idx with hlt | hgt
    · have h := hall' i' j' hlt
      simp only [c₁, Sym2.lift_mk, if_neg hne'] at h
      rw [hi', hj'] at h
      exact absurd (h.symm.trans hred) (by decide)
    · have h := hall' j' i' hgt
      simp only [c₁, Sym2.lift_mk, if_neg (Ne.symm hne')] at h
      rw [Sym2.eq_swap, hi', hj'] at h
      exact absurd (h.symm.trans hred) (by decide)

/-- Helper: Slice-threshold lemma for `ω^γ * ω`: any subset of `Lex (ℕ × τ)` of order type
`ω^γ * ω` (where `type τ = ω^γ`) has infinitely many slices of order type `ω^γ`. -/
private lemma inf_full_slices_of_mul_omega0 {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    {γ : Ordinal.{0}} (hτ : Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 ^ γ)
    (S : Set (Lex (ℕ × τ)))
    (hS : Ordinal.omega0 ^ γ * Ordinal.omega0 ≤ Ordinal.type ((· < ·) : ↑S → ↑S → Prop)) :
    {k : ℕ | Ordinal.omega0 ^ γ ≤
      Ordinal.type ((· < ·) : ↑{x : τ | toLex (k, x) ∈ S} → _ → Prop)}.Infinite := by
  classical
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  let S_lt : Set (Lex (ℕ × τ)) := {p ∈ S | (ofLex p).1 ≤ N}
  let S_ge : Set (Lex (ℕ × τ)) := {p ∈ S | N < (ofLex p).1}
  have hSplit : Ordinal.type ((· < ·) : ↑S → ↑S → Prop) ≤
      Ordinal.type ((· < ·) : ↑S_lt → ↑S_lt → Prop) +
      Ordinal.type ((· < ·) : ↑S_ge → ↑S_ge → Prop) := by
    rw [← Ordinal.type_sum_lex]
    refine Ordinal.type_le_iff'.mpr ⟨?_⟩
    refine ⟨⟨fun p => if h : (ofLex p.1).1 ≤ N then Sum.inl ⟨p.1, p.2, h⟩
      else Sum.inr ⟨p.1, p.2, lt_of_not_ge h⟩, ?_⟩, ?_⟩
    · intro p q heq
      by_cases hp : (ofLex p.1).1 ≤ N <;> by_cases hq : (ofLex q.1).1 ≤ N <;>
        simp [hp, hq] at heq
      · exact Subtype.ext heq
      · exact Subtype.ext heq
    · intro p q
      change Sum.Lex ((· < ·) : ↑S_lt → _ → Prop) ((· < ·) : ↑S_ge → _ → Prop)
        (if h : (ofLex p.1).1 ≤ N then Sum.inl ⟨p.1, p.2, h⟩ else Sum.inr ⟨p.1, p.2, lt_of_not_ge h⟩)
        (if h : (ofLex q.1).1 ≤ N then Sum.inl ⟨q.1, q.2, h⟩ else Sum.inr ⟨q.1, q.2, lt_of_not_ge h⟩) ↔
        p < q
      split_ifs with hp hq
      · exact Sum.lex_inl_inl
      · constructor
        · intro _
          exact Prod.Lex.left _ _ (lt_of_le_of_lt hp (lt_of_not_ge hq))
        · intro _
          exact Sum.Lex.sep _ _
      · constructor
        · intro h; cases h
        · intro hlt
          have hlt' : (ofLex p.1).1 < (ofLex q.1).1 ∨
              (ofLex p.1).1 = (ofLex q.1).1 ∧ (ofLex p.1).2 < (ofLex q.1).2 := Prod.lex_def.mp hlt
          rcases hlt' with h1 | ⟨h1, _⟩ <;> omega
      · exact Sum.lex_inr_inr
  have hlt_bound : Ordinal.type ((· < ·) : ↑S_lt → ↑S_lt → Prop) ≤
      Ordinal.omega0 ^ γ * ((N + 1 : ℕ) : Ordinal) := by
    have hprod : Ordinal.type ((· < ·) : Lex (Fin (N + 1) × τ) → _ → Prop) =
        Ordinal.omega0 ^ γ * ((N + 1 : ℕ) : Ordinal) := by
      rw [type_lex_prod, hτ, Ordinal.type_fin]
    rw [← hprod]
    refine Ordinal.type_le_iff'.mpr ⟨?_⟩
    refine ⟨⟨fun p => toLex (⟨(ofLex p.1).1, by have := p.2.2; omega⟩, (ofLex p.1).2), ?_⟩, ?_⟩
    · intro p q heq
      rcases Prod.mk.inj heq with ⟨h1, h2⟩
      exact Subtype.ext (Prod.ext (congrArg Fin.val h1) h2)
    · intro p q
      show Prod.Lex (· < ·) (· < ·) ((⟨(ofLex p.1).1, by have := p.2.2; omega⟩ : Fin (N + 1)), (ofLex p.1).2)
          ((⟨(ofLex q.1).1, by have := q.2.2; omega⟩ : Fin (N + 1)), (ofLex q.1).2) ↔
        Prod.Lex (· < ·) (· < ·) (ofLex p.1) (ofLex q.1)
      simp only [Prod.lex_def, Fin.mk_lt_mk, Fin.mk.injEq]
  have hge_bound : Ordinal.type ((· < ·) : ↑S_ge → ↑S_ge → Prop) ≤ Ordinal.omega0 ^ γ := by
    have hprinc : Ordinal.IsPrincipal (· + ·) (Ordinal.omega0 ^ γ) :=
      Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mpr (Or.inr ⟨γ, rfl⟩)
    have hfin_seg : ∀ m : ℕ,
        Ordinal.type ((· < ·) : ↑{p ∈ S_ge | (ofLex p).1 ≤ N + m} → _ → Prop) <
        Ordinal.omega0 ^ γ := by
      intro m
      induction m with
      | zero =>
        have : IsEmpty ↑{p ∈ S_ge | (ofLex p).1 ≤ N + 0} := ⟨fun p => by
          have h1 := p.2.1.2; have h2 := p.2.2; omega⟩
        rw [Ordinal.type_eq_zero_of_empty]
        exact Ordinal.opow_pos γ Ordinal.omega0_pos
      | succ m ihm =>
        let A : Set (Lex (ℕ × τ)) := {p ∈ S_ge | (ofLex p).1 ≤ N + m}
        let B : Set (Lex (ℕ × τ)) := {p ∈ S_ge | (ofLex p).1 = N + m + 1}
        have hsum : Ordinal.type ((· < ·) : ↑{p ∈ S_ge | (ofLex p).1 ≤ N + (m + 1)} → _ → Prop) ≤
            Ordinal.type ((· < ·) : ↑A → ↑A → Prop) +
            Ordinal.type ((· < ·) : ↑B → ↑B → Prop) := by
          rw [← Ordinal.type_sum_lex]
          refine Ordinal.type_le_iff'.mpr ⟨?_⟩
          refine ⟨⟨fun p => if h : (ofLex p.1).1 ≤ N + m then Sum.inl ⟨p.1, p.2.1, h⟩
            else Sum.inr ⟨p.1, p.2.1, by have := p.2.2; omega⟩, ?_⟩, ?_⟩
          · intro p q heq
            by_cases hp : (ofLex p.1).1 ≤ N + m <;> by_cases hq : (ofLex q.1).1 ≤ N + m <;>
              simp [hp, hq] at heq
            · exact Subtype.ext heq
            · exact Subtype.ext heq
          · intro p q
            change Sum.Lex ((· < ·) : ↑A → _ → Prop) ((· < ·) : ↑B → _ → Prop)
              (if h : (ofLex p.1).1 ≤ N + m then Sum.inl ⟨p.1, p.2.1, h⟩
                else Sum.inr ⟨p.1, p.2.1, by have := p.2.2; omega⟩)
              (if h : (ofLex q.1).1 ≤ N + m then Sum.inl ⟨q.1, q.2.1, h⟩
                else Sum.inr ⟨q.1, q.2.1, by have := q.2.2; omega⟩) ↔
              p < q
            split_ifs with hp hq
            · exact Sum.lex_inl_inl
            · constructor
              · intro _
                exact Prod.Lex.left _ _ (lt_of_le_of_lt hp (lt_of_not_ge hq))
              · intro _; exact Sum.Lex.sep _ _
            · constructor
              · intro h; cases h
              · intro hlt
                have hlt' : (ofLex p.1).1 < (ofLex q.1).1 ∨
                    (ofLex p.1).1 = (ofLex q.1).1 ∧ (ofLex p.1).2 < (ofLex q.1).2 := Prod.lex_def.mp hlt
                rcases hlt' with h1 | ⟨h1, _⟩ <;> omega
            · exact Sum.lex_inr_inr
        have hBlt : Ordinal.type ((· < ·) : ↑B → ↑B → Prop) < Ordinal.omega0 ^ γ := by
          have hnot : ¬ Ordinal.omega0 ^ γ ≤
              Ordinal.type ((· < ·) : ↑{x : τ | toLex (N + m + 1, x) ∈ S} → _ → Prop) := by
            intro hle
            have := hN hle
            omega
          have hB_le : Ordinal.type ((· < ·) : ↑B → ↑B → Prop) ≤
              Ordinal.type ((· < ·) : ↑{x : τ | toLex (N + m + 1, x) ∈ S} → _ → Prop) := by
            refine Ordinal.type_le_iff'.mpr ⟨?_⟩
            refine ⟨⟨fun p => ⟨(ofLex p.1).2, by
              have h1 : (ofLex p.1).1 = N + m + 1 := p.2.2
              have h2 : p.1 ∈ S := p.2.1.1
              simpa [← h1] using h2⟩, ?_⟩, ?_⟩
            · intro p q heq
              have h2 : (ofLex p.1).2 = (ofLex q.1).2 := congrArg Subtype.val heq
              exact Subtype.ext (Prod.ext (p.2.2.trans q.2.2.symm) h2)
            · intro p q
              show (ofLex p.1).2 < (ofLex q.1).2 ↔ Prod.Lex (· < ·) (· < ·) (ofLex p.1) (ofLex q.1)
              rw [Prod.lex_def, p.2.2, q.2.2]
              simp
          exact lt_of_le_of_lt hB_le (lt_of_not_ge hnot)
        exact lt_of_le_of_lt hsum (hprinc ihm hBlt)
    by_contra hgt
    push Not at hgt
    let p0 : ↑S_ge := Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop) ⟨Ordinal.omega0 ^ γ, hgt⟩
    let m := (ofLex p0.1).1 - N
    have hseg_le : Ordinal.omega0 ^ γ ≤
        Ordinal.type ((· < ·) : ↑{p ∈ S_ge | (ofLex p).1 ≤ N + m} → _ → Prop) := by
      rw [← Ordinal.type_toType (Ordinal.omega0 ^ γ)]
      refine Ordinal.type_le_iff'.mpr ⟨?_⟩
      let g : (Ordinal.omega0 ^ γ).ToType → ↑S_ge := fun a =>
        Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop)
          ⟨Ordinal.typein ((· < ·) : (Ordinal.omega0 ^ γ).ToType → _ → Prop) a,
            lt_trans (by rw [← Ordinal.type_toType (Ordinal.omega0 ^ γ)]; exact Ordinal.typein_lt_type _ a) hgt⟩
      have hg_lt_p0 : ∀ a, g a < p0 := by
        intro a
        change (Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop) _) <
          (Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop) _)
        rw [(Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop)).map_rel_iff]
        have h1 := Ordinal.typein_lt_type ((· < ·) : (Ordinal.omega0 ^ γ).ToType → _ → Prop) a
        rw [Ordinal.type_toType] at h1
        exact h1
      have hg_rel : ∀ a b, g a < g b ↔ a < b := by
        intro a b
        change (Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop) _) <
          (Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop) _) ↔ a < b
        rw [(Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop)).map_rel_iff]
        exact Ordinal.typein_lt_typein _
      refine ⟨⟨fun a => ⟨(g a).1, (g a).2, by
        have hlt : (g a).1 < p0.1 := hg_lt_p0 a
        have h1 : (ofLex (g a).1).1 ≤ (ofLex p0.1).1 := by
          rcases Prod.lex_def.mp hlt with h | ⟨h, _⟩
          · exact le_of_lt h
          · exact le_of_eq h
        have h2 : N < (ofLex p0.1).1 := p0.2.2
        omega⟩, ?_⟩, ?_⟩
      · intro a b hab
        dsimp only at hab
        have hval : g a = g b := Subtype.ext (Subtype.mk.inj hab)
        rcases lt_trichotomy a b with h | rfl | h
        · exact (ne_of_lt ((hg_rel a b).mpr h) hval).elim
        · rfl
        · exact (ne_of_gt ((hg_rel b a).mpr h) hval).elim
      · intro a b
        exact hg_rel a b
    exact not_lt_of_ge hseg_le (hfin_seg m)
  have htot : Ordinal.omega0 ^ γ * Ordinal.omega0 ≤
      Ordinal.omega0 ^ γ * ((N + 1 : ℕ) : Ordinal) + Ordinal.omega0 ^ γ :=
    le_trans hS (le_trans hSplit (add_le_add hlt_bound hge_bound))
  have hrhs : Ordinal.omega0 ^ γ * ((N + 1 : ℕ) : Ordinal) + Ordinal.omega0 ^ γ <
      Ordinal.omega0 ^ γ * Ordinal.omega0 := by
    have heq : Ordinal.omega0 ^ γ * ((N + 1 : ℕ) : Ordinal) + Ordinal.omega0 ^ γ =
        Ordinal.omega0 ^ γ * ((N + 2 : ℕ) : Ordinal) := by
      rw [show ((N + 2 : ℕ) : Ordinal) = ((N + 1 : ℕ) : Ordinal) + 1 by
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, add_assoc]; norm_num,
        mul_add, mul_one]
    rw [heq]
    exact mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 (N + 2))
      (Ordinal.opow_pos γ Ordinal.omega0_pos)
  exact not_lt_of_ge htot hrhs

/-- **Specker's Negative Theorem on `ω^3` (`ω^3 ↛ (ω^3, 3)^2`):**
Explicit triangle-free coloring on `Lex (ℕ × Lex (ℕ × ℕ))` with no red copy of `ω^3`. -/
private lemma specker_negative_omega0_cube_lex :
    ∃ c : Sym2 (Lex (ℕ × Lex (ℕ × ℕ))) → Bool,
      (∀ f : Lex (ℕ × Lex (ℕ × ℕ)) ↪o Lex (ℕ × Lex (ℕ × ℕ)),
        ∃ x y, x < y ∧ c s(f x, f y) = false) ∧
      (∀ g : Fin 3 ↪o Lex (ℕ × Lex (ℕ × ℕ)),
        ∃ i j, i < j ∧ c s(g i, g j) = true) := by
  classical
  let A : Lex (ℕ × Lex (ℕ × ℕ)) → ℕ := fun p => (ofLex p).1
  let B : Lex (ℕ × Lex (ℕ × ℕ)) → ℕ := fun p => (ofLex p).1 + 1 + (ofLex (ofLex p).2).1
  let C : Lex (ℕ × Lex (ℕ × ℕ)) → ℕ :=
    fun p => (ofLex p).1 + (ofLex (ofLex p).2).1 + (ofLex (ofLex p).2).2 + 2
  have hABC : ∀ p, A p < B p ∧ B p < C p := fun p => by dsimp [A, B, C]; omega
  let blueDir : Lex (ℕ × Lex (ℕ × ℕ)) → Lex (ℕ × Lex (ℕ × ℕ)) → Prop :=
    fun x y => B x < A y ∧ A y < C x ∧ C x < B y
  let col : Sym2 (Lex (ℕ × Lex (ℕ × ℕ))) → Bool :=
    Sym2.lift ⟨fun x y => decide (¬ (blueDir x y ∨ blueDir y x)),
      by intro x y; simp [or_comm]⟩
  refine ⟨col, ?_, ?_⟩
  · intro f
    let S : Set (Lex (ℕ × Lex (ℕ × ℕ))) := Set.range f
    have htype2 : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
        Ordinal.omega0 ^ (2 : Ordinal) := by
      rw [type_lex_prod, Ordinal.type_nat_lt,
        show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast, sq]
    have hS : Ordinal.omega0 ^ (2 : Ordinal) * Ordinal.omega0 ≤
        Ordinal.type ((· < ·) : ↑S → ↑S → Prop) := by
      have htype3 : Ordinal.type ((· < ·) : Lex (ℕ × Lex (ℕ × ℕ)) → _ → Prop) =
          Ordinal.omega0 ^ (2 : Ordinal) * Ordinal.omega0 := by
        rw [type_lex_prod, htype2, Ordinal.type_nat_lt]
      rw [← htype3]
      refine Ordinal.type_le_iff'.mpr ⟨?_⟩
      refine ⟨⟨fun p => ⟨f p, p, rfl⟩, fun p q h => f.injective (congrArg Subtype.val h)⟩, ?_⟩
      intro p q
      exact f.lt_iff_lt
    have hinfA := inf_full_slices_of_mul_omega0 htype2 S hS
    obtain ⟨a₁, ha₁⟩ := hinfA.nonempty
    have hSa1 : Ordinal.omega0 ^ (1 : Ordinal) * Ordinal.omega0 ≤
        Ordinal.type ((· < ·) : ↑{q : Lex (ℕ × ℕ) | toLex (a₁, q) ∈ S} → _ → Prop) := by
      have h2eq : Ordinal.omega0 ^ (2 : Ordinal) = Ordinal.omega0 ^ (1 : Ordinal) * Ordinal.omega0 := by
        rw [opow_one, show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast, sq]
      rw [← h2eq]
      exact ha₁
    have htype1 : Ordinal.type ((· < ·) : ℕ → ℕ → Prop) = Ordinal.omega0 ^ (1 : Ordinal) := by
      rw [opow_one]; exact Ordinal.type_nat_lt
    have hinfJ1 := inf_full_slices_of_mul_omega0 htype1 _ hSa1
    obtain ⟨j₁, hj₁⟩ := hinfJ1.nonempty
    let b₁ := a₁ + 1 + j₁
    obtain ⟨a₂, ha₂, ha₂_gt⟩ := hinfA.exists_gt b₁
    have hK1inf : {k : ℕ | toLex (a₁, toLex (j₁, k)) ∈ S}.Infinite := by
      by_contra hfin
      rw [Set.not_infinite] at hfin
      obtain ⟨M, hM⟩ := hfin.bddAbove
      have hleM : Ordinal.type ((· < ·) : ↑{k : ℕ | toLex (a₁, toLex (j₁, k)) ∈ S} → _ → Prop) ≤
          Ordinal.type ((· < ·) : Fin (M + 1) → Fin (M + 1) → Prop) := by
        refine Ordinal.type_le_iff'.mpr ⟨?_⟩
        refine ⟨⟨fun k => ⟨k.1, by have := hM k.2; omega⟩, ?_⟩, ?_⟩
        · intro a b h; exact Subtype.ext (congrArg Fin.val h)
        · intro a b; exact Iff.rfl
      rw [Ordinal.type_fin] at hleM
      have hlt : Ordinal.type ((· < ·) : ↑{k : ℕ | toLex (a₁, toLex (j₁, k)) ∈ S} → _ → Prop) <
          Ordinal.omega0 := lt_of_le_of_lt hleM (Ordinal.natCast_lt_omega0 (M + 1))
      change Ordinal.omega0 ^ (1 : Ordinal) ≤ _ at hj₁
      rw [opow_one] at hj₁
      exact not_lt_of_ge hj₁ hlt
    obtain ⟨k₁, hk₁, hk₁_gt⟩ := hK1inf.exists_gt a₂
    have hSa2 : Ordinal.omega0 ^ (1 : Ordinal) * Ordinal.omega0 ≤
        Ordinal.type ((· < ·) : ↑{q : Lex (ℕ × ℕ) | toLex (a₂, q) ∈ S} → _ → Prop) := by
      have h2eq : Ordinal.omega0 ^ (2 : Ordinal) = Ordinal.omega0 ^ (1 : Ordinal) * Ordinal.omega0 := by
        rw [opow_one, show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast, sq]
      rw [← h2eq]
      exact ha₂
    have hinfJ2 := inf_full_slices_of_mul_omega0 htype1 _ hSa2
    let c₁ := a₁ + j₁ + k₁ + 2
    obtain ⟨j₂, hj₂, hj₂_gt⟩ := hinfJ2.exists_gt c₁
    have hK2ne : {k : ℕ | toLex (a₂, toLex (j₂, k)) ∈ S}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hsub_emp : IsEmpty ↑{x : ℕ | toLex (j₂, x) ∈ {q : Lex (ℕ × ℕ) | toLex (a₂, q) ∈ S}} := by
        refine ⟨fun x => ?_⟩
        have hx : x.1 ∈ ({k : ℕ | toLex (a₂, toLex (j₂, k)) ∈ S} : Set ℕ) := x.2
        rw [hemp] at hx
        exact hx
      change Ordinal.omega0 ^ (1 : Ordinal) ≤ _ at hj₂
      rw [@Ordinal.type_eq_zero_of_empty _ _ _ hsub_emp, opow_one] at hj₂
      exact not_le_of_gt Ordinal.omega0_pos hj₂
    obtain ⟨k₂, hk₂⟩ := hK2ne
    obtain ⟨x, hx⟩ := hk₁
    obtain ⟨y, hy⟩ := hk₂
    have hlt_xy : f x < f y := by
      rw [hx, hy]
      exact Prod.Lex.left _ _ (by dsimp [b₁] at ha₂_gt; omega)
    refine ⟨x, y, f.lt_iff_lt.mp hlt_xy, ?_⟩
    simp only [col, Sym2.lift_mk, decide_eq_false_iff_not, not_not]
    left
    rw [hx, hy]
    refine ⟨?_, ?_, ?_⟩ <;> dsimp [A, B, C, b₁, c₁] at * <;> omega
  · intro g
    by_contra hall
    push Not at hall
    have hblue_pair : ∀ i j : Fin 3, i < j → blueDir (g i) (g j) ∨ blueDir (g j) (g i) := by
      intro i j hij
      have h := Bool.eq_false_iff.mpr (hall i j hij)
      simp only [col, Sym2.lift_mk, decide_eq_false_iff_not, not_not] at h
      exact h
    have h01 := hblue_pair 0 1 (by decide)
    have h12 := hblue_pair 1 2 (by decide)
    have h02 := hblue_pair 0 2 (by decide)
    have hA_le : ∀ {p q}, p < q → A p ≤ A q := by
      intro p q hpq
      rcases Prod.lex_def.mp hpq with h | ⟨h, _⟩
      · exact le_of_lt h
      · exact le_of_eq h
    have hA01 : A (g 0) ≤ A (g 1) := hA_le (g.strictMono (by decide))
    have hA12 : A (g 1) ≤ A (g 2) := hA_le (g.strictMono (by decide))
    have hA02 : A (g 0) ≤ A (g 2) := hA_le (g.strictMono (by decide))
    have hdir : ∀ {p q}, A p ≤ A q → (blueDir p q ∨ blueDir q p) → blueDir p q := by
      intro p q hle h
      rcases h with h1 | h2
      · exact h1
      · exfalso
        have hq := (hABC q).1
        have hp := h2.1
        omega
    have d01 := hdir hA01 h01
    have d12 := hdir hA12 h12
    have d02 := hdir hA02 h02
    have : C (g 0) < B (g 1) := d01.2.2
    have : B (g 1) < A (g 2) := d12.1
    have : A (g 2) < C (g 0) := d02.2.1
    omega

/-- **Specker's Negative Theorem (1957): `ω^n ↛ (ω^n, 3)^2` for all finite `n ≥ 3`.**
For every `n ≥ 3` and every well-ordered type `τ` of order type `Ordinal.omega0 ^ (n : Ordinal)`,
there exists a 2-coloring of `Sym2 τ` with NO red copy of `τ` and NO blue `K_3`.
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_specker_negative_finite {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    (n : ℕ) (hn : 3 ≤ n)
    (hτ : Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 ^ (n : Ordinal)) :
    ∃ c : Sym2 τ → Bool,
      (∀ f : τ ↪o τ, ∃ x y, x < y ∧ c s(f x, f y) = false) ∧
      (∀ g : Fin 3 ↪o τ, ∃ i j, i < j ∧ c s(g i, g j) = true) := by
  let W3 := Lex (ℕ × Lex (ℕ × ℕ))
  let Wrem : Type := (Ordinal.omega0 ^ ((n - 3 : ℕ) : Ordinal)).ToType
  have hW3 : Ordinal.type ((· < ·) : W3 → W3 → Prop) = Ordinal.omega0 ^ (3 : Ordinal) := by
    have h2 : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
        Ordinal.omega0 * Ordinal.omega0 := by
      rw [type_lex_prod, Ordinal.type_nat_lt]
    rw [show Ordinal.type ((· < ·) : W3 → W3 → Prop) =
        Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) *
        Ordinal.type ((· < ·) : ℕ → ℕ → Prop) from type_lex_prod,
      h2, Ordinal.type_nat_lt,
      show (3 : Ordinal) = ((3 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast,
      pow_succ, pow_succ, pow_one]
  have hprod : Ordinal.type ((· < ·) : Lex (W3 × Wrem) → Lex (W3 × Wrem) → Prop) =
      Ordinal.omega0 ^ (n : Ordinal) := by
    rw [type_lex_prod, Ordinal.type_toType, hW3, ← Ordinal.opow_add]
    congr 1
    rw [show (3 : Ordinal) = ((3 : ℕ) : Ordinal) by norm_num, ← Nat.cast_add]
    congr 1
    omega
  let e : τ ≃o Lex (W3 × Wrem) := orderIsoOfTypeEq (hτ.trans hprod.symm)
  let π : τ → W3 := fun x => (ofLex (e x)).1
  have hpin : ∀ f : τ ↪o τ, ∃ h : W3 ↪o W3, ∀ y, h y ∈ Set.range (π ∘ f) := by
    intro f
    let Y : Set W3 := Set.range (π ∘ f)
    have hYge : Ordinal.omega0 ^ (3 : Ordinal) ≤ Ordinal.type ((· < ·) : ↑Y → ↑Y → Prop) := by
      by_contra hlt
      push Not at hlt
      have hle : Ordinal.type ((· < ·) : τ → τ → Prop) ≤
          Ordinal.type ((· < ·) : Lex (↑Y × Wrem) → _ → Prop) := by
        refine Ordinal.type_le_iff'.mpr ⟨?_⟩
        refine ⟨⟨fun x => toLex (⟨π (f x), x, rfl⟩, (ofLex (e (f x))).2), ?_⟩, ?_⟩
        · intro x₁ x₂ heq
          rcases Prod.mk.inj heq with ⟨h1, h2⟩
          have h1' : (ofLex (e (f x₁))).1 = (ofLex (e (f x₂))).1 := congrArg Subtype.val h1
          exact f.injective (e.injective (Prod.ext h1' h2))
        · intro x₁ x₂
          have he : Prod.Lex (· < ·) (· < ·) (ofLex (e (f x₁))) (ofLex (e (f x₂))) ↔ x₁ < x₂ := by
            change e (f x₁) < e (f x₂) ↔ x₁ < x₂
            rw [e.lt_iff_lt, f.lt_iff_lt]
          rw [← he]
          show Prod.Lex (· < ·) (· < ·) ((⟨π (f x₁), ⟨x₁, rfl⟩⟩ : ↑Y), (ofLex (e (f x₁))).2)
              ((⟨π (f x₂), ⟨x₂, rfl⟩⟩ : ↑Y), (ofLex (e (f x₂))).2) ↔
            Prod.Lex (· < ·) (· < ·) (ofLex (e (f x₁))) (ofLex (e (f x₂)))
          simp only [Prod.lex_def]
          have hltY : (⟨π (f x₁), ⟨x₁, rfl⟩⟩ : ↑Y) < ⟨π (f x₂), ⟨x₂, rfl⟩⟩ ↔
              (ofLex (e (f x₁))).1 < (ofLex (e (f x₂))).1 := Iff.rfl
          have heqY : (⟨π (f x₁), ⟨x₁, rfl⟩⟩ : ↑Y) = ⟨π (f x₂), ⟨x₂, rfl⟩⟩ ↔
              (ofLex (e (f x₁))).1 = (ofLex (e (f x₂))).1 :=
            iff_of_eq (Subtype.mk.injEq _ _ _ _)
          rw [hltY, heqY]
      rw [type_lex_prod, Ordinal.type_toType, hτ] at hle
      have hstrict : Ordinal.omega0 ^ ((n - 3 : ℕ) : Ordinal) *
          Ordinal.type ((· < ·) : ↑Y → ↑Y → Prop) <
          Ordinal.omega0 ^ ((n - 3 : ℕ) : Ordinal) * Ordinal.omega0 ^ (3 : Ordinal) :=
        mul_lt_mul_of_pos_left hlt (Ordinal.opow_pos _ Ordinal.omega0_pos)
      rw [← Ordinal.opow_add] at hstrict
      have hadd : ((n - 3 : ℕ) : Ordinal) + (3 : Ordinal) = (n : Ordinal) := by
        rw [show (3 : Ordinal) = ((3 : ℕ) : Ordinal) by norm_num, ← Nat.cast_add]
        congr 1; omega
      rw [hadd] at hstrict
      exact not_lt_of_ge hle hstrict
    rw [← hW3] at hYge
    obtain ⟨emb⟩ := Ordinal.type_le_iff'.mp hYge
    refine ⟨OrderEmbedding.ofStrictMono (fun y => (emb y).1)
      (fun a b hab => emb.map_rel_iff.mpr hab), fun y => (emb y).2⟩
  obtain ⟨c3, hno_red, hno_blue⟩ := specker_negative_omega0_cube_lex
  exact pinning_pullback 3 π hpin c3 hno_red hno_blue

/-! ### Section 4: Galvin–Larson Necessary Condition (1974) -/

private lemma countable_toType_of_card_le {α : Ordinal.{0}} (h : α.card ≤ Cardinal.aleph0) :
    Countable α.ToType := by
  rw [← Cardinal.mk_le_aleph0_iff]
  have h1 : Cardinal.mk α.ToType = α.card := by
    rw [← Ordinal.card_type ((· < ·) : α.ToType → α.ToType → Prop), Ordinal.type_toType]
  rw [h1]
  exact h

private lemma infinite_of_omega0_le_type {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    {S : Set τ} (h : Ordinal.omega0 ≤ Ordinal.type ((· < ·) : ↑S → ↑S → Prop)) :
    S.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have : Finite ↑S := hfin.to_subtype
  have hcard_lt : Cardinal.mk ↑S < Cardinal.aleph0 := Cardinal.lt_aleph0_of_finite ↑S
  have hcard_le : Cardinal.aleph0 ≤ Cardinal.mk ↑S := by
    rw [← Ordinal.card_omega0, ← Ordinal.card_type ((· < ·) : ↑S → ↑S → Prop)]
    exact Ordinal.card_le_card h
  exact not_lt_of_ge hcard_le hcard_lt

private lemma opow_omega0_strictMono : StrictMono (fun β : Ordinal.{0} => Ordinal.omega0 ^ β) :=
  (Ordinal.isNormal_opow (a := Ordinal.omega0) (by norm_num)).strictMono

/-- Any additively decomposable ordinal `α = α₁ + α₂` (`α₁, α₂ < α`) fails `α → (α, 3)^2`. -/
private lemma decomposable_neg_partition {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    {α₁ α₂ : Ordinal.{0}}
    (hsum : Ordinal.type ((· < ·) : τ → τ → Prop) = α₁ + α₂)
    (h1 : α₁ < Ordinal.type ((· < ·) : τ → τ → Prop))
    (h2 : α₂ < Ordinal.type ((· < ·) : τ → τ → Prop)) :
    ∃ c : Sym2 τ → Bool,
      (∀ f : τ ↪o τ, ∃ x y, x < y ∧ c s(f x, f y) = false) ∧
      (∀ g : Fin 3 ↪o τ, ∃ i j, i < j ∧ c s(g i, g j) = true) := by
  classical
  have hts : Ordinal.type ((· < ·) : τ → τ → Prop) =
      Ordinal.type (Sum.Lex ((· < ·) : α₁.ToType → α₁.ToType → Prop)
        ((· < ·) : α₂.ToType → α₂.ToType → Prop)) := by
    rw [Ordinal.type_sum_lex, Ordinal.type_toType, Ordinal.type_toType, hsum]
  let e : ((· < ·) : τ → τ → Prop) ≃r
      Sum.Lex ((· < ·) : α₁.ToType → α₁.ToType → Prop)
        ((· < ·) : α₂.ToType → α₂.ToType → Prop) :=
    Classical.choice (Ordinal.type_eq.mp hts)
  let side : τ → Bool := fun x => match e x with
    | Sum.inl _ => true
    | Sum.inr _ => false
  let c : Sym2 τ → Bool := Sym2.lift ⟨fun x y => decide (side x = side y),
    by intro x y; simp [eq_comm]⟩
  refine ⟨c, ?_, ?_⟩
  · intro f
    by_contra hred
    push Not at hred
    have hred' : ∀ x y : τ, x < y → side (f x) = side (f y) := by
      intro x y hxy
      have h := Bool.eq_true_of_not_eq_false (hred x y hxy)
      simpa [c] using h
    have hconst : ∀ x y : τ, side (f x) = side (f y) := by
      intro x y
      rcases lt_trichotomy x y with h | rfl | h
      · exact hred' x y h
      · rfl
      · exact (hred' y x h).symm
    have hne : Nonempty τ := by
      by_contra hemp
      have : IsEmpty τ := not_nonempty_iff.mp hemp
      rw [Ordinal.type_eq_zero_of_empty] at h1
      exact not_lt_of_ge zero_le h1
    obtain ⟨x0⟩ := hne
    cases hs : side (f x0) with
    | true =>
      have hall : ∀ x, ∃ a : α₁.ToType, e (f x) = Sum.inl a := by
        intro x
        have hx : side (f x) = true := (hconst x x0).trans hs
        cases he : e (f x) with
        | inl a => exact ⟨a, rfl⟩
        | inr b => simp [side, he] at hx
      let φ : τ → α₁.ToType := fun x => Classical.choose (hall x)
      have hφ : ∀ x, e (f x) = Sum.inl (φ x) := fun x => Classical.choose_spec (hall x)
      have hle : Ordinal.type ((· < ·) : τ → τ → Prop) ≤ α₁ := by
        rw [← Ordinal.type_toType α₁]
        refine Ordinal.type_le_iff'.mpr ⟨?_⟩
        refine ⟨⟨φ, ?_⟩, ?_⟩
        · intro x y hxy
          have : e (f x) = e (f y) := by rw [hφ x, hφ y, hxy]
          exact f.injective (e.injective this)
        · intro x y
          have hrel : Sum.Lex ((· < ·) : α₁.ToType → _ → Prop) ((· < ·) : α₂.ToType → _ → Prop)
              (e (f x)) (e (f y)) ↔ x < y := by
            rw [e.map_rel_iff, f.lt_iff_lt]
          rw [hφ x, hφ y, Sum.lex_inl_inl] at hrel
          exact hrel
      exact not_lt_of_ge hle h1
    | false =>
      have hall : ∀ x, ∃ b : α₂.ToType, e (f x) = Sum.inr b := by
        intro x
        have hx : side (f x) = false := (hconst x x0).trans hs
        cases he : e (f x) with
        | inl a => simp [side, he] at hx
        | inr b => exact ⟨b, rfl⟩
      let φ : τ → α₂.ToType := fun x => Classical.choose (hall x)
      have hφ : ∀ x, e (f x) = Sum.inr (φ x) := fun x => Classical.choose_spec (hall x)
      have hle : Ordinal.type ((· < ·) : τ → τ → Prop) ≤ α₂ := by
        rw [← Ordinal.type_toType α₂]
        refine Ordinal.type_le_iff'.mpr ⟨?_⟩
        refine ⟨⟨φ, ?_⟩, ?_⟩
        · intro x y hxy
          have : e (f x) = e (f y) := by rw [hφ x, hφ y, hxy]
          exact f.injective (e.injective this)
        · intro x y
          have hrel : Sum.Lex ((· < ·) : α₁.ToType → _ → Prop) ((· < ·) : α₂.ToType → _ → Prop)
              (e (f x)) (e (f y)) ↔ x < y := by
            rw [e.map_rel_iff, f.lt_iff_lt]
          rw [hφ x, hφ y, Sum.lex_inr_inr] at hrel
          exact hrel
      exact not_lt_of_ge hle h2
  · intro g
    cases h0 : side (g 0) <;> cases h1 : side (g 1) <;> cases h2 : side (g 2)
    · exact ⟨0, 1, by decide, by simp [c, h0, h1]⟩
    · exact ⟨0, 1, by decide, by simp [c, h0, h1]⟩
    · exact ⟨0, 2, by decide, by simp [c, h0, h2]⟩
    · exact ⟨1, 2, by decide, by simp [c, h1, h2]⟩
    · exact ⟨1, 2, by decide, by simp [c, h1, h2]⟩
    · exact ⟨0, 2, by decide, by simp [c, h0, h2]⟩
    · exact ⟨0, 1, by decide, by simp [c, h0, h1]⟩
    · exact ⟨0, 1, by decide, by simp [c, h0, h1]⟩

/-- **Galvin–Larson Pinning to `ω^2`:**
For every countable ordinal `η ≥ 2` (`(ω^η).card ≤ ℵ₀`), there exists a pinning map
`p : (ω^η).ToType → Lex (ℕ × ℕ)` sending every subset of order type `ω^η` to a set of order
type at least `ω^2`. -/
private lemma pinning_opow_to_omega0_sq (η : Ordinal.{0}) :
    2 ≤ η → (Ordinal.omega0 ^ η).card ≤ Cardinal.aleph0 →
    ∃ p : (Ordinal.omega0 ^ η).ToType → Lex (ℕ × ℕ),
      ∀ S : Set (Ordinal.omega0 ^ η).ToType,
        Ordinal.omega0 ^ η ≤ Ordinal.type ((· < ·) : ↑S → ↑S → Prop) →
        Ordinal.omega0 ^ (2 : Ordinal) ≤ Ordinal.type ((· < ·) : ↑(p '' S) → ↑(p '' S) → Prop) := by
  classical
  refine Ordinal.limitRecOn (motive := fun η =>
    2 ≤ η → (Ordinal.omega0 ^ η).card ≤ Cardinal.aleph0 →
    ∃ p : (Ordinal.omega0 ^ η).ToType → Lex (ℕ × ℕ),
      ∀ S : Set (Ordinal.omega0 ^ η).ToType,
        Ordinal.omega0 ^ η ≤ Ordinal.type ((· < ·) : ↑S → ↑S → Prop) →
        Ordinal.omega0 ^ (2 : Ordinal) ≤ Ordinal.type ((· < ·) : ↑(p '' S) → ↑(p '' S) → Prop))
    η ?_ ?_ ?_
  · intro h2 _
    exfalso
    exact not_le_of_gt (by norm_num : (0 : Ordinal) < 2) h2
  · intro η' _ h2 hcount
    have hη'1 : 1 ≤ η' := by
      by_contra hlt
      push Not at hlt
      have h0 : η' = 0 := by
        have hlt1 : η' < ((1 : ℕ) : Ordinal) := by simpa using hlt
        obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (lt_trans hlt1 (Ordinal.natCast_lt_omega0 1))
        have hn : n < 1 := Nat.cast_lt.mp hlt1
        have : n = 0 := by omega
        subst this; simp
      rw [h0, zero_add] at h2
      exact not_le_of_gt (by norm_num : (1 : Ordinal) < 2) h2
    have hprod : Ordinal.type ((· < ·) : Lex (ℕ × (Ordinal.omega0 ^ η').ToType) → _ → Prop) =
        Ordinal.omega0 ^ (η' + 1) := by
      rw [type_lex_prod, Ordinal.type_toType, Ordinal.type_nat_lt, Ordinal.opow_add, opow_one]
    let e : (Ordinal.omega0 ^ (η' + 1)).ToType ≃o Lex (ℕ × (Ordinal.omega0 ^ η').ToType) :=
      orderIsoOfTypeEq ((Ordinal.type_toType _).trans hprod.symm)
    have hcard' : (Ordinal.omega0 ^ η').card ≤ Cardinal.aleph0 :=
      le_trans (Ordinal.card_le_card (Ordinal.opow_le_opow_right Ordinal.omega0_pos
        le_self_add)) hcount
    have : Countable (Ordinal.omega0 ^ η').ToType := countable_toType_of_card_le hcard'
    obtain ⟨b, hbinj⟩ := exists_injective_nat (Ordinal.omega0 ^ η').ToType
    let p : (Ordinal.omega0 ^ (η' + 1)).ToType → Lex (ℕ × ℕ) :=
      fun x => toLex ((ofLex (e x)).1, b (ofLex (e x)).2)
    refine ⟨p, fun S hS => ?_⟩
    let S' : Set (Lex (ℕ × (Ordinal.omega0 ^ η').ToType)) := e '' S
    have hS' : Ordinal.omega0 ^ η' * Ordinal.omega0 ≤ Ordinal.type ((· < ·) : ↑S' → ↑S' → Prop) := by
      have heq_pow : Ordinal.omega0 ^ η' * Ordinal.omega0 = Ordinal.omega0 ^ (η' + 1) := by
        rw [Ordinal.opow_add, opow_one]
      rw [heq_pow]
      refine le_trans hS (Ordinal.type_le_iff'.mpr ⟨?_⟩)
      refine ⟨⟨fun x => ⟨e x.1, x.1, x.2, rfl⟩,
        fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h))⟩, ?_⟩
      intro a b
      exact e.lt_iff_lt
    have hinfK := inf_full_slices_of_mul_omega0 (Ordinal.type_toType (Ordinal.omega0 ^ η')) S' hS'
    have hrows : {r : ℕ | {a : ℕ | toLex (r, a) ∈ p '' S}.Infinite}.Infinite := by
      refine hinfK.mono ?_
      intro k hk
      have hk_om : Ordinal.omega0 ≤
          Ordinal.type ((· < ·) : ↑{x : (Ordinal.omega0 ^ η').ToType | toLex (k, x) ∈ S'} → _ → Prop) :=
        le_trans (le_trans (le_of_eq (opow_one Ordinal.omega0).symm)
          (Ordinal.opow_le_opow_right Ordinal.omega0_pos hη'1)) hk
      have hkinf : {x : (Ordinal.omega0 ^ η').ToType | toLex (k, x) ∈ S'}.Infinite :=
        infinite_of_omega0_le_type hk_om
      have hbimg : (b '' {x : (Ordinal.omega0 ^ η').ToType | toLex (k, x) ∈ S'}).Infinite :=
        hkinf.image hbinj.injOn
      refine hbimg.mono ?_
      rintro a ⟨y, hy, rfl⟩
      rcases hy with ⟨z, hzS, hz_eq⟩
      refine ⟨z, hzS, ?_⟩
      show toLex ((ofLex (e z)).1, b (ofLex (e z)).2) = toLex (k, b y)
      rw [hz_eq, ofLex_toLex]
    obtain ⟨emb, hemb⟩ := exists_lex_emb_of_inf_rows (p '' S) hrows
    have hlex2 : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
        Ordinal.omega0 ^ (2 : Ordinal) := by
      rw [type_lex_prod, Ordinal.type_nat_lt,
        show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast, sq]
    rw [← hlex2]
    refine Ordinal.type_le_iff'.mpr ⟨?_⟩
    refine ⟨⟨fun q => ⟨emb q, hemb q⟩, fun a b h => emb.injective (congrArg Subtype.val h)⟩, ?_⟩
    intro a b
    exact emb.lt_iff_lt
  · intro l hl _ h2 hcount
    have hl_le : l ≤ Ordinal.omega0 ^ l :=
      Ordinal.right_le_opow l (by norm_num : (1 : Ordinal) < Ordinal.omega0)
    have : Countable l.ToType :=
      countable_toType_of_card_le (le_trans (Ordinal.card_le_card hl_le) hcount)
    have hl_pos : 0 < l := lt_of_lt_of_le (by norm_num : (0 : Ordinal) < 2) h2
    have hne_l : Nonempty l.ToType := by
      by_contra hemp
      have : IsEmpty l.ToType := not_nonempty_iff.mp hemp
      have h0 : l = 0 := by rw [← Ordinal.type_toType l, Ordinal.type_eq_zero_of_empty]
      exact ne_of_gt hl_pos h0
    obtain ⟨surj, hsurj⟩ := exists_surjective_nat l.ToType
    -- Build a strictly increasing cofinal sequence `seq : ℕ → Ordinal.{0}` in `l` with `1 ≤ seq 0`.
    let ti : l.ToType → Ordinal.{0} := Ordinal.typein ((· < ·) : l.ToType → l.ToType → Prop)
    have hti_lt : ∀ y : l.ToType, ti y < l := fun y => by
      have h := Ordinal.typein_lt_type ((· < ·) : l.ToType → l.ToType → Prop) y
      rwa [Ordinal.type_toType] at h
    let seq : ℕ → Ordinal.{0} := Nat.rec
      (max 1 (ti (surj 0)))
      (fun n prev => max prev (ti (surj (n + 1))) + 1)
    have hseq_lt : ∀ n, seq n < l := by
      intro n
      induction n with
      | zero =>
        exact max_lt (lt_of_lt_of_le (by norm_num : (1 : Ordinal) < 2) h2) (hti_lt (surj 0))
      | succ n ihn =>
        have hmax : max (seq n) (ti (surj (n + 1))) < l := max_lt ihn (hti_lt (surj (n + 1)))
        rw [← Order.succ_eq_add_one]
        exact hl.succ_lt hmax
    have hseq_mono : StrictMono seq := strictMono_nat_of_lt_succ (fun n => by
      have hle : seq n ≤ max (seq n) (ti (surj (n + 1))) := le_max_left _ _
      exact lt_of_le_of_lt hle (Order.lt_succ_of_le (le_refl _)))
    have hseq_ge1 : ∀ n, 1 ≤ seq n := fun n =>
      le_trans (le_max_left 1 (ti (surj 0))) (hseq_mono.monotone (Nat.zero_le n))
    have hseq_cof : ∀ ξ < l, ∃ n, ξ < seq n := by
      intro ξ hξ
      have hξ' : ξ < Ordinal.type ((· < ·) : l.ToType → l.ToType → Prop) := by
        rw [Ordinal.type_toType]; exact hξ
      let y : l.ToType := Ordinal.enum ((· < ·) : l.ToType → l.ToType → Prop) ⟨ξ, hξ'⟩
      obtain ⟨n, hn⟩ := hsurj y
      have hti_y : ti y = ξ := Ordinal.typein_enum _ _
      refine ⟨n + 1, ?_⟩
      cases n with
      | zero =>
        have hle : ξ ≤ seq 0 := by rw [← hti_y, ← hn]; exact le_max_right _ _
        exact lt_of_le_of_lt hle (hseq_mono (by omega : 0 < 1))
      | succ m =>
        have hle : ξ ≤ max (seq m) (ti (surj (m + 1))) := by
          rw [← hti_y, ← hn]; exact le_max_right _ _
        have hlt : ξ < seq (m + 1) := lt_of_le_of_lt hle (Order.lt_succ_of_le (le_refl _))
        exact lt_trans hlt (hseq_mono (by omega : m + 1 < m + 2))
    -- Every `x : (ω^l).ToType` has `typein x < ω^(seq n)` for some `n`.
    let tix : (Ordinal.omega0 ^ l).ToType → Ordinal.{0} :=
      Ordinal.typein ((· < ·) : (Ordinal.omega0 ^ l).ToType → _ → Prop)
    have htix_ex : ∀ x : (Ordinal.omega0 ^ l).ToType, ∃ n : ℕ, tix x < Ordinal.omega0 ^ seq n := by
      intro x
      have hxlt : tix x < Ordinal.omega0 ^ l := by
        have h := Ordinal.typein_lt_type ((· < ·) : (Ordinal.omega0 ^ l).ToType → _ → Prop) x
        rwa [Ordinal.type_toType] at h
      have hsup : Ordinal.omega0 ^ l = ⨆ γ : Set.Iio l, Ordinal.omega0 ^ (γ : Ordinal) :=
        (Ordinal.isNormal_opow (a := Ordinal.omega0) (by norm_num)).apply_of_isSuccLimit hl
      rw [hsup] at hxlt
      obtain ⟨⟨ξ, hξ⟩, hltξ⟩ := Ordinal.lt_iSup_iff.mp hxlt
      obtain ⟨n, hn⟩ := hseq_cof ξ hξ
      exact ⟨n, lt_trans hltξ (opow_omega0_strictMono hn)⟩
    let lvl : (Ordinal.omega0 ^ l).ToType → ℕ := fun x => Nat.find (htix_ex x)
    have hlvl_lt : ∀ x, tix x < Ordinal.omega0 ^ seq (lvl x) := fun x => Nat.find_spec (htix_ex x)
    have hlvl_min : ∀ x n, n < lvl x → Ordinal.omega0 ^ seq n ≤ tix x := fun x n hn =>
      le_of_not_gt (Nat.find_min (htix_ex x) hn)
    have : Countable (Ordinal.omega0 ^ l).ToType := countable_toType_of_card_le hcount
    obtain ⟨b, hbinj⟩ := exists_injective_nat (Ordinal.omega0 ^ l).ToType
    let p : (Ordinal.omega0 ^ l).ToType → Lex (ℕ × ℕ) := fun x => toLex (lvl x, b x)
    refine ⟨p, fun S hS => ?_⟩
    -- Prove infinitely many levels `n` have `{x ∈ S | lvl x = n}` infinite!
    have hinfL : {n : ℕ | {x ∈ S | lvl x = n}.Infinite}.Infinite := by
      by_contra hfin
      rw [Set.not_infinite] at hfin
      obtain ⟨N, hN⟩ := hfin.bddAbove
      let S_lt : Set (Ordinal.omega0 ^ l).ToType := {x ∈ S | lvl x ≤ N}
      let S_ge : Set (Ordinal.omega0 ^ l).ToType := {x ∈ S | N < lvl x}
      have hSplit : Ordinal.type ((· < ·) : ↑S → ↑S → Prop) ≤
          Ordinal.type ((· < ·) : ↑S_lt → ↑S_lt → Prop) +
          Ordinal.type ((· < ·) : ↑S_ge → ↑S_ge → Prop) := by
        rw [← Ordinal.type_sum_lex]
        refine Ordinal.type_le_iff'.mpr ⟨?_⟩
        refine ⟨⟨fun x => if h : lvl x.1 ≤ N then Sum.inl ⟨x.1, x.2, h⟩
          else Sum.inr ⟨x.1, x.2, lt_of_not_ge h⟩, ?_⟩, ?_⟩
        · intro x y heq
          by_cases hx : lvl x.1 ≤ N <;> by_cases hy : lvl y.1 ≤ N <;> simp [hx, hy] at heq
          · exact Subtype.ext heq
          · exact Subtype.ext heq
        · intro x y
          change Sum.Lex ((· < ·) : ↑S_lt → _ → Prop) ((· < ·) : ↑S_ge → _ → Prop)
            (if h : lvl x.1 ≤ N then Sum.inl ⟨x.1, x.2, h⟩ else Sum.inr ⟨x.1, x.2, lt_of_not_ge h⟩)
            (if h : lvl y.1 ≤ N then Sum.inl ⟨y.1, y.2, h⟩ else Sum.inr ⟨y.1, y.2, lt_of_not_ge h⟩) ↔
            x < y
          split_ifs with hx hy hy
          · exact Sum.lex_inl_inl
          · constructor
            · intro _
              change x.1 < y.1
              have h1 : tix x.1 < Ordinal.omega0 ^ seq N :=
                lt_of_lt_of_le (hlvl_lt x.1)
                  (Ordinal.opow_le_opow_right Ordinal.omega0_pos (hseq_mono.monotone hx))
              have h2 : Ordinal.omega0 ^ seq N ≤ tix y.1 := hlvl_min y.1 N (lt_of_not_ge hy)
              exact (Ordinal.typein_lt_typein ((· < ·) : (Ordinal.omega0 ^ l).ToType → _ → Prop)).mp
                (lt_of_lt_of_le h1 h2)
            · intro _; exact Sum.Lex.sep _ _
          · constructor
            · intro h; cases h
            · intro hlt
              have h1 : tix y.1 < Ordinal.omega0 ^ seq N :=
                lt_of_lt_of_le (hlvl_lt y.1)
                  (Ordinal.opow_le_opow_right Ordinal.omega0_pos (hseq_mono.monotone hy))
              have h2 : Ordinal.omega0 ^ seq N ≤ tix x.1 := hlvl_min x.1 N (lt_of_not_ge hx)
              exact (not_lt_of_ge (le_trans (le_of_lt h1) h2)
                ((Ordinal.typein_lt_typein ((· < ·) : (Ordinal.omega0 ^ l).ToType → _ → Prop)).mpr hlt)).elim
          · exact Sum.lex_inr_inr
      have hlt_bd : Ordinal.type ((· < ·) : ↑S_lt → ↑S_lt → Prop) ≤ Ordinal.omega0 ^ seq N := by
        rw [← Ordinal.type_toType (Ordinal.omega0 ^ seq N)]
        refine Ordinal.type_le_iff'.mpr ⟨?_⟩
        let φ : ↑S_lt → (Ordinal.omega0 ^ seq N).ToType := fun x =>
          Ordinal.enum ((· < ·) : (Ordinal.omega0 ^ seq N).ToType → _ → Prop)
            ⟨tix x.1, by
              rw [Ordinal.type_toType]
              exact lt_of_lt_of_le (hlvl_lt x.1)
                (Ordinal.opow_le_opow_right Ordinal.omega0_pos (hseq_mono.monotone x.2.2))⟩
        refine ⟨⟨φ, ?_⟩, ?_⟩
        · intro x y hxy
          have h1 := congrArg (fun z => Ordinal.typein ((· < ·) : (Ordinal.omega0 ^ seq N).ToType → _ → Prop) z) hxy
          have hx_eq : Ordinal.typein ((· < ·) : (Ordinal.omega0 ^ seq N).ToType → _ → Prop) (φ x) = tix x.1 :=
            Ordinal.typein_enum _ _
          have hy_eq : Ordinal.typein ((· < ·) : (Ordinal.omega0 ^ seq N).ToType → _ → Prop) (φ y) = tix y.1 :=
            Ordinal.typein_enum _ _
          rw [hx_eq, hy_eq] at h1
          exact Subtype.ext ((Ordinal.typein_inj ((· < ·) : (Ordinal.omega0 ^ l).ToType → _ → Prop)).mp h1)
        · intro x y
          change φ x < φ y ↔ x < y
          have hrel : φ x < φ y ↔ tix x.1 < tix y.1 :=
            (Ordinal.enum ((· < ·) : (Ordinal.omega0 ^ seq N).ToType → _ → Prop)).map_rel_iff
          rw [hrel]
          exact Ordinal.typein_lt_typein ((· < ·) : (Ordinal.omega0 ^ l).ToType → _ → Prop)
      have hge_bd : Ordinal.type ((· < ·) : ↑S_ge → ↑S_ge → Prop) ≤ Ordinal.omega0 := by
        by_contra hgt
        push Not at hgt
        let y0 : ↑S_ge := Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop) ⟨Ordinal.omega0, hgt⟩
        let K := lvl y0.1
        have hfin_below : {x : ↑S_ge | x < y0}.Finite := by
          let U : Set (Ordinal.omega0 ^ l).ToType :=
            ⋃ n ∈ Finset.Icc (N + 1) K, {z ∈ S | lvl z = n}
          have hUfin : U.Finite := by
            refine (Finset.Icc (N + 1) K).finite_toSet.biUnion (fun n hn => ?_)
            by_contra hinf
            have hleN : n ≤ N := hN hinf
            have hgtN : N + 1 ≤ n := (Finset.mem_Icc.mp hn).1
            omega
          have hsub : Subtype.val '' {x : ↑S_ge | x < y0} ⊆ U := by
            rintro _ ⟨x, hxlt, rfl⟩
            have hleK : lvl x.1 ≤ K := by
              by_contra hgtK
              push Not at hgtK
              have h1 : Ordinal.omega0 ^ seq K ≤ tix x.1 := hlvl_min x.1 K hgtK
              have h2 : tix y0.1 < Ordinal.omega0 ^ seq K := hlvl_lt y0.1
              have h3 : tix x.1 < tix y0.1 := (Ordinal.typein_lt_typein _).mpr hxlt
              exact not_lt_of_ge h1 (lt_trans h3 h2)
            exact Set.mem_biUnion (Finset.mem_Icc.mpr ⟨by have := x.2.2; omega, hleK⟩) ⟨x.2.1, rfl⟩
          exact (hUfin.subset hsub).of_finite_image Subtype.val_injective.injOn
        -- Yet `n ↦ Ordinal.enum (<) ⟨n, ...⟩` injects `ℕ` into `{x : ↑S_ge | x < y0}`!
        let inj : ℕ → ↑S_ge := fun n =>
          Ordinal.enum ((· < ·) : ↑S_ge → ↑S_ge → Prop)
            ⟨(n : Ordinal), lt_trans (Ordinal.natCast_lt_omega0 n) hgt⟩
        have hinj_inj : Function.Injective inj := by
          intro a b hab
          have h1 := congrArg (Ordinal.typein ((· < ·) : ↑S_ge → ↑S_ge → Prop)) hab
          dsimp only [inj] at h1
          rw [Ordinal.typein_enum, Ordinal.typein_enum] at h1
          exact Nat.cast_injective h1
        have hinj_mem : ∀ n, inj n ∈ {x : ↑S_ge | x < y0} := by
          intro n
          show inj n < y0
          simp only [inj, y0, (Ordinal.enum _).map_rel_iff]
          exact Ordinal.natCast_lt_omega0 n
        exact Set.infinite_of_injective_forall_mem hinj_inj hinj_mem hfin_below
      have htot : Ordinal.omega0 ^ l ≤ Ordinal.omega0 ^ seq N + Ordinal.omega0 :=
        le_trans hS (le_trans hSplit (add_le_add hlt_bd hge_bd))
      have hrhs : Ordinal.omega0 ^ seq N + Ordinal.omega0 < Ordinal.omega0 ^ l := by
        have hprinc : Ordinal.IsPrincipal (· + ·) (Ordinal.omega0 ^ (seq N + 1)) :=
          Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mpr (Or.inr ⟨seq N + 1, rfl⟩)
        have h1 : Ordinal.omega0 ^ seq N < Ordinal.omega0 ^ (seq N + 1) :=
          opow_omega0_strictMono (Order.lt_succ_of_le (le_refl _))
        have h2 : Ordinal.omega0 < Ordinal.omega0 ^ (seq N + 1) :=
          lt_of_eq_of_lt (opow_one Ordinal.omega0).symm
            (opow_omega0_strictMono (lt_of_le_of_lt (hseq_ge1 N) (Order.lt_succ_of_le (le_refl _))))
        have hsum_lt : Ordinal.omega0 ^ seq N + Ordinal.omega0 < Ordinal.omega0 ^ (seq N + 1) :=
          hprinc h1 h2
        have hsucc_lt : seq N + 1 < l := by
          rw [← Order.succ_eq_add_one]
          exact hl.succ_lt (hseq_lt N)
        exact lt_trans hsum_lt (opow_omega0_strictMono hsucc_lt)
      exact not_lt_of_ge htot hrhs
    have hrows : {r : ℕ | {a : ℕ | toLex (r, a) ∈ p '' S}.Infinite}.Infinite := by
      refine hinfL.mono ?_
      intro n hn
      have hbimg : (b '' {x ∈ S | lvl x = n}).Infinite := hn.image hbinj.injOn
      refine hbimg.mono ?_
      rintro a ⟨x, ⟨hxS, hxlvl⟩, rfl⟩
      exact ⟨x, hxS, by simp [p, hxlvl]⟩
    obtain ⟨emb, hemb⟩ := exists_lex_emb_of_inf_rows (p '' S) hrows
    have hlex2 : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
        Ordinal.omega0 ^ (2 : Ordinal) := by
      rw [type_lex_prod, Ordinal.type_nat_lt,
        show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast, sq]
    rw [← hlex2]
    refine Ordinal.type_le_iff'.mpr ⟨?_⟩
    refine ⟨⟨fun q => ⟨emb q, hemb q⟩, fun a b h => emb.injective (congrArg Subtype.val h)⟩, ?_⟩
    intro a b
    exact emb.lt_iff_lt

/-- **Galvin–Larson Pinning to `ω^3` for Countable Decomposable Exponents `β ≥ 3`:**
If `β = γ + δ` with `2 ≤ γ`, `1 ≤ δ`, `δ ≤ γ`, and `(ω^β).card ≤ ℵ₀`, then `ω^β` admits a
pinning map onto `W3 = Lex (ℕ × Lex (ℕ × ℕ))` (order type `ω^3`). -/
private lemma pinning_opow_add_to_omega0_cube {γ δ : Ordinal.{0}}
    (hγ2 : 2 ≤ γ) (hδ1 : 1 ≤ δ) (hδγ : δ ≤ γ)
    (hcount : (Ordinal.omega0 ^ (γ + δ)).card ≤ Cardinal.aleph0) :
    ∃ π : (Ordinal.omega0 ^ (γ + δ)).ToType → Lex (ℕ × Lex (ℕ × ℕ)),
      ∀ f : (Ordinal.omega0 ^ (γ + δ)).ToType ↪o (Ordinal.omega0 ^ (γ + δ)).ToType,
        ∃ h : Lex (ℕ × Lex (ℕ × ℕ)) ↪o Lex (ℕ × Lex (ℕ × ℕ)),
          ∀ y, h y ∈ Set.range (π ∘ f) := by
  classical
  let W3 := Lex (ℕ × Lex (ℕ × ℕ))
  have hW3 : Ordinal.type ((· < ·) : W3 → W3 → Prop) = Ordinal.omega0 ^ (3 : Ordinal) := by
    have h2 : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
        Ordinal.omega0 * Ordinal.omega0 := by
      rw [type_lex_prod, Ordinal.type_nat_lt]
    rw [show Ordinal.type ((· < ·) : W3 → W3 → Prop) =
        Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) *
        Ordinal.type ((· < ·) : ℕ → ℕ → Prop) from type_lex_prod,
      h2, Ordinal.type_nat_lt,
      show (3 : Ordinal) = ((3 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast,
      pow_succ, pow_succ, pow_one]
  by_cases hδ_one : δ = 1
  · -- Case 1: `δ = 1`, `ω^(γ + 1) = ω^γ * ω`, lift `p : ω^γ → ω^2` to `(k, x) ↦ (k, p x)`.
    subst hδ_one
    have hγcount : (Ordinal.omega0 ^ γ).card ≤ Cardinal.aleph0 :=
      le_trans (Ordinal.card_le_card (Ordinal.opow_le_opow_right Ordinal.omega0_pos
        le_self_add)) hcount
    obtain ⟨p, hp⟩ := pinning_opow_to_omega0_sq γ hγ2 hγcount
    have hprod : Ordinal.type ((· < ·) : Lex (ℕ × (Ordinal.omega0 ^ γ).ToType) → _ → Prop) =
        Ordinal.omega0 ^ (γ + 1) := by
      rw [type_lex_prod, Ordinal.type_toType, Ordinal.type_nat_lt, Ordinal.opow_add, opow_one]
    let e : (Ordinal.omega0 ^ (γ + 1)).ToType ≃o Lex (ℕ × (Ordinal.omega0 ^ γ).ToType) :=
      orderIsoOfTypeEq ((Ordinal.type_toType _).trans hprod.symm)
    let π : (Ordinal.omega0 ^ (γ + 1)).ToType → W3 :=
      fun x => toLex ((ofLex (e x)).1, p (ofLex (e x)).2)
    refine ⟨π, fun f => ?_⟩
    let S' : Set (Lex (ℕ × (Ordinal.omega0 ^ γ).ToType)) := Set.range (e ∘ f)
    have hS' : Ordinal.omega0 ^ γ * Ordinal.omega0 ≤ Ordinal.type ((· < ·) : ↑S' → ↑S' → Prop) := by
      have heq_pow : Ordinal.omega0 ^ γ * Ordinal.omega0 = Ordinal.omega0 ^ (γ + 1) := by
        rw [Ordinal.opow_add, opow_one]
      rw [heq_pow, ← Ordinal.type_toType (Ordinal.omega0 ^ (γ + 1))]
      refine Ordinal.type_le_iff'.mpr ⟨?_⟩
      refine ⟨⟨fun x => ⟨e (f x), x, rfl⟩,
        fun a b h => f.injective (e.injective (congrArg Subtype.val h))⟩, ?_⟩
      intro a b
      show e (f a) < e (f b) ↔ a < b
      rw [e.lt_iff_lt, f.lt_iff_lt]
    have hinfK := inf_full_slices_of_mul_omega0 (Ordinal.type_toType (Ordinal.omega0 ^ γ)) S' hS'
    obtain ⟨idx, hidx⟩ := exists_strictMono_of_infinite_nat hinfK
    have hlex2 : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
        Ordinal.omega0 ^ (2 : Ordinal) := by
      rw [type_lex_prod, Ordinal.type_nat_lt,
        show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast, sq]
    have hslice_emb : ∀ k : ℕ, ∃ φ : Lex (ℕ × ℕ) ↪o Lex (ℕ × ℕ),
        ∀ q, toLex (idx k, φ q) ∈ Set.range (π ∘ f) := by
      intro k
      let Sl : Set (Ordinal.omega0 ^ γ).ToType := {x | toLex (idx k, x) ∈ S'}
      have hSl : Ordinal.omega0 ^ γ ≤ Ordinal.type ((· < ·) : ↑Sl → ↑Sl → Prop) := hidx k
      have hpSl := hp Sl hSl
      rw [← hlex2] at hpSl
      obtain ⟨emb⟩ := Ordinal.type_le_iff'.mp hpSl
      refine ⟨OrderEmbedding.ofStrictMono (fun q => (emb q).1)
        (fun a b hab => emb.map_rel_iff.mpr hab), fun q => ?_⟩
      rcases (emb q).2 with ⟨y, hySl, hy_eq⟩
      rcases hySl with ⟨z, hz_eq⟩
      dsimp only [Function.comp] at hz_eq
      refine ⟨z, ?_⟩
      show toLex ((ofLex (e (f z))).1, p (ofLex (e (f z))).2) = toLex (idx k, (emb q).1)
      rw [hz_eq, ofLex_toLex, hy_eq]
    let φ : ℕ → (Lex (ℕ × ℕ) ↪o Lex (ℕ × ℕ)) := fun k => Classical.choose (hslice_emb k)
    have hφ : ∀ k q, toLex (idx k, φ k q) ∈ Set.range (π ∘ f) :=
      fun k => Classical.choose_spec (hslice_emb k)
    refine ⟨OrderEmbedding.ofStrictMono
      (fun u => toLex (idx (ofLex u).1, φ (ofLex u).1 (ofLex u).2)) ?_, ?_⟩
    · intro u v huv
      rcases u with ⟨u1, u2⟩
      rcases v with ⟨v1, v2⟩
      rcases Prod.lex_def.mp huv with h1 | ⟨rfl, h2⟩
      · exact Prod.Lex.left _ _ (idx.strictMono h1)
      · exact Prod.Lex.right _ ((φ u1).strictMono h2)
    · intro u
      exact hφ (ofLex u).1 (ofLex u).2
  · -- Case 2: `2 ≤ δ ≤ γ`, combine `b : ω^γ ↪ ℕ` and `q : ω^δ → ω^2` into `Lex (Lex (ℕ × ℕ) × ℕ) ≃o W3`.
    have hδ2 : 2 ≤ δ := by
      by_contra hlt
      push Not at hlt
      have hlt2 : δ < ((2 : ℕ) : Ordinal) := by simpa using hlt
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (lt_trans hlt2 (Ordinal.natCast_lt_omega0 2))
      have hn : n < 2 := Nat.cast_lt.mp hlt2
      have h1 : 1 ≤ n := by
        have h1' : ((1 : ℕ) : Ordinal.{0}) ≤ (n : Ordinal.{0}) := by simpa using hδ1
        exact Nat.cast_le.mp h1'
      have hn1 : n = 1 := by omega
      exact hδ_one (by simp [hn1])
    have hγcount : (Ordinal.omega0 ^ γ).card ≤ Cardinal.aleph0 :=
      le_trans (Ordinal.card_le_card (Ordinal.opow_le_opow_right Ordinal.omega0_pos
        le_self_add)) hcount
    have hδcount : (Ordinal.omega0 ^ δ).card ≤ Cardinal.aleph0 :=
      le_trans (Ordinal.card_le_card (Ordinal.opow_le_opow_right Ordinal.omega0_pos
        le_add_self)) hcount
    have : Countable (Ordinal.omega0 ^ γ).ToType := countable_toType_of_card_le hγcount
    obtain ⟨b, hbinj⟩ := exists_injective_nat (Ordinal.omega0 ^ γ).ToType
    obtain ⟨q, hq⟩ := pinning_opow_to_omega0_sq δ hδ2 hδcount
    -- Model `ω^(γ + δ) = ω^γ * ω^δ` via `Lex ((ω^δ).ToType × (ω^γ).ToType)`,
    -- and target `W3' = Lex (Lex (ℕ × ℕ) × ℕ)` (order type `ω * ω^2 = ω^3`).
    let W3' := Lex (Lex (ℕ × ℕ) × ℕ)
    have hW3' : Ordinal.type ((· < ·) : W3' → W3' → Prop) = Ordinal.omega0 ^ (3 : Ordinal) := by
      have h2 : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
          Ordinal.omega0 * Ordinal.omega0 := by
        rw [type_lex_prod, Ordinal.type_nat_lt]
      rw [show Ordinal.type ((· < ·) : W3' → W3' → Prop) =
          Ordinal.type ((· < ·) : ℕ → ℕ → Prop) *
          Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) from type_lex_prod,
        h2, Ordinal.type_nat_lt,
        show (3 : Ordinal) = ((3 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast,
        pow_succ, pow_succ, pow_one, mul_assoc]
    let isoW : W3' ≃o W3 := orderIsoOfTypeEq (hW3'.trans hW3.symm)
    have hprod : Ordinal.type ((· < ·) : Lex ((Ordinal.omega0 ^ δ).ToType × (Ordinal.omega0 ^ γ).ToType) → _ → Prop) =
        Ordinal.omega0 ^ (γ + δ) := by
      rw [type_lex_prod, Ordinal.type_toType, Ordinal.type_toType, Ordinal.opow_add]
    let e : (Ordinal.omega0 ^ (γ + δ)).ToType ≃o
        Lex ((Ordinal.omega0 ^ δ).ToType × (Ordinal.omega0 ^ γ).ToType) :=
      orderIsoOfTypeEq ((Ordinal.type_toType _).trans hprod.symm)
    let π' : (Ordinal.omega0 ^ (γ + δ)).ToType → W3' :=
      fun x => toLex (q (ofLex (e x)).1, b (ofLex (e x)).2)
    let π : (Ordinal.omega0 ^ (γ + δ)).ToType → W3 := fun x => isoW (π' x)
    refine ⟨π, fun f => ?_⟩
    let S' : Set (Lex ((Ordinal.omega0 ^ δ).ToType × (Ordinal.omega0 ^ γ).ToType)) :=
      Set.range (e ∘ f)
    have hS' : Ordinal.omega0 ^ (γ + δ) ≤ Ordinal.type ((· < ·) : ↑S' → ↑S' → Prop) := by
      rw [← Ordinal.type_toType (Ordinal.omega0 ^ (γ + δ))]
      refine Ordinal.type_le_iff'.mpr ⟨?_⟩
      refine ⟨⟨fun x => ⟨e (f x), x, rfl⟩,
        fun a b h => f.injective (e.injective (congrArg Subtype.val h))⟩, ?_⟩
      intro a b
      show e (f a) < e (f b) ↔ a < b
      rw [e.lt_iff_lt, f.lt_iff_lt]
    let Y_inf : Set (Ordinal.omega0 ^ δ).ToType :=
      {y | {x : (Ordinal.omega0 ^ γ).ToType | toLex (y, x) ∈ S'}.Infinite}
    let S_inf : Set (Lex ((Ordinal.omega0 ^ δ).ToType × (Ordinal.omega0 ^ γ).ToType)) :=
      {p ∈ S' | (ofLex p).1 ∈ Y_inf}
    let S_fin : Set (Lex ((Ordinal.omega0 ^ δ).ToType × (Ordinal.omega0 ^ γ).ToType)) :=
      {p ∈ S' | (ofLex p).1 ∉ Y_inf}
    have hSunion : S_inf ∪ S_fin = S' := by
      ext p; constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hy : (ofLex p).1 ∈ Y_inf
        · exact Or.inl ⟨h, hy⟩
        · exact Or.inr ⟨h, hy⟩
    -- Bound `type S_fin ≤ ω * ω^δ = ω^(1 + δ) < ω^(γ + δ)`!
    have hfin_lt : Ordinal.type ((· < ·) : ↑S_fin → ↑S_fin → Prop) < Ordinal.omega0 ^ (γ + δ) := by
      -- For every `y ∉ Y_inf`, the fiber `{x | (y, x) ∈ S'}` is finite, hence embeds order-preservingly into `ℕ`!
      have hfib_emb : ∀ y : (Ordinal.omega0 ^ δ).ToType, y ∉ Y_inf →
          ∃ φ : ↑{x : (Ordinal.omega0 ^ γ).ToType | toLex (y, x) ∈ S'} → ℕ,
            ∀ a b, φ a < φ b ↔ a < b := by
        intro y hy
        have hfin : {x : (Ordinal.omega0 ^ γ).ToType | toLex (y, x) ∈ S'}.Finite :=
          Set.not_infinite.mp hy
        let : Fintype ↑{x : (Ordinal.omega0 ^ γ).ToType | toLex (y, x) ∈ S'} := hfin.fintype
        let n := Fintype.card ↑{x : (Ordinal.omega0 ^ γ).ToType | toLex (y, x) ∈ S'}
        let iso := Fintype.orderIsoFinOfCardEq
          (α := ↑{x : (Ordinal.omega0 ^ γ).ToType | toLex (y, x) ∈ S'}) (rfl : Fintype.card _ = n)
        exact ⟨fun a => (iso.symm a).1, fun a b => iso.symm.lt_iff_lt⟩
      have hle_prod : Ordinal.type ((· < ·) : ↑S_fin → ↑S_fin → Prop) ≤
          Ordinal.type ((· < ·) : Lex ((Ordinal.omega0 ^ δ).ToType × ℕ) → _ → Prop) := by
        refine Ordinal.type_le_iff'.mpr ⟨?_⟩
        let ψ : ↑S_fin → Lex ((Ordinal.omega0 ^ δ).ToType × ℕ) := fun p =>
          toLex ((ofLex p.1).1, Classical.choose (hfib_emb (ofLex p.1).1 p.2.2)
            ⟨(ofLex p.1).2, p.2.1⟩)
        have hψ_rel : ∀ p q : ↑S_fin, ψ p < ψ q ↔ p < q := by
          rintro ⟨p, hpS, hpN⟩ ⟨q, hqS, hqN⟩
          rcases p with ⟨yp, xp⟩
          rcases q with ⟨yq, xq⟩
          show Prod.Lex (· < ·) (· < ·)
              (yp, Classical.choose (hfib_emb yp hpN) ⟨xp, hpS⟩)
              (yq, Classical.choose (hfib_emb yq hqN) ⟨xq, hqS⟩) ↔
            Prod.Lex (· < ·) (· < ·) (yp, xp) (yq, xq)
          rw [Prod.lex_def, Prod.lex_def]
          constructor
          · rintro (h1 | ⟨rfl, h2⟩)
            · exact Or.inl h1
            · exact Or.inr ⟨rfl, (Classical.choose_spec (hfib_emb yp hpN) ⟨xp, hpS⟩ ⟨xq, hqS⟩).mp h2⟩
          · rintro (h1 | ⟨rfl, h2⟩)
            · exact Or.inl h1
            · exact Or.inr ⟨rfl, (Classical.choose_spec (hfib_emb yp hpN) ⟨xp, hpS⟩ ⟨xq, hqS⟩).mpr h2⟩
        refine ⟨⟨ψ, ?_⟩, ?_⟩
        · intro p q hpq
          rcases lt_trichotomy p q with h | rfl | h
          · exact (ne_of_lt ((hψ_rel p q).mpr h) hpq).elim
          · rfl
          · exact (ne_of_gt ((hψ_rel q p).mpr h) hpq).elim
        · intro p q
          exact hψ_rel p q
      rw [type_lex_prod, Ordinal.type_nat_lt, Ordinal.type_toType] at hle_prod
      have hmul_pow : Ordinal.omega0 * Ordinal.omega0 ^ δ = Ordinal.omega0 ^ (1 + δ) := by
        rw [Ordinal.opow_add, opow_one]
      rw [hmul_pow] at hle_prod
      have hexp_lt : 1 + δ < γ + δ := by
        by_cases hδ_inf : Ordinal.omega0 ≤ δ
        · rw [Ordinal.one_add_of_omega0_le hδ_inf]
          have hposδ : 0 < δ := lt_of_lt_of_le (by norm_num : (0 : Ordinal) < 2) hδ2
          have h1 : δ < δ + δ := lt_add_of_pos_right δ hposδ
          exact lt_of_lt_of_le h1 (add_le_add hδγ (le_refl δ))
        · push Not at hδ_inf
          obtain ⟨d, rfl⟩ := Ordinal.lt_omega0.mp hδ_inf
          have h1d : (1 : Ordinal) + (d : Ordinal) < (2 : Ordinal) + (d : Ordinal) := by
            rw [show (1 : Ordinal) = ((1 : ℕ) : Ordinal) by norm_num,
                show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num,
                ← Nat.cast_add, ← Nat.cast_add]
            exact Nat.cast_lt.mpr (by omega)
          exact lt_of_lt_of_le h1d (add_le_add hγ2 (le_refl (d : Ordinal)))
      exact lt_of_le_of_lt hle_prod (opow_omega0_strictMono hexp_lt)
    -- By the 1-tuple union partition theorem `ppl035_opow_omega0_union_partition`, `type S_inf ≥ ω^(γ + δ)`!
    have hSinf : Ordinal.omega0 ^ (γ + δ) ≤ Ordinal.type ((· < ·) : ↑S_inf → ↑S_inf → Prop) := by
      rw [← hSunion] at hS'
      rcases ppl035_opow_omega0_union_partition (γ + δ) S_inf S_fin hS' with h | h
      · exact h
      · exact (not_lt_of_ge h hfin_lt).elim
    -- Therefore `type Y_inf ≥ ω^δ`!
    have hYinf : Ordinal.omega0 ^ δ ≤ Ordinal.type ((· < ·) : ↑Y_inf → ↑Y_inf → Prop) := by
      by_contra hlt
      push Not at hlt
      have hle : Ordinal.type ((· < ·) : ↑S_inf → ↑S_inf → Prop) ≤
          Ordinal.type ((· < ·) : Lex (↑Y_inf × (Ordinal.omega0 ^ γ).ToType) → _ → Prop) := by
        refine Ordinal.type_le_iff'.mpr ⟨?_⟩
        refine ⟨⟨fun p => toLex (⟨(ofLex p.1).1, p.2.2⟩, (ofLex p.1).2), ?_⟩, ?_⟩
        · intro p q heq
          rcases Prod.mk.inj heq with ⟨h1, h2⟩
          exact Subtype.ext (Prod.ext (congrArg Subtype.val h1) h2)
        · intro p q
          show Prod.Lex (· < ·) (· < ·) ((⟨(ofLex p.1).1, p.2.2⟩ : ↑Y_inf), (ofLex p.1).2)
              ((⟨(ofLex q.1).1, q.2.2⟩ : ↑Y_inf), (ofLex q.1).2) ↔
            Prod.Lex (· < ·) (· < ·) (ofLex p.1) (ofLex q.1)
          simp only [Prod.lex_def, Subtype.mk_lt_mk, Subtype.mk.injEq]
      rw [type_lex_prod, Ordinal.type_toType] at hle
      have hstrict : Ordinal.omega0 ^ γ * Ordinal.type ((· < ·) : ↑Y_inf → ↑Y_inf → Prop) <
          Ordinal.omega0 ^ γ * Ordinal.omega0 ^ δ :=
        mul_lt_mul_of_pos_left hlt (Ordinal.opow_pos γ Ordinal.omega0_pos)
      rw [← Ordinal.opow_add] at hstrict
      exact not_lt_of_ge (le_trans hSinf hle) hstrict
    -- By pinning of `q`, `q '' Y_inf` has order type `≥ ω^2`!
    have hqY := hq Y_inf hYinf
    have hlex2 : Ordinal.type ((· < ·) : Lex (ℕ × ℕ) → Lex (ℕ × ℕ) → Prop) =
        Ordinal.omega0 ^ (2 : Ordinal) := by
      rw [type_lex_prod, Ordinal.type_nat_lt,
        show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num, Ordinal.opow_natCast, sq]
    rw [← hlex2] at hqY
    obtain ⟨emb2⟩ := Ordinal.type_le_iff'.mp hqY
    -- For every `z : Lex (ℕ × ℕ)`, `(emb2 z).1 ∈ q '' Y_inf`, so its `b`-fiber in `π' '' range f` is infinite!
    have hcol : ∀ z : Lex (ℕ × ℕ), ∃ g : ℕ ↪o ℕ,
        ∀ m, toLex ((emb2 z).1, g m) ∈ Set.range (π' ∘ f) := by
      intro z
      rcases (emb2 z).2 with ⟨y, hyInf, hy_eq⟩
      have hbinf : (b '' {x : (Ordinal.omega0 ^ γ).ToType | toLex (y, x) ∈ S'}).Infinite :=
        hyInf.image hbinj.injOn
      obtain ⟨g, hg⟩ := exists_strictMono_of_infinite_nat hbinf
      refine ⟨g, fun m => ?_⟩
      rcases hg m with ⟨x, hxS', hbx⟩
      rcases hxS' with ⟨u, hu_eq⟩
      dsimp only [Function.comp] at hu_eq
      refine ⟨u, ?_⟩
      show toLex (q (ofLex (e (f u))).1, b (ofLex (e (f u))).2) = toLex ((emb2 z).1, g m)
      rw [hu_eq, ofLex_toLex, hy_eq, hbx]
    let colF : Lex (ℕ × ℕ) → (ℕ ↪o ℕ) := fun z => Classical.choose (hcol z)
    have hcolF : ∀ z m, toLex ((emb2 z).1, colF z m) ∈ Set.range (π' ∘ f) :=
      fun z => Classical.choose_spec (hcol z)
    let emb3' : W3' ↪o W3' :=
      OrderEmbedding.ofStrictMono
        (fun u => toLex ((emb2 (ofLex u).1).1, colF (ofLex u).1 (ofLex u).2))
        (by
          intro u v huv
          rcases u with ⟨u1, u2⟩
          rcases v with ⟨v1, v2⟩
          rcases Prod.lex_def.mp huv with h1 | ⟨rfl, h2⟩
          · exact Prod.Lex.left _ _ (emb2.map_rel_iff.mpr h1)
          · exact Prod.Lex.right _ ((colF u1).strictMono h2))
    refine ⟨isoW.symm.toOrderEmbedding.trans (emb3'.trans isoW.toOrderEmbedding), fun w => ?_⟩
    obtain ⟨u, hu⟩ := hcolF (ofLex (isoW.symm w)).1 (ofLex (isoW.symm w)).2
    refine ⟨u, ?_⟩
    change isoW (π' (f u)) = isoW (emb3' (isoW.symm w))
    exact congrArg isoW hu

/-- **Galvin–Larson Necessary Condition (1974):**
Every nonzero countable ordinal `α` (`α.card ≤ ℵ₀`) satisfying the partition relation
`α → (α, 3)^2` must be additively indecomposable (`α = ω^β`), AND either `β ∈ {0, 1, 2}`
or `β` itself is additively indecomposable (`∃ γ, β = ω^γ`).
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_galvin_larson_necessary {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    (hcount : (Ordinal.type ((· < ·) : τ → τ → Prop)).card ≤ Cardinal.aleph0)
    (hpos : 0 < Ordinal.type ((· < ·) : τ → τ → Prop))
    (hpart : ∀ c : Sym2 τ → Bool,
      (∃ f : τ ↪o τ, ∀ x y, x < y → c s(f x, f y) = true) ∨
      (∃ g : Fin 3 ↪o τ, ∀ i j, i < j → c s(g i, g j) = false)) :
    ∃ β : Ordinal.{0},
      Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 ^ β ∧
      (β = 0 ∨ β = 1 ∨ β = 2 ∨ ∃ γ : Ordinal.{0}, β = Ordinal.omega0 ^ γ) := by
  classical
  set α := Ordinal.type ((· < ·) : τ → τ → Prop)
  -- Step 1: `α` must be additively principal, hence `α = ω^β`.
  have hprinc : Ordinal.IsPrincipal (· + ·) α := by
    intro a b ha hb
    by_contra hge
    push Not at hge
    -- Since `a < α ≤ a + b`, let `r = α - a`: then `a + r = α`, `a < α`, and `r ≤ b < α`!
    have har : a + (α - a) = α := Ordinal.add_sub_cancel_of_le (le_of_lt ha)
    have hr_lt : α - a < α := by
      have hle_b : α - a ≤ b := by
        by_contra hlt
        push Not at hlt
        have hstrict : a + b < a + (α - a) := add_lt_add_right hlt a
        rw [har] at hstrict
        exact not_lt_of_ge hge hstrict
      exact lt_of_le_of_lt hle_b hb
    obtain ⟨c, hno_red, hno_blue⟩ := decomposable_neg_partition har.symm ha hr_lt
    rcases hpart c with ⟨f, hf⟩ | ⟨g, hg⟩
    · obtain ⟨x, y, hxy, hblue⟩ := hno_red f
      exact absurd ((hf x y hxy).symm.trans hblue) (by decide)
    · obtain ⟨i, j, hij, hred⟩ := hno_blue g
      exact absurd ((hg i j hij).symm.trans hred) (by decide)
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hprinc with h0 | ⟨β, hβ⟩
  · exact (ne_of_gt hpos h0).elim
  · dsimp only at hβ
    refine ⟨β, hβ.symm, ?_⟩
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨hβ0, hβ1, hβ2, hβnotpow⟩
    -- Since `β ≠ 0, 1, 2`, we have `3 ≤ β`.
    have hβ3 : (3 : Ordinal) ≤ β := by
      by_contra hlt3
      push Not at hlt3
      have hlt3' : β < ((3 : ℕ) : Ordinal) := by simpa using hlt3
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (lt_trans hlt3' (Ordinal.natCast_lt_omega0 3))
      have hn : n < 3 := Nat.cast_lt.mp hlt3'
      interval_cases n
      · exact hβ0 (by simp)
      · exact hβ1 (by simp)
      · exact hβ2 (by simp)
    -- Helper: `1 ≤ x → a ≤ a * x` for `Ordinal`
    have hmul_ge : ∀ a x : Ordinal.{0}, 0 < a → 1 ≤ x → a ≤ a * x := by
      intro a x ha hx
      rcases eq_or_lt_of_le hx with rfl | hlt
      · rw [mul_one]
      · exact le_of_lt (by simpa [mul_one] using mul_lt_mul_of_pos_left hlt ha)
    -- Decompose `β = γ + δ` with `2 ≤ γ`, `1 ≤ δ`, `δ ≤ γ` using `e = log ω β`, `c = β / ω^e`, `r = β % ω^e`.
    have hdecomp : ∃ γ δ : Ordinal.{0}, β = γ + δ ∧ 2 ≤ γ ∧ 1 ≤ δ ∧ δ ≤ γ := by
      let e := Ordinal.log Ordinal.omega0 β
      have hβne0 : β ≠ 0 := hβ0
      have hle_β : Ordinal.omega0 ^ e ≤ β := Ordinal.opow_log_le_self Ordinal.omega0 hβne0
      have hlt_β : β < Ordinal.omega0 ^ (e + 1) := by
        rw [← Order.succ_eq_add_one]
        exact Ordinal.lt_opow_succ_log_self (by norm_num : (1 : Ordinal) < Ordinal.omega0) β
      have hlt_pow : Ordinal.omega0 ^ e < β :=
        lt_of_le_of_ne hle_β (fun h => hβnotpow e h.symm)
      have hpow_pos : 0 < Ordinal.omega0 ^ e := Ordinal.opow_pos e Ordinal.omega0_pos
      have hpow_ne0 : Ordinal.omega0 ^ e ≠ 0 := ne_of_gt hpow_pos
      let c := β / Ordinal.omega0 ^ e
      let r := β % Ordinal.omega0 ^ e
      have hdiv : Ordinal.omega0 ^ e * c + r = β := Ordinal.div_add_mod β (Ordinal.omega0 ^ e)
      have hr_lt : r < Ordinal.omega0 ^ e := Ordinal.mod_lt β hpow_ne0
      have hc_lt : c < Ordinal.omega0 := by
        rw [← Ordinal.lt_mul_iff_div_lt hpow_ne0]
        rwa [Ordinal.opow_add, opow_one] at hlt_β
      obtain ⟨cn, hcn⟩ := Ordinal.lt_omega0.mp hc_lt
      have hcn_pos : 1 ≤ cn := by
        by_contra h0
        have : cn = 0 := by omega
        rw [this, Nat.cast_zero] at hcn
        rw [hcn, mul_zero, zero_add] at hdiv
        rw [← hdiv] at hle_β
        exact not_lt_of_ge hle_β hr_lt
      by_cases hr0 : r = 0
      · rw [hr0, add_zero] at hdiv
        have hcn2 : 2 ≤ cn := by
          by_contra h1
          have : cn = 1 := by omega
          rw [this, Nat.cast_one] at hcn
          rw [hcn, mul_one] at hdiv
          exact hβnotpow e hdiv.symm
        refine ⟨Ordinal.omega0 ^ e * ((cn - 1 : ℕ) : Ordinal), Ordinal.omega0 ^ e, ?_, ?_, ?_, ?_⟩
        · rw [← hdiv, hcn]
          have hadd : ((cn - 1 : ℕ) : Ordinal) + 1 = (cn : Ordinal) := by
            rw [show (1 : Ordinal) = ((1 : ℕ) : Ordinal) by norm_num, ← Nat.cast_add]
            congr 1; omega
          rw [← hadd, mul_add, mul_one]
        · by_cases he0 : e = 0
          · rw [he0, opow_zero, one_mul] at hdiv ⊢
            rw [hcn] at hdiv
            have hcn3 : 3 ≤ cn := by
              have h3le : ((3 : ℕ) : Ordinal) ≤ (cn : Ordinal) := by
                rw [hdiv]; simpa using hβ3
              exact Nat.cast_le.mp h3le
            rw [show (2 : Ordinal) = ((2 : ℕ) : Ordinal) by norm_num]
            exact Nat.cast_le.mpr (by omega)
          · have he1 : 1 ≤ e :=
              Order.one_le_iff_pos.mpr (lt_of_le_of_ne zero_le (Ne.symm he0))
            have h2om : (2 : Ordinal) ≤ Ordinal.omega0 ^ e :=
              le_trans (le_of_lt (Ordinal.natCast_lt_omega0 2))
                (le_trans (le_of_eq (opow_one Ordinal.omega0).symm)
                  (Ordinal.opow_le_opow_right Ordinal.omega0_pos he1))
            have h1c : (1 : Ordinal) ≤ ((cn - 1 : ℕ) : Ordinal) := by
              rw [show (1 : Ordinal) = ((1 : ℕ) : Ordinal) by norm_num]
              exact Nat.cast_le.mpr (by omega)
            exact le_trans h2om (hmul_ge _ _ hpow_pos h1c)
        · exact Order.one_le_iff_pos.mpr hpow_pos
        · have h1c : (1 : Ordinal) ≤ ((cn - 1 : ℕ) : Ordinal) := by
            rw [show (1 : Ordinal) = ((1 : ℕ) : Ordinal) by norm_num]
            exact Nat.cast_le.mpr (by omega)
          exact hmul_ge _ _ hpow_pos h1c
      · have hr_pos : 1 ≤ r :=
          Order.one_le_iff_pos.mpr (lt_of_le_of_ne zero_le (Ne.symm hr0))
        have he_pos : 1 ≤ e := by
          by_contra h0
          have he0 : e = 0 := by
            by_contra hne
            exact h0 (Order.one_le_iff_pos.mpr (lt_of_le_of_ne zero_le (Ne.symm hne)))
          rw [he0, opow_zero] at hr_lt
          exact not_lt_of_ge hr_pos hr_lt
        refine ⟨Ordinal.omega0 ^ e * c, r, hdiv.symm, ?_, hr_pos, ?_⟩
        · have h2om : (2 : Ordinal) ≤ Ordinal.omega0 ^ e :=
            le_trans (le_of_lt (Ordinal.natCast_lt_omega0 2))
              (le_trans (le_of_eq (opow_one Ordinal.omega0).symm)
                (Ordinal.opow_le_opow_right Ordinal.omega0_pos he_pos))
          have hc1 : (1 : Ordinal) ≤ c := by
            rw [hcn, show (1 : Ordinal) = ((1 : ℕ) : Ordinal) by norm_num]
            exact Nat.cast_le.mpr hcn_pos
          exact le_trans h2om (hmul_ge _ _ hpow_pos hc1)
        · have hc1 : (1 : Ordinal) ≤ c := by
            rw [hcn, show (1 : Ordinal) = ((1 : ℕ) : Ordinal) by norm_num]
            exact Nat.cast_le.mpr hcn_pos
          exact le_trans (le_of_lt hr_lt) (hmul_ge _ _ hpow_pos hc1)
    obtain ⟨γ, δ, hβeq, hγ2, hδ1, hδγ⟩ := hdecomp
    have hcount' : (Ordinal.omega0 ^ (γ + δ)).card ≤ Cardinal.aleph0 := by
      rw [← hβeq, hβ]; exact hcount
    obtain ⟨π, hπ⟩ := pinning_opow_add_to_omega0_cube hγ2 hδ1 hδγ hcount'
    obtain ⟨c3, hno_red3, hno_blue3⟩ := specker_negative_omega0_cube_lex
    obtain ⟨c0, hno_red0, hno_blue0⟩ := pinning_pullback 3 π hπ c3 hno_red3 hno_blue3
    -- Transfer `c0` from `(ω^(γ+δ)).ToType` to `τ` via `orderIsoOfTypeEq`!
    have htype_eq : Ordinal.type ((· < ·) : τ → τ → Prop) =
        Ordinal.type ((· < ·) : (Ordinal.omega0 ^ (γ + δ)).ToType → _ → Prop) := by
      rw [Ordinal.type_toType, ← hβeq, hβ]
    let eτ : τ ≃o (Ordinal.omega0 ^ (γ + δ)).ToType := orderIsoOfTypeEq htype_eq
    let cτ : Sym2 τ → Bool := fun p => c0 (Sym2.map eτ p)
    rcases hpart cτ with ⟨f, hf⟩ | ⟨g, hg⟩
    · obtain ⟨x, y, hxy, hblue⟩ := hno_red0 (eτ.symm.toOrderEmbedding.trans (f.trans eτ.toOrderEmbedding))
      have h := hf (eτ.symm x) (eτ.symm y) (eτ.symm.lt_iff_lt.mpr hxy)
      have h' : c0 s(eτ (f (eτ.symm x)), eτ (f (eτ.symm y))) = true := by simpa [cτ] using h
      exact absurd (h'.symm.trans hblue) (by decide)
    · obtain ⟨i, j, hij, hred⟩ := hno_blue0 (g.trans eτ.toOrderEmbedding)
      have h := hg i j hij
      have h' : c0 s(eτ (g i), eτ (g j)) = false := by simpa [cτ] using h
      exact absurd (h'.symm.trans hred) (by decide)

/-- **Galvin–Larson Necessary Condition for `α > 2` (1974):**
Every countable ordinal `α > 2` satisfying `α → (α, 3)^2` is of the form `α = ω^β` with
`β ∈ {0, 1, 2}` or `∃ γ, β = ω^γ`. Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_galvin_larson_gt_two {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    (hcount : (Ordinal.type ((· < ·) : τ → τ → Prop)).card ≤ Cardinal.aleph0)
    (hgt2 : (2 : Ordinal) < Ordinal.type ((· < ·) : τ → τ → Prop))
    (hpart : ∀ c : Sym2 τ → Bool,
      (∃ f : τ ↪o τ, ∀ x y, x < y → c s(f x, f y) = true) ∨
      (∃ g : Fin 3 ↪o τ, ∀ i j, i < j → c s(g i, g j) = false)) :
    ∃ β : Ordinal.{0},
      Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 ^ β ∧
      (β = 0 ∨ β = 1 ∨ β = 2 ∨ ∃ γ : Ordinal.{0}, β = Ordinal.omega0 ^ γ) :=
  ppl035_galvin_larson_necessary hcount (lt_trans (by norm_num : (0 : Ordinal) < 2) hgt2) hpart

/-! ### Section 5: Complete Finite-Exponent Classification & Hypergraph Ramsey Engine -/

/-- **Complete Finite-Exponent Classification for Erdős Problem #592 (Specker 1957):**
For every natural number `n : ℕ` and every well-ordered type `τ` of order type `ω^n`,
`ω^n → (ω^n, 3)^2` holds if and only if `n ≤ 2`.
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_finite_exponent_complete_classification
    {τ : Type} [LinearOrder τ] [IsWellOrder τ (· < ·)]
    (n : ℕ) (hτ : Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 ^ (n : Ordinal)) :
    (∀ c : Sym2 τ → Bool,
      (∃ f : τ ↪o τ, ∀ x y, x < y → c s(f x, f y) = true) ∨
      (∃ g : Fin 3 ↪o τ, ∀ i j, i < j → c s(g i, g j) = false)) ↔ n ≤ 2 := by
  constructor
  · intro hpart
    by_contra hgt
    have hn3 : 3 ≤ n := by omega
    obtain ⟨c, hno_red, hno_blue⟩ := ppl035_specker_negative_finite n hn3 hτ
    rcases hpart c with ⟨f, hf⟩ | ⟨g, hg⟩
    · obtain ⟨x, y, hxy, hblue⟩ := hno_red f
      exact absurd ((hf x y hxy).symm.trans hblue) (by decide)
    · obtain ⟨i, j, hij, hred⟩ := hno_blue g
      exact absurd ((hg i j hij).symm.trans hred) (by decide)
  · intro hn2 c
    interval_cases n
    · left
      refine ⟨(OrderIso.refl τ).toOrderEmbedding, fun x y hxy => ?_⟩
      exfalso
      have h1 : Ordinal.type ((· < ·) : τ → τ → Prop) = 1 := by
        simpa [opow_zero] using hτ
      have hfin : Ordinal.type ((· < ·) : τ → τ → Prop) =
          Ordinal.type ((· < ·) : Fin 1 → Fin 1 → Prop) := by
        rw [h1, Ordinal.type_fin]; norm_num
      let e : τ ≃o Fin 1 := orderIsoOfTypeEq hfin
      have hlt : e x < e y := e.lt_iff_lt.mpr hxy
      exact lt_irrefl _ (Subsingleton.elim (e x) (e y) ▸ hlt)
    · have hτ1 : Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 := by
        simpa [opow_one] using hτ
      exact ppl035_infinite_ramsey_omega0 hτ1 3 c
    · have hτ2 : Ordinal.type ((· < ·) : τ → τ → Prop) = Ordinal.omega0 ^ (2 : Ordinal) := by
        simpa using hτ
      exact ppl035_specker_positive_omega0_sq hτ2 c

/-- **Infinite Hypergraph Ramsey Theorem (`ω → (ω)^r_2` for all `r : ℕ`):**
Every 2-coloring of strictly increasing `r`-tuples of `ℕ` admits a strictly increasing
infinite homogeneous sequence `f : ℕ ↪o ℕ` (foundational combinatorial engine for
Chang's 1972 / Larson's 1973 canonical-form analysis on `ω^ω`).
Pure-Mathlib statement (`0` custom definitions). -/
theorem ppl035_infinite_ramsey_r_tuples (r : ℕ) :
    ∀ (c : { s : Fin r → ℕ // StrictMono s } → Bool),
      ∃ (b : Bool) (f : ℕ ↪o ℕ),
        ∀ s : { s : Fin r → ℕ // StrictMono s },
          c ⟨f ∘ s.1, f.strictMono.comp s.2⟩ = b := by
  classical
  induction r with
  | zero =>
    intro c
    let s0 : { s : Fin 0 → ℕ // StrictMono s } := ⟨Fin.elim0, fun i => i.elim0⟩
    refine ⟨c s0, (OrderIso.refl ℕ).toOrderEmbedding, fun s => ?_⟩
    congr 1
    exact Subtype.ext (funext (fun i => i.elim0))
  | succ r ih =>
    intro c
    have hthin : ∀ (A : Set ℕ), A.Infinite →
        ∃ (a : ℕ) (b : Bool) (B : Set ℕ),
          a ∈ A ∧ B ⊆ {y ∈ A | a < y} ∧ B.Infinite ∧
          ∀ s : { s : Fin (r + 1) → ℕ // StrictMono s },
            s.1 0 = a → (∀ i : Fin r, s.1 i.succ ∈ B) → c s = b := by
      intro A hAinf
      obtain ⟨a, haA⟩ := hAinf.nonempty
      let A_gt : Set ℕ := {y ∈ A | a < y}
      have hAgt_inf : A_gt.Infinite := by
        have hfin : {y ∈ A | y ≤ a}.Finite := (Set.finite_le_nat a).subset (fun y hy => hy.2)
        refine (hAinf.sdiff hfin).mono ?_
        intro y ⟨hyA, hyn⟩
        refine ⟨hyA, ?_⟩
        by_contra hle
        exact hyn ⟨hyA, le_of_not_gt hle⟩
      obtain ⟨e, he⟩ := exists_strictMono_of_infinite_nat hAgt_inf
      let c_sub : { s : Fin r → ℕ // StrictMono s } → Bool := fun s =>
        c ⟨Fin.cons a (e ∘ s.1), by
          intro i j
          refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij
          · exact (lt_irrefl _ hij).elim
          · simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
            exact (he (s.1 j')).2
          · exact (not_lt_of_ge (Fin.zero_le _) hij).elim
          · simp only [Fin.cons_succ, Function.comp_apply]
            exact e.strictMono (s.2 (Fin.succ_lt_succ_iff.mp hij))⟩
      obtain ⟨b, f, hf⟩ := ih c_sub
      let B : Set ℕ := Set.range (e ∘ f)
      refine ⟨a, b, B, haA, ?_, Set.infinite_range_of_injective (e.injective.comp f.injective), ?_⟩
      · rintro _ ⟨n, rfl⟩
        exact he (f n)
      · intro s hs0 hsB
        have hex : ∀ i : Fin r, ∃ n : ℕ, e (f n) = s.1 i.succ := fun i => hsB i
        let tFun : Fin r → ℕ := fun i => Classical.choose (hex i)
        have htFun : ∀ i, e (f (tFun i)) = s.1 i.succ := fun i => Classical.choose_spec (hex i)
        have htMono : StrictMono tFun := by
          intro i j hij
          have hlt : e (f (tFun i)) < e (f (tFun j)) := by
            rw [htFun i, htFun j]
            exact s.2 (Fin.succ_lt_succ_iff.mpr hij)
          exact f.lt_iff_lt.mp (e.lt_iff_lt.mp hlt)
        have hval := hf ⟨tFun, htMono⟩
        have hseq_fun : Fin.cons a (e ∘ (f ∘ tFun)) = s.1 := by
          funext i
          refine Fin.cases ?_ (fun i' => ?_) i
          · simp [hs0]
          · simp only [Fin.cons_succ, Function.comp_apply]
            exact htFun i'
        have hseq : (⟨Fin.cons a (e ∘ (f ∘ tFun)), hseq_fun.symm ▸ s.2⟩ :
            { s : Fin (r + 1) → ℕ // StrictMono s }) = s := Subtype.ext hseq_fun
        rw [← hseq]
        exact hval
    -- Iterate `hthin` ω times to get `x 0 < x 1 < ...` with color depending only on the first element `x i`!
    let St := { p : (ℕ × Bool) × Set ℕ // p.2.Infinite ∧ (∀ y ∈ p.2, p.1.1 < y) ∧
      ∀ s : { s : Fin (r + 1) → ℕ // StrictMono s },
        s.1 0 = p.1.1 → (∀ i : Fin r, s.1 i.succ ∈ p.2) → c s = p.1.2 }
    have h0 : ∃ st0 : St, True := by
      obtain ⟨a, b, B, _, hBsub, hBinf, hBc⟩ := hthin Set.univ Set.infinite_univ
      exact ⟨⟨((a, b), B), hBinf, fun y hy => (hBsub hy).2, hBc⟩, trivial⟩
    have hstep : ∀ st : St, ∃ st' : St,
        st'.1.1.1 ∈ st.1.2 ∧ st'.1.2 ⊆ st.1.2 := by
      intro st
      obtain ⟨a, b, B, ha, hBsub, hBinf, hBc⟩ := hthin st.1.2 st.2.1
      exact ⟨⟨((a, b), B), hBinf, fun y hy => (hBsub hy).2, hBc⟩, ha, fun y hy => (hBsub hy).1⟩
    let P : ℕ → St := Nat.rec (Classical.choose h0) (fun _ prev => Classical.choose (hstep prev))
    have hP_mem : ∀ k, (P (k + 1)).1.1.1 ∈ (P k).1.2 := fun k => (Classical.choose_spec (hstep (P k))).1
    have hP_sub : ∀ k, (P (k + 1)).1.2 ⊆ (P k).1.2 := fun k => (Classical.choose_spec (hstep (P k))).2
    have hP_sub_le : ∀ a b, a ≤ b → (P b).1.2 ⊆ (P a).1.2 := by
      intro a b hab
      induction hab with
      | refl => exact Set.Subset.rfl
      | @step m _ ihm => intro y hy; exact ihm (hP_sub m hy)
    have hP_lt_mem : ∀ {i j}, i < j → (P j).1.1.1 ∈ (P i).1.2 ∧ (P i).1.1.1 < (P j).1.1.1 := by
      intro i j hij
      have hmem : (P j).1.1.1 ∈ (P i).1.2 := by
        cases j with
        | zero => omega
        | succ m => exact hP_sub_le i m (by omega) (hP_mem m)
      exact ⟨hmem, (P i).2.2.1 _ hmem⟩
    -- Pigeonhole on the 2-coloring `k ↦ (P k).1.1.2` of `ℕ`.
    let I_t : Set ℕ := {k | (P k).1.1.2 = true}
    let I_f : Set ℕ := {k | (P k).1.1.2 = false}
    have hinf : I_t.Infinite ∨ I_f.Infinite := by
      by_contra h
      push Not at h
      have huniv : I_t ∪ I_f = Set.univ := by
        ext k
        simp only [Set.mem_union, Set.mem_univ, iff_true, I_t, I_f]
        change (P k).1.1.2 = true ∨ (P k).1.1.2 = false
        cases (P k).1.1.2 <;> simp
      have hfin : (Set.univ : Set ℕ).Finite := by rw [← huniv]; exact h.1.union h.2
      exact Set.infinite_univ hfin
    have finish : ∀ (b : Bool) (I : Set ℕ), I.Infinite → (∀ k ∈ I, (P k).1.1.2 = b) →
        ∃ f : ℕ ↪o ℕ, ∀ s : { s : Fin (r + 1) → ℕ // StrictMono s },
          c ⟨f ∘ s.1, f.strictMono.comp s.2⟩ = b := by
      intro b I hIinf hIb
      obtain ⟨idx, hidx⟩ := exists_strictMono_of_infinite_nat hIinf
      let f : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono (fun n => (P (idx n)).1.1.1)
        (fun i j hij => (hP_lt_mem (idx.strictMono hij)).2)
      refine ⟨f, fun s => ?_⟩
      have hcol := (P (idx (s.1 0))).2.2.2 ⟨f ∘ s.1, f.strictMono.comp s.2⟩ rfl (fun i => by
        have hlt : idx (s.1 0) < idx (s.1 i.succ) :=
          idx.strictMono (s.2 (Fin.succ_pos i))
        exact (hP_lt_mem hlt).1)
      rw [hcol, hIb _ (hidx (s.1 0))]
    rcases hinf with ht | hf
    · obtain ⟨f, hf⟩ := finish true I_t ht (fun _ hk => hk)
      exact ⟨true, f, hf⟩
    · obtain ⟨f, hf⟩ := finish false I_f hf (fun _ hk => hk)
      exact ⟨false, f, hf⟩

end PPL035
