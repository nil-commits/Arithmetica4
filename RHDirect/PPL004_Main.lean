/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.Free
import Mathlib.Logic.Relation
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-!
# PPL 004: Wolfram `$20,000` `S`-Combinator Universality Prize — Structural Foundations

## Scope & Honest Labeling
This file formalizes a comprehensive pure-Mathlib foundation (`0` `sorry`, `0` custom or `private`
definitions in any public theorem signature) for **PPL 004** (Wolfram Foundation `$20,000` Prize:
*Is the `S` Combinator Computation-Universal by Itself?*, LIVE-VERIFIED OPEN as of 2026).

- **Honest Scope:** The full `$20,000` Wolfram Prize (whether pure `S` alone is computation-universal
  under a finitary encoding/decoding scheme) remains **OPEN**. This file makes **no claim** to solve
  the open universality prize. Instead, it machine-verifies the foundational structural theory of pure
  `S`-combinator reduction, its exact obstructions (`K`-impossibility, non-erasing variable invariance,
  monotone leaf growth), minimal non-terminating terms (Waldmann 2000), and the sharp contrast with
  Turing-complete `SK`-combinatory logic.

- **Pure-Mathlib Representation (Zero Custom/Private Defs in Public Signatures):**
  - Closed pure `S`-terms: `FreeMagma Unit` (`FreeMagma.of ()` = `S`, `x * y` = application).
  - Open pure `S`-terms: `FreeMagma (Option α)` (`FreeMagma.of none` = `S`, `FreeMagma.of (some v)` = variable `v`).
  - Closed `SK`-terms: `FreeMagma Bool` (`FreeMagma.of true` = `S`, `FreeMagma.of false` = `K`).
  - Open `SK`-terms: `FreeMagma (Bool ⊕ α)`.
  - Single-step `S`- and `SK`-reduction are expressed directly in public theorem types via their
    exact least-congruence characterization (`∀ R, ... → R a b`), with multi-step reduction
    `Relation.ReflTransGen` and convertibility `Relation.EqvGen`.
  - Term size (leaf count) is `FreeMagma.length`; variable multiplicity is lifted via
    `Multiplicative.toAdd (FreeMagma.lift ... t)`.

## Main Verified Public Theorems
1. `ppl004_s_confluence` — Confluence of `S`-reduction on `FreeMagma α` (Takahashi parallel reduction).
2. `ppl004_s_church_rosser` — Church–Rosser property (`Relation.EqvGen` implies common reduct).
3. `ppl004_s_unique_normal_form` — Uniqueness of normal forms under `S`-conversion.
4. `ppl004_closed_s_confluence` — Confluence specialization on closed `S`-terms `FreeMagma Unit`.
5. `ppl004_open_s_unique_normal_form` — Unique normal forms on open `S`-terms `FreeMagma (Option α)`.
6. `ppl004_s_step_length_le` & `ppl004_s_multistep_length_le` — Monotone leaf-count growth `|t'| ≥ |t|`.
7. `ppl004_s_redex_length_formula` & `ppl004_closed_s_step_length_eq_iff` — Exact size-preserving
   characterization: closed `S`-steps preserve leaf count iff the reduced redex has `z = S`.
8. `ppl004_s_small_terms_normal` — Every term of leaf count `≤ 3` is already in normal form.
9. `ppl004_s_var_count_nondecreasing` & `ppl004_s_var_absence_preserved` — Non-erasing and
   non-creating variable invariants.
10. `ppl004_s_no_k_combinator` & `ppl004_s_no_k_combinator_eqv` — Unconditional impossibility of `K`
    in pure `S` (neither reduction nor `S`-conversion can represent `K`).
11. `ppl004_s_no_constant_combinator` — No closed pure `S`-term is constant modulo `S`-conversion.
12. `ppl004_s_no_I_B_C_W_M_combinators` — None of `I, B, C, W, M` is representable in pure `S`
    even up to full `S`-conversion (`Relation.EqvGen`), via monotone leaf count + Church–Rosser.
13. `ppl004_waldmann_size7_no_normal_form` — Minimal size-7 pure `S`-term `S S S (S S) S S` has
    unbounded reducts and NO normal form.
14. `ppl004_waldmann_size7_alt_no_normal_form` — Second size-7 pure `S`-term `S (S S) S S S S` has
    NO normal form.
15. `ppl004_waldmann_size8_no_normal_form` — Minimal size-8 non-head-normalizing pure `S`-term
    `S S S (S S) S S S` has NO normal form.
16. `ppl004_self_app_size10_no_normal_form` — Symmetric size-10 pure `S`-term
    `S (S S) (S S) (S (S S) (S S))` has NO normal form.
17. `ppl004_sk_confluence` — Confluence of `SK`-combinatory logic (Takahashi parallel reduction).
18. `ppl004_sk_combinatory_completeness` — Full Bracket Abstraction Theorem for `SK`.
19. `ppl004_sk_standard_combinators` — Explicit `I, B, C, W, M` and Turing fixed-point combinator `Θ`
    (`Θ * f →* f * (Θ * f)`) in `SK`.
-/

namespace PPL004

/-! ### Section 1: Internal S-Reduction, Takahashi Parallel Reduction, and Confluence -/

private inductive SStep {α : Type*} (s : α) : FreeMagma α → FreeMagma α → Prop
  | redex (x y z : FreeMagma α) :
      SStep s (FreeMagma.of s * x * y * z) (x * z * (y * z))
  | left {u u' : FreeMagma α} (v : FreeMagma α) :
      SStep s u u' → SStep s (u * v) (u' * v)
  | right (u : FreeMagma α) {v v' : FreeMagma α} :
      SStep s v v' → SStep s (u * v) (u * v')

private lemma sStep_iff_least {α : Type*} (s : α) (a b : FreeMagma α) :
    SStep s a b ↔
      ∀ (R : FreeMagma α → FreeMagma α → Prop),
        (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
        (∀ u u' v, R u u' → R (u * v) (u' * v)) →
        (∀ u v v', R v v' → R (u * v) (u * v')) →
        R a b := by
  constructor
  · intro h R hred hL hR
    induction h with
    | redex x y z => exact hred x y z
    | left v _ ih => exact hL _ _ v ih
    | right u _ ih => exact hR u _ _ ih
  · intro h
    exact h (SStep s) SStep.redex (fun _ _ v h' => SStep.left v h') (fun u _ _ h' => SStep.right u h')

private lemma sStep_rtg_left {α : Type*} {s : α} {u u' : FreeMagma α} (v : FreeMagma α)
    (h : Relation.ReflTransGen (SStep s) u u') :
    Relation.ReflTransGen (SStep s) (u * v) (u' * v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (SStep.left v hstep)

private lemma sStep_rtg_right {α : Type*} {s : α} (u : FreeMagma α) {v v' : FreeMagma α}
    (h : Relation.ReflTransGen (SStep s) v v') :
    Relation.ReflTransGen (SStep s) (u * v) (u * v') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (SStep.right u hstep)

private lemma sStep_rtg_mul {α : Type*} {s : α} {u u' v v' : FreeMagma α}
    (hu : Relation.ReflTransGen (SStep s) u u') (hv : Relation.ReflTransGen (SStep s) v v') :
    Relation.ReflTransGen (SStep s) (u * v) (u' * v') :=
  (sStep_rtg_left v hu).trans (sStep_rtg_right u' hv)

private inductive SPar {α : Type*} (s : α) : FreeMagma α → FreeMagma α → Prop
  | refl (t : FreeMagma α) : SPar s t t
  | mul {u u' v v' : FreeMagma α} :
      SPar s u u' → SPar s v v' → SPar s (u * v) (u' * v')
  | redex {x x' y y' z z' : FreeMagma α} :
      SPar s x x' → SPar s y y' → SPar s z z' →
      SPar s (FreeMagma.of s * x * y * z) (x' * z' * (y' * z'))

private lemma sStep_to_sPar {α : Type*} {s : α} {a b : FreeMagma α} (h : SStep s a b) :
    SPar s a b := by
  induction h with
  | redex x y z => exact SPar.redex (SPar.refl x) (SPar.refl y) (SPar.refl z)
  | left v _ ih => exact SPar.mul ih (SPar.refl v)
  | right u _ ih => exact SPar.mul (SPar.refl u) ih

private lemma sPar_to_rtg {α : Type*} {s : α} {a b : FreeMagma α} (h : SPar s a b) :
    Relation.ReflTransGen (SStep s) a b := by
  induction h with
  | refl _ => exact Relation.ReflTransGen.refl
  | mul _ _ ihu ihv => exact sStep_rtg_mul ihu ihv
  | redex _ _ _ ihx ihy ihz =>
    have h1 : Relation.ReflTransGen (SStep s)
        (FreeMagma.of s * _ * _ * _) (FreeMagma.of s * _ * _ * _) :=
      sStep_rtg_mul (sStep_rtg_mul (sStep_rtg_mul Relation.ReflTransGen.refl ihx) ihy) ihz
    exact h1.tail (SStep.redex _ _ _)

private lemma sPar_of_inv {α : Type*} {s a : α} {w : FreeMagma α}
    (h : SPar s (FreeMagma.of a) w) : w = FreeMagma.of a := by
  cases h with
  | refl => rfl

private lemma sPar_of_mul_inv {α : Type*} {s a : α} {x w : FreeMagma α}
    (h : SPar s (FreeMagma.of a * x) w) :
    ∃ x', w = FreeMagma.of a * x' ∧ SPar s x x' := by
  cases h with
  | refl => exact ⟨x, rfl, SPar.refl x⟩
  | mul hu hv =>
    obtain rfl := sPar_of_inv hu
    exact ⟨_, rfl, hv⟩

private lemma sPar_of_mul_mul_inv {α : Type*} {s a : α} {x y w : FreeMagma α}
    (h : SPar s (FreeMagma.of a * x * y) w) :
    ∃ x' y', w = FreeMagma.of a * x' * y' ∧ SPar s x x' ∧ SPar s y y' := by
  cases h with
  | refl => exact ⟨x, y, rfl, SPar.refl x, SPar.refl y⟩
  | mul hu hv =>
    obtain ⟨x', rfl, hx⟩ := sPar_of_mul_inv hu
    exact ⟨x', _, rfl, hx, hv⟩

private noncomputable def completeDev {α : Type*} [DecidableEq α] (s : α) :
    FreeMagma α → FreeMagma α
  | FreeMagma.of a => FreeMagma.of a
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.mul (FreeMagma.of a) x) y) z =>
      if a = s then
        completeDev s x * completeDev s z * (completeDev s y * completeDev s z)
      else
        completeDev s (FreeMagma.of a * x * y) * completeDev s z
  | FreeMagma.mul u v => completeDev s u * completeDev s v

private lemma completeDev_redex {α : Type*} [DecidableEq α] (s : α) (x y z : FreeMagma α) :
    completeDev s (FreeMagma.of s * x * y * z) =
      completeDev s x * completeDev s z * (completeDev s y * completeDev s z) := by
  change (if s = s then _ else _) = _
  simp

private lemma sPar_completeDev_self {α : Type*} [DecidableEq α] (s : α) :
    ∀ t : FreeMagma α, SPar s t (completeDev s t)
  | FreeMagma.of a => SPar.refl _
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.mul (FreeMagma.of a) x) y) z => by
      change SPar s _ (if a = s then _ else _)
      split_ifs with ha
      · subst a
        exact SPar.redex (sPar_completeDev_self s x) (sPar_completeDev_self s y)
          (sPar_completeDev_self s z)
      · exact SPar.mul (sPar_completeDev_self s (FreeMagma.of a * x * y))
          (sPar_completeDev_self s z)
  | FreeMagma.mul (FreeMagma.of a) v =>
      SPar.mul (SPar.refl _) (sPar_completeDev_self s v)
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.of a) x) v =>
      SPar.mul (sPar_completeDev_self s (FreeMagma.of a * x)) (sPar_completeDev_self s v)
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.mul (FreeMagma.mul a b) c) d) v =>
      SPar.mul (sPar_completeDev_self s (a * b * c * d)) (sPar_completeDev_self s v)

private lemma sPar_triangle {α : Type*} [DecidableEq α] (s : α) :
    ∀ {t u : FreeMagma α}, SPar s t u → SPar s u (completeDev s t) := by
  intro t u h
  induction h with
  | refl t => exact sPar_completeDev_self s t
  | redex hx hy hz ihx ihy ihz =>
    rw [completeDev_redex]
    exact SPar.mul (SPar.mul ihx ihz) (SPar.mul ihy ihz)
  | @mul u u' v v' hu hv ihu ihv =>
    cases u with
    | of a =>
      exact SPar.mul ihu ihv
    | mul u1 u2 =>
      cases u1 with
      | of a =>
        exact SPar.mul ihu ihv
      | mul u11 u12 =>
        cases u11 with
        | of a =>
          change SPar s (u' * v') (if a = s then _ else _)
          split_ifs with ha
          · subst a
            obtain ⟨x', y', rfl, _, _⟩ := sPar_of_mul_mul_inv hu
            have ihu' : SPar s (FreeMagma.of s * x' * y')
                (FreeMagma.of s * completeDev s u12 * completeDev s u2) := ihu
            obtain ⟨x'', y'', heq, ihx, ihy⟩ := sPar_of_mul_mul_inv ihu'
            cases heq
            exact SPar.redex ihx ihy ihv
          · exact SPar.mul ihu ihv
        | mul _ _ =>
          exact SPar.mul ihu ihv

private lemma sPar_diamond {α : Type*} (s : α) {t u₁ u₂ : FreeMagma α}
    (h1 : SPar s t u₁) (h2 : SPar s t u₂) :
    ∃ w, SPar s u₁ w ∧ SPar s u₂ w := by
  classical
  exact ⟨completeDev s t, sPar_triangle s h1, sPar_triangle s h2⟩

private lemma sPar_strip {α : Type*} (s : α) {t u₁ u₂ : FreeMagma α}
    (h1 : SPar s t u₁) (h2 : Relation.ReflTransGen (SPar s) t u₂) :
    ∃ w, Relation.ReflTransGen (SPar s) u₁ w ∧ SPar s u₂ w := by
  induction h2 generalizing u₁ with
  | refl => exact ⟨u₁, Relation.ReflTransGen.refl, h1⟩
  | tail _ hstep ih =>
    obtain ⟨w₁, hw₁, hw₂⟩ := ih h1
    obtain ⟨w₂, hw₃, hw₄⟩ := sPar_diamond s hw₂ hstep
    exact ⟨w₂, hw₁.tail hw₃, hw₄⟩

private lemma sPar_confluent {α : Type*} (s : α) {t u₁ u₂ : FreeMagma α}
    (h1 : Relation.ReflTransGen (SPar s) t u₁) (h2 : Relation.ReflTransGen (SPar s) t u₂) :
    ∃ w, Relation.ReflTransGen (SPar s) u₁ w ∧ Relation.ReflTransGen (SPar s) u₂ w := by
  induction h1 generalizing u₂ with
  | refl => exact ⟨u₂, h2, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨w₁, hw₁, hw₂⟩ := ih h2
    obtain ⟨w₂, hw₃, hw₄⟩ := sPar_strip s hstep hw₁
    exact ⟨w₂, hw₃, hw₂.tail hw₄⟩

private lemma sStep_rtg_iff_sPar_rtg {α : Type*} (s : α) (a b : FreeMagma α) :
    Relation.ReflTransGen (SStep s) a b ↔ Relation.ReflTransGen (SPar s) a b := by
  constructor
  · intro h
    exact Relation.ReflTransGen.mono (fun _ _ hs => sStep_to_sPar hs) a b h
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hpar ih => exact ih.trans (sPar_to_rtg hpar)

private lemma sStep_confluent {α : Type*} (s : α) {t u₁ u₂ : FreeMagma α}
    (h1 : Relation.ReflTransGen (SStep s) t u₁) (h2 : Relation.ReflTransGen (SStep s) t u₂) :
    ∃ w, Relation.ReflTransGen (SStep s) u₁ w ∧ Relation.ReflTransGen (SStep s) u₂ w := by
  rw [sStep_rtg_iff_sPar_rtg] at h1 h2
  obtain ⟨w, hw1, hw2⟩ := sPar_confluent s h1 h2
  exact ⟨w, (sStep_rtg_iff_sPar_rtg s _ _).2 hw1, (sStep_rtg_iff_sPar_rtg s _ _).2 hw2⟩

private lemma sStep_church_rosser {α : Type*} (s : α) {u v : FreeMagma α}
    (h : Relation.EqvGen (SStep s) u v) :
    ∃ w, Relation.ReflTransGen (SStep s) u w ∧ Relation.ReflTransGen (SStep s) v w := by
  induction h with
  | rel _ _ hstep => exact ⟨_, Relation.ReflTransGen.single hstep, Relation.ReflTransGen.refl⟩
  | refl x => exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm _ _ _ ih =>
    obtain ⟨w, hw1, hw2⟩ := ih
    exact ⟨w, hw2, hw1⟩
  | trans _ _ _ _ _ ih1 ih2 =>
    obtain ⟨w₁, h1, h2⟩ := ih1
    obtain ⟨w₂, h3, h4⟩ := ih2
    obtain ⟨w, hw1, hw2⟩ := sStep_confluent s h2 h3
    exact ⟨w, h1.trans hw1, h4.trans hw2⟩

private lemma rtg_eq_of_normal {α : Type*} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) (hnf : ∀ c, ¬ R a c) : b = a := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ => exact False.elim (hnf _ hstep)

private lemma rtg_iff_of_rel_iff {α : Type*} {R₁ R₂ : α → α → Prop}
    (hiff : ∀ x y, R₁ x y ↔ R₂ x y) (a b : α) :
    Relation.ReflTransGen R₁ a b ↔ Relation.ReflTransGen R₂ a b :=
  ⟨fun h => Relation.ReflTransGen.mono (fun x y hxy => (hiff x y).1 hxy) a b h,
   fun h => Relation.ReflTransGen.mono (fun x y hxy => (hiff x y).2 hxy) a b h⟩

private lemma eqv_iff_of_rel_iff {α : Type*} {R₁ R₂ : α → α → Prop}
    (hiff : ∀ x y, R₁ x y ↔ R₂ x y) (a b : α) :
    Relation.EqvGen R₁ a b ↔ Relation.EqvGen R₂ a b := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel x y ((hiff x y).1 hxy)
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact Relation.EqvGen.symm x y ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans x y z ih1 ih2
  · intro h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel x y ((hiff x y).2 hxy)
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact Relation.EqvGen.symm x y ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans x y z ih1 ih2

/-- **Confluence of Pure `S`-Reduction (General `FreeMagma α`)**:
Using Takahashi parallel reduction, if `t →* u₁` and `t →* u₂` under the `S`-combinator rule
`S x y z → x z (y z)`, then there exists a common reduct `w` with `u₁ →* w` and `u₂ →* w`. -/
theorem ppl004_s_confluence {α : Type*} (s : α) {t u₁ u₂ : FreeMagma α}
    (h1 : Relation.ReflTransGen
      (fun a b : FreeMagma α =>
        ∀ (R : FreeMagma α → FreeMagma α → Prop),
          (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) t u₁)
    (h2 : Relation.ReflTransGen
      (fun a b : FreeMagma α =>
        ∀ (R : FreeMagma α → FreeMagma α → Prop),
          (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) t u₂) :
    ∃ w : FreeMagma α,
      Relation.ReflTransGen
        (fun a b : FreeMagma α =>
          ∀ (R : FreeMagma α → FreeMagma α → Prop),
            (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
            (∀ u u' v, R u u' → R (u * v) (u' * v)) →
            (∀ u v v', R v v' → R (u * v) (u * v')) →
            R a b) u₁ w ∧
      Relation.ReflTransGen
        (fun a b : FreeMagma α =>
          ∀ (R : FreeMagma α → FreeMagma α → Prop),
            (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
            (∀ u u' v, R u u' → R (u * v) (u' * v)) →
            (∀ u v v', R v v' → R (u * v) (u * v')) →
            R a b) u₂ w := by
  have hiff := sStep_iff_least s
  have h1' := (rtg_iff_of_rel_iff hiff t u₁).2 h1
  have h2' := (rtg_iff_of_rel_iff hiff t u₂).2 h2
  obtain ⟨w, hw1, hw2⟩ := sStep_confluent s h1' h2'
  exact ⟨w, (rtg_iff_of_rel_iff hiff u₁ w).1 hw1, (rtg_iff_of_rel_iff hiff u₂ w).1 hw2⟩

/-- **Church–Rosser Theorem for Pure `S`-Reduction**:
Any two `S`-convertible terms (`Relation.EqvGen`) admit a common reduct. -/
theorem ppl004_s_church_rosser {α : Type*} (s : α) {u v : FreeMagma α}
    (h : Relation.EqvGen
      (fun a b : FreeMagma α =>
        ∀ (R : FreeMagma α → FreeMagma α → Prop),
          (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) u v) :
    ∃ w : FreeMagma α,
      Relation.ReflTransGen
        (fun a b : FreeMagma α =>
          ∀ (R : FreeMagma α → FreeMagma α → Prop),
            (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
            (∀ u u' v, R u u' → R (u * v) (u' * v)) →
            (∀ u v v', R v v' → R (u * v) (u * v')) →
            R a b) u w ∧
      Relation.ReflTransGen
        (fun a b : FreeMagma α =>
          ∀ (R : FreeMagma α → FreeMagma α → Prop),
            (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
            (∀ u u' v, R u u' → R (u * v) (u' * v)) →
            (∀ u v v', R v v' → R (u * v) (u * v')) →
            R a b) v w := by
  have hiff := sStep_iff_least s
  have h' := (eqv_iff_of_rel_iff hiff u v).2 h
  obtain ⟨w, hw1, hw2⟩ := sStep_church_rosser s h'
  exact ⟨w, (rtg_iff_of_rel_iff hiff u w).1 hw1, (rtg_iff_of_rel_iff hiff v w).1 hw2⟩

/-- **Uniqueness of Normal Forms for Pure `S`-Reduction**:
If `n₁` and `n₂` are `S`-convertible and both are normal forms, then `n₁ = n₂`. -/
theorem ppl004_s_unique_normal_form {α : Type*} (s : α) {n₁ n₂ : FreeMagma α}
    (heqv : Relation.EqvGen
      (fun a b : FreeMagma α =>
        ∀ (R : FreeMagma α → FreeMagma α → Prop),
          (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) n₁ n₂)
    (hn1 : ∀ m, ¬ ∀ (R : FreeMagma α → FreeMagma α → Prop),
      (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
      (∀ u u' v, R u u' → R (u * v) (u' * v)) →
      (∀ u v v', R v v' → R (u * v) (u * v')) →
      R n₁ m)
    (hn2 : ∀ m, ¬ ∀ (R : FreeMagma α → FreeMagma α → Prop),
      (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
      (∀ u u' v, R u u' → R (u * v) (u' * v)) →
      (∀ u v v', R v v' → R (u * v) (u * v')) →
      R n₂ m) :
    n₁ = n₂ := by
  obtain ⟨w, hw1, hw2⟩ := ppl004_s_church_rosser s heqv
  have h1 := rtg_eq_of_normal hw1 hn1
  have h2 := rtg_eq_of_normal hw2 hn2
  exact h1.symm.trans h2

/-- **Confluence on Closed Pure `S`-Terms (`FreeMagma Unit`)**. -/
theorem ppl004_closed_s_confluence {t u₁ u₂ : FreeMagma Unit}
    (h1 : Relation.ReflTransGen
      (fun a b : FreeMagma Unit =>
        ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
          (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) t u₁)
    (h2 : Relation.ReflTransGen
      (fun a b : FreeMagma Unit =>
        ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
          (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) t u₂) :
    ∃ w : FreeMagma Unit,
      Relation.ReflTransGen
        (fun a b : FreeMagma Unit =>
          ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
            (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
            (∀ u u' v, R u u' → R (u * v) (u' * v)) →
            (∀ u v v', R v v' → R (u * v) (u * v')) →
            R a b) u₁ w ∧
      Relation.ReflTransGen
        (fun a b : FreeMagma Unit =>
          ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
            (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
            (∀ u u' v, R u u' → R (u * v) (u' * v)) →
            (∀ u v v', R v v' → R (u * v) (u * v')) →
            R a b) u₂ w :=
  ppl004_s_confluence () h1 h2

/-- **Uniqueness of Normal Forms on Open Pure `S`-Terms (`FreeMagma (Option α)`)**. -/
theorem ppl004_open_s_unique_normal_form {α : Type*} {t n₁ n₂ : FreeMagma (Option α)}
    (h1 : Relation.ReflTransGen
      (fun a b : FreeMagma (Option α) =>
        ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
          (∀ x y z, R (FreeMagma.of none * x * y * z) (x * z * (y * z))) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) t n₁)
    (h2 : Relation.ReflTransGen
      (fun a b : FreeMagma (Option α) =>
        ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
          (∀ x y z, R (FreeMagma.of none * x * y * z) (x * z * (y * z))) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) t n₂)
    (hn1 : ∀ m, ¬ ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
      (∀ x y z, R (FreeMagma.of none * x * y * z) (x * z * (y * z))) →
      (∀ u u' v, R u u' → R (u * v) (u' * v)) →
      (∀ u v v', R v v' → R (u * v) (u * v')) →
      R n₁ m)
    (hn2 : ∀ m, ¬ ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
      (∀ x y z, R (FreeMagma.of none * x * y * z) (x * z * (y * z))) →
      (∀ u u' v, R u u' → R (u * v) (u' * v)) →
      (∀ u v v', R v v' → R (u * v) (u * v')) →
      R n₂ m) :
    n₁ = n₂ := by
  obtain ⟨w, hw1, hw2⟩ := ppl004_s_confluence (none : Option α) h1 h2
  exact (rtg_eq_of_normal hw1 hn1).symm.trans (rtg_eq_of_normal hw2 hn2)

/-! ### Section 2: Monotone Leaf-Count Growth & Exact Size-Preserving Characterization -/

private lemma length_pos {α : Type*} (t : FreeMagma α) : 1 ≤ t.length := by
  induction t with
  | ih1 _ => simp [FreeMagma.length]
  | ih2 u v ihu ihv =>
    simp only [FreeMagma.length]
    omega

private lemma length_eq_one_iff {α : Type*} (t : FreeMagma α) :
    t.length = 1 ↔ ∃ a : α, t = FreeMagma.of a := by
  cases t with
  | of a =>
    simp [FreeMagma.length]
  | mul u v =>
    have hu := length_pos u
    have hv := length_pos v
    constructor
    · intro h
      simp only [FreeMagma.length] at h
      omega
    · rintro ⟨a, h⟩
      cases h

private lemma sStep_length_le_internal {α : Type*} {s : α} {a b : FreeMagma α}
    (h : SStep s a b) : a.length ≤ b.length := by
  induction h with
  | redex x y z =>
    have hz := length_pos z
    simp only [FreeMagma.length]
    omega
  | left v _ ih =>
    simp only [FreeMagma.length]
    omega
  | right u _ ih =>
    simp only [FreeMagma.length]
    omega

private lemma sStep_rtg_length_le_internal {α : Type*} {s : α} {a b : FreeMagma α}
    (h : Relation.ReflTransGen (SStep s) a b) : a.length ≤ b.length := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact ih.trans (sStep_length_le_internal hstep)

/-- **Exact Leaf-Count Formula for an `S`-Redex**:
Contracting `S x y z → x z (y z)` increases the leaf count by `z.length - 1 ≥ 0`,
strictly increasing iff `z` is not an atom (`¬ ∃ c, z = FreeMagma.of c`). -/
theorem ppl004_s_redex_length_formula {α : Type*} (s : α) (x y z : FreeMagma α) :
    (x * z * (y * z)).length + 1 = (FreeMagma.of s * x * y * z).length + z.length ∧
    ((FreeMagma.of s * x * y * z).length < (x * z * (y * z)).length ↔
      ∀ c : α, z ≠ FreeMagma.of c) := by
  have hz := length_pos z
  constructor
  · simp only [FreeMagma.length]
    omega
  · constructor
    · intro hlt c hc
      subst hc
      simp only [FreeMagma.length] at hlt
      omega
    · intro hne
      have hgt : 1 < z.length := by
        by_contra hle
        have heq1 : z.length = 1 := by omega
        obtain ⟨c, hc⟩ := (length_eq_one_iff z).1 heq1
        exact hne c hc
      simp only [FreeMagma.length]
      omega

/-- **Single-Step Monotone Leaf-Count Growth (`|a| ≤ |b|`)**. -/
theorem ppl004_s_step_length_le {α : Type*} (s : α) {a b : FreeMagma α}
    (h : ∀ (R : FreeMagma α → FreeMagma α → Prop),
      (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
      (∀ u u' v, R u u' → R (u * v) (u' * v)) →
      (∀ u v v', R v v' → R (u * v) (u * v')) →
      R a b) :
    a.length ≤ b.length :=
  sStep_length_le_internal ((sStep_iff_least s a b).2 h)

/-- **Multi-Step Monotone Leaf-Count Growth (`|a| ≤ |b|`)**. -/
theorem ppl004_s_multistep_length_le {α : Type*} (s : α) {a b : FreeMagma α}
    (h : Relation.ReflTransGen
      (fun u v : FreeMagma α =>
        ∀ (R : FreeMagma α → FreeMagma α → Prop),
          (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
          (∀ p p' q, R p p' → R (p * q) (p' * q)) →
          (∀ p q q', R q q' → R (p * q) (p * q')) →
          R u v) a b) :
    a.length ≤ b.length :=
  sStep_rtg_length_le_internal ((rtg_iff_of_rel_iff (sStep_iff_least s) a b).2 h)

/-- **Exact Size-Preserving Characterization for Closed Pure `S`-Terms**:
A single `S`-reduction step `a → b` on `FreeMagma Unit` preserves leaf count (`a.length = b.length`)
if and only if it contracts a redex whose third argument is `S = FreeMagma.of ()`
(i.e. `S x y S → x S (y S)` inside some context). Consequently, constant-size loops can only
reduce `z = S` redexes. -/
theorem ppl004_closed_s_step_length_eq_iff {a b : FreeMagma Unit} :
    ((∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
        (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
        (∀ u u' v, R u u' → R (u * v) (u' * v)) →
        (∀ u v v', R v v' → R (u * v) (u * v')) →
        R a b) ∧ a.length = b.length) ↔
    (∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
      (∀ x y, R (FreeMagma.of () * x * y * FreeMagma.of ())
                (x * FreeMagma.of () * (y * FreeMagma.of ()))) →
      (∀ u u' v, R u u' → R (u * v) (u' * v)) →
      (∀ u v v', R v v' → R (u * v) (u * v')) →
      R a b) := by
  constructor
  · rintro ⟨hstep, hlen⟩
    have hs := (sStep_iff_least () a b).2 hstep
    clear hstep
    intro R hred hL hR
    induction hs with
    | redex x y z =>
      have hz1 : z.length = 1 := by
        simp only [FreeMagma.length] at hlen
        omega
      obtain ⟨u, rfl⟩ := (length_eq_one_iff z).1 hz1
      cases u
      exact hred x y
    | left v _ ih =>
      simp only [FreeMagma.length] at hlen
      exact hL _ _ v (ih (by omega))
    | right u _ ih =>
      simp only [FreeMagma.length] at hlen
      exact hR u _ _ (ih (by omega))
  · intro h
    have hpair : SStep () a b ∧ a.length = b.length := by
      refine h (fun u v => SStep () u v ∧ u.length = v.length) ?_ ?_ ?_
      · intro x y
        refine ⟨SStep.redex x y (FreeMagma.of ()), ?_⟩
        simp only [FreeMagma.length]
        omega
      · rintro u u' v ⟨hu, hlu⟩
        exact ⟨SStep.left v hu, by simp only [FreeMagma.length]; omega⟩
      · rintro u v v' ⟨hv, hlv⟩
        exact ⟨SStep.right u hv, by simp only [FreeMagma.length]; omega⟩
    exact ⟨(sStep_iff_least () a b).1 hpair.1, hpair.2⟩

private lemma sStep_length_ge_four {α : Type*} {s : α} {t t' : FreeMagma α}
    (hs : SStep s t t') : 4 ≤ t.length := by
  induction hs with
  | redex x y z =>
    have hx := length_pos x
    have hy := length_pos y
    have hz := length_pos z
    simp only [FreeMagma.length]
    omega
  | left v _ ih =>
    have hv := length_pos v
    simp only [FreeMagma.length]
    omega
  | right u _ ih =>
    have hu := length_pos u
    simp only [FreeMagma.length]
    omega

/-- **Small Pure `S`-Terms (`|t| ≤ 3`) Are Normal Forms**:
Every `S`-redex `S x y z` has leaf count `≥ 4`, so no term of leaf count `≤ 3` can step. -/
theorem ppl004_s_small_terms_normal {α : Type*} (s : α) {t : FreeMagma α}
    (ht : t.length ≤ 3) (t' : FreeMagma α) :
    ¬ ∀ (R : FreeMagma α → FreeMagma α → Prop),
      (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
      (∀ u u' v, R u u' → R (u * v) (u' * v)) →
      (∀ u v v', R v v' → R (u * v) (u * v')) →
      R t t' := by
  intro h
  have hge := sStep_length_ge_four ((sStep_iff_least s t t').2 h)
  omega

/-! ### Section 3: No-Deletion Invariant & Impossibility of `K` in Pure `S` -/

private lemma sStep_varCount_le {α : Type*} [DecidableEq α] (v : α)
    {a b : FreeMagma (Option α)} (h : SStep (none : Option α) a b) :
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) a) ≤
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) b) := by
  induction h with
  | redex x y z =>
    simp only [map_mul, toAdd_mul, FreeMagma.lift_of, toAdd_ofAdd, reduceCtorEq, ↓reduceIte]
    omega
  | left w _ ih =>
    simp only [map_mul, toAdd_mul]
    omega
  | right u _ ih =>
    simp only [map_mul, toAdd_mul]
    omega

private lemma sStep_varCount_zero {α : Type*} [DecidableEq α] (v : α)
    {a b : FreeMagma (Option α)} (h : SStep (none : Option α) a b) :
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) a) = 0 →
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) b) = 0 := by
  induction h with
  | redex x y z =>
    intro h0
    simp only [map_mul, toAdd_mul, FreeMagma.lift_of, toAdd_ofAdd, reduceCtorEq, ↓reduceIte] at h0 ⊢
    omega
  | @left u u' w _ ih =>
    intro h0
    simp only [map_mul, toAdd_mul] at h0 ⊢
    have h1 : Multiplicative.toAdd
        (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) u) = 0 := by
      omega
    have h2 := ih h1
    omega
  | @right u w w' _ ih =>
    intro h0
    simp only [map_mul, toAdd_mul] at h0 ⊢
    have h1 : Multiplicative.toAdd
        (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) w) = 0 := by
      omega
    have h2 := ih h1
    omega

private lemma varCount_map_none {α : Type*} [DecidableEq α] (v : α) (e : FreeMagma Unit) :
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0))
        (FreeMagma.map (fun _ => (none : Option α)) e)) = 0 := by
  induction e with
  | ih1 _ =>
    simp
  | ih2 u w ihu ihw =>
    simp [map_mul, ihu, ihw]

/-- **No-Deletion Invariant (Monotone Variable Multiplicity)**:
Every free variable's occurrence count in an open pure `S`-term is monotonically non-decreasing
along every `S`-reduction sequence. In particular, no free variable can ever be erased. -/
theorem ppl004_s_var_count_nondecreasing {α : Type*} [DecidableEq α] (v : α)
    {t t' : FreeMagma (Option α)}
    (h : Relation.ReflTransGen
      (fun a b : FreeMagma (Option α) =>
        ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
          (∀ x y z, R (FreeMagma.of none * x * y * z) (x * z * (y * z))) →
          (∀ u u' w, R u u' → R (u * w) (u' * w)) →
          (∀ u w w', R w w' → R (u * w) (u * w')) →
          R a b) t t') :
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) t) ≤
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) t') := by
  have h' := (rtg_iff_of_rel_iff (sStep_iff_least (none : Option α)) t t').2 h
  clear h
  induction h' with
  | refl => exact le_refl _
  | tail _ hstep ih => exact ih.trans (sStep_varCount_le v hstep)

/-- **Non-Creation Invariant (Variable Absence Preserved)**:
If variable `v` does not occur in `t`, it cannot occur in any reduct `t'` of `t`. -/
theorem ppl004_s_var_absence_preserved {α : Type*} [DecidableEq α] (v : α)
    {t t' : FreeMagma (Option α)}
    (h : Relation.ReflTransGen
      (fun a b : FreeMagma (Option α) =>
        ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
          (∀ x y z, R (FreeMagma.of none * x * y * z) (x * z * (y * z))) →
          (∀ u u' w, R u u' → R (u * w) (u' * w)) →
          (∀ u w w', R w w' → R (u * w) (u * w')) →
          R a b) t t')
    (h0 : Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) t) = 0) :
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Option α => Multiplicative.ofAdd (if x = some v then (1 : ℕ) else 0)) t') = 0 := by
  have h' := (rtg_iff_of_rel_iff (sStep_iff_least (none : Option α)) t t').2 h
  clear h
  induction h' with
  | refl => exact h0
  | tail _ hstep ih => exact sStep_varCount_zero v hstep ih

/-- **Impossibility of `K` in Pure `S` (Reduction Form)**:
No closed pure `S`-term `e : FreeMagma Unit` satisfies `e * x * y →* x` for distinct variables `x ≠ y`. -/
theorem ppl004_s_no_k_combinator {α : Type*} (e : FreeMagma Unit) {x y : α} (hxy : x ≠ y) :
    ¬ Relation.ReflTransGen
      (fun a b : FreeMagma (Option α) =>
        ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
          (∀ p q r, R (FreeMagma.of none * p * q * r) (p * r * (q * r))) →
          (∀ u u' w, R u u' → R (u * w) (u' * w)) →
          (∀ u w w', R w w' → R (u * w) (u * w')) →
          R a b)
      (FreeMagma.map (fun _ => (none : Option α)) e * FreeMagma.of (some x) * FreeMagma.of (some y))
      (FreeMagma.of (some x)) := by
  classical
  intro hred
  have hle := ppl004_s_var_count_nondecreasing y hred
  simp only [map_mul, toAdd_mul, FreeMagma.lift_of, toAdd_ofAdd, varCount_map_none] at hle
  have hne : (some x : Option α) ≠ some y := fun h => hxy (Option.some.inj h)
  simp [hne] at hle

/-- **Impossibility of `K` in Pure `S` (Full Convertibility Form)**:
Combining Confluence (Church–Rosser) with the No-Deletion Invariant, no closed pure `S`-term `e`
even satisfies `e * x * y ↔* x` (under `Relation.EqvGen`) for distinct variables `x ≠ y`. -/
theorem ppl004_s_no_k_combinator_eqv {α : Type*} (e : FreeMagma Unit) {x y : α} (hxy : x ≠ y) :
    ¬ Relation.EqvGen
      (fun a b : FreeMagma (Option α) =>
        ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
          (∀ p q r, R (FreeMagma.of none * p * q * r) (p * r * (q * r))) →
          (∀ u u' w, R u u' → R (u * w) (u' * w)) →
          (∀ u w w', R w w' → R (u * w) (u * w')) →
          R a b)
      (FreeMagma.map (fun _ => (none : Option α)) e * FreeMagma.of (some x) * FreeMagma.of (some y))
      (FreeMagma.of (some x)) := by
  intro heqv
  obtain ⟨w, hw1, hw2⟩ := ppl004_s_church_rosser (none : Option α) heqv
  have hnf : ∀ m, ¬ ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
      (∀ p q r, R (FreeMagma.of none * p * q * r) (p * r * (q * r))) →
      (∀ u u' v, R u u' → R (u * v) (u' * v)) →
      (∀ u v v', R v v' → R (u * v) (u * v')) →
      R (FreeMagma.of (some x)) m := by
    intro m hm
    exact ppl004_s_small_terms_normal (none : Option α) (by simp [FreeMagma.length]) m hm
  have hw : w = FreeMagma.of (some x) := rtg_eq_of_normal hw2 hnf
  subst hw
  exact ppl004_s_no_k_combinator e hxy hw1

/-- **No Closed Pure `S`-Term Is Constant Modulo `S`-Conversion**:
For every closed pure `S`-term `e` and distinct variables `x ≠ y`, `e * x` and `e * y` are
never `S`-convertible (`Relation.EqvGen`), because every reduct of `e * x` contains `x` while
no reduct of `e * y` can ever contain `x`. -/
theorem ppl004_s_no_constant_combinator {α : Type*} (e : FreeMagma Unit) {x y : α} (hxy : x ≠ y) :
    ¬ Relation.EqvGen
      (fun a b : FreeMagma (Option α) =>
        ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
          (∀ p q r, R (FreeMagma.of none * p * q * r) (p * r * (q * r))) →
          (∀ u u' w, R u u' → R (u * w) (u' * w)) →
          (∀ u w w', R w w' → R (u * w) (u * w')) →
          R a b)
      (FreeMagma.map (fun _ => (none : Option α)) e * FreeMagma.of (some x))
      (FreeMagma.map (fun _ => (none : Option α)) e * FreeMagma.of (some y)) := by
  classical
  intro heqv
  obtain ⟨w, hw1, hw2⟩ := ppl004_s_church_rosser (none : Option α) heqv
  have hge := ppl004_s_var_count_nondecreasing x hw1
  have hzero : Multiplicative.toAdd
      (FreeMagma.lift (fun o : Option α => Multiplicative.ofAdd (if o = some x then (1 : ℕ) else 0))
        (FreeMagma.map (fun _ => (none : Option α)) e * FreeMagma.of (some y))) = 0 := by
    have hne : (some y : Option α) ≠ some x := fun h => hxy (Option.some.inj h).symm
    simp [map_mul, varCount_map_none, hne]
  have hw0 := ppl004_s_var_absence_preserved x hw2 hzero
  rw [hw0] at hge
  simp [map_mul, varCount_map_none] at hge

private lemma length_map {α β : Type*} (f : α → β) (t : FreeMagma α) :
    (FreeMagma.map f t).length = t.length := by
  induction t with
  | ih1 _ => simp [FreeMagma.length]
  | ih2 a b iha ihb => simp [map_mul, FreeMagma.length, iha, ihb]

/-- **Impossibility of Standard Combinators `I, B, C, W, M` in Pure `S` (Full Convertibility Form)**:
Combining Church–Rosser with Monotone Leaf-Count Growth (`|t'| ≥ |t|`) and small-term normality
(`|t| ≤ 3`), NO closed pure `S`-term `e : FreeMagma Unit` can represent `I` (`e x ↔* x`),
`B` (`e x y z ↔* x (y z)`), `C` (`e x y z ↔* x z y`), `W` (`e x y ↔* x y y`), or
`M` (`e x ↔* x x`), in sharp contrast with `ppl004_sk_standard_combinators` in `SK`. -/
theorem ppl004_s_no_I_B_C_W_M_combinators {α : Type*} (e : FreeMagma Unit) (x y z : α) :
    let step : FreeMagma (Option α) → FreeMagma (Option α) → Prop := fun a b =>
      ∀ (R : FreeMagma (Option α) → FreeMagma (Option α) → Prop),
        (∀ p q r, R (FreeMagma.of none * p * q * r) (p * r * (q * r))) →
        (∀ u u' w, R u u' → R (u * w) (u' * w)) →
        (∀ u w w', R w w' → R (u * w) (u * w')) →
        R a b
    let e' := FreeMagma.map (fun _ => (none : Option α)) e
    let vx := FreeMagma.of (some x)
    let vy := FreeMagma.of (some y)
    let vz := FreeMagma.of (some z)
    (¬ Relation.EqvGen step (e' * vx) vx) ∧
    (¬ Relation.EqvGen step (e' * vx * vy * vz) (vx * (vy * vz))) ∧
    (¬ Relation.EqvGen step (e' * vx * vy * vz) (vx * vz * vy)) ∧
    (¬ Relation.EqvGen step (e' * vx * vy) (vx * vy * vy)) ∧
    (¬ Relation.EqvGen step (e' * vx) (vx * vx)) := by
  intro step e' vx vy vz
  have hepos : 1 ≤ e'.length := length_pos e'
  have hnf_le3 : ∀ {u : FreeMagma (Option α)}, u.length ≤ 3 → ∀ m, ¬ step u m :=
    fun hu m hm => ppl004_s_small_terms_normal (none : Option α) hu m hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro heqv
    obtain ⟨w, hw1, hw2⟩ := ppl004_s_church_rosser (none : Option α) heqv
    have hw := rtg_eq_of_normal hw2 (hnf_le3 (by simp [vx, FreeMagma.length]))
    subst hw
    have hle := ppl004_s_multistep_length_le (none : Option α) hw1
    simp only [vx, FreeMagma.length] at hle
    omega
  · intro heqv
    obtain ⟨w, hw1, hw2⟩ := ppl004_s_church_rosser (none : Option α) heqv
    have hw := rtg_eq_of_normal hw2 (hnf_le3 (by simp [vx, vy, vz, FreeMagma.length]))
    subst hw
    have hle := ppl004_s_multistep_length_le (none : Option α) hw1
    simp only [vx, vy, vz, FreeMagma.length] at hle
    omega
  · intro heqv
    obtain ⟨w, hw1, hw2⟩ := ppl004_s_church_rosser (none : Option α) heqv
    have hw := rtg_eq_of_normal hw2 (hnf_le3 (by simp [vx, vy, vz, FreeMagma.length]))
    subst hw
    have hle := ppl004_s_multistep_length_le (none : Option α) hw1
    simp only [vx, vy, vz, FreeMagma.length] at hle
    omega
  · intro heqv
    obtain ⟨w, hw1, hw2⟩ := ppl004_s_church_rosser (none : Option α) heqv
    have hw := rtg_eq_of_normal hw2 (hnf_le3 (by simp [vx, vy, FreeMagma.length]))
    subst hw
    have hle := ppl004_s_multistep_length_le (none : Option α) hw1
    have he1 : e'.length = 1 := by
      simp only [vx, vy, FreeMagma.length] at hle
      omega
    have hnfL : ∀ m, ¬ step (e' * vx * vy) m :=
      hnf_le3 (by simp only [vx, vy, FreeMagma.length]; omega)
    have heq := rtg_eq_of_normal hw1 hnfL
    obtain ⟨c, hc⟩ := (length_eq_one_iff e).1 (by rw [← length_map (fun _ => (none : Option α)) e]; exact he1)
    subst hc
    simp only [e', vx, vy, FreeMagma.map_of] at heq
    cases heq
  · intro heqv
    obtain ⟨w, hw1, hw2⟩ := ppl004_s_church_rosser (none : Option α) heqv
    have hw := rtg_eq_of_normal hw2 (hnf_le3 (by simp [vx, FreeMagma.length]))
    subst hw
    have hle := ppl004_s_multistep_length_le (none : Option α) hw1
    have he1 : e'.length = 1 := by
      simp only [vx, FreeMagma.length] at hle
      omega
    have hnfL : ∀ m, ¬ step (e' * vx) m :=
      hnf_le3 (by simp only [vx, FreeMagma.length]; omega)
    have heq := rtg_eq_of_normal hw1 hnfL
    obtain ⟨c, hc⟩ := (length_eq_one_iff e).1 (by rw [← length_map (fun _ => (none : Option α)) e]; exact he1)
    subst hc
    simp only [e', vx, FreeMagma.map_of] at heq
    cases heq

/-! ### Section 4: Minimal Non-Terminating Pure `S`-Terms (Waldmann Counterexamples) -/

private inductive Subterm {α : Type*} : FreeMagma α → FreeMagma α → Prop
  | refl (t : FreeMagma α) : Subterm t t
  | left {u v t : FreeMagma α} : Subterm u t → Subterm (u * v) t
  | right {u v t : FreeMagma α} : Subterm v t → Subterm (u * v) t

private lemma subterm_length_le {α : Type*} {u t : FreeMagma α} (h : Subterm u t) :
    t.length ≤ u.length := by
  induction h with
  | refl _ => exact le_refl _
  | left _ ih =>
    simp only [FreeMagma.length]
    omega
  | right _ ih =>
    simp only [FreeMagma.length]
    omega

private lemma subterm_replace_rtg {α : Type*} {s : α} {u t t' : FreeMagma α}
    (hsub : Subterm u t) (hred : Relation.ReflTransGen (SStep s) t t') :
    ∃ u', Relation.ReflTransGen (SStep s) u u' ∧ Subterm u' t' ∧
      u.length + t'.length = u'.length + t.length := by
  induction hsub with
  | refl _ =>
    exact ⟨t', hred, Subterm.refl t', by omega⟩
  | @left a b _ _ ih =>
    obtain ⟨a', ha', hsub', hlen⟩ := ih hred
    refine ⟨a' * b, sStep_rtg_left b ha', Subterm.left hsub', ?_⟩
    simp only [FreeMagma.length]
    omega
  | @right a b _ _ ih =>
    obtain ⟨b', hb', hsub', hlen⟩ := ih hred
    refine ⟨a * b', sStep_rtg_right a hb', Subterm.right hsub', ?_⟩
    simp only [FreeMagma.length]
    omega

private lemma subterm_trans {α : Type*} {a b c : FreeMagma α}
    (h1 : Subterm a b) (h2 : Subterm b c) : Subterm a c := by
  induction h1 with
  | refl _ => exact h2
  | left _ ih => exact Subterm.left (ih h2)
  | right _ ih => exact Subterm.right (ih h2)

/-- General criterion: if a closed `S`-term `t` admits reducts of arbitrarily large leaf count,
then `t` has NO normal form (every reduct `u` of `t` can step further). -/
private lemma no_nf_of_unbounded_length {t : FreeMagma Unit}
    (hunb : ∀ N : ℕ, ∃ w, Relation.ReflTransGen (SStep ()) t w ∧ N ≤ w.length) :
    ∀ u, Relation.ReflTransGen (SStep ()) t u → ∃ v, SStep () u v := by
  intro u hu
  by_contra hnf
  push Not at hnf
  obtain ⟨w, hw, hlen⟩ := hunb (u.length + 1)
  obtain ⟨z, hzw, hzu⟩ := sStep_confluent () hw hu
  have hz : z = u := rtg_eq_of_normal hzu hnf
  subst hz
  have hle := sStep_rtg_length_le_internal hzw
  omega

/-! #### Part 4A: Size-7 Minimal Non-Terminating Terms (`S S S (S S) S S` & `S (S S) S S S S`) -/

private def S₀ : FreeMagma Unit := FreeMagma.of ()

private def waldA : FreeMagma Unit := S₀ * (S₀ * (S₀ * S₀) * S₀) * S₀
private def waldB : FreeMagma Unit := S₀ * (S₀ * S₀) * waldA

private inductive WaldGood : FreeMagma Unit → Prop
  | base : WaldGood waldB
  | appS {X : FreeMagma Unit} : WaldGood X → WaldGood (S₀ * X)
  | mul {X Y : FreeMagma Unit} : WaldGood X → WaldGood Y → WaldGood (X * Y)

private lemma waldGood_length_ge_two {X : FreeMagma Unit} (h : WaldGood X) :
    2 ≤ X.length := by
  cases h with
  | base => simp [waldB, waldA, S₀, FreeMagma.length]
  | @appS X' _ =>
    have := length_pos X'
    simp only [S₀, FreeMagma.length]
    omega
  | @mul X₁ X₂ _ _ =>
    have := length_pos X₁
    have := length_pos X₂
    simp only [FreeMagma.length]
    omega

private lemma waldA_step (X : FreeMagma Unit) :
    Relation.ReflTransGen (SStep ()) (waldA * X)
      ((S₀ * X) * (S₀ * X) * (X * (S₀ * X) * (S₀ * X))) := by
  have h1 : SStep () (waldA * X) ((S₀ * (S₀ * S₀) * S₀ * X) * (S₀ * X)) :=
    SStep.redex (S₀ * (S₀ * S₀) * S₀) S₀ X
  have h2 : SStep () ((S₀ * (S₀ * S₀) * S₀ * X) * (S₀ * X))
      ((S₀ * S₀ * X * (S₀ * X)) * (S₀ * X)) :=
    SStep.left (S₀ * X) (SStep.redex (S₀ * S₀) S₀ X)
  have h3 : SStep () ((S₀ * S₀ * X * (S₀ * X)) * (S₀ * X))
      ((S₀ * (S₀ * X) * (X * (S₀ * X))) * (S₀ * X)) :=
    SStep.left (S₀ * X) (SStep.redex S₀ X (S₀ * X))
  have h4 : SStep () ((S₀ * (S₀ * X) * (X * (S₀ * X))) * (S₀ * X))
      ((S₀ * X) * (S₀ * X) * (X * (S₀ * X) * (S₀ * X))) :=
    SStep.redex (S₀ * X) (X * (S₀ * X)) (S₀ * X)
  exact (Relation.ReflTransGen.single h1).tail h2 |>.tail h3 |>.tail h4

private lemma waldB_step (U V : FreeMagma Unit) :
    Relation.ReflTransGen (SStep ()) (waldB * U * V)
      ((waldA * U * V) * (U * (waldA * U) * V)) := by
  have h1 : SStep () (waldB * U * V) ((S₀ * S₀ * U * (waldA * U)) * V) :=
    SStep.left V (SStep.redex (S₀ * S₀) waldA U)
  have h2 : SStep () ((S₀ * S₀ * U * (waldA * U)) * V)
      ((S₀ * (waldA * U) * (U * (waldA * U))) * V) :=
    SStep.left V (SStep.redex S₀ U (waldA * U))
  have h3 : SStep () ((S₀ * (waldA * U) * (U * (waldA * U))) * V)
      ((waldA * U * V) * (U * (waldA * U) * V)) :=
    SStep.redex (waldA * U) (U * (waldA * U)) V
  exact (Relation.ReflTransGen.single h1).tail h2 |>.tail h3

private lemma waldGood_app2 {X U V : FreeMagma Unit}
    (hX : WaldGood X) (hU : WaldGood U) (hV : WaldGood V) :
    ∃ W Z, Relation.ReflTransGen (SStep ()) (X * U * V) W ∧
      Subterm W (waldA * Z) ∧ WaldGood Z := by
  induction hX generalizing U V with
  | base =>
    refine ⟨(waldA * U * V) * (U * (waldA * U) * V), U, waldB_step U V, ?_, hU⟩
    exact Subterm.left (Subterm.left (Subterm.refl _))
  | @appS X' hX' ih =>
    have h1 : SStep () (S₀ * X' * U * V) (X' * V * (U * V)) :=
      SStep.redex X' U V
    obtain ⟨W, Z, hred, hsub, hZ⟩ := ih hV (WaldGood.mul hU hV)
    exact ⟨W, Z, Relation.ReflTransGen.head h1 hred, hsub, hZ⟩
  | @mul X₁ X₂ hX₁ hX₂ ih1 _ =>
    obtain ⟨W₁, Z, hred, hsub, hZ⟩ := ih1 hX₂ hU
    exact ⟨W₁ * V, Z, sStep_rtg_left V hred, Subterm.left hsub, hZ⟩

private lemma waldA_next {X : FreeMagma Unit} (hX : WaldGood X) :
    ∃ W Z, Relation.ReflTransGen (SStep ()) (waldA * X) W ∧
      Subterm W (waldA * Z) ∧ WaldGood Z ∧ (waldA * X).length + 1 ≤ W.length := by
  obtain ⟨W₀, Z, hred0, hsub0, hZ⟩ :=
    waldGood_app2 hX (WaldGood.appS hX) (WaldGood.appS hX)
  have hred1 := waldA_step X
  have hred2 : Relation.ReflTransGen (SStep ())
      ((S₀ * X) * (S₀ * X) * (X * (S₀ * X) * (S₀ * X)))
      ((S₀ * X) * (S₀ * X) * W₀) :=
    sStep_rtg_right ((S₀ * X) * (S₀ * X)) hred0
  have hred := hred1.trans hred2
  have hle_w0 := sStep_rtg_length_le_internal hred0
  have hge2 := waldGood_length_ge_two hX
  have hlen : (waldA * X).length + 1 ≤ ((S₀ * X) * (S₀ * X) * W₀).length := by
    simp only [waldA, S₀, FreeMagma.length] at hle_w0 ⊢
    omega
  exact ⟨(S₀ * X) * (S₀ * X) * W₀, Z, hred, Subterm.right hsub0, hZ, hlen⟩

private lemma waldA_unbounded :
    ∀ n : ℕ, ∃ W Z, Relation.ReflTransGen (SStep ()) (waldA * waldB) W ∧
      Subterm W (waldA * Z) ∧ WaldGood Z ∧ n ≤ W.length := by
  intro n
  induction n with
  | zero =>
    exact ⟨waldA * waldB, waldB, Relation.ReflTransGen.refl, Subterm.refl _, WaldGood.base, by omega⟩
  | succ k ih =>
    obtain ⟨W, Z, hred, hsub, hZ, hlen⟩ := ih
    obtain ⟨W₁, Z', hred1, hsub1, hZ', hlen1⟩ := waldA_next hZ
    obtain ⟨W', hredW, hsubW, hlenW⟩ := subterm_replace_rtg hsub hred1
    refine ⟨W', Z', hred.trans hredW, subterm_trans hsubW hsub1, hZ', ?_⟩
    omega

private lemma wald7_to_waldA_waldB :
    Relation.ReflTransGen (SStep ())
      (S₀ * S₀ * S₀ * (S₀ * S₀) * S₀ * S₀)
      (S₀ * waldB * (waldA * waldB)) := by
  have h1 : SStep () (S₀ * S₀ * S₀ * (S₀ * S₀) * S₀ * S₀)
      (S₀ * (S₀ * S₀) * (S₀ * (S₀ * S₀)) * S₀ * S₀) :=
    SStep.left S₀ (SStep.left S₀ (SStep.redex S₀ S₀ (S₀ * S₀)))
  have h2 : SStep () (S₀ * (S₀ * S₀) * (S₀ * (S₀ * S₀)) * S₀ * S₀)
      (S₀ * S₀ * S₀ * (S₀ * (S₀ * S₀) * S₀) * S₀) :=
    SStep.left S₀ (SStep.redex (S₀ * S₀) (S₀ * (S₀ * S₀)) S₀)
  have h3 : SStep () (S₀ * S₀ * S₀ * (S₀ * (S₀ * S₀) * S₀) * S₀)
      (S₀ * (S₀ * (S₀ * S₀) * S₀) * (S₀ * (S₀ * (S₀ * S₀) * S₀)) * S₀) :=
    SStep.left S₀ (SStep.redex S₀ S₀ (S₀ * (S₀ * S₀) * S₀))
  have h4 : SStep () (S₀ * (S₀ * (S₀ * S₀) * S₀) * (S₀ * (S₀ * (S₀ * S₀) * S₀)) * S₀)
      (S₀ * (S₀ * S₀) * S₀ * S₀ * waldA) :=
    SStep.redex (S₀ * (S₀ * S₀) * S₀) (S₀ * (S₀ * (S₀ * S₀) * S₀)) S₀
  have h5 : SStep () (S₀ * (S₀ * S₀) * S₀ * S₀ * waldA)
      (S₀ * S₀ * S₀ * (S₀ * S₀) * waldA) :=
    SStep.left waldA (SStep.redex (S₀ * S₀) S₀ S₀)
  have h6 : SStep () (S₀ * S₀ * S₀ * (S₀ * S₀) * waldA)
      (S₀ * (S₀ * S₀) * (S₀ * (S₀ * S₀)) * waldA) :=
    SStep.left waldA (SStep.redex S₀ S₀ (S₀ * S₀))
  have h7 : SStep () (S₀ * (S₀ * S₀) * (S₀ * (S₀ * S₀)) * waldA)
      (S₀ * S₀ * waldA * waldB) :=
    SStep.redex (S₀ * S₀) (S₀ * (S₀ * S₀)) waldA
  have h8 : SStep () (S₀ * S₀ * waldA * waldB)
      (S₀ * waldB * (waldA * waldB)) :=
    SStep.redex S₀ waldA waldB
  exact (((((((Relation.ReflTransGen.single h1).tail h2).tail h3).tail h4).tail h5).tail h6).tail h7).tail h8

/-- **Minimal Size-7 Non-Terminating Pure `S`-Term (`S S S (S S) S S`)**:
This closed pure `S`-term of leaf count `7` (Waldmann 2000 minimal non-normalizing size)
has reducts of arbitrarily large leaf count and **NO normal form** (every reduct steps further),
proving unconditionally that pure `S` is neither strongly nor weakly normalizing. -/
theorem ppl004_waldmann_size7_no_normal_form :
    let S := FreeMagma.of ()
    let w7 := S * S * S * (S * S) * S * S
    w7.length = 7 ∧
    (∀ N : ℕ, ∃ u : FreeMagma Unit,
      Relation.ReflTransGen
        (fun a b : FreeMagma Unit =>
          ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
            (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
            (∀ p p' q, R p p' → R (p * q) (p' * q)) →
            (∀ p q q', R q q' → R (p * q) (p * q')) →
            R a b) w7 u ∧ N ≤ u.length) ∧
    (∀ u : FreeMagma Unit,
      Relation.ReflTransGen
        (fun a b : FreeMagma Unit =>
          ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
            (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
            (∀ p p' q, R p p' → R (p * q) (p' * q)) →
            (∀ p q q', R q q' → R (p * q) (p * q')) →
            R a b) w7 u →
      ∃ v : FreeMagma Unit,
        ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
          (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
          (∀ p p' q, R p p' → R (p * q) (p' * q)) →
          (∀ p q q', R q q' → R (p * q) (p * q')) →
          R u v) := by
  have hunb : ∀ N : ℕ, ∃ u, Relation.ReflTransGen (SStep ())
      (S₀ * S₀ * S₀ * (S₀ * S₀) * S₀ * S₀) u ∧ N ≤ u.length := by
    intro N
    obtain ⟨W, _, hred, _, _, hlen⟩ := waldA_unbounded N
    refine ⟨S₀ * waldB * W, wald7_to_waldA_waldB.trans (sStep_rtg_right (S₀ * waldB) hred), ?_⟩
    simp only [FreeMagma.length]
    omega
  have hiff := sStep_iff_least ()
  refine ⟨by simp [FreeMagma.length], ?_, ?_⟩
  · intro N
    obtain ⟨u, hu, hlen⟩ := hunb N
    exact ⟨u, (rtg_iff_of_rel_iff hiff _ u).1 hu, hlen⟩
  · intro u hu
    obtain ⟨v, hv⟩ := no_nf_of_unbounded_length hunb u ((rtg_iff_of_rel_iff hiff _ u).2 hu)
    exact ⟨v, (hiff u v).1 hv⟩

/-- **Second Minimal Size-7 Non-Terminating Pure `S`-Term (`S (S S) S S S S`)**:
Reduces in 1 step to `S S S (S S) S S` and therefore has leaf count `7` and NO normal form. -/
theorem ppl004_waldmann_size7_alt_no_normal_form :
    let S := FreeMagma.of ()
    let w7' := S * (S * S) * S * S * S * S
    w7'.length = 7 ∧
    (∀ u : FreeMagma Unit,
      Relation.ReflTransGen
        (fun a b : FreeMagma Unit =>
          ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
            (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
            (∀ p p' q, R p p' → R (p * q) (p' * q)) →
            (∀ p q q', R q q' → R (p * q) (p * q')) →
            R a b) w7' u →
      ∃ v : FreeMagma Unit,
        ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
          (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
          (∀ p p' q, R p p' → R (p * q) (p' * q)) →
          (∀ p q q', R q q' → R (p * q) (p * q')) →
          R u v) := by
  have h1 : SStep () (S₀ * (S₀ * S₀) * S₀ * S₀ * S₀ * S₀)
      (S₀ * S₀ * S₀ * (S₀ * S₀) * S₀ * S₀) :=
    SStep.left S₀ (SStep.left S₀ (SStep.redex (S₀ * S₀) S₀ S₀))
  have hunb : ∀ N : ℕ, ∃ u, Relation.ReflTransGen (SStep ())
      (S₀ * (S₀ * S₀) * S₀ * S₀ * S₀ * S₀) u ∧ N ≤ u.length := by
    intro N
    obtain ⟨W, _, hred, _, _, hlen⟩ := waldA_unbounded N
    refine ⟨S₀ * waldB * W,
      (Relation.ReflTransGen.head h1 wald7_to_waldA_waldB).trans (sStep_rtg_right (S₀ * waldB) hred), ?_⟩
    simp only [FreeMagma.length]
    omega
  have hiff := sStep_iff_least ()
  refine ⟨by simp [FreeMagma.length], ?_⟩
  intro u hu
  obtain ⟨v, hv⟩ := no_nf_of_unbounded_length hunb u ((rtg_iff_of_rel_iff hiff _ u).2 hu)
  exact ⟨v, (hiff u v).1 hv⟩

/-- **Minimal Size-8 Non-Head-Normalizing Pure `S`-Term (`S S S (S S) S S S`)**:
Has leaf count `8`, unbounded reduct size, and NO normal form. -/
theorem ppl004_waldmann_size8_no_normal_form :
    let S := FreeMagma.of ()
    let w8 := S * S * S * (S * S) * S * S * S
    w8.length = 8 ∧
    (∀ u : FreeMagma Unit,
      Relation.ReflTransGen
        (fun a b : FreeMagma Unit =>
          ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
            (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
            (∀ p p' q, R p p' → R (p * q) (p' * q)) →
            (∀ p q q', R q q' → R (p * q) (p * q')) →
            R a b) w8 u →
      ∃ v : FreeMagma Unit,
        ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
          (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
          (∀ p p' q, R p p' → R (p * q) (p' * q)) →
          (∀ p q q', R q q' → R (p * q) (p * q')) →
          R u v) := by
  have hunb : ∀ N : ℕ, ∃ u, Relation.ReflTransGen (SStep ())
      (S₀ * S₀ * S₀ * (S₀ * S₀) * S₀ * S₀ * S₀) u ∧ N ≤ u.length := by
    intro N
    obtain ⟨W, _, hred, _, _, hlen⟩ := waldA_unbounded N
    refine ⟨S₀ * waldB * W * S₀,
      (sStep_rtg_left S₀ wald7_to_waldA_waldB).trans
        (sStep_rtg_left S₀ (sStep_rtg_right (S₀ * waldB) hred)), ?_⟩
    simp only [FreeMagma.length]
    omega
  have hiff := sStep_iff_least ()
  refine ⟨by simp [FreeMagma.length], ?_⟩
  intro u hu
  obtain ⟨v, hv⟩ := no_nf_of_unbounded_length hunb u ((rtg_iff_of_rel_iff hiff _ u).2 hu)
  exact ⟨v, (hiff u v).1 hv⟩

/-! #### Part 4B: Symmetric Size-10 Self-Application Non-Terminating Term `A * A` -/

private def selfA : FreeMagma Unit := S₀ * (S₀ * S₀) * (S₀ * S₀)

private def selfY : ℕ → FreeMagma Unit
  | 0 => selfA
  | n + 1 => S₀ * S₀ * selfY n

private lemma selfY_length (n : ℕ) : (selfY n).length = 5 + 2 * n := by
  induction n with
  | zero => simp [selfY, selfA, S₀, FreeMagma.length]
  | succ k ih =>
    simp only [selfY, S₀, FreeMagma.length]
    omega

private lemma selfY_app_subterm (k : ℕ) (U : FreeMagma Unit) :
    ∃ W, Relation.ReflTransGen (SStep ()) (selfY k * U) W ∧ Subterm W (selfA * U) := by
  induction k with
  | zero =>
    exact ⟨selfA * U, Relation.ReflTransGen.refl, Subterm.refl _⟩
  | succ m ih =>
    have h1 : SStep () (selfY (m + 1) * U) (S₀ * U * (selfY m * U)) :=
      SStep.redex S₀ (selfY m) U
    obtain ⟨W, hred, hsub⟩ := ih
    exact ⟨S₀ * U * W, Relation.ReflTransGen.head h1 (sStep_rtg_right (S₀ * U) hred),
      Subterm.right hsub⟩

private lemma selfA_selfY_step (n : ℕ) :
    ∃ W, Relation.ReflTransGen (SStep ()) (selfA * selfY n) W ∧
      Subterm W (selfA * selfY (n + 1)) := by
  have h1 : SStep () (selfA * selfY n) (selfY (n + 1) * selfY (n + 1)) :=
    SStep.redex (S₀ * S₀) (S₀ * S₀) (selfY n)
  obtain ⟨W, hred, hsub⟩ := selfY_app_subterm (n + 1) (selfY (n + 1))
  exact ⟨W, Relation.ReflTransGen.head h1 hred, hsub⟩

private lemma selfAA_reaches_selfY (n : ℕ) :
    ∃ W, Relation.ReflTransGen (SStep ()) (selfA * selfA) W ∧
      Subterm W (selfA * selfY n) := by
  induction n with
  | zero =>
    exact ⟨selfA * selfA, Relation.ReflTransGen.refl, Subterm.refl _⟩
  | succ k ih =>
    obtain ⟨W, hred, hsub⟩ := ih
    obtain ⟨W₁, hred1, hsub1⟩ := selfA_selfY_step k
    obtain ⟨W', hredW, hsubW, _⟩ := subterm_replace_rtg hsub hred1
    exact ⟨W', hred.trans hredW, subterm_trans hsubW hsub1⟩

/-- **Symmetric Size-10 Non-Terminating Self-Application Term `A * A`**:
With `A = S (S S) (S S)`, the term `A * A` of leaf count `10` reduces along an infinite
chain containing `A * Y_n` (`Y_0 = A`, `Y_{n+1} = S S Y_n`, `|A * Y_n| = 10 + 2n`) and has
NO normal form. -/
theorem ppl004_self_app_size10_no_normal_form :
    let S := FreeMagma.of ()
    let A := S * (S * S) * (S * S)
    (A * A).length = 10 ∧
    (∀ u : FreeMagma Unit,
      Relation.ReflTransGen
        (fun a b : FreeMagma Unit =>
          ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
            (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
            (∀ p p' q, R p p' → R (p * q) (p' * q)) →
            (∀ p q q', R q q' → R (p * q) (p * q')) →
            R a b) (A * A) u →
      ∃ v : FreeMagma Unit,
        ∀ (R : FreeMagma Unit → FreeMagma Unit → Prop),
          (∀ x y z, R (FreeMagma.of () * x * y * z) (x * z * (y * z))) →
          (∀ p p' q, R p p' → R (p * q) (p' * q)) →
          (∀ p q q', R q q' → R (p * q) (p * q')) →
          R u v) := by
  have hunb : ∀ N : ℕ, ∃ u, Relation.ReflTransGen (SStep ()) (selfA * selfA) u ∧ N ≤ u.length := by
    intro N
    obtain ⟨W, hred, hsub⟩ := selfAA_reaches_selfY N
    have hle := subterm_length_le hsub
    have hlen : (selfA * selfY N).length = 10 + 2 * N := by
      have hy := selfY_length N
      simp only [selfA, S₀, FreeMagma.length] at hy ⊢
      omega
    exact ⟨W, hred, by omega⟩
  have hiff := sStep_iff_least ()
  refine ⟨by simp [FreeMagma.length], ?_⟩
  intro u hu
  obtain ⟨v, hv⟩ := no_nf_of_unbounded_length hunb u ((rtg_iff_of_rel_iff hiff _ u).2 hu)
  exact ⟨v, (hiff u v).1 hv⟩

/-! ### Section 5: `SK`-Combinatory Logic Contrast — Confluence, Bracket Abstraction & Fixed-Point `Θ` -/

private inductive SKStep {α : Type*} (s k : α) : FreeMagma α → FreeMagma α → Prop
  | redexS (x y z : FreeMagma α) :
      SKStep s k (FreeMagma.of s * x * y * z) (x * z * (y * z))
  | redexK (x y : FreeMagma α) :
      SKStep s k (FreeMagma.of k * x * y) x
  | left {u u' : FreeMagma α} (v : FreeMagma α) :
      SKStep s k u u' → SKStep s k (u * v) (u' * v)
  | right (u : FreeMagma α) {v v' : FreeMagma α} :
      SKStep s k v v' → SKStep s k (u * v) (u * v')

private lemma skStep_iff_least {α : Type*} (s k : α) (a b : FreeMagma α) :
    SKStep s k a b ↔
      ∀ (R : FreeMagma α → FreeMagma α → Prop),
        (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
        (∀ x y, R (FreeMagma.of k * x * y) x) →
        (∀ u u' v, R u u' → R (u * v) (u' * v)) →
        (∀ u v v', R v v' → R (u * v) (u * v')) →
        R a b := by
  constructor
  · intro h R hS hK hL hR
    induction h with
    | redexS x y z => exact hS x y z
    | redexK x y => exact hK x y
    | left v _ ih => exact hL _ _ v ih
    | right u _ ih => exact hR u _ _ ih
  · intro h
    exact h (SKStep s k) SKStep.redexS SKStep.redexK
      (fun _ _ v h' => SKStep.left v h') (fun u _ _ h' => SKStep.right u h')

private lemma skStep_rtg_left {α : Type*} {s k : α} {u u' : FreeMagma α} (v : FreeMagma α)
    (h : Relation.ReflTransGen (SKStep s k) u u') :
    Relation.ReflTransGen (SKStep s k) (u * v) (u' * v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (SKStep.left v hstep)

private lemma skStep_rtg_right {α : Type*} {s k : α} (u : FreeMagma α) {v v' : FreeMagma α}
    (h : Relation.ReflTransGen (SKStep s k) v v') :
    Relation.ReflTransGen (SKStep s k) (u * v) (u * v') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (SKStep.right u hstep)

private lemma skStep_rtg_mul {α : Type*} {s k : α} {u u' v v' : FreeMagma α}
    (hu : Relation.ReflTransGen (SKStep s k) u u')
    (hv : Relation.ReflTransGen (SKStep s k) v v') :
    Relation.ReflTransGen (SKStep s k) (u * v) (u' * v') :=
  (skStep_rtg_left v hu).trans (skStep_rtg_right u' hv)

private inductive SKPar {α : Type*} (s k : α) : FreeMagma α → FreeMagma α → Prop
  | refl (t : FreeMagma α) : SKPar s k t t
  | mul {u u' v v' : FreeMagma α} :
      SKPar s k u u' → SKPar s k v v' → SKPar s k (u * v) (u' * v')
  | redexS {x x' y y' z z' : FreeMagma α} :
      SKPar s k x x' → SKPar s k y y' → SKPar s k z z' →
      SKPar s k (FreeMagma.of s * x * y * z) (x' * z' * (y' * z'))
  | redexK {x x' y : FreeMagma α} :
      SKPar s k x x' → SKPar s k (FreeMagma.of k * x * y) x'

private lemma skStep_to_skPar {α : Type*} {s k : α} {a b : FreeMagma α} (h : SKStep s k a b) :
    SKPar s k a b := by
  induction h with
  | redexS x y z => exact SKPar.redexS (SKPar.refl x) (SKPar.refl y) (SKPar.refl z)
  | redexK x y => exact SKPar.redexK (SKPar.refl x)
  | left v _ ih => exact SKPar.mul ih (SKPar.refl v)
  | right u _ ih => exact SKPar.mul (SKPar.refl u) ih

private lemma skPar_to_rtg {α : Type*} {s k : α} {a b : FreeMagma α} (h : SKPar s k a b) :
    Relation.ReflTransGen (SKStep s k) a b := by
  induction h with
  | refl _ => exact Relation.ReflTransGen.refl
  | mul _ _ ihu ihv => exact skStep_rtg_mul ihu ihv
  | redexS _ _ _ ihx ihy ihz =>
    have h1 : Relation.ReflTransGen (SKStep s k)
        (FreeMagma.of s * _ * _ * _) (FreeMagma.of s * _ * _ * _) :=
      skStep_rtg_mul
        (skStep_rtg_mul (skStep_rtg_mul Relation.ReflTransGen.refl ihx) ihy) ihz
    exact h1.tail (SKStep.redexS _ _ _)
  | @redexK x x' y _ ihx =>
    have h1 := skStep_rtg_left y (skStep_rtg_right (FreeMagma.of k) ihx)
    exact h1.tail (SKStep.redexK x' y)

private lemma skPar_of_inv {α : Type*} {s k a : α} {w : FreeMagma α}
    (h : SKPar s k (FreeMagma.of a) w) : w = FreeMagma.of a := by
  cases h with
  | refl => rfl

private lemma skPar_of_mul_inv {α : Type*} {s k a : α} {x w : FreeMagma α}
    (h : SKPar s k (FreeMagma.of a * x) w) :
    ∃ x', w = FreeMagma.of a * x' ∧ SKPar s k x x' := by
  cases h with
  | refl => exact ⟨x, rfl, SKPar.refl x⟩
  | mul hu hv =>
    obtain rfl := skPar_of_inv hu
    exact ⟨_, rfl, hv⟩

private lemma skPar_of_s_mul_mul_inv {α : Type*} {s k : α} (hsk : s ≠ k) {x y w : FreeMagma α}
    (h : SKPar s k (FreeMagma.of s * x * y) w) :
    ∃ x' y', w = FreeMagma.of s * x' * y' ∧ SKPar s k x x' ∧ SKPar s k y y' := by
  cases h with
  | refl => exact ⟨x, y, rfl, SKPar.refl x, SKPar.refl y⟩
  | mul hu hv =>
    obtain ⟨x', rfl, hx⟩ := skPar_of_mul_inv hu
    exact ⟨x', _, rfl, hx, hv⟩
  | redexK _ => exact False.elim (hsk rfl)

private noncomputable def completeDevSK {α : Type*} [DecidableEq α] (s k : α) :
    FreeMagma α → FreeMagma α
  | FreeMagma.of a => FreeMagma.of a
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.of a) x) y =>
      if a = k then
        completeDevSK s k x
      else
        completeDevSK s k (FreeMagma.of a * x) * completeDevSK s k y
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.mul (FreeMagma.of a) x) y) z =>
      if a = s then
        completeDevSK s k x * completeDevSK s k z *
          (completeDevSK s k y * completeDevSK s k z)
      else
        completeDevSK s k (FreeMagma.of a * x * y) * completeDevSK s k z
  | FreeMagma.mul u v => completeDevSK s k u * completeDevSK s k v

private lemma completeDevSK_redexK {α : Type*} [DecidableEq α] (s k : α) (x y : FreeMagma α) :
    completeDevSK s k (FreeMagma.of k * x * y) = completeDevSK s k x := by
  change (if k = k then _ else _) = _
  simp

private lemma completeDevSK_redexS {α : Type*} [DecidableEq α] (s k : α) (x y z : FreeMagma α) :
    completeDevSK s k (FreeMagma.of s * x * y * z) =
      completeDevSK s k x * completeDevSK s k z *
        (completeDevSK s k y * completeDevSK s k z) := by
  change (if s = s then _ else _) = _
  simp

private lemma skPar_completeDevSK_self {α : Type*} [DecidableEq α] (s k : α) :
    ∀ t : FreeMagma α, SKPar s k t (completeDevSK s k t)
  | FreeMagma.of a => SKPar.refl _
  | FreeMagma.mul (FreeMagma.of a) v =>
      SKPar.mul (SKPar.refl _) (skPar_completeDevSK_self s k v)
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.of a) x) y => by
      change SKPar s k _ (if a = k then _ else _)
      split_ifs with ha
      · subst a
        exact SKPar.redexK (skPar_completeDevSK_self s k x)
      · exact SKPar.mul (skPar_completeDevSK_self s k (FreeMagma.of a * x))
          (skPar_completeDevSK_self s k y)
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.mul (FreeMagma.of a) x) y) z => by
      change SKPar s k _ (if a = s then _ else _)
      split_ifs with ha
      · subst a
        exact SKPar.redexS (skPar_completeDevSK_self s k x) (skPar_completeDevSK_self s k y)
          (skPar_completeDevSK_self s k z)
      · exact SKPar.mul (skPar_completeDevSK_self s k (FreeMagma.of a * x * y))
          (skPar_completeDevSK_self s k z)
  | FreeMagma.mul (FreeMagma.mul (FreeMagma.mul (FreeMagma.mul a b) c) d) v =>
      SKPar.mul (skPar_completeDevSK_self s k (a * b * c * d)) (skPar_completeDevSK_self s k v)

private lemma skPar_triangle {α : Type*} [DecidableEq α] {s k : α} (hsk : s ≠ k) :
    ∀ {t u : FreeMagma α}, SKPar s k t u → SKPar s k u (completeDevSK s k t) := by
  intro t u h
  induction h with
  | refl t => exact skPar_completeDevSK_self s k t
  | redexS hx hy hz ihx ihy ihz =>
    rw [completeDevSK_redexS]
    exact SKPar.mul (SKPar.mul ihx ihz) (SKPar.mul ihy ihz)
  | redexK hx ihx =>
    rw [completeDevSK_redexK]
    exact ihx
  | @mul u u' v v' hu hv ihu ihv =>
    cases u with
    | of a =>
      exact SKPar.mul ihu ihv
    | mul u1 u2 =>
      cases u1 with
      | of a =>
        change SKPar s k (u' * v') (if a = k then _ else _)
        split_ifs with ha
        · subst a
          obtain ⟨x', rfl, _⟩ := skPar_of_mul_inv hu
          have ihu' : SKPar s k (FreeMagma.of k * x')
              (FreeMagma.of k * completeDevSK s k u2) := ihu
          obtain ⟨x'', heq, ihx⟩ := skPar_of_mul_inv ihu'
          cases heq
          exact SKPar.redexK ihx
        · exact SKPar.mul ihu ihv
      | mul u11 u12 =>
        cases u11 with
        | of a =>
          change SKPar s k (u' * v') (if a = s then _ else _)
          split_ifs with ha
          · subst a
            obtain ⟨x', y', rfl, _, _⟩ := skPar_of_s_mul_mul_inv hsk hu
            have ihu' : SKPar s k (FreeMagma.of s * x' * y')
                (completeDevSK s k (FreeMagma.of s * u12 * u2)) := ihu
            have hdev : completeDevSK s k (FreeMagma.of s * u12 * u2) =
                FreeMagma.of s * completeDevSK s k u12 * completeDevSK s k u2 := by
              change (if s = k then _ else _) = _
              simp [hsk, completeDevSK]
            rw [hdev] at ihu'
            obtain ⟨x'', y'', heq, ihx, ihy⟩ := skPar_of_s_mul_mul_inv hsk ihu'
            cases heq
            exact SKPar.redexS ihx ihy ihv
          · exact SKPar.mul ihu ihv
        | mul _ _ =>
          exact SKPar.mul ihu ihv

private lemma skPar_diamond {α : Type*} {s k : α} (hsk : s ≠ k) {t u₁ u₂ : FreeMagma α}
    (h1 : SKPar s k t u₁) (h2 : SKPar s k t u₂) :
    ∃ w, SKPar s k u₁ w ∧ SKPar s k u₂ w := by
  classical
  exact ⟨completeDevSK s k t, skPar_triangle hsk h1, skPar_triangle hsk h2⟩

private lemma skPar_strip {α : Type*} {s k : α} (hsk : s ≠ k) {t u₁ u₂ : FreeMagma α}
    (h1 : SKPar s k t u₁) (h2 : Relation.ReflTransGen (SKPar s k) t u₂) :
    ∃ w, Relation.ReflTransGen (SKPar s k) u₁ w ∧ SKPar s k u₂ w := by
  induction h2 generalizing u₁ with
  | refl => exact ⟨u₁, Relation.ReflTransGen.refl, h1⟩
  | tail _ hstep ih =>
    obtain ⟨w₁, hw₁, hw₂⟩ := ih h1
    obtain ⟨w₂, hw₃, hw₄⟩ := skPar_diamond hsk hw₂ hstep
    exact ⟨w₂, hw₁.tail hw₃, hw₄⟩

private lemma skPar_confluent {α : Type*} {s k : α} (hsk : s ≠ k) {t u₁ u₂ : FreeMagma α}
    (h1 : Relation.ReflTransGen (SKPar s k) t u₁)
    (h2 : Relation.ReflTransGen (SKPar s k) t u₂) :
    ∃ w, Relation.ReflTransGen (SKPar s k) u₁ w ∧ Relation.ReflTransGen (SKPar s k) u₂ w := by
  induction h1 generalizing u₂ with
  | refl => exact ⟨u₂, h2, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨w₁, hw₁, hw₂⟩ := ih h2
    obtain ⟨w₂, hw₃, hw₄⟩ := skPar_strip hsk hstep hw₁
    exact ⟨w₂, hw₃, hw₂.tail hw₄⟩

private lemma skStep_rtg_iff_skPar_rtg {α : Type*} (s k : α) (a b : FreeMagma α) :
    Relation.ReflTransGen (SKStep s k) a b ↔ Relation.ReflTransGen (SKPar s k) a b :=
  ⟨fun h => Relation.ReflTransGen.mono (fun _ _ hs => skStep_to_skPar hs) a b h,
   fun h => by
     induction h with
     | refl => exact Relation.ReflTransGen.refl
     | tail _ hp ih => exact ih.trans (skPar_to_rtg hp)⟩

/-- **Confluence of `SK`-Combinatory Logic (General `FreeMagma α` with `s ≠ k`)**. -/
theorem ppl004_sk_confluence {α : Type*} {s k : α} (hsk : s ≠ k) {t u₁ u₂ : FreeMagma α}
    (h1 : Relation.ReflTransGen
      (fun a b : FreeMagma α =>
        ∀ (R : FreeMagma α → FreeMagma α → Prop),
          (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
          (∀ x y, R (FreeMagma.of k * x * y) x) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) t u₁)
    (h2 : Relation.ReflTransGen
      (fun a b : FreeMagma α =>
        ∀ (R : FreeMagma α → FreeMagma α → Prop),
          (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
          (∀ x y, R (FreeMagma.of k * x * y) x) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b) t u₂) :
    ∃ w : FreeMagma α,
      Relation.ReflTransGen
        (fun a b : FreeMagma α =>
          ∀ (R : FreeMagma α → FreeMagma α → Prop),
            (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
            (∀ x y, R (FreeMagma.of k * x * y) x) →
            (∀ u u' v, R u u' → R (u * v) (u' * v)) →
            (∀ u v v', R v v' → R (u * v) (u * v')) →
            R a b) u₁ w ∧
      Relation.ReflTransGen
        (fun a b : FreeMagma α =>
          ∀ (R : FreeMagma α → FreeMagma α → Prop),
            (∀ x y z, R (FreeMagma.of s * x * y * z) (x * z * (y * z))) →
            (∀ x y, R (FreeMagma.of k * x * y) x) →
            (∀ u u' v, R u u' → R (u * v) (u' * v)) →
            (∀ u v v', R v v' → R (u * v) (u * v')) →
            R a b) u₂ w := by
  have hiff := skStep_iff_least s k
  have h1' := (skStep_rtg_iff_skPar_rtg s k t u₁).1 ((rtg_iff_of_rel_iff hiff t u₁).2 h1)
  have h2' := (skStep_rtg_iff_skPar_rtg s k t u₂).1 ((rtg_iff_of_rel_iff hiff t u₂).2 h2)
  obtain ⟨w, hw1, hw2⟩ := skPar_confluent hsk h1' h2'
  exact ⟨w,
    (rtg_iff_of_rel_iff hiff u₁ w).1 ((skStep_rtg_iff_skPar_rtg s k u₁ w).2 hw1),
    (rtg_iff_of_rel_iff hiff u₂ w).1 ((skStep_rtg_iff_skPar_rtg s k u₂ w).2 hw2)⟩

/-! #### Bracket Abstraction (Combinatory Completeness of `SK`) -/

private def skAbs {α : Type*} [DecidableEq α] (v : α) :
    FreeMagma (Bool ⊕ α) → FreeMagma (Bool ⊕ α)
  | FreeMagma.of x =>
      if x = Sum.inr v then
        FreeMagma.of (Sum.inl true) * FreeMagma.of (Sum.inl false) * FreeMagma.of (Sum.inl false)
      else
        FreeMagma.of (Sum.inl false) * FreeMagma.of x
  | FreeMagma.mul u w =>
      FreeMagma.of (Sum.inl true) * skAbs v u * skAbs v w

private lemma skAbs_no_var {α : Type*} [DecidableEq α] (v : α) (t : FreeMagma (Bool ⊕ α)) :
    Multiplicative.toAdd
      (FreeMagma.lift (fun x : Bool ⊕ α => Multiplicative.ofAdd (if x = Sum.inr v then (1 : ℕ) else 0))
        (skAbs v t)) = 0 := by
  induction t with
  | ih1 x =>
    unfold skAbs
    split_ifs with hx <;> simp [map_mul, hx]
  | ih2 u w ihu ihw =>
    simp [skAbs, map_mul, ihu, ihw]

private lemma skAbs_beta {α : Type*} [DecidableEq α] (v : α)
    (t arg : FreeMagma (Bool ⊕ α)) :
    Relation.ReflTransGen (SKStep (Sum.inl true : Bool ⊕ α) (Sum.inl false))
      (skAbs v t * arg)
      (FreeMagma.lift (fun x : Bool ⊕ α => if x = Sum.inr v then arg else FreeMagma.of x) t) := by
  induction t with
  | ih1 x =>
    unfold skAbs
    simp only [FreeMagma.lift_of]
    split_ifs with hx
    · have h1 : SKStep (Sum.inl true : Bool ⊕ α) (Sum.inl false)
          (FreeMagma.of (Sum.inl true) * FreeMagma.of (Sum.inl false) *
            FreeMagma.of (Sum.inl false) * arg)
          (FreeMagma.of (Sum.inl false) * arg * (FreeMagma.of (Sum.inl false) * arg)) :=
        SKStep.redexS _ _ _
      have h2 : SKStep (Sum.inl true : Bool ⊕ α) (Sum.inl false)
          (FreeMagma.of (Sum.inl false) * arg * (FreeMagma.of (Sum.inl false) * arg))
          arg :=
        SKStep.redexK _ _
      exact (Relation.ReflTransGen.single h1).tail h2
    · exact Relation.ReflTransGen.single (SKStep.redexK _ _)
  | ih2 u w ihu ihw =>
    simp only [skAbs, map_mul]
    have h1 : SKStep (Sum.inl true : Bool ⊕ α) (Sum.inl false)
        (FreeMagma.of (Sum.inl true) * skAbs v u * skAbs v w * arg)
        ((skAbs v u * arg) * (skAbs v w * arg)) :=
      SKStep.redexS _ _ _
    exact Relation.ReflTransGen.head h1 (skStep_rtg_mul ihu ihw)

/-- **Combinatory Completeness of `SK` (Bracket Abstraction Theorem)**:
For every open `SK`-term `t : FreeMagma (Bool ⊕ α)` and variable `v : α`, there exists an
open `SK`-term `f` in which `v` does not occur such that for EVERY argument `arg`,
`f * arg →* t[v := arg]`. (Contrast with `ppl004_s_no_k_combinator`: pure `S` fails
combinatory completeness because `λy. x = K x` cannot be abstracted!) -/
theorem ppl004_sk_combinatory_completeness {α : Type*} [DecidableEq α]
    (v : α) (t : FreeMagma (Bool ⊕ α)) :
    ∃ f : FreeMagma (Bool ⊕ α),
      Multiplicative.toAdd
        (FreeMagma.lift (fun x : Bool ⊕ α => Multiplicative.ofAdd (if x = Sum.inr v then (1 : ℕ) else 0)) f) = 0 ∧
      ∀ arg : FreeMagma (Bool ⊕ α),
        Relation.ReflTransGen
          (fun a b : FreeMagma (Bool ⊕ α) =>
            ∀ (R : FreeMagma (Bool ⊕ α) → FreeMagma (Bool ⊕ α) → Prop),
              (∀ x y z, R (FreeMagma.of (Sum.inl true) * x * y * z) (x * z * (y * z))) →
              (∀ x y, R (FreeMagma.of (Sum.inl false) * x * y) x) →
              (∀ u u' w, R u u' → R (u * w) (u' * w)) →
              (∀ u w w', R w w' → R (u * w) (u * w')) →
              R a b)
          (f * arg)
          (FreeMagma.lift (fun x : Bool ⊕ α => if x = Sum.inr v then arg else FreeMagma.of x) t) := by
  refine ⟨skAbs v t, skAbs_no_var v t, fun arg => ?_⟩
  exact (rtg_iff_of_rel_iff (skStep_iff_least (Sum.inl true : Bool ⊕ α) (Sum.inl false)) _ _).1
    (skAbs_beta v t arg)

/-! #### Explicit Standard Combinators (`I, B, C, W, M`) and Turing Fixed-Point Combinator `Θ` in `SK` -/

private def skS : FreeMagma Bool := FreeMagma.of true
private def skK : FreeMagma Bool := FreeMagma.of false
private def skI : FreeMagma Bool := skS * skK * skK
private def skB : FreeMagma Bool := skS * (skK * skS) * skK
private def skW : FreeMagma Bool := skS * skS * (skS * skK)
private def skM : FreeMagma Bool := skS * skI * skI
private def skC : FreeMagma Bool := skS * (skB * skB * skS) * (skK * skK)
private def skThetaA : FreeMagma Bool := skB * (skS * skI) * skM
private def skTheta : FreeMagma Bool := skThetaA * skThetaA

private lemma skI_red (x : FreeMagma Bool) :
    Relation.ReflTransGen (SKStep true false) (skI * x) x :=
  (Relation.ReflTransGen.single (SKStep.redexS skK skK x)).tail (SKStep.redexK x (skK * x))

private lemma skB_red (x y z : FreeMagma Bool) :
    Relation.ReflTransGen (SKStep true false) (skB * x * y * z) (x * (y * z)) := by
  have h1 : SKStep true false (skB * x * y * z)
      ((skK * skS * x * (skK * x)) * y * z) :=
    SKStep.left z (SKStep.left y (SKStep.redexS (skK * skS) skK x))
  have h2 : SKStep true false ((skK * skS * x * (skK * x)) * y * z)
      ((skS * (skK * x)) * y * z) :=
    SKStep.left z (SKStep.left y (SKStep.left (skK * x) (SKStep.redexK skS x)))
  have h3 : SKStep true false ((skS * (skK * x)) * y * z)
      ((skK * x * z) * (y * z)) :=
    SKStep.redexS (skK * x) y z
  have h4 : SKStep true false ((skK * x * z) * (y * z)) (x * (y * z)) :=
    SKStep.left (y * z) (SKStep.redexK x z)
  exact (((Relation.ReflTransGen.single h1).tail h2).tail h3).tail h4

private lemma skW_red (x y : FreeMagma Bool) :
    Relation.ReflTransGen (SKStep true false) (skW * x * y) (x * y * y) := by
  have h1 : SKStep true false (skW * x * y) (skS * x * (skS * skK * x) * y) :=
    SKStep.left y (SKStep.redexS skS (skS * skK) x)
  have h2 : SKStep true false (skS * x * (skS * skK * x) * y)
      ((x * y) * (skS * skK * x * y)) :=
    SKStep.redexS x (skS * skK * x) y
  have h3 : SKStep true false ((x * y) * (skS * skK * x * y))
      ((x * y) * (skK * y * (x * y))) :=
    SKStep.right (x * y) (SKStep.redexS skK x y)
  have h4 : SKStep true false ((x * y) * (skK * y * (x * y))) (x * y * y) :=
    SKStep.right (x * y) (SKStep.redexK y (x * y))
  exact (((Relation.ReflTransGen.single h1).tail h2).tail h3).tail h4

private lemma skM_red (x : FreeMagma Bool) :
    Relation.ReflTransGen (SKStep true false) (skM * x) (x * x) := by
  have h1 : SKStep true false (skM * x) ((skI * x) * (skI * x)) :=
    SKStep.redexS skI skI x
  exact Relation.ReflTransGen.head h1 (skStep_rtg_mul (skI_red x) (skI_red x))

private lemma skC_red (x y z : FreeMagma Bool) :
    Relation.ReflTransGen (SKStep true false) (skC * x * y * z) (x * z * y) := by
  have h1 : SKStep true false (skC * x * y * z)
      ((skB * skB * skS * x) * (skK * skK * x) * y * z) :=
    SKStep.left z (SKStep.left y (SKStep.redexS (skB * skB * skS) (skK * skK) x))
  have h2 : Relation.ReflTransGen (SKStep true false)
      ((skB * skB * skS * x) * (skK * skK * x) * y * z)
      ((skB * (skS * x)) * skK * y * z) :=
    skStep_rtg_left z (skStep_rtg_left y
      (skStep_rtg_mul (skB_red skB skS x) (Relation.ReflTransGen.single (SKStep.redexK skK x))))
  have h3 : Relation.ReflTransGen (SKStep true false)
      ((skB * (skS * x)) * skK * y * z)
      (((skS * x) * (skK * y)) * z) :=
    skStep_rtg_left z (skB_red (skS * x) skK y)
  have h4 : SKStep true false (((skS * x) * (skK * y)) * z)
      ((x * z) * (skK * y * z)) :=
    SKStep.redexS x (skK * y) z
  have h5 : SKStep true false ((x * z) * (skK * y * z)) (x * z * y) :=
    SKStep.right (x * z) (SKStep.redexK y z)
  exact ((Relation.ReflTransGen.head h1 h2).trans h3).tail h4 |>.tail h5

private lemma skTheta_red (f : FreeMagma Bool) :
    Relation.ReflTransGen (SKStep true false) (skTheta * f) (f * (skTheta * f)) := by
  have h1 : Relation.ReflTransGen (SKStep true false)
      (skThetaA * skThetaA * f)
      (((skS * skI) * (skM * skThetaA)) * f) :=
    skStep_rtg_left f (skB_red (skS * skI) skM skThetaA)
  have h2 : Relation.ReflTransGen (SKStep true false)
      (((skS * skI) * (skM * skThetaA)) * f)
      ((skS * skI * skTheta) * f) :=
    skStep_rtg_left f (skStep_rtg_right (skS * skI) (skM_red skThetaA))
  have h3 : SKStep true false ((skS * skI * skTheta) * f)
      ((skI * f) * (skTheta * f)) :=
    SKStep.redexS skI skTheta f
  have h4 : Relation.ReflTransGen (SKStep true false)
      ((skI * f) * (skTheta * f))
      (f * (skTheta * f)) :=
    skStep_rtg_left (skTheta * f) (skI_red f)
  exact ((h1.trans h2).tail h3).trans h4

/-- **Standard Combinators `I, B, C, W, M` and Turing's Fixed-Point Combinator `Θ` in `SK`**:
In `FreeMagma Bool` (`true` = `S`, `false` = `K`), there exist closed terms `I, B, C, W, M, Θ`
satisfying all classical reduction laws, including unconditional forward fixed-point reduction
`Θ * f →* f * (Θ * f)` for every `f : FreeMagma Bool`. -/
theorem ppl004_sk_standard_combinators :
    ∃ I B C W M Θ : FreeMagma Bool,
      let step : FreeMagma Bool → FreeMagma Bool → Prop := fun a b =>
        ∀ (R : FreeMagma Bool → FreeMagma Bool → Prop),
          (∀ x y z, R (FreeMagma.of true * x * y * z) (x * z * (y * z))) →
          (∀ x y, R (FreeMagma.of false * x * y) x) →
          (∀ u u' v, R u u' → R (u * v) (u' * v)) →
          (∀ u v v', R v v' → R (u * v) (u * v')) →
          R a b
      (∀ x, Relation.ReflTransGen step (I * x) x) ∧
      (∀ x y z, Relation.ReflTransGen step (B * x * y * z) (x * (y * z))) ∧
      (∀ x y z, Relation.ReflTransGen step (C * x * y * z) (x * z * y)) ∧
      (∀ x y, Relation.ReflTransGen step (W * x * y) (x * y * y)) ∧
      (∀ x, Relation.ReflTransGen step (M * x) (x * x)) ∧
      (∀ f, Relation.ReflTransGen step (Θ * f) (f * (Θ * f))) := by
  have hiff := skStep_iff_least true false
  refine ⟨skI, skB, skC, skW, skM, skTheta, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact (rtg_iff_of_rel_iff hiff _ _).1 (skI_red x)
  · intro x y z; exact (rtg_iff_of_rel_iff hiff _ _).1 (skB_red x y z)
  · intro x y z; exact (rtg_iff_of_rel_iff hiff _ _).1 (skC_red x y z)
  · intro x y; exact (rtg_iff_of_rel_iff hiff _ _).1 (skW_red x y)
  · intro x; exact (rtg_iff_of_rel_iff hiff _ _).1 (skM_red x)
  · intro f; exact (rtg_iff_of_rel_iff hiff _ _).1 (skTheta_red f)

end PPL004
