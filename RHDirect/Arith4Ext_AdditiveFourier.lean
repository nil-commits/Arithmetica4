/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.unusedSectionVars false

/-!
# Arithmetica4 Extension: Additive Combinatorics & Discrete Fourier Engine

A self-contained, unconditional, Tier A library on native Mathlib structures
(`AddCommGroup`, `Finset`, `Pointwise`, `ZMod N`, `AddChar`, `ℂ`) providing:

1. **Ruzsa Calculus** (for any `AddCommGroup G`):
   - `ruzsa_triangle_inequality`: `|A| · |B - C| ≤ |A - B| · |A - C|`
   - `ruzsa_triangle_inequality_add`: `|A| · |B - C| ≤ |A + B| · |A + C|`
   - `ruzsa_triangle_inequality_sum`: `|A| · |B + C| ≤ |A + B| · |A - C|`
   - `ruzsa_covering_lemma`: `∃ F ⊆ B, |F| · |A| ≤ |A + B| ∧ B ⊆ F + (A - A)`
   - `ruzsa_covering_lemma_sub`: `∃ F ⊆ B, |F| · |A| ≤ |B - A| ∧ B ⊆ F + (A - A)`

2. **Petridis's Lemma & Plünnecke–Ruzsa Inequality** (via Petridis's elementary inductive proof):
   - `iterSum n B`: the `n`-fold iterated sumset `B + ⋯ + B` (`iterSum 0 B = {0}`)
   - `petridis_lemma`: for `X ⊆ A` minimizing `|X + B| / |X|`,
     `|X + B + C| · |X| ≤ |X + B| · |X + C|` for every finite `C`
   - `pluennecke_ruzsa`: `|A + B| ≤ K |A| ⇒ |nB - mB| ≤ K^(n+m) |A|`
   - `pluennecke_ruzsa_sum`: `|A + B| ≤ K |A| ⇒ |nB| ≤ K^n |A|`

3. **Additive Energy & Quantitative Balog–Szemerédi–Gowers (BSG) Theorem**:
   - `addEnergy A B`, `addRep A B`, `subRep A B` with exact sum-of-squares identities
     and Cauchy–Schwarz lower bounds
   - `bipartite_paths_of_length_three`: Sudakov–Szemerédi–Vu graph lemma yielding
     large subsets `A' ⊆ A`, `B' ⊆ B` with `Ω(α⁵ |A| |B|)` length-3 paths for every pair
   - `balog_szemeredi_gowers`: `E(A, B) ≥ c |A|^(3/2) |B|^(3/2)` implies large
     `A' ⊆ A, B' ⊆ B` with `|A' + B'| ≤ (2^22 / c^8) √(|A| |B|)`
   - `balog_szemeredi_gowers_single`: `E(A, A) ≥ |A|^3 / K` implies `A' ⊆ A` with
     `|A'| ≥ |A| / (16 K)` and polynomial sumset/difference-set bounds

4. **Discrete Fourier Analysis over `ZMod N` & Finite Abelian Groups + Roth-Style Density**:
   - `eZMod`, `dft`, `conv`, `indicatorC`, `largeSpectrum`, `threeAPCount`, `bohrSet`
   - Exact orthogonality (for `ZMod N` and general finite `AddChar G ℂ`),
     Fourier inversion, Plancherel, Parseval, convolution-to-product,
     and `E(A, B) = N⁻¹ ∑ |f̂_A(r)|² |f̂_B(r)|²`
   - Large-spectrum bound, energy-to-large-Fourier-coefficient lemma,
     3-AP Fourier identity, Roth large-Fourier-coefficient lemma, and
     Bohr-set density increment theorem
-/

open scoped BigOperators Pointwise

namespace Arith4Ext.AdditiveFourier

/-! ### Section 1: Ruzsa Triangle Inequality & Ruzsa Covering Lemma -/

section RuzsaCalculus

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- **Ruzsa Triangle Inequality** (difference form):
For any finite subsets `A, B, C` of an abelian group `G`,
`|A| · |B - C| ≤ |A - B| · |A - C|`. -/
theorem ruzsa_triangle_inequality (A B C : Finset G) :
    A.card * (B - C).card ≤ (A - B).card * (A - C).card := by
  classical
  have hrep : ∀ d : G, d ∈ B - C → ∃ bc : G × G, bc.1 ∈ B ∧ bc.2 ∈ C ∧ bc.1 - bc.2 = d := by
    intro d hd
    rcases Finset.mem_sub.mp hd with ⟨b, hb, c, hc, hbc⟩
    exact ⟨(b, c), hb, hc, hbc⟩
  let pickB : G → G := fun d => if h : d ∈ B - C then (Classical.choose (hrep d h)).1 else 0
  let pickC : G → G := fun d => if h : d ∈ B - C then (Classical.choose (hrep d h)).2 else 0
  have hpickB : ∀ d (h : d ∈ B - C), pickB d ∈ B := by
    intro d h; simp only [pickB, dif_pos h]; exact (Classical.choose_spec (hrep d h)).1
  have hpickC : ∀ d (h : d ∈ B - C), pickC d ∈ C := by
    intro d h; simp only [pickC, dif_pos h]; exact (Classical.choose_spec (hrep d h)).2.1
  have hpickSub : ∀ d (h : d ∈ B - C), pickB d - pickC d = d := by
    intro d h; simp only [pickB, pickC, dif_pos h]; exact (Classical.choose_spec (hrep d h)).2.2
  let φ : G × G → G × G := fun p => (p.1 - pickB p.2, p.1 - pickC p.2)
  have hmaps : Set.MapsTo φ (A ×ˢ (B - C) : Finset (G × G)) ((A - B) ×ˢ (A - C) : Finset (G × G)) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_product] at hp ⊢
    exact ⟨Finset.sub_mem_sub hp.1 (hpickB p.2 hp.2),
           Finset.sub_mem_sub hp.1 (hpickC p.2 hp.2)⟩
  have hinj : Set.InjOn φ (A ×ˢ (B - C) : Finset (G × G)) := by
    intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
    have h1 : p₁.1 - pickB p₁.2 = p₂.1 - pickB p₂.2 := congrArg Prod.fst heq
    have h2 : p₁.1 - pickC p₁.2 = p₂.1 - pickC p₂.2 := congrArg Prod.snd heq
    have hd : p₁.2 = p₂.2 := by
      calc p₁.2 = pickB p₁.2 - pickC p₁.2 := (hpickSub p₁.2 hp₁.2).symm
        _ = (p₁.1 - pickC p₁.2) - (p₁.1 - pickB p₁.2) := by abel
        _ = (p₂.1 - pickC p₂.2) - (p₂.1 - pickB p₂.2) := by rw [h1, h2]
        _ = pickB p₂.2 - pickC p₂.2 := by abel
        _ = p₂.2 := hpickSub p₂.2 hp₂.2
    have ha : p₁.1 = p₂.1 := by
      rw [hd] at h1
      exact sub_left_inj.mp h1
    exact Prod.ext ha hd
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  simpa only [Finset.card_product] using hcard

/-- Cardinality of `-(A : Finset G)` equals `A.card`. -/
lemma card_neg_finset (A : Finset G) : (-A).card = A.card := by
  have h : -A = A.image (fun x : G => -x) := by
    ext x; simp only [Finset.mem_neg, Finset.mem_image]
  rw [h, Finset.card_image_of_injective _ neg_injective]

/-- Cardinality of `B - C` equals cardinality of `C - B`. -/
lemma card_sub_comm (B C : Finset G) : (B - C).card = (C - B).card := by
  have h : -(B - C) = C - B := by
    ext x
    simp only [Finset.mem_neg, Finset.mem_sub]
    constructor
    · rintro ⟨d, ⟨b, hb, c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, b, hb, by abel⟩
    · rintro ⟨c, hc, b, hb, rfl⟩
      exact ⟨b - c, ⟨b, hb, c, hc, rfl⟩, by abel⟩
  rw [← h, card_neg_finset]

/-- **Ruzsa Triangle Inequality** (sumset form):
`|A| · |B - C| ≤ |A + B| · |A + C|`. -/
theorem ruzsa_triangle_inequality_add (A B C : Finset G) :
    A.card * (B - C).card ≤ (A + B).card * (A + C).card := by
  have h := ruzsa_triangle_inequality A (-B) (-C)
  have h1 : A - (-B) = A + B := by
    ext x; simp only [Finset.mem_sub, Finset.mem_neg, Finset.mem_add]
    constructor
    · rintro ⟨a, ha, y, ⟨b, hb, rfl⟩, rfl⟩; exact ⟨a, ha, b, hb, by abel⟩
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, -b, ⟨b, hb, rfl⟩, by abel⟩
  have h2 : A - (-C) = A + C := by
    ext x; simp only [Finset.mem_sub, Finset.mem_neg, Finset.mem_add]
    constructor
    · rintro ⟨a, ha, y, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨a, ha, c, hc, by abel⟩
    · rintro ⟨a, ha, c, hc, rfl⟩; exact ⟨a, ha, -c, ⟨c, hc, rfl⟩, by abel⟩
  have h3 : (-B) - (-C) = C - B := by
    ext x; simp only [Finset.mem_sub, Finset.mem_neg]
    constructor
    · rintro ⟨u, ⟨b, hb, rfl⟩, v, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨c, hc, b, hb, by abel⟩
    · rintro ⟨c, hc, b, hb, rfl⟩; exact ⟨-b, ⟨b, hb, rfl⟩, -c, ⟨c, hc, rfl⟩, by abel⟩
  rw [h1, h2, h3, card_sub_comm C B] at h
  exact h

/-- **Ruzsa Triangle Inequality** (mixed sum/difference form):
`|A| · |B + C| ≤ |A + B| · |A - C|`. -/
theorem ruzsa_triangle_inequality_sum (A B C : Finset G) :
    A.card * (B + C).card ≤ (A + B).card * (A - C).card := by
  have h := ruzsa_triangle_inequality_add A B (-C)
  have h1 : B - (-C) = B + C := by
    ext x; simp only [Finset.mem_sub, Finset.mem_neg, Finset.mem_add]
    constructor
    · rintro ⟨b, hb, y, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨b, hb, c, hc, by abel⟩
    · rintro ⟨b, hb, c, hc, rfl⟩; exact ⟨b, hb, -c, ⟨c, hc, rfl⟩, by abel⟩
  have h2 : A + (-C) = A - C := by
    ext x; simp only [Finset.mem_add, Finset.mem_neg, Finset.mem_sub]
    constructor
    · rintro ⟨a, ha, y, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨a, ha, c, hc, by abel⟩
    · rintro ⟨a, ha, c, hc, rfl⟩; exact ⟨a, ha, -c, ⟨c, hc, rfl⟩, by abel⟩
  rw [h1, h2] at h
  exact h

/-- **Ruzsa Covering Lemma** (sumset form):
If `A` is nonempty, there exists `F ⊆ B` such that `|F| · |A| ≤ |A + B|` and
`B ⊆ F + (A - A)`. -/
theorem ruzsa_covering_lemma (A B : Finset G) (hA : A.Nonempty) :
    ∃ F ⊆ B, F.card * A.card ≤ (A + B).card ∧ B ⊆ F + (A - A) := by
  classical
  let valid : Finset G → Prop := fun F =>
    ∀ x ∈ F, ∀ y ∈ F, ∀ a₁ ∈ A, ∀ a₂ ∈ A, x + a₁ = y + a₂ → x = y
  let S : Finset (Finset G) := B.powerset.filter valid
  have hS_ne : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset B, ?_⟩⟩
    intro x hx; exact False.elim (Finset.notMem_empty x hx)
  obtain ⟨F, hF_mem, hF_max⟩ := Finset.exists_max_image S Finset.card hS_ne
  rw [Finset.mem_filter, Finset.mem_powerset] at hF_mem
  rcases hF_mem with ⟨hFB, hFvalid⟩
  refine ⟨F, hFB, ?_, ?_⟩
  · -- Size bound via injection `(f, a) ↦ a + f` into `A + B`
    let ψ : G × G → G := fun p => p.2 + p.1
    have hmaps : Set.MapsTo ψ (F ×ˢ A : Finset (G × G)) (A + B : Finset G) := by
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_product] at hp
      exact Finset.add_mem_add hp.2 (hFB hp.1)
    have hinj : Set.InjOn ψ (F ×ˢ A : Finset (G × G)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
      have heq' : p₁.1 + p₁.2 = p₂.1 + p₂.2 := by
        simpa [ψ, add_comm] using heq
      have hf : p₁.1 = p₂.1 := hFvalid p₁.1 hp₁.1 p₂.1 hp₂.1 p₁.2 hp₁.2 p₂.2 hp₂.2 heq'
      have ha : p₁.2 = p₂.2 := by
        rw [hf] at heq'
        exact add_left_cancel heq'
      exact Prod.ext hf ha
    have hcard := Finset.card_le_card_of_injOn ψ hmaps hinj
    simpa only [Finset.card_product] using hcard
  · -- Covering property by maximality of `F`
    intro b hb
    by_cases hbF : b ∈ F
    · obtain ⟨a, ha⟩ := hA
      have h0 : (0 : G) ∈ A - A := by
        rw [Finset.mem_sub]; exact ⟨a, ha, a, ha, sub_self a⟩
      have : b = b + 0 := (add_zero b).symm
      rw [this]
      exact Finset.add_mem_add hbF h0
    · have hnot : ¬ valid (insert b F) := by
        intro hval
        have hins_mem : insert b F ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hb hFB), hval⟩
        have hle := hF_max (insert b F) hins_mem
        rw [Finset.card_insert_of_notMem hbF] at hle
        omega
      dsimp only [valid] at hnot
      push Not at hnot
      obtain ⟨x, hx, y, hy, a₁, ha₁, a₂, ha₂, hsum, hxy⟩ := hnot
      rw [Finset.mem_insert] at hx hy
      rcases hx with hxb | hxF
      · rcases hy with hyb | hyF
        · exact False.elim (hxy (hxb.trans hyb.symm))
        · rw [hxb] at hsum
          have hb_eq : b = y + (a₂ - a₁) := by
            have := eq_sub_of_add_eq hsum
            rw [this]; abel
          rw [hb_eq]
          exact Finset.add_mem_add hyF (Finset.sub_mem_sub ha₂ ha₁)
      · rcases hy with hyb | hyF
        · rw [hyb] at hsum
          have hb_eq : b = x + (a₁ - a₂) := by
            have := eq_sub_of_add_eq hsum.symm
            rw [this]; abel
          rw [hb_eq]
          exact Finset.add_mem_add hxF (Finset.sub_mem_sub ha₁ ha₂)
        · exact False.elim (hxy (hFvalid x hxF y hyF a₁ ha₁ a₂ ha₂ hsum))

/-- **Ruzsa Covering Lemma** (real-valued ratio form):
If `A` is nonempty, there exists `F ⊆ B` with `|F| ≤ |A + B| / |A|` and `B ⊆ F + (A - A)`. -/
theorem ruzsa_covering_lemma_real (A B : Finset G) (hA : A.Nonempty) :
    ∃ F ⊆ B, (F.card : ℝ) ≤ (A + B).card / (A.card : ℝ) ∧ B ⊆ F + (A - A) := by
  obtain ⟨F, hFB, hcard, hcov⟩ := ruzsa_covering_lemma A B hA
  refine ⟨F, hFB, ?_, hcov⟩
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  rw [le_div_iff₀ hApos]
  exact_mod_cast hcard

/-- **Ruzsa Covering Lemma** (difference-set form):
If `A` is nonempty, there exists `F ⊆ B` such that `|F| · |A| ≤ |B - A|` and
`B ⊆ F + (A - A)`. -/
theorem ruzsa_covering_lemma_sub (A B : Finset G) (hA : A.Nonempty) :
    ∃ F ⊆ B, F.card * A.card ≤ (B - A).card ∧ B ⊆ F + (A - A) := by
  have hnegA : (-A).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨-a, Finset.mem_neg.mpr ⟨a, ha, rfl⟩⟩
  obtain ⟨F, hFB, hcard, hcov⟩ := ruzsa_covering_lemma (-A) B hnegA
  have h1 : (-A) + B = B - A := by
    ext x; simp only [Finset.mem_add, Finset.mem_neg, Finset.mem_sub]
    constructor
    · rintro ⟨u, ⟨a, ha, rfl⟩, b, hb, rfl⟩; exact ⟨b, hb, a, ha, by abel⟩
    · rintro ⟨b, hb, a, ha, rfl⟩; exact ⟨-a, ⟨a, ha, rfl⟩, b, hb, by abel⟩
  have h2 : (-A) - (-A) = A - A := by
    ext x; simp only [Finset.mem_sub, Finset.mem_neg]
    constructor
    · rintro ⟨u, ⟨a₁, ha₁, rfl⟩, v, ⟨a₂, ha₂, rfl⟩, rfl⟩; exact ⟨a₂, ha₂, a₁, ha₁, by abel⟩
    · rintro ⟨a₁, ha₁, a₂, ha₂, rfl⟩; exact ⟨-a₂, ⟨a₂, ha₂, rfl⟩, -a₁, ⟨a₁, ha₁, rfl⟩, by abel⟩
  rw [card_neg_finset, h1] at hcard
  rw [h2] at hcov
  exact ⟨F, hFB, hcard, hcov⟩

end RuzsaCalculus

/-! ### Section 2: Petridis's Lemma & Plünnecke–Ruzsa Inequality -/

section PluenneckeRuzsa

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The `n`-fold iterated sumset `B + B + ⋯ + B`, with `iterSum 0 B = {0}`.
Unlike Mathlib's pointwise scalar multiplication `n • B` (which is dilation `{n • b | b ∈ B}`),
`iterSum n B` is the genuine Minkowski `n`-fold sumset. -/
def iterSum : ℕ → Finset G → Finset G
  | 0, _ => {0}
  | n + 1, B => iterSum n B + B

@[simp] lemma iterSum_zero (B : Finset G) : iterSum 0 B = {0} := rfl

@[simp] lemma iterSum_succ (n : ℕ) (B : Finset G) :
    iterSum (n + 1) B = iterSum n B + B := rfl

@[simp] lemma iterSum_one (B : Finset G) : iterSum 1 B = B := by
  ext x; simp [iterSum, Finset.mem_add]

lemma iterSum_add (m n : ℕ) (B : Finset G) :
    iterSum (m + n) B = iterSum m B + iterSum n B := by
  induction n with
  | zero =>
    ext x; simp [iterSum, Finset.mem_add]
  | succ k ih =>
    rw [← Nat.add_assoc, iterSum_succ, ih, iterSum_succ, add_assoc]

lemma card_sub_zero_singleton (A : Finset G) : (A - ({0} : Finset G)).card = A.card := by
  have h : A - ({0} : Finset G) = A := by
    ext x; simp
  rw [h]

/-- Existence of a nonempty subset `X ⊆ A` minimizing the doubling ratio `|X + B| / |X|`. -/
lemma exists_min_doubling_subset (A B : Finset G) (hA : A.Nonempty) :
    ∃ X ⊆ A, X.Nonempty ∧
      ∀ Y ⊆ A, Y.Nonempty → (X + B).card * Y.card ≤ (Y + B).card * X.card := by
  classical
  let P : Finset (Finset G) := A.powerset.filter Finset.Nonempty
  have hP_ne : P.Nonempty := ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hA⟩⟩
  let ratio : Finset G → ℚ := fun X => ((X + B).card : ℚ) / (X.card : ℚ)
  obtain ⟨X, hX_mem, hX_min⟩ := Finset.exists_min_image P ratio hP_ne
  rw [Finset.mem_filter, Finset.mem_powerset] at hX_mem
  refine ⟨X, hX_mem.1, hX_mem.2, ?_⟩
  intro Y hYA hYne
  have hY_mem : Y ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYA, hYne⟩
  have hle : ratio X ≤ ratio Y := hX_min Y hY_mem
  have hXpos : (0 : ℚ) < (X.card : ℚ) := Nat.cast_pos.mpr hX_mem.2.card_pos
  have hYpos : (0 : ℚ) < (Y.card : ℚ) := Nat.cast_pos.mpr hYne.card_pos
  simp only [ratio, div_le_div_iff₀ hXpos hYpos] at hle
  exact_mod_cast hle

/-- **Petridis's Lemma (2012)**:
If `X ⊆ A` is a nonempty subset minimizing `|X + B| / |X|` among all nonempty subsets
of `A`, then for every finite set `C ⊆ G`,
`|X + B + C| · |X| ≤ |X + B| · |X + C|`. -/
theorem petridis_lemma (A B X : Finset G) (hXA : X ⊆ A)
    (hmin : ∀ Y ⊆ A, Y.Nonempty → (X + B).card * Y.card ≤ (Y + B).card * X.card)
    (C : Finset G) :
    (X + B + C).card * X.card ≤ (X + B).card * (X + C).card := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    simp
  | @insert c C' hc ih =>
    -- Split `X` into `Z = {x ∈ X | x + c ∈ X + C'}` and its complement `X \ Z`
    let Z : Finset G := X.filter (fun x => x + c ∈ X + C')
    have hZX : Z ⊆ X := Finset.filter_subset _ _
    have hZA : Z ⊆ A := hZX.trans hXA
    -- Exact cardinality of `X + insert c C'`
    have hXC_eq : (X + insert c C').card = (X + C').card + (X.card - Z.card) := by
      have hdecomp : X + insert c C' = (X + C') ∪ ((X \ Z).image (fun x => x + c)) := by
        ext u
        simp only [Finset.mem_add, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          Finset.mem_sdiff, Finset.mem_filter, Z]
        constructor
        · rintro ⟨x, hx, d, hdc | hd, rfl⟩
          · subst hdc
            by_cases hmem : x + d ∈ X + C'
            · exact Or.inl (Finset.mem_add.mp hmem)
            · exact Or.inr ⟨x, ⟨hx, fun h => hmem (Finset.mem_add.mpr h.2)⟩, rfl⟩
          · exact Or.inl ⟨x, hx, d, hd, rfl⟩
        · rintro (⟨x, hx, d, hd, rfl⟩ | ⟨x, ⟨hx, _⟩, rfl⟩)
          · exact ⟨x, hx, d, Or.inr hd, rfl⟩
          · exact ⟨x, hx, c, Or.inl rfl, rfl⟩
      have hdisj : Disjoint (X + C') ((X \ Z).image (fun x => x + c)) := by
        rw [Finset.disjoint_left]
        intro u hu1 hu2
        rw [Finset.mem_image] at hu2
        rcases hu2 with ⟨x, hx, rfl⟩
        rw [Finset.mem_sdiff, Finset.mem_filter] at hx
        exact hx.2 ⟨hx.1, hu1⟩
      rw [hdecomp, Finset.card_union_of_disjoint hdisj]
      have hinj : Function.Injective (fun x : G => x + c) := add_left_injective c
      rw [Finset.card_image_of_injective _ hinj, Finset.card_sdiff, Finset.inter_eq_left.mpr hZX]
    -- Upper bound on cardinality of `X + B + insert c C'`
    have hZB_sub : Z + B ⊆ X + B := Finset.add_subset_add_right hZX
    have hXBC_le : (X + B + insert c C').card ≤
        (X + B + C').card + ((X + B).card - (Z + B).card) := by
      have hsub : X + B + insert c C' ⊆
          (X + B + C') ∪ (((X + B) \ (Z + B)).image (fun u => u + c)) := by
        intro w hw
        rw [Finset.mem_add] at hw
        rcases hw with ⟨u, hu, d, hd, rfl⟩
        rw [Finset.mem_insert] at hd
        rcases hd with hdc | hd'
        · rw [hdc]
          by_cases huZB : u ∈ Z + B
          · rw [Finset.mem_add] at huZB
            rcases huZB with ⟨z, hz, b, hb, rfl⟩
            rw [Finset.mem_filter] at hz
            rcases Finset.mem_add.mp hz.2 with ⟨x', hx', d', hd', hxd⟩
            apply Finset.mem_union_left
            have : z + b + c = (x' + b) + d' := by
              calc z + b + c = (z + c) + b := by abel
                _ = (x' + d') + b := by rw [← hxd]
                _ = (x' + b) + d' := by abel
            rw [this]
            exact Finset.add_mem_add (Finset.add_mem_add hx' hb) hd'
          · apply Finset.mem_union_right
            rw [Finset.mem_image]
            exact ⟨u, Finset.mem_sdiff.mpr ⟨hu, huZB⟩, rfl⟩
        · apply Finset.mem_union_left
          exact Finset.add_mem_add hu hd'
      calc (X + B + insert c C').card
          ≤ ((X + B + C') ∪ (((X + B) \ (Z + B)).image (fun u => u + c))).card :=
            Finset.card_le_card hsub
        _ ≤ (X + B + C').card + (((X + B) \ (Z + B)).image (fun u => u + c)).card :=
            Finset.card_union_le _ _
        _ = (X + B + C').card + ((X + B) \ (Z + B)).card := by
            rw [Finset.card_image_of_injective _ (add_left_injective c)]
        _ = (X + B + C').card + ((X + B).card - (Z + B).card) := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hZB_sub]
    -- Combine via minimality of `X`
    have hZ_key : ((X + B).card - (Z + B).card) * X.card ≤
        (X + B).card * (X.card - Z.card) := by
      by_cases hZne : Z.Nonempty
      · have hminZ : (X + B).card * Z.card ≤ (Z + B).card * X.card := hmin Z hZA hZne
        have hZB_le : (Z + B).card ≤ (X + B).card := Finset.card_le_card hZB_sub
        have hZ_le : Z.card ≤ X.card := Finset.card_le_card hZX
        zify [hZB_le, hZ_le] at hminZ ⊢
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hZne
        rw [hZne]
        simp
    calc (X + B + insert c C').card * X.card
        ≤ ((X + B + C').card + ((X + B).card - (Z + B).card)) * X.card :=
          Nat.mul_le_mul_right X.card hXBC_le
      _ = (X + B + C').card * X.card + ((X + B).card - (Z + B).card) * X.card :=
          Nat.add_mul _ _ _
      _ ≤ (X + B).card * (X + C').card + (X + B).card * (X.card - Z.card) :=
          Nat.add_le_add ih hZ_key
      _ = (X + B).card * ((X + C').card + (X.card - Z.card)) :=
          (Nat.mul_add _ _ _).symm
      _ = (X + B).card * (X + insert c C').card := by rw [hXC_eq]

/-- Iterated Petridis bound: for a minimizing subset `X ⊆ A` with `|X + B| ≤ K · |X|`,
`|X + kB| ≤ K^k · |X|` for every `k : ℕ`. -/
theorem petridis_iterated_sumset (A B X : Finset G) (hXA : X ⊆ A) (hXne : X.Nonempty)
    (hmin : ∀ Y ⊆ A, Y.Nonempty → (X + B).card * Y.card ≤ (Y + B).card * X.card)
    {K : ℝ} (hK0 : 0 ≤ K) (hKB : ((X + B).card : ℝ) ≤ K * (X.card : ℝ)) (k : ℕ) :
    ((X + iterSum k B).card : ℝ) ≤ K ^ k * (X.card : ℝ) := by
  induction k with
  | zero =>
    have h0 : X + ({0} : Finset G) = X := by
      ext x; simp [Finset.mem_add]
    simp [iterSum, h0]
  | succ n ih =>
    have hpet : ((X + B + iterSum n B).card : ℝ) * (X.card : ℝ) ≤
        ((X + B).card : ℝ) * ((X + iterSum n B).card : ℝ) := by
      exact_mod_cast petridis_lemma A B X hXA hmin (iterSum n B)
    have hcomm : X + iterSum (n + 1) B = X + B + iterSum n B := by
      rw [iterSum_succ]
      have : X + (iterSum n B + B) = X + B + iterSum n B := by
        rw [add_comm (iterSum n B) B, ← add_assoc]
      exact this
    rw [hcomm]
    have hXpos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hXne.card_pos
    have hstep : ((X + B + iterSum n B).card : ℝ) * (X.card : ℝ) ≤
        (K ^ (n + 1) * (X.card : ℝ)) * (X.card : ℝ) := by
      calc ((X + B + iterSum n B).card : ℝ) * (X.card : ℝ)
          ≤ ((X + B).card : ℝ) * ((X + iterSum n B).card : ℝ) := hpet
        _ ≤ (K * (X.card : ℝ)) * (K ^ n * (X.card : ℝ)) :=
            mul_le_mul hKB ih (Nat.cast_nonneg _) (mul_nonneg hK0 (Nat.cast_nonneg _))
        _ = (K ^ (n + 1) * (X.card : ℝ)) * (X.card : ℝ) := by
            rw [pow_succ]; ring
    exact le_of_mul_le_mul_right hstep hXpos

/-- **Plünnecke–Ruzsa Inequality** (Petridis proof):
If `A` is nonempty, `0 ≤ K`, and `|A + B| ≤ K · |A|`, then for all `n, m : ℕ`,
`|nB - mB| ≤ K^(n + m) · |A|`. -/
theorem pluennecke_ruzsa (A B : Finset G) (hA : A.Nonempty)
    {K : ℝ} (hK0 : 0 ≤ K) (hAB : ((A + B).card : ℝ) ≤ K * (A.card : ℝ)) (n m : ℕ) :
    ((iterSum n B - iterSum m B).card : ℝ) ≤ K ^ (n + m) * (A.card : ℝ) := by
  obtain ⟨X, hXA, hXne, hmin⟩ := exists_min_doubling_subset A B hA
  have hXpos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.mpr hXne.card_pos
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hXB_le : ((X + B).card : ℝ) ≤ K * (X.card : ℝ) := by
    have hminA : ((X + B).card : ℝ) * (A.card : ℝ) ≤ ((A + B).card : ℝ) * (X.card : ℝ) := by
      exact_mod_cast hmin A Finset.Subset.rfl hA
    have h1 : ((X + B).card : ℝ) * (A.card : ℝ) ≤ (K * (X.card : ℝ)) * (A.card : ℝ) := by
      calc ((X + B).card : ℝ) * (A.card : ℝ)
          ≤ ((A + B).card : ℝ) * (X.card : ℝ) := hminA
        _ ≤ (K * (A.card : ℝ)) * (X.card : ℝ) :=
            mul_le_mul_of_nonneg_right hAB (Nat.cast_nonneg _)
        _ = (K * (X.card : ℝ)) * (A.card : ℝ) := by ring
    exact le_of_mul_le_mul_right h1 hApos
  have hn := petridis_iterated_sumset A B X hXA hXne hmin hK0 hXB_le n
  have hm := petridis_iterated_sumset A B X hXA hXne hmin hK0 hXB_le m
  have htri : (X.card : ℝ) * ((iterSum n B - iterSum m B).card : ℝ) ≤
      ((X + iterSum n B).card : ℝ) * ((X + iterSum m B).card : ℝ) := by
    exact_mod_cast ruzsa_triangle_inequality_add X (iterSum n B) (iterSum m B)
  have hmul : (X.card : ℝ) * ((iterSum n B - iterSum m B).card : ℝ) ≤
      (X.card : ℝ) * (K ^ (n + m) * (X.card : ℝ)) := by
    calc (X.card : ℝ) * ((iterSum n B - iterSum m B).card : ℝ)
        ≤ ((X + iterSum n B).card : ℝ) * ((X + iterSum m B).card : ℝ) := htri
      _ ≤ (K ^ n * (X.card : ℝ)) * (K ^ m * (X.card : ℝ)) :=
          mul_le_mul hn hm (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hK0 n) (Nat.cast_nonneg _))
      _ = (X.card : ℝ) * (K ^ (n + m) * (X.card : ℝ)) := by
          rw [pow_add]; ring
  have hXleA : (X.card : ℝ) ≤ (A.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hXA)
  calc ((iterSum n B - iterSum m B).card : ℝ)
      ≤ K ^ (n + m) * (X.card : ℝ) := le_of_mul_le_mul_left hmul hXpos
    _ ≤ K ^ (n + m) * (A.card : ℝ) :=
        mul_le_mul_of_nonneg_left hXleA (pow_nonneg hK0 _)

/-- **Plünnecke–Ruzsa Inequality** (pure iterated sumset specialization `m = 0`):
If `A` is nonempty, `0 ≤ K`, and `|A + B| ≤ K · |A|`, then `|nB| ≤ K^n · |A|`. -/
theorem pluennecke_ruzsa_sum (A B : Finset G) (hA : A.Nonempty)
    {K : ℝ} (hK0 : 0 ≤ K) (hAB : ((A + B).card : ℝ) ≤ K * (A.card : ℝ)) (n : ℕ) :
    ((iterSum n B).card : ℝ) ≤ K ^ n * (A.card : ℝ) := by
  have h := pluennecke_ruzsa A B hA hK0 hAB n 0
  simpa [iterSum_zero, card_sub_zero_singleton] using h

end PluenneckeRuzsa

/-! ### Section 3: Additive Energy & Quantitative Balog–Szemerédi–Gowers Theorem -/

section AdditiveEnergyAndBSG

/-- Elementary Cauchy–Schwarz inequality on a finite index set over `ℝ`:
`(∑ i ∈ s, f i)^2 ≤ |s| · ∑ i ∈ s, (f i)^2`. -/
lemma sq_sum_le_card_mul_sum_sq_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  have hnonneg : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexpand : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
      2 * ((s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 - (∑ i ∈ s, f i) ^ 2) := by
    have h1 : ∀ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
        (s.card : ℝ) * (f i) ^ 2 - 2 * f i * (∑ j ∈ s, f j) + ∑ j ∈ s, (f j) ^ 2 := by
      intro i _
      have : ∀ j ∈ s, (f i - f j) ^ 2 = (f i) ^ 2 - 2 * f i * f j + (f j) ^ 2 := by
        intro j _; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ i ∈ s, (2 * f i * ∑ j ∈ s, f j) = 2 * (∑ i ∈ s, f i) ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
    rw [h2]
    ring
  linarith

section EnergyDefs

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Number of additive representations `a + b = s` with `a ∈ A, b ∈ B`. -/
def addRep (A B : Finset G) (s : G) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 + p.2 = s)).card

/-- Number of difference representations `a - b = d` with `a ∈ A, b ∈ B`. -/
def subRep (A B : Finset G) (d : G) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 - p.2 = d)).card

/-- Additive energy `E(A, B) = |{(a₁, b₁, a₂, b₂) ∈ A × B × A × B : a₁ + b₁ = a₂ + b₂}|`. -/
def addEnergy (A B : Finset G) : ℕ :=
  (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun p => p.1.1 + p.1.2 = p.2.1 + p.2.2)).card

lemma sum_addRep (A B : Finset G) : ∑ s ∈ A + B, addRep A B s = A.card * B.card := by
  have hmaps : ∀ p ∈ A ×ˢ B, p.1 + p.2 ∈ A + B := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact Finset.add_mem_add hp.1 hp.2
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_product] at h
  exact h.symm

lemma addEnergy_eq_sum_sq_addRep (A B : Finset G) :
    addEnergy A B = ∑ s ∈ A + B, (addRep A B s) ^ 2 := by
  classical
  let E4 : Finset ((G × G) × (G × G)) :=
    ((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun p => p.1.1 + p.1.2 = p.2.1 + p.2.2)
  have hmaps : ∀ p ∈ E4, p.1.1 + p.1.2 ∈ A + B := by
    intro p hp
    simp only [E4, Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.add_mem_add hp.1.1.1 hp.1.1.2
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  change E4.card = ∑ s ∈ A + B, (addRep A B s) ^ 2
  rw [hfib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hset : E4.filter (fun p => p.1.1 + p.1.2 = s) =
      ((A ×ˢ B).filter (fun p => p.1 + p.2 = s)) ×ˢ
      ((A ×ˢ B).filter (fun p => p.1 + p.2 = s)) := by
    ext ⟨p₁, p₂⟩
    simp only [E4, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hp₁, hp₂⟩, heq⟩, hs⟩
      exact ⟨⟨hp₁, hs⟩, ⟨hp₂, heq.symm.trans hs⟩⟩
    · rintro ⟨⟨hp₁, hs₁⟩, ⟨hp₂, hs₂⟩⟩
      exact ⟨⟨⟨hp₁, hp₂⟩, hs₁.trans hs₂.symm⟩, hs₁⟩
  rw [hset, Finset.card_product, sq, addRep]

lemma addRep_le_left (A B : Finset G) (s : G) : addRep A B s ≤ A.card := by
  unfold addRep
  have hmaps : Set.MapsTo Prod.fst
      (((A ×ˢ B).filter (fun p => p.1 + p.2 = s)) : Set (G × G)) (A : Set G) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact hp.1.1
  have hinj : Set.InjOn Prod.fst
      (((A ×ˢ B).filter (fun p => p.1 + p.2 = s)) : Set (G × G)) := by
    intro p₁ hp₁ p₂ hp₂ hfst
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
    have hsnd : p₁.2 = p₂.2 := by
      have : p₁.1 + p₁.2 = p₁.1 + p₂.2 := by rw [hp₁.2, ← hp₂.2, hfst]
      exact add_left_cancel this
    exact Prod.ext hfst hsnd
  exact Finset.card_le_card_of_injOn Prod.fst hmaps hinj

lemma addRep_le_right (A B : Finset G) (s : G) : addRep A B s ≤ B.card := by
  unfold addRep
  have hmaps : Set.MapsTo Prod.snd
      (((A ×ˢ B).filter (fun p => p.1 + p.2 = s)) : Set (G × G)) (B : Set G) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact hp.1.2
  have hinj : Set.InjOn Prod.snd
      (((A ×ˢ B).filter (fun p => p.1 + p.2 = s)) : Set (G × G)) := by
    intro p₁ hp₁ p₂ hp₂ hsnd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
    have hfst : p₁.1 = p₂.1 := by
      have : p₁.1 + p₁.2 = p₂.1 + p₁.2 := by rw [hp₁.2, ← hp₂.2, hsnd]
      exact add_right_cancel this
    exact Prod.ext hfst hsnd
  exact Finset.card_le_card_of_injOn Prod.snd hmaps hinj

lemma addRep_le_sqrt (A B : Finset G) (s : G) :
    (addRep A B s : ℝ) ≤ Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
  have h1 : (addRep A B s : ℝ) ≤ (A.card : ℝ) := Nat.cast_le.mpr (addRep_le_left A B s)
  have h2 : (addRep A B s : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr (addRep_le_right A B s)
  have hsq : (addRep A B s : ℝ) ^ 2 ≤ (A.card : ℝ) * (B.card : ℝ) := by
    rw [sq]; exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact Real.le_sqrt_of_sq_le hsq

lemma addEnergy_le_left (A B : Finset G) : addEnergy A B ≤ A.card ^ 2 * B.card := by
  rw [addEnergy_eq_sum_sq_addRep]
  calc ∑ s ∈ A + B, (addRep A B s) ^ 2
      ≤ ∑ s ∈ A + B, A.card * addRep A B s := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [sq]; exact Nat.mul_le_mul_right _ (addRep_le_left A B s)
    _ = A.card * ∑ s ∈ A + B, addRep A B s := (Finset.mul_sum _ _ _).symm
    _ = A.card * (A.card * B.card) := by rw [sum_addRep]
    _ = A.card ^ 2 * B.card := by ring

lemma addEnergy_le_right (A B : Finset G) : addEnergy A B ≤ A.card * B.card ^ 2 := by
  rw [addEnergy_eq_sum_sq_addRep]
  calc ∑ s ∈ A + B, (addRep A B s) ^ 2
      ≤ ∑ s ∈ A + B, B.card * addRep A B s := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [sq]; exact Nat.mul_le_mul_right _ (addRep_le_right A B s)
    _ = B.card * ∑ s ∈ A + B, addRep A B s := (Finset.mul_sum _ _ _).symm
    _ = B.card * (A.card * B.card) := by rw [sum_addRep]
    _ = A.card * B.card ^ 2 := by ring

lemma addEnergy_le_three_halves (A B : Finset G) :
    (addEnergy A B : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
  rw [addEnergy_eq_sum_sq_addRep]
  push_cast
  calc ∑ s ∈ A + B, ((addRep A B s : ℝ) ^ 2)
      ≤ ∑ s ∈ A + B, Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) * (addRep A B s : ℝ) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [sq]; exact mul_le_mul_of_nonneg_right (addRep_le_sqrt A B s) (Nat.cast_nonneg _)
    _ = Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) * ∑ s ∈ A + B, (addRep A B s : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ = Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) * ((A.card : ℝ) * (B.card : ℝ)) := by
        have hsum : ∑ s ∈ A + B, (addRep A B s : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by
          exact_mod_cast sum_addRep A B
        rw [hsum]
    _ = (A.card : ℝ) * (B.card : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by ring

/-- Cauchy–Schwarz lower bound on additive energy: `(|A| · |B|)^2 ≤ |A + B| · E(A, B)`. -/
theorem cauchy_schwarz_addEnergy (A B : Finset G) :
    (A.card * B.card) ^ 2 ≤ (A + B).card * addEnergy A B := by
  have hcs := sq_sum_le_card_mul_sum_sq_real (A + B) (fun s => (addRep A B s : ℝ))
  have hsum : ∑ s ∈ A + B, (addRep A B s : ℝ) = ((A.card * B.card : ℕ) : ℝ) := by
    exact_mod_cast sum_addRep A B
  have hsq : ∑ s ∈ A + B, (addRep A B s : ℝ) ^ 2 = (addEnergy A B : ℝ) := by
    rw [addEnergy_eq_sum_sq_addRep]; push_cast; rfl
  rw [hsum, hsq] at hcs
  exact_mod_cast hcs

end EnergyDefs

section GraphBSG

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Length-3 paths from `a ∈ A` to `b ∈ B` in a bipartite graph `E ⊆ A ×ˢ B`:
pairs `(b', a') ∈ B ×ˢ A` such that `(a, b') ∈ E`, `(a', b') ∈ E`, and `(a', b) ∈ E`. -/
def paths3 (A : Finset α) (B : Finset β) (E : Finset (α × β)) (a : α) (b : β) :
    Finset (β × α) :=
  (B ×ˢ A).filter (fun p => (a, p.1) ∈ E ∧ (p.2, p.1) ∈ E ∧ (p.2, b) ∈ E)

/-- **Sudakov–Szemerédi–Vu Graph BSG Lemma (Paths of Length 3)**:
In any bipartite graph `E ⊆ A ×ˢ B` with density `|E| ≥ δ · |A| · |B|` (`δ > 0`),
there exist subsets `A' ⊆ A` and `B' ⊆ B` with `|A'| ≥ (δ / 8) |A|` and
`|B'| ≥ (δ / 4) |B|` such that every `(a, b) ∈ A' × B'` is joined by at least
`(δ^5 / 16384) · |A| · |B|` paths of length 3 in `E`. -/
theorem bipartite_paths_of_length_three (A : Finset α) (B : Finset β)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (E : Finset (α × β)) (hE_sub : E ⊆ A ×ˢ B)
    {δ : ℝ} (hδ : 0 < δ) (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' ⊆ A, ∃ B' ⊆ B,
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 4) * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ ^ 5 / 16384) * (A.card : ℝ) * (B.card : ℝ) ≤ ((paths3 A B E a b).card : ℝ) := by
  classical
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.mpr hB.card_pos
  -- Neighborhoods in E
  let N_B : α → Finset β := fun a => B.filter (fun b => (a, b) ∈ E)
  let N_A : β → Finset α := fun b => A.filter (fun a => (a, b) ∈ E)
  let codeg : α → α → ℕ := fun a₁ a₂ => (N_B a₁ ∩ N_B a₂).card
  -- Step 1: Trim low-degree vertices from A
  let A₁ : Finset α := A.filter (fun a => (δ / 2) * (B.card : ℝ) ≤ ((N_B a).card : ℝ))
  let E₁ : Finset (α × β) := E.filter (fun p => p.1 ∈ A₁)
  let N₁ : β → Finset α := fun b => A₁.filter (fun a => (a, b) ∈ E)
  have hE_eq_sum : E.card = ∑ a ∈ A, (N_B a).card := by
    have hmaps : ∀ p ∈ E, p.1 ∈ A := fun p hp => (Finset.mem_product.mp (hE_sub hp)).1
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hbij : E.filter (fun p => p.1 = a) = (N_B a).image (fun b => (a, b)) := by
      ext ⟨a', b'⟩
      simp only [N_B, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hp, rfl⟩
        exact ⟨b', ⟨(Finset.mem_product.mp (hE_sub hp)).2, hp⟩, rfl⟩
      · rintro ⟨b, ⟨_, hmem⟩, hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        exact ⟨hmem, rfl⟩
    rw [hbij, Finset.card_image_of_injective _ (fun b₁ b₂ h => (Prod.mk.inj h).2)]
  have hE₁_eq_sumA : E₁.card = ∑ a ∈ A₁, (N_B a).card := by
    have hmaps : ∀ p ∈ E₁, p.1 ∈ A₁ := fun p hp => (Finset.mem_filter.mp hp).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hbij : E₁.filter (fun p => p.1 = a) = (N_B a).image (fun b => (a, b)) := by
      ext ⟨a', b'⟩
      simp only [E₁, N_B, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨hp, _⟩, rfl⟩
        exact ⟨b', ⟨(Finset.mem_product.mp (hE_sub hp)).2, hp⟩, rfl⟩
      · rintro ⟨b, ⟨_, hmem⟩, hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        exact ⟨⟨hmem, ha⟩, rfl⟩
    rw [hbij, Finset.card_image_of_injective _ (fun b₁ b₂ h => (Prod.mk.inj h).2)]
  have hE₁_eq_sumB : E₁.card = ∑ b ∈ B, (N₁ b).card := by
    have hmaps : ∀ p ∈ E₁, p.2 ∈ B := fun p hp =>
      (Finset.mem_product.mp (hE_sub (Finset.mem_filter.mp hp).1)).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbij : E₁.filter (fun p => p.2 = b) = (N₁ b).image (fun a => (a, b)) := by
      ext ⟨a', b'⟩
      simp only [E₁, N₁, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨hp, ha₁⟩, rfl⟩
        exact ⟨a', ⟨ha₁, hp⟩, rfl⟩
      · rintro ⟨a, ⟨ha₁, hp⟩, hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        exact ⟨⟨hp, ha₁⟩, rfl⟩
    rw [hbij, Finset.card_image_of_injective _ (fun a₁ a₂ h => (Prod.mk.inj h).1)]
  have hE₁_dense : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    have hsplit : (E.card : ℝ) = (E₁.card : ℝ) + ∑ a ∈ A \ A₁, ((N_B a).card : ℝ) := by
      have hsub : A₁ ⊆ A := Finset.filter_subset _ _
      have hunion : A = A₁ ∪ (A \ A₁) := (Finset.union_sdiff_of_subset hsub).symm
      have hdisj : Disjoint A₁ (A \ A₁) := Finset.disjoint_sdiff
      have hnat : E.card = E₁.card + ∑ a ∈ A \ A₁, (N_B a).card := by
        rw [hE_eq_sum, hE₁_eq_sumA]
        conv_lhs => rw [hunion]
        exact Finset.sum_union hdisj
      exact_mod_cast hnat
    have hlow : ∑ a ∈ A \ A₁, ((N_B a).card : ℝ) ≤ (δ / 2) * (A.card : ℝ) * (B.card : ℝ) := by
      calc ∑ a ∈ A \ A₁, ((N_B a).card : ℝ)
          ≤ ∑ _a ∈ A \ A₁, ((δ / 2) * (B.card : ℝ)) := by
            refine Finset.sum_le_sum fun a ha => ?_
            rw [Finset.mem_sdiff] at ha
            have hnot : ¬ ((δ / 2) * (B.card : ℝ) ≤ ((N_B a).card : ℝ)) := by
              intro hle; exact ha.2 (Finset.mem_filter.mpr ⟨ha.1, hle⟩)
            linarith
        _ = ((A \ A₁).card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
            have hle : ((A \ A₁).card : ℝ) ≤ (A.card : ℝ) :=
              Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
            exact mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (δ / 2) * (A.card : ℝ) * (B.card : ℝ) := by ring
    linarith
  -- Step 2: Cauchy–Schwarz on ∑_{b ∈ B} |N₁(b)|^2
  have hsum_sq : (δ ^ 2 / 4) * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤
      ∑ b ∈ B, ((N₁ b).card : ℝ) ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq_real B (fun b => ((N₁ b).card : ℝ))
    have hsumE₁ : ∑ b ∈ B, ((N₁ b).card : ℝ) = (E₁.card : ℝ) := by
      exact_mod_cast hE₁_eq_sumB.symm
    rw [hsumE₁] at hcs
    have hsq : ((δ / 2) * (A.card : ℝ) * (B.card : ℝ)) ^ 2 ≤ (E₁.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hE₁_dense 2
    have hmul : (B.card : ℝ) * ((δ ^ 2 / 4) * (A.card : ℝ) ^ 2 * (B.card : ℝ)) ≤
        (B.card : ℝ) * ∑ b ∈ B, ((N₁ b).card : ℝ) ^ 2 := by
      calc (B.card : ℝ) * ((δ ^ 2 / 4) * (A.card : ℝ) ^ 2 * (B.card : ℝ))
          = ((δ / 2) * (A.card : ℝ) * (B.card : ℝ)) ^ 2 := by ring
        _ ≤ (E₁.card : ℝ) ^ 2 := hsq
        _ ≤ (B.card : ℝ) * ∑ b ∈ B, ((N₁ b).card : ℝ) ^ 2 := hcs
    exact le_of_mul_le_mul_left hmul hBpos
  -- Step 3: Parameters γ = 32 / δ, ε = δ^3 / 256, bad pairs inside N₁(b) × N₁(b)
  let γ : ℝ := 32 / δ
  let ε : ℝ := δ ^ 3 / 256
  have hγpos : 0 < γ := by positivity
  have hεpos : 0 < ε := by positivity
  let badPairs : β → Finset (α × α) := fun b =>
    (N₁ b ×ˢ N₁ b).filter (fun p => (codeg p.1 p.2 : ℝ) < ε * (B.card : ℝ))
  -- Double count ∑_{b ∈ B} |badPairs(b)| ≤ |A|^2 · ε |B|
  have hsum_bad : ∑ b ∈ B, ((badPairs b).card : ℝ) ≤
      (A.card : ℝ) ^ 2 * (ε * (B.card : ℝ)) := by
    let badAll : Finset (α × α) :=
      (A₁ ×ˢ A₁).filter (fun p => (codeg p.1 p.2 : ℝ) < ε * (B.card : ℝ))
    have hswap : ∑ b ∈ B, (badPairs b).card = ∑ p ∈ badAll, codeg p.1 p.2 := by
      calc ∑ b ∈ B, (badPairs b).card
          = ∑ b ∈ B, ∑ p ∈ badAll, (if p ∈ badPairs b then 1 else 0) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            have hsub : badPairs b ⊆ badAll := by
              intro p hp
              simp only [badPairs, badAll, N₁, Finset.mem_filter, Finset.mem_product] at hp ⊢
              exact ⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.2⟩
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub,
                Finset.sum_const, smul_eq_mul, mul_one]
        _ = ∑ p ∈ badAll, ∑ b ∈ B, (if p ∈ badPairs b then 1 else 0) := Finset.sum_comm
        _ = ∑ p ∈ badAll, codeg p.1 p.2 := by
            refine Finset.sum_congr rfl fun p hp => ?_
            simp only [badAll, Finset.mem_filter, Finset.mem_product] at hp
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
            congr 1
            ext b
            simp only [badPairs, N₁, N_B, Finset.mem_filter, Finset.mem_product, Finset.mem_inter]
            exact ⟨fun ⟨hb, ⟨⟨_, h1⟩, ⟨_, h2⟩⟩, _⟩ => ⟨⟨hb, h1⟩, ⟨hb, h2⟩⟩,
                   fun ⟨⟨hb, h1⟩, ⟨_, h2⟩⟩ => ⟨hb, ⟨⟨hp.1.1, h1⟩, ⟨hp.1.2, h2⟩⟩, hp.2⟩⟩
    have hswapR : ∑ b ∈ B, ((badPairs b).card : ℝ) = ∑ p ∈ badAll, (codeg p.1 p.2 : ℝ) := by
      exact_mod_cast hswap
    rw [hswapR]
    calc ∑ p ∈ badAll, (codeg p.1 p.2 : ℝ)
        ≤ ∑ _p ∈ badAll, (ε * (B.card : ℝ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          exact le_of_lt (Finset.mem_filter.mp hp).2
      _ = (badAll.card : ℝ) * (ε * (B.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A.card : ℝ) ^ 2 * (ε * (B.card : ℝ)) := by
          have hsub : badAll ⊆ A ×ˢ A := by
            intro p hp
            simp only [badAll, A₁, Finset.mem_filter, Finset.mem_product] at hp ⊢
            exact ⟨hp.1.1.1, hp.1.2.1⟩
          have hle : (badAll.card : ℝ) ≤ (A.card : ℝ) ^ 2 := by
            have hnat : badAll.card ≤ (A ×ˢ A).card := Finset.card_le_card hsub
            rw [Finset.card_product, ← sq] at hnat
            exact_mod_cast hnat
          exact mul_le_mul_of_nonneg_right hle (by positivity)
  -- Step 4: Averaging over b ∈ B yields b₀ ∈ B with large |N₁(b₀)|^2 - γ |badPairs(b₀)|
  have havg : (δ ^ 2 / 8) * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤
      ∑ b ∈ B, (((N₁ b).card : ℝ) ^ 2 - γ * ((badPairs b).card : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hγε : γ * ε = δ ^ 2 / 8 := by
      simp only [γ, ε]; field_simp; ring
    have hmul_bad : γ * ∑ b ∈ B, ((badPairs b).card : ℝ) ≤
        (δ ^ 2 / 8) * (A.card : ℝ) ^ 2 * (B.card : ℝ) := by
      calc γ * ∑ b ∈ B, ((badPairs b).card : ℝ)
          ≤ γ * ((A.card : ℝ) ^ 2 * (ε * (B.card : ℝ))) :=
            mul_le_mul_of_nonneg_left hsum_bad (le_of_lt hγpos)
        _ = (γ * ε) * (A.card : ℝ) ^ 2 * (B.card : ℝ) := by ring
        _ = (δ ^ 2 / 8) * (A.card : ℝ) ^ 2 * (B.card : ℝ) := by rw [hγε]
    linarith
  have hex_b₀ : ∃ b₀ ∈ B, (δ ^ 2 / 8) * (A.card : ℝ) ^ 2 ≤
      ((N₁ b₀).card : ℝ) ^ 2 - γ * ((badPairs b₀).card : ℝ) := by
    by_contra hcontra
    push Not at hcontra
    have hlt : ∑ b ∈ B, (((N₁ b).card : ℝ) ^ 2 - γ * ((badPairs b).card : ℝ)) <
        ∑ _b ∈ B, ((δ ^ 2 / 8) * (A.card : ℝ) ^ 2) :=
      Finset.sum_lt_sum_of_nonempty hB hcontra
    rw [Finset.sum_const, nsmul_eq_mul] at hlt
    linarith
  obtain ⟨b₀, _hb₀B, hb₀_ineq⟩ := hex_b₀
  -- Consequences for N₁(b₀)
  have hN₁b₀_lb : (δ / 4) * (A.card : ℝ) ≤ ((N₁ b₀).card : ℝ) := by
    have hsq : ((δ / 4) * (A.card : ℝ)) ^ 2 ≤ ((N₁ b₀).card : ℝ) ^ 2 := by
      have hbad_nn : 0 ≤ γ * ((badPairs b₀).card : ℝ) := by positivity
      have h1 : (δ ^ 2 / 8) * (A.card : ℝ) ^ 2 ≤ ((N₁ b₀).card : ℝ) ^ 2 := by linarith
      nlinarith
    have hnn : 0 ≤ (δ / 4) * (A.card : ℝ) := by positivity
    nlinarith [sq_nonneg (((N₁ b₀).card : ℝ) - (δ / 4) * (A.card : ℝ))]
  have hN₁b₀_pos : (0 : ℝ) < ((N₁ b₀).card : ℝ) := lt_of_lt_of_le (by positivity) hN₁b₀_lb
  have hbad_b₀_ub : ((badPairs b₀).card : ℝ) ≤ (δ / 32) * ((N₁ b₀).card : ℝ) ^ 2 := by
    have h1 : γ * ((badPairs b₀).card : ℝ) ≤ ((N₁ b₀).card : ℝ) ^ 2 := by
      have hnn : 0 ≤ (δ ^ 2 / 8) * (A.card : ℝ) ^ 2 := by positivity
      linarith
    have h2 : ((badPairs b₀).card : ℝ) ≤ ((N₁ b₀).card : ℝ) ^ 2 / γ :=
      (le_div_iff₀' hγpos).mpr h1
    have hdiv : ((N₁ b₀).card : ℝ) ^ 2 / γ = (δ / 32) * ((N₁ b₀).card : ℝ) ^ 2 := by
      simp only [γ]; field_simp
    linarith
  -- Step 5: Define A' ⊆ N₁(b₀) by removing vertices with too many bad partners
  let badDeg : α → ℕ := fun a =>
    ((N₁ b₀).filter (fun a' => (codeg a a' : ℝ) < ε * (B.card : ℝ))).card
  have hsum_badDeg : ∑ a ∈ N₁ b₀, (badDeg a : ℝ) = ((badPairs b₀).card : ℝ) := by
    have hnat : (badPairs b₀).card = ∑ a ∈ N₁ b₀, badDeg a := by
      have hmaps : ∀ p ∈ badPairs b₀, p.1 ∈ N₁ b₀ := by
        intro p hp
        simp only [badPairs, Finset.mem_filter, Finset.mem_product] at hp
        exact hp.1.1
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hbij : (badPairs b₀).filter (fun p => p.1 = a) =
          ((N₁ b₀).filter (fun a' => (codeg a a' : ℝ) < ε * (B.card : ℝ))).image
            (fun a' => (a, a')) := by
        ext ⟨a₁, a₂⟩
        simp only [badPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        constructor
        · rintro ⟨⟨⟨_, ha₂⟩, hlt⟩, rfl⟩
          exact ⟨a₂, ⟨ha₂, hlt⟩, rfl⟩
        · rintro ⟨a', ⟨ha', hlt⟩, hpair⟩
          rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
          exact ⟨⟨⟨ha, ha'⟩, hlt⟩, rfl⟩
      rw [hbij, Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)]
    exact_mod_cast hnat.symm
  let A' : Finset α :=
    (N₁ b₀).filter (fun a => (badDeg a : ℝ) ≤ (δ / 16) * ((N₁ b₀).card : ℝ))
  have hA'_sub_N₁ : A' ⊆ N₁ b₀ := Finset.filter_subset _ _
  have hA'_sub_A₁ : A' ⊆ A₁ := fun a ha => (Finset.mem_filter.mp (hA'_sub_N₁ ha)).1
  have hA'_sub_A : A' ⊆ A := fun a ha => (Finset.mem_filter.mp (hA'_sub_A₁ ha)).1
  have hA'_half : (1 / 2 : ℝ) * ((N₁ b₀).card : ℝ) ≤ (A'.card : ℝ) := by
    have hsdiff_ub : (((N₁ b₀) \ A').card : ℝ) * ((δ / 16) * ((N₁ b₀).card : ℝ)) ≤
        (δ / 32) * ((N₁ b₀).card : ℝ) ^ 2 := by
      calc (((N₁ b₀) \ A').card : ℝ) * ((δ / 16) * ((N₁ b₀).card : ℝ))
          = ∑ _a ∈ (N₁ b₀) \ A', ((δ / 16) * ((N₁ b₀).card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ a ∈ (N₁ b₀) \ A', (badDeg a : ℝ) := by
            refine Finset.sum_le_sum fun a ha => ?_
            rw [Finset.mem_sdiff] at ha
            have hnot : ¬ ((badDeg a : ℝ) ≤ (δ / 16) * ((N₁ b₀).card : ℝ)) := by
              intro hle; exact ha.2 (Finset.mem_filter.mpr ⟨ha.1, hle⟩)
            linarith
        _ ≤ ∑ a ∈ N₁ b₀, (badDeg a : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
        _ = ((badPairs b₀).card : ℝ) := hsum_badDeg
        _ ≤ (δ / 32) * ((N₁ b₀).card : ℝ) ^ 2 := hbad_b₀_ub
    have hfac_pos : 0 < (δ / 16) * ((N₁ b₀).card : ℝ) := by positivity
    have hsdiff_half : (((N₁ b₀) \ A').card : ℝ) ≤ (1 / 2 : ℝ) * ((N₁ b₀).card : ℝ) := by
      have : (((N₁ b₀) \ A').card : ℝ) * ((δ / 16) * ((N₁ b₀).card : ℝ)) ≤
          ((1 / 2 : ℝ) * ((N₁ b₀).card : ℝ)) * ((δ / 16) * ((N₁ b₀).card : ℝ)) := by
        linarith
      exact le_of_mul_le_mul_right this hfac_pos
    have hcard_eq : ((N₁ b₀).card : ℝ) = (A'.card : ℝ) + (((N₁ b₀) \ A').card : ℝ) := by
      have hnat : (N₁ b₀).card = A'.card + ((N₁ b₀) \ A').card := by
        rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff,
            Finset.union_sdiff_of_subset hA'_sub_N₁]
      exact_mod_cast hnat
    linarith
  have hA'_lb : (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) := by linarith
  have hA'_pos : (0 : ℝ) < (A'.card : ℝ) := lt_of_lt_of_le (by positivity) hA'_lb
  -- Step 6: Define B' ⊆ B as vertices with ≥ (δ/4) |A'| neighbors in A'
  let degA' : β → ℕ := fun b => (A'.filter (fun a => (a, b) ∈ E)).card
  let B' : Finset β := B.filter (fun b => (δ / 4) * (A'.card : ℝ) ≤ (degA' b : ℝ))
  have hB'_sub_B : B' ⊆ B := Finset.filter_subset _ _
  have hB'_lb : (δ / 4) * (B.card : ℝ) ≤ (B'.card : ℝ) := by
    have hdouble : ∑ b ∈ B, degA' b = ∑ a ∈ A', (N_B a).card := by
      calc ∑ b ∈ B, degA' b
          = ∑ b ∈ B, ∑ a ∈ A', (if (a, b) ∈ E then 1 else 0) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        _ = ∑ a ∈ A', ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := Finset.sum_comm
        _ = ∑ a ∈ A', (N_B a).card := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have hsum_ge : (δ / 2) * (A'.card : ℝ) * (B.card : ℝ) ≤ ∑ b ∈ B, (degA' b : ℝ) := by
      have hdoubleR : ∑ b ∈ B, (degA' b : ℝ) = ∑ a ∈ A', ((N_B a).card : ℝ) := by
        exact_mod_cast hdouble
      rw [hdoubleR]
      calc (δ / 2) * (A'.card : ℝ) * (B.card : ℝ)
          = ∑ _a ∈ A', ((δ / 2) * (B.card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ a ∈ A', ((N_B a).card : ℝ) := by
            refine Finset.sum_le_sum fun a ha => ?_
            exact (Finset.mem_filter.mp (hA'_sub_A₁ ha)).2
    have hsplitB : ∑ b ∈ B, (degA' b : ℝ) =
        ∑ b ∈ B', (degA' b : ℝ) + ∑ b ∈ B \ B', (degA' b : ℝ) := by
      have hunion : B = B' ∪ (B \ B') := (Finset.union_sdiff_of_subset hB'_sub_B).symm
      conv_lhs => rw [hunion]
      exact Finset.sum_union Finset.disjoint_sdiff
    have hpart1 : ∑ b ∈ B', (degA' b : ℝ) ≤ (B'.card : ℝ) * (A'.card : ℝ) := by
      calc ∑ b ∈ B', (degA' b : ℝ)
          ≤ ∑ _b ∈ B', (A'.card : ℝ) := by
            refine Finset.sum_le_sum fun b _ => ?_
            exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
        _ = (B'.card : ℝ) * (A'.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hpart2 : ∑ b ∈ B \ B', (degA' b : ℝ) ≤ (B.card : ℝ) * ((δ / 4) * (A'.card : ℝ)) := by
      calc ∑ b ∈ B \ B', (degA' b : ℝ)
          ≤ ∑ _b ∈ B \ B', ((δ / 4) * (A'.card : ℝ)) := by
            refine Finset.sum_le_sum fun b hb => ?_
            rw [Finset.mem_sdiff] at hb
            have hnot : ¬ ((δ / 4) * (A'.card : ℝ) ≤ (degA' b : ℝ)) := by
              intro hle; exact hb.2 (Finset.mem_filter.mpr ⟨hb.1, hle⟩)
            linarith
        _ = ((B \ B').card : ℝ) * ((δ / 4) * (A'.card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (B.card : ℝ) * ((δ / 4) * (A'.card : ℝ)) := by
            have hle : ((B \ B').card : ℝ) ≤ (B.card : ℝ) :=
              Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
            exact mul_le_mul_of_nonneg_right hle (by positivity)
    have hmul : ((δ / 4) * (B.card : ℝ)) * (A'.card : ℝ) ≤ (B'.card : ℝ) * (A'.card : ℝ) := by
      linarith
    exact le_of_mul_le_mul_right hmul hA'_pos
  -- Step 7: Count length-3 paths for every a ∈ A' and b ∈ B'
  refine ⟨A', hA'_sub_A, B', hB'_sub_B, hA'_lb, hB'_lb, ?_⟩
  intro a ha b hb
  let neigh : Finset α := A'.filter (fun a' => (a', b) ∈ E)
  let good : Finset α := neigh.filter (fun a' => ε * (B.card : ℝ) ≤ (codeg a a' : ℝ))
  let badInNeigh : Finset α := neigh.filter (fun a' => (codeg a a' : ℝ) < ε * (B.card : ℝ))
  have hbad_sub : badInNeigh ⊆ (N₁ b₀).filter (fun a' => (codeg a a' : ℝ) < ε * (B.card : ℝ)) := by
    intro a' ha'
    simp only [badInNeigh, neigh, Finset.mem_filter] at ha' ⊢
    exact ⟨hA'_sub_N₁ ha'.1.1, ha'.2⟩
  have hgood_lb : (δ ^ 2 / 64) * (A.card : ℝ) ≤ (good.card : ℝ) := by
    have hsplit : (neigh.card : ℝ) = (good.card : ℝ) + (badInNeigh.card : ℝ) := by
      have hnat : neigh.card = good.card + badInNeigh.card := by
        have hdisj : Disjoint good badInNeigh := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have h1 := (Finset.mem_filter.mp hx1).2
          have h2 := (Finset.mem_filter.mp hx2).2
          linarith
        have hunion : good ∪ badInNeigh = neigh := by
          ext x
          simp only [good, badInNeigh, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
          · intro hx
            by_cases hle : ε * (B.card : ℝ) ≤ (codeg a x : ℝ)
            · exact Or.inl ⟨hx, hle⟩
            · exact Or.inr ⟨hx, lt_of_not_ge hle⟩
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      exact_mod_cast hnat
    have hneigh_ge : (δ / 8) * ((N₁ b₀).card : ℝ) ≤ (neigh.card : ℝ) := by
      have hb_deg : (δ / 4) * (A'.card : ℝ) ≤ (neigh.card : ℝ) := (Finset.mem_filter.mp hb).2
      linarith [mul_le_mul_of_nonneg_left hA'_half (show (0 : ℝ) ≤ δ / 4 by positivity)]
    have hbad_le : (badInNeigh.card : ℝ) ≤ (δ / 16) * ((N₁ b₀).card : ℝ) := by
      have h1 : (badInNeigh.card : ℝ) ≤ (badDeg a : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hbad_sub)
      have h2 : (badDeg a : ℝ) ≤ (δ / 16) * ((N₁ b₀).card : ℝ) := (Finset.mem_filter.mp ha).2
      linarith
    have hgood_N₁ : (δ / 16) * ((N₁ b₀).card : ℝ) ≤ (good.card : ℝ) := by linarith
    calc (δ ^ 2 / 64) * (A.card : ℝ)
        = (δ / 16) * ((δ / 4) * (A.card : ℝ)) := by ring
      _ ≤ (δ / 16) * ((N₁ b₀).card : ℝ) :=
          mul_le_mul_of_nonneg_left hN₁b₀_lb (by positivity)
      _ ≤ (good.card : ℝ) := hgood_N₁
  -- Express lower bound on |(paths3 A B E a b)| via ∑_{a' ∈ good} codeg a a'
  have hpaths_ge_sum : ∑ a' ∈ good, codeg a a' ≤ (paths3 A B E a b).card := by
    have hmaps : ∀ p ∈ paths3 A B E a b, p.2 ∈ A := by
      intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hgood_sub_A : good ⊆ A := fun a' ha' =>
      hA'_sub_A (Finset.mem_filter.mp (Finset.mem_filter.mp ha').1).1
    calc ∑ a' ∈ good, codeg a a'
        ≤ ∑ a' ∈ good, ((paths3 A B E a b).filter (fun p => p.2 = a')).card := by
          refine Finset.sum_le_sum fun a' ha' => ?_
          have ha'b : (a', b) ∈ E := (Finset.mem_filter.mp (Finset.mem_filter.mp ha').1).2
          have ha'A : a' ∈ A := hgood_sub_A ha'
          have hbij : (paths3 A B E a b).filter (fun p => p.2 = a') =
              (N_B a ∩ N_B a').image (fun b' => (b', a')) := by
            ext ⟨b₁, a₁⟩
            simp only [paths3, N_B, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
              Finset.mem_inter]
            constructor
            · rintro ⟨⟨⟨hb₁, _⟩, h1, h2, _⟩, rfl⟩
              exact ⟨b₁, ⟨⟨hb₁, h1⟩, ⟨hb₁, h2⟩⟩, rfl⟩
            · rintro ⟨b', ⟨⟨hb', h1⟩, ⟨_, h2⟩⟩, hpair⟩
              rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
              exact ⟨⟨⟨hb', ha'A⟩, h1, h2, ha'b⟩, rfl⟩
          rw [hbij, Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]
      _ ≤ ∑ a' ∈ A, ((paths3 A B E a b).filter (fun p => p.2 = a')).card :=
          Finset.sum_le_sum_of_subset hgood_sub_A
  have hpaths_ge_sumR : ∑ a' ∈ good, (codeg a a' : ℝ) ≤ ((paths3 A B E a b).card : ℝ) := by
    exact_mod_cast hpaths_ge_sum
  calc (δ ^ 5 / 16384) * (A.card : ℝ) * (B.card : ℝ)
      = ((δ ^ 2 / 64) * (A.card : ℝ)) * (ε * (B.card : ℝ)) := by
        simp only [ε]; ring
    _ ≤ (good.card : ℝ) * (ε * (B.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hgood_lb (by positivity)
    _ = ∑ _a' ∈ good, (ε * (B.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a' ∈ good, (codeg a a' : ℝ) :=
        Finset.sum_le_sum fun a' ha' => (Finset.mem_filter.mp ha').2
    _ ≤ ((paths3 A B E a b).card : ℝ) := hpaths_ge_sumR

end GraphBSG

section QuantitativeBSG

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Path-counting sumset bound: if every `(a, b) ∈ A' × B'` has at least `M` length-3 paths
in a bipartite graph `E ⊆ A ×ˢ B` whose edge-sums lie in `S`, then `M · |A' + B'| ≤ |S|^3`. -/
lemma sumset_card_le_of_paths3 (A B A' B' S : Finset G) (E : Finset (G × G))
    (hES : ∀ p ∈ E, p.1 + p.2 ∈ S)
    {M : ℝ} (hM : ∀ a ∈ A', ∀ b ∈ B', M ≤ ((paths3 A B E a b).card : ℝ)) :
    M * ((A' + B').card : ℝ) ≤ (S.card : ℝ) ^ 3 := by
  classical
  have hrep : ∀ x : G, x ∈ A' + B' → ∃ ab : G × G, ab.1 ∈ A' ∧ ab.2 ∈ B' ∧ ab.1 + ab.2 = x := by
    intro x hx
    rcases Finset.mem_add.mp hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(a, b), ha, hb, hab⟩
  let pickA : G → G := fun x => if h : x ∈ A' + B' then (Classical.choose (hrep x h)).1 else 0
  let pickB : G → G := fun x => if h : x ∈ A' + B' then (Classical.choose (hrep x h)).2 else 0
  have hpickA : ∀ x (h : x ∈ A' + B'), pickA x ∈ A' := by
    intro x h; simp only [pickA, dif_pos h]; exact (Classical.choose_spec (hrep x h)).1
  have hpickB : ∀ x (h : x ∈ A' + B'), pickB x ∈ B' := by
    intro x h; simp only [pickB, dif_pos h]; exact (Classical.choose_spec (hrep x h)).2.1
  have hpickAdd : ∀ x (h : x ∈ A' + B'), pickA x + pickB x = x := by
    intro x h; simp only [pickA, pickB, dif_pos h]; exact (Classical.choose_spec (hrep x h)).2.2
  let dom : Finset (Σ _ : G, G × G) :=
    (A' + B').sigma (fun x => paths3 A B E (pickA x) (pickB x))
  let φ : (Σ _ : G, G × G) → G × (G × G) := fun q =>
    (pickA q.1 + q.2.1, (q.2.2 + q.2.1, q.2.2 + pickB q.1))
  have hmaps : Set.MapsTo φ (dom : Finset (Σ _ : G, G × G))
      ((S ×ˢ (S ×ˢ S)) : Finset (G × (G × G))) := by
    intro q hq
    simp only [dom, Finset.mem_coe, Finset.mem_sigma, paths3, Finset.mem_filter,
      Finset.mem_product] at hq ⊢
    rcases hq with ⟨_, ⟨_, h1, h2, h3⟩⟩
    exact ⟨hES _ h1, hES _ h2, hES _ h3⟩
  have hinj : Set.InjOn φ (dom : Finset (Σ _ : G, G × G)) := by
    intro q₁ hq₁ q₂ hq₂ heq
    simp only [dom, Finset.mem_coe, Finset.mem_sigma] at hq₁ hq₂
    have h1 : pickA q₁.1 + q₁.2.1 = pickA q₂.1 + q₂.2.1 := congrArg Prod.fst heq
    have h2 : q₁.2.2 + q₁.2.1 = q₂.2.2 + q₂.2.1 := congrArg (fun t => t.2.1) heq
    have h3 : q₁.2.2 + pickB q₁.1 = q₂.2.2 + pickB q₂.1 := congrArg (fun t => t.2.2) heq
    have hx : q₁.1 = q₂.1 := by
      calc q₁.1 = pickA q₁.1 + pickB q₁.1 := (hpickAdd q₁.1 hq₁.1).symm
        _ = (pickA q₁.1 + q₁.2.1) - (q₁.2.2 + q₁.2.1) + (q₁.2.2 + pickB q₁.1) := by abel
        _ = (pickA q₂.1 + q₂.2.1) - (q₂.2.2 + q₂.2.1) + (q₂.2.2 + pickB q₂.1) := by
            rw [h1, h2, h3]
        _ = pickA q₂.1 + pickB q₂.1 := by abel
        _ = q₂.1 := hpickAdd q₂.1 hq₂.1
    rw [hx] at h1 h3
    have hb' : q₁.2.1 = q₂.2.1 := add_left_cancel h1
    have ha' : q₁.2.2 = q₂.2.2 := add_right_cancel h3
    cases q₁; cases q₂
    simp only at hx hb' ha'
    subst hx
    congr 1
    exact Prod.ext hb' ha'
  have hcard_nat : dom.card ≤ (S ×ˢ (S ×ˢ S)).card :=
    Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Finset.card_sigma, Finset.card_product, Finset.card_product] at hcard_nat
  have hcard_real : ∑ x ∈ A' + B', ((paths3 A B E (pickA x) (pickB x)).card : ℝ) ≤
      (S.card : ℝ) ^ 3 := by
    have h1 : (∑ x ∈ A' + B', (paths3 A B E (pickA x) (pickB x)).card : ℝ) ≤
        ((S.card * (S.card * S.card) : ℕ) : ℝ) := by exact_mod_cast hcard_nat
    push_cast at h1
    linarith [show (S.card : ℝ) * ((S.card : ℝ) * (S.card : ℝ)) = (S.card : ℝ) ^ 3 by ring]
  calc M * ((A' + B').card : ℝ)
      = ∑ _x ∈ A' + B', M := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ A' + B', ((paths3 A B E (pickA x) (pickB x)).card : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact hM (pickA x) (hpickA x hx) (pickB x) (hpickB x hx)
    _ ≤ (S.card : ℝ) ^ 3 := hcard_real

/-- **Balog–Szemerédi–Gowers (BSG) Quantitative Theorem** (asymmetric form):
If `A, B ⊆ G` are nonempty with additive energy `E(A, B) ≥ c · |A|^(3/2) · |B|^(3/2)` (`c > 0`),
then there exist large subsets `A' ⊆ A` and `B' ⊆ B` such that
- `|A'| ≥ (c / 16) · |A|`,
- `|B'| ≥ (c / 8) · |B|`,
- `|A' + B'| ≤ (2^22 / c^8) · √(|A| · |B|) ≤ (2^22 / c^9) · |A|`. -/
theorem balog_szemeredi_gowers (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hE : c * (A.card : ℝ) * (B.card : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) ≤
      (addEnergy A B : ℝ)) :
    ∃ A' ⊆ A, ∃ B' ⊆ B,
      (c / 16) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (c / 8) * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
      ((A' + B').card : ℝ) ≤ ((2 : ℝ) ^ 22 / c ^ 8) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) ∧
      ((A' + B').card : ℝ) ≤ ((2 : ℝ) ^ 22 / c ^ 9) * (A.card : ℝ) := by
  classical
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.mpr hB.card_pos
  let sqAB : ℝ := Real.sqrt ((A.card : ℝ) * (B.card : ℝ))
  have hsqAB_pos : 0 < sqAB := Real.sqrt_pos.mpr (mul_pos hApos hBpos)
  -- Popular sums S = {s ∈ A + B | r(s) ≥ (c / 2) √(|A||B|)}
  let t : ℝ := (c / 2) * sqAB
  have htpos : 0 < t := by positivity
  let S : Finset G := (A + B).filter (fun s => t ≤ (addRep A B s : ℝ))
  let E : Finset (G × G) := (A ×ˢ B).filter (fun p => p.1 + p.2 ∈ S)
  have hE_sub : E ⊆ A ×ˢ B := Finset.filter_subset _ _
  have hES : ∀ p ∈ E, p.1 + p.2 ∈ S := fun p hp => (Finset.mem_filter.mp hp).2
  -- |E| = ∑_{s ∈ S} addRep A B s
  have hE_card_eq : E.card = ∑ s ∈ S, addRep A B s := by
    have hmaps : ∀ p ∈ E, p.1 + p.2 ∈ S := hES
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun s hs => ?_
    congr 1
    ext p
    simp only [E, Finset.mem_filter]
    exact ⟨fun ⟨⟨hp, _⟩, heq⟩ => ⟨hp, heq⟩,
           fun ⟨hp, heq⟩ => ⟨⟨hp, heq ▸ hs⟩, heq⟩⟩
  -- Unpopular sums contribute at most (c / 2) |A| |B| √(|A| |B|)
  have hunpop : ∑ s ∈ (A + B) \ S, ((addRep A B s : ℝ) ^ 2) ≤
      (c / 2) * (A.card : ℝ) * (B.card : ℝ) * sqAB := by
    calc ∑ s ∈ (A + B) \ S, ((addRep A B s : ℝ) ^ 2)
        ≤ ∑ s ∈ (A + B) \ S, t * (addRep A B s : ℝ) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [Finset.mem_sdiff] at hs
          have hlt : (addRep A B s : ℝ) < t := by
            by_contra hge; exact hs.2 (Finset.mem_filter.mpr ⟨hs.1, not_lt.mp hge⟩)
          rw [sq]
          exact mul_le_mul_of_nonneg_right (le_of_lt hlt) (Nat.cast_nonneg _)
      _ = t * ∑ s ∈ (A + B) \ S, (addRep A B s : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ t * ∑ s ∈ A + B, (addRep A B s : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _))
            (le_of_lt htpos)
      _ = t * ((A.card : ℝ) * (B.card : ℝ)) := by
          have hsum : ∑ s ∈ A + B, (addRep A B s : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by
            exact_mod_cast sum_addRep A B
          rw [hsum]
      _ = (c / 2) * (A.card : ℝ) * (B.card : ℝ) * sqAB := by simp only [t]; ring
  -- Popular sums carry at least (c / 2) |A| |B| √(|A| |B|) energy
  have hpop : (c / 2) * (A.card : ℝ) * (B.card : ℝ) * sqAB ≤
      ∑ s ∈ S, ((addRep A B s : ℝ) ^ 2) := by
    have hsplit : (addEnergy A B : ℝ) =
        ∑ s ∈ S, ((addRep A B s : ℝ) ^ 2) + ∑ s ∈ (A + B) \ S, ((addRep A B s : ℝ) ^ 2) := by
      have hunion : A + B = S ∪ ((A + B) \ S) :=
        (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
      rw [addEnergy_eq_sum_sq_addRep]; push_cast
      conv_lhs => rw [hunion]
      exact Finset.sum_union Finset.disjoint_sdiff
    linarith
  -- Edge density |E| ≥ (c / 2) |A| |B|
  have hE_dense : (c / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) := by
    have h1 : ∑ s ∈ S, ((addRep A B s : ℝ) ^ 2) ≤ sqAB * (E.card : ℝ) := by
      calc ∑ s ∈ S, ((addRep A B s : ℝ) ^ 2)
          ≤ ∑ s ∈ S, sqAB * (addRep A B s : ℝ) := by
            refine Finset.sum_le_sum fun s _ => ?_
            rw [sq]; exact mul_le_mul_of_nonneg_right (addRep_le_sqrt A B s) (Nat.cast_nonneg _)
        _ = sqAB * ∑ s ∈ S, (addRep A B s : ℝ) := (Finset.mul_sum _ _ _).symm
        _ = sqAB * (E.card : ℝ) := by
            have : ∑ s ∈ S, (addRep A B s : ℝ) = (E.card : ℝ) := by exact_mod_cast hE_card_eq.symm
            rw [this]
    have hmul : sqAB * ((c / 2) * (A.card : ℝ) * (B.card : ℝ)) ≤ sqAB * (E.card : ℝ) := by
      linarith
    exact le_of_mul_le_mul_left hmul hsqAB_pos
  -- Upper bound on |S|: |S| ≤ (2 / c) √(|A| |B|)
  have hS_ub : (S.card : ℝ) ≤ (2 / c) * sqAB := by
    have h1 : t * (S.card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := by
      calc t * (S.card : ℝ)
          = ∑ _s ∈ S, t := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ s ∈ S, (addRep A B s : ℝ) :=
            Finset.sum_le_sum fun s hs => (Finset.mem_filter.mp hs).2
        _ = (E.card : ℝ) := by exact_mod_cast hE_card_eq.symm
        _ ≤ ((A ×ˢ B).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hE_sub)
        _ = (A.card : ℝ) * (B.card : ℝ) := by rw [Finset.card_product]; push_cast; rfl
    have hsq_eq : sqAB * sqAB = (A.card : ℝ) * (B.card : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hmul : t * (S.card : ℝ) ≤ t * ((2 / c) * sqAB) := by
      calc t * (S.card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := h1
        _ = sqAB * sqAB := hsq_eq.symm
        _ = t * ((2 / c) * sqAB) := by simp only [t]; field_simp
    exact le_of_mul_le_mul_left hmul htpos
  -- Apply Graph BSG Lemma with δ = c / 2
  obtain ⟨A', hA'A, B', hB'B, hA'lb, hB'lb, hpaths⟩ :=
    bipartite_paths_of_length_three A B hA hB E hE_sub (by positivity : (0 : ℝ) < c / 2) hE_dense
  have hpath_sum := sumset_card_le_of_paths3 A B A' B' S E hES hpaths
  -- Derive |A' + B'| ≤ (2^22 / c^8) √(|A| |B|)
  have hsumset_sqrt :
      ((A' + B').card : ℝ) ≤ ((2 : ℝ) ^ 22 / c ^ 8) * sqAB := by
    have hMpos : 0 < ((c / 2) ^ 5 / 16384) * (A.card : ℝ) * (B.card : ℝ) := by positivity
    have hS3 : (S.card : ℝ) ^ 3 ≤ ((2 / c) * sqAB) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hS_ub 3
    have hsq3 : sqAB ^ 3 = (A.card : ℝ) * (B.card : ℝ) * sqAB := by
      have hsq_eq : sqAB ^ 2 = (A.card : ℝ) * (B.card : ℝ) :=
        Real.sq_sqrt (by positivity)
      calc sqAB ^ 3 = sqAB ^ 2 * sqAB := by ring
        _ = (A.card : ℝ) * (B.card : ℝ) * sqAB := by rw [hsq_eq]
    have hmul :
        (((c / 2) ^ 5 / 16384) * (A.card : ℝ) * (B.card : ℝ)) * ((A' + B').card : ℝ) ≤
        (((c / 2) ^ 5 / 16384) * (A.card : ℝ) * (B.card : ℝ)) * (((2 : ℝ) ^ 22 / c ^ 8) * sqAB) := by
      calc (((c / 2) ^ 5 / 16384) * (A.card : ℝ) * (B.card : ℝ)) * ((A' + B').card : ℝ)
          ≤ (S.card : ℝ) ^ 3 := hpath_sum
        _ ≤ ((2 / c) * sqAB) ^ 3 := hS3
        _ = (8 / c ^ 3) * sqAB ^ 3 := by ring
        _ = (8 / c ^ 3) * ((A.card : ℝ) * (B.card : ℝ) * sqAB) := by rw [hsq3]
        _ = (((c / 2) ^ 5 / 16384) * (A.card : ℝ) * (B.card : ℝ)) * (((2 : ℝ) ^ 22 / c ^ 8) * sqAB) := by
            field_simp; ring
    exact le_of_mul_le_mul_left hmul hMpos
  -- Derive √(|A||B|) ≤ (1/c) |A| from E(A, B) ≤ |A|^2 |B|
  have hsqAB_le_A : sqAB ≤ (1 / c) * (A.card : ℝ) := by
    have hE_ub : (addEnergy A B : ℝ) ≤ (A.card : ℝ) ^ 2 * (B.card : ℝ) := by
      exact_mod_cast addEnergy_le_left A B
    have h1 : c * (A.card : ℝ) * (B.card : ℝ) * sqAB ≤ (A.card : ℝ) ^ 2 * (B.card : ℝ) :=
      hE.trans hE_ub
    have hfac : 0 < c * (A.card : ℝ) * (B.card : ℝ) := by positivity
    have h2 : (c * (A.card : ℝ) * (B.card : ℝ)) * sqAB ≤
        (c * (A.card : ℝ) * (B.card : ℝ)) * ((1 / c) * (A.card : ℝ)) := by
      have : (c * (A.card : ℝ) * (B.card : ℝ)) * ((1 / c) * (A.card : ℝ)) =
          (A.card : ℝ) ^ 2 * (B.card : ℝ) := by field_simp
      linarith
    exact le_of_mul_le_mul_left h2 hfac
  have hsumset_A : ((A' + B').card : ℝ) ≤ ((2 : ℝ) ^ 22 / c ^ 9) * (A.card : ℝ) := by
    calc ((A' + B').card : ℝ)
        ≤ ((2 : ℝ) ^ 22 / c ^ 8) * sqAB := hsumset_sqrt
      _ ≤ ((2 : ℝ) ^ 22 / c ^ 8) * ((1 / c) * (A.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqAB_le_A (by positivity)
      _ = ((2 : ℝ) ^ 22 / c ^ 9) * (A.card : ℝ) := by field_simp
  exact ⟨A', hA'A, B', hB'B, by linarith, by linarith, hsumset_sqrt, hsumset_A⟩

/-- **Balog–Szemerédi–Gowers (BSG) Single-Subset Theorem**:
If `A ⊆ G` is nonempty with additive energy `E(A, A) ≥ |A|^3 / K` (`K > 0`),
then there exists a large subset `A' ⊆ A` with `|A'| ≥ |A| / (16 K)` having small
difference set `|A' - A'| ≤ 2^47 · K^17 · |A|` and small sumset
`|A' + A'| ≤ 2^50 · K^18 · |A|`. -/
theorem balog_szemeredi_gowers_single (A : Finset G) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (hE : (A.card : ℝ) ^ 3 / K ≤ (addEnergy A A : ℝ)) :
    ∃ A' ⊆ A,
      (A.card : ℝ) / (16 * K) ≤ (A'.card : ℝ) ∧
      ((A' - A').card : ℝ) ≤ (2 : ℝ) ^ 47 * K ^ 17 * (A.card : ℝ) ∧
      ((A' + A').card : ℝ) ≤ (2 : ℝ) ^ 50 * K ^ 18 * (A.card : ℝ) := by
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hc : 0 < (1 / K : ℝ) := by positivity
  have hsq : Real.sqrt ((A.card : ℝ) * (A.card : ℝ)) = (A.card : ℝ) :=
    Real.sqrt_mul_self (Nat.cast_nonneg _)
  have hE' : (1 / K) * (A.card : ℝ) * (A.card : ℝ) * Real.sqrt ((A.card : ℝ) * (A.card : ℝ)) ≤
      (addEnergy A A : ℝ) := by
    rw [hsq]
    have : (1 / K) * (A.card : ℝ) * (A.card : ℝ) * (A.card : ℝ) = (A.card : ℝ) ^ 3 / K := by ring
    linarith
  obtain ⟨A', hA'A, B', hB'A, hA'lb, hB'lb, hsum_sqrt, _⟩ :=
    balog_szemeredi_gowers A A hA hA hc hE'
  rw [hsq] at hsum_sqrt
  have hA'lb' : (A.card : ℝ) / (16 * K) ≤ (A'.card : ℝ) := by
    have : (1 / K / 16) * (A.card : ℝ) = (A.card : ℝ) / (16 * K) := by ring
    linarith
  have hB'lb' : (A.card : ℝ) / (8 * K) ≤ (B'.card : ℝ) := by
    have : (1 / K / 8) * (A.card : ℝ) = (A.card : ℝ) / (8 * K) := by ring
    linarith
  have hB'pos : (0 : ℝ) < (B'.card : ℝ) := lt_of_lt_of_le (by positivity) hB'lb'
  have hB'ne : B'.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hB'pos)
  have hsum_ub : ((B' + A').card : ℝ) ≤ (2 : ℝ) ^ 22 * K ^ 8 * (A.card : ℝ) := by
    rw [add_comm B' A']
    have hcoeff : (2 : ℝ) ^ 22 / (1 / K) ^ 8 = (2 : ℝ) ^ 22 * K ^ 8 := by field_simp
    rw [hcoeff] at hsum_sqrt
    exact hsum_sqrt
  -- Difference-set bound via Ruzsa Triangle Inequality
  have hdiff : ((A' - A').card : ℝ) ≤ (2 : ℝ) ^ 47 * K ^ 17 * (A.card : ℝ) := by
    have htri : (B'.card : ℝ) * ((A' - A').card : ℝ) ≤ ((B' + A').card : ℝ) * ((B' + A').card : ℝ) := by
      exact_mod_cast ruzsa_triangle_inequality_add B' A' A'
    have hmul : ((A.card : ℝ) / (8 * K)) * ((A' - A').card : ℝ) ≤
        ((A.card : ℝ) / (8 * K)) * ((2 : ℝ) ^ 47 * K ^ 17 * (A.card : ℝ)) := by
      calc ((A.card : ℝ) / (8 * K)) * ((A' - A').card : ℝ)
          ≤ (B'.card : ℝ) * ((A' - A').card : ℝ) :=
            mul_le_mul_of_nonneg_right hB'lb' (Nat.cast_nonneg _)
        _ ≤ ((B' + A').card : ℝ) * ((B' + A').card : ℝ) := htri
        _ ≤ ((2 : ℝ) ^ 22 * K ^ 8 * (A.card : ℝ)) * ((2 : ℝ) ^ 22 * K ^ 8 * (A.card : ℝ)) :=
            mul_le_mul hsum_ub hsum_ub (Nat.cast_nonneg _) (by positivity)
        _ = ((A.card : ℝ) / (8 * K)) * ((2 : ℝ) ^ 47 * K ^ 17 * (A.card : ℝ)) := by
            field_simp; ring
    exact le_of_mul_le_mul_left hmul (by positivity)
  -- Sumset bound via Plünnecke–Ruzsa applied to (B', A')
  have hsum : ((A' + A').card : ℝ) ≤ (2 : ℝ) ^ 50 * K ^ 18 * (A.card : ℝ) := by
    have hdoub : ((B' + A').card : ℝ) ≤ ((2 : ℝ) ^ 25 * K ^ 9) * (B'.card : ℝ) := by
      calc ((B' + A').card : ℝ)
          ≤ (2 : ℝ) ^ 22 * K ^ 8 * (A.card : ℝ) := hsum_ub
        _ = ((2 : ℝ) ^ 25 * K ^ 9) * ((A.card : ℝ) / (8 * K)) := by field_simp; ring
        _ ≤ ((2 : ℝ) ^ 25 * K ^ 9) * (B'.card : ℝ) :=
            mul_le_mul_of_nonneg_left hB'lb' (by positivity)
    have hpr := pluennecke_ruzsa_sum B' A' hB'ne (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 25 * K ^ 9) hdoub 2
    have hiter2 : iterSum 2 A' = A' + A' := by rw [iterSum_succ, iterSum_one]
    rw [hiter2] at hpr
    have hB'leA : (B'.card : ℝ) ≤ (A.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hB'A)
    calc ((A' + A').card : ℝ)
        ≤ ((2 : ℝ) ^ 25 * K ^ 9) ^ 2 * (B'.card : ℝ) := hpr
      _ ≤ ((2 : ℝ) ^ 25 * K ^ 9) ^ 2 * (A.card : ℝ) :=
          mul_le_mul_of_nonneg_left hB'leA (by positivity)
      _ = (2 : ℝ) ^ 50 * K ^ 18 * (A.card : ℝ) := by ring
  exact ⟨A', hA'A, hA'lb', hdiff, hsum⟩

end QuantitativeBSG

end AdditiveEnergyAndBSG

/-! ### Section 4: Discrete Fourier Analysis over Finite Abelian Groups & `ZMod N` -/

section DiscreteFourier

section FiniteAbelianCharacters

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- In any finite additive abelian group `G`, `|G| • x = 0`. -/
lemma card_nsmul_eq_zero_ab (x : G) : Fintype.card G • x = 0 := by
  have hshift : ∑ y : G, (y + x) = ∑ y : G, y :=
    Fintype.sum_equiv (Equiv.addRight x) _ _ (fun _ => rfl)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hshift
  exact add_left_cancel (hshift.trans (add_zero _).symm)

lemma addChar_nsmul (ψ : AddChar G ℂ) (n : ℕ) (x : G) : ψ (n • x) = ψ x ^ n := by
  induction n with
  | zero => simp [AddChar.map_zero_eq_one]
  | succ k ih => rw [succ_nsmul, AddChar.map_add_eq_mul, ih, pow_succ]

lemma addChar_pow_card_eq_one (ψ : AddChar G ℂ) (x : G) : ψ x ^ Fintype.card G = 1 := by
  rw [← addChar_nsmul, card_nsmul_eq_zero_ab, AddChar.map_zero_eq_one]

/-- Every complex additive character on a finite abelian group takes values on the unit circle. -/
lemma norm_addChar_eq_one (ψ : AddChar G ℂ) (x : G) : ‖ψ x‖ = 1 := by
  have hpow : ‖ψ x‖ ^ Fintype.card G = 1 := by
    rw [← norm_pow, addChar_pow_card_eq_one, norm_one]
  have hpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hnn : 0 ≤ ‖ψ x‖ := norm_nonneg _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : ‖ψ x‖ ^ Fintype.card G < 1 ^ Fintype.card G :=
      pow_lt_pow_left₀ hlt hnn (Nat.ne_of_gt hpos)
    rw [one_pow] at this; linarith
  · have : 1 ^ Fintype.card G < ‖ψ x‖ ^ Fintype.card G :=
      pow_lt_pow_left₀ hgt zero_le_one (Nat.ne_of_gt hpos)
    rw [one_pow] at this; linarith

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.sq_norm]

/-- For any complex additive character on a finite abelian group, `star (ψ x) = ψ (-x)`. -/
lemma star_addChar_eq_neg (ψ : AddChar G ℂ) (x : G) : star (ψ x) = ψ (-x) := by
  have h1 : ψ x * star (ψ x) = 1 := by
    rw [complex_mul_star_eq_norm_sq, norm_addChar_eq_one]; norm_num
  have h2 : ψ x * ψ (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hne : ψ x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

/-- **Character Orthogonality** (sum of a nontrivial character vanishes):
For any finite abelian group `G` and `ψ : AddChar G ℂ` with `ψ ≠ 1`, `∑ x : G, ψ x = 0`. -/
theorem sum_addChar_eq_zero_of_ne_one (ψ : AddChar G ℂ) (hψ : ψ ≠ 1) :
    ∑ x : G, ψ x = 0 := by
  have hex : ∃ g : G, ψ g ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hψ
    ext x
    exact hall x
  obtain ⟨g, hg⟩ := hex
  have hshift : ψ g * ∑ x : G, ψ x = ∑ x : G, ψ x := by
    rw [Finset.mul_sum]
    have heq : ∀ x : G, ψ g * ψ x = ψ (g + x) := fun x => (AddChar.map_add_eq_mul ψ g x).symm
    simp_rw [heq]
    exact Fintype.sum_equiv (Equiv.addLeft g) _ _ (fun _ => rfl)
  have hmul : (ψ g - 1) * ∑ x : G, ψ x = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hg)

/-- **Exact Character Orthogonality** on any finite abelian group `G`:
`∑ x : G, ψ₁ x * star (ψ₂ x) = if ψ₁ = ψ₂ then |G| else 0`. -/
theorem addChar_orthogonality [DecidableEq (AddChar G ℂ)] (ψ₁ ψ₂ : AddChar G ℂ) :
    ∑ x : G, ψ₁ x * star (ψ₂ x) = if ψ₁ = ψ₂ then (Fintype.card G : ℂ) else 0 := by
  by_cases h : ψ₁ = ψ₂
  · subst h
    simp only [↓reduceIte]
    have h1 : ∀ x : G, ψ₁ x * star (ψ₁ x) = 1 := fun x => by
      rw [complex_mul_star_eq_norm_sq, norm_addChar_eq_one]; norm_num
    simp_rw [h1]
    simp
  · simp only [h, ↓reduceIte]
    let χ : AddChar G ℂ :=
      { toFun := fun x => ψ₁ x * ψ₂ (-x)
        map_zero_eq_one' := by simp [AddChar.map_zero_eq_one]
        map_add_eq_mul' := fun a b => by
          rw [neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]; ring }
    have hχne : χ ≠ 1 := by
      intro h1
      apply h
      ext x
      have hx : ψ₁ x * ψ₂ (-x) = 1 := congrFun (congrArg DFunLike.coe h1) x
      have h2 : ψ₂ x * ψ₂ (-x) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      have hne0 : ψ₂ (-x) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h2; exact zero_ne_one h2
      exact mul_right_cancel₀ hne0 (hx.trans h2.symm)
    have hterm : ∀ x : G, ψ₁ x * star (ψ₂ x) = χ x := fun x => by
      simp only [χ, AddChar.coe_mk, star_addChar_eq_neg]
    simp_rw [hterm]
    exact sum_addChar_eq_zero_of_ne_one χ hχne

/-- Discrete convolution `(f * g)(z) = ∑_{x ∈ G} f(x) g(z - x)` on any finite abelian group `G`. -/
def convG (f g : G → ℂ) (z : G) : ℂ :=
  ∑ x : G, f x * g (z - x)

/-- Character Fourier transform `f̂(ψ) = ∑_{x ∈ G} f(x) · star (ψ x)` on a finite abelian group. -/
def charTransform (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ x : G, f x * star (ψ x)

/-- **Convolution-to-Product Theorem** for arbitrary finite abelian groups `G`:
`(f * g)̂(ψ) = f̂(ψ) · ĝ(ψ)`. -/
theorem charTransform_convG (f g : G → ℂ) (ψ : AddChar G ℂ) :
    charTransform (convG f g) ψ = charTransform f ψ * charTransform g ψ := by
  unfold charTransform convG
  calc ∑ z : G, (∑ x : G, f x * g (z - x)) * star (ψ z)
      = ∑ z : G, ∑ x : G, f x * g (z - x) * star (ψ z) := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_mul _ _ _
    _ = ∑ x : G, ∑ z : G, f x * g (z - x) * star (ψ z) := Finset.sum_comm
    _ = ∑ x : G, ∑ y : G, (f x * star (ψ x)) * (g y * star (ψ y)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun z => ?_
        simp only [Equiv.subRight_apply]
        have hψ : star (ψ z) = star (ψ x) * star (ψ (z - x)) := by
          rw [← star_mul, mul_comm, ← AddChar.map_add_eq_mul, add_sub_cancel]
        rw [hψ]; ring
    _ = (∑ x : G, f x * star (ψ x)) * (∑ y : G, g y * star (ψ y)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm

end FiniteAbelianCharacters

section ZModFourier

/-- Canonical additive character `e_N(x) = exp(2πi x / N)` on `ZMod N`. -/
noncomputable def eZMod (N : ℕ) (x : ZMod N) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / (N : ℂ))

lemma eZMod_zero (N : ℕ) : eZMod N 0 = 1 := by
  simp [eZMod]

lemma eZMod_add (N : ℕ) [NeZero N] (x y : ZMod N) :
    eZMod N (x + y) = eZMod N x * eZMod N y := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdiv : (x.val + y.val : ℕ) = (x + y).val + N * ((x.val + y.val) / N) := by
    rw [ZMod.val_add]
    exact (Nat.mod_add_div (x.val + y.val) N).symm
  have hdivC : ((x.val : ℂ) + (y.val : ℂ)) =
      ((x + y).val : ℂ) + (N : ℂ) * (((x.val + y.val) / N : ℕ) : ℂ) := by
    exact_mod_cast hdiv
  have hexp_eq :
      2 * (Real.pi : ℂ) * Complex.I * (x.val : ℂ) / (N : ℂ) +
      2 * (Real.pi : ℂ) * Complex.I * (y.val : ℂ) / (N : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * ((x + y).val : ℂ) / (N : ℂ) +
      (((x.val + y.val) / N : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have h1 :
        2 * (Real.pi : ℂ) * Complex.I * (x.val : ℂ) / (N : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * (y.val : ℂ) / (N : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * ((x.val : ℂ) + (y.val : ℂ)) / (N : ℂ) := by ring
    rw [h1, hdivC]
    field_simp
  unfold eZMod
  rw [← Complex.exp_add, hexp_eq, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- The additive character `x ↦ e_N(r · x)` on `ZMod N`. -/
noncomputable def eZModAddChar (N : ℕ) [NeZero N] (r : ZMod N) : AddChar (ZMod N) ℂ where
  toFun x := eZMod N (r * x)
  map_zero_eq_one' := by simp [eZMod_zero]
  map_add_eq_mul' a b := by rw [mul_add, eZMod_add]

lemma norm_eZMod (N : ℕ) [NeZero N] (x : ZMod N) : ‖eZMod N x‖ = 1 := by
  have h := norm_addChar_eq_one (eZModAddChar N 1) x
  simpa [eZModAddChar] using h

lemma eZMod_neg (N : ℕ) [NeZero N] (x : ZMod N) : eZMod N (-x) = star (eZMod N x) := by
  have h := star_addChar_eq_neg (eZModAddChar N 1) x
  simpa [eZModAddChar] using h.symm

lemma eZMod_ne_one_of_ne_zero (N : ℕ) [NeZero N] {r : ZMod N} (hr : r ≠ 0) :
    eZMod N r ≠ 1 := by
  intro heq
  unfold eZMod at heq
  rw [Complex.exp_eq_one_iff] at heq
  obtain ⟨k, hk⟩ := heq
  have h2piI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hfrac : (r.val : ℂ) / (N : ℂ) = (k : ℂ) := by
    have hmul : (2 * (Real.pi : ℂ) * Complex.I) * ((r.val : ℂ) / (N : ℂ)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) := by
      calc (2 * (Real.pi : ℂ) * Complex.I) * ((r.val : ℂ) / (N : ℂ))
          = 2 * (Real.pi : ℂ) * Complex.I * (r.val : ℂ) / (N : ℂ) := by ring
        _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hk
        _ = (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) := by ring
    exact mul_left_cancel₀ h2piI hmul
  have hC : (r.val : ℂ) = (k : ℂ) * (N : ℂ) := (div_eq_iff hN0).mp hfrac
  have hZ : (r.val : ℤ) = k * (N : ℤ) := by
    have hre := congrArg Complex.re hC
    simp only [Complex.natCast_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.natCast_im, mul_zero, sub_zero] at hre
    exact_mod_cast hre
  have hrpos : 0 < r.val := Nat.pos_of_ne_zero (fun h0 => hr ((ZMod.val_eq_zero r).mp h0))
  have hrlt : r.val < N := ZMod.val_lt r
  have hNpos : (0 : ℤ) < (N : ℤ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hkpos : 0 < k := by nlinarith
  have hklt : k < 1 := by nlinarith
  omega

/-- **Exact Discrete Orthogonality over `ZMod N`**:
`∑ x : ZMod N, e_N(r · x) = if r = 0 then N else 0`. -/
theorem sum_eZMod_eq_ite (N : ℕ) [NeZero N] (r : ZMod N) :
    ∑ x : ZMod N, eZMod N (r * x) = if r = 0 then (N : ℂ) else 0 := by
  by_cases hr : r = 0
  · subst hr
    simp [eZMod_zero, ZMod.card]
  · simp only [hr, ↓reduceIte]
    have hne : eZModAddChar N r ≠ 1 := by
      intro h1
      have hval : eZModAddChar N r 1 = 1 := congrFun (congrArg DFunLike.coe h1) 1
      simp only [eZModAddChar, AddChar.coe_mk, mul_one] at hval
      exact eZMod_ne_one_of_ne_zero N hr hval
    exact sum_addChar_eq_zero_of_ne_one (eZModAddChar N r) hne

/-- Discrete Fourier Transform on `ZMod N`: `f̂(r) = ∑_{x ∈ ZMod N} f(x) e_N(-r · x)`. -/
noncomputable def dft {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (r : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * eZMod N (-(r * x))

lemma dft_eq_charTransform {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (r : ZMod N) :
    dft f r = charTransform f (eZModAddChar N r) := by
  unfold dft charTransform
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [eZModAddChar, AddChar.coe_mk, eZMod_neg]

/-- **Convolution-to-Product Theorem over `ZMod N`**:
`(f * g)̂(r) = f̂(r) · ĝ(r)`. -/
theorem dft_conv {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (r : ZMod N) :
    dft (convG f g) r = dft f r * dft g r := by
  rw [dft_eq_charTransform, dft_eq_charTransform, dft_eq_charTransform]
  exact charTransform_convG f g (eZModAddChar N r)

/-- **Exact Discrete Fourier Inversion over `ZMod N`**:
`N⁻¹ · ∑_{r ∈ ZMod N} f̂(r) e_N(r · x) = f(x)`. -/
theorem dft_inversion {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (x : ZMod N) :
    (N : ℂ)⁻¹ * ∑ r : ZMod N, dft f r * eZMod N (r * x) = f x := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsum : ∑ r : ZMod N, dft f r * eZMod N (r * x) = (N : ℂ) * f x := by
    unfold dft
    calc ∑ r : ZMod N, (∑ y : ZMod N, f y * eZMod N (-(r * y))) * eZMod N (r * x)
        = ∑ r : ZMod N, ∑ y : ZMod N, f y * (eZMod N (-(r * y)) * eZMod N (r * x)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ y : ZMod N, ∑ r : ZMod N, f y * eZMod N ((x - y) * r) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun r _ => ?_
          rw [← eZMod_add]
          congr 2; ring
      _ = ∑ y : ZMod N, f y * (if x - y = 0 then (N : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.mul_sum, sum_eZMod_eq_ite]
      _ = (N : ℂ) * f x := by
          have hite : ∀ y : ZMod N,
              f y * (if x - y = 0 then (N : ℂ) else 0) = if y = x then f y * (N : ℂ) else 0 := by
            intro y
            by_cases hy : y = x
            · subst hy; simp
            · have hsub : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
              simp [hy, hsub]
          simp_rw [hite]
          rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ x)]
          ring
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]

/-- **Plancherel Identity over `ZMod N`**:
`∑_{r ∈ ZMod N} f̂(r) · star (ĝ(r)) = N · ∑_{x ∈ ZMod N} f(x) · star (g(x))`. -/
theorem plancherel_zmod {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    ∑ r : ZMod N, dft f r * star (dft g r) = (N : ℂ) * ∑ x : ZMod N, f x * star (g x) := by
  unfold dft
  calc ∑ r : ZMod N, (∑ x : ZMod N, f x * eZMod N (-(r * x))) *
          star (∑ y : ZMod N, g y * eZMod N (-(r * y)))
      = ∑ r : ZMod N, ∑ x : ZMod N, ∑ y : ZMod N,
          f x * star (g y) * eZMod N ((y - x) * r) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [star_mul', ← eZMod_neg, neg_neg]
        have hmul : eZMod N (-(r * x)) * eZMod N (r * y) = eZMod N ((y - x) * r) := by
          rw [← eZMod_add]; congr 1; ring
        calc f x * eZMod N (-(r * x)) * (star (g y) * eZMod N (r * y))
            = f x * star (g y) * (eZMod N (-(r * x)) * eZMod N (r * y)) := by ring
          _ = f x * star (g y) * eZMod N ((y - x) * r) := by rw [hmul]
    _ = ∑ x : ZMod N, ∑ y : ZMod N, ∑ r : ZMod N,
          f x * star (g y) * eZMod N ((y - x) * r) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : ZMod N, ∑ y : ZMod N,
          f x * star (g y) * (if y - x = 0 then (N : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.mul_sum, sum_eZMod_eq_ite]
    _ = ∑ x : ZMod N, (N : ℂ) * (f x * star (g x)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hite : ∀ y : ZMod N,
            f x * star (g y) * (if y - x = 0 then (N : ℂ) else 0) =
            if y = x then (N : ℂ) * (f x * star (g y)) else 0 := by
          intro y
          by_cases hy : y = x
          · subst hy; simp [mul_comm]
          · have hsub : y - x ≠ 0 := sub_ne_zero.mpr hy
            simp [hy, hsub]
        simp_rw [hite]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ x)]
    _ = (N : ℂ) * ∑ x : ZMod N, f x * star (g x) := (Finset.mul_sum _ _ _).symm

/-- **Parseval Identity over `ZMod N`**:
`∑_{r ∈ ZMod N} ‖f̂(r)‖^2 = N · ∑_{x ∈ ZMod N} ‖f(x)‖^2`. -/
theorem parseval_zmod {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    ∑ r : ZMod N, ‖dft f r‖ ^ 2 = (N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 := by
  have hP := plancherel_zmod f f
  simp_rw [complex_mul_star_eq_norm_sq] at hP
  have hre := congrArg Complex.re hP
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, zero_mul, sub_zero] at hre
  exact hre

/-- Complex indicator function `1_A : ZMod N → ℂ` of a subset `A ⊆ ZMod N`. -/
def indicatorC {N : ℕ} (A : Finset (ZMod N)) (x : ZMod N) : ℂ :=
  if x ∈ A then 1 else 0

lemma dft_indicatorC_zero {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    dft (indicatorC A) 0 = (A.card : ℂ) := by
  unfold dft indicatorC
  simp [eZMod_zero]

lemma norm_dft_indicatorC_le {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (r : ZMod N) :
    ‖dft (indicatorC A) r‖ ≤ (A.card : ℝ) := by
  unfold dft indicatorC
  calc ‖∑ x : ZMod N, (if x ∈ A then (1 : ℂ) else 0) * eZMod N (-(r * x))‖
      ≤ ∑ x : ZMod N, ‖(if x ∈ A then (1 : ℂ) else 0) * eZMod N (-(r * x))‖ :=
        norm_sum_le _ _
    _ = ∑ x : ZMod N, (if x ∈ A then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : x ∈ A <;> simp [hx, norm_eZMod]
    _ = (A.card : ℝ) := by simp

/-- **Parseval for Set Indicators**: `∑_r ‖1̂_A(r)‖^2 = N · |A|`. -/
theorem parseval_indicatorC {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    ∑ r : ZMod N, ‖dft (indicatorC A) r‖ ^ 2 = (N : ℝ) * (A.card : ℝ) := by
  rw [parseval_zmod]
  congr 1
  have hterm : ∀ x : ZMod N, ‖indicatorC A x‖ ^ 2 = if x ∈ A then (1 : ℝ) else 0 := by
    intro x; unfold indicatorC; by_cases hx : x ∈ A <;> simp [hx]
  simp_rw [hterm]
  simp

/-- Convolution of indicators equals additive representation count:
`(1_A * 1_B)(z) = addRep A B z`. -/
theorem convG_indicatorC_eq_addRep {N : ℕ} [NeZero N] (A B : Finset (ZMod N)) (z : ZMod N) :
    convG (indicatorC A) (indicatorC B) z = (addRep A B z : ℂ) := by
  unfold convG indicatorC addRep
  have hcard : ((A ×ˢ B).filter (fun p => p.1 + p.2 = z)).card =
      (Finset.univ.filter (fun x : ZMod N => x ∈ A ∧ z - x ∈ B)).card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨hp.1.1, ?_⟩
      have : z - p.1 = p.2 := by rw [← hp.2]; ring
      rw [this]; exact hp.1.2
    · intro p₁ hp₁ p₂ hp₂ hfst
      simp only [Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
      have hsnd : p₁.2 = p₂.2 := by
        have : p₁.1 + p₁.2 = p₁.1 + p₂.2 := by rw [hp₁.2, ← hp₂.2, hfst]
        exact add_left_cancel this
      exact Prod.ext hfst hsnd
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨(x, z - x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hx, add_sub_cancel x z⟩, rfl⟩
  rw [hcard]
  have hterm : ∀ x : ZMod N,
      (if x ∈ A then (1 : ℂ) else 0) * (if z - x ∈ B then (1 : ℂ) else 0) =
      if x ∈ A ∧ z - x ∈ B then (1 : ℂ) else 0 := by
    intro x; by_cases h1 : x ∈ A <;> by_cases h2 : z - x ∈ B <;> simp [h1, h2]
  simp_rw [hterm]
  simp

/-- **Exact Additive Energy Fourier Formula (Pair Form)**:
`E(A, B) = N⁻¹ · ∑_{r ∈ ZMod N} ‖1̂_A(r)‖^2 · ‖1̂_B(r)‖^2`. -/
theorem addEnergy_pair_eq_dft {N : ℕ} [NeZero N] (A B : Finset (ZMod N)) :
    (addEnergy A B : ℝ) =
      (N : ℝ)⁻¹ * ∑ r : ZMod N, ‖dft (indicatorC A) r‖ ^ 2 * ‖dft (indicatorC B) r‖ ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hP := parseval_zmod (convG (indicatorC A) (indicatorC B))
  have hlhs : ∑ r : ZMod N, ‖dft (convG (indicatorC A) (indicatorC B)) r‖ ^ 2 =
      ∑ r : ZMod N, ‖dft (indicatorC A) r‖ ^ 2 * ‖dft (indicatorC B) r‖ ^ 2 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [dft_conv, norm_mul, mul_pow]
  have hrhs : ∑ z : ZMod N, ‖convG (indicatorC A) (indicatorC B) z‖ ^ 2 = (addEnergy A B : ℝ) := by
    simp_rw [convG_indicatorC_eq_addRep, Complex.norm_natCast]
    rw [addEnergy_eq_sum_sq_addRep]
    push_cast
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun z _ hz => ?_
    have h0 : addRep A B z = 0 := by
      rw [addRep, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp heq
      rw [Finset.mem_product] at hp
      exact hz (Finset.mem_add.mpr ⟨p.1, hp.1, p.2, hp.2, heq⟩)
    rw [h0]
    simp
  rw [hlhs, hrhs] at hP
  rw [hP, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), one_mul]

/-- **Exact Additive Energy Fourth-Moment Identity**:
`E(A, A) = N⁻¹ · ∑_{r ∈ ZMod N} ‖1̂_A(r)‖^4`. -/
theorem addEnergy_eq_dft_fourth_moment {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (addEnergy A A : ℝ) = (N : ℝ)⁻¹ * ∑ r : ZMod N, ‖dft (indicatorC A) r‖ ^ 4 := by
  rw [addEnergy_pair_eq_dft A A]
  congr 1
  refine Finset.sum_congr rfl fun r _ => by ring

end ZModFourier

section LargeSpectrumAndRoth

/-- The `η`-large Fourier spectrum of `A ⊆ ZMod N`:
`Spec_η(A) = {r ∈ ZMod N | ‖1̂_A(r)‖ ≥ η · |A|}`. -/
noncomputable def largeSpectrum {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (η : ℝ) : Finset (ZMod N) :=
  Finset.univ.filter (fun r => η * (A.card : ℝ) ≤ ‖dft (indicatorC A) r‖)

/-- **Large-Spectrum Cardinality Bound (Parseval / Chang-style)**:
For nonempty `A ⊆ ZMod N` and `η > 0`, `|Spec_η(A)| ≤ N / (η^2 · |A|)`. -/
theorem largeSpectrum_card_le {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (hA : A.Nonempty)
    {η : ℝ} (hη : 0 < η) :
    ((largeSpectrum A η).card : ℝ) ≤ (N : ℝ) / (η ^ 2 * (A.card : ℝ)) := by
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have h1 : ((largeSpectrum A η).card : ℝ) * (η * (A.card : ℝ)) ^ 2 ≤
      (N : ℝ) * (A.card : ℝ) := by
    calc ((largeSpectrum A η).card : ℝ) * (η * (A.card : ℝ)) ^ 2
        = ∑ _r ∈ largeSpectrum A η, (η * (A.card : ℝ)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ largeSpectrum A η, ‖dft (indicatorC A) r‖ ^ 2 := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hge := (Finset.mem_filter.mp hr).2
          exact pow_le_pow_left₀ (by positivity) hge 2
      _ ≤ ∑ r : ZMod N, ‖dft (indicatorC A) r‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ = (N : ℝ) * (A.card : ℝ) := parseval_indicatorC A
  have hden : 0 < η ^ 2 * (A.card : ℝ) := by positivity
  rw [le_div_iff₀ hden]
  have hmul : (((largeSpectrum A η).card : ℝ) * (η ^ 2 * (A.card : ℝ))) * (A.card : ℝ) ≤
      (N : ℝ) * (A.card : ℝ) := by linarith
  exact le_of_mul_le_mul_right hmul hApos

/-- **Energy-to-Large-Fourier-Coefficient Lemma**:
If `E(A, A) ≥ |A|^4 / N + δ · |A|^3` (`δ > 0`), then there exists a nonzero frequency
`r ≠ 0` with `‖1̂_A(r)‖ ≥ √δ · |A|`. -/
theorem exists_large_fourier_of_addEnergy {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hA : A.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (hE : (A.card : ℝ) ^ 4 / (N : ℝ) + δ * (A.card : ℝ) ^ 3 ≤ (addEnergy A A : ℝ)) :
    ∃ r : ZMod N, r ≠ 0 ∧ Real.sqrt δ * (A.card : ℝ) ≤ ‖dft (indicatorC A) r‖ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have h4 := addEnergy_eq_dft_fourth_moment A
  have hsum4 : (A.card : ℝ) ^ 4 + δ * (N : ℝ) * (A.card : ℝ) ^ 3 ≤
      ∑ r : ZMod N, ‖dft (indicatorC A) r‖ ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hE (le_of_lt hNpos)
    rw [h4, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul] at hmul
    have hlhs : (N : ℝ) * ((A.card : ℝ) ^ 4 / (N : ℝ) + δ * (A.card : ℝ) ^ 3) =
        (A.card : ℝ) ^ 4 + δ * (N : ℝ) * (A.card : ℝ) ^ 3 := by field_simp
    linarith
  have hzero4 : ‖dft (indicatorC A) 0‖ ^ 4 = (A.card : ℝ) ^ 4 := by
    rw [dft_indicatorC_zero, Complex.norm_natCast]
  have hsplit4 : ∑ r : ZMod N, ‖dft (indicatorC A) r‖ ^ 4 =
      ‖dft (indicatorC A) 0‖ ^ 4 + ∑ r ∈ Finset.univ.erase 0, ‖dft (indicatorC A) r‖ ^ 4 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod N))]
  have hnz4 : δ * (N : ℝ) * (A.card : ℝ) ^ 3 ≤
      ∑ r ∈ Finset.univ.erase (0 : ZMod N), ‖dft (indicatorC A) r‖ ^ 4 := by linarith
  by_contra hcontra
  push Not at hcontra
  have hstrict : ∑ r ∈ Finset.univ.erase (0 : ZMod N), ‖dft (indicatorC A) r‖ ^ 4 ≤
      (δ * (A.card : ℝ) ^ 2) * ∑ r ∈ Finset.univ.erase (0 : ZMod N), ‖dft (indicatorC A) r‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrne : r ≠ 0 := (Finset.mem_erase.mp hr).1
    have hlt : ‖dft (indicatorC A) r‖ < Real.sqrt δ * (A.card : ℝ) := hcontra r hrne
    have hsq : ‖dft (indicatorC A) r‖ ^ 2 ≤ δ * (A.card : ℝ) ^ 2 := by
      have h1 : ‖dft (indicatorC A) r‖ ^ 2 ≤ (Real.sqrt δ * (A.card : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hlt) 2
      rw [mul_pow, Real.sq_sqrt (le_of_lt hδ)] at h1
      exact h1
    calc ‖dft (indicatorC A) r‖ ^ 4
        = ‖dft (indicatorC A) r‖ ^ 2 * ‖dft (indicatorC A) r‖ ^ 2 := by ring
      _ ≤ (δ * (A.card : ℝ) ^ 2) * ‖dft (indicatorC A) r‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hparseval_nz : ∑ r ∈ Finset.univ.erase (0 : ZMod N), ‖dft (indicatorC A) r‖ ^ 2 =
      (N : ℝ) * (A.card : ℝ) - (A.card : ℝ) ^ 2 := by
    have hsp := (Finset.add_sum_erase (Finset.univ : Finset (ZMod N))
      (fun r => ‖dft (indicatorC A) r‖ ^ 2) (Finset.mem_univ (0 : ZMod N)))
    rw [parseval_indicatorC, dft_indicatorC_zero, Complex.norm_natCast] at hsp
    linarith
  rw [hparseval_nz] at hstrict
  have hcomb : δ * (N : ℝ) * (A.card : ℝ) ^ 3 ≤
      (δ * (A.card : ℝ) ^ 2) * ((N : ℝ) * (A.card : ℝ) - (A.card : ℝ) ^ 2) :=
    hnz4.trans hstrict
  have hposA4 : 0 < δ * (A.card : ℝ) ^ 4 := by positivity
  nlinarith

/-- Number of solutions `(x, y, z) ∈ A^3` to the 3-AP equation `x + z = 2 y` in `ZMod N`. -/
def threeAPCount {N : ℕ} (A : Finset (ZMod N)) : ℕ :=
  ((A ×ˢ (A ×ˢ A)).filter (fun t => t.1 + t.2.2 = 2 * t.2.1)).card

/-- A subset `A ⊆ ZMod N` is 3-AP-free if every solution to `x + z = 2 y` in `A` is trivial. -/
def IsThreeAPFree {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = 2 * y → x = y ∧ y = z

lemma threeAPCount_of_free {N : ℕ} (A : Finset (ZMod N)) (hfree : IsThreeAPFree A) :
    threeAPCount A = A.card := by
  unfold threeAPCount
  refine Finset.card_bij (fun t _ => t.2.1) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_product] at ht
    exact ht.1.2.1
  · intro t₁ ht₁ t₂ ht₂ hy
    simp only [Finset.mem_filter, Finset.mem_product] at ht₁ ht₂
    obtain ⟨hx₁, hz₁⟩ := hfree t₁.1 ht₁.1.1 t₁.2.1 ht₁.1.2.1 t₁.2.2 ht₁.1.2.2 ht₁.2
    obtain ⟨hx₂, hz₂⟩ := hfree t₂.1 ht₂.1.1 t₂.2.1 ht₂.1.2.1 t₂.2.2 ht₂.1.2.2 ht₂.2
    exact Prod.ext (hx₁.trans (hy.trans hx₂.symm))
      (Prod.ext hy (hz₁.symm.trans (hy.trans hz₂)))
  · intro a ha
    refine ⟨(a, (a, a)),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨ha, ha⟩⟩, ?_⟩, rfl⟩
    ring

/-- **Exact 3-AP Fourier Identity over `ZMod N`**:
`threeAPCount A = N⁻¹ · ∑_{r ∈ ZMod N} (1̂_A(r))^2 · 1̂_A(-2r)`. -/
theorem threeAPCount_eq_dft {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (threeAPCount A : ℂ) =
      (N : ℂ)⁻¹ * ∑ r : ZMod N, (dft (indicatorC A) r) ^ 2 * dft (indicatorC A) (-(2 * r)) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsum :
      ∑ r : ZMod N, (dft (indicatorC A) r) ^ 2 * dft (indicatorC A) (-(2 * r)) =
      (N : ℂ) * (threeAPCount A : ℂ) := by
    have hdftA : ∀ s : ZMod N, dft (indicatorC A) s = ∑ a ∈ A, eZMod N (-(s * a)) := by
      intro s; unfold dft indicatorC
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    simp_rw [hdftA]
    calc ∑ r : ZMod N, (∑ x ∈ A, eZMod N (-(r * x))) ^ 2 *
            (∑ y ∈ A, eZMod N (-(-(2 * r) * y)))
        = ∑ r : ZMod N, ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, eZMod N ((2 * y - x - z) * r) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [sq]
          calc (∑ x ∈ A, eZMod N (-(r * x))) * (∑ z ∈ A, eZMod N (-(r * z))) *
                (∑ y ∈ A, eZMod N (-(-(2 * r) * y)))
              = ∑ x ∈ A, ∑ z ∈ A, ∑ y ∈ A,
                  eZMod N (-(r * x)) * eZMod N (-(r * z)) * eZMod N (-(-(2 * r) * y)) := by
                rw [Finset.sum_mul, Finset.sum_mul]
                refine Finset.sum_congr rfl fun x _ => ?_
                have hx1 : eZMod N (-(r * x)) * ∑ z ∈ A, eZMod N (-(r * z)) =
                    ∑ z ∈ A, eZMod N (-(r * x)) * eZMod N (-(r * z)) := Finset.mul_sum _ _ _
                rw [hx1, Finset.sum_mul]
                refine Finset.sum_congr rfl fun z _ => Finset.mul_sum _ _ _
            _ = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A,
                  eZMod N (-(r * x)) * eZMod N (-(r * z)) * eZMod N (-(-(2 * r) * y)) := by
                refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
            _ = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, eZMod N ((2 * y - x - z) * r) := by
                refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
                  Finset.sum_congr rfl fun z _ => ?_
                rw [← eZMod_add, ← eZMod_add]
                congr 1; ring
      _ = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, ∑ r : ZMod N, eZMod N ((2 * y - x - z) * r) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_comm
      _ = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (if 2 * y - x - z = 0 then (N : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun z _ => sum_eZMod_eq_ite N (2 * y - x - z)
      _ = (N : ℂ) * (threeAPCount A : ℂ) := by
          have heq : ∀ x y z : ZMod N, (2 * y - x - z = 0) ↔ (x + z = 2 * y) := by
            intro x y z
            constructor
            · intro h; calc x + z = 2 * y - (2 * y - x - z) := by ring
                _ = 2 * y := by rw [h, sub_zero]
            · intro h; calc 2 * y - x - z = (x + z) - x - z := by rw [h]
                _ = 0 := by ring
          simp_rw [heq]
          unfold threeAPCount
          rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Finset.sum_product]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
          by_cases h : x + z = 2 * y <;> simp [h]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]

lemma neg_two_mul_ne_zero_of_odd {N : ℕ} (hodd : Odd N) {r : ZMod N} (hr : r ≠ 0) :
    -(2 * r) ≠ 0 := by
  obtain ⟨k, hk⟩ := hodd
  intro h0
  have h2r : 2 * r = 0 := neg_eq_zero.mp h0
  have h1 : ((k + 1 : ℕ) : ZMod N) * (2 : ZMod N) = 1 := by
    have hN0 : ((2 * k + 1 : ℕ) : ZMod N) = 0 := by
      rw [← hk]; exact ZMod.natCast_self N
    have hcast : ((k + 1 : ℕ) : ZMod N) * (2 : ZMod N) = ((2 * k + 1 : ℕ) : ZMod N) + 1 := by
      push_cast; ring
    rw [hcast, hN0, zero_add]
  apply hr
  calc r = 1 * r := (one_mul r).symm
    _ = (((k + 1 : ℕ) : ZMod N) * (2 : ZMod N)) * r := by rw [h1]
    _ = ((k + 1 : ℕ) : ZMod N) * (2 * r) := by rw [mul_assoc]
    _ = 0 := by rw [h2r, mul_zero]

/-- **Roth Large-Fourier-Coefficient Lemma**:
If `N` is odd, `A ⊆ ZMod N` is nonempty and 3-AP-free, and `2 N ≤ |A|^2`,
then there exists a nonzero frequency `r ≠ 0` with `‖1̂_A(r)‖ ≥ |A|^2 / (2 N)`. -/
theorem roth_large_fourier_coeff {N : ℕ} [NeZero N] (hodd : Odd N)
    (A : Finset (ZMod N)) (hA : A.Nonempty) (hfree : IsThreeAPFree A)
    (hdense : 2 * (N : ℝ) ≤ (A.card : ℝ) ^ 2) :
    ∃ r : ZMod N, r ≠ 0 ∧ (A.card : ℝ) ^ 2 / (2 * (N : ℝ)) ≤ ‖dft (indicatorC A) r‖ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hid := threeAPCount_eq_dft A
  rw [threeAPCount_of_free A hfree] at hid
  have hsplit : ∑ r : ZMod N, (dft (indicatorC A) r) ^ 2 * dft (indicatorC A) (-(2 * r)) =
      (A.card : ℂ) ^ 3 +
      ∑ r ∈ Finset.univ.erase (0 : ZMod N),
        (dft (indicatorC A) r) ^ 2 * dft (indicatorC A) (-(2 * r)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod N))]
    congr 1
    simp [dft_indicatorC_zero]; ring
  have hmulN : (N : ℂ) * (A.card : ℂ) = (A.card : ℂ) ^ 3 +
      ∑ r ∈ Finset.univ.erase (0 : ZMod N),
        (dft (indicatorC A) r) ^ 2 * dft (indicatorC A) (-(2 * r)) := by
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have h1 := congrArg ((N : ℂ) * ·) hid
    rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul, hsplit] at h1
    exact h1
  have hsub : (A.card : ℂ) ^ 3 - (N : ℂ) * (A.card : ℂ) =
      -(∑ r ∈ Finset.univ.erase (0 : ZMod N),
        (dft (indicatorC A) r) ^ 2 * dft (indicatorC A) (-(2 * r))) := by
    linear_combination -hmulN
  have hnorm_lb : (A.card : ℝ) ^ 3 / 2 ≤
      ∑ r ∈ Finset.univ.erase (0 : ZMod N),
        ‖dft (indicatorC A) r‖ ^ 2 * ‖dft (indicatorC A) (-(2 * r))‖ := by
    have hnorm_lhs : ‖(A.card : ℂ) ^ 3 - (N : ℂ) * (A.card : ℂ)‖ =
        (A.card : ℝ) ^ 3 - (N : ℝ) * (A.card : ℝ) := by
      have hcast : (A.card : ℂ) ^ 3 - (N : ℂ) * (A.card : ℂ) =
          (((A.card : ℝ) ^ 3 - (N : ℝ) * (A.card : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      nlinarith
    have hge : (A.card : ℝ) ^ 3 / 2 ≤ (A.card : ℝ) ^ 3 - (N : ℝ) * (A.card : ℝ) := by nlinarith
    calc (A.card : ℝ) ^ 3 / 2
        ≤ ‖(A.card : ℂ) ^ 3 - (N : ℂ) * (A.card : ℂ)‖ := by linarith
      _ = ‖∑ r ∈ Finset.univ.erase (0 : ZMod N),
            (dft (indicatorC A) r) ^ 2 * dft (indicatorC A) (-(2 * r))‖ := by
          rw [hsub, norm_neg]
      _ ≤ ∑ r ∈ Finset.univ.erase (0 : ZMod N),
            ‖(dft (indicatorC A) r) ^ 2 * dft (indicatorC A) (-(2 * r))‖ := norm_sum_le _ _
      _ = ∑ r ∈ Finset.univ.erase (0 : ZMod N),
            ‖dft (indicatorC A) r‖ ^ 2 * ‖dft (indicatorC A) (-(2 * r))‖ := by
          refine Finset.sum_congr rfl fun r _ => by rw [norm_mul, norm_pow]
  by_contra hcontra
  push Not at hcontra
  have hstrict : ∑ r ∈ Finset.univ.erase (0 : ZMod N),
      ‖dft (indicatorC A) r‖ ^ 2 * ‖dft (indicatorC A) (-(2 * r))‖ ≤
      ((A.card : ℝ) ^ 2 / (2 * (N : ℝ))) *
      ∑ r ∈ Finset.univ.erase (0 : ZMod N), ‖dft (indicatorC A) r‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrne : r ≠ 0 := (Finset.mem_erase.mp hr).1
    have h2rne : -(2 * r) ≠ 0 := neg_two_mul_ne_zero_of_odd hodd hrne
    have hlt := hcontra (-(2 * r)) h2rne
    calc ‖dft (indicatorC A) r‖ ^ 2 * ‖dft (indicatorC A) (-(2 * r))‖
        ≤ ‖dft (indicatorC A) r‖ ^ 2 * ((A.card : ℝ) ^ 2 / (2 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left (le_of_lt hlt) (sq_nonneg _)
      _ = ((A.card : ℝ) ^ 2 / (2 * (N : ℝ))) * ‖dft (indicatorC A) r‖ ^ 2 := by ring
  have hparseval_nz : ∑ r ∈ Finset.univ.erase (0 : ZMod N), ‖dft (indicatorC A) r‖ ^ 2 =
      (N : ℝ) * (A.card : ℝ) - (A.card : ℝ) ^ 2 := by
    have hsp := Finset.add_sum_erase (Finset.univ : Finset (ZMod N))
      (fun r => ‖dft (indicatorC A) r‖ ^ 2) (Finset.mem_univ (0 : ZMod N))
    rw [parseval_indicatorC, dft_indicatorC_zero, Complex.norm_natCast] at hsp
    linarith
  rw [hparseval_nz] at hstrict
  have hcomb : (A.card : ℝ) ^ 3 / 2 ≤
      ((A.card : ℝ) ^ 2 / (2 * (N : ℝ))) * ((N : ℝ) * (A.card : ℝ) - (A.card : ℝ) ^ 2) :=
    hnorm_lb.trans hstrict
  have hmul : (2 * (N : ℝ)) * ((A.card : ℝ) ^ 3 / 2) ≤
      (2 * (N : ℝ)) * (((A.card : ℝ) ^ 2 / (2 * (N : ℝ))) *
        ((N : ℝ) * (A.card : ℝ) - (A.card : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hcomb (by positivity)
  have h2Nne : 2 * (N : ℝ) ≠ 0 := ne_of_gt (mul_pos two_pos hNpos)
  have hsimp : (2 * (N : ℝ)) * (((A.card : ℝ) ^ 2 / (2 * (N : ℝ))) *
      ((N : ℝ) * (A.card : ℝ) - (A.card : ℝ) ^ 2)) =
      (N : ℝ) * (A.card : ℝ) ^ 3 - (A.card : ℝ) ^ 4 := by
    rw [← mul_assoc, mul_div_cancel₀ _ h2Nne]; ring
  have hposA4 : 0 < (A.card : ℝ) ^ 4 := pow_pos hApos 4
  linarith

/-- One-dimensional Bohr set `B(r, δ) = {x ∈ ZMod N | ‖e_N(r · x) - 1‖ ≤ δ}`. -/
noncomputable def bohrSet (N : ℕ) [NeZero N] (r : ZMod N) (δ : ℝ) : Finset (ZMod N) :=
  Finset.univ.filter (fun x => ‖eZMod N (r * x) - 1‖ ≤ δ)

lemma zero_mem_bohrSet (N : ℕ) [NeZero N] (r : ZMod N) {δ : ℝ} (hδ : 0 ≤ δ) :
    (0 : ZMod N) ∈ bohrSet N r δ := by
  simp [bohrSet, eZMod_zero, hδ]

/-- For unit-radius Bohr set `P = bohrSet N r 1`, `‖1̂_P(r)‖ ≥ |P| / 2`. -/
lemma norm_dft_bohrSet_ge_half {N : ℕ} [NeZero N] (r : ZMod N) :
    ((bohrSet N r 1).card : ℝ) / 2 ≤ ‖dft (indicatorC (bohrSet N r 1)) r‖ := by
  have hre_ge : ((bohrSet N r 1).card : ℝ) / 2 ≤ (dft (indicatorC (bohrSet N r 1)) r).re := by
    unfold dft indicatorC
    rw [Complex.re_sum]
    have hfilt : ∑ x : ZMod N, ((if x ∈ bohrSet N r 1 then (1 : ℂ) else 0) *
        eZMod N (-(r * x))).re =
        ∑ x ∈ bohrSet N r 1, (eZMod N (r * x)).re := by
      have hterm : ∀ x : ZMod N,
          ((if x ∈ bohrSet N r 1 then (1 : ℂ) else 0) * eZMod N (-(r * x))).re =
          if x ∈ bohrSet N r 1 then (eZMod N (r * x)).re else 0 := by
        intro x
        by_cases hx : x ∈ bohrSet N r 1
        · simp [hx, eZMod_neg]
        · simp [hx]
      simp_rw [hterm, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hfilt]
    calc ((bohrSet N r 1).card : ℝ) / 2
        = ∑ _x ∈ bohrSet N r 1, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ x ∈ bohrSet N r 1, (eZMod N (r * x)).re := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hle1 : ‖eZMod N (r * x) - 1‖ ≤ 1 := (Finset.mem_filter.mp hx).2
          have hsq1 : ‖eZMod N (r * x) - 1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (eZMod N (r * x) - 1)]
          have hnorm1 : ‖eZMod N (r * x)‖ ^ 2 = 1 := by rw [norm_eZMod]; norm_num
          have hexp : ‖eZMod N (r * x) - 1‖ ^ 2 =
              ‖eZMod N (r * x)‖ ^ 2 - 2 * (eZMod N (r * x)).re + 1 := by
            rw [Complex.sq_norm, Complex.sq_norm]
            simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
              Complex.sub_im, Complex.one_im, sub_zero]
            ring
          linarith
  exact hre_ge.trans (Complex.re_le_norm _)

/-- Pigeonhole size lower bound for the unit Bohr set: `|bohrSet N r 1| ≥ N / 6`. -/
theorem bohrSet_card_ge_div_six (N : ℕ) [NeZero N] (r : ZMod N) :
    (N : ℝ) / 6 ≤ ((bohrSet N r 1).card : ℝ) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNposR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  let bucket : ZMod N → Fin 6 := fun x =>
    ⟨(6 * (r * x).val) / N, by
      have hlt : (r * x).val < N := ZMod.val_lt (r * x)
      exact Nat.div_lt_of_lt_mul (by omega)⟩
  have hsum_buckets : ∑ j : Fin 6, (Finset.univ.filter (fun x : ZMod N => bucket x = j)).card = N := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod N))) (t := (Finset.univ : Finset (Fin 6)))
      (f := bucket) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, ZMod.card] at hfib
    exact hfib.symm
  have hex_j : ∃ j : Fin 6, (N : ℝ) / 6 ≤
      ((Finset.univ.filter (fun x : ZMod N => bucket x = j)).card : ℝ) := by
    by_contra hall
    push Not at hall
    have hlt : ∑ j : Fin 6, ((Finset.univ.filter (fun x : ZMod N => bucket x = j)).card : ℝ) <
        ∑ _j : Fin 6, ((N : ℝ) / 6) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hall j)
    have hsumR : ∑ j : Fin 6, ((Finset.univ.filter (fun x : ZMod N => bucket x = j)).card : ℝ) =
        (N : ℝ) := by exact_mod_cast hsum_buckets
    rw [hsumR, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    linarith
  obtain ⟨j, hj⟩ := hex_j
  let Bj : Finset (ZMod N) := Finset.univ.filter (fun x : ZMod N => bucket x = j)
  have hBjne : Bj.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le (by positivity) hj))
  obtain ⟨x₀, hx₀⟩ := hBjne
  have hmaps : Set.MapsTo (fun x => x - x₀) (Bj : Set (ZMod N)) (bohrSet N r 1 : Set (ZMod N)) := by
    intro x hx
    simp only [Finset.mem_coe, bohrSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hbx : (6 * (r * x).val) / N = j.val := congrArg Fin.val (Finset.mem_filter.mp hx).2
    have hbx₀ : (6 * (r * x₀).val) / N = j.val := congrArg Fin.val (Finset.mem_filter.mp hx₀).2
    have hmul_x_lo : j.val * N ≤ 6 * (r * x).val := by
      rw [← hbx]; exact Nat.div_mul_le_self _ _
    have hmul_x_hi : 6 * (r * x).val < (j.val + 1) * N := by
      rw [← hbx, add_mul, one_mul]
      have hrem : 6 * (r * x).val % N < N := Nat.mod_lt _ hNpos
      have hdiv := Nat.div_add_mod (6 * (r * x).val) N
      linarith
    have hmul_x₀_lo : j.val * N ≤ 6 * (r * x₀).val := by
      rw [← hbx₀]; exact Nat.div_mul_le_self _ _
    have hmul_x₀_hi : 6 * (r * x₀).val < (j.val + 1) * N := by
      rw [← hbx₀, add_mul, one_mul]
      have hrem : 6 * (r * x₀).val % N < N := Nat.mod_lt _ hNpos
      have hdiv := Nat.div_add_mod (6 * (r * x₀).val) N
      linarith
    let θ : ℝ := 2 * Real.pi * (((r * x).val : ℝ) - ((r * x₀).val : ℝ)) / (N : ℝ)
    have hθ_abs : |θ| ≤ Real.pi / 3 := by
      have hdiff_abs : |((r * x).val : ℝ) - ((r * x₀).val : ℝ)| ≤ (N : ℝ) / 6 := by
        rw [abs_le]
        have h1 : (j.val : ℝ) * (N : ℝ) ≤ 6 * ((r * x).val : ℝ) := by exact_mod_cast hmul_x_lo
        have h2 : 6 * ((r * x).val : ℝ) ≤ ((j.val : ℝ) + 1) * (N : ℝ) := by
          exact_mod_cast le_of_lt hmul_x_hi
        have h3 : (j.val : ℝ) * (N : ℝ) ≤ 6 * ((r * x₀).val : ℝ) := by exact_mod_cast hmul_x₀_lo
        have h4 : 6 * ((r * x₀).val : ℝ) ≤ ((j.val : ℝ) + 1) * (N : ℝ) := by
          exact_mod_cast le_of_lt hmul_x₀_hi
        constructor <;> linarith
      have hθeq : |θ| = (2 * Real.pi / (N : ℝ)) * |((r * x).val : ℝ) - ((r * x₀).val : ℝ)| := by
        simp only [θ, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hNposR,
          abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        ring
      rw [hθeq]
      calc (2 * Real.pi / (N : ℝ)) * |((r * x).val : ℝ) - ((r * x₀).val : ℝ)|
          ≤ (2 * Real.pi / (N : ℝ)) * ((N : ℝ) / 6) :=
            mul_le_mul_of_nonneg_left hdiff_abs (by positivity)
        _ = Real.pi / 3 := by field_simp; ring
    have he_eq : eZMod N (r * (x - x₀)) = Complex.exp ((θ : ℂ) * Complex.I) := by
      have hmul_sub : r * (x - x₀) = r * x + -(r * x₀) := by ring
      rw [hmul_sub, eZMod_add, eZMod_neg]
      unfold eZMod
      rw [Complex.star_def, ← Complex.exp_conj]
      rw [← Complex.exp_add]
      congr 1
      simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
        Complex.conj_natCast, θ]
      push_cast
      ring
    rw [he_eq]
    have hcos_ge : (1 / 2 : ℝ) ≤ Real.cos θ := by
      have hcos_abs : Real.cos θ = Real.cos |θ| := by
        rcases le_or_gt 0 θ with hge | hlt
        · rw [abs_of_nonneg hge]
        · rw [abs_of_neg hlt, Real.cos_neg]
      rw [hcos_abs, ← Real.cos_pi_div_three]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [Real.pi_pos]) hθ_abs
    have hsq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 ≤ 1 := by
      rw [Complex.exp_mul_I, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.cos_ofReal_re,
        Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im,
        Complex.I_im, mul_one, sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
        Complex.cos_ofReal_im, Complex.mul_im, zero_add, Complex.one_im]
      have hpyth := Real.sin_sq_add_cos_sq θ
      nlinarith
    nlinarith [norm_nonneg (Complex.exp ((θ : ℂ) * Complex.I) - 1)]
  have hinj : Set.InjOn (fun x : ZMod N => x - x₀) (Bj : Set (ZMod N)) :=
    fun _ _ _ _ h => sub_left_inj.mp h
  have hcard : Bj.card ≤ (bohrSet N r 1).card := Finset.card_le_card_of_injOn _ hmaps hinj
  exact hj.trans (Nat.cast_le.mpr hcard)

/-- **General Fourier-to-Density-Increment Lemma**:
For any nonempty `P ⊆ ZMod N`, any `A ⊆ ZMod N`, and any nonzero frequency `r ≠ 0`,
there exists a translate `y - P` on which `A` has density at least
`|A|/N + (‖1̂_A(r)‖ · ‖1̂_P(r)‖) / (2 N |P|)`. -/
theorem density_increment_of_fourier {N : ℕ} [NeZero N]
    (A P : Finset (ZMod N)) (hP : P.Nonempty) {r : ZMod N} (hr : r ≠ 0) :
    ∃ y : ZMod N,
      (A.card : ℝ) / (N : ℝ) +
        (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (2 * (N : ℝ) * (P.card : ℝ)) ≤
      ((A ∩ P.image (fun p => y - p)).card : ℝ) / (P.card : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hPpos : (0 : ℝ) < (P.card : ℝ) := Nat.cast_pos.mpr hP.card_pos
  let α : ℝ := (A.card : ℝ) / (N : ℝ)
  let cnt : ZMod N → ℕ := fun y => (A ∩ P.image (fun p => y - p)).card
  let u : ZMod N → ℝ := fun y => (cnt y : ℝ) - α * (P.card : ℝ)
  have hcnt_eq_rep : ∀ y : ZMod N, cnt y = addRep A P y := by
    intro y
    unfold cnt addRep
    refine Finset.card_bij (fun a _ => (a, y - a)) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_inter, Finset.mem_image] at ha
      rcases ha with ⟨haA, ⟨p, hpP, hpy⟩⟩
      have hya : y - a = p := by rw [← hpy]; ring
      rw [hya]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haA, hpP⟩, by rw [← hpy]; ring⟩
    · intro a₁ _ a₂ _ h; exact (Prod.mk.inj h).1
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product] at hq
      refine ⟨q.1, Finset.mem_inter.mpr ⟨hq.1.1, Finset.mem_image.mpr ⟨q.2, hq.1.2, ?_⟩⟩, ?_⟩
      · rw [← hq.2]; ring
      · exact Prod.ext rfl (by rw [← hq.2]; ring)
  -- ∑_y u(y) = 0
  have hsum_u : ∑ y : ZMod N, u y = 0 := by
    have hsum_cnt : ∑ y : ZMod N, (cnt y : ℝ) = (A.card : ℝ) * (P.card : ℝ) := by
      have hnat : ∑ y : ZMod N, cnt y = A.card * P.card := by
        simp_rw [hcnt_eq_rep]
        rw [← sum_addRep A P]
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun z _ hz => ?_
        rw [addRep, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p hp heq
        rw [Finset.mem_product] at hp
        exact hz (Finset.mem_add.mpr ⟨p.1, hp.1, p.2, hp.2, heq⟩)
      exact_mod_cast hnat
    simp only [u, Finset.sum_sub_distrib, hsum_cnt, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, α]
    field_simp
    ring
  -- Fourier transform of u at r ≠ 0 equals dft 1_A r * dft 1_P r
  have hdft_u : dft (fun y => (u y : ℂ)) r = dft (indicatorC A) r * dft (indicatorC P) r := by
    rw [← dft_conv]
    unfold dft
    have hzero : ∑ y : ZMod N, ((α * (P.card : ℝ) : ℝ) : ℂ) * eZMod N (-(r * y)) = 0 := by
      rw [← Finset.mul_sum]
      have h1 : ∑ y : ZMod N, eZMod N (-(r * y)) = 0 := by
        have heq : ∀ y : ZMod N, eZMod N (-(r * y)) = eZMod N ((-r) * y) := fun y => by
          congr 1; ring
        simp_rw [heq, sum_eZMod_eq_ite]
        simp [neg_ne_zero.mpr hr]
      rw [h1, mul_zero]
    have hsub : ∑ y : ZMod N, (u y : ℂ) * eZMod N (-(r * y)) =
        ∑ y : ZMod N, convG (indicatorC A) (indicatorC P) y * eZMod N (-(r * y)) -
        ∑ y : ZMod N, ((α * (P.card : ℝ) : ℝ) : ℂ) * eZMod N (-(r * y)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [convG_indicatorC_eq_addRep, ← hcnt_eq_rep]
      simp only [u]
      push_cast
      ring
    rw [hsub, hzero, sub_zero]
  -- L¹ lower bound: ‖1̂_A(r)‖ · ‖1̂_P(r)‖ ≤ ∑_y |u(y)| = ∑_y (|u(y)| + u(y))
  have hl1 : ‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖ ≤ ∑ y : ZMod N, (|u y| + u y) := by
    have hnorm : ‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖ ≤ ∑ y : ZMod N, |u y| := by
      rw [← norm_mul, ← hdft_u]
      unfold dft
      calc ‖∑ y : ZMod N, (u y : ℂ) * eZMod N (-(r * y))‖
          ≤ ∑ y : ZMod N, ‖(u y : ℂ) * eZMod N (-(r * y))‖ := norm_sum_le _ _
        _ = ∑ y : ZMod N, |u y| := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [norm_mul, norm_eZMod, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [Finset.sum_add_distrib, hsum_u, add_zero]
    exact hnorm
  -- Averaging gives y with |u(y)| + u(y) ≥ ‖1̂_A(r)‖ · ‖1̂_P(r)‖ / N, hence u(y) ≥ ... / (2 N)
  have hex_y : ∃ y : ZMod N,
      (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (N : ℝ) ≤ |u y| + u y := by
    by_contra hall
    push Not at hall
    have hlt : ∑ y : ZMod N, (|u y| + u y) <
        ∑ _y : ZMod N, ((‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (N : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun y _ => hall y)
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        mul_div_cancel₀ _ (ne_of_gt hNpos)] at hlt
    linarith
  -- Either product = 0 (pick y with u y ≥ 0) or product > 0 (so |u y| + u y > 0 ⇒ u y > 0)
  by_cases hprod0 : ‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖ = 0
  · have hex_nn : ∃ y : ZMod N, 0 ≤ u y := by
      by_contra hall
      push Not at hall
      have hlt : ∑ y : ZMod N, u y < ∑ _y : ZMod N, (0 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun y _ => hall y)
      rw [hsum_u, Finset.sum_const_zero] at hlt
      linarith
    obtain ⟨y, hy⟩ := hex_nn
    refine ⟨y, ?_⟩
    rw [hprod0, zero_div, add_zero]
    have hcnt_ge : α * (P.card : ℝ) ≤ (cnt y : ℝ) := by simp only [u] at hy; linarith
    exact (le_div_iff₀ hPpos).mpr hcnt_ge
  · obtain ⟨y, hy⟩ := hex_y
    have hprod_pos : 0 < ‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖ :=
      lt_of_le_of_ne (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm hprod0)
    have huy_pos : 0 < u y := by
      by_contra hle
      have habs : |u y| = -u y := abs_of_nonpos (not_lt.mp hle)
      rw [habs, neg_add_cancel] at hy
      have : (0 : ℝ) < (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (N : ℝ) := by positivity
      linarith
    have h2u : (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (N : ℝ) ≤ 2 * u y := by
      rw [abs_of_pos huy_pos] at hy; linarith
    refine ⟨y, ?_⟩
    have hcnt_ge : α * (P.card : ℝ) +
        (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (2 * (N : ℝ)) ≤ (cnt y : ℝ) := by
      have hdiv2 : (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (2 * (N : ℝ)) =
          ((‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (N : ℝ)) / 2 := by ring
      simp only [u] at h2u
      linarith
    rw [le_div_iff₀ hPpos]
    have hlhs : (α + (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (2 * (N : ℝ) * (P.card : ℝ))) *
        (P.card : ℝ) = α * (P.card : ℝ) +
        (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (2 * (N : ℝ)) := by
      field_simp
    linarith

/-- **Roth Bohr-Set Density Increment Theorem**:
If `N` is odd and `A ⊆ ZMod N` is nonempty, 3-AP-free, with `2 N ≤ |A|^2` (density `α = |A|/N`),
then there exist a nonzero frequency `r ≠ 0` and a shift `y ∈ ZMod N` such that the unit Bohr set
`P = bohrSet N r 1` has size `|P| ≥ N / 6` and `A` achieves density increment at least `α + α^2 / 8`
on the Bohr translate `y - P`. -/
theorem roth_bohr_density_increment {N : ℕ} [NeZero N] (hodd : Odd N)
    (A : Finset (ZMod N)) (hA : A.Nonempty) (hfree : IsThreeAPFree A)
    (hdense : 2 * (N : ℝ) ≤ (A.card : ℝ) ^ 2) :
    ∃ r : ZMod N, r ≠ 0 ∧ ∃ y : ZMod N,
      (N : ℝ) / 6 ≤ ((bohrSet N r 1).card : ℝ) ∧
      (A.card : ℝ) / (N : ℝ) + ((A.card : ℝ) / (N : ℝ)) ^ 2 / 8 ≤
        ((A ∩ (bohrSet N r 1).image (fun p => y - p)).card : ℝ) / ((bohrSet N r 1).card : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨r, hrne, hfour⟩ := roth_large_fourier_coeff hodd A hA hfree hdense
  let P : Finset (ZMod N) := bohrSet N r 1
  have hPne : P.Nonempty := ⟨0, zero_mem_bohrSet N r zero_le_one⟩
  have hPpos : (0 : ℝ) < (P.card : ℝ) := Nat.cast_pos.mpr hPne.card_pos
  have hPcard : (N : ℝ) / 6 ≤ (P.card : ℝ) := bohrSet_card_ge_div_six N r
  have hPfour : (P.card : ℝ) / 2 ≤ ‖dft (indicatorC P) r‖ := norm_dft_bohrSet_ge_half r
  obtain ⟨y, hy⟩ := density_increment_of_fourier A P hPne hrne
  refine ⟨r, hrne, y, hPcard, ?_⟩
  have hinc : ((A.card : ℝ) / (N : ℝ)) ^ 2 / 8 ≤
      (‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖) / (2 * (N : ℝ) * (P.card : ℝ)) := by
    have hprod : ((A.card : ℝ) ^ 2 / (2 * (N : ℝ))) * ((P.card : ℝ) / 2) ≤
        ‖dft (indicatorC A) r‖ * ‖dft (indicatorC P) r‖ :=
      mul_le_mul hfour hPfour (by positivity) (norm_nonneg _)
    have hdiv := div_le_div_of_nonneg_right hprod (show (0 : ℝ) ≤ 2 * (N : ℝ) * (P.card : ℝ) by positivity)
    have hsimp : ((A.card : ℝ) ^ 2 / (2 * (N : ℝ))) * ((P.card : ℝ) / 2) /
        (2 * (N : ℝ) * (P.card : ℝ)) = ((A.card : ℝ) / (N : ℝ)) ^ 2 / 8 := by
      field_simp; ring
    linarith
  linarith

end LargeSpectrumAndRoth

end DiscreteFourier

end Arith4Ext.AdditiveFourier
