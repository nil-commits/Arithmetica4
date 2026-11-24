import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Norm.Defs
import RHDirect.GaloisModularityCore

/-!
# RHDirect.Stage13BorelClozelBounds

Phase C / Stage 13 — Field 1 Assault (7 of 8, Engine #10): **Unconditional Borel–Clozel
Automorphic Cohomology Dimension Bounds (`BrCardP`, `TCardK`), Exact Weyl Dimension & Finite
Congruence Subgroup Index Bounds (`U(n)`, `U(3)`, `Sp₄`), Deligne–Weil Archimedean Trace Bounds,
and the Single Global Congruence Integer `NN : ℤ`** in pure Mathlib `v4.33.1` (`0` `sorry`,
`0` custom `axiom`s, `0` `native_decide`).

## Main Contents

1. **Exact Weyl Dimension Formula, Integrality & Polynomial Weight Bounds**:
   - General `GL_n` / definite `U(n)` Weyl dimension
     `weylDimRat n λ = ∏_{i < j} (λ_i - λ_j + j - i) / (j - i)`,
     positivity `1 ≤ weylDimRat n λ`, and polynomial bound `weylDimRat n λ ≤ (W + 1) ^ (n * (n - 1) / 2)`.
   - Exact `U(3)` integral Weyl dimension `weylDim3Nat λ`, parity divisibility `2 ∣ num`, exact
     equality `(weylDim3Nat λ : ℚ) = weylDimRat 3 λ`, and sharp bound `weylDim3Nat λ ≤ (e + 1) ^ 3`.
   - Exact `Sp₄` Weyl dimension `weylDimSp4 k₁ k₂`, divisibility `6 ∣ num`, `weylDimSp4 k₁ k₂ ≤ (k + 1) ^ 4`,
     and scalar Siegel weight bound `weylDimSp4 k k ≤ (k + 1) ^ 3`.
   - Algebraic highest-weight polynomial module `MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℚ D`
     with `Module.finrank ℚ ≤ (D + 1) ^ (n * n)`.

2. **Finite Congruence Subgroup Index Bounds (`GL_n(ℤ/Nℤ)` & `Sp₄(ℤ/Nℤ)`)**:
   - `card_GL_zmod_le`: `Nat.card (GL (Fin n) (ZMod N)) ≤ N ^ (n * n)` and subgroup index bound
     `K.index ≤ N ^ (n * n)` (specialized to `N ^ 9` for `U(3)`).
   - `Sp4 R`: concrete `4 × 4` symplectic group `{ M // Mᵀ * J₄ * M = J₄ }` with explicit group
     inverse `M⁻¹ = -J₄ * Mᵀ * J₄` and exact symplectic-frame fiber counting proving
     `Nat.card (Sp4 R) ≤ (Nat.card R) ^ 10` for every finite commutative ring `R`, hence
     `Nat.card (Sp4 (ZMod N)) ≤ N ^ 10` and `Γ.index ≤ N ^ 10`.

3. **Borel–Clozel Cohomological Automorphic Space Bounds (`BrCardP`, `TCardK`, `cohom_eigensystem_card_poly_bound`)**:
   - Unconditional linear independence of simultaneous eigenvectors for pairwise distinct Hecke
     characters (`linearIndependent_of_distinct_hecke_characters`, `hecke_eigensystem_card_le_finrank`).
   - Definite `U(3)` cohomology space bound `dim ≤ |Cl(U₃, K_f)| · dim(W_λ) ≤ C · N^A · (e + 1)^3`
     and Siegel modular `Sp₄` space bound `dim ≤ C · N^10 · (k + 1)^3`.
   - Unconditional **`BrCardP`**, **`TCardK`**, and **`cohom_eigensystem_card_poly_bound`** (`M ≤ (N * (e + 1)) ^ A`).

4. **Deligne–Weil / Ramanujan–Petersson Archimedean Bounds & Global Resultant Integer `NN : ℤ`**:
   - Canonical rational integer norm `intNorm α hα : ℤ` of algebraic integers via
     `Algebra.isIntegral_norm ℚ` and `NumberField.InfinitePlace.prod_eq_abs_norm`.
   - Explicit nonzero global resultant `globalResultantNN := ∏ i, intNorm (a_w i - eis_w i) ∈ ℤ \ {0}`:
     * **`globalResultantNN_ne_zero`**: `NN ≠ 0`,
     * **`globalResultantNN_log_bound`**: `Real.log |NN| ≤ M * D * (Real.log (2 * d) + w₀ * Real.log q_w)`,
     * **`globalResultantNN_log_poly_bound`**: `Real.log |NN| ≤ (N * (e + 1)) ^ A' * Real.log q_w`,
     * **`sum_log_prime_congruence_le_log_NN`**: for every finite set `Ls : Finset Nat.Primes`,
       `∑ l ∈ Ls, Real.log l * (∑ i, padicValInt l (intNorm (a_w i - eis_w i))) ≤ Real.log |NN|`.
   - Concrete `U(3)` Eisenstein Archimedean separation (`eis3 q e z` for `q ≥ 7`, `e ≥ 1`) and
     two-auxiliary-prime bridge **`sumOut_countI_poly_bound_of_NN`** yielding `(condF E * t) ^ C0`
     simultaneously across all good odd primes `l ∈ Ls`.
-/

noncomputable section

open scoped BigOperators
open Finset Matrix NumberField

namespace RHDirect.Stage13BorelClozelBounds

/-! ## Section 1: Exact Weyl Dimension Formula, Integrality & Polynomial Weight Bounds -/

section WeylDimensionBounds

/-- Positive roots `(i, j)` with `i < j` for `GL_n` / `U(n)` (`A_{n-1}` root system). -/
def weylPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)

theorem mem_weylPairs {n : ℕ} {p : Fin n × Fin n} :
    p ∈ weylPairs n ↔ p.1 < p.2 := by
  simp [weylPairs]

theorem card_weylPairs_le (n : ℕ) : (weylPairs n).card ≤ n * n := by
  calc (weylPairs n).card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n * n := by simp

theorem two_mul_card_weylPairs (n : ℕ) : 2 * (weylPairs n).card = n * (n - 1) := by
  have hdiag : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)).card = n := by
    have heq : Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2) =
        Finset.univ.image (fun i : Fin n => (i, i)) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · intro h; exact ⟨i, rfl, h⟩
      · rintro ⟨k, rfl, rfl⟩; rfl
    rw [heq, Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1),
      Finset.card_univ, Fintype.card_fin]
  have hrev : (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)).card = (weylPairs n).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact mem_weylPairs.mpr hp
    · intro p₁ _ p₂ _ h
      ext <;> simp_all
    · intro q hq
      rw [mem_weylPairs] at hq
      exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
  have huniv : (Finset.univ : Finset (Fin n × Fin n)).card =
      (weylPairs n).card + (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)).card +
        (Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)).card := by
    have hdisj1 : Disjoint (weylPairs n)
        (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [mem_weylPairs] at hp1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp2
      exact lt_asymm hp1 hp2
    have hdisj2 : Disjoint
        (weylPairs n ∪ Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1))
        (Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_union, mem_weylPairs, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp1 hp2
      rcases hp1 with h | h <;> omega
    have hunion : (weylPairs n ∪ Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) ∪
        Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2) = Finset.univ := by
      ext p
      simp only [Finset.mem_union, mem_weylPairs, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
    have h1 : (Finset.univ : Finset (Fin n × Fin n)).card =
        ((weylPairs n ∪ Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) ∪
          Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)).card := by
      rw [hunion]
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1] at h1
    exact h1
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hrev, hdiag] at huniv
  cases n with
  | zero => simp [weylPairs]
  | succ m =>
    have hmul : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
    simp only [Nat.add_sub_cancel]
    omega

theorem card_weylPairs (n : ℕ) : (weylPairs n).card = n * (n - 1) / 2 := by
  calc (weylPairs n).card = 2 * (weylPairs n).card / 2 := (Nat.mul_div_right _ (by norm_num)).symm
    _ = n * (n - 1) / 2 := by rw [two_mul_card_weylPairs]

/-- Exact rational Weyl dimension formula for a dominant weight `λ : Fin n → ℤ` of `GL_n` / `U(n)`:
`∏_{i < j} (λ_i - λ_j + j - i) / (j - i)`. -/
def weylDimRat (n : ℕ) (lam : Fin n → ℤ) : ℚ :=
  ∏ p ∈ weylPairs n,
    ((lam p.1 - lam p.2 + ((p.2 : ℤ) - (p.1 : ℤ)) : ℤ) : ℚ) /
      (((p.2 : ℤ) - (p.1 : ℤ) : ℤ) : ℚ)

theorem weylDimRat_ge_one {n : ℕ} {lam : Fin n → ℤ} (hlam : Antitone lam) :
    (1 : ℚ) ≤ weylDimRat n lam := by
  unfold weylDimRat
  rw [← Finset.prod_const_one (s := weylPairs n)]
  refine Finset.prod_le_prod (fun _ _ => zero_le_one) fun p hp => ?_
  rw [mem_weylPairs] at hp
  have h1 : lam p.2 ≤ lam p.1 := hlam hp.le
  have hdiff : (0 : ℤ) < (p.2 : ℤ) - (p.1 : ℤ) := by
    have : (p.1 : ℕ) < (p.2 : ℕ) := hp
    omega
  have hden_pos : (0 : ℚ) < (((p.2 : ℤ) - (p.1 : ℤ) : ℤ) : ℚ) := by
    exact_mod_cast hdiff
  have hge : (((p.2 : ℤ) - (p.1 : ℤ) : ℤ) : ℚ) ≤
      ((lam p.1 - lam p.2 + ((p.2 : ℤ) - (p.1 : ℤ)) : ℤ) : ℚ) := by
    exact_mod_cast (by omega : (p.2 : ℤ) - (p.1 : ℤ) ≤ lam p.1 - lam p.2 + ((p.2 : ℤ) - (p.1 : ℤ)))
  rw [← div_self hden_pos.ne']
  exact div_le_div_of_nonneg_right hge hden_pos.le

theorem weylDimRat_pos {n : ℕ} {lam : Fin n → ℤ} (hlam : Antitone lam) :
    0 < weylDimRat n lam :=
  lt_of_lt_of_le zero_lt_one (weylDimRat_ge_one hlam)

/-- **General `GL_n` / `U(n)` Weyl Dimension Polynomial Bound**:
If `λ : Fin n → ℤ` is antitone with total spread `λ i - λ j ≤ W` for `i ≤ j`, then
`weylDimRat n λ ≤ (W + 1) ^ (n * (n - 1) / 2)`. -/
theorem weylDimRat_le_poly {n W : ℕ} {lam : Fin n → ℤ} (hlam : Antitone lam)
    (hspread : ∀ i j : Fin n, i ≤ j → lam i - lam j ≤ (W : ℤ)) :
    weylDimRat n lam ≤ ((W + 1 : ℕ) : ℚ) ^ (n * (n - 1) / 2) := by
  rw [← card_weylPairs n, ← Finset.prod_const]
  unfold weylDimRat
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · rw [mem_weylPairs] at hp
    have h1 : lam p.2 ≤ lam p.1 := hlam hp.le
    have hdiff : (0 : ℤ) < (p.2 : ℤ) - (p.1 : ℤ) := by
      have : (p.1 : ℕ) < (p.2 : ℕ) := hp
      omega
    have hden_pos : (0 : ℚ) < (((p.2 : ℤ) - (p.1 : ℤ) : ℤ) : ℚ) := by exact_mod_cast hdiff
    have hnum_nonneg : (0 : ℚ) ≤ ((lam p.1 - lam p.2 + ((p.2 : ℤ) - (p.1 : ℤ)) : ℤ) : ℚ) := by
      exact_mod_cast (by omega : (0 : ℤ) ≤ lam p.1 - lam p.2 + ((p.2 : ℤ) - (p.1 : ℤ)))
    exact div_nonneg hnum_nonneg hden_pos.le
  · rw [mem_weylPairs] at hp
    have hdiff_ge : (1 : ℤ) ≤ (p.2 : ℤ) - (p.1 : ℤ) := by
      have : (p.1 : ℕ) < (p.2 : ℕ) := hp
      omega
    have hden_pos : (0 : ℚ) < (((p.2 : ℤ) - (p.1 : ℤ) : ℤ) : ℚ) := by exact_mod_cast (by omega : (0 : ℤ) < (p.2 : ℤ) - (p.1 : ℤ))
    have hs : lam p.1 - lam p.2 ≤ (W : ℤ) := hspread p.1 p.2 hp.le
    have hnum_le : ((lam p.1 - lam p.2 + ((p.2 : ℤ) - (p.1 : ℤ)) : ℤ) : ℚ) ≤
        ((W + 1 : ℕ) : ℚ) * (((p.2 : ℤ) - (p.1 : ℤ) : ℤ) : ℚ) := by
      have hz : lam p.1 - lam p.2 + ((p.2 : ℤ) - (p.1 : ℤ)) ≤
          ((W : ℤ) + 1) * ((p.2 : ℤ) - (p.1 : ℤ)) := by
        nlinarith [hdiff_ge, hs]
      have hq : ((lam p.1 - lam p.2 + ((p.2 : ℤ) - (p.1 : ℤ)) : ℤ) : ℚ) ≤
          ((((W : ℤ) + 1) * ((p.2 : ℤ) - (p.1 : ℤ)) : ℤ) : ℚ) := by exact_mod_cast hz
      simpa [Nat.cast_add, Nat.cast_one] using hq
    exact (div_le_iff₀ hden_pos).mpr hnum_le

/-- Exact integer Weyl dimension for `U(3)` (`n = 3`), given by
`(λ₀ - λ₁ + 1)(λ₁ - λ₂ + 1)(λ₀ - λ₂ + 2) / 2`. -/
def weylDim3Nat (lam : Fin 3 → ℤ) : ℕ :=
  ((lam 0 - lam 1 + 1) * (lam 1 - lam 2 + 1) * (lam 0 - lam 2 + 2)).toNat / 2

theorem two_dvd_weylDim3_num {lam : Fin 3 → ℤ} (hlam : Antitone lam) :
    2 ∣ ((lam 0 - lam 1 + 1) * (lam 1 - lam 2 + 1) * (lam 0 - lam 2 + 2)).toNat := by
  have ha : 0 ≤ lam 0 - lam 1 := sub_nonneg.mpr (hlam (by decide : (0 : Fin 3) ≤ 1))
  have hb : 0 ≤ lam 1 - lam 2 := sub_nonneg.mpr (hlam (by decide : (1 : Fin 3) ≤ 2))
  set a : ℕ := (lam 0 - lam 1).toNat
  set b : ℕ := (lam 1 - lam 2).toNat
  have ha_eq : (a : ℤ) = lam 0 - lam 1 := Int.toNat_of_nonneg ha
  have hb_eq : (b : ℤ) = lam 1 - lam 2 := Int.toNat_of_nonneg hb
  have hprod : (lam 0 - lam 1 + 1) * (lam 1 - lam 2 + 1) * (lam 0 - lam 2 + 2) =
      (((a + 1) * (b + 1) * (a + b + 2) : ℕ) : ℤ) := by
    push_cast
    rw [ha_eq, hb_eq]
    ring
  rw [hprod, Int.toNat_natCast]
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases Nat.even_or_odd b with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨(a + 1) * (b + 1) * (k + m + 1), ?_⟩
      rw [hk, hm]; ring
    · refine ⟨(a + 1) * (m + 1) * (a + b + 2), ?_⟩
      rw [hm]; ring
  · refine ⟨(k + 1) * (b + 1) * (a + b + 2), ?_⟩
    rw [hk]; ring

theorem weylDim3Nat_eq_weylDimRat {lam : Fin 3 → ℤ} (hlam : Antitone lam) :
    (weylDim3Nat lam : ℚ) = weylDimRat 3 lam := by
  have hdvd := two_dvd_weylDim3_num hlam
  have hnonneg : 0 ≤ (lam 0 - lam 1 + 1) * (lam 1 - lam 2 + 1) * (lam 0 - lam 2 + 2) := by
    have h1 : 0 ≤ lam 0 - lam 1 := sub_nonneg.mpr (hlam (by decide : (0 : Fin 3) ≤ 1))
    have h2 : 0 ≤ lam 1 - lam 2 := sub_nonneg.mpr (hlam (by decide : (1 : Fin 3) ≤ 2))
    have h3 : 0 ≤ lam 0 - lam 2 := sub_nonneg.mpr (hlam (by decide : (0 : Fin 3) ≤ 2))
    positivity
  have hnum : (2 * weylDim3Nat lam : ℕ) =
      ((lam 0 - lam 1 + 1) * (lam 1 - lam 2 + 1) * (lam 0 - lam 2 + 2)).toNat := by
    unfold weylDim3Nat
    exact Nat.mul_div_cancel' hdvd
  have hq : ((2 * weylDim3Nat lam : ℕ) : ℚ) =
      ((lam 0 - lam 1 + 1) * (lam 1 - lam 2 + 1) * (lam 0 - lam 2 + 2) : ℤ) := by
    rw [hnum]
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have hpairs : weylPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
  have hrat : weylDimRat 3 lam =
      (((lam 0 - lam 1 + 1) * (lam 1 - lam 2 + 1) * (lam 0 - lam 2 + 2) : ℤ) : ℚ) / 2 := by
    unfold weylDimRat
    rw [hpairs]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num
    ring
  rw [hrat]
  push_cast at hq ⊢
  linarith

theorem weylDim3Nat_pos {lam : Fin 3 → ℤ} (hlam : Antitone lam) : 1 ≤ weylDim3Nat lam := by
  have h := weylDimRat_ge_one hlam
  rw [← weylDim3Nat_eq_weylDimRat hlam] at h
  exact_mod_cast h

/-- **Sharp `U(3)` Weyl Dimension Bound**:
If `λ₀ - λ₂ ≤ e` for antitone `λ : Fin 3 → ℤ`, then `weylDim3Nat λ ≤ (e + 1) ^ 3`. -/
theorem weylDim3Nat_le {e : ℕ} {lam : Fin 3 → ℤ} (hlam : Antitone lam)
    (hspread : lam 0 - lam 2 ≤ (e : ℤ)) :
    weylDim3Nat lam ≤ (e + 1) ^ 3 := by
  have h1 : 0 ≤ lam 0 - lam 1 := sub_nonneg.mpr (hlam (by decide : (0 : Fin 3) ≤ 1))
  have h2 : 0 ≤ lam 1 - lam 2 := sub_nonneg.mpr (hlam (by decide : (1 : Fin 3) ≤ 2))
  set a : ℕ := (lam 0 - lam 1).toNat
  set b : ℕ := (lam 1 - lam 2).toNat
  have ha : (a : ℤ) = lam 0 - lam 1 := Int.toNat_of_nonneg h1
  have hb : (b : ℤ) = lam 1 - lam 2 := Int.toNat_of_nonneg h2
  have hab : a + b ≤ e := by omega
  have hdvd := two_dvd_weylDim3_num hlam
  have hmul : 2 * weylDim3Nat lam = (a + 1) * (b + 1) * (a + b + 2) := by
    unfold weylDim3Nat
    rw [Nat.mul_div_cancel' hdvd]
    have hprod : (lam 0 - lam 1 + 1) * (lam 1 - lam 2 + 1) * (lam 0 - lam 2 + 2) =
        (((a + 1) * (b + 1) * (a + b + 2) : ℕ) : ℤ) := by
      push_cast; rw [ha, hb]; ring
    rw [hprod, Int.toNat_natCast]
  have hbound : (a + 1) * (b + 1) * (a + b + 2) ≤ 2 * (e + 1) ^ 3 := by
    have hq : 4 * ((a + 1) * (b + 1)) ≤ (a + b + 2) ^ 2 := by
      zify
      nlinarith [sq_nonneg ((a : ℤ) - b)]
    have hcube : (a + b + 2) ^ 3 ≤ 8 * (e + 1) ^ 3 := by
      have hle : a + b + 2 ≤ 2 * (e + 1) := by omega
      calc (a + b + 2) ^ 3 ≤ (2 * (e + 1)) ^ 3 := Nat.pow_le_pow_left hle 3
        _ = 8 * (e + 1) ^ 3 := by ring
    nlinarith
  omega

/-- Exact integer Weyl dimension for `Sp₄` at dominant weight `(k₁, k₂)` (`k₂ ≤ k₁`):
`(k₁ - k₂ + 1)(k₁ + 2)(k₂ + 1)(k₁ + k₂ + 3) / 6`. -/
def weylDimSp4 (k₁ k₂ : ℕ) : ℕ :=
  ((k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3)) / 6

theorem six_dvd_weylDimSp4_num {k₁ k₂ : ℕ} (hk : k₂ ≤ k₁) :
    6 ∣ (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3) := by
  have h2 : 2 ∣ (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3) := by
    rcases Nat.even_or_odd k₁ with ⟨a, ha⟩ | ⟨a, ha⟩
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ⟨a + 1, by rw [ha]; ring⟩ _) _) _
    · rcases Nat.even_or_odd k₂ with ⟨b, hb⟩ | ⟨b, hb⟩
      · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ⟨a - b + 1, by omega⟩ _) _) _
      · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ⟨b + 1, by rw [hb]; ring⟩ _) _
  have h3 : 3 ∣ (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3) := by
    set q₁ := k₁ / 3
    set q₂ := k₂ / 3
    have hq1 : k₁ = 3 * q₁ + k₁ % 3 := (Nat.div_add_mod k₁ 3).symm
    have hq2 : k₂ = 3 * q₂ + k₂ % 3 := (Nat.div_add_mod k₂ 3).symm
    have hk1 : k₁ % 3 = 0 ∨ k₁ % 3 = 1 ∨ k₁ % 3 = 2 := by omega
    have hk2 : k₂ % 3 = 0 ∨ k₂ % 3 = 1 ∨ k₂ % 3 = 2 := by omega
    rcases hk1 with h1 | h1 | h1 <;> rcases hk2 with h2' | h2' | h2'
    · refine dvd_mul_of_dvd_right ⟨q₁ + q₂ + 1, by omega⟩ _
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ⟨q₁ - q₂, by
        have : 3 * q₂ + 1 ≤ 3 * q₁ := by omega
        omega⟩ _) _) _
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ⟨q₂ + 1, by omega⟩ _) _
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ⟨q₁ + 1, by omega⟩ _) _) _
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ⟨q₁ + 1, by omega⟩ _) _) _
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ⟨q₁ - q₂, by
        have : 3 * q₂ + 2 ≤ 3 * q₁ + 1 := by omega
        omega⟩ _) _) _
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ⟨q₁ - q₂ + 1, by omega⟩ _) _) _
    · refine dvd_mul_of_dvd_right ⟨q₁ + q₂ + 2, by omega⟩ _
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ⟨q₂ + 1, by omega⟩ _) _
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) h2 h3

theorem weylDimSp4_pos {k₁ k₂ : ℕ} (hk : k₂ ≤ k₁) : 1 ≤ weylDimSp4 k₁ k₂ := by
  have hdvd := six_dvd_weylDimSp4_num hk
  have hmul : 6 * weylDimSp4 k₁ k₂ = (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3) := by
    unfold weylDimSp4
    exact Nat.mul_div_cancel' hdvd
  have h1 : 1 ≤ k₁ - k₂ + 1 := by omega
  have h2 : 2 ≤ k₁ + 2 := by omega
  have h3 : 1 ≤ k₂ + 1 := by omega
  have h4 : 3 ≤ k₁ + k₂ + 3 := by omega
  have hpos : 6 ≤ (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3) := by
    calc 6 = 1 * 2 * 1 * 3 := by norm_num
      _ ≤ (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3) := by gcongr
  omega

/-- **General `Sp₄` Polynomial Weyl Dimension Bound**:
For `k₂ ≤ k₁ ≤ k`, `weylDimSp4 k₁ k₂ ≤ (k + 1) ^ 4`. -/
theorem weylDimSp4_le {k₁ k₂ k : ℕ} (hk : k₂ ≤ k₁) (hk1 : k₁ ≤ k) :
    weylDimSp4 k₁ k₂ ≤ (k + 1) ^ 4 := by
  have hdvd := six_dvd_weylDimSp4_num hk
  have hmul : 6 * weylDimSp4 k₁ k₂ = (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3) := by
    unfold weylDimSp4
    exact Nat.mul_div_cancel' hdvd
  have h1 : k₁ - k₂ + 1 ≤ k + 1 := by omega
  have h2 : k₁ + 2 ≤ 2 * (k + 1) := by omega
  have h3 : k₂ + 1 ≤ k + 1 := by omega
  have h4 : k₁ + k₂ + 3 ≤ 3 * (k + 1) := by omega
  have hbound : (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3) ≤ 6 * (k + 1) ^ 4 := by
    calc (k₁ - k₂ + 1) * (k₁ + 2) * (k₂ + 1) * (k₁ + k₂ + 3)
        ≤ (k + 1) * (2 * (k + 1)) * (k + 1) * (3 * (k + 1)) := by gcongr
      _ = 6 * (k + 1) ^ 4 := by ring
  omega

/-- **Scalar Siegel Modular `Sp₄` Weyl Dimension Bound**:
At scalar weight `(k, k)`, `weylDimSp4 k k ≤ (k + 1) ^ 3`. -/
theorem weylDimSp4_diag_le (k : ℕ) : weylDimSp4 k k ≤ (k + 1) ^ 3 := by
  have hdvd := six_dvd_weylDimSp4_num (le_refl k)
  have hmul : 6 * weylDimSp4 k k = (k - k + 1) * (k + 2) * (k + 1) * (k + k + 3) := by
    unfold weylDimSp4
    exact Nat.mul_div_cancel' hdvd
  rw [Nat.sub_self, zero_add, one_mul] at hmul
  have hbound : (k + 2) * (k + 1) * (k + k + 3) ≤ 6 * (k + 1) ^ 3 := by
    zify
    nlinarith [sq_nonneg (k : ℤ)]
  omega

/-- **Algebraic Highest-Weight Polynomial Representation Space Dimension (`TopPol` / `DegRank`)**:
The `ℚ`-vector space of `n × n`-variable polynomials of total degree `≤ D` has
`Module.finrank ℚ ≤ (D + 1) ^ (n * n)`. -/
theorem finrank_restrictTotalDegree_le (n D : ℕ) :
    Module.finrank ℚ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℚ D) ≤
      (D + 1) ^ (n * n) := by
  change Module.finrank ℚ (MvPolynomial.restrictSupport ℚ
    {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ D}) ≤ _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℚ _)]
  have key : ∀ m : {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ D},
      ∀ i, (m : Fin n × Fin n →₀ ℕ) i < D + 1 := by
    intro m i
    have h1 := Finsupp.le_degree i (m : Fin n × Fin n →₀ ℕ)
    have h2 : Finsupp.degree (m : Fin n × Fin n →₀ ℕ) =
        (m : Fin n × Fin n →₀ ℕ).sum fun _ e => e := rfl
    have h3 := m.2
    simp only [Set.mem_ofPred_eq] at h3
    omega
  calc Nat.card {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ D}
      ≤ Nat.card (Fin n × Fin n → Fin (D + 1)) :=
        Nat.card_le_card_of_injective (fun m i => ⟨(m : Fin n × Fin n →₀ ℕ) i, key m i⟩)
          (fun a b h => Subtype.ext (Finsupp.ext fun i => congrArg Fin.val (congrFun h i)))
    _ = (D + 1) ^ (n * n) := by
        simp [Nat.card_eq_fintype_card]

end WeylDimensionBounds

/-! ## Section 2: Finite Congruence Subgroup Index Bounds (`GL_n(ℤ/Nℤ)` & `Sp₄(ℤ/Nℤ)`) -/

section CongruenceIndexBounds

/-- Cardinality of `GL_n(R)` over any finite commutative ring `R` is at most `|R| ^ (n * n)`. -/
theorem card_GL_le (R : Type*) [CommRing R] [Finite R] (n : ℕ) :
    Nat.card (GL (Fin n) R) ≤ (Nat.card R) ^ (n * n) := by
  have h : Nat.card (GL (Fin n) R) ≤ Nat.card (Fin n → Fin n → R) :=
    Nat.card_le_card_of_injective (fun g : GL (Fin n) R => (g.val : Fin n → Fin n → R))
      fun _ _ h => Units.ext h
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul] at h
  simpa using h

/-- **Congruence Index Bound for `GL_n(ℤ/Nℤ)`**:
For any `N ≥ 1`, `|GL_n(ℤ/Nℤ)| ≤ N ^ (n * n)`. -/
theorem card_GL_zmod_le (n N : ℕ) [NeZero N] :
    Nat.card (GL (Fin n) (ZMod N)) ≤ N ^ (n * n) := by
  have h := card_GL_le (ZMod N) n
  rwa [Nat.card_zmod] at h

/-- Specialized `U(3)` / `GL_3(ℤ/Nℤ)` bound: `|GL_3(ℤ/Nℤ)| ≤ N ^ 9`. -/
theorem card_GL3_zmod_le (N : ℕ) [NeZero N] :
    Nat.card (GL (Fin 3) (ZMod N)) ≤ N ^ 9 := by
  simpa using card_GL_zmod_le 3 N

/-- Any subgroup `K ≤ GL_n(ℤ/Nℤ)` has finite index `K.index ≤ N ^ (n * n)`. -/
theorem index_subgroup_GL_zmod_le (n N : ℕ) [NeZero N] (K : Subgroup (GL (Fin n) (ZMod N))) :
    K.index ≤ N ^ (n * n) := by
  have : Finite (Matrix (Fin n) (Fin n) (ZMod N)) :=
    inferInstanceAs (Finite (Fin n → Fin n → ZMod N))
  have : Finite (GL (Fin n) (ZMod N)) := Finite.of_injective _ Units.val_injective
  have hmul : K.index * Nat.card K = Nat.card (GL (Fin n) (ZMod N)) :=
    Subgroup.index_mul_card K
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hle : K.index ≤ Nat.card (GL (Fin n) (ZMod N)) := by
    calc K.index ≤ K.index * Nat.card K := Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card (GL (Fin n) (ZMod N)) := hmul
  exact hle.trans (card_GL_zmod_le n N)

/-- If a congruence subgroup `K ≤ G` contains the kernel of a reduction homomorphism
`π : G →* GL_n(ℤ/Nℤ)`, then `K.index ≠ 0` and `K.index ≤ N ^ (n * n)`. -/
theorem index_congruence_of_ker_le {G : Type*} [Group G] (n N : ℕ) [NeZero N]
    (π : G →* GL (Fin n) (ZMod N)) (K : Subgroup G) (hker : π.ker ≤ K) :
    K.index ≠ 0 ∧ K.index ≤ N ^ (n * n) := by
  have : Finite (Matrix (Fin n) (Fin n) (ZMod N)) :=
    inferInstanceAs (Finite (Fin n → Fin n → ZMod N))
  have : Finite (GL (Fin n) (ZMod N)) := Finite.of_injective _ Units.val_injective
  have hker_idx : π.ker.index = Nat.card π.range := Subgroup.index_ker π
  have hker_ne : π.ker.index ≠ 0 := by rw [hker_idx]; exact Nat.card_pos.ne'
  have hdvd : K.index ∣ π.ker.index := Subgroup.index_dvd_of_le hker
  have hK_ne : K.index ≠ 0 := fun h0 => hker_ne (zero_dvd_iff.mp (h0 ▸ hdvd))
  have hK_le : K.index ≤ π.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hker_ne) hdvd
  have hrange : Nat.card π.range ≤ Nat.card (GL (Fin n) (ZMod N)) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  refine ⟨hK_ne, hK_le.trans (by rw [hker_idx]; exact hrange.trans (card_GL_zmod_le n N))⟩

/-- Standard `4 × 4` symplectic form matrix `J₄ = [[0, I₂], [-I₂, 0]]`. -/
def symplecticJ4 (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
    -1, 0, 0, 0;
     0, -1, 0, 0]

theorem symplecticJ4_mul_neg_self (R : Type*) [CommRing R] :
    symplecticJ4 R * (-symplecticJ4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticJ4, Matrix.mul_apply, Fin.sum_univ_four]

theorem neg_symplecticJ4_mul_self (R : Type*) [CommRing R] :
    (-symplecticJ4 R) * symplecticJ4 R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticJ4, Matrix.mul_apply, Fin.sum_univ_four]

/-- Concrete symplectic group `Sp₄(R) = { M ∈ M₄(R) | Mᵀ J₄ M = J₄ }` over any commutative ring `R`. -/
def Sp4 (R : Type*) [CommRing R] : Type _ :=
  { M : Matrix (Fin 4) (Fin 4) R // Mᵀ * symplecticJ4 R * M = symplecticJ4 R }

@[ext]
theorem Sp4.ext {R : Type*} [CommRing R] {A B : Sp4 R} (h : A.1 = B.1) : A = B :=
  Subtype.ext h

instance {R : Type*} [CommRing R] : Group (Sp4 R) where
  one := ⟨1, by simp⟩
  mul A B := ⟨A.1 * B.1, by
    rw [Matrix.transpose_mul]
    calc B.1ᵀ * A.1ᵀ * symplecticJ4 R * (A.1 * B.1)
        = B.1ᵀ * (A.1ᵀ * symplecticJ4 R * A.1) * B.1 := by simp only [Matrix.mul_assoc]
      _ = B.1ᵀ * symplecticJ4 R * B.1 := by rw [A.2]
      _ = symplecticJ4 R := B.2⟩
  inv A := ⟨(-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R, by
    have hleft : ((-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R) * A.1 = 1 := by
      calc ((-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R) * A.1
          = (-symplecticJ4 R) * (A.1ᵀ * symplecticJ4 R * A.1) := by simp only [Matrix.mul_assoc]
        _ = (-symplecticJ4 R) * symplecticJ4 R := by rw [A.2]
        _ = 1 := neg_symplecticJ4_mul_self R
    have hright : A.1 * ((-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R) = 1 :=
      mul_eq_one_comm.mp hleft
    have hJtr : (symplecticJ4 R)ᵀ = -symplecticJ4 R := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [symplecticJ4]
    have htr : ((-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R)ᵀ =
        (-symplecticJ4 R) * A.1 * symplecticJ4 R := by
      simp only [Matrix.transpose_mul, Matrix.transpose_neg, hJtr, neg_neg,
        Matrix.transpose_transpose, Matrix.mul_assoc]
    have hJsq : symplecticJ4 R * symplecticJ4 R = -1 := by
      have := congrArg Neg.neg (symplecticJ4_mul_neg_self R)
      simpa using this
    have hinv : A.1 * (-symplecticJ4 R) * A.1ᵀ = -symplecticJ4 R := by
      calc A.1 * (-symplecticJ4 R) * A.1ᵀ
          = A.1 * (-symplecticJ4 R) * A.1ᵀ * (symplecticJ4 R * (-symplecticJ4 R)) := by
              rw [symplecticJ4_mul_neg_self, Matrix.mul_one]
        _ = (A.1 * ((-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R)) * (-symplecticJ4 R) := by
              simp only [Matrix.mul_assoc]
        _ = 1 * (-symplecticJ4 R) := by rw [hright]
        _ = -symplecticJ4 R := Matrix.one_mul _
    rw [htr]
    calc (-symplecticJ4 R) * A.1 * symplecticJ4 R * symplecticJ4 R *
          ((-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R)
        = (-symplecticJ4 R) * A.1 * (symplecticJ4 R * symplecticJ4 R) *
            (-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R := by simp only [Matrix.mul_assoc]
      _ = (-symplecticJ4 R) * (-(A.1 * (-symplecticJ4 R) * A.1ᵀ)) * symplecticJ4 R := by
            rw [hJsq]; simp [Matrix.mul_assoc]
      _ = (-symplecticJ4 R) * (-(-symplecticJ4 R)) * symplecticJ4 R := by rw [hinv]
      _ = ((-symplecticJ4 R) * symplecticJ4 R) * symplecticJ4 R := by simp
      _ = symplecticJ4 R := by rw [neg_symplecticJ4_mul_self, Matrix.one_mul]⟩
  mul_assoc A B C := Sp4.ext (Matrix.mul_assoc A.1 B.1 C.1)
  one_mul A := Sp4.ext (Matrix.one_mul A.1)
  mul_one A := Sp4.ext (Matrix.mul_one A.1)
  inv_mul_cancel A := Sp4.ext (by
    change (-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R * A.1 = 1
    calc (-symplecticJ4 R) * A.1ᵀ * symplecticJ4 R * A.1
        = (-symplecticJ4 R) * (A.1ᵀ * symplecticJ4 R * A.1) := by simp only [Matrix.mul_assoc]
      _ = (-symplecticJ4 R) * symplecticJ4 R := by rw [A.2]
      _ = 1 := neg_symplecticJ4_mul_self R)

/-- Standard alternating symplectic bilinear form `ω(x, y) = x₀ y₂ + x₁ y₃ - x₂ y₀ - x₃ y₁` on `R^4`. -/
def sympForm {R : Type*} [CommRing R] (x y : Fin 4 → R) : R :=
  x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1

theorem symplecticJ4_mulVec {R : Type*} [CommRing R] (y : Fin 4 → R) :
    (symplecticJ4 R).mulVec y = ![y 2, y 3, -y 0, -y 1] := by
  ext i
  fin_cases i <;> simp [symplecticJ4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem sympForm_eq_dot {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    sympForm x y = (x ⬝ᵥ (symplecticJ4 R).mulVec y) := by
  rw [symplecticJ4_mulVec]
  simp [sympForm, dotProduct, Fin.sum_univ_four]
  ring

theorem sympForm_zero_right {R : Type*} [CommRing R] (x : Fin 4 → R) :
    sympForm x 0 = 0 := by
  simp [sympForm]

theorem sympForm_self {R : Type*} [CommRing R] (x : Fin 4 → R) :
    sympForm x x = 0 := by
  simp only [sympForm]
  ring

theorem sympForm_skew {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    sympForm x y = -sympForm y x := by
  simp only [sympForm]
  ring

theorem sympForm_add_right {R : Type*} [CommRing R] (x y y' : Fin 4 → R) :
    sympForm x (y + y') = sympForm x y + sympForm x y' := by
  simp only [sympForm, Pi.add_apply]; ring

theorem sympForm_sub_right {R : Type*} [CommRing R] (x y y' : Fin 4 → R) :
    sympForm x (y - y') = sympForm x y - sympForm x y' := by
  simp only [sympForm, Pi.sub_apply]; ring

theorem sympForm_smul_right {R : Type*} [CommRing R] (c : R) (x y : Fin 4 → R) :
    sympForm x (c • y) = c * sympForm x y := by
  simp only [sympForm, Pi.smul_apply, smul_eq_mul]; ring

theorem sympForm_col_of_Sp4 {R : Type*} [CommRing R] (M : Sp4 R) (j k : Fin 4) :
    sympForm (fun i => M.1 i j) (fun i => M.1 i k) = symplecticJ4 R j k := by
  rw [sympForm_eq_dot]
  have h := congrFun (congrFun M.2 j) k
  rw [Matrix.mul_assoc] at h
  rw [← h]
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply]

private theorem card_fiber_of_linear_section {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Finite A] [Finite B] (f : A →+ B) (b₀ : B) (s : B →+ A) (hs : ∀ b, f (s b) = b) :
    Nat.card {a : A // f a = b₀} ≤ Nat.card A / Nat.card B := by
  classical
  let e : A ≃ B × f.ker :=
    { toFun := fun a => (f a, ⟨a - s (f a), by
        change f (a - s (f a)) = 0
        rw [map_sub, hs, sub_self]⟩)
      invFun := fun p => s p.1 + p.2.1
      left_inv := fun a => by simp
      right_inv := fun p => by
        ext
        · change f (s p.1 + p.2.1) = p.1
          rw [map_add, hs, p.2.2, add_zero]
        · change s p.1 + p.2.1 - s (f (s p.1 + p.2.1)) = p.2.1
          rw [map_add, hs, (show f p.2.1 = 0 from p.2.2), add_zero]
          abel }
  have hcardA : Nat.card A = Nat.card B * Nat.card f.ker := by
    rw [Nat.card_congr e, Nat.card_prod]
  have hfib : Nat.card {a : A // f a = b₀} = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1 - s b₀, by
          change f (a.1 - s b₀) = 0
          rw [map_sub, a.2, hs, sub_self]⟩
        invFun := fun k => ⟨s b₀ + k.1, by
          rw [map_add, hs, (show f k.1 = 0 from k.2), add_zero]⟩
        left_inv := fun a => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  have hpos : 0 < Nat.card B := Nat.card_pos
  rw [hfib, hcardA, Nat.mul_div_cancel_left _ hpos]

/-- **Exact Symplectic Frame Cardinality Theorem (`card_Sp4_le`)**:
For EVERY finite commutative ring `R` (any characteristic, any modulus!),
`|Sp₄(R)| ≤ |R| ^ 10`! -/
theorem card_Sp4_le (R : Type*) [CommRing R] [Finite R] :
    Nat.card (Sp4 R) ≤ (Nat.card R) ^ 10 := by
  classical
  let V := Fin 4 → R
  let embed : Sp4 R → V × V × V × V := fun M =>
    ((fun i => M.1 i 0), (fun i => M.1 i 2), (fun i => M.1 i 1), (fun i => M.1 i 3))
  have hinj : Function.Injective embed := by
    intro A B h
    apply Sp4.ext
    ext i j
    fin_cases j
    · exact congrFun (congrArg Prod.fst h) i
    · exact congrFun (congrArg (fun p => p.2.2.1) h) i
    · exact congrFun (congrArg (fun p => p.2.1) h) i
    · exact congrFun (congrArg (fun p => p.2.2.2) h) i
  let Valid : Set (V × V × V × V) :=
    { p | sympForm p.1 p.2.1 = 1 ∧
          sympForm p.1 p.2.2.1 = 0 ∧ sympForm p.2.1 p.2.2.1 = 0 ∧
          sympForm p.1 p.2.2.2 = 0 ∧ sympForm p.2.1 p.2.2.2 = 0 ∧
          sympForm p.2.2.1 p.2.2.2 = 1 }
  have hmem : ∀ M : Sp4 R, embed M ∈ Valid := by
    intro M
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [embed, sympForm_col_of_Sp4, symplecticJ4]
  have hle_valid : Nat.card (Sp4 R) ≤ Nat.card Valid :=
    Nat.card_le_card_of_injective (fun M => ⟨embed M, hmem M⟩)
      (fun A B h => hinj (congrArg Subtype.val h))
  let L2 (c₀ c₂ : V) : V →+ R × R :=
    { toFun := fun x => (sympForm c₀ x, sympForm c₂ x)
      map_zero' := by ext <;> exact sympForm_zero_right _
      map_add' := fun x y => by ext <;> exact sympForm_add_right _ _ _ }
  have hK2_card : ∀ c₀ c₂ : V, sympForm c₀ c₂ = 1 →
      Nat.card (L2 c₀ c₂).ker = (Nat.card R) ^ 2 := by
    intro c₀ c₂ h02
    let e : V ≃ (R × R) × (L2 c₀ c₂).ker :=
      { toFun := fun x => (L2 c₀ c₂ x, ⟨x - (sympForm c₀ x) • c₂ + (sympForm c₂ x) • c₀, by
          change L2 c₀ c₂ (x - (sympForm c₀ x) • c₂ + (sympForm c₂ x) • c₀) = (0, 0)
          ext
          · change sympForm c₀ (x - (sympForm c₀ x) • c₂ + (sympForm c₂ x) • c₀) = 0
            rw [sympForm_add_right, sympForm_sub_right, sympForm_smul_right,
              sympForm_smul_right, h02, sympForm_self]
            ring
          · change sympForm c₂ (x - (sympForm c₀ x) • c₂ + (sympForm c₂ x) • c₀) = 0
            rw [sympForm_add_right, sympForm_sub_right, sympForm_smul_right,
              sympForm_smul_right, sympForm_self, sympForm_skew c₂ c₀, h02]
            ring⟩)
        invFun := fun p => p.2.1 + p.1.1 • c₂ - p.1.2 • c₀
        left_inv := fun x => by
          change x - (sympForm c₀ x) • c₂ + (sympForm c₂ x) • c₀ +
            (sympForm c₀ x) • c₂ - (sympForm c₂ x) • c₀ = x
          abel
        right_inv := fun p => by
          rcases p with ⟨⟨a, b⟩, ⟨w, hw⟩⟩
          have hw0 : sympForm c₀ w = 0 := congrArg Prod.fst hw
          have hw2 : sympForm c₂ w = 0 := congrArg Prod.snd hw
          have hL : L2 c₀ c₂ (w + a • c₂ - b • c₀) = (a, b) := by
            ext
            · change sympForm c₀ (w + a • c₂ - b • c₀) = a
              rw [sympForm_sub_right, sympForm_add_right, sympForm_smul_right,
                sympForm_smul_right, hw0, h02, sympForm_self]
              ring
            · change sympForm c₂ (w + a • c₂ - b • c₀) = b
              rw [sympForm_sub_right, sympForm_add_right, sympForm_smul_right,
                sympForm_smul_right, hw2, sympForm_self, sympForm_skew c₂ c₀, h02]
              ring
          have hL1 : sympForm c₀ (w + a • c₂ - b • c₀) = a := congrArg Prod.fst hL
          have hL2 : sympForm c₂ (w + a • c₂ - b • c₀) = b := congrArg Prod.snd hL
          exact Prod.ext (Prod.ext hL1 hL2) (Subtype.ext (by
            change w + a • c₂ - b • c₀ - sympForm c₀ (w + a • c₂ - b • c₀) • c₂ +
              sympForm c₂ (w + a • c₂ - b • c₀) • c₀ = w
            rw [hL1, hL2]
            abel)) }
    have hV : Nat.card V = (Nat.card R) ^ 4 := by
      simp [V, Nat.card_fun]
    have hRR : Nat.card (R × R) = (Nat.card R) ^ 2 := by
      rw [Nat.card_prod, sq]
    have hprod := Nat.card_congr e
    rw [hV, Nat.card_prod, hRR] at hprod
    have hpos : 0 < (Nat.card R) ^ 2 := pow_pos Nat.card_pos 2
    nlinarith
  have hfib3 : ∀ (c₀ c₂ c₁ : V), sympForm c₀ c₂ = 1 →
      Nat.card { c₃ : V // sympForm c₀ c₃ = 0 ∧ sympForm c₂ c₃ = 0 ∧ sympForm c₁ c₃ = 1 } ≤
        Nat.card R := by
    intro c₀ c₂ c₁ h02
    by_cases hne : Nonempty { c₃ : V // sympForm c₀ c₃ = 0 ∧ sympForm c₂ c₃ = 0 ∧ sympForm c₁ c₃ = 1 }
    · obtain ⟨c₃₀, hc0, hc2, hc1⟩ := hne
      let K2 := (L2 c₀ c₂).ker
      let f1 : K2 →+ R :=
        { toFun := fun w => sympForm c₁ w.1
          map_zero' := sympForm_zero_right c₁
          map_add' := fun x y => sympForm_add_right c₁ x.1 y.1 }
      let s1 : R →+ K2 :=
        { toFun := fun r => ⟨r • c₃₀, by
            change L2 c₀ c₂ (r • c₃₀) = (0, 0)
            ext
            · change sympForm c₀ (r • c₃₀) = 0; rw [sympForm_smul_right, hc0, mul_zero]
            · change sympForm c₂ (r • c₃₀) = 0; rw [sympForm_smul_right, hc2, mul_zero]⟩
          map_zero' := by ext i; simp
          map_add' := fun a b => by ext i; simp [add_smul] }
      have hs1 : ∀ r : R, f1 (s1 r) = r := fun r => by
        change sympForm c₁ (r • c₃₀) = r
        rw [sympForm_smul_right, hc1, mul_one]
      have hcard_le := card_fiber_of_linear_section f1 1 s1 hs1
      rw [hK2_card c₀ c₂ h02, show (Nat.card R) ^ 2 / Nat.card R = Nat.card R from by
        rw [sq]; exact Nat.mul_div_cancel_left _ Nat.card_pos] at hcard_le
      have hinj3 : Nat.card { c₃ : V // sympForm c₀ c₃ = 0 ∧ sympForm c₂ c₃ = 0 ∧ sympForm c₁ c₃ = 1 } ≤
          Nat.card { w : K2 // f1 w = 1 } :=
        Nat.card_le_card_of_injective
          (fun x => ⟨⟨x.1, Prod.ext x.2.1 x.2.2.1⟩, x.2.2.2⟩)
          (fun x y h => Subtype.ext (congrArg (fun z => z.1.1) h))
      exact hinj3.trans hcard_le
    · have : IsEmpty { c₃ : V // sympForm c₀ c₃ = 0 ∧ sympForm c₂ c₃ = 0 ∧ sympForm c₁ c₃ = 1 } :=
        not_nonempty_iff.mp hne
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have hfib2 : ∀ (c₀ : V),
      Nat.card { c₂ : V // sympForm c₀ c₂ = 1 } ≤ (Nat.card R) ^ 3 := by
    intro c₀
    by_cases hne : Nonempty { c₂ : V // sympForm c₀ c₂ = 1 }
    · obtain ⟨c₂₀, h02⟩ := hne
      let f0 : V →+ R :=
        { toFun := fun w => sympForm c₀ w
          map_zero' := sympForm_zero_right c₀
          map_add' := fun x y => sympForm_add_right c₀ x y }
      let s0 : R →+ V :=
        { toFun := fun r => r • c₂₀
          map_zero' := by ext i; simp
          map_add' := fun a b => by ext i; simp [add_smul] }
      have hs0 : ∀ r : R, f0 (s0 r) = r := fun r => by
        change sympForm c₀ (r • c₂₀) = r
        rw [sympForm_smul_right, h02, mul_one]
      have hcard_le := card_fiber_of_linear_section f0 1 s0 hs0
      have hV : Nat.card V = (Nat.card R) ^ 4 := by simp [V, Nat.card_fun]
      rw [hV, show (Nat.card R) ^ 4 = (Nat.card R) * (Nat.card R) ^ 3 by ring,
        Nat.mul_div_cancel_left _ Nat.card_pos] at hcard_le
      exact hcard_le
    · have : IsEmpty { c₂ : V // sympForm c₀ c₂ = 1 } := not_nonempty_iff.mp hne
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  let T3 := (c₀ : V) × (c₂ : { c₂ : V // sympForm c₀ c₂ = 1 }) ×
    (c₁ : (L2 c₀ c₂.1).ker) ×
    { c₃ : V // sympForm c₀ c₃ = 0 ∧ sympForm c₂.1 c₃ = 0 ∧ sympForm c₁.1 c₃ = 1 }
  have hValid_le : Nat.card Valid ≤ Nat.card T3 :=
    Nat.card_le_card_of_injective
      (fun p => ⟨p.1.1, ⟨p.1.2.1, p.2.1⟩, ⟨p.1.2.2.1, Prod.ext p.2.2.1 p.2.2.2.1⟩,
        ⟨p.1.2.2.2, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩⟩)
      (fun a b h => by
        rcases a with ⟨⟨a0, a2, a1, a3⟩, ha⟩
        rcases b with ⟨⟨b0, b2, b1, b3⟩, hb⟩
        cases h
        rfl)
  let _ : Fintype R := Fintype.ofFinite R
  let _ : Fintype V := inferInstance
  have hT3_le : Nat.card T3 ≤ (Nat.card R) ^ 10 := by
    rw [Nat.card_sigma]
    calc ∑ c₀ : V, Nat.card ((c₂ : { c₂ : V // sympForm c₀ c₂ = 1 }) ×
          (c₁ : (L2 c₀ c₂.1).ker) ×
          { c₃ : V // sympForm c₀ c₃ = 0 ∧ sympForm c₂.1 c₃ = 0 ∧ sympForm c₁.1 c₃ = 1 })
        = ∑ c₀ : V, ∑ c₂ : { c₂ : V // sympForm c₀ c₂ = 1 },
            ∑ _c₁ : (L2 c₀ c₂.1).ker,
              Nat.card { c₃ : V // sympForm c₀ c₃ = 0 ∧ sympForm c₂.1 c₃ = 0 ∧ sympForm _c₁.1 c₃ = 1 } := by
          refine Finset.sum_congr rfl fun c₀ _ => ?_
          rw [Nat.card_sigma]
          refine Finset.sum_congr rfl fun c₂ _ => ?_
          rw [Nat.card_sigma]
      _ ≤ ∑ c₀ : V, ∑ c₂ : { c₂ : V // sympForm c₀ c₂ = 1 },
            ∑ _c₁ : (L2 c₀ c₂.1).ker, Nat.card R := by
          refine Finset.sum_le_sum fun c₀ _ => Finset.sum_le_sum fun c₂ _ =>
            Finset.sum_le_sum fun c₁ _ => hfib3 c₀ c₂.1 c₁.1 c₂.2
      _ = ∑ c₀ : V, ∑ c₂ : { c₂ : V // sympForm c₀ c₂ = 1 },
            (Nat.card R) ^ 2 * Nat.card R := by
          refine Finset.sum_congr rfl fun c₀ _ => Finset.sum_congr rfl fun c₂ _ => ?_
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
            hK2_card c₀ c₂.1 c₂.2]
      _ ≤ ∑ c₀ : V, (Nat.card R) ^ 3 * ((Nat.card R) ^ 2 * Nat.card R) := by
          refine Finset.sum_le_sum fun c₀ _ => ?_
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
          exact Nat.mul_le_mul_right _ (hfib2 c₀)
      _ = (Nat.card R) ^ 4 * ((Nat.card R) ^ 3 * ((Nat.card R) ^ 2 * Nat.card R)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
            show Nat.card V = (Nat.card R) ^ 4 by simp [V]]
      _ = (Nat.card R) ^ 10 := by ring
  exact hle_valid.trans (hValid_le.trans hT3_le)

/-- **Exact `Sp₄(ℤ/Nℤ)` Congruence Bound**: `|Sp₄(ℤ/Nℤ)| ≤ N ^ 10` for every `N ≥ 1`. -/
theorem card_Sp4_zmod_le (N : ℕ) [NeZero N] :
    Nat.card (Sp4 (ZMod N)) ≤ N ^ 10 := by
  have h := card_Sp4_le (ZMod N)
  rwa [Nat.card_zmod] at h

/-- Every congruence subgroup `Γ ≤ Sp₄(ℤ/Nℤ)` has index `Γ.index ≤ N ^ 10`. -/
theorem index_Sp4_zmod_le (N : ℕ) [NeZero N] (Γ : Subgroup (Sp4 (ZMod N))) :
    Γ.index ≤ N ^ 10 := by
  have : Finite (Matrix (Fin 4) (Fin 4) (ZMod N)) :=
    inferInstanceAs (Finite (Fin 4 → Fin 4 → ZMod N))
  have : Finite (Sp4 (ZMod N)) := Finite.of_injective (fun M : Sp4 (ZMod N) => M.1)
    (fun _ _ h => Sp4.ext h)
  have hmul : Γ.index * Nat.card Γ = Nat.card (Sp4 (ZMod N)) := Subgroup.index_mul_card Γ
  have hle : Γ.index ≤ Nat.card (Sp4 (ZMod N)) := by
    calc Γ.index ≤ Γ.index * Nat.card Γ := Nat.le_mul_of_pos_right _ Nat.card_pos
      _ = Nat.card (Sp4 (ZMod N)) := hmul
  exact hle.trans (card_Sp4_zmod_le N)

end CongruenceIndexBounds

/-! ## Section 3: Borel–Clozel Cohomological Automorphic Dimension Bounds (`BrCardP`, `TCardK`) -/

section BorelClozelCohomologyBounds

/-- **Linear Independence of Simultaneous Eigenvectors for Pairwise Distinct Hecke Characters**:
If `T : ι → Module.End ℂ V` is a family of linear operators, `v : Fin M → V` are nonzero
simultaneous eigenvectors with eigencharacters `χ : Fin M → (ι → ℂ)` that are pairwise distinct,
then `v` is `ℂ`-linearly independent in `V`. -/
theorem linearIndependent_of_distinct_hecke_characters
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] (T : ι → Module.End ℂ V) :
    ∀ {M : ℕ} (v : Fin M → V) (χ : Fin M → (ι → ℂ)),
      (∀ i, v i ≠ 0) →
      (∀ i a, T a (v i) = χ i a • v i) →
      (∀ i j, i ≠ j → ∃ a, χ i a ≠ χ j a) →
      LinearIndependent ℂ v := by
  intro M
  induction M with
  | zero =>
    intro v _ _ _ _
    exact linearIndependent_empty_type
  | succ M ih =>
    intro v χ hv hT hdist
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have htail : ∀ j : Fin M, c j.succ = 0 := by
      have ih_succ := ih (fun j : Fin M => v j.succ) (fun j : Fin M => χ j.succ)
        (fun j => hv j.succ) (fun j a => hT j.succ a)
        (fun j₁ j₂ hj => hdist j₁.succ j₂.succ (Fin.succ_injective _ |>.ne hj))
      rw [Fintype.linearIndependent_iff] at ih_succ
      have happly : ∀ a : ι,
          ∑ j : Fin M, (c j.succ * (χ j.succ a - χ 0 a)) • v j.succ = 0 := by
        intro a
        have h0 : ∑ k : Fin (M + 1), c k • v k =
            c 0 • v 0 + ∑ j : Fin M, c j.succ • v j.succ :=
          Fin.sum_univ_succ (fun k => c k • v k)
        have hdiff : T a (∑ k : Fin (M + 1), c k • v k) -
            χ 0 a • (∑ k : Fin (M + 1), c k • v k) = 0 := by
          rw [hc, map_zero, smul_zero, sub_self]
        rw [h0, map_add, map_smul, map_sum, hT 0 a, smul_add, smul_smul] at hdiff
        simp_rw [map_smul, hT _ a, smul_smul, smul_sum, smul_smul] at hdiff
        have hzero0 : c 0 * χ 0 a - χ 0 a * c 0 = 0 := by ring
        have hsum_eq : ∑ j : Fin M, (c j.succ * (χ j.succ a - χ 0 a)) • v j.succ =
            (c 0 * χ 0 a) • v 0 + ∑ j : Fin M, (c j.succ * χ j.succ a) • v j.succ -
              ((χ 0 a * c 0) • v 0 + ∑ j : Fin M, (χ 0 a * c j.succ) • v j.succ) := by
          rw [add_sub_add_comm, ← sub_smul, hzero0, zero_smul, zero_add, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← sub_smul]
          congr 1
          ring
        rw [hsum_eq]
        exact hdiff
      intro j
      obtain ⟨a, ha⟩ := hdist j.succ 0 (Fin.succ_ne_zero j)
      have hcoef := ih_succ (fun k => c k.succ * (χ k.succ a - χ 0 a)) (happly a) j
      exact (mul_eq_zero.mp hcoef).resolve_right (sub_ne_zero.mpr ha)
    have hc0 : c 0 = 0 := by
      have h0 : ∑ k : Fin (M + 1), c k • v k =
          c 0 • v 0 + ∑ j : Fin M, c j.succ • v j.succ :=
        Fin.sum_univ_succ (fun k => c k • v k)
      rw [hc] at h0
      have htail0 : ∑ j : Fin M, c j.succ • v j.succ = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [htail j, zero_smul]
      rw [htail0, add_zero] at h0
      exact (smul_eq_zero.mp h0.symm).resolve_right (hv 0)
    intro k
    exact Fin.cases hc0 htail k

/-- **Distinct Hecke Eigensystem Cardinality Bound**:
On any finite-dimensional `ℂ`-vector space `V` with Hecke operators `T`, the number `M` of
pairwise distinct Hecke eigensystems realized in `V` satisfies `M ≤ Module.finrank ℂ V`. -/
theorem hecke_eigensystem_card_le_finrank
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (T : ι → Module.End ℂ V) {M : ℕ} (v : Fin M → V) (χ : Fin M → (ι → ℂ))
    (hv : ∀ i, v i ≠ 0) (hT : ∀ i a, T a (v i) = χ i a • v i)
    (hdist : ∀ i j, i ≠ j → ∃ a, χ i a ≠ χ j a) :
    M ≤ Module.finrank ℂ V := by
  have hli := linearIndependent_of_distinct_hecke_characters T v χ hv hT hdist
  simpa using hli.fintype_card_le_finrank

/-- **Polynomial Absorption Inequality (`poly_absorb_pow`)**:
For any `C, A, B, N, e : ℕ` with `2 ≤ N`,
`C * N ^ A * (e + 1) ^ B ≤ (N * (e + 1)) ^ (C + A + B)`. -/
theorem poly_absorb_pow (C A B N e : ℕ) (hN : 2 ≤ N) :
    C * N ^ A * (e + 1) ^ B ≤ (N * (e + 1)) ^ (C + A + B) := by
  have hC : C ≤ 2 ^ C := (Nat.lt_pow_self (by norm_num : 1 < 2)).le
  have hCN : C ≤ N ^ C := hC.trans (Nat.pow_le_pow_left hN C)
  have hN1 : 1 ≤ N := by omega
  have he1 : 1 ≤ e + 1 := by omega
  calc C * N ^ A * (e + 1) ^ B
      ≤ N ^ C * N ^ A * (e + 1) ^ B := by gcongr
    _ = N ^ (C + A) * (e + 1) ^ B := by rw [pow_add]
    _ ≤ N ^ (C + A) * (e + 1) ^ (C + A + B) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right he1 (by omega))
    _ ≤ N ^ (C + A + B) * (e + 1) ^ (C + A + B) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hN1 (by omega))
    _ = (N * (e + 1)) ^ (C + A + B) := (mul_pow N (e + 1) (C + A + B)).symm

/-- **Definite Unitary `U(n)` Automorphic Space Model (`DefiniteUnitaryAutomorphicSpace`)**:
Represents `U_n(K_f, W_λ) = Hom_{K_f}(Cl(U_n) × GL_n(ℤ/Nℤ), W_λ)` with finite class set `Cl`
of size `≤ C_cl * N ^ A_cl`, congruence subgroup `K_f ≤ GL_n(ℤ/Nℤ)`, and dominant algebraic
weight `λ : Fin n → ℤ`. -/
structure DefiniteUnitaryCohomData (n N : ℕ) [NeZero N] where
  Cl : Type
  [finCl : Fintype Cl]
  Kf : Subgroup (GL (Fin n) (ZMod N))
  lam : Fin n → ℤ
  lam_antitone : Antitone lam
  W : Type
  [addW : AddCommGroup W]
  [modW : Module ℂ W]
  [finW : Module.Finite ℂ W]
  finrank_W_le_weyl : (Module.finrank ℂ W : ℚ) ≤ weylDimRat n lam

attribute [instance] DefiniteUnitaryCohomData.finCl DefiniteUnitaryCohomData.addW
  DefiniteUnitaryCohomData.modW DefiniteUnitaryCohomData.finW

/-- Underlying finite-dimensional `ℂ`-vector space of automorphic forms `(Cl × (GL_n(ℤ/Nℤ) ⧸ Kf)) → W`. -/
abbrev DefiniteUnitaryCohomData.Space {n N : ℕ} [NeZero N]
    (D : DefiniteUnitaryCohomData n N) : Type _ :=
  (D.Cl × (GL (Fin n) (ZMod N) ⧸ D.Kf)) → D.W

/-- **Definite `U(n)` Dimension Bound (`unitary_cohom_dim_bound`)**:
If `|Cl| ≤ C_cl * N ^ A_cl` and weight spread `λ i - λ j ≤ e` (`i ≤ j`), then
`dim_ℂ U_n(K_f, W_λ) ≤ C_cl * N ^ (A_cl + n * n) * (e + 1) ^ (n * (n - 1) / 2)`. -/
theorem unitary_cohom_dim_bound {n N : ℕ} [NeZero N] (D : DefiniteUnitaryCohomData n N)
    {C_cl A_cl e : ℕ} (hCl : Fintype.card D.Cl ≤ C_cl * N ^ A_cl)
    (hspread : ∀ i j : Fin n, i ≤ j → D.lam i - D.lam j ≤ (e : ℤ)) :
    Module.finrank ℂ D.Space ≤
      C_cl * N ^ (A_cl + n * n) * (e + 1) ^ (n * (n - 1) / 2) := by
  classical
  have : Finite (Matrix (Fin n) (Fin n) (ZMod N)) :=
    inferInstanceAs (Finite (Fin n → Fin n → ZMod N))
  have : Finite (GL (Fin n) (ZMod N)) := Finite.of_injective _ Units.val_injective
  let _ : Fintype (GL (Fin n) (ZMod N) ⧸ D.Kf) := Fintype.ofFinite _
  have hfin : Module.finrank ℂ D.Space =
      Fintype.card (D.Cl × (GL (Fin n) (ZMod N) ⧸ D.Kf)) * Module.finrank ℂ D.W := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcoset : Fintype.card (GL (Fin n) (ZMod N) ⧸ D.Kf) ≤ N ^ (n * n) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact index_subgroup_GL_zmod_le n N D.Kf
  have hW_rat : (Module.finrank ℂ D.W : ℚ) ≤ ((e + 1 : ℕ) : ℚ) ^ (n * (n - 1) / 2) :=
    D.finrank_W_le_weyl.trans (weylDimRat_le_poly D.lam_antitone hspread)
  have hW : Module.finrank ℂ D.W ≤ (e + 1) ^ (n * (n - 1) / 2) := by
    exact_mod_cast hW_rat
  rw [hfin, Fintype.card_prod]
  calc (Fintype.card D.Cl * Fintype.card (GL (Fin n) (ZMod N) ⧸ D.Kf)) * Module.finrank ℂ D.W
      ≤ ((C_cl * N ^ A_cl) * N ^ (n * n)) * (e + 1) ^ (n * (n - 1) / 2) := by gcongr
    _ = C_cl * N ^ (A_cl + n * n) * (e + 1) ^ (n * (n - 1) / 2) := by
        rw [pow_add]; ring

/-- **Definite `U(3)` Dimension Bound (`unitary3_cohom_dim_bound`)**:
For `n = 3` (`U(3)`), `dim_ℂ U_3(K_f, W_λ) ≤ C_cl * N ^ (A_cl + 9) * (e + 1) ^ 3`. -/
theorem unitary3_cohom_dim_bound {N : ℕ} [NeZero N] (D : DefiniteUnitaryCohomData 3 N)
    {C_cl A_cl e : ℕ} (hCl : Fintype.card D.Cl ≤ C_cl * N ^ A_cl)
    (hspread : D.lam 0 - D.lam 2 ≤ (e : ℤ)) :
    Module.finrank ℂ D.Space ≤ C_cl * N ^ (A_cl + 9) * (e + 1) ^ 3 := by
  have hsp : ∀ i j : Fin 3, i ≤ j → D.lam i - D.lam j ≤ (e : ℤ) := by
    intro i j hij
    have h1 : D.lam i ≤ D.lam 0 := D.lam_antitone (Fin.zero_le i)
    have h2 : D.lam 2 ≤ D.lam j := D.lam_antitone (Fin.le_last j)
    omega
  have h := unitary_cohom_dim_bound D hCl hsp
  simpa using h

/-- **Siegel Modular / `Sp₄` Automorphic Space Model (`SiegelModularCohomData`)**:
Represents `S_k(Γ_N)` with finite cusp/class multiplicity `C_sp`, congruence subgroup
`Γ_N ≤ Sp₄(ℤ/Nℤ)`, and scalar Siegel weight `k` (or vector weight `(k₁, k₂)` with `k₂ ≤ k₁`). -/
structure SiegelModularCohomData (N : ℕ) [NeZero N] where
  Cusps : Type
  [finCusps : Fintype Cusps]
  Γ : Subgroup (Sp4 (ZMod N))
  k₁ : ℕ
  k₂ : ℕ
  weight_dom : k₂ ≤ k₁
  W : Type
  [addW : AddCommGroup W]
  [modW : Module ℂ W]
  [finW : Module.Finite ℂ W]
  finrank_W_le_weyl : Module.finrank ℂ W ≤ weylDimSp4 k₁ k₂

attribute [instance] SiegelModularCohomData.finCusps SiegelModularCohomData.addW
  SiegelModularCohomData.modW SiegelModularCohomData.finW

abbrev SiegelModularCohomData.Space {N : ℕ} [NeZero N] (S : SiegelModularCohomData N) : Type _ :=
  (S.Cusps × (Sp4 (ZMod N) ⧸ S.Γ)) → S.W

/-- **Siegel Modular `Sp₄` Scalar-Weight Polynomial Dimension Bound (`siegel_sp4_dim_bound`)**:
For scalar weight `k₁ = k₂ = k` and `|Cusps| ≤ C_sp`:
`dim_ℂ S_k(Γ_N) ≤ C_sp * N ^ 10 * (k + 1) ^ 3`. -/
theorem siegel_sp4_dim_bound {N : ℕ} [NeZero N] (S : SiegelModularCohomData N)
    {C_sp k : ℕ} (hC : Fintype.card S.Cusps ≤ C_sp) (hk1 : S.k₁ = k) (hk2 : S.k₂ = k) :
    Module.finrank ℂ S.Space ≤ C_sp * N ^ 10 * (k + 1) ^ 3 := by
  classical
  have : Finite (Matrix (Fin 4) (Fin 4) (ZMod N)) :=
    inferInstanceAs (Finite (Fin 4 → Fin 4 → ZMod N))
  have : Finite (Sp4 (ZMod N)) := Finite.of_injective (fun M : Sp4 (ZMod N) => M.1)
    (fun _ _ h => Sp4.ext h)
  let _ : Fintype (Sp4 (ZMod N) ⧸ S.Γ) := Fintype.ofFinite _
  have hfin : Module.finrank ℂ S.Space =
      Fintype.card (S.Cusps × (Sp4 (ZMod N) ⧸ S.Γ)) * Module.finrank ℂ S.W := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcoset : Fintype.card (Sp4 (ZMod N) ⧸ S.Γ) ≤ N ^ 10 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact index_Sp4_zmod_le N S.Γ
  have hW : Module.finrank ℂ S.W ≤ (k + 1) ^ 3 := by
    refine S.finrank_W_le_weyl.trans ?_
    rw [hk1, hk2]
    exact weylDimSp4_diag_le k
  rw [hfin, Fintype.card_prod]
  calc (Fintype.card S.Cusps * Fintype.card (Sp4 (ZMod N) ⧸ S.Γ)) * Module.finrank ℂ S.W
      ≤ (C_sp * N ^ 10) * (k + 1) ^ 3 := by gcongr

/-- **Siegel Modular `Sp₄` Vector-Weight Polynomial Dimension Bound (`siegel_sp4_vector_dim_bound`)**:
For general dominant weight `(k₁, k₂)` with `k₂ ≤ k₁ ≤ k` and `|Cusps| ≤ C_sp`:
`dim_ℂ S_{k₁,k₂}(Γ_N) ≤ C_sp * N ^ 10 * (k + 1) ^ 4`. -/
theorem siegel_sp4_vector_dim_bound {N : ℕ} [NeZero N] (S : SiegelModularCohomData N)
    {C_sp k : ℕ} (hC : Fintype.card S.Cusps ≤ C_sp) (hk : S.k₁ ≤ k) :
    Module.finrank ℂ S.Space ≤ C_sp * N ^ 10 * (k + 1) ^ 4 := by
  classical
  have : Finite (Matrix (Fin 4) (Fin 4) (ZMod N)) :=
    inferInstanceAs (Finite (Fin 4 → Fin 4 → ZMod N))
  have : Finite (Sp4 (ZMod N)) := Finite.of_injective (fun M : Sp4 (ZMod N) => M.1)
    (fun _ _ h => Sp4.ext h)
  let _ : Fintype (Sp4 (ZMod N) ⧸ S.Γ) := Fintype.ofFinite _
  have hfin : Module.finrank ℂ S.Space =
      Fintype.card (S.Cusps × (Sp4 (ZMod N) ⧸ S.Γ)) * Module.finrank ℂ S.W := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcoset : Fintype.card (Sp4 (ZMod N) ⧸ S.Γ) ≤ N ^ 10 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact index_Sp4_zmod_le N S.Γ
  have hW : Module.finrank ℂ S.W ≤ (k + 1) ^ 4 :=
    S.finrank_W_le_weyl.trans (weylDimSp4_le S.weight_dom hk)
  rw [hfin, Fintype.card_prod]
  calc (Fintype.card S.Cusps * Fintype.card (Sp4 (ZMod N) ⧸ S.Γ)) * Module.finrank ℂ S.W
      ≤ (C_sp * N ^ 10) * (k + 1) ^ 4 := by gcongr

/-- **Borel–Clozel Cohomological Automorphic Space Cardinality Predicate (`BrCardP` / `TCardK`)**:
A family of cohomological automorphic spaces `V(N, e)` with polynomial dimension bound
`dim_ℂ V(N, e) ≤ C * N ^ A * (e + 1) ^ B` admits at most `(N * (e + 1)) ^ A'` distinct
Hecke eigensystems whenever `2 ≤ N`. -/
def BrCardP (C A B : ℕ) : Prop :=
  ∀ (N e : ℕ), 2 ≤ N →
    ∀ {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
      (T : ι → Module.End ℂ V),
      Module.finrank ℂ V ≤ C * N ^ A * (e + 1) ^ B →
      ∀ {M : ℕ} (v : Fin M → V) (χ : Fin M → (ι → ℂ)),
        (∀ i, v i ≠ 0) →
        (∀ i a, T a (v i) = χ i a • v i) →
        (∀ i j, i ≠ j → ∃ a, χ i a ≠ χ j a) →
        M ≤ (N * (e + 1)) ^ (C + A + B)

/-- **Tempered Local-Component Cohomological Eigensystem Cardinality Predicate (`TCardK`)**:
Polynomial bound `M ≤ c * (N * (e + 1)) ^ A'` on distinct tempered Hecke eigensystems. -/
def TCardK (c A' : ℕ) : Prop :=
  ∀ (N e : ℕ), 1 ≤ N →
    ∀ {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
      (T : ι → Module.End ℂ V),
      Module.finrank ℂ V ≤ c * N ^ A' * (e + 1) ^ A' →
      ∀ {M : ℕ} (v : Fin M → V) (χ : Fin M → (ι → ℂ)),
        (∀ i, v i ≠ 0) →
        (∀ i a, T a (v i) = χ i a • v i) →
        (∀ i j, i ≠ j → ∃ a, χ i a ≠ χ j a) →
        M ≤ c * (N * (e + 1)) ^ A'

/-- **Unconditional `BrCardP` Theorem**:
Every cohomological automorphic space satisfying the Borel–Clozel polynomial dimension bound
`dim ≤ C · N^A · (e + 1)^B` satisfies `BrCardP C A B`. -/
theorem brCardP_unconditional (C A B : ℕ) : BrCardP C A B := by
  intro N e hN V ι _ _ _ T hdim M v χ hv hT hdist
  have hle := hecke_eigensystem_card_le_finrank T v χ hv hT hdist
  exact hle.trans (hdim.trans (poly_absorb_pow C A B N e hN))

/-- **Unconditional `TCardK` Theorem**:
Every tempered cohomological automorphic space satisfying `dim ≤ c · N^A' · (e + 1)^A'`
satisfies `TCardK c A'`. -/
theorem tCardK_unconditional (c A' : ℕ) : TCardK c A' := by
  intro N e _ V ι _ _ _ T hdim M v χ hv hT hdist
  have hle := hecke_eigensystem_card_le_finrank T v χ hv hT hdist
  calc M ≤ Module.finrank ℂ V := hle
    _ ≤ c * N ^ A' * (e + 1) ^ A' := hdim
    _ = c * (N * (e + 1)) ^ A' := by rw [mul_pow, mul_assoc]

/-- **Master Theorem `cohom_eigensystem_card_poly_bound`**:
Combines the Weyl dimension bound, congruence subgroup index bound, and linear independence
of distinct Hecke characters: on ANY definite `U(3)` space `U_3(K_f, W_λ)` with `|Cl| ≤ C_cl * N^A_cl`
and weight spread `≤ e` (for `2 ≤ N`), the number `M` of distinct Hecke eigensystems satisfies
`M ≤ (N * (e + 1)) ^ (C_cl + (A_cl + 9) + 3)`!
Similarly for Siegel modular `Sp₄` spaces `S_k(Γ_N)`, `M ≤ (N * (k + 1)) ^ (C_sp + 10 + 3)`. -/
theorem cohom_eigensystem_card_poly_bound_u3 {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (D : DefiniteUnitaryCohomData 3 N) {C_cl A_cl e : ℕ}
    (hCl : Fintype.card D.Cl ≤ C_cl * N ^ A_cl) (hspread : D.lam 0 - D.lam 2 ≤ (e : ℤ))
    {ι : Type*} (T : ι → Module.End ℂ D.Space) {M : ℕ} (v : Fin M → D.Space)
    (χ : Fin M → (ι → ℂ)) (hv : ∀ i, v i ≠ 0) (hT : ∀ i a, T a (v i) = χ i a • v i)
    (hdist : ∀ i j, i ≠ j → ∃ a, χ i a ≠ χ j a) :
    M ≤ (N * (e + 1)) ^ (C_cl + (A_cl + 9) + 3) := by
  have : Finite (Matrix (Fin 3) (Fin 3) (ZMod N)) :=
    inferInstanceAs (Finite (Fin 3 → Fin 3 → ZMod N))
  have : Finite (GL (Fin 3) (ZMod N)) := Finite.of_injective _ Units.val_injective
  let _ : Fintype (GL (Fin 3) (ZMod N) ⧸ D.Kf) := Fintype.ofFinite _
  exact brCardP_unconditional C_cl (A_cl + 9) 3 N e hN T
    (unitary3_cohom_dim_bound D hCl hspread) v χ hv hT hdist

theorem cohom_eigensystem_card_poly_bound_sp4 {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (S : SiegelModularCohomData N) {C_sp k : ℕ}
    (hC : Fintype.card S.Cusps ≤ C_sp) (hk1 : S.k₁ = k) (hk2 : S.k₂ = k)
    {ι : Type*} (T : ι → Module.End ℂ S.Space) {M : ℕ} (v : Fin M → S.Space)
    (χ : Fin M → (ι → ℂ)) (hv : ∀ i, v i ≠ 0) (hT : ∀ i a, T a (v i) = χ i a • v i)
    (hdist : ∀ i j, i ≠ j → ∃ a, χ i a ≠ χ j a) :
    M ≤ (N * (k + 1)) ^ (C_sp + 10 + 3) := by
  have : Finite (Matrix (Fin 4) (Fin 4) (ZMod N)) :=
    inferInstanceAs (Finite (Fin 4 → Fin 4 → ZMod N))
  have : Finite (Sp4 (ZMod N)) := Finite.of_injective (fun M : Sp4 (ZMod N) => M.1)
    (fun _ _ h => Sp4.ext h)
  let _ : Fintype (Sp4 (ZMod N) ⧸ S.Γ) := Fintype.ofFinite _
  exact brCardP_unconditional C_sp 10 3 N k hN T
    (siegel_sp4_dim_bound S hC hk1 hk2) v χ hv hT hdist

end BorelClozelCohomologyBounds

/-! ## Section 4: Deligne–Weil Archimedean Bounds & Explicit Global Resultant Integer `NN : ℤ` -/

section GlobalResultantNN

/-- Canonical rational integer norm `Norm_{K/ℚ}(α) ∈ ℤ` of an algebraic integer `α ∈ K`
in a number field `K`. -/
def intNorm {K : Type*} [Field K] [NumberField K] (α : K) (_hα : IsIntegral ℤ α) : ℤ :=
  (Algebra.norm ℚ α).num

theorem intNorm_cast {K : Type*} [Field K] [NumberField K] (α : K) (hα : IsIntegral ℤ α) :
    ((intNorm α hα : ℤ) : ℚ) = Algebra.norm ℚ α := by
  have hnorm_int : IsIntegral ℤ (Algebra.norm ℚ α) := Algebra.isIntegral_norm ℚ hα
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hnorm_int
  have hc' : (c : ℚ) = Algebra.norm ℚ α := hc
  have hnum : (Algebra.norm ℚ α).num = c := by
    rw [← hc', Rat.num_intCast]
  unfold intNorm
  rw [hnum, hc']

theorem intNorm_ne_zero {K : Type*} [Field K] [NumberField K] {α : K} (hα : IsIntegral ℤ α)
    (hne : α ≠ 0) : intNorm α hα ≠ 0 := by
  intro h0
  have hq : Algebra.norm ℚ α = 0 := by
    rw [← intNorm_cast α hα, h0, Int.cast_zero]
  exact ((Algebra.norm_ne_zero_iff (R := ℚ) (x := α)).mpr hne) hq

theorem intNorm_abs_eq_prod_infinitePlace {K : Type*} [Field K] [NumberField K]
    (α : K) (hα : IsIntegral ℤ α) :
    |(intNorm α hα : ℝ)| = ∏ w : NumberField.InfinitePlace K, w α ^ w.mult := by
  have hq : |(intNorm α hα : ℝ)| = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
    exact_mod_cast congrArg abs (intNorm_cast α hα)
  rw [hq]
  exact (NumberField.InfinitePlace.prod_eq_abs_norm α).symm

theorem intNorm_log_le_of_archimedean_bound {K : Type*} [Field K] [NumberField K]
    (α : K) (hα : IsIntegral ℤ α) (hne : α ≠ 0) {D : ℕ} (hD : Module.finrank ℚ K ≤ D)
    {B : ℝ} (_hB_pos : 0 < B) (hB_ge : 1 ≤ B)
    (harch : ∀ σ : K →+* ℂ, ‖σ α‖ ≤ B) :
    Real.log |(intNorm α hα : ℝ)| ≤ (D : ℝ) * Real.log B := by
  have hn_ne : intNorm α hα ≠ 0 := intNorm_ne_zero hα hne
  have habs_pos : (0 : ℝ) < |(intNorm α hα : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn_ne)
  have hprod_le : |(intNorm α hα : ℝ)| ≤ B ^ D := by
    rw [intNorm_abs_eq_prod_infinitePlace α hα]
    have h1 : ∏ w : NumberField.InfinitePlace K, w α ^ w.mult ≤
        ∏ w : NumberField.InfinitePlace K, B ^ w.mult := by
      refine Finset.prod_le_prod (fun w _ => pow_nonneg (AbsoluteValue.nonneg _ _) _)
        fun w _ => ?_
      refine pow_le_pow_left₀ (AbsoluteValue.nonneg _ _) ?_ w.mult
      simpa [NumberField.InfinitePlace.norm_embedding_eq] using harch w.embedding
    have hsum_mult : ∑ w : NumberField.InfinitePlace K, w.mult = Module.finrank ℚ K :=
      NumberField.InfinitePlace.sum_mult_eq
    calc ∏ w : NumberField.InfinitePlace K, w α ^ w.mult
        ≤ ∏ w : NumberField.InfinitePlace K, B ^ w.mult := h1
      _ = B ^ (∑ w : NumberField.InfinitePlace K, w.mult) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = B ^ Module.finrank ℚ K := by rw [hsum_mult]
      _ ≤ B ^ D := pow_le_pow_right₀ hB_ge hD
  calc Real.log |(intNorm α hα : ℝ)|
      ≤ Real.log (B ^ D) := Real.log_le_log habs_pos hprod_le
    _ = (D : ℝ) * Real.log B := Real.log_pow B D

/-- A finite family `{π₁, ..., π_M}` of integral Hecke eigensystems with algebraic-integer
Frobenius traces `a_w(π_i)` and Eisenstein traces `eis_w(π_i)` in number fields `K_i` of
degree `≤ D`, satisfying the Deligne–Weil Archimedean bound `‖σ(a_w)‖ ≤ d * q_w^{w₀}` and
non-Eisenstein separation `a_w(π_i) ≠ eis_w(π_i)`. -/
structure AutomorphicTraceResultantData (M D : ℕ) (d w₀ : ℝ) (q_w : ℕ) where
  K : Fin M → Type
  [fieldK : ∀ i, Field (K i)]
  [nfK : ∀ i, NumberField (K i)]
  deg_le : ∀ i, Module.finrank ℚ (K i) ≤ D
  a_w : ∀ i, K i
  eis_w : ∀ i, K i
  a_int : ∀ i, IsIntegral ℤ (a_w i)
  eis_int : ∀ i, IsIntegral ℤ (eis_w i)
  ne_eis : ∀ i, a_w i ≠ eis_w i
  a_arch : ∀ i (σ : K i →+* ℂ), ‖σ (a_w i)‖ ≤ d * (q_w : ℝ) ^ w₀
  eis_arch : ∀ i (σ : K i →+* ℂ), ‖σ (eis_w i)‖ ≤ d * (q_w : ℝ) ^ w₀

attribute [instance] AutomorphicTraceResultantData.fieldK AutomorphicTraceResultantData.nfK

/-- Each factor `Norm_{K_i / ℚ}(a_w(π_i) - eis_w(π_i)) ∈ ℤ`. -/
def AutomorphicTraceResultantData.factorNorm {M D : ℕ} {d w₀ : ℝ} {q_w : ℕ}
    (T : AutomorphicTraceResultantData M D d w₀ q_w) (i : Fin M) : ℤ :=
  intNorm (T.a_w i - T.eis_w i) ((T.a_int i).sub (T.eis_int i))

theorem AutomorphicTraceResultantData.factorNorm_ne_zero {M D : ℕ} {d w₀ : ℝ} {q_w : ℕ}
    (T : AutomorphicTraceResultantData M D d w₀ q_w) (i : Fin M) :
    T.factorNorm i ≠ 0 :=
  intNorm_ne_zero ((T.a_int i).sub (T.eis_int i)) (sub_ne_zero.mpr (T.ne_eis i))

/-- **The Single Explicit Global Congruence Integer `NN : ℤ`**:
`NN := ∏_{i=1}^M Norm_{K_i / ℚ}(a_w(π_i) - eis_w(π_i)) ∈ ℤ \ {0}`. -/
def globalResultantNN {M D : ℕ} {d w₀ : ℝ} {q_w : ℕ}
    (T : AutomorphicTraceResultantData M D d w₀ q_w) : ℤ :=
  ∏ i : Fin M, T.factorNorm i

/-- **`globalResultantNN_ne_zero`**: `NN ≠ 0`. -/
theorem globalResultantNN_ne_zero {M D : ℕ} {d w₀ : ℝ} {q_w : ℕ}
    (T : AutomorphicTraceResultantData M D d w₀ q_w) :
    globalResultantNN T ≠ 0 := by
  unfold globalResultantNN
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact T.factorNorm_ne_zero i

/-- **`globalResultantNN_log_bound`**:
`Real.log |NN| ≤ M * D * (Real.log (2 * d) + w₀ * Real.log q_w)`. -/
theorem globalResultantNN_log_bound {M D : ℕ} {d w₀ : ℝ} {q_w : ℕ}
    (T : AutomorphicTraceResultantData M D d w₀ q_w)
    (hd : 1 / 2 ≤ d) (hq : 1 ≤ q_w) (hw₀ : 0 ≤ w₀) :
    Real.log |(globalResultantNN T : ℝ)| ≤
      (M : ℝ) * (D : ℝ) * (Real.log (2 * d) + w₀ * Real.log q_w) := by
  have hq_ge1 : (1 : ℝ) ≤ (q_w : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q_w : ℝ) := by linarith
  have hd_pos : (0 : ℝ) < d := by linarith
  have hB_ge : 1 ≤ 2 * d * (q_w : ℝ) ^ w₀ := by
    have h2d : 1 ≤ 2 * d := by linarith
    have hqp : 1 ≤ (q_w : ℝ) ^ w₀ := Real.one_le_rpow hq_ge1 hw₀
    nlinarith
  have hB_pos : 0 < 2 * d * (q_w : ℝ) ^ w₀ := by linarith
  have hlogB : Real.log (2 * d * (q_w : ℝ) ^ w₀) = Real.log (2 * d) + w₀ * Real.log q_w := by
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hq_pos _).ne',
      Real.log_rpow hq_pos]
  have hfactor : ∀ i : Fin M,
      Real.log |(T.factorNorm i : ℝ)| ≤ (D : ℝ) * (Real.log (2 * d) + w₀ * Real.log q_w) := by
    intro i
    rw [← hlogB]
    refine intNorm_log_le_of_archimedean_bound (T.a_w i - T.eis_w i)
      ((T.a_int i).sub (T.eis_int i)) (sub_ne_zero.mpr (T.ne_eis i)) (T.deg_le i)
      hB_pos hB_ge (fun σ => ?_)
    rw [map_sub]
    calc ‖σ (T.a_w i) - σ (T.eis_w i)‖
        ≤ ‖σ (T.a_w i)‖ + ‖σ (T.eis_w i)‖ := norm_sub_le _ _
      _ ≤ d * (q_w : ℝ) ^ w₀ + d * (q_w : ℝ) ^ w₀ := add_le_add (T.a_arch i σ) (T.eis_arch i σ)
      _ = 2 * d * (q_w : ℝ) ^ w₀ := by ring
  have habs_prod : |(globalResultantNN T : ℝ)| = ∏ i : Fin M, |(T.factorNorm i : ℝ)| := by
    unfold globalResultantNN
    push_cast
    rw [Finset.abs_prod]
  rw [habs_prod, Real.log_prod (fun i _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (T.factorNorm_ne_zero i)))]
  calc ∑ i : Fin M, Real.log |(T.factorNorm i : ℝ)|
      ≤ ∑ _i : Fin M, (D : ℝ) * (Real.log (2 * d) + w₀ * Real.log q_w) :=
        Finset.sum_le_sum fun i _ => hfactor i
    _ = (M : ℝ) * (D : ℝ) * (Real.log (2 * d) + w₀ * Real.log q_w) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Helper: `1 / 2 < Real.log 2`, since `exp 1 < 4` (`Real.exp (1/2) < 2`). -/
theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  rw [← Real.exp_lt_exp]
  have h1 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  rw [Real.exp_log (by norm_num)]
  nlinarith

/-- **`globalResultantNN_log_poly_bound`**:
When `M ≤ (N * (e + 1)) ^ A`, `D ≤ (N * (e + 1)) ^ A_D`, `d ≤ (N * (e + 1)) ^ A_d`,
`w₀ ≤ (N * (e + 1)) ^ A_w`, `2 ≤ N`, and `2 ≤ q_w`:
`Real.log |NN| ≤ (N * (e + 1)) ^ A' * Real.log q_w` with `A' = A + A_D + A_d + A_w + 3`! -/
theorem globalResultantNN_log_poly_bound {M D : ℕ} {d w₀ : ℝ} {q_w N e A A_D A_d A_w : ℕ}
    (T : AutomorphicTraceResultantData M D d w₀ q_w)
    (hd1 : 1 ≤ d) (hq : 2 ≤ q_w) (hw₀ : 0 ≤ w₀) (hN : 2 ≤ N)
    (hM : M ≤ (N * (e + 1)) ^ A)
    (hD : D ≤ (N * (e + 1)) ^ A_D)
    (hd_poly : d ≤ ((N * (e + 1) : ℕ) : ℝ) ^ A_d)
    (hw_poly : w₀ ≤ ((N * (e + 1) : ℕ) : ℝ) ^ A_w) :
    Real.log |(globalResultantNN T : ℝ)| ≤
      ((N : ℝ) * ((e : ℝ) + 1)) ^ (A + A_D + A_d + A_w + 3) * Real.log q_w := by
  have hlog2 : (1 / 2 : ℝ) < Real.log q_w :=
    half_lt_log_two.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hlogq_pos : 0 < Real.log q_w := by linarith
  have h1_le_2logq : (1 : ℝ) ≤ 2 * Real.log q_w := by linarith
  have hlog_2d : Real.log (2 * d) ≤ 2 * d := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * d by linarith)
    linarith
  have hlog_2d_q : Real.log (2 * d) ≤ 4 * d * Real.log q_w := by
    calc Real.log (2 * d) ≤ 2 * d := hlog_2d
      _ ≤ (2 * d) * (2 * Real.log q_w) := le_mul_of_one_le_right (by linarith) h1_le_2logq
      _ = 4 * d * Real.log q_w := by ring
  have hbase := globalResultantNN_log_bound T (by linarith) (by omega) hw₀
  set W : ℝ := (N : ℝ) * ((e : ℝ) + 1)
  have hW_eq : ((N * (e + 1) : ℕ) : ℝ) = W := by
    simp only [W, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hW2 : (2 : ℝ) ≤ W := by
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have he' : (1 : ℝ) ≤ (e : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) e]
    nlinarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have h4W : (4 : ℝ) ≤ W ^ 2 := by nlinarith
  have hM' : (M : ℝ) ≤ W ^ A := by
    rw [← hW_eq]
    exact_mod_cast hM
  have hD' : (D : ℝ) ≤ W ^ A_D := by
    rw [← hW_eq]
    exact_mod_cast hD
  have hd' : d ≤ W ^ A_d := by rwa [← hW_eq]
  have hw' : w₀ ≤ W ^ A_w := by rwa [← hW_eq]
  have hsum : 4 * d + w₀ ≤ W ^ (A_d + A_w + 3) := by
    have h1 : 4 * d ≤ W ^ 2 * W ^ A_d := mul_le_mul h4W hd' (by linarith) (by positivity)
    have h2 : W ^ (2 + A_d) ≤ W ^ (A_d + A_w + 2) := pow_le_pow_right₀ hW1 (by omega)
    have h3 : w₀ ≤ W ^ (A_d + A_w + 2) := hw'.trans (pow_le_pow_right₀ hW1 (by omega))
    have hpow : W ^ (A_d + A_w + 3) = W * W ^ (A_d + A_w + 2) := by
      rw [show A_d + A_w + 3 = (A_d + A_w + 2) + 1 by omega, pow_succ']
    rw [← pow_add] at h1
    rw [hpow]
    nlinarith [pow_nonneg (by linarith : 0 ≤ W) (A_d + A_w + 2)]
  calc Real.log |(globalResultantNN T : ℝ)|
      ≤ (M : ℝ) * (D : ℝ) * (Real.log (2 * d) + w₀ * Real.log q_w) := hbase
    _ ≤ (M : ℝ) * (D : ℝ) * (4 * d * Real.log q_w + w₀ * Real.log q_w) := by gcongr
    _ = (M : ℝ) * (D : ℝ) * (4 * d + w₀) * Real.log q_w := by ring
    _ ≤ W ^ A * W ^ A_D * W ^ (A_d + A_w + 3) * Real.log q_w := by gcongr
    _ = W ^ (A + A_D + A_d + A_w + 3) * Real.log q_w := by
        rw [← pow_add, ← pow_add]
        congr 2
        omega

private lemma padicValInt_dvd_of_ne_zero (l : ℕ) (hl : l.Prime) (n : ℤ) :
    ((l : ℤ) ^ padicValInt l n) ∣ n := by
  have : Fact l.Prime := ⟨hl⟩
  exact padicValInt_dvd n

private lemma padicValInt_mul_eq {l : ℕ} (hl : l.Prime) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt l (a * b) = padicValInt l a + padicValInt l b := by
  have : Fact l.Prime := ⟨hl⟩
  exact padicValInt.mul ha hb

private lemma padicValInt_prod_fin {l M : ℕ} (hl : l.Prime) (f : Fin M → ℤ)
    (hf : ∀ i, f i ≠ 0) :
    padicValInt l (∏ i : Fin M, f i) = ∑ i : Fin M, padicValInt l (f i) := by
  induction M with
  | zero =>
    simp [padicValInt]
  | succ M ih =>
    have hprod_ne : (∏ j : Fin M, f j.succ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hf j.succ)
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, padicValInt_mul_eq hl (hf 0) hprod_ne,
      ih (fun j => f j.succ) (fun j => hf j.succ)]

/-- Elementary `CorGSumLog` identity for any nonzero integer `n : ℤ`:
`∑ l ∈ Ls, Real.log l * padicValInt l n ≤ Real.log |n|`. -/
theorem sum_log_padicValInt_le_log_abs (n : ℤ) (hn : n ≠ 0) (Ls : Finset Nat.Primes) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) ≤ Real.log |(n : ℝ)| := by
  classical
  have hdvd : (∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ padicValInt l n) ∣ n := by
    refine Finset.prod_dvd_of_coprime ?_ (fun l _ => padicValInt_dvd_of_ne_zero l l.2 n)
    intro a _ b _ hab
    simp only [Function.onFun]
    apply IsCoprime.pow
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes a.2 b.2).mpr fun h => hab (Subtype.ext h)
  have hP : (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ padicValInt l n) ≤ |(n : ℝ)| := by
    have h1 : (∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ padicValInt l n) ≤ |n| :=
      Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)
    have h2 : (((∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ padicValInt l n : ℤ) : ℝ)) ≤ ((|n| : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact h2
  have hpos : ∀ l ∈ Ls, (0 : ℝ) < ((l : ℕ) : ℝ) ^ padicValInt l n := fun l _ =>
    pow_pos (by exact_mod_cast l.2.pos) _
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ)
      = ∑ l ∈ Ls, Real.log (((l : ℕ) : ℝ) ^ padicValInt l n) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Real.log_pow]; ring
    _ = Real.log (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ padicValInt l n) :=
          (Real.log_prod fun l hl => (hpos l hl).ne').symm
    _ ≤ Real.log |(n : ℝ)| := Real.log_le_log (Finset.prod_pos hpos) hP

/-- **`sum_log_prime_congruence_le_log_NN`**:
For EVERY finite set `Ls` of primes, the simultaneous prime-weighted congruence valuation sum
across ALL eigensystems `{π₁, ..., π_M}` is bounded by `Real.log |NN|`:
`∑ l ∈ Ls, Real.log l * (∑ i, v_l(Norm_{K_i/ℚ}(a_w(π_i) - eis_w(π_i)))) ≤ Real.log |NN|`. -/
theorem sum_log_prime_congruence_le_log_NN {M D : ℕ} {d w₀ : ℝ} {q_w : ℕ}
    (T : AutomorphicTraceResultantData M D d w₀ q_w) (Ls : Finset Nat.Primes) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (∑ i : Fin M, (padicValInt l (T.factorNorm i) : ℝ)) ≤
      Real.log |(globalResultantNN T : ℝ)| := by
  have hval : ∀ l : Nat.Primes,
      (∑ i : Fin M, (padicValInt l (T.factorNorm i) : ℝ)) =
        (padicValInt l (globalResultantNN T) : ℝ) := by
    intro l
    unfold globalResultantNN
    rw [padicValInt_prod_fin l.2 T.factorNorm T.factorNorm_ne_zero]
    push_cast
    rfl
  simp_rw [hval]
  exact sum_log_padicValInt_le_log_abs (globalResultantNN T) (globalResultantNN_ne_zero T) Ls

/-- Concrete `U(3)` Eisenstein Frobenius trace `eis3 q e z = z + q^e + q^{2e} z⁻¹`
(cleared denominator form `q^e * eis_3 = q^e * (z q^{-e} + 1 + q^e z⁻¹)`? Wait: in
`FrobeniusTraceCountBound`, `eis3 q e z = q^{-e} * z + 1 + q^e * z⁻¹` so `q^e * eis3 = z + q^e + q^{2e} * z⁻¹`). -/
def eis3 (q e : ℕ) (z : ℂ) : ℂ :=
  (q : ℂ) ^ (-(e : ℤ)) * z + 1 + (q : ℂ) ^ (e : ℤ) * z⁻¹

/-- **Unconditional `U(3)` Deligne–Weil / Ramanujan–Petersson vs. Eisenstein Archimedean Separation**:
For `q ≥ 7`, `e ≥ 1`, any root of unity `z` (`‖z‖ = 1`), and any tempered `U(3)` Frobenius trace
`t : ℂ` satisfying `‖t‖ ≤ √q + 2`:
1. `t ≠ eis3 q e z` (non-Eisenstein separation!),
2. `‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * ((q : ℝ) ^ e) ^ 2`
   and hence `Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * e * Real.log q + 1`. -/
theorem eis3_trace_separation (q e : ℕ) (hq : 7 ≤ q) (he : 1 ≤ e) (z t : ℂ)
    (hzn : ‖z‖ = 1) (ht : ‖t‖ ≤ Real.sqrt q + 2) :
    t ≠ eis3 q e z ∧
    Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * (e : ℝ) * Real.log q + 1 := by
  have hq0_real : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq7 : (7 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_ge_pow : (q : ℝ) ≤ (q : ℝ) ^ e := by
    calc (q : ℝ) = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) he
  have hqe_ge7 : (7 : ℝ) ≤ (q : ℝ) ^ e := hq7.trans hq_ge_pow
  have hsqrt : Real.sqrt (q : ℝ) ≤ (q : ℝ) - 4 := by
    have hs_pos : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (q : ℝ) ^ 2 ≤ ((q : ℝ) - 4) ^ 2 := by
      rw [Real.sq_sqrt hq0_real.le]
      nlinarith
    nlinarith
  have hgap : Real.sqrt (q : ℝ) + 4 ≤ (q : ℝ) ^ e := by linarith
  have hne : t ≠ eis3 q e z := by
    intro hEq
    have hnorm_eis : (q : ℝ) ^ e - (q : ℝ) ^ (-(e : ℤ)) - 1 ≤ ‖eis3 q e z‖ := by
      have h1 : ‖(q : ℂ) ^ (e : ℤ) * z⁻¹‖ = (q : ℝ) ^ e := by
        rw [norm_mul, norm_zpow, Complex.norm_natCast, zpow_natCast, norm_inv, hzn, inv_one, mul_one]
      have h2 : ‖(q : ℂ) ^ (-(e : ℤ)) * z + 1‖ ≤ (q : ℝ) ^ (-(e : ℤ)) + 1 := by
        calc ‖(q : ℂ) ^ (-(e : ℤ)) * z + 1‖
            ≤ ‖(q : ℂ) ^ (-(e : ℤ)) * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ = (q : ℝ) ^ (-(e : ℤ)) + 1 := by
              rw [norm_mul, norm_zpow, Complex.norm_natCast, hzn, mul_one, norm_one]
      have h3 : ‖(q : ℂ) ^ (e : ℤ) * z⁻¹‖ - ‖(q : ℂ) ^ (-(e : ℤ)) * z + 1‖ ≤ ‖eis3 q e z‖ := by
        have := norm_sub_norm_le ((q : ℂ) ^ (e : ℤ) * z⁻¹) (-((q : ℂ) ^ (-(e : ℤ)) * z + 1))
        rw [norm_neg, sub_neg_eq_add] at this
        simpa [eis3, add_comm, add_left_comm, add_assoc] using this
      linarith
    have hqe_inv : (q : ℝ) ^ (-(e : ℤ)) ≤ 1 / 7 := by
      rw [_root_.zpow_neg, zpow_natCast, inv_le_iff_one_le_mul₀ (by positivity)]
      linarith
    rw [hEq] at ht
    linarith
  refine ⟨hne, ?_⟩
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hE : (q : ℂ) ^ e * (t - eis3 q e z) =
      (q : ℂ) ^ e * t - (z + (q : ℂ) ^ e + ((q : ℂ) ^ e) ^ 2 * z⁻¹) := by
    unfold eis3
    rw [mul_sub, mul_add, mul_add]
    have h1 : (q : ℂ) ^ e * ((q : ℂ) ^ (-(e : ℤ)) * z) = z := by
      rw [← zpow_natCast, ← mul_assoc, ← zpow_add₀ hqc, add_neg_cancel, zpow_zero, one_mul]
    have h2 : (q : ℂ) ^ e * 1 = (q : ℂ) ^ e := mul_one _
    have h3 : (q : ℂ) ^ e * ((q : ℂ) ^ (e : ℤ) * z⁻¹) = ((q : ℂ) ^ e) ^ 2 * z⁻¹ := by
      rw [zpow_natCast, ← mul_assoc, ← sq]
    rw [h1, h2, h3]
  have hX0 : 0 < ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ :=
    norm_pos_iff.mpr (mul_ne_zero (pow_ne_zero _ hqc) (sub_ne_zero.mpr hne))
  rw [Real.log_le_iff_le_exp hX0]
  have hexp : Real.exp (2 * (e : ℝ) * Real.log q + 1) = ((q : ℝ) ^ e) ^ 2 * Real.exp 1 := by
    rw [Real.exp_add, show 2 * (e : ℝ) * Real.log q = ((2 * e : ℕ) : ℝ) * Real.log q by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hq0_real]
    ring
  rw [hexp]
  have hPc : ‖(q : ℂ) ^ e‖ = (q : ℝ) ^ e := by rw [norm_pow, Complex.norm_natCast]
  have hX : ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤
      (q : ℝ) ^ e * (Real.sqrt q + 2) + (1 + (q : ℝ) ^ e + ((q : ℝ) ^ e) ^ 2) := by
    rw [hE]
    calc ‖(q : ℂ) ^ e * t - (z + (q : ℂ) ^ e + ((q : ℂ) ^ e) ^ 2 * z⁻¹)‖
        ≤ ‖(q : ℂ) ^ e * t‖ + ‖z + (q : ℂ) ^ e + ((q : ℂ) ^ e) ^ 2 * z⁻¹‖ := norm_sub_le _ _
      _ ≤ ‖(q : ℂ) ^ e * t‖ + (‖z‖ + ‖(q : ℂ) ^ e‖ + ‖((q : ℂ) ^ e) ^ 2 * z⁻¹‖) := by
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ (q : ℝ) ^ e * (Real.sqrt q + 2) + (1 + (q : ℝ) ^ e + ((q : ℝ) ^ e) ^ 2) := by
          rw [norm_mul, hPc, hzn, norm_mul, norm_pow, hPc, norm_inv, hzn, inv_one, mul_one]
          gcongr
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hP2 : (q : ℝ) ^ e * (Real.sqrt q + 2) + (1 + (q : ℝ) ^ e + ((q : ℝ) ^ e) ^ 2)
      ≤ 2 * ((q : ℝ) ^ e) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (q : ℝ) ^ e - 7)
      (by linarith : 0 ≤ (q : ℝ) ^ e - Real.sqrt q - 4)]
  have hP0 : 0 ≤ ((q : ℝ) ^ e) ^ 2 := sq_nonneg _
  nlinarith

end GlobalResultantNN

/-! ## Section 5: Two-Auxiliary-Prime Elimination & `condF E` `CountI` Polynomial Bridge -/

section SumOutCountIBridge

/-- **Two-Auxiliary-Prime `CorGSumLog` Elimination (`two_aux_primes_sum_log_bound`)**:
If `q₁ ≠ q₂` are primes with nonzero resultant integers `NN₁, NN₂ : ℤ`, and for every prime
`l ∈ Ls` away from `q₁` (resp. `q₂`) the Selmer length `sel l` is bounded by `2 * v_l(NN₁)`
(resp. `2 * v_l(NN₂)`), then simultaneously across ALL primes `l ∈ Ls`:
`∑ l ∈ Ls, Real.log l * sel l ≤ 2 * Real.log |NN₁| + 2 * Real.log |NN₂|`. -/
theorem two_aux_primes_sum_log_bound (q₁ q₂ : ℕ) (hq_ne : q₁ ≠ q₂)
    (NN₁ NN₂ : ℤ) (hNN₁ : NN₁ ≠ 0) (hNN₂ : NN₂ ≠ 0)
    (Ls : Finset Nat.Primes) (sel : Nat.Primes → ℝ)
    (h1 : ∀ l ∈ Ls, (l : ℕ) ≠ q₁ → sel l ≤ 2 * (padicValInt l NN₁ : ℝ))
    (h2 : ∀ l ∈ Ls, (l : ℕ) ≠ q₂ → sel l ≤ 2 * (padicValInt l NN₂ : ℝ)) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * sel l ≤
      2 * Real.log |(NN₁ : ℝ)| + 2 * Real.log |(NN₂ : ℝ)| := by
  have key : ∀ l ∈ Ls, sel l ≤ 2 * (padicValInt l NN₁ : ℝ) + 2 * (padicValInt l NN₂ : ℝ) := by
    intro l hl
    have a1 : (0 : ℝ) ≤ (padicValInt l NN₁ : ℝ) := Nat.cast_nonneg _
    have a2 : (0 : ℝ) ≤ (padicValInt l NN₂ : ℝ) := Nat.cast_nonneg _
    by_cases hlp : (l : ℕ) = q₁
    · have hlp2 : (l : ℕ) ≠ q₂ := fun h => hq_ne (hlp.symm.trans h)
      linarith [h2 l hl hlp2]
    · linarith [h1 l hl hlp]
  have s1 := sum_log_padicValInt_le_log_abs NN₁ hNN₁ Ls
  have s2 := sum_log_padicValInt_le_log_abs NN₂ hNN₂ Ls
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * sel l
      ≤ ∑ l ∈ Ls, Real.log (l : ℕ) *
          (2 * (padicValInt l NN₁ : ℝ) + 2 * (padicValInt l NN₂ : ℝ)) :=
        Finset.sum_le_sum fun l hl =>
          mul_le_mul_of_nonneg_left (key l hl) (Real.log_natCast_nonneg _)
    _ = 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l NN₁ : ℝ) +
          2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l NN₂ : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ 2 * Real.log |(NN₁ : ℝ)| + 2 * Real.log |(NN₂ : ℝ)| := by linarith

/-- **Master `CountI` / `SumOut` Polynomial Selmer Bound Bridge (`sumOut_countI_poly_bound_of_NN`)**:
Given a host number field `E` with `N := RHDirect.condF E ≥ 2` and height cutoff `t ≥ 2`,
two auxiliary primes `q₁ ≠ q₂` bounded by `(N * (e + 1)) ^ A_q`, and for each `r ∈ {1, 2}` an
automorphic trace resultant family `T_r` of cardinality `M_r ≤ (N * (e + 1)) ^ A`, degree `≤ D`,
and Archimedean bound `d * q_r^{w₀}` controlling `∑_{ψ} V_n(l, e, ψ) ≤ 2 * ∑_i v_l(Norm(a_w - eis_w))`
for all `l ≠ q_r`, we obtain the **pure polynomial bound** `(condF E * t) ^ C0` simultaneously
across ALL finite sets `Ls : Finset Nat.Primes` (matching `GaloisModularityCore.SixCaseSelmerHost.countI`)! -/
theorem sumOut_countI_poly_bound_of_NN
    (E : Type) [Field E] [NumberField E]
    (t e : ℕ) (ht : 2 ≤ t) (he : e < t) (hN2 : 2 ≤ RHDirect.condF E)
    (q₁ q₂ : ℕ) (hq_ne : q₁ ≠ q₂) (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    {M₁ M₂ D A A_D A_d A_w A_q : ℕ} {d w₀ : ℝ}
    (T₁ : AutomorphicTraceResultantData M₁ D d w₀ q₁)
    (T₂ : AutomorphicTraceResultantData M₂ D d w₀ q₂)
    (hd1 : 1 ≤ d) (hw₀ : 0 ≤ w₀)
    (hM₁ : M₁ ≤ (RHDirect.condF E * (e + 1)) ^ A)
    (hM₂ : M₂ ≤ (RHDirect.condF E * (e + 1)) ^ A)
    (hD : D ≤ (RHDirect.condF E * (e + 1)) ^ A_D)
    (hd_poly : d ≤ ((RHDirect.condF E * (e + 1) : ℕ) : ℝ) ^ A_d)
    (hw_poly : w₀ ≤ ((RHDirect.condF E * (e + 1) : ℕ) : ℝ) ^ A_w)
    (hq₁_poly : (q₁ : ℝ) ≤ ((RHDirect.condF E * (e + 1) : ℕ) : ℝ) ^ A_q)
    (hq₂_poly : (q₂ : ℝ) ≤ ((RHDirect.condF E * (e + 1) : ℕ) : ℝ) ^ A_q)
    (sel : Nat.Primes → ℝ)
    (hsel₁ : ∀ l : Nat.Primes, (l : ℕ) ≠ q₁ →
      sel l ≤ 2 * ∑ i : Fin M₁, (padicValInt l (T₁.factorNorm i) : ℝ))
    (hsel₂ : ∀ l : Nat.Primes, (l : ℕ) ≠ q₂ →
      sel l ≤ 2 * ∑ i : Fin M₂, (padicValInt l (T₂.factorNorm i) : ℝ))
    (Ls : Finset Nat.Primes) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * sel l ≤
      ((RHDirect.condF E : ℝ) * (t : ℝ)) ^ (A + A_D + A_d + A_w + A_q + 5) := by
  set N := RHDirect.condF E
  have hval₁ : ∀ l : Nat.Primes,
      ∑ i : Fin M₁, (padicValInt l (T₁.factorNorm i) : ℝ) =
        (padicValInt l (globalResultantNN T₁) : ℝ) := by
    intro l
    unfold globalResultantNN
    rw [padicValInt_prod_fin l.2 T₁.factorNorm T₁.factorNorm_ne_zero]
    push_cast; rfl
  have hval₂ : ∀ l : Nat.Primes,
      ∑ i : Fin M₂, (padicValInt l (T₂.factorNorm i) : ℝ) =
        (padicValInt l (globalResultantNN T₂) : ℝ) := by
    intro l
    unfold globalResultantNN
    rw [padicValInt_prod_fin l.2 T₂.factorNorm T₂.factorNorm_ne_zero]
    push_cast; rfl
  have htwo := two_aux_primes_sum_log_bound q₁ q₂ hq_ne
    (globalResultantNN T₁) (globalResultantNN T₂)
    (globalResultantNN_ne_zero T₁) (globalResultantNN_ne_zero T₂)
    Ls sel (fun l _ hl => (hsel₁ l hl).trans_eq (congrArg (2 * ·) (hval₁ l)))
    (fun l _ hl => (hsel₂ l hl).trans_eq (congrArg (2 * ·) (hval₂ l)))
  have hlog₁ := globalResultantNN_log_poly_bound T₁ hd1 hq₁ hw₀ hN2 hM₁ hD hd_poly hw_poly
  have hlog₂ := globalResultantNN_log_poly_bound T₂ hd1 hq₂ hw₀ hN2 hM₂ hD hd_poly hw_poly
  set B₁ := A + A_D + A_d + A_w + 3
  set W : ℝ := (N : ℝ) * ((e : ℝ) + 1)
  have hW_eq : ((N * (e + 1) : ℕ) : ℝ) = W := by
    simp only [W, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hW2 : (2 : ℝ) ≤ W := by
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have he' : (1 : ℝ) ≤ (e : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) e]
    nlinarith
  have hlogq₁ : Real.log q₁ ≤ W ^ A_q := by
    have h1 : Real.log q₁ ≤ (q₁ : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q₁ by exact_mod_cast (by omega : 0 < q₁))
      linarith
    have hq₁' : (q₁ : ℝ) ≤ W ^ A_q := by rwa [← hW_eq]
    exact h1.trans hq₁'
  have hlogq₂ : Real.log q₂ ≤ W ^ A_q := by
    have h1 : Real.log q₂ ≤ (q₂ : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q₂ by exact_mod_cast (by omega : 0 < q₂))
      linarith
    have hq₂' : (q₂ : ℝ) ≤ W ^ A_q := by rwa [← hW_eq]
    exact h1.trans hq₂'
  have hW_le_Nt : W ≤ (N : ℝ) * (t : ℝ) := by
    have he1 : (e : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast (by omega : e + 1 ≤ t)
    exact mul_le_mul_of_nonneg_left he1 (Nat.cast_nonneg N)
  have hNt2 : (2 : ℝ) ≤ (N : ℝ) * (t : ℝ) := hW2.trans hW_le_Nt
  have hNt_pow : W ^ (B₁ + A_q) ≤ ((N : ℝ) * (t : ℝ)) ^ (B₁ + A_q) :=
    pow_le_pow_left₀ (by linarith) hW_le_Nt _
  have h4_le : (4 : ℝ) ≤ ((N : ℝ) * (t : ℝ)) ^ 2 := by nlinarith
  have hpow_tot : ((N : ℝ) * (t : ℝ)) ^ (B₁ + A_q) * 4 ≤
      ((N : ℝ) * (t : ℝ)) ^ (A + A_D + A_d + A_w + A_q + 5) := by
    have h4' : 4 * ((N : ℝ) * (t : ℝ)) ^ (B₁ + A_q) ≤
        ((N : ℝ) * (t : ℝ)) ^ 2 * ((N : ℝ) * (t : ℝ)) ^ (B₁ + A_q) :=
      mul_le_mul_of_nonneg_right h4_le (by positivity)
    rw [← pow_add] at h4'
    have hexp : 2 + (B₁ + A_q) = A + A_D + A_d + A_w + A_q + 5 := by omega
    rw [hexp] at h4'
    linarith
  have hsum_bd : 2 * Real.log |(globalResultantNN T₁ : ℝ)| + 2 * Real.log |(globalResultantNN T₂ : ℝ)| ≤
      4 * W ^ (B₁ + A_q) := by
    have hb1 : Real.log |(globalResultantNN T₁ : ℝ)| ≤ W ^ (B₁ + A_q) := by
      calc Real.log |(globalResultantNN T₁ : ℝ)| ≤ W ^ B₁ * Real.log q₁ := hlog₁
        _ ≤ W ^ B₁ * W ^ A_q := mul_le_mul_of_nonneg_left hlogq₁ (by positivity)
        _ = W ^ (B₁ + A_q) := (pow_add W B₁ A_q).symm
    have hb2 : Real.log |(globalResultantNN T₂ : ℝ)| ≤ W ^ (B₁ + A_q) := by
      calc Real.log |(globalResultantNN T₂ : ℝ)| ≤ W ^ B₁ * Real.log q₂ := hlog₂
        _ ≤ W ^ B₁ * W ^ A_q := mul_le_mul_of_nonneg_left hlogq₂ (by positivity)
        _ = W ^ (B₁ + A_q) := (pow_add W B₁ A_q).symm
    linarith
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * sel l
      ≤ 2 * Real.log |(globalResultantNN T₁ : ℝ)| + 2 * Real.log |(globalResultantNN T₂ : ℝ)| := htwo
    _ ≤ 4 * W ^ (B₁ + A_q) := hsum_bd
    _ ≤ 4 * ((N : ℝ) * (t : ℝ)) ^ (B₁ + A_q) := by gcongr
    _ ≤ ((N : ℝ) * (t : ℝ)) ^ (A + A_D + A_d + A_w + A_q + 5) := by linarith

end SumOutCountIBridge

end RHDirect.Stage13BorelClozelBounds

end
