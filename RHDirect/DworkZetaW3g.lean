/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3g: the fixed field of `φ ^ m` as a subfield — the tower `𝔽_{p^m} ⊆ 𝔽_{p^n}`.
-/
import RHDirect.DworkZetaW3f
import Mathlib.FieldTheory.Galois.Basic

/-!
# `RHDirect.DworkZetaW3g`

Wave 3b proved `Nat.card {x // (φ^m) x = x} = p^m` for `m ∣ n`.  That is a statement about a
*set*.  This file upgrades it: the set is a **subfield** (`fixSubfield`), so it is a copy of
`𝔽_{p^m}` sitting inside `𝔽_{p^n}`, and the tower is nested.
-/

namespace RHDirect
namespace HasseWeil

noncomputable section

/-- The fixed points of an automorphism power `φ ^ m` form a subfield. -/
def fixSubfield (K : Type*) [Field K] (φ : K ≃+* K) (m : ℕ) : Subfield K where
  carrier := {x | (φ ^ m) x = x}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [RingEquiv.map_add, ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [RingEquiv.map_neg, ha]
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [RingEquiv.map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv₀, ha]

@[simp] theorem mem_fixSubfield {K : Type*} [Field K] (φ : K ≃+* K) (m : ℕ) (x : K) :
    x ∈ fixSubfield K φ m ↔ (φ ^ m) x = x := Iff.rfl

/-- **The tower.**  Inside a field with `p ^ n` elements, the fixed field of `φ ^ m` (for `m ∣ n`)
has exactly `p ^ m` elements — it is a copy of `𝔽_{p^m}`. -/
theorem card_fixSubfield (K : Type*) [Field K] [Fintype K] (p n m : ℕ) [CharP K p] [ExpChar K p]
    (hK : Nat.card K = p ^ n) (hm : 0 < m) (hmn : m ∣ n) :
    Nat.card (fixSubfield K (frobeniusAut K p) m) = p ^ m := by
  classical
  have hcarrier : Nat.card (fixSubfield K (frobeniusAut K p) m)
      = Nat.card {x : K // (frobeniusAut K p ^ m) x = x} := rfl
  rw [hcarrier, natCard_fixed_eq_pow_of_dvd K p m n hK hm hmn]

/-- **`𝔽_{p^m}` is a subfield of `𝔽_{p^n}`** when `m ∣ n`: the fixed field of `φ^m` has `p^m`
elements, so it *is* the field with `p^m` elements. -/
theorem exists_subfield_card (K : Type*) [Field K] [Fintype K] (p n m : ℕ) [CharP K p] [ExpChar K p]
    (hK : Nat.card K = p ^ n) (hm : 0 < m) (hmn : m ∣ n) :
    ∃ L : Subfield K, Nat.card L = p ^ m :=
  ⟨fixSubfield K (frobeniusAut K p) m, card_fixSubfield K p n m hK hm hmn⟩

/-- The tower is nested: `d ∣ m` gives `Fix(φ^d) ≤ Fix(φ^m)`. -/
theorem fixSubfield_mono (K : Type*) [Field K] (φ : K ≃+* K) {d m : ℕ} (hdm : d ∣ m) :
    fixSubfield K φ d ≤ fixSubfield K φ m := by
  obtain ⟨k, rfl⟩ := hdm
  intro x hx
  simp only [mem_fixSubfield] at hx ⊢
  rw [pow_mul]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    show ((φ ^ d) ^ k) ((φ ^ d) x) = x
    rw [hx]
    exact ih

end

end HasseWeil
end RHDirect
