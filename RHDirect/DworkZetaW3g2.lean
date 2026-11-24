/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3b'-general, steps 2 and 4.
-/
import RHDirect.DworkZetaW3g3

/-!
# `RHDirect.DworkZetaW3g2`

**Step 2.**  Over a field `K` with `Nat.card K = p ^ n`, every element satisfies `x ^ (p ^ n) = x`
(`FiniteField.pow_card`), so `X ^ (p ^ n) - X` has all `p ^ n` elements of `K` as roots.  Its degree
is `p ^ n` (`FiniteField.X_pow_card_sub_X_natDegree_eq`), so the root multiset has full cardinality
and the polynomial splits (`splits_iff_card_roots`).  No `CharP`/`ExpChar` and no `n ≠ 0` is needed:
`1 < p ^ n` follows from `Fintype.one_lt_card`.

**Step 4.**  For `m ∣ n`, `X ^ (p^m) - X` divides `X ^ (p^n) - X` (step 1), the latter splits
(step 2), so the former splits (`Splits.of_dvd`); it is separable (step 3), so all its roots are
simple (`Polynomial.nodup_roots`) and there are `natDegree = p ^ m` of them.  Hence
`N_m = #Fix(φ^m) = p ^ m`.
-/

namespace RHDirect
namespace HasseWeil

open Polynomial

/-- **Step 2.**  `X ^ (p ^ n) - X` splits over a field with `p ^ n` elements. -/
theorem splits_X_pow_pow_sub_X (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (p n : ℕ) (hK : Nat.card K = p ^ n) :
    (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).Splits := by
  classical
  have hcard : p ^ n = Fintype.card K := by rw [← hK, Nat.card_eq_fintype_card]
  have hgt : 1 < p ^ n := by rw [hcard]; exact Fintype.one_lt_card
  have hdeg : (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).natDegree = p ^ n :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K hgt
  have hne : (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K) ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hdeg
    omega
  have hroot : ∀ x : K, (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).IsRoot x := by
    intro x
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero, hcard]
    exact FiniteField.pow_card x
  have hset : (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).roots.toFinset
      = Finset.univ := by
    ext x
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact ⟨fun _ => Finset.mem_univ x, fun _ => hroot x⟩
  have hlow : p ^ n ≤ (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).roots.card := by
    have h1 : (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).roots.toFinset.card
        = p ^ n := by
      rw [hset]
      simp [hcard]
    calc p ^ n
        = (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).roots.toFinset.card := h1.symm
      _ ≤ (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).roots.card :=
          Multiset.toFinset_card_le _
  have hup : (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K).roots.card ≤ p ^ n := by
    have h := Polynomial.card_roots' (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial K)
    rw [hdeg] at h
    exact h
  rw [Polynomial.splits_iff_card_roots]
  omega

/-- **Step 4, core.**  For `m ∣ n`, the number of solutions of `x ^ (p^m) = x` in a field with
`p ^ n` elements is exactly `p ^ m`. -/
theorem natCard_roots_eq_pow (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (p m n : ℕ) [CharP K p] (hK : Nat.card K = p ^ n) (hm : 0 < m) (hmn : m ∣ n) :
    Nat.card {x : K // x ^ (p ^ m) = x} = p ^ m := by
  classical
  obtain ⟨k, rfl⟩ := hmn
  -- `k ≠ 0`, since `#K = p ^ (m * k) ≥ 2`
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [h, mul_zero, pow_zero] at hK
      have h2 : 1 < Nat.card K := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
      omega
    · exact h
  -- hence `1 < p ^ m`
  have hgtm : 1 < p ^ m := by
    by_contra hle
    push Not at hle
    have h1 : (p ^ m) ^ k ≤ 1 ^ k := Nat.pow_le_pow_left hle k
    rw [one_pow] at h1
    have h2 : p ^ (m * k) ≤ 1 := by rw [pow_mul]; exact h1
    have h3 : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  have hdegm : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).natDegree = p ^ m :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K hgtm
  have hfm : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K) ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hdegm
    omega
  -- the solution set is the root set of `X ^ (p^m) - X`
  have hset : Nat.card {x : K // x ^ (p ^ m) = x}
      = (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).roots.toFinset.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfm, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    simp
  rw [hset]
  -- `X ^ (p^m) - X` divides `X ^ (p^(m*k)) - X`  (step 1, with `R := K`)
  have hgtg : 1 < p ^ (m * k) := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hg : (Polynomial.X ^ (p ^ (m * k)) - Polynomial.X : Polynomial K).Splits :=
    splits_X_pow_pow_sub_X K p (m * k) hK
  have hgne : (Polynomial.X ^ (p ^ (m * k)) - Polynomial.X : Polynomial K) ≠ 0 := by
    intro hzero
    have hd := FiniteField.X_pow_card_sub_X_natDegree_eq K hgtg
    rw [hzero, Polynomial.natDegree_zero] at hd
    omega
  have hdvd : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K) ∣
      Polynomial.X ^ (p ^ (m * k)) - Polynomial.X := by
    have h := X_pow_sub_X_dvd_X_pow_pow_sub_X (R := K) (p ^ m) k
    simpa [pow_mul] using h
  have hspl : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).Splits :=
    Polynomial.Splits.of_dvd hg hgne hdvd
  have hsep : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).Separable :=
    separable_X_pow_pow_sub_X p m hm
  have hnodup : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).roots.Nodup :=
    Polynomial.nodup_roots hsep
  have hcardeq : (Polynomial.X ^ (p ^ m) - Polynomial.X : Polynomial K).roots.card = p ^ m := by
    rw [← hspl.natDegree_eq_card_roots, hdegm]
  rw [Multiset.toFinset_card_of_nodup hnodup, hcardeq]

/-- **Step 4.**  `N_m = #Fix(φ^m) = p ^ m` inside a field with `p ^ n` elements, for `m ∣ n`. -/
theorem natCard_fixed_eq_pow_of_dvd (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (p m n : ℕ) [CharP K p] [ExpChar K p] (hK : Nat.card K = p ^ n) (hm : 0 < m) (hmn : m ∣ n) :
    Nat.card {x : K // ((frobeniusAut K p) ^ m) x = x} = p ^ m := by
  rw [natCard_fixed_eq K p m]
  exact natCard_roots_eq_pow K p m n hK hm hmn

end HasseWeil
end RHDirect
