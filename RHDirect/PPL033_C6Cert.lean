/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import RHDirect.PPL033_C6Base
import RHDirect.PPL033_C6Q3
import RHDirect.PPL033_C6Q2A
import RHDirect.PPL033_C6Q2B
import RHDirect.PPL033_C6B2_0
import RHDirect.PPL033_C6B2_1
import RHDirect.PPL033_C6B2_2
import RHDirect.PPL033_C6B2_3
import RHDirect.PPL033_C6B2_4
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

/-!
# PPL 033 — World-Record Coupled `Q_3 + B_2(Q_4)` Certificate for `ex(Q_n, C_6)` (`< 0.3649 < 0.36577`)

Zero `sorry`, zero custom axioms, zero `native_decide`.
-/

namespace PPL033_C6Cert

private lemma q2Term_eq_shift (a b ab ba c0 ca cb ck cl d0 da db dk dl : Bool) :
    q2Term a b ab ba c0 ca cb ck cl d0 da db dk dl = (q2Shift a b ab ba c0 ca cb ck cl d0 da db dk dl : ℤ) - 1000000 := by
  unfold q2Term q2Shift
  by_cases hc : isCanonRoot a b ab ba
  · simp only [hc, ↓reduceIte]
    generalize rcIdx a b ab ba = r
    fin_cases r <;> dsimp only
    · simp only [checkQ2_0_ok]; ring
    · simp only [checkQ2_1_ok]; ring
    · simp only [checkQ2_2_ok]; ring
    · simp only [checkQ2_3_ok]; ring
    · simp only [checkQ2_4_ok]; ring
    · simp only [checkQ2_5_ok]; ring
    · simp only [checkQ2_6_ok]; ring
    · simp only [checkQ2_7_ok]; ring
    · simp only [checkQ2_8_ok]; ring
    · simp only [checkQ2_9_ok]; ring
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; ring

private lemma b2LocalBool_eq_shift (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) :
    b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = (b2PosShift b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : ℤ) - 144000000 := by
  unfold b2LocalBool b2UngaugedBool b2PosShift
  simp_rw [b4Pair_eq_shift, q2Term_eq_shift]
  unfold lam23 phiFlip phiFlip2; push_cast; ring

private lemma b4Pair_symm (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair c d cd dc a b ab ba := by dsimp only [b4Pair]; ring
private lemma b4Pair_swap1 (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair b a ba ab c d cd dc := by dsimp only [b4Pair]; rw [rcIdx_swap a b ab ba]
private lemma b4Pair_swap2 (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair a b ab ba d c dc cd := by dsimp only [b4Pair]; rw [rcIdx_swap c d cd dc]
private lemma q2Term_symm (a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 : Bool) :
    q2Term a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 = q2Term a b ab ba l4 l3 l2 l1 l0 k4 k3 k2 k1 k0 := by
  dsimp only [q2Term]; split_ifs <;> ring

private lemma b2IsC6FreeBool_swap01 (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) :
    b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = b2IsC6FreeBool b02 b01 b04 b08 b23 b26 b2a b13 b15 b19 b46 b45 b4c b8a b89 b8c := by
  dsimp only [b2IsC6FreeBool]
  have hc_0 : (!(b01 && b08 && b13 && b23 && b2a && b8a)) = (!(b01 && b08 && b23 && b2a && b13 && b8a)) := by congr 1; ac_rfl
  have hc_1 : (!(b01 && b02 && b19 && b2a && b89 && b8a)) = (!(b02 && b01 && b2a && b19 && b8a && b89)) := by congr 1; ac_rfl
  have hc_3 : (!(b01 && b04 && b13 && b23 && b26 && b46)) = (!(b01 && b04 && b23 && b26 && b13 && b46)) := by congr 1; ac_rfl
  have hc_6 : (!(b13 && b15 && b23 && b26 && b45 && b46)) = (!(b23 && b26 && b13 && b15 && b46 && b45)) := by congr 1; ac_rfl
  have hc_9 : (!(b13 && b19 && b23 && b2a && b89 && b8a)) = (!(b23 && b2a && b13 && b19 && b8a && b89)) := by congr 1; ac_rfl
  have hc_11 : (!(b01 && b02 && b15 && b26 && b45 && b46)) = (!(b02 && b01 && b26 && b15 && b46 && b45)) := by congr 1; ac_rfl
  have hc_12 : (!(b02 && b04 && b13 && b15 && b23 && b45)) = (!(b02 && b04 && b23 && b13 && b15 && b45)) := by congr 1; ac_rfl
  have hc_13 : (!(b02 && b08 && b13 && b19 && b23 && b89)) = (!(b02 && b08 && b23 && b13 && b19 && b89)) := by congr 1; ac_rfl
  rw [hc_0, hc_1, hc_3, hc_6, hc_9, hc_11, hc_12, hc_13]
  ac_rfl

private lemma b2LocalBool_swap01 (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) :
    b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = b2LocalBool b02 b01 b04 b08 b23 b26 b2a b13 b15 b19 b46 b45 b4c b8a b89 b8c := by
  dsimp only [b2LocalBool, b2UngaugedBool]
  rw [lam23_swap01 b01 b02 b08 b13 b23 b19 b89 b2a b8a, lam23_swap01 b01 b02 b04 b13 b23 b15 b45 b26 b46]
  rw [phiFlip_swap12 b04 (mkFlag b01 b45 b15) (mkFlag b02 b46 b26) (mkFlag b08 b4c b8c), phiFlip_swap12 b08 (mkFlag b01 b89 b19) (mkFlag b02 b8a b2a) (mkFlag b04 b8c b4c)]
  rw [b4Pair_swap1 b01 b02 b13 b23 b04 b08 b4c b8c, b4Pair_symm b01 b04 b15 b45 b02 b08 b2a b8a, b4Pair_symm b01 b08 b19 b89 b02 b04 b26 b46]
  rw [q2Term_symm b04 b08 b4c b8c b01 b45 b89 b15 b19 b02 b46 b8a b26 b2a, q2Term_symm b08 b04 b8c b4c b01 b89 b45 b19 b15 b02 b8a b46 b2a b26]
  rw [phiFlip2_swapAB b01 b02 b13 b23 b15 b19 b26 b2a, phiFlip2_swapKL b04 b08 b4c b8c b45 b46 b89 b8a]
  ring

private lemma b2IsC6FreeBool_swap12 (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) :
    b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = b2IsC6FreeBool b01 b04 b02 b08 b15 b13 b19 b45 b46 b4c b23 b26 b2a b89 b8c b8a := by
  dsimp only [b2IsC6FreeBool]
  have hc_3 : (!(b01 && b04 && b13 && b23 && b26 && b46)) = (!(b01 && b04 && b13 && b46 && b23 && b26)) := by congr 1; ac_rfl
  have hc_5 : (!(b26 && b2a && b46 && b4c && b8a && b8c)) = (!(b46 && b4c && b26 && b2a && b8c && b8a)) := by congr 1; ac_rfl
  have hc_6 : (!(b13 && b15 && b23 && b26 && b45 && b46)) = (!(b15 && b13 && b45 && b46 && b23 && b26)) := by congr 1; ac_rfl
  have hc_7 : (!(b02 && b08 && b26 && b46 && b4c && b8c)) = (!(b02 && b08 && b46 && b4c && b26 && b8c)) := by congr 1; ac_rfl
  have hc_8 : (!(b04 && b08 && b26 && b2a && b46 && b8a)) = (!(b04 && b08 && b46 && b26 && b2a && b8a)) := by congr 1; ac_rfl
  have hc_11 : (!(b01 && b02 && b15 && b26 && b45 && b46)) = (!(b01 && b02 && b15 && b45 && b46 && b26)) := by congr 1; ac_rfl
  have hc_12 : (!(b02 && b04 && b13 && b15 && b23 && b45)) = (!(b04 && b02 && b15 && b13 && b45 && b23)) := by congr 1; ac_rfl
  have hc_15 : (!(b02 && b04 && b2a && b4c && b8a && b8c)) = (!(b04 && b02 && b4c && b2a && b8c && b8a)) := by congr 1; ac_rfl
  rw [hc_3, hc_5, hc_6, hc_7, hc_8, hc_11, hc_12, hc_15]
  ac_rfl

private lemma b2LocalBool_swap12 (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) :
    b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = b2LocalBool b01 b04 b02 b08 b15 b13 b19 b45 b46 b4c b23 b26 b2a b89 b8c b8a := by
  dsimp only [b2LocalBool, b2UngaugedBool]
  rw [lam23_swap01 b02 b04 b08 b26 b46 b2a b8a b4c b8c, lam23_swap12 b01 b02 b04 b13 b23 b15 b45 b26 b46]
  rw [phiFlip_swap12 b01 (mkFlag b02 b13 b23) (mkFlag b04 b15 b45) (mkFlag b08 b19 b89), phiFlip_swap23 b08 (mkFlag b01 b89 b19) (mkFlag b02 b8a b2a) (mkFlag b04 b8c b4c)]
  rw [b4Pair_swap2 b01 b08 b19 b89 b02 b04 b26 b46]
  rw [q2Term_symm b01 b08 b19 b89 b02 b13 b8a b23 b2a b04 b15 b8c b45 b4c, q2Term_symm b08 b01 b89 b19 b02 b8a b13 b2a b23 b04 b8c b15 b4c b45]
  rw [phiFlip2_swapKL b01 b08 b19 b89 b13 b15 b8a b8c, phiFlip2_swapAB b02 b04 b26 b46 b23 b2a b45 b4c]
  ring

private lemma b2IsC6FreeBool_swap23 (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) :
    b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = b2IsC6FreeBool b01 b02 b08 b04 b13 b19 b15 b23 b2a b26 b89 b8a b8c b45 b46 b4c := by
  dsimp only [b2IsC6FreeBool]
  have hc_2 : (!(b01 && b04 && b19 && b4c && b89 && b8c)) = (!(b01 && b04 && b19 && b89 && b8c && b4c)) := by congr 1; ac_rfl
  have hc_4 : (!(b15 && b19 && b45 && b4c && b89 && b8c)) = (!(b19 && b15 && b89 && b8c && b45 && b4c)) := by congr 1; ac_rfl
  have hc_5 : (!(b26 && b2a && b46 && b4c && b8a && b8c)) = (!(b2a && b26 && b8a && b8c && b46 && b4c)) := by congr 1; ac_rfl
  have hc_7 : (!(b02 && b08 && b26 && b46 && b4c && b8c)) = (!(b02 && b08 && b26 && b8c && b46 && b4c)) := by congr 1; ac_rfl
  have hc_8 : (!(b04 && b08 && b26 && b2a && b46 && b8a)) = (!(b08 && b04 && b2a && b26 && b8a && b46)) := by congr 1; ac_rfl
  have hc_10 : (!(b04 && b08 && b15 && b19 && b45 && b89)) = (!(b08 && b04 && b19 && b15 && b89 && b45)) := by congr 1; ac_rfl
  have hc_14 : (!(b01 && b08 && b15 && b45 && b4c && b8c)) = (!(b01 && b08 && b15 && b8c && b45 && b4c)) := by congr 1; ac_rfl
  have hc_15 : (!(b02 && b04 && b2a && b4c && b8a && b8c)) = (!(b02 && b04 && b2a && b8a && b8c && b4c)) := by congr 1; ac_rfl
  rw [hc_2, hc_4, hc_5, hc_7, hc_8, hc_10, hc_14, hc_15]
  ac_rfl

private lemma b2LocalBool_swap23 (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) :
    b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = b2LocalBool b01 b02 b08 b04 b13 b19 b15 b23 b2a b26 b89 b8a b8c b45 b46 b4c := by
  dsimp only [b2LocalBool, b2UngaugedBool]
  rw [lam23_swap12 b02 b04 b08 b26 b46 b2a b8a b4c b8c, lam23_swap12 b01 b04 b08 b15 b45 b19 b89 b4c b8c]
  rw [phiFlip_swap23 b01 (mkFlag b02 b13 b23) (mkFlag b04 b15 b45) (mkFlag b08 b19 b89), phiFlip_swap23 b02 (mkFlag b01 b23 b13) (mkFlag b04 b26 b46) (mkFlag b08 b2a b8a)]
  rw [b4Pair_swap2 b01 b02 b13 b23 b04 b08 b4c b8c]
  rw [q2Term_symm b01 b02 b13 b23 b04 b15 b26 b45 b46 b08 b19 b2a b89 b8a, q2Term_symm b02 b01 b23 b13 b04 b26 b15 b46 b45 b08 b2a b19 b8a b89]
  rw [phiFlip2_swapKL b01 b02 b13 b23 b15 b19 b26 b2a, phiFlip2_swapAB b04 b08 b4c b8c b45 b46 b89 b8a]
  ring
private lemma b2_le_of_sorted_star (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool)
    (h01 : (!b01 || b02) = true) (h12 : (!b02 || b04) = true) (h23 : (!b04 || b08) = true)
    (hc : b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = true) :
    0 ≤ b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c + (B2_OFF : ℤ) ∧ b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c ≤ M4 := by
  have hsh := b2LocalBool_eq_shift b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c
  have hp : 124000000 ≤ b2PosShift b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c ∧ b2PosShift b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c ≤ M4_shift + 124000000 := by
    cases b01 <;> cases b02 <;> cases b04 <;> cases b08 <;> try contradiction
    · exact b2_sorted_0000 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c hc
    · exact b2_sorted_0001 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c hc
    · exact b2_sorted_0011 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c hc
    · exact b2_sorted_0111 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c hc
    · exact b2_sorted_1111 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c hc
  have hZ1 := Int.ofNat_le.mpr hp.1; have hZ2 := Int.ofNat_le.mpr hp.2
  push_cast at hZ1 hZ2; dsimp only [B2_OFF, M4_shift, M4] at *; constructor <;> omega

private lemma b2_bounds_all (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) (hc : b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = true) :
    0 ≤ b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c + (B2_OFF : ℤ) ∧ b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c ≤ M4 := by
  by_cases s01 : b01 = true ∧ b02 = false
  · rw [b2LocalBool_swap01]; rw [b2IsC6FreeBool_swap01] at hc; rcases s01 with ⟨rfl, rfl⟩
    by_cases s23 : b04 = true ∧ b08 = false
    · rw [b2LocalBool_swap23]; rw [b2IsC6FreeBool_swap23] at hc; rcases s23 with ⟨rfl, rfl⟩
      rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
      exact b2_le_of_sorted_star false false true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
    · by_cases h2 : b04 = false
      · rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
        by_cases h3 : b08 = false
        · rw [b2LocalBool_swap23]; rw [b2IsC6FreeBool_swap23] at hc; subst h2 h3
          exact b2_le_of_sorted_star false false false true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
        · have ht3 : b08 = true := by cases b08 <;> simp_all
          subst h2 ht3; exact b2_le_of_sorted_star false false true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · have ht2 : b04 = true := by cases b04 <;> simp_all
        have ht3 : b08 = true := by cases b08 <;> simp_all
        subst ht2 ht3; exact b2_le_of_sorted_star false true true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
  · by_cases s23 : b04 = true ∧ b08 = false
    · rw [b2LocalBool_swap23]; rw [b2IsC6FreeBool_swap23] at hc; rcases s23 with ⟨rfl, rfl⟩
      cases b01 <;> cases b02 <;> try (exfalso; exact s01 ⟨rfl, rfl⟩)
      · exact b2_le_of_sorted_star false false false true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
        exact b2_le_of_sorted_star false false true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
        rw [b2LocalBool_swap01]; rw [b2IsC6FreeBool_swap01] at hc
        exact b2_le_of_sorted_star false true true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
    · cases b01 <;> cases b02 <;> cases b04 <;> cases b08 <;>
        try (exfalso; first | exact s01 ⟨rfl, rfl⟩ | exact s23 ⟨rfl, rfl⟩)
      · exact b2_le_of_sorted_star false false false false _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · exact b2_le_of_sorted_star false false false true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · exact b2_le_of_sorted_star false false true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
        rw [b2LocalBool_swap23]; rw [b2IsC6FreeBool_swap23] at hc
        exact b2_le_of_sorted_star false false false true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
        exact b2_le_of_sorted_star false false true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · exact b2_le_of_sorted_star false true  true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
        rw [b2LocalBool_swap01]; rw [b2IsC6FreeBool_swap01] at hc
        rw [b2LocalBool_swap23]; rw [b2IsC6FreeBool_swap23] at hc
        rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
        exact b2_le_of_sorted_star false false true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · rw [b2LocalBool_swap12]; rw [b2IsC6FreeBool_swap12] at hc
        rw [b2LocalBool_swap01]; rw [b2IsC6FreeBool_swap01] at hc
        exact b2_le_of_sorted_star false true  true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc
      · exact b2_le_of_sorted_star true  true  true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc

lemma b2LocalBool_le_M4 (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) (hc : b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = true) :
    b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c ≤ M4 := (b2_bounds_all b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c hc).2

lemma b2Fast_eq (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) :
    (b2Fast b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : ℤ) = if b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c then b2LocalBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c + (B2_OFF : ℤ) else 0 := by
  unfold b2Fast
  by_cases hc : b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = true
  · simp only [hc, ↓reduceIte]; have hb := (b2_bounds_all b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c hc).1; have hsh := b2LocalBool_eq_shift b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c
    have hle : 124000000 ≤ b2PosShift b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c := by dsimp only [B2_OFF] at hb; omega
    rw [Int.ofNat_sub hle]; dsimp only [B2_OFF] at *; omega
  · have hcf : b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = false := Bool.eq_false_iff.mpr hc; simp only [hcf, Bool.false_eq_true, ↓reduceIte]; rfl

lemma b2Fast_le_M4 (b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool) : b2Fast b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c ≤ M4_shift := by
  have he := b2Fast_eq b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c
  by_cases hc : b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = true
  · simp only [hc, ↓reduceIte] at he; have hle := b2LocalBool_le_M4 b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c hc
    have hZ : (b2Fast b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : ℤ) ≤ (M4_shift : ℤ) := by dsimp only [M4_shift, B2_OFF, M4] at *; omega
    exact Int.ofNat_le.mp hZ
  · have hcf : b2IsC6FreeBool b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = false := Bool.eq_false_iff.mpr hc
    simp only [hcf, Bool.false_eq_true, ↓reduceIte] at he; have h0 : b2Fast b01 b02 b04 b08 b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = 0 := by omega
    rw [h0]; decide

structure Q4Bits where
  q00 : Bool
  q01 : Bool
  q02 : Bool
  q03 : Bool
  q04 : Bool
  q05 : Bool
  q06 : Bool
  q07 : Bool
  q08 : Bool
  q09 : Bool
  q10 : Bool
  q11 : Bool
  q12 : Bool
  q13 : Bool
  q14 : Bool
  q15 : Bool
  q16 : Bool
  q17 : Bool
  q18 : Bool
  q19 : Bool
  q20 : Bool
  q21 : Bool
  q22 : Bool
  q23 : Bool
  q24 : Bool
  q25 : Bool
  q26 : Bool
  q27 : Bool
  q28 : Bool
  q29 : Bool
  q30 : Bool
  q31 : Bool
  deriving DecidableEq

structure B2Bits where
  b01 : Bool
  b02 : Bool
  b04 : Bool
  b08 : Bool
  b13 : Bool
  b15 : Bool
  b19 : Bool
  b23 : Bool
  b26 : Bool
  b2a : Bool
  b45 : Bool
  b46 : Bool
  b4c : Bool
  b89 : Bool
  b8a : Bool
  b8c : Bool
  deriving DecidableEq

def extractFacetQ3 (fk : Fin 8) (g : Q4Bits) : Q3Bits :=
  match fk.val with
  | 0 => { e01 := g.q01, e02 := g.q02, e04 := g.q03, e13 := g.q08, e15 := g.q09, e23 := g.q13, e26 := g.q14, e37 := g.q18, e45 := g.q21, e46 := g.q22, e57 := g.q26, e67 := g.q29 }
  | 1 => { e01 := g.q04, e02 := g.q05, e04 := g.q06, e13 := g.q10, e15 := g.q11, e23 := g.q15, e26 := g.q16, e37 := g.q19, e45 := g.q23, e46 := g.q24, e57 := g.q27, e67 := g.q30 }
  | 2 => { e01 := g.q00, e02 := g.q02, e04 := g.q03, e13 := g.q05, e15 := g.q06, e23 := g.q12, e26 := g.q14, e37 := g.q16, e45 := g.q20, e46 := g.q22, e57 := g.q24, e67 := g.q28 }
  | 3 => { e01 := g.q07, e02 := g.q08, e04 := g.q09, e13 := g.q10, e15 := g.q11, e23 := g.q17, e26 := g.q18, e37 := g.q19, e45 := g.q25, e46 := g.q26, e57 := g.q27, e67 := g.q31 }
  | 4 => { e01 := g.q00, e02 := g.q01, e04 := g.q03, e13 := g.q04, e15 := g.q06, e23 := g.q07, e26 := g.q09, e37 := g.q11, e45 := g.q20, e46 := g.q21, e57 := g.q23, e67 := g.q25 }
  | 5 => { e01 := g.q12, e02 := g.q13, e04 := g.q14, e13 := g.q15, e15 := g.q16, e23 := g.q17, e26 := g.q18, e37 := g.q19, e45 := g.q28, e46 := g.q29, e57 := g.q30, e67 := g.q31 }
  | 6 => { e01 := g.q00, e02 := g.q01, e04 := g.q02, e13 := g.q04, e15 := g.q05, e23 := g.q07, e26 := g.q08, e37 := g.q10, e45 := g.q12, e46 := g.q13, e57 := g.q15, e67 := g.q17 }
  | 7 => { e01 := g.q20, e02 := g.q21, e04 := g.q22, e13 := g.q23, e15 := g.q24, e23 := g.q25, e26 := g.q26, e37 := g.q27, e45 := g.q28, e46 := g.q29, e57 := g.q30, e67 := g.q31 }
  | _ => { e01 := false, e02 := false, e04 := false, e13 := false, e15 := false, e23 := false, e26 := false, e37 := false, e45 := false, e46 := false, e57 := false, e67 := false }

def extractBallB2 (v : Fin 16) (g : Q4Bits) : B2Bits :=
  match v.val with
  | 0 => { b01 := g.q00, b02 := g.q01, b04 := g.q02, b08 := g.q03, b13 := g.q04, b15 := g.q05, b19 := g.q06, b23 := g.q07, b26 := g.q08, b2a := g.q09, b45 := g.q12, b46 := g.q13, b4c := g.q14, b89 := g.q20, b8a := g.q21, b8c := g.q22 }
  | 1 => { b01 := g.q00, b02 := g.q04, b04 := g.q05, b08 := g.q06, b13 := g.q01, b15 := g.q02, b19 := g.q03, b23 := g.q07, b26 := g.q10, b2a := g.q11, b45 := g.q12, b46 := g.q15, b4c := g.q16, b89 := g.q20, b8a := g.q23, b8c := g.q24 }
  | 2 => { b01 := g.q07, b02 := g.q01, b04 := g.q08, b08 := g.q09, b13 := g.q04, b15 := g.q10, b19 := g.q11, b23 := g.q00, b26 := g.q02, b2a := g.q03, b45 := g.q17, b46 := g.q13, b4c := g.q18, b89 := g.q25, b8a := g.q21, b8c := g.q26 }
  | 3 => { b01 := g.q07, b02 := g.q04, b04 := g.q10, b08 := g.q11, b13 := g.q01, b15 := g.q08, b19 := g.q09, b23 := g.q00, b26 := g.q05, b2a := g.q06, b45 := g.q17, b46 := g.q15, b4c := g.q19, b89 := g.q25, b8a := g.q23, b8c := g.q27 }
  | 4 => { b01 := g.q12, b02 := g.q13, b04 := g.q02, b08 := g.q14, b13 := g.q15, b15 := g.q05, b19 := g.q16, b23 := g.q17, b26 := g.q08, b2a := g.q18, b45 := g.q00, b46 := g.q01, b4c := g.q03, b89 := g.q28, b8a := g.q29, b8c := g.q22 }
  | 5 => { b01 := g.q12, b02 := g.q15, b04 := g.q05, b08 := g.q16, b13 := g.q13, b15 := g.q02, b19 := g.q14, b23 := g.q17, b26 := g.q10, b2a := g.q19, b45 := g.q00, b46 := g.q04, b4c := g.q06, b89 := g.q28, b8a := g.q30, b8c := g.q24 }
  | 6 => { b01 := g.q17, b02 := g.q13, b04 := g.q08, b08 := g.q18, b13 := g.q15, b15 := g.q10, b19 := g.q19, b23 := g.q12, b26 := g.q02, b2a := g.q14, b45 := g.q07, b46 := g.q01, b4c := g.q09, b89 := g.q31, b8a := g.q29, b8c := g.q26 }
  | 7 => { b01 := g.q17, b02 := g.q15, b04 := g.q10, b08 := g.q19, b13 := g.q13, b15 := g.q08, b19 := g.q18, b23 := g.q12, b26 := g.q05, b2a := g.q16, b45 := g.q07, b46 := g.q04, b4c := g.q11, b89 := g.q31, b8a := g.q30, b8c := g.q27 }
  | 8 => { b01 := g.q20, b02 := g.q21, b04 := g.q22, b08 := g.q03, b13 := g.q23, b15 := g.q24, b19 := g.q06, b23 := g.q25, b26 := g.q26, b2a := g.q09, b45 := g.q28, b46 := g.q29, b4c := g.q14, b89 := g.q00, b8a := g.q01, b8c := g.q02 }
  | 9 => { b01 := g.q20, b02 := g.q23, b04 := g.q24, b08 := g.q06, b13 := g.q21, b15 := g.q22, b19 := g.q03, b23 := g.q25, b26 := g.q27, b2a := g.q11, b45 := g.q28, b46 := g.q30, b4c := g.q16, b89 := g.q00, b8a := g.q04, b8c := g.q05 }
  | 10 => { b01 := g.q25, b02 := g.q21, b04 := g.q26, b08 := g.q09, b13 := g.q23, b15 := g.q27, b19 := g.q11, b23 := g.q20, b26 := g.q22, b2a := g.q03, b45 := g.q31, b46 := g.q29, b4c := g.q18, b89 := g.q07, b8a := g.q01, b8c := g.q08 }
  | 11 => { b01 := g.q25, b02 := g.q23, b04 := g.q27, b08 := g.q11, b13 := g.q21, b15 := g.q26, b19 := g.q09, b23 := g.q20, b26 := g.q24, b2a := g.q06, b45 := g.q31, b46 := g.q30, b4c := g.q19, b89 := g.q07, b8a := g.q04, b8c := g.q10 }
  | 12 => { b01 := g.q28, b02 := g.q29, b04 := g.q22, b08 := g.q14, b13 := g.q30, b15 := g.q24, b19 := g.q16, b23 := g.q31, b26 := g.q26, b2a := g.q18, b45 := g.q20, b46 := g.q21, b4c := g.q03, b89 := g.q12, b8a := g.q13, b8c := g.q02 }
  | 13 => { b01 := g.q28, b02 := g.q30, b04 := g.q24, b08 := g.q16, b13 := g.q29, b15 := g.q22, b19 := g.q14, b23 := g.q31, b26 := g.q27, b2a := g.q19, b45 := g.q20, b46 := g.q23, b4c := g.q06, b89 := g.q12, b8a := g.q15, b8c := g.q05 }
  | 14 => { b01 := g.q31, b02 := g.q29, b04 := g.q26, b08 := g.q18, b13 := g.q30, b15 := g.q27, b19 := g.q19, b23 := g.q28, b26 := g.q22, b2a := g.q14, b45 := g.q25, b46 := g.q21, b4c := g.q09, b89 := g.q17, b8a := g.q13, b8c := g.q08 }
  | 15 => { b01 := g.q31, b02 := g.q30, b04 := g.q27, b08 := g.q19, b13 := g.q29, b15 := g.q26, b19 := g.q18, b23 := g.q28, b26 := g.q24, b2a := g.q16, b45 := g.q25, b46 := g.q23, b4c := g.q11, b89 := g.q17, b8a := g.q15, b8c := g.q10 }
  | _ => { b01 := false, b02 := false, b04 := false, b08 := false, b13 := false, b15 := false, b19 := false, b23 := false, b26 := false, b2a := false, b45 := false, b46 := false, b4c := false, b89 := false, b8a := false, b8c := false }

def evalQ3U (q : Q3Bits) : ℤ := q3UngaugedBool q.e01 q.e02 q.e04 q.e13 q.e15 q.e23 q.e26 q.e37 q.e45 q.e46 q.e57 q.e67
def evalQ3G (q : Q3Bits) : ℤ := q3LocalBool q.e01 q.e02 q.e04 q.e13 q.e15 q.e23 q.e26 q.e37 q.e45 q.e46 q.e57 q.e67
def evalQ3Fast (q : Q3Bits) : ℕ := q3Fast q.e01 q.e02 q.e04 q.e13 q.e15 q.e23 q.e26 q.e37 q.e45 q.e46 q.e57 q.e67
def isQ3C6Free (q : Q3Bits) : Bool := q3IsC6FreeBool q.e01 q.e02 q.e04 q.e13 q.e15 q.e23 q.e26 q.e37 q.e45 q.e46 q.e57 q.e67

def evalB2U (b : B2Bits) : ℤ := b2UngaugedBool b.b01 b.b02 b.b04 b.b08 b.b13 b.b15 b.b19 b.b23 b.b26 b.b2a b.b45 b.b46 b.b4c b.b89 b.b8a b.b8c
def evalB2G (b : B2Bits) : ℤ := b2LocalBool b.b01 b.b02 b.b04 b.b08 b.b13 b.b15 b.b19 b.b23 b.b26 b.b2a b.b45 b.b46 b.b4c b.b89 b.b8a b.b8c
def evalB2Fast (b : B2Bits) : ℕ := b2Fast b.b01 b.b02 b.b04 b.b08 b.b13 b.b15 b.b19 b.b23 b.b26 b.b2a b.b45 b.b46 b.b4c b.b89 b.b8a b.b8c
def isB2C6Free (b : B2Bits) : Bool := b2IsC6FreeBool b.b01 b.b02 b.b04 b.b08 b.b13 b.b15 b.b19 b.b23 b.b26 b.b2a b.b45 b.b46 b.b4c b.b89 b.b8a b.b8c

def q4ScoreUngauged (g : Q4Bits) : ℤ :=
  (∑ fk : Fin 8, evalQ3U (extractFacetQ3 fk g)) + (∑ v : Fin 16, evalB2U (extractBallB2 v g))

def q4ScoreGauged (g : Q4Bits) : ℤ :=
  (∑ fk : Fin 8, evalQ3G (extractFacetQ3 fk g)) + (∑ v : Fin 16, evalB2G (extractBallB2 v g))

lemma evalQ3Fast_eq (q : Q3Bits) :
    (evalQ3Fast q : ℤ) = if isQ3C6Free q then evalQ3G q + (Q3_OFF : ℤ) else 0 :=
  q3Fast_eq q.e01 q.e02 q.e04 q.e13 q.e15 q.e23 q.e26 q.e37 q.e45 q.e46 q.e57 q.e67
lemma evalQ3Fast_le_M3 (q : Q3Bits) : evalQ3Fast q ≤ M3_shift :=
  q3Fast_le_M3 q.e01 q.e02 q.e04 q.e13 q.e15 q.e23 q.e26 q.e37 q.e45 q.e46 q.e57 q.e67
lemma evalB2Fast_eq (b : B2Bits) :
    (evalB2Fast b : ℤ) = if isB2C6Free b then evalB2G b + (B2_OFF : ℤ) else 0 :=
  b2Fast_eq b.b01 b.b02 b.b04 b.b08 b.b13 b.b15 b.b19 b.b23 b.b26 b.b2a b.b45 b.b46 b.b4c b.b89 b.b8a b.b8c
lemma evalB2Fast_le_M4 (b : B2Bits) : evalB2Fast b ≤ M4_shift :=
  b2Fast_le_M4 b.b01 b.b02 b.b04 b.b08 b.b13 b.b15 b.b19 b.b23 b.b26 b.b2a b.b45 b.b46 b.b4c b.b89 b.b8a b.b8c

lemma q4ScoreGauged_eq_ungauged (g : Q4Bits) : q4ScoreGauged g = q4ScoreUngauged g := by
  have hL : (lam23 g.q01 g.q02 g.q03 g.q08 g.q13 g.q09 g.q21 g.q14 g.q22 + lam23 g.q01 g.q08 g.q09 g.q02 g.q13 g.q03 g.q21 g.q18 g.q26 + lam23 g.q13 g.q02 g.q14 g.q08 g.q01 g.q18 g.q29 g.q03 g.q22 + lam23 g.q13 g.q08 g.q18 g.q02 g.q01 g.q14 g.q29 g.q09 g.q26 + lam23 g.q21 g.q22 g.q03 g.q26 g.q29 g.q09 g.q01 g.q14 g.q02 + lam23 g.q21 g.q26 g.q09 g.q22 g.q29 g.q03 g.q01 g.q18 g.q08 + lam23 g.q29 g.q22 g.q14 g.q26 g.q21 g.q18 g.q13 g.q03 g.q02 + lam23 g.q29 g.q26 g.q18 g.q22 g.q21 g.q14 g.q13 g.q09 g.q08 + lam23 g.q04 g.q05 g.q06 g.q10 g.q15 g.q11 g.q23 g.q16 g.q24 + lam23 g.q04 g.q10 g.q11 g.q05 g.q15 g.q06 g.q23 g.q19 g.q27 + lam23 g.q15 g.q05 g.q16 g.q10 g.q04 g.q19 g.q30 g.q06 g.q24 + lam23 g.q15 g.q10 g.q19 g.q05 g.q04 g.q16 g.q30 g.q11 g.q27 + lam23 g.q23 g.q24 g.q06 g.q27 g.q30 g.q11 g.q04 g.q16 g.q05 + lam23 g.q23 g.q27 g.q11 g.q24 g.q30 g.q06 g.q04 g.q19 g.q10 + lam23 g.q30 g.q24 g.q16 g.q27 g.q23 g.q19 g.q15 g.q06 g.q05 + lam23 g.q30 g.q27 g.q19 g.q24 g.q23 g.q16 g.q15 g.q11 g.q10 + lam23 g.q00 g.q02 g.q03 g.q05 g.q12 g.q06 g.q20 g.q14 g.q22 + lam23 g.q00 g.q05 g.q06 g.q02 g.q12 g.q03 g.q20 g.q16 g.q24 + lam23 g.q12 g.q02 g.q14 g.q05 g.q00 g.q16 g.q28 g.q03 g.q22 + lam23 g.q12 g.q05 g.q16 g.q02 g.q00 g.q14 g.q28 g.q06 g.q24 + lam23 g.q20 g.q22 g.q03 g.q24 g.q28 g.q06 g.q00 g.q14 g.q02 + lam23 g.q20 g.q24 g.q06 g.q22 g.q28 g.q03 g.q00 g.q16 g.q05 + lam23 g.q28 g.q22 g.q14 g.q24 g.q20 g.q16 g.q12 g.q03 g.q02 + lam23 g.q28 g.q24 g.q16 g.q22 g.q20 g.q14 g.q12 g.q06 g.q05 + lam23 g.q07 g.q08 g.q09 g.q10 g.q17 g.q11 g.q25 g.q18 g.q26 + lam23 g.q07 g.q10 g.q11 g.q08 g.q17 g.q09 g.q25 g.q19 g.q27 + lam23 g.q17 g.q08 g.q18 g.q10 g.q07 g.q19 g.q31 g.q09 g.q26 + lam23 g.q17 g.q10 g.q19 g.q08 g.q07 g.q18 g.q31 g.q11 g.q27 + lam23 g.q25 g.q26 g.q09 g.q27 g.q31 g.q11 g.q07 g.q18 g.q08 + lam23 g.q25 g.q27 g.q11 g.q26 g.q31 g.q09 g.q07 g.q19 g.q10 + lam23 g.q31 g.q26 g.q18 g.q27 g.q25 g.q19 g.q17 g.q09 g.q08 + lam23 g.q31 g.q27 g.q19 g.q26 g.q25 g.q18 g.q17 g.q11 g.q10 + lam23 g.q00 g.q01 g.q03 g.q04 g.q07 g.q06 g.q20 g.q09 g.q21 + lam23 g.q00 g.q04 g.q06 g.q01 g.q07 g.q03 g.q20 g.q11 g.q23 + lam23 g.q07 g.q01 g.q09 g.q04 g.q00 g.q11 g.q25 g.q03 g.q21 + lam23 g.q07 g.q04 g.q11 g.q01 g.q00 g.q09 g.q25 g.q06 g.q23 + lam23 g.q20 g.q21 g.q03 g.q23 g.q25 g.q06 g.q00 g.q09 g.q01 + lam23 g.q20 g.q23 g.q06 g.q21 g.q25 g.q03 g.q00 g.q11 g.q04 + lam23 g.q25 g.q21 g.q09 g.q23 g.q20 g.q11 g.q07 g.q03 g.q01 + lam23 g.q25 g.q23 g.q11 g.q21 g.q20 g.q09 g.q07 g.q06 g.q04 + lam23 g.q12 g.q13 g.q14 g.q15 g.q17 g.q16 g.q28 g.q18 g.q29 + lam23 g.q12 g.q15 g.q16 g.q13 g.q17 g.q14 g.q28 g.q19 g.q30 + lam23 g.q17 g.q13 g.q18 g.q15 g.q12 g.q19 g.q31 g.q14 g.q29 + lam23 g.q17 g.q15 g.q19 g.q13 g.q12 g.q18 g.q31 g.q16 g.q30 + lam23 g.q28 g.q29 g.q14 g.q30 g.q31 g.q16 g.q12 g.q18 g.q13 + lam23 g.q28 g.q30 g.q16 g.q29 g.q31 g.q14 g.q12 g.q19 g.q15 + lam23 g.q31 g.q29 g.q18 g.q30 g.q28 g.q19 g.q17 g.q14 g.q13 + lam23 g.q31 g.q30 g.q19 g.q29 g.q28 g.q18 g.q17 g.q16 g.q15 + lam23 g.q00 g.q01 g.q02 g.q04 g.q07 g.q05 g.q12 g.q08 g.q13 + lam23 g.q00 g.q04 g.q05 g.q01 g.q07 g.q02 g.q12 g.q10 g.q15 + lam23 g.q07 g.q01 g.q08 g.q04 g.q00 g.q10 g.q17 g.q02 g.q13 + lam23 g.q07 g.q04 g.q10 g.q01 g.q00 g.q08 g.q17 g.q05 g.q15 + lam23 g.q12 g.q13 g.q02 g.q15 g.q17 g.q05 g.q00 g.q08 g.q01 + lam23 g.q12 g.q15 g.q05 g.q13 g.q17 g.q02 g.q00 g.q10 g.q04 + lam23 g.q17 g.q13 g.q08 g.q15 g.q12 g.q10 g.q07 g.q02 g.q01 + lam23 g.q17 g.q15 g.q10 g.q13 g.q12 g.q08 g.q07 g.q05 g.q04 + lam23 g.q20 g.q21 g.q22 g.q23 g.q25 g.q24 g.q28 g.q26 g.q29 + lam23 g.q20 g.q23 g.q24 g.q21 g.q25 g.q22 g.q28 g.q27 g.q30 + lam23 g.q25 g.q21 g.q26 g.q23 g.q20 g.q27 g.q31 g.q22 g.q29 + lam23 g.q25 g.q23 g.q27 g.q21 g.q20 g.q26 g.q31 g.q24 g.q30 + lam23 g.q28 g.q29 g.q22 g.q30 g.q31 g.q24 g.q20 g.q26 g.q21 + lam23 g.q28 g.q30 g.q24 g.q29 g.q31 g.q22 g.q20 g.q27 g.q23 + lam23 g.q31 g.q29 g.q26 g.q30 g.q28 g.q27 g.q25 g.q22 g.q21 + lam23 g.q31 g.q30 g.q27 g.q29 g.q28 g.q26 g.q25 g.q24 g.q23) = (lam23 g.q01 g.q02 g.q03 g.q08 g.q13 g.q09 g.q21 g.q14 g.q22 + lam23 g.q00 g.q02 g.q03 g.q05 g.q12 g.q06 g.q20 g.q14 g.q22 + lam23 g.q00 g.q01 g.q03 g.q04 g.q07 g.q06 g.q20 g.q09 g.q21 + lam23 g.q00 g.q01 g.q02 g.q04 g.q07 g.q05 g.q12 g.q08 g.q13 + lam23 g.q04 g.q05 g.q06 g.q10 g.q15 g.q11 g.q23 g.q16 g.q24 + lam23 g.q00 g.q05 g.q06 g.q02 g.q12 g.q03 g.q20 g.q16 g.q24 + lam23 g.q00 g.q04 g.q06 g.q01 g.q07 g.q03 g.q20 g.q11 g.q23 + lam23 g.q00 g.q04 g.q05 g.q01 g.q07 g.q02 g.q12 g.q10 g.q15 + lam23 g.q01 g.q08 g.q09 g.q02 g.q13 g.q03 g.q21 g.q18 g.q26 + lam23 g.q07 g.q08 g.q09 g.q10 g.q17 g.q11 g.q25 g.q18 g.q26 + lam23 g.q07 g.q01 g.q09 g.q04 g.q00 g.q11 g.q25 g.q03 g.q21 + lam23 g.q07 g.q01 g.q08 g.q04 g.q00 g.q10 g.q17 g.q02 g.q13 + lam23 g.q04 g.q10 g.q11 g.q05 g.q15 g.q06 g.q23 g.q19 g.q27 + lam23 g.q07 g.q10 g.q11 g.q08 g.q17 g.q09 g.q25 g.q19 g.q27 + lam23 g.q07 g.q04 g.q11 g.q01 g.q00 g.q09 g.q25 g.q06 g.q23 + lam23 g.q07 g.q04 g.q10 g.q01 g.q00 g.q08 g.q17 g.q05 g.q15 + lam23 g.q13 g.q02 g.q14 g.q08 g.q01 g.q18 g.q29 g.q03 g.q22 + lam23 g.q12 g.q02 g.q14 g.q05 g.q00 g.q16 g.q28 g.q03 g.q22 + lam23 g.q12 g.q13 g.q14 g.q15 g.q17 g.q16 g.q28 g.q18 g.q29 + lam23 g.q12 g.q13 g.q02 g.q15 g.q17 g.q05 g.q00 g.q08 g.q01 + lam23 g.q15 g.q05 g.q16 g.q10 g.q04 g.q19 g.q30 g.q06 g.q24 + lam23 g.q12 g.q05 g.q16 g.q02 g.q00 g.q14 g.q28 g.q06 g.q24 + lam23 g.q12 g.q15 g.q16 g.q13 g.q17 g.q14 g.q28 g.q19 g.q30 + lam23 g.q12 g.q15 g.q05 g.q13 g.q17 g.q02 g.q00 g.q10 g.q04 + lam23 g.q13 g.q08 g.q18 g.q02 g.q01 g.q14 g.q29 g.q09 g.q26 + lam23 g.q17 g.q08 g.q18 g.q10 g.q07 g.q19 g.q31 g.q09 g.q26 + lam23 g.q17 g.q13 g.q18 g.q15 g.q12 g.q19 g.q31 g.q14 g.q29 + lam23 g.q17 g.q13 g.q08 g.q15 g.q12 g.q10 g.q07 g.q02 g.q01 + lam23 g.q15 g.q10 g.q19 g.q05 g.q04 g.q16 g.q30 g.q11 g.q27 + lam23 g.q17 g.q10 g.q19 g.q08 g.q07 g.q18 g.q31 g.q11 g.q27 + lam23 g.q17 g.q15 g.q19 g.q13 g.q12 g.q18 g.q31 g.q16 g.q30 + lam23 g.q17 g.q15 g.q10 g.q13 g.q12 g.q08 g.q07 g.q05 g.q04 + lam23 g.q21 g.q22 g.q03 g.q26 g.q29 g.q09 g.q01 g.q14 g.q02 + lam23 g.q20 g.q22 g.q03 g.q24 g.q28 g.q06 g.q00 g.q14 g.q02 + lam23 g.q20 g.q21 g.q03 g.q23 g.q25 g.q06 g.q00 g.q09 g.q01 + lam23 g.q20 g.q21 g.q22 g.q23 g.q25 g.q24 g.q28 g.q26 g.q29 + lam23 g.q23 g.q24 g.q06 g.q27 g.q30 g.q11 g.q04 g.q16 g.q05 + lam23 g.q20 g.q24 g.q06 g.q22 g.q28 g.q03 g.q00 g.q16 g.q05 + lam23 g.q20 g.q23 g.q06 g.q21 g.q25 g.q03 g.q00 g.q11 g.q04 + lam23 g.q20 g.q23 g.q24 g.q21 g.q25 g.q22 g.q28 g.q27 g.q30 + lam23 g.q21 g.q26 g.q09 g.q22 g.q29 g.q03 g.q01 g.q18 g.q08 + lam23 g.q25 g.q26 g.q09 g.q27 g.q31 g.q11 g.q07 g.q18 g.q08 + lam23 g.q25 g.q21 g.q09 g.q23 g.q20 g.q11 g.q07 g.q03 g.q01 + lam23 g.q25 g.q21 g.q26 g.q23 g.q20 g.q27 g.q31 g.q22 g.q29 + lam23 g.q23 g.q27 g.q11 g.q24 g.q30 g.q06 g.q04 g.q19 g.q10 + lam23 g.q25 g.q27 g.q11 g.q26 g.q31 g.q09 g.q07 g.q19 g.q10 + lam23 g.q25 g.q23 g.q11 g.q21 g.q20 g.q09 g.q07 g.q06 g.q04 + lam23 g.q25 g.q23 g.q27 g.q21 g.q20 g.q26 g.q31 g.q24 g.q30 + lam23 g.q29 g.q22 g.q14 g.q26 g.q21 g.q18 g.q13 g.q03 g.q02 + lam23 g.q28 g.q22 g.q14 g.q24 g.q20 g.q16 g.q12 g.q03 g.q02 + lam23 g.q28 g.q29 g.q14 g.q30 g.q31 g.q16 g.q12 g.q18 g.q13 + lam23 g.q28 g.q29 g.q22 g.q30 g.q31 g.q24 g.q20 g.q26 g.q21 + lam23 g.q30 g.q24 g.q16 g.q27 g.q23 g.q19 g.q15 g.q06 g.q05 + lam23 g.q28 g.q24 g.q16 g.q22 g.q20 g.q14 g.q12 g.q06 g.q05 + lam23 g.q28 g.q30 g.q16 g.q29 g.q31 g.q14 g.q12 g.q19 g.q15 + lam23 g.q28 g.q30 g.q24 g.q29 g.q31 g.q22 g.q20 g.q27 g.q23 + lam23 g.q29 g.q26 g.q18 g.q22 g.q21 g.q14 g.q13 g.q09 g.q08 + lam23 g.q31 g.q26 g.q18 g.q27 g.q25 g.q19 g.q17 g.q09 g.q08 + lam23 g.q31 g.q29 g.q18 g.q30 g.q28 g.q19 g.q17 g.q14 g.q13 + lam23 g.q31 g.q29 g.q26 g.q30 g.q28 g.q27 g.q25 g.q22 g.q21 + lam23 g.q30 g.q27 g.q19 g.q24 g.q23 g.q16 g.q15 g.q11 g.q10 + lam23 g.q31 g.q27 g.q19 g.q26 g.q25 g.q18 g.q17 g.q11 g.q10 + lam23 g.q31 g.q30 g.q19 g.q29 g.q28 g.q18 g.q17 g.q16 g.q15 + lam23 g.q31 g.q30 g.q27 g.q29 g.q28 g.q26 g.q25 g.q24 g.q23) := by ring
  have hP1 : (phiFlip g.q00 (mkFlag g.q01 g.q04 g.q07) (mkFlag g.q02 g.q05 g.q12) (mkFlag g.q03 g.q06 g.q20) + phiFlip g.q01 (mkFlag g.q00 g.q07 g.q04) (mkFlag g.q02 g.q08 g.q13) (mkFlag g.q03 g.q09 g.q21) + phiFlip g.q02 (mkFlag g.q00 g.q12 g.q05) (mkFlag g.q01 g.q13 g.q08) (mkFlag g.q03 g.q14 g.q22) + phiFlip g.q03 (mkFlag g.q00 g.q20 g.q06) (mkFlag g.q01 g.q21 g.q09) (mkFlag g.q02 g.q22 g.q14) + phiFlip g.q00 (mkFlag g.q04 g.q01 g.q07) (mkFlag g.q05 g.q02 g.q12) (mkFlag g.q06 g.q03 g.q20) + phiFlip g.q04 (mkFlag g.q00 g.q07 g.q01) (mkFlag g.q05 g.q10 g.q15) (mkFlag g.q06 g.q11 g.q23) + phiFlip g.q05 (mkFlag g.q00 g.q12 g.q02) (mkFlag g.q04 g.q15 g.q10) (mkFlag g.q06 g.q16 g.q24) + phiFlip g.q06 (mkFlag g.q00 g.q20 g.q03) (mkFlag g.q04 g.q23 g.q11) (mkFlag g.q05 g.q24 g.q16) + phiFlip g.q07 (mkFlag g.q01 g.q04 g.q00) (mkFlag g.q08 g.q10 g.q17) (mkFlag g.q09 g.q11 g.q25) + phiFlip g.q01 (mkFlag g.q07 g.q00 g.q04) (mkFlag g.q08 g.q02 g.q13) (mkFlag g.q09 g.q03 g.q21) + phiFlip g.q08 (mkFlag g.q07 g.q17 g.q10) (mkFlag g.q01 g.q13 g.q02) (mkFlag g.q09 g.q18 g.q26) + phiFlip g.q09 (mkFlag g.q07 g.q25 g.q11) (mkFlag g.q01 g.q21 g.q03) (mkFlag g.q08 g.q26 g.q18) + phiFlip g.q07 (mkFlag g.q04 g.q01 g.q00) (mkFlag g.q10 g.q08 g.q17) (mkFlag g.q11 g.q09 g.q25) + phiFlip g.q04 (mkFlag g.q07 g.q00 g.q01) (mkFlag g.q10 g.q05 g.q15) (mkFlag g.q11 g.q06 g.q23) + phiFlip g.q10 (mkFlag g.q07 g.q17 g.q08) (mkFlag g.q04 g.q15 g.q05) (mkFlag g.q11 g.q19 g.q27) + phiFlip g.q11 (mkFlag g.q07 g.q25 g.q09) (mkFlag g.q04 g.q23 g.q06) (mkFlag g.q10 g.q27 g.q19) + phiFlip g.q12 (mkFlag g.q13 g.q15 g.q17) (mkFlag g.q02 g.q05 g.q00) (mkFlag g.q14 g.q16 g.q28) + phiFlip g.q13 (mkFlag g.q12 g.q17 g.q15) (mkFlag g.q02 g.q08 g.q01) (mkFlag g.q14 g.q18 g.q29) + phiFlip g.q02 (mkFlag g.q12 g.q00 g.q05) (mkFlag g.q13 g.q01 g.q08) (mkFlag g.q14 g.q03 g.q22) + phiFlip g.q14 (mkFlag g.q12 g.q28 g.q16) (mkFlag g.q13 g.q29 g.q18) (mkFlag g.q02 g.q22 g.q03) + phiFlip g.q12 (mkFlag g.q15 g.q13 g.q17) (mkFlag g.q05 g.q02 g.q00) (mkFlag g.q16 g.q14 g.q28) + phiFlip g.q15 (mkFlag g.q12 g.q17 g.q13) (mkFlag g.q05 g.q10 g.q04) (mkFlag g.q16 g.q19 g.q30) + phiFlip g.q05 (mkFlag g.q12 g.q00 g.q02) (mkFlag g.q15 g.q04 g.q10) (mkFlag g.q16 g.q06 g.q24) + phiFlip g.q16 (mkFlag g.q12 g.q28 g.q14) (mkFlag g.q15 g.q30 g.q19) (mkFlag g.q05 g.q24 g.q06) + phiFlip g.q17 (mkFlag g.q13 g.q15 g.q12) (mkFlag g.q08 g.q10 g.q07) (mkFlag g.q18 g.q19 g.q31) + phiFlip g.q13 (mkFlag g.q17 g.q12 g.q15) (mkFlag g.q08 g.q02 g.q01) (mkFlag g.q18 g.q14 g.q29) + phiFlip g.q08 (mkFlag g.q17 g.q07 g.q10) (mkFlag g.q13 g.q01 g.q02) (mkFlag g.q18 g.q09 g.q26) + phiFlip g.q18 (mkFlag g.q17 g.q31 g.q19) (mkFlag g.q13 g.q29 g.q14) (mkFlag g.q08 g.q26 g.q09) + phiFlip g.q17 (mkFlag g.q15 g.q13 g.q12) (mkFlag g.q10 g.q08 g.q07) (mkFlag g.q19 g.q18 g.q31) + phiFlip g.q15 (mkFlag g.q17 g.q12 g.q13) (mkFlag g.q10 g.q05 g.q04) (mkFlag g.q19 g.q16 g.q30) + phiFlip g.q10 (mkFlag g.q17 g.q07 g.q08) (mkFlag g.q15 g.q04 g.q05) (mkFlag g.q19 g.q11 g.q27) + phiFlip g.q19 (mkFlag g.q17 g.q31 g.q18) (mkFlag g.q15 g.q30 g.q16) (mkFlag g.q10 g.q27 g.q11) + phiFlip g.q20 (mkFlag g.q21 g.q23 g.q25) (mkFlag g.q22 g.q24 g.q28) (mkFlag g.q03 g.q06 g.q00) + phiFlip g.q21 (mkFlag g.q20 g.q25 g.q23) (mkFlag g.q22 g.q26 g.q29) (mkFlag g.q03 g.q09 g.q01) + phiFlip g.q22 (mkFlag g.q20 g.q28 g.q24) (mkFlag g.q21 g.q29 g.q26) (mkFlag g.q03 g.q14 g.q02) + phiFlip g.q03 (mkFlag g.q20 g.q00 g.q06) (mkFlag g.q21 g.q01 g.q09) (mkFlag g.q22 g.q02 g.q14) + phiFlip g.q20 (mkFlag g.q23 g.q21 g.q25) (mkFlag g.q24 g.q22 g.q28) (mkFlag g.q06 g.q03 g.q00) + phiFlip g.q23 (mkFlag g.q20 g.q25 g.q21) (mkFlag g.q24 g.q27 g.q30) (mkFlag g.q06 g.q11 g.q04) + phiFlip g.q24 (mkFlag g.q20 g.q28 g.q22) (mkFlag g.q23 g.q30 g.q27) (mkFlag g.q06 g.q16 g.q05) + phiFlip g.q06 (mkFlag g.q20 g.q00 g.q03) (mkFlag g.q23 g.q04 g.q11) (mkFlag g.q24 g.q05 g.q16) + phiFlip g.q25 (mkFlag g.q21 g.q23 g.q20) (mkFlag g.q26 g.q27 g.q31) (mkFlag g.q09 g.q11 g.q07) + phiFlip g.q21 (mkFlag g.q25 g.q20 g.q23) (mkFlag g.q26 g.q22 g.q29) (mkFlag g.q09 g.q03 g.q01) + phiFlip g.q26 (mkFlag g.q25 g.q31 g.q27) (mkFlag g.q21 g.q29 g.q22) (mkFlag g.q09 g.q18 g.q08) + phiFlip g.q09 (mkFlag g.q25 g.q07 g.q11) (mkFlag g.q21 g.q01 g.q03) (mkFlag g.q26 g.q08 g.q18) + phiFlip g.q25 (mkFlag g.q23 g.q21 g.q20) (mkFlag g.q27 g.q26 g.q31) (mkFlag g.q11 g.q09 g.q07) + phiFlip g.q23 (mkFlag g.q25 g.q20 g.q21) (mkFlag g.q27 g.q24 g.q30) (mkFlag g.q11 g.q06 g.q04) + phiFlip g.q27 (mkFlag g.q25 g.q31 g.q26) (mkFlag g.q23 g.q30 g.q24) (mkFlag g.q11 g.q19 g.q10) + phiFlip g.q11 (mkFlag g.q25 g.q07 g.q09) (mkFlag g.q23 g.q04 g.q06) (mkFlag g.q27 g.q10 g.q19) + phiFlip g.q28 (mkFlag g.q29 g.q30 g.q31) (mkFlag g.q22 g.q24 g.q20) (mkFlag g.q14 g.q16 g.q12) + phiFlip g.q29 (mkFlag g.q28 g.q31 g.q30) (mkFlag g.q22 g.q26 g.q21) (mkFlag g.q14 g.q18 g.q13) + phiFlip g.q22 (mkFlag g.q28 g.q20 g.q24) (mkFlag g.q29 g.q21 g.q26) (mkFlag g.q14 g.q03 g.q02) + phiFlip g.q14 (mkFlag g.q28 g.q12 g.q16) (mkFlag g.q29 g.q13 g.q18) (mkFlag g.q22 g.q02 g.q03) + phiFlip g.q28 (mkFlag g.q30 g.q29 g.q31) (mkFlag g.q24 g.q22 g.q20) (mkFlag g.q16 g.q14 g.q12) + phiFlip g.q30 (mkFlag g.q28 g.q31 g.q29) (mkFlag g.q24 g.q27 g.q23) (mkFlag g.q16 g.q19 g.q15) + phiFlip g.q24 (mkFlag g.q28 g.q20 g.q22) (mkFlag g.q30 g.q23 g.q27) (mkFlag g.q16 g.q06 g.q05) + phiFlip g.q16 (mkFlag g.q28 g.q12 g.q14) (mkFlag g.q30 g.q15 g.q19) (mkFlag g.q24 g.q05 g.q06) + phiFlip g.q31 (mkFlag g.q29 g.q30 g.q28) (mkFlag g.q26 g.q27 g.q25) (mkFlag g.q18 g.q19 g.q17) + phiFlip g.q29 (mkFlag g.q31 g.q28 g.q30) (mkFlag g.q26 g.q22 g.q21) (mkFlag g.q18 g.q14 g.q13) + phiFlip g.q26 (mkFlag g.q31 g.q25 g.q27) (mkFlag g.q29 g.q21 g.q22) (mkFlag g.q18 g.q09 g.q08) + phiFlip g.q18 (mkFlag g.q31 g.q17 g.q19) (mkFlag g.q29 g.q13 g.q14) (mkFlag g.q26 g.q08 g.q09) + phiFlip g.q31 (mkFlag g.q30 g.q29 g.q28) (mkFlag g.q27 g.q26 g.q25) (mkFlag g.q19 g.q18 g.q17) + phiFlip g.q30 (mkFlag g.q31 g.q28 g.q29) (mkFlag g.q27 g.q24 g.q23) (mkFlag g.q19 g.q16 g.q15) + phiFlip g.q27 (mkFlag g.q31 g.q25 g.q26) (mkFlag g.q30 g.q23 g.q24) (mkFlag g.q19 g.q11 g.q10) + phiFlip g.q19 (mkFlag g.q31 g.q17 g.q18) (mkFlag g.q30 g.q15 g.q16) (mkFlag g.q27 g.q10 g.q11)) = 0 := by
    have hp_1_0 : phiFlip g.q00 (mkFlag g.q04 g.q01 g.q07) (mkFlag g.q05 g.q02 g.q12) (mkFlag g.q06 g.q03 g.q20) = -(phiFlip g.q00 (mkFlag g.q01 g.q04 g.q07) (mkFlag g.q02 g.q05 g.q12) (mkFlag g.q03 g.q06 g.q20)) := by
      have h := phiFlip_antisymm g.q00 (mkFlag g.q01 g.q04 g.q07) (mkFlag g.q02 g.q05 g.q12) (mkFlag g.q03 g.q06 g.q20); simp only [flipF_mkFlag] at h; linarith
    have hp_2_1 : phiFlip g.q01 (mkFlag g.q07 g.q00 g.q04) (mkFlag g.q08 g.q02 g.q13) (mkFlag g.q09 g.q03 g.q21) = -(phiFlip g.q01 (mkFlag g.q00 g.q07 g.q04) (mkFlag g.q02 g.q08 g.q13) (mkFlag g.q03 g.q09 g.q21)) := by
      have h := phiFlip_antisymm g.q01 (mkFlag g.q00 g.q07 g.q04) (mkFlag g.q02 g.q08 g.q13) (mkFlag g.q03 g.q09 g.q21); simp only [flipF_mkFlag] at h; linarith
    have hp_3_0 : phiFlip g.q07 (mkFlag g.q04 g.q01 g.q00) (mkFlag g.q10 g.q08 g.q17) (mkFlag g.q11 g.q09 g.q25) = -(phiFlip g.q07 (mkFlag g.q01 g.q04 g.q00) (mkFlag g.q08 g.q10 g.q17) (mkFlag g.q09 g.q11 g.q25)) := by
      have h := phiFlip_antisymm g.q07 (mkFlag g.q01 g.q04 g.q00) (mkFlag g.q08 g.q10 g.q17) (mkFlag g.q09 g.q11 g.q25); simp only [flipF_mkFlag] at h; linarith
    have hp_3_1 : phiFlip g.q04 (mkFlag g.q07 g.q00 g.q01) (mkFlag g.q10 g.q05 g.q15) (mkFlag g.q11 g.q06 g.q23) = -(phiFlip g.q04 (mkFlag g.q00 g.q07 g.q01) (mkFlag g.q05 g.q10 g.q15) (mkFlag g.q06 g.q11 g.q23)) := by
      have h := phiFlip_antisymm g.q04 (mkFlag g.q00 g.q07 g.q01) (mkFlag g.q05 g.q10 g.q15) (mkFlag g.q06 g.q11 g.q23); simp only [flipF_mkFlag] at h; linarith
    have hp_4_2 : phiFlip g.q02 (mkFlag g.q12 g.q00 g.q05) (mkFlag g.q13 g.q01 g.q08) (mkFlag g.q14 g.q03 g.q22) = -(phiFlip g.q02 (mkFlag g.q00 g.q12 g.q05) (mkFlag g.q01 g.q13 g.q08) (mkFlag g.q03 g.q14 g.q22)) := by
      have h := phiFlip_antisymm g.q02 (mkFlag g.q00 g.q12 g.q05) (mkFlag g.q01 g.q13 g.q08) (mkFlag g.q03 g.q14 g.q22); simp only [flipF_mkFlag] at h; linarith
    have hp_5_0 : phiFlip g.q12 (mkFlag g.q15 g.q13 g.q17) (mkFlag g.q05 g.q02 g.q00) (mkFlag g.q16 g.q14 g.q28) = -(phiFlip g.q12 (mkFlag g.q13 g.q15 g.q17) (mkFlag g.q02 g.q05 g.q00) (mkFlag g.q14 g.q16 g.q28)) := by
      have h := phiFlip_antisymm g.q12 (mkFlag g.q13 g.q15 g.q17) (mkFlag g.q02 g.q05 g.q00) (mkFlag g.q14 g.q16 g.q28); simp only [flipF_mkFlag] at h; linarith
    have hp_5_2 : phiFlip g.q05 (mkFlag g.q12 g.q00 g.q02) (mkFlag g.q15 g.q04 g.q10) (mkFlag g.q16 g.q06 g.q24) = -(phiFlip g.q05 (mkFlag g.q00 g.q12 g.q02) (mkFlag g.q04 g.q15 g.q10) (mkFlag g.q06 g.q16 g.q24)) := by
      have h := phiFlip_antisymm g.q05 (mkFlag g.q00 g.q12 g.q02) (mkFlag g.q04 g.q15 g.q10) (mkFlag g.q06 g.q16 g.q24); simp only [flipF_mkFlag] at h; linarith
    have hp_6_1 : phiFlip g.q13 (mkFlag g.q17 g.q12 g.q15) (mkFlag g.q08 g.q02 g.q01) (mkFlag g.q18 g.q14 g.q29) = -(phiFlip g.q13 (mkFlag g.q12 g.q17 g.q15) (mkFlag g.q02 g.q08 g.q01) (mkFlag g.q14 g.q18 g.q29)) := by
      have h := phiFlip_antisymm g.q13 (mkFlag g.q12 g.q17 g.q15) (mkFlag g.q02 g.q08 g.q01) (mkFlag g.q14 g.q18 g.q29); simp only [flipF_mkFlag] at h; linarith
    have hp_6_2 : phiFlip g.q08 (mkFlag g.q17 g.q07 g.q10) (mkFlag g.q13 g.q01 g.q02) (mkFlag g.q18 g.q09 g.q26) = -(phiFlip g.q08 (mkFlag g.q07 g.q17 g.q10) (mkFlag g.q01 g.q13 g.q02) (mkFlag g.q09 g.q18 g.q26)) := by
      have h := phiFlip_antisymm g.q08 (mkFlag g.q07 g.q17 g.q10) (mkFlag g.q01 g.q13 g.q02) (mkFlag g.q09 g.q18 g.q26); simp only [flipF_mkFlag] at h; linarith
    have hp_7_0 : phiFlip g.q17 (mkFlag g.q15 g.q13 g.q12) (mkFlag g.q10 g.q08 g.q07) (mkFlag g.q19 g.q18 g.q31) = -(phiFlip g.q17 (mkFlag g.q13 g.q15 g.q12) (mkFlag g.q08 g.q10 g.q07) (mkFlag g.q18 g.q19 g.q31)) := by
      have h := phiFlip_antisymm g.q17 (mkFlag g.q13 g.q15 g.q12) (mkFlag g.q08 g.q10 g.q07) (mkFlag g.q18 g.q19 g.q31); simp only [flipF_mkFlag] at h; linarith
    have hp_7_1 : phiFlip g.q15 (mkFlag g.q17 g.q12 g.q13) (mkFlag g.q10 g.q05 g.q04) (mkFlag g.q19 g.q16 g.q30) = -(phiFlip g.q15 (mkFlag g.q12 g.q17 g.q13) (mkFlag g.q05 g.q10 g.q04) (mkFlag g.q16 g.q19 g.q30)) := by
      have h := phiFlip_antisymm g.q15 (mkFlag g.q12 g.q17 g.q13) (mkFlag g.q05 g.q10 g.q04) (mkFlag g.q16 g.q19 g.q30); simp only [flipF_mkFlag] at h; linarith
    have hp_7_2 : phiFlip g.q10 (mkFlag g.q17 g.q07 g.q08) (mkFlag g.q15 g.q04 g.q05) (mkFlag g.q19 g.q11 g.q27) = -(phiFlip g.q10 (mkFlag g.q07 g.q17 g.q08) (mkFlag g.q04 g.q15 g.q05) (mkFlag g.q11 g.q19 g.q27)) := by
      have h := phiFlip_antisymm g.q10 (mkFlag g.q07 g.q17 g.q08) (mkFlag g.q04 g.q15 g.q05) (mkFlag g.q11 g.q19 g.q27); simp only [flipF_mkFlag] at h; linarith
    have hp_8_3 : phiFlip g.q03 (mkFlag g.q20 g.q00 g.q06) (mkFlag g.q21 g.q01 g.q09) (mkFlag g.q22 g.q02 g.q14) = -(phiFlip g.q03 (mkFlag g.q00 g.q20 g.q06) (mkFlag g.q01 g.q21 g.q09) (mkFlag g.q02 g.q22 g.q14)) := by
      have h := phiFlip_antisymm g.q03 (mkFlag g.q00 g.q20 g.q06) (mkFlag g.q01 g.q21 g.q09) (mkFlag g.q02 g.q22 g.q14); simp only [flipF_mkFlag] at h; linarith
    have hp_9_0 : phiFlip g.q20 (mkFlag g.q23 g.q21 g.q25) (mkFlag g.q24 g.q22 g.q28) (mkFlag g.q06 g.q03 g.q00) = -(phiFlip g.q20 (mkFlag g.q21 g.q23 g.q25) (mkFlag g.q22 g.q24 g.q28) (mkFlag g.q03 g.q06 g.q00)) := by
      have h := phiFlip_antisymm g.q20 (mkFlag g.q21 g.q23 g.q25) (mkFlag g.q22 g.q24 g.q28) (mkFlag g.q03 g.q06 g.q00); simp only [flipF_mkFlag] at h; linarith
    have hp_9_3 : phiFlip g.q06 (mkFlag g.q20 g.q00 g.q03) (mkFlag g.q23 g.q04 g.q11) (mkFlag g.q24 g.q05 g.q16) = -(phiFlip g.q06 (mkFlag g.q00 g.q20 g.q03) (mkFlag g.q04 g.q23 g.q11) (mkFlag g.q05 g.q24 g.q16)) := by
      have h := phiFlip_antisymm g.q06 (mkFlag g.q00 g.q20 g.q03) (mkFlag g.q04 g.q23 g.q11) (mkFlag g.q05 g.q24 g.q16); simp only [flipF_mkFlag] at h; linarith
    have hp_10_1 : phiFlip g.q21 (mkFlag g.q25 g.q20 g.q23) (mkFlag g.q26 g.q22 g.q29) (mkFlag g.q09 g.q03 g.q01) = -(phiFlip g.q21 (mkFlag g.q20 g.q25 g.q23) (mkFlag g.q22 g.q26 g.q29) (mkFlag g.q03 g.q09 g.q01)) := by
      have h := phiFlip_antisymm g.q21 (mkFlag g.q20 g.q25 g.q23) (mkFlag g.q22 g.q26 g.q29) (mkFlag g.q03 g.q09 g.q01); simp only [flipF_mkFlag] at h; linarith
    have hp_10_3 : phiFlip g.q09 (mkFlag g.q25 g.q07 g.q11) (mkFlag g.q21 g.q01 g.q03) (mkFlag g.q26 g.q08 g.q18) = -(phiFlip g.q09 (mkFlag g.q07 g.q25 g.q11) (mkFlag g.q01 g.q21 g.q03) (mkFlag g.q08 g.q26 g.q18)) := by
      have h := phiFlip_antisymm g.q09 (mkFlag g.q07 g.q25 g.q11) (mkFlag g.q01 g.q21 g.q03) (mkFlag g.q08 g.q26 g.q18); simp only [flipF_mkFlag] at h; linarith
    have hp_11_0 : phiFlip g.q25 (mkFlag g.q23 g.q21 g.q20) (mkFlag g.q27 g.q26 g.q31) (mkFlag g.q11 g.q09 g.q07) = -(phiFlip g.q25 (mkFlag g.q21 g.q23 g.q20) (mkFlag g.q26 g.q27 g.q31) (mkFlag g.q09 g.q11 g.q07)) := by
      have h := phiFlip_antisymm g.q25 (mkFlag g.q21 g.q23 g.q20) (mkFlag g.q26 g.q27 g.q31) (mkFlag g.q09 g.q11 g.q07); simp only [flipF_mkFlag] at h; linarith
    have hp_11_1 : phiFlip g.q23 (mkFlag g.q25 g.q20 g.q21) (mkFlag g.q27 g.q24 g.q30) (mkFlag g.q11 g.q06 g.q04) = -(phiFlip g.q23 (mkFlag g.q20 g.q25 g.q21) (mkFlag g.q24 g.q27 g.q30) (mkFlag g.q06 g.q11 g.q04)) := by
      have h := phiFlip_antisymm g.q23 (mkFlag g.q20 g.q25 g.q21) (mkFlag g.q24 g.q27 g.q30) (mkFlag g.q06 g.q11 g.q04); simp only [flipF_mkFlag] at h; linarith
    have hp_11_3 : phiFlip g.q11 (mkFlag g.q25 g.q07 g.q09) (mkFlag g.q23 g.q04 g.q06) (mkFlag g.q27 g.q10 g.q19) = -(phiFlip g.q11 (mkFlag g.q07 g.q25 g.q09) (mkFlag g.q04 g.q23 g.q06) (mkFlag g.q10 g.q27 g.q19)) := by
      have h := phiFlip_antisymm g.q11 (mkFlag g.q07 g.q25 g.q09) (mkFlag g.q04 g.q23 g.q06) (mkFlag g.q10 g.q27 g.q19); simp only [flipF_mkFlag] at h; linarith
    have hp_12_2 : phiFlip g.q22 (mkFlag g.q28 g.q20 g.q24) (mkFlag g.q29 g.q21 g.q26) (mkFlag g.q14 g.q03 g.q02) = -(phiFlip g.q22 (mkFlag g.q20 g.q28 g.q24) (mkFlag g.q21 g.q29 g.q26) (mkFlag g.q03 g.q14 g.q02)) := by
      have h := phiFlip_antisymm g.q22 (mkFlag g.q20 g.q28 g.q24) (mkFlag g.q21 g.q29 g.q26) (mkFlag g.q03 g.q14 g.q02); simp only [flipF_mkFlag] at h; linarith
    have hp_12_3 : phiFlip g.q14 (mkFlag g.q28 g.q12 g.q16) (mkFlag g.q29 g.q13 g.q18) (mkFlag g.q22 g.q02 g.q03) = -(phiFlip g.q14 (mkFlag g.q12 g.q28 g.q16) (mkFlag g.q13 g.q29 g.q18) (mkFlag g.q02 g.q22 g.q03)) := by
      have h := phiFlip_antisymm g.q14 (mkFlag g.q12 g.q28 g.q16) (mkFlag g.q13 g.q29 g.q18) (mkFlag g.q02 g.q22 g.q03); simp only [flipF_mkFlag] at h; linarith
    have hp_13_0 : phiFlip g.q28 (mkFlag g.q30 g.q29 g.q31) (mkFlag g.q24 g.q22 g.q20) (mkFlag g.q16 g.q14 g.q12) = -(phiFlip g.q28 (mkFlag g.q29 g.q30 g.q31) (mkFlag g.q22 g.q24 g.q20) (mkFlag g.q14 g.q16 g.q12)) := by
      have h := phiFlip_antisymm g.q28 (mkFlag g.q29 g.q30 g.q31) (mkFlag g.q22 g.q24 g.q20) (mkFlag g.q14 g.q16 g.q12); simp only [flipF_mkFlag] at h; linarith
    have hp_13_2 : phiFlip g.q24 (mkFlag g.q28 g.q20 g.q22) (mkFlag g.q30 g.q23 g.q27) (mkFlag g.q16 g.q06 g.q05) = -(phiFlip g.q24 (mkFlag g.q20 g.q28 g.q22) (mkFlag g.q23 g.q30 g.q27) (mkFlag g.q06 g.q16 g.q05)) := by
      have h := phiFlip_antisymm g.q24 (mkFlag g.q20 g.q28 g.q22) (mkFlag g.q23 g.q30 g.q27) (mkFlag g.q06 g.q16 g.q05); simp only [flipF_mkFlag] at h; linarith
    have hp_13_3 : phiFlip g.q16 (mkFlag g.q28 g.q12 g.q14) (mkFlag g.q30 g.q15 g.q19) (mkFlag g.q24 g.q05 g.q06) = -(phiFlip g.q16 (mkFlag g.q12 g.q28 g.q14) (mkFlag g.q15 g.q30 g.q19) (mkFlag g.q05 g.q24 g.q06)) := by
      have h := phiFlip_antisymm g.q16 (mkFlag g.q12 g.q28 g.q14) (mkFlag g.q15 g.q30 g.q19) (mkFlag g.q05 g.q24 g.q06); simp only [flipF_mkFlag] at h; linarith
    have hp_14_1 : phiFlip g.q29 (mkFlag g.q31 g.q28 g.q30) (mkFlag g.q26 g.q22 g.q21) (mkFlag g.q18 g.q14 g.q13) = -(phiFlip g.q29 (mkFlag g.q28 g.q31 g.q30) (mkFlag g.q22 g.q26 g.q21) (mkFlag g.q14 g.q18 g.q13)) := by
      have h := phiFlip_antisymm g.q29 (mkFlag g.q28 g.q31 g.q30) (mkFlag g.q22 g.q26 g.q21) (mkFlag g.q14 g.q18 g.q13); simp only [flipF_mkFlag] at h; linarith
    have hp_14_2 : phiFlip g.q26 (mkFlag g.q31 g.q25 g.q27) (mkFlag g.q29 g.q21 g.q22) (mkFlag g.q18 g.q09 g.q08) = -(phiFlip g.q26 (mkFlag g.q25 g.q31 g.q27) (mkFlag g.q21 g.q29 g.q22) (mkFlag g.q09 g.q18 g.q08)) := by
      have h := phiFlip_antisymm g.q26 (mkFlag g.q25 g.q31 g.q27) (mkFlag g.q21 g.q29 g.q22) (mkFlag g.q09 g.q18 g.q08); simp only [flipF_mkFlag] at h; linarith
    have hp_14_3 : phiFlip g.q18 (mkFlag g.q31 g.q17 g.q19) (mkFlag g.q29 g.q13 g.q14) (mkFlag g.q26 g.q08 g.q09) = -(phiFlip g.q18 (mkFlag g.q17 g.q31 g.q19) (mkFlag g.q13 g.q29 g.q14) (mkFlag g.q08 g.q26 g.q09)) := by
      have h := phiFlip_antisymm g.q18 (mkFlag g.q17 g.q31 g.q19) (mkFlag g.q13 g.q29 g.q14) (mkFlag g.q08 g.q26 g.q09); simp only [flipF_mkFlag] at h; linarith
    have hp_15_0 : phiFlip g.q31 (mkFlag g.q30 g.q29 g.q28) (mkFlag g.q27 g.q26 g.q25) (mkFlag g.q19 g.q18 g.q17) = -(phiFlip g.q31 (mkFlag g.q29 g.q30 g.q28) (mkFlag g.q26 g.q27 g.q25) (mkFlag g.q18 g.q19 g.q17)) := by
      have h := phiFlip_antisymm g.q31 (mkFlag g.q29 g.q30 g.q28) (mkFlag g.q26 g.q27 g.q25) (mkFlag g.q18 g.q19 g.q17); simp only [flipF_mkFlag] at h; linarith
    have hp_15_1 : phiFlip g.q30 (mkFlag g.q31 g.q28 g.q29) (mkFlag g.q27 g.q24 g.q23) (mkFlag g.q19 g.q16 g.q15) = -(phiFlip g.q30 (mkFlag g.q28 g.q31 g.q29) (mkFlag g.q24 g.q27 g.q23) (mkFlag g.q16 g.q19 g.q15)) := by
      have h := phiFlip_antisymm g.q30 (mkFlag g.q28 g.q31 g.q29) (mkFlag g.q24 g.q27 g.q23) (mkFlag g.q16 g.q19 g.q15); simp only [flipF_mkFlag] at h; linarith
    have hp_15_2 : phiFlip g.q27 (mkFlag g.q31 g.q25 g.q26) (mkFlag g.q30 g.q23 g.q24) (mkFlag g.q19 g.q11 g.q10) = -(phiFlip g.q27 (mkFlag g.q25 g.q31 g.q26) (mkFlag g.q23 g.q30 g.q24) (mkFlag g.q11 g.q19 g.q10)) := by
      have h := phiFlip_antisymm g.q27 (mkFlag g.q25 g.q31 g.q26) (mkFlag g.q23 g.q30 g.q24) (mkFlag g.q11 g.q19 g.q10); simp only [flipF_mkFlag] at h; linarith
    have hp_15_3 : phiFlip g.q19 (mkFlag g.q31 g.q17 g.q18) (mkFlag g.q30 g.q15 g.q16) (mkFlag g.q27 g.q10 g.q11) = -(phiFlip g.q19 (mkFlag g.q17 g.q31 g.q18) (mkFlag g.q15 g.q30 g.q16) (mkFlag g.q10 g.q27 g.q11)) := by
      have h := phiFlip_antisymm g.q19 (mkFlag g.q17 g.q31 g.q18) (mkFlag g.q15 g.q30 g.q16) (mkFlag g.q10 g.q27 g.q11); simp only [flipF_mkFlag] at h; linarith
    rw [hp_1_0, hp_2_1, hp_3_0, hp_3_1, hp_4_2, hp_5_0, hp_5_2, hp_6_1, hp_6_2, hp_7_0, hp_7_1, hp_7_2, hp_8_3, hp_9_0, hp_9_3, hp_10_1, hp_10_3, hp_11_0, hp_11_1, hp_11_3, hp_12_2, hp_12_3, hp_13_0, hp_13_2, hp_13_3, hp_14_1, hp_14_2, hp_14_3, hp_15_0, hp_15_1, hp_15_2, hp_15_3]
    ring
  have hP2 : (phiFlip2 g.q00 g.q01 g.q04 g.q07 g.q05 g.q06 g.q08 g.q09 + phiFlip2 g.q00 g.q02 g.q05 g.q12 g.q04 g.q06 g.q13 g.q14 + phiFlip2 g.q00 g.q03 g.q06 g.q20 g.q04 g.q05 g.q21 g.q22 + phiFlip2 g.q01 g.q02 g.q08 g.q13 g.q07 g.q09 g.q12 g.q14 + phiFlip2 g.q01 g.q03 g.q09 g.q21 g.q07 g.q08 g.q20 g.q22 + phiFlip2 g.q02 g.q03 g.q14 g.q22 g.q12 g.q13 g.q20 g.q21 + phiFlip2 g.q00 g.q04 g.q01 g.q07 g.q02 g.q03 g.q10 g.q11 + phiFlip2 g.q00 g.q05 g.q02 g.q12 g.q01 g.q03 g.q15 g.q16 + phiFlip2 g.q00 g.q06 g.q03 g.q20 g.q01 g.q02 g.q23 g.q24 + phiFlip2 g.q04 g.q05 g.q10 g.q15 g.q07 g.q11 g.q12 g.q16 + phiFlip2 g.q04 g.q06 g.q11 g.q23 g.q07 g.q10 g.q20 g.q24 + phiFlip2 g.q05 g.q06 g.q16 g.q24 g.q12 g.q15 g.q20 g.q23 + phiFlip2 g.q07 g.q01 g.q04 g.q00 g.q10 g.q11 g.q02 g.q03 + phiFlip2 g.q07 g.q08 g.q10 g.q17 g.q04 g.q11 g.q13 g.q18 + phiFlip2 g.q07 g.q09 g.q11 g.q25 g.q04 g.q10 g.q21 g.q26 + phiFlip2 g.q01 g.q08 g.q02 g.q13 g.q00 g.q03 g.q17 g.q18 + phiFlip2 g.q01 g.q09 g.q03 g.q21 g.q00 g.q02 g.q25 g.q26 + phiFlip2 g.q08 g.q09 g.q18 g.q26 g.q17 g.q13 g.q25 g.q21 + phiFlip2 g.q07 g.q04 g.q01 g.q00 g.q08 g.q09 g.q05 g.q06 + phiFlip2 g.q07 g.q10 g.q08 g.q17 g.q01 g.q09 g.q15 g.q19 + phiFlip2 g.q07 g.q11 g.q09 g.q25 g.q01 g.q08 g.q23 g.q27 + phiFlip2 g.q04 g.q10 g.q05 g.q15 g.q00 g.q06 g.q17 g.q19 + phiFlip2 g.q04 g.q11 g.q06 g.q23 g.q00 g.q05 g.q25 g.q27 + phiFlip2 g.q10 g.q11 g.q19 g.q27 g.q17 g.q15 g.q25 g.q23 + phiFlip2 g.q12 g.q13 g.q15 g.q17 g.q05 g.q16 g.q08 g.q18 + phiFlip2 g.q12 g.q02 g.q05 g.q00 g.q15 g.q16 g.q01 g.q03 + phiFlip2 g.q12 g.q14 g.q16 g.q28 g.q15 g.q05 g.q29 g.q22 + phiFlip2 g.q13 g.q02 g.q08 g.q01 g.q17 g.q18 g.q00 g.q03 + phiFlip2 g.q13 g.q14 g.q18 g.q29 g.q17 g.q08 g.q28 g.q22 + phiFlip2 g.q02 g.q14 g.q03 g.q22 g.q00 g.q01 g.q28 g.q29 + phiFlip2 g.q12 g.q15 g.q13 g.q17 g.q02 g.q14 g.q10 g.q19 + phiFlip2 g.q12 g.q05 g.q02 g.q00 g.q13 g.q14 g.q04 g.q06 + phiFlip2 g.q12 g.q16 g.q14 g.q28 g.q13 g.q02 g.q30 g.q24 + phiFlip2 g.q15 g.q05 g.q10 g.q04 g.q17 g.q19 g.q00 g.q06 + phiFlip2 g.q15 g.q16 g.q19 g.q30 g.q17 g.q10 g.q28 g.q24 + phiFlip2 g.q05 g.q16 g.q06 g.q24 g.q00 g.q04 g.q28 g.q30 + phiFlip2 g.q17 g.q13 g.q15 g.q12 g.q10 g.q19 g.q02 g.q14 + phiFlip2 g.q17 g.q08 g.q10 g.q07 g.q15 g.q19 g.q01 g.q09 + phiFlip2 g.q17 g.q18 g.q19 g.q31 g.q15 g.q10 g.q29 g.q26 + phiFlip2 g.q13 g.q08 g.q02 g.q01 g.q12 g.q14 g.q07 g.q09 + phiFlip2 g.q13 g.q18 g.q14 g.q29 g.q12 g.q02 g.q31 g.q26 + phiFlip2 g.q08 g.q18 g.q09 g.q26 g.q07 g.q01 g.q31 g.q29 + phiFlip2 g.q17 g.q15 g.q13 g.q12 g.q08 g.q18 g.q05 g.q16 + phiFlip2 g.q17 g.q10 g.q08 g.q07 g.q13 g.q18 g.q04 g.q11 + phiFlip2 g.q17 g.q19 g.q18 g.q31 g.q13 g.q08 g.q30 g.q27 + phiFlip2 g.q15 g.q10 g.q05 g.q04 g.q12 g.q16 g.q07 g.q11 + phiFlip2 g.q15 g.q19 g.q16 g.q30 g.q12 g.q05 g.q31 g.q27 + phiFlip2 g.q10 g.q19 g.q11 g.q27 g.q07 g.q04 g.q31 g.q30 + phiFlip2 g.q20 g.q21 g.q23 g.q25 g.q24 g.q06 g.q26 g.q09 + phiFlip2 g.q20 g.q22 g.q24 g.q28 g.q23 g.q06 g.q29 g.q14 + phiFlip2 g.q20 g.q03 g.q06 g.q00 g.q23 g.q24 g.q01 g.q02 + phiFlip2 g.q21 g.q22 g.q26 g.q29 g.q25 g.q09 g.q28 g.q14 + phiFlip2 g.q21 g.q03 g.q09 g.q01 g.q25 g.q26 g.q00 g.q02 + phiFlip2 g.q22 g.q03 g.q14 g.q02 g.q28 g.q29 g.q00 g.q01 + phiFlip2 g.q20 g.q23 g.q21 g.q25 g.q22 g.q03 g.q27 g.q11 + phiFlip2 g.q20 g.q24 g.q22 g.q28 g.q21 g.q03 g.q30 g.q16 + phiFlip2 g.q20 g.q06 g.q03 g.q00 g.q21 g.q22 g.q04 g.q05 + phiFlip2 g.q23 g.q24 g.q27 g.q30 g.q25 g.q11 g.q28 g.q16 + phiFlip2 g.q23 g.q06 g.q11 g.q04 g.q25 g.q27 g.q00 g.q05 + phiFlip2 g.q24 g.q06 g.q16 g.q05 g.q28 g.q30 g.q00 g.q04 + phiFlip2 g.q25 g.q21 g.q23 g.q20 g.q27 g.q11 g.q22 g.q03 + phiFlip2 g.q25 g.q26 g.q27 g.q31 g.q23 g.q11 g.q29 g.q18 + phiFlip2 g.q25 g.q09 g.q11 g.q07 g.q23 g.q27 g.q01 g.q08 + phiFlip2 g.q21 g.q26 g.q22 g.q29 g.q20 g.q03 g.q31 g.q18 + phiFlip2 g.q21 g.q09 g.q03 g.q01 g.q20 g.q22 g.q07 g.q08 + phiFlip2 g.q26 g.q09 g.q18 g.q08 g.q31 g.q29 g.q07 g.q01 + phiFlip2 g.q25 g.q23 g.q21 g.q20 g.q26 g.q09 g.q24 g.q06 + phiFlip2 g.q25 g.q27 g.q26 g.q31 g.q21 g.q09 g.q30 g.q19 + phiFlip2 g.q25 g.q11 g.q09 g.q07 g.q21 g.q26 g.q04 g.q10 + phiFlip2 g.q23 g.q27 g.q24 g.q30 g.q20 g.q06 g.q31 g.q19 + phiFlip2 g.q23 g.q11 g.q06 g.q04 g.q20 g.q24 g.q07 g.q10 + phiFlip2 g.q27 g.q11 g.q19 g.q10 g.q31 g.q30 g.q07 g.q04 + phiFlip2 g.q28 g.q29 g.q30 g.q31 g.q24 g.q16 g.q26 g.q18 + phiFlip2 g.q28 g.q22 g.q24 g.q20 g.q30 g.q16 g.q21 g.q03 + phiFlip2 g.q28 g.q14 g.q16 g.q12 g.q30 g.q24 g.q13 g.q02 + phiFlip2 g.q29 g.q22 g.q26 g.q21 g.q31 g.q18 g.q20 g.q03 + phiFlip2 g.q29 g.q14 g.q18 g.q13 g.q31 g.q26 g.q12 g.q02 + phiFlip2 g.q22 g.q14 g.q03 g.q02 g.q20 g.q21 g.q12 g.q13 + phiFlip2 g.q28 g.q30 g.q29 g.q31 g.q22 g.q14 g.q27 g.q19 + phiFlip2 g.q28 g.q24 g.q22 g.q20 g.q29 g.q14 g.q23 g.q06 + phiFlip2 g.q28 g.q16 g.q14 g.q12 g.q29 g.q22 g.q15 g.q05 + phiFlip2 g.q30 g.q24 g.q27 g.q23 g.q31 g.q19 g.q20 g.q06 + phiFlip2 g.q30 g.q16 g.q19 g.q15 g.q31 g.q27 g.q12 g.q05 + phiFlip2 g.q24 g.q16 g.q06 g.q05 g.q20 g.q23 g.q12 g.q15 + phiFlip2 g.q31 g.q29 g.q30 g.q28 g.q27 g.q19 g.q22 g.q14 + phiFlip2 g.q31 g.q26 g.q27 g.q25 g.q30 g.q19 g.q21 g.q09 + phiFlip2 g.q31 g.q18 g.q19 g.q17 g.q30 g.q27 g.q13 g.q08 + phiFlip2 g.q29 g.q26 g.q22 g.q21 g.q28 g.q14 g.q25 g.q09 + phiFlip2 g.q29 g.q18 g.q14 g.q13 g.q28 g.q22 g.q17 g.q08 + phiFlip2 g.q26 g.q18 g.q09 g.q08 g.q25 g.q21 g.q17 g.q13 + phiFlip2 g.q31 g.q30 g.q29 g.q28 g.q26 g.q18 g.q24 g.q16 + phiFlip2 g.q31 g.q27 g.q26 g.q25 g.q29 g.q18 g.q23 g.q11 + phiFlip2 g.q31 g.q19 g.q18 g.q17 g.q29 g.q26 g.q15 g.q10 + phiFlip2 g.q30 g.q27 g.q24 g.q23 g.q28 g.q16 g.q25 g.q11 + phiFlip2 g.q30 g.q19 g.q16 g.q15 g.q28 g.q24 g.q17 g.q10 + phiFlip2 g.q27 g.q19 g.q11 g.q10 g.q25 g.q23 g.q17 g.q15) = 0 := by
    have hq_2_0_1 : phiFlip2 g.q07 g.q01 g.q04 g.q00 g.q10 g.q11 g.q02 g.q03 = -(phiFlip2 g.q00 g.q04 g.q01 g.q07 g.q02 g.q03 g.q10 g.q11) := by
      have h := phiFlip2_antisymm g.q00 g.q04 g.q01 g.q07 g.q02 g.q03 g.q10 g.q11; linarith
    have hq_3_0_1 : phiFlip2 g.q07 g.q04 g.q01 g.q00 g.q08 g.q09 g.q05 g.q06 = -(phiFlip2 g.q00 g.q01 g.q04 g.q07 g.q05 g.q06 g.q08 g.q09) := by
      have h := phiFlip2_antisymm g.q00 g.q01 g.q04 g.q07 g.q05 g.q06 g.q08 g.q09; linarith
    have hq_4_0_2 : phiFlip2 g.q12 g.q02 g.q05 g.q00 g.q15 g.q16 g.q01 g.q03 = -(phiFlip2 g.q00 g.q05 g.q02 g.q12 g.q01 g.q03 g.q15 g.q16) := by
      have h := phiFlip2_antisymm g.q00 g.q05 g.q02 g.q12 g.q01 g.q03 g.q15 g.q16; linarith
    have hq_4_1_2 : phiFlip2 g.q13 g.q02 g.q08 g.q01 g.q17 g.q18 g.q00 g.q03 = -(phiFlip2 g.q01 g.q08 g.q02 g.q13 g.q00 g.q03 g.q17 g.q18) := by
      have h := phiFlip2_antisymm g.q01 g.q08 g.q02 g.q13 g.q00 g.q03 g.q17 g.q18; linarith
    have hq_5_0_2 : phiFlip2 g.q12 g.q05 g.q02 g.q00 g.q13 g.q14 g.q04 g.q06 = -(phiFlip2 g.q00 g.q02 g.q05 g.q12 g.q04 g.q06 g.q13 g.q14) := by
      have h := phiFlip2_antisymm g.q00 g.q02 g.q05 g.q12 g.q04 g.q06 g.q13 g.q14; linarith
    have hq_5_1_2 : phiFlip2 g.q15 g.q05 g.q10 g.q04 g.q17 g.q19 g.q00 g.q06 = -(phiFlip2 g.q04 g.q10 g.q05 g.q15 g.q00 g.q06 g.q17 g.q19) := by
      have h := phiFlip2_antisymm g.q04 g.q10 g.q05 g.q15 g.q00 g.q06 g.q17 g.q19; linarith
    have hq_6_0_1 : phiFlip2 g.q17 g.q13 g.q15 g.q12 g.q10 g.q19 g.q02 g.q14 = -(phiFlip2 g.q12 g.q15 g.q13 g.q17 g.q02 g.q14 g.q10 g.q19) := by
      have h := phiFlip2_antisymm g.q12 g.q15 g.q13 g.q17 g.q02 g.q14 g.q10 g.q19; linarith
    have hq_6_0_2 : phiFlip2 g.q17 g.q08 g.q10 g.q07 g.q15 g.q19 g.q01 g.q09 = -(phiFlip2 g.q07 g.q10 g.q08 g.q17 g.q01 g.q09 g.q15 g.q19) := by
      have h := phiFlip2_antisymm g.q07 g.q10 g.q08 g.q17 g.q01 g.q09 g.q15 g.q19; linarith
    have hq_6_1_2 : phiFlip2 g.q13 g.q08 g.q02 g.q01 g.q12 g.q14 g.q07 g.q09 = -(phiFlip2 g.q01 g.q02 g.q08 g.q13 g.q07 g.q09 g.q12 g.q14) := by
      have h := phiFlip2_antisymm g.q01 g.q02 g.q08 g.q13 g.q07 g.q09 g.q12 g.q14; linarith
    have hq_7_0_1 : phiFlip2 g.q17 g.q15 g.q13 g.q12 g.q08 g.q18 g.q05 g.q16 = -(phiFlip2 g.q12 g.q13 g.q15 g.q17 g.q05 g.q16 g.q08 g.q18) := by
      have h := phiFlip2_antisymm g.q12 g.q13 g.q15 g.q17 g.q05 g.q16 g.q08 g.q18; linarith
    have hq_7_0_2 : phiFlip2 g.q17 g.q10 g.q08 g.q07 g.q13 g.q18 g.q04 g.q11 = -(phiFlip2 g.q07 g.q08 g.q10 g.q17 g.q04 g.q11 g.q13 g.q18) := by
      have h := phiFlip2_antisymm g.q07 g.q08 g.q10 g.q17 g.q04 g.q11 g.q13 g.q18; linarith
    have hq_7_1_2 : phiFlip2 g.q15 g.q10 g.q05 g.q04 g.q12 g.q16 g.q07 g.q11 = -(phiFlip2 g.q04 g.q05 g.q10 g.q15 g.q07 g.q11 g.q12 g.q16) := by
      have h := phiFlip2_antisymm g.q04 g.q05 g.q10 g.q15 g.q07 g.q11 g.q12 g.q16; linarith
    have hq_8_0_3 : phiFlip2 g.q20 g.q03 g.q06 g.q00 g.q23 g.q24 g.q01 g.q02 = -(phiFlip2 g.q00 g.q06 g.q03 g.q20 g.q01 g.q02 g.q23 g.q24) := by
      have h := phiFlip2_antisymm g.q00 g.q06 g.q03 g.q20 g.q01 g.q02 g.q23 g.q24; linarith
    have hq_8_1_3 : phiFlip2 g.q21 g.q03 g.q09 g.q01 g.q25 g.q26 g.q00 g.q02 = -(phiFlip2 g.q01 g.q09 g.q03 g.q21 g.q00 g.q02 g.q25 g.q26) := by
      have h := phiFlip2_antisymm g.q01 g.q09 g.q03 g.q21 g.q00 g.q02 g.q25 g.q26; linarith
    have hq_8_2_3 : phiFlip2 g.q22 g.q03 g.q14 g.q02 g.q28 g.q29 g.q00 g.q01 = -(phiFlip2 g.q02 g.q14 g.q03 g.q22 g.q00 g.q01 g.q28 g.q29) := by
      have h := phiFlip2_antisymm g.q02 g.q14 g.q03 g.q22 g.q00 g.q01 g.q28 g.q29; linarith
    have hq_9_0_3 : phiFlip2 g.q20 g.q06 g.q03 g.q00 g.q21 g.q22 g.q04 g.q05 = -(phiFlip2 g.q00 g.q03 g.q06 g.q20 g.q04 g.q05 g.q21 g.q22) := by
      have h := phiFlip2_antisymm g.q00 g.q03 g.q06 g.q20 g.q04 g.q05 g.q21 g.q22; linarith
    have hq_9_1_3 : phiFlip2 g.q23 g.q06 g.q11 g.q04 g.q25 g.q27 g.q00 g.q05 = -(phiFlip2 g.q04 g.q11 g.q06 g.q23 g.q00 g.q05 g.q25 g.q27) := by
      have h := phiFlip2_antisymm g.q04 g.q11 g.q06 g.q23 g.q00 g.q05 g.q25 g.q27; linarith
    have hq_9_2_3 : phiFlip2 g.q24 g.q06 g.q16 g.q05 g.q28 g.q30 g.q00 g.q04 = -(phiFlip2 g.q05 g.q16 g.q06 g.q24 g.q00 g.q04 g.q28 g.q30) := by
      have h := phiFlip2_antisymm g.q05 g.q16 g.q06 g.q24 g.q00 g.q04 g.q28 g.q30; linarith
    have hq_10_0_1 : phiFlip2 g.q25 g.q21 g.q23 g.q20 g.q27 g.q11 g.q22 g.q03 = -(phiFlip2 g.q20 g.q23 g.q21 g.q25 g.q22 g.q03 g.q27 g.q11) := by
      have h := phiFlip2_antisymm g.q20 g.q23 g.q21 g.q25 g.q22 g.q03 g.q27 g.q11; linarith
    have hq_10_0_3 : phiFlip2 g.q25 g.q09 g.q11 g.q07 g.q23 g.q27 g.q01 g.q08 = -(phiFlip2 g.q07 g.q11 g.q09 g.q25 g.q01 g.q08 g.q23 g.q27) := by
      have h := phiFlip2_antisymm g.q07 g.q11 g.q09 g.q25 g.q01 g.q08 g.q23 g.q27; linarith
    have hq_10_1_3 : phiFlip2 g.q21 g.q09 g.q03 g.q01 g.q20 g.q22 g.q07 g.q08 = -(phiFlip2 g.q01 g.q03 g.q09 g.q21 g.q07 g.q08 g.q20 g.q22) := by
      have h := phiFlip2_antisymm g.q01 g.q03 g.q09 g.q21 g.q07 g.q08 g.q20 g.q22; linarith
    have hq_10_2_3 : phiFlip2 g.q26 g.q09 g.q18 g.q08 g.q31 g.q29 g.q07 g.q01 = -(phiFlip2 g.q08 g.q18 g.q09 g.q26 g.q07 g.q01 g.q31 g.q29) := by
      have h := phiFlip2_antisymm g.q08 g.q18 g.q09 g.q26 g.q07 g.q01 g.q31 g.q29; linarith
    have hq_11_0_1 : phiFlip2 g.q25 g.q23 g.q21 g.q20 g.q26 g.q09 g.q24 g.q06 = -(phiFlip2 g.q20 g.q21 g.q23 g.q25 g.q24 g.q06 g.q26 g.q09) := by
      have h := phiFlip2_antisymm g.q20 g.q21 g.q23 g.q25 g.q24 g.q06 g.q26 g.q09; linarith
    have hq_11_0_3 : phiFlip2 g.q25 g.q11 g.q09 g.q07 g.q21 g.q26 g.q04 g.q10 = -(phiFlip2 g.q07 g.q09 g.q11 g.q25 g.q04 g.q10 g.q21 g.q26) := by
      have h := phiFlip2_antisymm g.q07 g.q09 g.q11 g.q25 g.q04 g.q10 g.q21 g.q26; linarith
    have hq_11_1_3 : phiFlip2 g.q23 g.q11 g.q06 g.q04 g.q20 g.q24 g.q07 g.q10 = -(phiFlip2 g.q04 g.q06 g.q11 g.q23 g.q07 g.q10 g.q20 g.q24) := by
      have h := phiFlip2_antisymm g.q04 g.q06 g.q11 g.q23 g.q07 g.q10 g.q20 g.q24; linarith
    have hq_11_2_3 : phiFlip2 g.q27 g.q11 g.q19 g.q10 g.q31 g.q30 g.q07 g.q04 = -(phiFlip2 g.q10 g.q19 g.q11 g.q27 g.q07 g.q04 g.q31 g.q30) := by
      have h := phiFlip2_antisymm g.q10 g.q19 g.q11 g.q27 g.q07 g.q04 g.q31 g.q30; linarith
    have hq_12_0_2 : phiFlip2 g.q28 g.q22 g.q24 g.q20 g.q30 g.q16 g.q21 g.q03 = -(phiFlip2 g.q20 g.q24 g.q22 g.q28 g.q21 g.q03 g.q30 g.q16) := by
      have h := phiFlip2_antisymm g.q20 g.q24 g.q22 g.q28 g.q21 g.q03 g.q30 g.q16; linarith
    have hq_12_0_3 : phiFlip2 g.q28 g.q14 g.q16 g.q12 g.q30 g.q24 g.q13 g.q02 = -(phiFlip2 g.q12 g.q16 g.q14 g.q28 g.q13 g.q02 g.q30 g.q24) := by
      have h := phiFlip2_antisymm g.q12 g.q16 g.q14 g.q28 g.q13 g.q02 g.q30 g.q24; linarith
    have hq_12_1_2 : phiFlip2 g.q29 g.q22 g.q26 g.q21 g.q31 g.q18 g.q20 g.q03 = -(phiFlip2 g.q21 g.q26 g.q22 g.q29 g.q20 g.q03 g.q31 g.q18) := by
      have h := phiFlip2_antisymm g.q21 g.q26 g.q22 g.q29 g.q20 g.q03 g.q31 g.q18; linarith
    have hq_12_1_3 : phiFlip2 g.q29 g.q14 g.q18 g.q13 g.q31 g.q26 g.q12 g.q02 = -(phiFlip2 g.q13 g.q18 g.q14 g.q29 g.q12 g.q02 g.q31 g.q26) := by
      have h := phiFlip2_antisymm g.q13 g.q18 g.q14 g.q29 g.q12 g.q02 g.q31 g.q26; linarith
    have hq_12_2_3 : phiFlip2 g.q22 g.q14 g.q03 g.q02 g.q20 g.q21 g.q12 g.q13 = -(phiFlip2 g.q02 g.q03 g.q14 g.q22 g.q12 g.q13 g.q20 g.q21) := by
      have h := phiFlip2_antisymm g.q02 g.q03 g.q14 g.q22 g.q12 g.q13 g.q20 g.q21; linarith
    have hq_13_0_2 : phiFlip2 g.q28 g.q24 g.q22 g.q20 g.q29 g.q14 g.q23 g.q06 = -(phiFlip2 g.q20 g.q22 g.q24 g.q28 g.q23 g.q06 g.q29 g.q14) := by
      have h := phiFlip2_antisymm g.q20 g.q22 g.q24 g.q28 g.q23 g.q06 g.q29 g.q14; linarith
    have hq_13_0_3 : phiFlip2 g.q28 g.q16 g.q14 g.q12 g.q29 g.q22 g.q15 g.q05 = -(phiFlip2 g.q12 g.q14 g.q16 g.q28 g.q15 g.q05 g.q29 g.q22) := by
      have h := phiFlip2_antisymm g.q12 g.q14 g.q16 g.q28 g.q15 g.q05 g.q29 g.q22; linarith
    have hq_13_1_2 : phiFlip2 g.q30 g.q24 g.q27 g.q23 g.q31 g.q19 g.q20 g.q06 = -(phiFlip2 g.q23 g.q27 g.q24 g.q30 g.q20 g.q06 g.q31 g.q19) := by
      have h := phiFlip2_antisymm g.q23 g.q27 g.q24 g.q30 g.q20 g.q06 g.q31 g.q19; linarith
    have hq_13_1_3 : phiFlip2 g.q30 g.q16 g.q19 g.q15 g.q31 g.q27 g.q12 g.q05 = -(phiFlip2 g.q15 g.q19 g.q16 g.q30 g.q12 g.q05 g.q31 g.q27) := by
      have h := phiFlip2_antisymm g.q15 g.q19 g.q16 g.q30 g.q12 g.q05 g.q31 g.q27; linarith
    have hq_13_2_3 : phiFlip2 g.q24 g.q16 g.q06 g.q05 g.q20 g.q23 g.q12 g.q15 = -(phiFlip2 g.q05 g.q06 g.q16 g.q24 g.q12 g.q15 g.q20 g.q23) := by
      have h := phiFlip2_antisymm g.q05 g.q06 g.q16 g.q24 g.q12 g.q15 g.q20 g.q23; linarith
    have hq_14_0_1 : phiFlip2 g.q31 g.q29 g.q30 g.q28 g.q27 g.q19 g.q22 g.q14 = -(phiFlip2 g.q28 g.q30 g.q29 g.q31 g.q22 g.q14 g.q27 g.q19) := by
      have h := phiFlip2_antisymm g.q28 g.q30 g.q29 g.q31 g.q22 g.q14 g.q27 g.q19; linarith
    have hq_14_0_2 : phiFlip2 g.q31 g.q26 g.q27 g.q25 g.q30 g.q19 g.q21 g.q09 = -(phiFlip2 g.q25 g.q27 g.q26 g.q31 g.q21 g.q09 g.q30 g.q19) := by
      have h := phiFlip2_antisymm g.q25 g.q27 g.q26 g.q31 g.q21 g.q09 g.q30 g.q19; linarith
    have hq_14_0_3 : phiFlip2 g.q31 g.q18 g.q19 g.q17 g.q30 g.q27 g.q13 g.q08 = -(phiFlip2 g.q17 g.q19 g.q18 g.q31 g.q13 g.q08 g.q30 g.q27) := by
      have h := phiFlip2_antisymm g.q17 g.q19 g.q18 g.q31 g.q13 g.q08 g.q30 g.q27; linarith
    have hq_14_1_2 : phiFlip2 g.q29 g.q26 g.q22 g.q21 g.q28 g.q14 g.q25 g.q09 = -(phiFlip2 g.q21 g.q22 g.q26 g.q29 g.q25 g.q09 g.q28 g.q14) := by
      have h := phiFlip2_antisymm g.q21 g.q22 g.q26 g.q29 g.q25 g.q09 g.q28 g.q14; linarith
    have hq_14_1_3 : phiFlip2 g.q29 g.q18 g.q14 g.q13 g.q28 g.q22 g.q17 g.q08 = -(phiFlip2 g.q13 g.q14 g.q18 g.q29 g.q17 g.q08 g.q28 g.q22) := by
      have h := phiFlip2_antisymm g.q13 g.q14 g.q18 g.q29 g.q17 g.q08 g.q28 g.q22; linarith
    have hq_14_2_3 : phiFlip2 g.q26 g.q18 g.q09 g.q08 g.q25 g.q21 g.q17 g.q13 = -(phiFlip2 g.q08 g.q09 g.q18 g.q26 g.q17 g.q13 g.q25 g.q21) := by
      have h := phiFlip2_antisymm g.q08 g.q09 g.q18 g.q26 g.q17 g.q13 g.q25 g.q21; linarith
    have hq_15_0_1 : phiFlip2 g.q31 g.q30 g.q29 g.q28 g.q26 g.q18 g.q24 g.q16 = -(phiFlip2 g.q28 g.q29 g.q30 g.q31 g.q24 g.q16 g.q26 g.q18) := by
      have h := phiFlip2_antisymm g.q28 g.q29 g.q30 g.q31 g.q24 g.q16 g.q26 g.q18; linarith
    have hq_15_0_2 : phiFlip2 g.q31 g.q27 g.q26 g.q25 g.q29 g.q18 g.q23 g.q11 = -(phiFlip2 g.q25 g.q26 g.q27 g.q31 g.q23 g.q11 g.q29 g.q18) := by
      have h := phiFlip2_antisymm g.q25 g.q26 g.q27 g.q31 g.q23 g.q11 g.q29 g.q18; linarith
    have hq_15_0_3 : phiFlip2 g.q31 g.q19 g.q18 g.q17 g.q29 g.q26 g.q15 g.q10 = -(phiFlip2 g.q17 g.q18 g.q19 g.q31 g.q15 g.q10 g.q29 g.q26) := by
      have h := phiFlip2_antisymm g.q17 g.q18 g.q19 g.q31 g.q15 g.q10 g.q29 g.q26; linarith
    have hq_15_1_2 : phiFlip2 g.q30 g.q27 g.q24 g.q23 g.q28 g.q16 g.q25 g.q11 = -(phiFlip2 g.q23 g.q24 g.q27 g.q30 g.q25 g.q11 g.q28 g.q16) := by
      have h := phiFlip2_antisymm g.q23 g.q24 g.q27 g.q30 g.q25 g.q11 g.q28 g.q16; linarith
    have hq_15_1_3 : phiFlip2 g.q30 g.q19 g.q16 g.q15 g.q28 g.q24 g.q17 g.q10 = -(phiFlip2 g.q15 g.q16 g.q19 g.q30 g.q17 g.q10 g.q28 g.q24) := by
      have h := phiFlip2_antisymm g.q15 g.q16 g.q19 g.q30 g.q17 g.q10 g.q28 g.q24; linarith
    have hq_15_2_3 : phiFlip2 g.q27 g.q19 g.q11 g.q10 g.q25 g.q23 g.q17 g.q15 = -(phiFlip2 g.q10 g.q11 g.q19 g.q27 g.q17 g.q15 g.q25 g.q23) := by
      have h := phiFlip2_antisymm g.q10 g.q11 g.q19 g.q27 g.q17 g.q15 g.q25 g.q23; linarith
    rw [hq_2_0_1, hq_3_0_1, hq_4_0_2, hq_4_1_2, hq_5_0_2, hq_5_1_2, hq_6_0_1, hq_6_0_2, hq_6_1_2, hq_7_0_1, hq_7_0_2, hq_7_1_2, hq_8_0_3, hq_8_1_3, hq_8_2_3, hq_9_0_3, hq_9_1_3, hq_9_2_3, hq_10_0_1, hq_10_0_3, hq_10_1_3, hq_10_2_3, hq_11_0_1, hq_11_0_3, hq_11_1_3, hq_11_2_3, hq_12_0_2, hq_12_0_3, hq_12_1_2, hq_12_1_3, hq_12_2_3, hq_13_0_2, hq_13_0_3, hq_13_1_2, hq_13_1_3, hq_13_2_3, hq_14_0_1, hq_14_0_2, hq_14_0_3, hq_14_1_2, hq_14_1_3, hq_14_2_3, hq_15_0_1, hq_15_0_2, hq_15_0_3, hq_15_1_2, hq_15_1_3, hq_15_2_3]
    ring
  have hdiff : q4ScoreGauged g - q4ScoreUngauged g =
      (∑ fk : Fin 8, (evalQ3G (extractFacetQ3 fk g) - evalQ3U (extractFacetQ3 fk g))) +
      (∑ v : Fin 16, (evalB2G (extractBallB2 v g) - evalB2U (extractBallB2 v g))) := by
    unfold q4ScoreGauged q4ScoreUngauged
    simp only [Finset.sum_sub_distrib]
    ring
  have hsum16 : ∀ (f : Fin 16 → ℤ),
      (∑ v : Fin 16, f v) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 +
        f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 := fun f => by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc, add_assoc]
  rw [Fin.sum_univ_eight, hsum16] at hdiff
  dsimp only [Fin.val_zero, Fin.val_one, Fin.val_two, extractFacetQ3, extractBallB2,
    evalQ3G, evalB2G, evalQ3U, evalB2U, q3LocalBool, b2LocalBool] at hdiff
  have hz : q4ScoreGauged g - q4ScoreUngauged g = 0 := by
    rw [hdiff]
    linear_combination -6 * hL + 6 * hP1 + 4 * hP2
  omega

end PPL033_C6Cert
