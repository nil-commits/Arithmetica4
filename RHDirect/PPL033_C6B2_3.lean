/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import RHDirect.PPL033_C6Base

/-!
# PPL 033 — `B_2(Q_4)` Star-Orbit 0111 Exhaustive Bounds
-/

namespace PPL033_C6Cert

private def checkB2_0111_s (b13 b15 b19 b23 : Bool) : Bool :=
  [false, true].all fun b26 => [false, true].all fun b2a => [false, true].all fun b45 => [false, true].all fun b46 => [false, true].all fun b4c => [false, true].all fun b89 => [false, true].all fun b8a => [false, true].all fun b8c =>
    checkB2Step false true true true b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c
private lemma checkB2_0111_00 : checkB2_0111_s false false false false = true := by decide
private lemma checkB2_0111_01 : checkB2_0111_s false false false true = true := by decide
private lemma checkB2_0111_02 : checkB2_0111_s false false true false = true := by decide
private lemma checkB2_0111_03 : checkB2_0111_s false false true true = true := by decide
private lemma checkB2_0111_04 : checkB2_0111_s false true false false = true := by decide
private lemma checkB2_0111_05 : checkB2_0111_s false true false true = true := by decide
private lemma checkB2_0111_06 : checkB2_0111_s false true true false = true := by decide
private lemma checkB2_0111_07 : checkB2_0111_s false true true true = true := by decide
private lemma checkB2_0111_08 : checkB2_0111_s true false false false = true := by decide
private lemma checkB2_0111_09 : checkB2_0111_s true false false true = true := by decide
private lemma checkB2_0111_10 : checkB2_0111_s true false true false = true := by decide
private lemma checkB2_0111_11 : checkB2_0111_s true false true true = true := by decide
private lemma checkB2_0111_12 : checkB2_0111_s true true false false = true := by decide
private lemma checkB2_0111_13 : checkB2_0111_s true true false true = true := by decide
private lemma checkB2_0111_14 : checkB2_0111_s true true true false = true := by decide
private lemma checkB2_0111_15 : checkB2_0111_s true true true true = true := by decide

lemma b2_sorted_0111 (b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c : Bool)
    (hc : b2IsC6FreeBool false true true true b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c = true) :
    124000000 ≤ b2PosShift false true true true b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c ∧
    b2PosShift false true true true b13 b15 b19 b23 b26 b2a b45 b46 b4c b89 b8a b8c ≤ M4_shift + 124000000 := by
  have hs : checkB2_0111_s b13 b15 b19 b23 = true := by
    cases b13 <;> cases b15 <;> cases b19 <;> cases b23
    · exact checkB2_0111_00
    · exact checkB2_0111_01
    · exact checkB2_0111_02
    · exact checkB2_0111_03
    · exact checkB2_0111_04
    · exact checkB2_0111_05
    · exact checkB2_0111_06
    · exact checkB2_0111_07
    · exact checkB2_0111_08
    · exact checkB2_0111_09
    · exact checkB2_0111_10
    · exact checkB2_0111_11
    · exact checkB2_0111_12
    · exact checkB2_0111_13
    · exact checkB2_0111_14
    · exact checkB2_0111_15
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs b26) b2a) b45) b46) b4c) b89) b8a) b8c)
  simp only [checkB2Step, hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h; exact h

end PPL033_C6Cert
