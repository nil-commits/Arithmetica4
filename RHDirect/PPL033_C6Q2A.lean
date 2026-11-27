/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import RHDirect.PPL033_C6Base

/-!
# PPL 033 — `Q_2` Dot-Product Shift Checks (0..4)
-/

namespace PPL033_C6Cert

private def checkQ2_0_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift0 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨0, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_0_f : checkQ2_0_s false = true := by decide
private lemma checkQ2_0_t : checkQ2_0_s true = true := by decide
lemma checkQ2_0_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift0 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨0, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_0_s a4 = true := by cases a4 with | false => exact checkQ2_0_f | true => exact checkQ2_0_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

private def checkQ2_1_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift1 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨1, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_1_f : checkQ2_1_s false = true := by decide
private lemma checkQ2_1_t : checkQ2_1_s true = true := by decide
lemma checkQ2_1_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift1 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨1, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_1_s a4 = true := by cases a4 with | false => exact checkQ2_1_f | true => exact checkQ2_1_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

private def checkQ2_2_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift2 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨2, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_2_f : checkQ2_2_s false = true := by decide
private lemma checkQ2_2_t : checkQ2_2_s true = true := by decide
lemma checkQ2_2_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift2 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨2, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_2_s a4 = true := by cases a4 with | false => exact checkQ2_2_f | true => exact checkQ2_2_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

private def checkQ2_3_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift3 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨3, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_3_f : checkQ2_3_s false = true := by decide
private lemma checkQ2_3_t : checkQ2_3_s true = true := by decide
lemma checkQ2_3_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift3 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨3, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_3_s a4 = true := by cases a4 with | false => exact checkQ2_3_f | true => exact checkQ2_3_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

private def checkQ2_4_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift4 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨4, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_4_f : checkQ2_4_s false = true := by decide
private lemma checkQ2_4_t : checkQ2_4_s true = true := by decide
lemma checkQ2_4_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift4 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨4, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_4_s a4 = true := by cases a4 with | false => exact checkQ2_4_f | true => exact checkQ2_4_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

end PPL033_C6Cert
