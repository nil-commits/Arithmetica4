/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import RHDirect.PPL033_C6Base

/-!
# PPL 033 — `Q_2` Dot-Product Shift Checks (5..9)
-/

namespace PPL033_C6Cert

private def checkQ2_5_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift5 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨5, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_5_f : checkQ2_5_s false = true := by decide
private lemma checkQ2_5_t : checkQ2_5_s true = true := by decide
lemma checkQ2_5_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift5 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨5, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_5_s a4 = true := by cases a4 with | false => exact checkQ2_5_f | true => exact checkQ2_5_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

private def checkQ2_6_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift6 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨6, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_6_f : checkQ2_6_s false = true := by decide
private lemma checkQ2_6_t : checkQ2_6_s true = true := by decide
lemma checkQ2_6_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift6 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨6, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_6_s a4 = true := by cases a4 with | false => exact checkQ2_6_f | true => exact checkQ2_6_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

private def checkQ2_7_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift7 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨7, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_7_f : checkQ2_7_s false = true := by decide
private lemma checkQ2_7_t : checkQ2_7_s true = true := by decide
lemma checkQ2_7_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift7 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨7, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_7_s a4 = true := by cases a4 with | false => exact checkQ2_7_f | true => exact checkQ2_7_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

private def checkQ2_8_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift8 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨8, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_8_f : checkQ2_8_s false = true := by decide
private lemma checkQ2_8_t : checkQ2_8_s true = true := by decide
lemma checkQ2_8_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift8 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨8, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_8_s a4 = true := by cases a4 with | false => exact checkQ2_8_f | true => exact checkQ2_8_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

private def checkQ2_9_s (a4 : Bool) : Bool :=
  [false, true].all fun a3 => [false, true].all fun a2 =>
  [false, true].all fun a1 => [false, true].all fun a0 =>
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide ((q2DotShift9 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨9, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 9 b4 b3 b2 b1 b0))
private lemma checkQ2_9_f : checkQ2_9_s false = true := by decide
private lemma checkQ2_9_t : checkQ2_9_s true = true := by decide
lemma checkQ2_9_ok (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) :
    (q2DotShift9 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 1000000 + (q2W ⟨9, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 1 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 3 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 5 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 7 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 8 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 8 b4 b3 b2 b1 b0 + q2W ⟨9, by decide⟩ 9 a4 a3 a2 a1 a0 * q2W ⟨9, by decide⟩ 9 b4 b3 b2 b1 b0) := by
  have hs : checkQ2_9_s a4 = true := by cases a4 with | false => exact checkQ2_9_f | true => exact checkQ2_9_t
  have h := (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs a3) a2) a1) a0) b4) b3) b2) b1) b0)
  simp only [decide_eq_true_eq] at h; exact h

end PPL033_C6Cert
