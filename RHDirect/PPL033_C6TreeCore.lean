/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import RHDirect.PPL033_C6Lookup
import Mathlib.Tactic.FinCases

/-!
# PPL 033 — `C_6` Fast Strict-Normal-Form Branch-and-Bound Certificate Core & Soundness Theorem

Zero `sorry`, zero custom axioms, zero `native_decide`.
-/

namespace PPL033_C6Cert

inductive Tri | z | o | u deriving DecidableEq

def isTriO : Tri → Bool | .o => true | _ => false
def isTriU : Tri → Bool | .u => true | _ => false

lemma eq_o_of_isTriO {t : Tri} (h : isTriO t = true) : t = .o := by
  cases t <;> first | rfl | exact absurd h (by decide)

lemma isTriU_false_of_not_u {t : Tri} (h : isTriU t = false) : t ≠ .u := by
  intro hu; subst hu; simp [isTriU] at h

def matchTri : Tri → Bool → Prop
  | .z, b => b = false
  | .o, b => b = true
  | .u, _ => True

def natMax (a b : ℕ) : ℕ := if Nat.ble a b then b else a

private lemma le_natMax_left (a b : ℕ) : a ≤ natMax a b := by
  unfold natMax
  cases h : Nat.ble a b with
  | true => exact Nat.le_of_ble_eq_true h
  | false => exact le_refl a

private lemma le_natMax_right (a b : ℕ) : b ≤ natMax a b := by
  unfold natMax
  by_cases h : Nat.ble a b = true
  · rw [if_pos h]
  · have hlt : b < a := Nat.lt_of_not_le (fun hle => h (Nat.ble_eq_true_of_le hle))
    rw [if_neg h]; omega

def max1 (t : Tri) (f : Bool → ℕ) : ℕ :=
  match t with | .z => f false | .o => f true | .u => natMax (f false) (f true)

lemma le_max1 (t : Tri) (b : Bool) (f : Bool → ℕ) (hm : matchTri t b) : f b ≤ max1 t f := by
  cases t with
  | z => simp only [matchTri] at hm; subst hm; rfl
  | o => simp only [matchTri] at hm; subst hm; rfl
  | u => cases b with | false => exact le_natMax_left _ _ | true => exact le_natMax_right _ _

lemma max1_eq_of_isTriU_false (t : Tri) (b : Bool) (f : Bool → ℕ) (hm : matchTri t b) (hu : isTriU t = false) :
    max1 t f = f b := by
  cases t with
  | z => simp only [matchTri] at hm; subst hm; rfl
  | o => simp only [matchTri] at hm; subst hm; rfl
  | u => simp [isTriU] at hu

structure State8 where
  t0 : Tri
  t1 : Tri
  t2 : Tri
  t3 : Tri
  t4 : Tri
  t5 : Tri
  t6 : Tri
  t7 : Tri
  deriving DecidableEq

structure State32 where
  b0 : State8
  b1 : State8
  b2 : State8
  b3 : State8
  deriving DecidableEq

def getE (st : State32) (e : ℕ) : Tri :=
  match e with
  | 0 => st.b0.t0
  | 1 => st.b0.t1
  | 2 => st.b0.t2
  | 3 => st.b0.t3
  | 4 => st.b0.t4
  | 5 => st.b0.t5
  | 6 => st.b0.t6
  | 7 => st.b0.t7
  | 8 => st.b1.t0
  | 9 => st.b1.t1
  | 10 => st.b1.t2
  | 11 => st.b1.t3
  | 12 => st.b1.t4
  | 13 => st.b1.t5
  | 14 => st.b1.t6
  | 15 => st.b1.t7
  | 16 => st.b2.t0
  | 17 => st.b2.t1
  | 18 => st.b2.t2
  | 19 => st.b2.t3
  | 20 => st.b2.t4
  | 21 => st.b2.t5
  | 22 => st.b2.t6
  | 23 => st.b2.t7
  | 24 => st.b3.t0
  | 25 => st.b3.t1
  | 26 => st.b3.t2
  | 27 => st.b3.t3
  | 28 => st.b3.t4
  | 29 => st.b3.t5
  | 30 => st.b3.t6
  | 31 => st.b3.t7
  | _ => .u

def setE (st : State32) (e : ℕ) (v : Tri) : State32 :=
  let ⟨b0, b1, b2, b3⟩ := st
  match e with
  | 0 => let ⟨_, t1, t2, t3, t4, t5, t6, t7⟩ := b0; ⟨⟨v, t1, t2, t3, t4, t5, t6, t7⟩, b1, b2, b3⟩
  | 1 => let ⟨t0, _, t2, t3, t4, t5, t6, t7⟩ := b0; ⟨⟨t0, v, t2, t3, t4, t5, t6, t7⟩, b1, b2, b3⟩
  | 2 => let ⟨t0, t1, _, t3, t4, t5, t6, t7⟩ := b0; ⟨⟨t0, t1, v, t3, t4, t5, t6, t7⟩, b1, b2, b3⟩
  | 3 => let ⟨t0, t1, t2, _, t4, t5, t6, t7⟩ := b0; ⟨⟨t0, t1, t2, v, t4, t5, t6, t7⟩, b1, b2, b3⟩
  | 4 => let ⟨t0, t1, t2, t3, _, t5, t6, t7⟩ := b0; ⟨⟨t0, t1, t2, t3, v, t5, t6, t7⟩, b1, b2, b3⟩
  | 5 => let ⟨t0, t1, t2, t3, t4, _, t6, t7⟩ := b0; ⟨⟨t0, t1, t2, t3, t4, v, t6, t7⟩, b1, b2, b3⟩
  | 6 => let ⟨t0, t1, t2, t3, t4, t5, _, t7⟩ := b0; ⟨⟨t0, t1, t2, t3, t4, t5, v, t7⟩, b1, b2, b3⟩
  | 7 => let ⟨t0, t1, t2, t3, t4, t5, t6, _⟩ := b0; ⟨⟨t0, t1, t2, t3, t4, t5, t6, v⟩, b1, b2, b3⟩
  | 8 => let ⟨_, t1, t2, t3, t4, t5, t6, t7⟩ := b1; ⟨b0, ⟨v, t1, t2, t3, t4, t5, t6, t7⟩, b2, b3⟩
  | 9 => let ⟨t0, _, t2, t3, t4, t5, t6, t7⟩ := b1; ⟨b0, ⟨t0, v, t2, t3, t4, t5, t6, t7⟩, b2, b3⟩
  | 10 => let ⟨t0, t1, _, t3, t4, t5, t6, t7⟩ := b1; ⟨b0, ⟨t0, t1, v, t3, t4, t5, t6, t7⟩, b2, b3⟩
  | 11 => let ⟨t0, t1, t2, _, t4, t5, t6, t7⟩ := b1; ⟨b0, ⟨t0, t1, t2, v, t4, t5, t6, t7⟩, b2, b3⟩
  | 12 => let ⟨t0, t1, t2, t3, _, t5, t6, t7⟩ := b1; ⟨b0, ⟨t0, t1, t2, t3, v, t5, t6, t7⟩, b2, b3⟩
  | 13 => let ⟨t0, t1, t2, t3, t4, _, t6, t7⟩ := b1; ⟨b0, ⟨t0, t1, t2, t3, t4, v, t6, t7⟩, b2, b3⟩
  | 14 => let ⟨t0, t1, t2, t3, t4, t5, _, t7⟩ := b1; ⟨b0, ⟨t0, t1, t2, t3, t4, t5, v, t7⟩, b2, b3⟩
  | 15 => let ⟨t0, t1, t2, t3, t4, t5, t6, _⟩ := b1; ⟨b0, ⟨t0, t1, t2, t3, t4, t5, t6, v⟩, b2, b3⟩
  | 16 => let ⟨_, t1, t2, t3, t4, t5, t6, t7⟩ := b2; ⟨b0, b1, ⟨v, t1, t2, t3, t4, t5, t6, t7⟩, b3⟩
  | 17 => let ⟨t0, _, t2, t3, t4, t5, t6, t7⟩ := b2; ⟨b0, b1, ⟨t0, v, t2, t3, t4, t5, t6, t7⟩, b3⟩
  | 18 => let ⟨t0, t1, _, t3, t4, t5, t6, t7⟩ := b2; ⟨b0, b1, ⟨t0, t1, v, t3, t4, t5, t6, t7⟩, b3⟩
  | 19 => let ⟨t0, t1, t2, _, t4, t5, t6, t7⟩ := b2; ⟨b0, b1, ⟨t0, t1, t2, v, t4, t5, t6, t7⟩, b3⟩
  | 20 => let ⟨t0, t1, t2, t3, _, t5, t6, t7⟩ := b2; ⟨b0, b1, ⟨t0, t1, t2, t3, v, t5, t6, t7⟩, b3⟩
  | 21 => let ⟨t0, t1, t2, t3, t4, _, t6, t7⟩ := b2; ⟨b0, b1, ⟨t0, t1, t2, t3, t4, v, t6, t7⟩, b3⟩
  | 22 => let ⟨t0, t1, t2, t3, t4, t5, _, t7⟩ := b2; ⟨b0, b1, ⟨t0, t1, t2, t3, t4, t5, v, t7⟩, b3⟩
  | 23 => let ⟨t0, t1, t2, t3, t4, t5, t6, _⟩ := b2; ⟨b0, b1, ⟨t0, t1, t2, t3, t4, t5, t6, v⟩, b3⟩
  | 24 => let ⟨_, t1, t2, t3, t4, t5, t6, t7⟩ := b3; ⟨b0, b1, b2, ⟨v, t1, t2, t3, t4, t5, t6, t7⟩⟩
  | 25 => let ⟨t0, _, t2, t3, t4, t5, t6, t7⟩ := b3; ⟨b0, b1, b2, ⟨t0, v, t2, t3, t4, t5, t6, t7⟩⟩
  | 26 => let ⟨t0, t1, _, t3, t4, t5, t6, t7⟩ := b3; ⟨b0, b1, b2, ⟨t0, t1, v, t3, t4, t5, t6, t7⟩⟩
  | 27 => let ⟨t0, t1, t2, _, t4, t5, t6, t7⟩ := b3; ⟨b0, b1, b2, ⟨t0, t1, t2, v, t4, t5, t6, t7⟩⟩
  | 28 => let ⟨t0, t1, t2, t3, _, t5, t6, t7⟩ := b3; ⟨b0, b1, b2, ⟨t0, t1, t2, t3, v, t5, t6, t7⟩⟩
  | 29 => let ⟨t0, t1, t2, t3, t4, _, t6, t7⟩ := b3; ⟨b0, b1, b2, ⟨t0, t1, t2, t3, t4, v, t6, t7⟩⟩
  | 30 => let ⟨t0, t1, t2, t3, t4, t5, _, t7⟩ := b3; ⟨b0, b1, b2, ⟨t0, t1, t2, t3, t4, t5, v, t7⟩⟩
  | 31 => let ⟨t0, t1, t2, t3, t4, t5, t6, _⟩ := b3; ⟨b0, b1, b2, ⟨t0, t1, t2, t3, t4, t5, t6, v⟩⟩
  | _ => ⟨b0, b1, b2, b3⟩

private lemma getE_setE (st : State32) (e e' : Fin 32) (v : Tri) :
    getE (setE st e.val v) e'.val = if e' = e then v else getE st e'.val := by
  rcases st with ⟨b0, b1, b2, b3⟩
  rcases b0 with ⟨t00, t01, t02, t03, t04, t05, t06, t07⟩
  rcases b1 with ⟨t10, t11, t12, t13, t14, t15, t16, t17⟩
  rcases b2 with ⟨t20, t21, t22, t23, t24, t25, t26, t27⟩
  rcases b3 with ⟨t30, t31, t32, t33, t34, t35, t36, t37⟩
  fin_cases e <;> fin_cases e' <;> rfl

lemma getE_setE_self (st : State32) (e : Fin 32) (v : Tri) : getE (setE st e.val v) e.val = v := by
  rw [getE_setE]; simp

lemma getE_setE_ne (st : State32) {e e' : Fin 32} (hne : e' ≠ e) (v : Tri) :
    getE (setE st e.val v) e'.val = getE st e'.val := by
  rw [getE_setE, if_neg hne]

structure UbF7 where
  u0 : ℕ
  u1 : ℕ
  u2 : ℕ
  u3 : ℕ
  u4 : ℕ
  u5 : ℕ
  u7 : ℕ
  deriving DecidableEq

def getUbF (u : UbF7) (fk : ℕ) : ℕ :=
  match fk with | 0 => u.u0 | 1 => u.u1 | 2 => u.u2 | 3 => u.u3 | 4 => u.u4 | 5 => u.u5 | 7 => u.u7 | _ => 0

def setUbF (u : UbF7) (fk : ℕ) (v : ℕ) : UbF7 :=
  let ⟨u0, u1, u2, u3, u4, u5, u7⟩ := u
  match fk with
  | 0 => ⟨v, u1, u2, u3, u4, u5, u7⟩ | 1 => ⟨u0, v, u2, u3, u4, u5, u7⟩ | 2 => ⟨u0, u1, v, u3, u4, u5, u7⟩ | 3 => ⟨u0, u1, u2, v, u4, u5, u7⟩
  | 4 => ⟨u0, u1, u2, u3, v, u5, u7⟩ | 5 => ⟨u0, u1, u2, u3, u4, v, u7⟩ | 7 => ⟨u0, u1, u2, u3, u4, u5, v⟩ | _ => ⟨u0, u1, u2, u3, u4, u5, u7⟩

def ubFSum (u : UbF7) : ℕ := u.u0 + u.u1 + u.u2 + u.u3 + u.u4 + u.u5 + u.u7

lemma ubFSum_setUbF (u : UbF7) (fk : Fin 8) (hne6 : fk.val ≠ 6) (mx : ℕ) (hlt : mx < getUbF u fk.val) :
    ubFSum (setUbF u fk.val mx) + (getUbF u fk.val - mx) = ubFSum u := by
  rcases u with ⟨u0, u1, u2, u3, u4, u5, u7⟩
  fin_cases fk <;> simp [ubFSum, setUbF, getUbF] at hne6 hlt ⊢ <;> omega

lemma getUbF_setUbF_self (u : UbF7) (fk : Fin 8) (hne6 : fk.val ≠ 6) (v : ℕ) : getUbF (setUbF u fk.val v) fk.val = v := by
  rcases u with ⟨u0, u1, u2, u3, u4, u5, u7⟩
  fin_cases fk <;> simp [getUbF, setUbF] at hne6 ⊢

lemma getUbF_setUbF_ne (u : UbF7) {fk fk' : Fin 8} (hne : fk' ≠ fk) (v : ℕ) : getUbF (setUbF u fk.val v) fk'.val = getUbF u fk'.val := by
  rcases u with ⟨u0, u1, u2, u3, u4, u5, u7⟩
  fin_cases fk <;> fin_cases fk' <;> simp [getUbF, setUbF] at hne ⊢

structure UbB8 where
  n0 : ℕ
  n1 : ℕ
  n2 : ℕ
  n3 : ℕ
  n4 : ℕ
  n5 : ℕ
  n6 : ℕ
  n7 : ℕ
  deriving DecidableEq

structure UbB16 where
  lo : UbB8
  hi : UbB8
  deriving DecidableEq

def getUbB (u : UbB16) (bi : ℕ) : ℕ :=
  match bi with
  | 0 => u.lo.n0
  | 1 => u.lo.n1
  | 2 => u.lo.n2
  | 3 => u.lo.n3
  | 4 => u.lo.n4
  | 5 => u.lo.n5
  | 6 => u.lo.n6
  | 7 => u.lo.n7
  | 8 => u.hi.n0
  | 9 => u.hi.n1
  | 10 => u.hi.n2
  | 11 => u.hi.n3
  | 12 => u.hi.n4
  | 13 => u.hi.n5
  | 14 => u.hi.n6
  | 15 => u.hi.n7
  | _ => 0

def setUbB (u : UbB16) (bi : ℕ) (v : ℕ) : UbB16 :=
  let ⟨lo, hi⟩ := u
  match bi with
  | 0 => let ⟨_, n1, n2, n3, n4, n5, n6, n7⟩ := lo; ⟨⟨v, n1, n2, n3, n4, n5, n6, n7⟩, hi⟩
  | 1 => let ⟨n0, _, n2, n3, n4, n5, n6, n7⟩ := lo; ⟨⟨n0, v, n2, n3, n4, n5, n6, n7⟩, hi⟩
  | 2 => let ⟨n0, n1, _, n3, n4, n5, n6, n7⟩ := lo; ⟨⟨n0, n1, v, n3, n4, n5, n6, n7⟩, hi⟩
  | 3 => let ⟨n0, n1, n2, _, n4, n5, n6, n7⟩ := lo; ⟨⟨n0, n1, n2, v, n4, n5, n6, n7⟩, hi⟩
  | 4 => let ⟨n0, n1, n2, n3, _, n5, n6, n7⟩ := lo; ⟨⟨n0, n1, n2, n3, v, n5, n6, n7⟩, hi⟩
  | 5 => let ⟨n0, n1, n2, n3, n4, _, n6, n7⟩ := lo; ⟨⟨n0, n1, n2, n3, n4, v, n6, n7⟩, hi⟩
  | 6 => let ⟨n0, n1, n2, n3, n4, n5, _, n7⟩ := lo; ⟨⟨n0, n1, n2, n3, n4, n5, v, n7⟩, hi⟩
  | 7 => let ⟨n0, n1, n2, n3, n4, n5, n6, _⟩ := lo; ⟨⟨n0, n1, n2, n3, n4, n5, n6, v⟩, hi⟩
  | 8 => let ⟨_, n1, n2, n3, n4, n5, n6, n7⟩ := hi; ⟨lo, ⟨v, n1, n2, n3, n4, n5, n6, n7⟩⟩
  | 9 => let ⟨n0, _, n2, n3, n4, n5, n6, n7⟩ := hi; ⟨lo, ⟨n0, v, n2, n3, n4, n5, n6, n7⟩⟩
  | 10 => let ⟨n0, n1, _, n3, n4, n5, n6, n7⟩ := hi; ⟨lo, ⟨n0, n1, v, n3, n4, n5, n6, n7⟩⟩
  | 11 => let ⟨n0, n1, n2, _, n4, n5, n6, n7⟩ := hi; ⟨lo, ⟨n0, n1, n2, v, n4, n5, n6, n7⟩⟩
  | 12 => let ⟨n0, n1, n2, n3, _, n5, n6, n7⟩ := hi; ⟨lo, ⟨n0, n1, n2, n3, v, n5, n6, n7⟩⟩
  | 13 => let ⟨n0, n1, n2, n3, n4, _, n6, n7⟩ := hi; ⟨lo, ⟨n0, n1, n2, n3, n4, v, n6, n7⟩⟩
  | 14 => let ⟨n0, n1, n2, n3, n4, n5, _, n7⟩ := hi; ⟨lo, ⟨n0, n1, n2, n3, n4, n5, v, n7⟩⟩
  | 15 => let ⟨n0, n1, n2, n3, n4, n5, n6, _⟩ := hi; ⟨lo, ⟨n0, n1, n2, n3, n4, n5, n6, v⟩⟩
  | _ => ⟨lo, hi⟩

def sumB8 (u : UbB8) : ℕ := u.n0 + u.n1 + u.n2 + u.n3 + u.n4 + u.n5 + u.n6 + u.n7
def ubBSum (u : UbB16) : ℕ := sumB8 u.lo + sumB8 u.hi

lemma ubBSum_setUbB (u : UbB16) (bi : Fin 16) (mx : ℕ) (hlt : mx < getUbB u bi.val) :
    ubBSum (setUbB u bi.val mx) + (getUbB u bi.val - mx) = ubBSum u := by
  rcases u with ⟨⟨n0, n1, n2, n3, n4, n5, n6, n7⟩, ⟨m0, m1, m2, m3, m4, m5, m6, m7⟩⟩
  fin_cases bi <;> simp [ubBSum, sumB8, setUbB, getUbB] at hlt ⊢ <;> omega

private lemma getUbB_setUbB (u : UbB16) (bi bi' : Fin 16) (v : ℕ) :
    getUbB (setUbB u bi.val v) bi'.val = if bi' = bi then v else getUbB u bi'.val := by
  rcases u with ⟨⟨n0, n1, n2, n3, n4, n5, n6, n7⟩, ⟨m0, m1, m2, m3, m4, m5, m6, m7⟩⟩
  fin_cases bi <;> fin_cases bi' <;> rfl

lemma getUbB_setUbB_self (u : UbB16) (bi : Fin 16) (v : ℕ) : getUbB (setUbB u bi.val v) bi.val = v := by
  rw [getUbB_setUbB]; simp

lemma getUbB_setUbB_ne (u : UbB16) {bi bi' : Fin 16} (hne : bi' ≠ bi) (v : ℕ) :
    getUbB (setUbB u bi.val v) bi'.val = getUbB u bi'.val := by
  rw [getUbB_setUbB, if_neg hne]

def getQ4E (g : Q4Bits) (e : Fin 32) : Bool :=
  (if e.val < 16 then (if e.val < 8 then (if e.val < 4 then (if e.val < 2 then (if e.val < 1 then g.q00 else g.q01) else (if e.val < 3 then g.q02 else g.q03)) else (if e.val < 6 then (if e.val < 5 then g.q04 else g.q05) else (if e.val < 7 then g.q06 else g.q07))) else (if e.val < 12 then (if e.val < 10 then (if e.val < 9 then g.q08 else g.q09) else (if e.val < 11 then g.q10 else g.q11)) else (if e.val < 14 then (if e.val < 13 then g.q12 else g.q13) else (if e.val < 15 then g.q14 else g.q15)))) else (if e.val < 24 then (if e.val < 20 then (if e.val < 18 then (if e.val < 17 then g.q16 else g.q17) else (if e.val < 19 then g.q18 else g.q19)) else (if e.val < 22 then (if e.val < 21 then g.q20 else g.q21) else (if e.val < 23 then g.q22 else g.q23))) else (if e.val < 28 then (if e.val < 26 then (if e.val < 25 then g.q24 else g.q25) else (if e.val < 27 then g.q26 else g.q27)) else (if e.val < 30 then (if e.val < 29 then g.q28 else g.q29) else (if e.val < 31 then g.q30 else g.q31)))))

def c6CyclesQ4 (cid : Fin 128) : Fin 32 × Fin 32 × Fin 32 × Fin 32 × Fin 32 × Fin 32 :=
  (if cid.val < 64 then (if cid.val < 32 then (if cid.val < 16 then (if cid.val < 8 then (if cid.val < 4 then (if cid.val < 2 then (if cid.val < 1 then (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨22, by decide⟩, ⟨28, by decide⟩) else (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨17, by decide⟩)) else (if cid.val < 3 then (⟨7, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩) else (⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩))) else (if cid.val < 6 then (if cid.val < 5 then (⟨15, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩) else (⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩)) else (if cid.val < 7 then (⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩) else (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨11, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩)))) else (if cid.val < 12 then (if cid.val < 10 then (if cid.val < 9 then (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩) else (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨22, by decide⟩, ⟨29, by decide⟩)) else (if cid.val < 11 then (⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩) else (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩))) else (if cid.val < 14 then (if cid.val < 13 then (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨20, by decide⟩) else (⟨4, by decide⟩, ⟨5, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨27, by decide⟩)) else (if cid.val < 15 then (⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩) else (⟨4, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨24, by decide⟩))))) else (if cid.val < 24 then (if cid.val < 20 then (if cid.val < 18 then (if cid.val < 17 then (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨14, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩) else (⟨4, by decide⟩, ⟨6, by decide⟩, ⟨11, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩)) else (if cid.val < 19 then (⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩) else (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩))) else (if cid.val < 22 then (if cid.val < 21 then (⟨8, by decide⟩, ⟨9, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩) else (⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩)) else (if cid.val < 23 then (⟨7, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ⟨18, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩) else (⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩)))) else (if cid.val < 28 then (if cid.val < 26 then (if cid.val < 25 then (⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩) else (⟨4, by decide⟩, ⟨6, by decide⟩, ⟨11, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩)) else (if cid.val < 27 then (⟨12, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩) else (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨8, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨29, by decide⟩))) else (if cid.val < 30 then (if cid.val < 29 then (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨18, by decide⟩, ⟨22, by decide⟩, ⟨29, by decide⟩) else (⟨7, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩)) else (if cid.val < 31 then (⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩) else (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩)))))) else (if cid.val < 48 then (if cid.val < 40 then (if cid.val < 36 then (if cid.val < 34 then (if cid.val < 33 then (⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩) else (⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩)) else (if cid.val < 35 then (⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩) else (⟨7, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩))) else (if cid.val < 38 then (if cid.val < 37 then (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩) else (⟨10, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩)) else (if cid.val < 39 then (⟨7, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨31, by decide⟩) else (⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨31, by decide⟩)))) else (if cid.val < 44 then (if cid.val < 42 then (if cid.val < 41 then (⟨21, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩) else (⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩)) else (if cid.val < 43 then (⟨12, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨29, by decide⟩) else (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩))) else (if cid.val < 46 then (if cid.val < 45 then (⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩) else (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨21, by decide⟩)) else (if cid.val < 47 then (⟨8, by decide⟩, ⟨9, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨29, by decide⟩) else (⟨8, by decide⟩, ⟨9, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩))))) else (if cid.val < 56 then (if cid.val < 52 then (if cid.val < 50 then (if cid.val < 49 then (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨9, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩) else (⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩)) else (if cid.val < 51 then (⟨4, by decide⟩, ⟨5, by decide⟩, ⟨11, by decide⟩, ⟨16, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩) else (⟨8, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩))) else (if cid.val < 54 then (if cid.val < 53 then (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨12, by decide⟩) else (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩)) else (if cid.val < 55 then (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩) else (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩)))) else (if cid.val < 60 then (if cid.val < 58 then (if cid.val < 57 then (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩) else (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩)) else (if cid.val < 59 then (⟨20, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩) else (⟨12, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩))) else (if cid.val < 62 then (if cid.val < 61 then (⟨10, by decide⟩, ⟨11, by decide⟩, ⟨19, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩) else (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨17, by decide⟩)) else (if cid.val < 63 then (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨24, by decide⟩) else (⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩))))))) else (if cid.val < 96 then (if cid.val < 80 then (if cid.val < 72 then (if cid.val < 68 then (if cid.val < 66 then (if cid.val < 65 then (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩, ⟨14, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩) else (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨23, by decide⟩)) else (if cid.val < 67 then (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩) else (⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩))) else (if cid.val < 70 then (if cid.val < 69 then (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨22, by decide⟩) else (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩)) else (if cid.val < 71 then (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨21, by decide⟩) else (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩)))) else (if cid.val < 76 then (if cid.val < 74 then (if cid.val < 73 then (⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩) else (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩)) else (if cid.val < 75 then (⟨4, by decide⟩, ⟨5, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨17, by decide⟩) else (⟨10, by decide⟩, ⟨11, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩))) else (if cid.val < 78 then (if cid.val < 77 then (⟨7, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨27, by decide⟩) else (⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨25, by decide⟩)) else (if cid.val < 79 then (⟨12, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨30, by decide⟩) else (⟨12, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩))))) else (if cid.val < 88 then (if cid.val < 84 then (if cid.val < 82 then (if cid.val < 81 then (⟨4, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩) else (⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩)) else (if cid.val < 83 then (⟨10, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩) else (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩))) else (if cid.val < 86 then (if cid.val < 85 then (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩) else (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩)) else (if cid.val < 87 then (⟨8, by decide⟩, ⟨9, by decide⟩, ⟨18, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩) else (⟨7, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩)))) else (if cid.val < 92 then (if cid.val < 90 then (if cid.val < 89 then (⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩) else (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨9, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩)) else (if cid.val < 91 then (⟨13, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩) else (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨11, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩))) else (if cid.val < 94 then (if cid.val < 93 then (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨22, by decide⟩) else (⟨8, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩)) else (if cid.val < 95 then (⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩) else (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨23, by decide⟩)))))) else (if cid.val < 112 then (if cid.val < 104 then (if cid.val < 100 then (if cid.val < 98 then (if cid.val < 97 then (⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩) else (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨16, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩)) else (if cid.val < 99 then (⟨7, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨26, by decide⟩) else (⟨10, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩))) else (if cid.val < 102 then (if cid.val < 101 then (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨28, by decide⟩) else (⟨15, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩)) else (if cid.val < 103 then (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨17, by decide⟩) else (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩)))) else (if cid.val < 108 then (if cid.val < 106 then (if cid.val < 105 then (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩) else (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨20, by decide⟩)) else (if cid.val < 107 then (⟨12, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩) else (⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩))) else (if cid.val < 110 then (if cid.val < 109 then (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨25, by decide⟩) else (⟨4, by decide⟩, ⟨5, by decide⟩, ⟨10, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨30, by decide⟩)) else (if cid.val < 111 then (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨9, by decide⟩, ⟨14, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩) else (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩))))) else (if cid.val < 120 then (if cid.val < 116 then (if cid.val < 114 then (if cid.val < 113 then (⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩) else (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩)) else (if cid.val < 115 then (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨9, by decide⟩, ⟨14, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩) else (⟨13, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩))) else (if cid.val < 118 then (if cid.val < 117 then (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨28, by decide⟩) else (⟨10, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩)) else (if cid.val < 119 then (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨16, by decide⟩, ⟨22, by decide⟩, ⟨28, by decide⟩) else (⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩)))) else (if cid.val < 124 then (if cid.val < 122 then (if cid.val < 121 then (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨26, by decide⟩) else (⟨4, by decide⟩, ⟨5, by decide⟩, ⟨11, by decide⟩, ⟨16, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩)) else (if cid.val < 123 then (⟨4, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩) else (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩))) else (if cid.val < 126 then (if cid.val < 125 then (⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩) else (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩)) else (if cid.val < 127 then (⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨28, by decide⟩) else (⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩))))))))

def c6CyclesQ4Nat (cid : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  match cid with
  | 0 => (2, 3, 12, 16, 22, 28)
  | 1 => (0, 1, 4, 8, 10, 17)
  | 2 => (7, 9, 10, 19, 26, 31)
  | 3 => (20, 21, 24, 25, 27, 30)
  | 4 => (15, 16, 19, 28, 29, 31)
  | 5 => (15, 16, 17, 18, 30, 31)
  | 6 => (21, 22, 25, 27, 28, 30)
  | 7 => (0, 3, 4, 11, 21, 25)
  | 8 => (5, 6, 15, 19, 23, 27)
  | 9 => (2, 3, 13, 18, 22, 29)
  | 10 => (20, 22, 23, 27, 29, 31)
  | 11 => (0, 1, 6, 9, 23, 25)
  | 12 => (1, 3, 4, 6, 7, 20)
  | 13 => (4, 5, 11, 15, 19, 27)
  | 14 => (23, 24, 27, 28, 29, 31)
  | 15 => (4, 6, 10, 15, 16, 24)
  | 16 => (2, 3, 14, 21, 26, 29)
  | 17 => (4, 6, 11, 24, 27, 30)
  | 18 => (13, 14, 17, 19, 29, 31)
  | 19 => (2, 3, 13, 18, 21, 26)
  | 20 => (8, 9, 17, 19, 25, 27)
  | 21 => (20, 21, 23, 26, 27, 31)
  | 22 => (7, 8, 11, 18, 25, 26)
  | 23 => (17, 18, 19, 25, 26, 27)
  | 24 => (25, 26, 27, 28, 29, 30)
  | 25 => (4, 6, 11, 20, 21, 25)
  | 26 => (12, 13, 16, 18, 30, 31)
  | 27 => (1, 2, 8, 14, 18, 29)
  | 28 => (1, 3, 8, 18, 22, 29)
  | 29 => (7, 8, 11, 18, 27, 31)
  | 30 => (20, 22, 23, 25, 26, 29)
  | 31 => (2, 3, 12, 16, 20, 24)
  | 32 => (23, 24, 25, 26, 28, 29)
  | 33 => (13, 14, 17, 19, 28, 30)
  | 34 => (20, 21, 24, 26, 30, 31)
  | 35 => (7, 9, 10, 19, 25, 27)
  | 36 => (5, 6, 12, 14, 20, 22)
  | 37 => (10, 11, 17, 18, 25, 26)
  | 38 => (7, 8, 10, 18, 19, 31)
  | 39 => (12, 13, 15, 18, 19, 31)
  | 40 => (21, 22, 26, 28, 30, 31)
  | 41 => (7, 9, 11, 26, 27, 31)
  | 42 => (12, 14, 15, 17, 18, 29)
  | 43 => (5, 6, 15, 19, 24, 30)
  | 44 => (23, 24, 25, 26, 30, 31)
  | 45 => (2, 3, 8, 9, 13, 21)
  | 46 => (8, 9, 18, 21, 22, 29)
  | 47 => (8, 9, 17, 19, 26, 31)
  | 48 => (1, 3, 9, 20, 23, 25)
  | 49 => (12, 14, 16, 29, 30, 31)
  | 50 => (4, 5, 11, 16, 23, 24)
  | 51 => (8, 9, 13, 14, 26, 29)
  | 52 => (1, 2, 4, 5, 7, 12)
  | 53 => (2, 3, 14, 20, 24, 28)
  | 54 => (5, 6, 12, 14, 24, 28)
  | 55 => (0, 1, 5, 8, 12, 13)
  | 56 => (0, 1, 5, 7, 10, 15)
  | 57 => (0, 1, 5, 8, 15, 17)
  | 58 => (20, 22, 24, 29, 30, 31)
  | 59 => (12, 14, 15, 19, 28, 30)
  | 60 => (10, 11, 19, 25, 26, 31)
  | 61 => (0, 2, 4, 10, 13, 17)
  | 62 => (0, 2, 6, 12, 16, 24)
  | 63 => (20, 21, 24, 26, 28, 29)
  | 64 => (0, 2, 6, 14, 24, 28)
  | 65 => (0, 1, 6, 7, 11, 23)
  | 66 => (1, 2, 7, 10, 12, 15)
  | 67 => (21, 22, 23, 24, 25, 28)
  | 68 => (1, 3, 8, 13, 14, 22)
  | 69 => (0, 3, 6, 22, 24, 28)
  | 70 => (0, 3, 4, 7, 9, 21)
  | 71 => (0, 2, 6, 14, 20, 22)
  | 72 => (4, 5, 7, 8, 15, 17)
  | 73 => (1, 3, 8, 18, 21, 26)
  | 74 => (4, 5, 10, 12, 13, 17)
  | 75 => (10, 11, 19, 23, 24, 30)
  | 76 => (7, 8, 11, 17, 19, 27)
  | 77 => (8, 9, 10, 11, 17, 25)
  | 78 => (12, 13, 16, 17, 19, 30)
  | 79 => (12, 13, 16, 18, 28, 29)
  | 80 => (4, 6, 10, 19, 24, 30)
  | 81 => (12, 14, 16, 20, 22, 24)
  | 82 => (10, 11, 15, 16, 27, 30)
  | 83 => (0, 2, 4, 7, 8, 13)
  | 84 => (0, 2, 4, 10, 12, 15)
  | 85 => (1, 3, 7, 11, 20, 23)
  | 86 => (8, 9, 18, 25, 27, 31)
  | 87 => (7, 8, 10, 12, 13, 15)
  | 88 => (17, 18, 19, 28, 29, 30)
  | 89 => (1, 3, 9, 22, 26, 29)
  | 90 => (13, 14, 18, 21, 22, 26)
  | 91 => (0, 3, 4, 11, 20, 23)
  | 92 => (0, 3, 5, 12, 14, 22)
  | 93 => (8, 9, 13, 14, 21, 22)
  | 94 => (21, 22, 25, 27, 29, 31)
  | 95 => (5, 6, 10, 11, 15, 23)
  | 96 => (15, 16, 17, 18, 28, 29)
  | 97 => (5, 6, 16, 23, 27, 30)
  | 98 => (7, 9, 10, 17, 18, 26)
  | 99 => (10, 11, 17, 18, 27, 31)
  | 100 => (5, 6, 16, 20, 22, 28)
  | 101 => (15, 16, 19, 23, 24, 27)
  | 102 => (1, 2, 7, 10, 13, 17)
  | 103 => (1, 2, 8, 12, 15, 17)
  | 104 => (0, 2, 5, 13, 15, 17)
  | 105 => (2, 3, 5, 6, 12, 20)
  | 106 => (12, 14, 15, 19, 29, 31)
  | 107 => (7, 9, 11, 20, 21, 23)
  | 108 => (0, 1, 4, 9, 11, 25)
  | 109 => (4, 5, 10, 16, 19, 30)
  | 110 => (1, 2, 9, 14, 21, 22)
  | 111 => (0, 3, 6, 21, 23, 25)
  | 112 => (4, 6, 7, 9, 20, 21)
  | 113 => (0, 3, 5, 16, 20, 24)
  | 114 => (1, 2, 9, 14, 26, 29)
  | 115 => (13, 14, 18, 28, 30, 31)
  | 116 => (0, 2, 5, 14, 16, 28)
  | 117 => (10, 11, 15, 16, 23, 24)
  | 118 => (0, 3, 5, 16, 22, 28)
  | 119 => (20, 22, 23, 27, 28, 30)
  | 120 => (1, 2, 9, 13, 18, 26)
  | 121 => (4, 5, 11, 16, 27, 30)
  | 122 => (4, 6, 10, 19, 23, 27)
  | 123 => (1, 3, 7, 11, 21, 25)
  | 124 => (4, 5, 7, 8, 12, 13)
  | 125 => (0, 1, 6, 9, 20, 21)
  | 126 => (13, 14, 15, 16, 17, 28)
  | 127 => (4, 6, 7, 9, 23, 25)
  | _ => (0, 0, 0, 0, 0, 0)

lemma c6CyclesQ4Nat_eq (cid : Fin 128) :
    c6CyclesQ4Nat cid.val = let (a,b,c,d,e,f) := c6CyclesQ4 cid; (a.val, b.val, c.val, d.val, e.val, f.val) := by
  fin_cases cid <;> rfl

def isQ4C6Free (g : Q4Bits) : Prop :=
  ∀ cid : Fin 128, let (e0, e1, e2, e3, e4, e5) := c6CyclesQ4 cid
  ¬ (getQ4E g e0 = true ∧ getQ4E g e1 = true ∧ getQ4E g e2 = true ∧ getQ4E g e3 = true ∧ getQ4E g e4 = true ∧ getQ4E g e5 = true)

def getQ3Edge (q : Q3Bits) (k : Fin 12) : Bool :=
  match k.val with | 0 => q.e01 | 1 => q.e02 | 2 => q.e04 | 3 => q.e13 | 4 => q.e15 | 5 => q.e23 | 6 => q.e26 | 7 => q.e37 | 8 => q.e45 | 9 => q.e46 | 10 => q.e57 | _ => q.e67
def facetEdge (fk : Fin 8) (k : Fin 12) : Fin 32 :=
  match fk.val with
  | 0 => (if k.val < 6 then (if k.val < 3 then (if k.val < 1 then ⟨1, by decide⟩ else (if k.val < 2 then ⟨2, by decide⟩ else ⟨3, by decide⟩)) else (if k.val < 4 then ⟨8, by decide⟩ else (if k.val < 5 then ⟨9, by decide⟩ else ⟨13, by decide⟩))) else (if k.val < 9 then (if k.val < 7 then ⟨14, by decide⟩ else (if k.val < 8 then ⟨18, by decide⟩ else ⟨21, by decide⟩)) else (if k.val < 10 then ⟨22, by decide⟩ else (if k.val < 11 then ⟨26, by decide⟩ else ⟨29, by decide⟩))))
  | 1 => (if k.val < 6 then (if k.val < 3 then (if k.val < 1 then ⟨4, by decide⟩ else (if k.val < 2 then ⟨5, by decide⟩ else ⟨6, by decide⟩)) else (if k.val < 4 then ⟨10, by decide⟩ else (if k.val < 5 then ⟨11, by decide⟩ else ⟨15, by decide⟩))) else (if k.val < 9 then (if k.val < 7 then ⟨16, by decide⟩ else (if k.val < 8 then ⟨19, by decide⟩ else ⟨23, by decide⟩)) else (if k.val < 10 then ⟨24, by decide⟩ else (if k.val < 11 then ⟨27, by decide⟩ else ⟨30, by decide⟩))))
  | 2 => (if k.val < 6 then (if k.val < 3 then (if k.val < 1 then ⟨0, by decide⟩ else (if k.val < 2 then ⟨2, by decide⟩ else ⟨3, by decide⟩)) else (if k.val < 4 then ⟨5, by decide⟩ else (if k.val < 5 then ⟨6, by decide⟩ else ⟨12, by decide⟩))) else (if k.val < 9 then (if k.val < 7 then ⟨14, by decide⟩ else (if k.val < 8 then ⟨16, by decide⟩ else ⟨20, by decide⟩)) else (if k.val < 10 then ⟨22, by decide⟩ else (if k.val < 11 then ⟨24, by decide⟩ else ⟨28, by decide⟩))))
  | 3 => (if k.val < 6 then (if k.val < 3 then (if k.val < 1 then ⟨7, by decide⟩ else (if k.val < 2 then ⟨8, by decide⟩ else ⟨9, by decide⟩)) else (if k.val < 4 then ⟨10, by decide⟩ else (if k.val < 5 then ⟨11, by decide⟩ else ⟨17, by decide⟩))) else (if k.val < 9 then (if k.val < 7 then ⟨18, by decide⟩ else (if k.val < 8 then ⟨19, by decide⟩ else ⟨25, by decide⟩)) else (if k.val < 10 then ⟨26, by decide⟩ else (if k.val < 11 then ⟨27, by decide⟩ else ⟨31, by decide⟩))))
  | 4 => (if k.val < 6 then (if k.val < 3 then (if k.val < 1 then ⟨0, by decide⟩ else (if k.val < 2 then ⟨1, by decide⟩ else ⟨3, by decide⟩)) else (if k.val < 4 then ⟨4, by decide⟩ else (if k.val < 5 then ⟨6, by decide⟩ else ⟨7, by decide⟩))) else (if k.val < 9 then (if k.val < 7 then ⟨9, by decide⟩ else (if k.val < 8 then ⟨11, by decide⟩ else ⟨20, by decide⟩)) else (if k.val < 10 then ⟨21, by decide⟩ else (if k.val < 11 then ⟨23, by decide⟩ else ⟨25, by decide⟩))))
  | 5 => (if k.val < 6 then (if k.val < 3 then (if k.val < 1 then ⟨12, by decide⟩ else (if k.val < 2 then ⟨13, by decide⟩ else ⟨14, by decide⟩)) else (if k.val < 4 then ⟨15, by decide⟩ else (if k.val < 5 then ⟨16, by decide⟩ else ⟨17, by decide⟩))) else (if k.val < 9 then (if k.val < 7 then ⟨18, by decide⟩ else (if k.val < 8 then ⟨19, by decide⟩ else ⟨28, by decide⟩)) else (if k.val < 10 then ⟨29, by decide⟩ else (if k.val < 11 then ⟨30, by decide⟩ else ⟨31, by decide⟩))))
  | 6 => (if k.val < 6 then (if k.val < 3 then (if k.val < 1 then ⟨0, by decide⟩ else (if k.val < 2 then ⟨1, by decide⟩ else ⟨2, by decide⟩)) else (if k.val < 4 then ⟨4, by decide⟩ else (if k.val < 5 then ⟨5, by decide⟩ else ⟨7, by decide⟩))) else (if k.val < 9 then (if k.val < 7 then ⟨8, by decide⟩ else (if k.val < 8 then ⟨10, by decide⟩ else ⟨12, by decide⟩)) else (if k.val < 10 then ⟨13, by decide⟩ else (if k.val < 11 then ⟨15, by decide⟩ else ⟨17, by decide⟩))))
  | 7 => (if k.val < 6 then (if k.val < 3 then (if k.val < 1 then ⟨20, by decide⟩ else (if k.val < 2 then ⟨21, by decide⟩ else ⟨22, by decide⟩)) else (if k.val < 4 then ⟨23, by decide⟩ else (if k.val < 5 then ⟨24, by decide⟩ else ⟨25, by decide⟩))) else (if k.val < 9 then (if k.val < 7 then ⟨26, by decide⟩ else (if k.val < 8 then ⟨27, by decide⟩ else ⟨28, by decide⟩)) else (if k.val < 10 then ⟨29, by decide⟩ else (if k.val < 11 then ⟨30, by decide⟩ else ⟨31, by decide⟩))))
  | _ => ⟨0, by decide⟩
lemma getQ3Edge_extractFacetQ3 (fk : Fin 8) (k : Fin 12) (g : Q4Bits) :
    getQ3Edge (extractFacetQ3 fk g) k = getQ4E g (facetEdge fk k) := by
  fin_cases fk <;> fin_cases k <;> rfl

def q3CycleEdges (j : Fin 16) : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 :=
  match j.val with
  | 0 => (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩)
  | 1 => (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩)
  | 2 => (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩)
  | 3 => (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩)
  | 4 => (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩)
  | 5 => (⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩)
  | 6 => (⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩)
  | 7 => (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩)
  | 8 => (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩)
  | 9 => (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩)
  | 10 => (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩)
  | 11 => (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩)
  | 12 => (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩)
  | 13 => (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩)
  | 14 => (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩)
  | _ => (⟨3, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩)

private lemma isQ3C6Free_of_all (q : Q3Bits)
    (h : ∀ j : Fin 16, let (k0,k1,k2,k3,k4,k5) := q3CycleEdges j
      (!(getQ3Edge q k0 && getQ3Edge q k1 && getQ3Edge q k2 && getQ3Edge q k3 && getQ3Edge q k4 && getQ3Edge q k5)) = true) :
    isQ3C6Free q = true := by
  have h0 : (!(q.e01 && q.e02 && q.e13 && q.e26 && q.e37 && q.e67)) = true := h 0
  have h1 : (!(q.e02 && q.e04 && q.e23 && q.e37 && q.e45 && q.e57)) = true := h 1
  have h2 : (!(q.e01 && q.e04 && q.e13 && q.e23 && q.e26 && q.e46)) = true := h 2
  have h3 : (!(q.e01 && q.e04 && q.e13 && q.e37 && q.e46 && q.e67)) = true := h 3
  have h4 : (!(q.e01 && q.e02 && q.e15 && q.e26 && q.e45 && q.e46)) = true := h 4
  have h5 : (!(q.e13 && q.e15 && q.e23 && q.e26 && q.e57 && q.e67)) = true := h 5
  have h6 : (!(q.e13 && q.e15 && q.e23 && q.e26 && q.e45 && q.e46)) = true := h 6
  have h7 : (!(q.e23 && q.e26 && q.e37 && q.e45 && q.e46 && q.e57)) = true := h 7
  have h8 : (!(q.e02 && q.e04 && q.e26 && q.e45 && q.e57 && q.e67)) = true := h 8
  have h9 : (!(q.e01 && q.e02 && q.e15 && q.e26 && q.e57 && q.e67)) = true := h 9
  have h10 : (!(q.e02 && q.e04 && q.e23 && q.e37 && q.e46 && q.e67)) = true := h 10
  have h11 : (!(q.e01 && q.e04 && q.e15 && q.e46 && q.e57 && q.e67)) = true := h 11
  have h12 : (!(q.e02 && q.e04 && q.e13 && q.e15 && q.e23 && q.e45)) = true := h 12
  have h13 : (!(q.e01 && q.e02 && q.e15 && q.e23 && q.e37 && q.e57)) = true := h 13
  have h14 : (!(q.e01 && q.e04 && q.e13 && q.e37 && q.e45 && q.e57)) = true := h 14
  have h15 : (!(q.e13 && q.e15 && q.e37 && q.e45 && q.e46 && q.e67)) = true := h 15
  simp only [isQ3C6Free, q3IsC6FreeBool, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩

private def facetC6Cid (fk : Fin 8) (j : Fin 16) : Fin 128 :=
  match fk.val with
  | 0 => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨27, by decide⟩ else ⟨19, by decide⟩) else (if j.val < 3 then ⟨68, by decide⟩ else ⟨28, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨110, by decide⟩ else ⟨51, by decide⟩) else (if j.val < 7 then ⟨93, by decide⟩ else ⟨90, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨16, by decide⟩ else ⟨114, by decide⟩) else (if j.val < 11 then ⟨9, by decide⟩ else ⟨89, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨45, by decide⟩ else ⟨120, by decide⟩) else (if j.val < 15 then ⟨73, by decide⟩ else ⟨46, by decide⟩))))
  | 1 => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨109, by decide⟩ else ⟨8, by decide⟩) else (if j.val < 3 then ⟨15, by decide⟩ else ⟨80, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨50, by decide⟩ else ⟨82, by decide⟩) else (if j.val < 7 then ⟨117, by decide⟩ else ⟨101, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨97, by decide⟩ else ⟨121, by decide⟩) else (if j.val < 11 then ⟨43, by decide⟩ else ⟨17, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨95, by decide⟩ else ⟨13, by decide⟩) else (if j.val < 15 then ⟨122, by decide⟩ else ⟨75, by decide⟩))))
  | 2 => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨116, by decide⟩ else ⟨31, by decide⟩) else (if j.val < 3 then ⟨92, by decide⟩ else ⟨118, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨71, by decide⟩ else ⟨54, by decide⟩) else (if j.val < 7 then ⟨36, by decide⟩ else ⟨81, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨53, by decide⟩ else ⟨64, by decide⟩) else (if j.val < 11 then ⟨0, by decide⟩ else ⟨69, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨105, by decide⟩ else ⟨62, by decide⟩) else (if j.val < 15 then ⟨113, by decide⟩ else ⟨100, by decide⟩))))
  | 3 => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨38, by decide⟩ else ⟨20, by decide⟩) else (if j.val < 3 then ⟨98, by decide⟩ else ⟨2, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨22, by decide⟩ else ⟨99, by decide⟩) else (if j.val < 7 then ⟨37, by decide⟩ else ⟨23, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨86, by decide⟩ else ⟨29, by decide⟩) else (if j.val < 11 then ⟨47, by decide⟩ else ⟨41, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨77, by decide⟩ else ⟨76, by decide⟩) else (if j.val < 15 then ⟨35, by decide⟩ else ⟨60, by decide⟩))))
  | 4 => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨108, by decide⟩ else ⟨85, by decide⟩) else (if j.val < 3 then ⟨70, by decide⟩ else ⟨7, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨125, by decide⟩ else ⟨127, by decide⟩) else (if j.val < 7 then ⟨112, by decide⟩ else ⟨107, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨48, by decide⟩ else ⟨11, by decide⟩) else (if j.val < 11 then ⟨123, by decide⟩ else ⟨111, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨12, by decide⟩ else ⟨65, by decide⟩) else (if j.val < 15 then ⟨91, by decide⟩ else ⟨25, by decide⟩))))
  | 5 => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨39, by decide⟩ else ⟨33, by decide⟩) else (if j.val < 3 then ⟨42, by decide⟩ else ⟨106, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨79, by decide⟩ else ⟨5, by decide⟩) else (if j.val < 7 then ⟨96, by decide⟩ else ⟨88, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨115, by decide⟩ else ⟨26, by decide⟩) else (if j.val < 11 then ⟨18, by decide⟩ else ⟨49, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨126, by decide⟩ else ⟨78, by decide⟩) else (if j.val < 15 then ⟨59, by decide⟩ else ⟨4, by decide⟩))))
  | 6 => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨1, by decide⟩ else ⟨66, by decide⟩) else (if j.val < 3 then ⟨83, by decide⟩ else ⟨61, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨55, by decide⟩ else ⟨72, by decide⟩) else (if j.val < 7 then ⟨124, by decide⟩ else ⟨87, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨103, by decide⟩ else ⟨57, by decide⟩) else (if j.val < 11 then ⟨102, by decide⟩ else ⟨104, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨52, by decide⟩ else ⟨56, by decide⟩) else (if j.val < 15 then ⟨84, by decide⟩ else ⟨74, by decide⟩))))
  | 7 => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨21, by decide⟩ else ⟨6, by decide⟩) else (if j.val < 3 then ⟨30, by decide⟩ else ⟨10, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨63, by decide⟩ else ⟨44, by decide⟩) else (if j.val < 7 then ⟨32, by decide⟩ else ⟨24, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨40, by decide⟩ else ⟨34, by decide⟩) else (if j.val < 11 then ⟨94, by decide⟩ else ⟨58, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨67, by decide⟩ else ⟨3, by decide⟩) else (if j.val < 15 then ⟨119, by decide⟩ else ⟨14, by decide⟩))))
  | _ => ⟨0, by decide⟩
private def in6 (x a0 a1 a2 a3 a4 a5 : Fin 32) : Bool :=
  decide (x = a0) || decide (x = a1) || decide (x = a2) || decide (x = a3) || decide (x = a4) || decide (x = a5)
private lemma mem_of_in6 {g : Q4Bits} {x a0 a1 a2 a3 a4 a5 : Fin 32}
    (hin : in6 x a0 a1 a2 a3 a4 a5 = true)
    (h0 : getQ4E g a0 = true) (h1 : getQ4E g a1 = true) (h2 : getQ4E g a2 = true)
    (h3 : getQ4E g a3 = true) (h4 : getQ4E g a4 = true) (h5 : getQ4E g a5 = true) :
    getQ4E g x = true := by
  simp only [in6, Bool.or_eq_true, decide_eq_true_eq] at hin
  rcases hin with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) <;> assumption

private def allFin16 (P : Fin 16 → Bool) : Bool :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15].all fun i => if h : i < 16 then P ⟨i, h⟩ else true
private lemma allFin16_ok {P : Fin 16 → Bool} (h : allFin16 P = true) (x : Fin 16) : P x = true := by
  fin_cases x <;> simp_all [allFin16]

private def checkFacetC6Map : Bool :=
  allFin8 fun fk => allFin16 fun j =>
    let (k0,k1,k2,k3,k4,k5) := q3CycleEdges j
    let (c0,c1,c2,c3,c4,c5) := c6CyclesQ4 (facetC6Cid fk j)
    let f0 := facetEdge fk k0; let f1 := facetEdge fk k1; let f2 := facetEdge fk k2
    let f3 := facetEdge fk k3; let f4 := facetEdge fk k4; let f5 := facetEdge fk k5
    in6 c0 f0 f1 f2 f3 f4 f5 && in6 c1 f0 f1 f2 f3 f4 f5 && in6 c2 f0 f1 f2 f3 f4 f5 &&
    in6 c3 f0 f1 f2 f3 f4 f5 && in6 c4 f0 f1 f2 f3 f4 f5 && in6 c5 f0 f1 f2 f3 f4 f5
private lemma checkFacetC6Map_ok : checkFacetC6Map = true := by decide

lemma isQ3C6Free_of_isQ4C6Free (g : Q4Bits) (hc : isQ4C6Free g) (fk : Fin 8) :
    isQ3C6Free (extractFacetQ3 fk g) = true := by
  apply isQ3C6Free_of_all
  intro j
  have hmap := allFin16_ok (allFin8_ok checkFacetC6Map_ok fk) j
  dsimp only at hmap
  rcases hq : q3CycleEdges j with ⟨k0,k1,k2,k3,k4,k5⟩
  rcases hcid : c6CyclesQ4 (facetC6Cid fk j) with ⟨c0,c1,c2,c3,c4,c5⟩
  rw [hq, hcid] at hmap
  dsimp only at hmap ⊢
  simp only [Bool.and_eq_true] at hmap
  rcases hmap with ⟨⟨⟨⟨⟨hm0, hm1⟩, hm2⟩, hm3⟩, hm4⟩, hm5⟩
  by_cases hbt : (getQ3Edge (extractFacetQ3 fk g) k0 && getQ3Edge (extractFacetQ3 fk g) k1 &&
    getQ3Edge (extractFacetQ3 fk g) k2 && getQ3Edge (extractFacetQ3 fk g) k3 &&
    getQ3Edge (extractFacetQ3 fk g) k4 && getQ3Edge (extractFacetQ3 fk g) k5) = true
  · exfalso
    simp only [Bool.and_eq_true, getQ3Edge_extractFacetQ3] at hbt
    rcases hbt with ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩
    have hbad := hc (facetC6Cid fk j)
    rw [hcid] at hbad
    exact hbad ⟨mem_of_in6 hm0 e0 e1 e2 e3 e4 e5, mem_of_in6 hm1 e0 e1 e2 e3 e4 e5,
      mem_of_in6 hm2 e0 e1 e2 e3 e4 e5, mem_of_in6 hm3 e0 e1 e2 e3 e4 e5,
      mem_of_in6 hm4 e0 e1 e2 e3 e4 e5, mem_of_in6 hm5 e0 e1 e2 e3 e4 e5⟩
  · have hbf := Bool.eq_false_iff.mpr hbt; simp [hbf]

def getB2Edge (b : B2Bits) (k : Fin 16) : Bool :=
  match k.val with | 0 => b.b01 | 1 => b.b02 | 2 => b.b04 | 3 => b.b08 | 4 => b.b13 | 5 => b.b15 | 6 => b.b19 | 7 => b.b23 | 8 => b.b26 | 9 => b.b2a | 10 => b.b45 | 11 => b.b46 | 12 => b.b4c | 13 => b.b89 | 14 => b.b8a | _ => b.b8c
def ballEdge (bi : Fin 16) (k : Fin 16) : Fin 32 :=
  (if bi.val < 8 then (if bi.val < 4 then (if bi.val < 2 then (if bi.val < 1 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨0, by decide⟩ else ⟨1, by decide⟩) else (if k.val < 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨4, by decide⟩ else ⟨5, by decide⟩) else (if k.val < 7 then ⟨6, by decide⟩ else ⟨7, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨8, by decide⟩ else ⟨9, by decide⟩) else (if k.val < 11 then ⟨12, by decide⟩ else ⟨13, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨14, by decide⟩ else ⟨20, by decide⟩) else (if k.val < 15 then ⟨21, by decide⟩ else ⟨22, by decide⟩)))) else (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨0, by decide⟩ else ⟨4, by decide⟩) else (if k.val < 3 then ⟨5, by decide⟩ else ⟨6, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨1, by decide⟩ else ⟨2, by decide⟩) else (if k.val < 7 then ⟨3, by decide⟩ else ⟨7, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨10, by decide⟩ else ⟨11, by decide⟩) else (if k.val < 11 then ⟨12, by decide⟩ else ⟨15, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨16, by decide⟩ else ⟨20, by decide⟩) else (if k.val < 15 then ⟨23, by decide⟩ else ⟨24, by decide⟩))))) else (if bi.val < 3 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨7, by decide⟩ else ⟨1, by decide⟩) else (if k.val < 3 then ⟨8, by decide⟩ else ⟨9, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨4, by decide⟩ else ⟨10, by decide⟩) else (if k.val < 7 then ⟨11, by decide⟩ else ⟨0, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨2, by decide⟩ else ⟨3, by decide⟩) else (if k.val < 11 then ⟨17, by decide⟩ else ⟨13, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨18, by decide⟩ else ⟨25, by decide⟩) else (if k.val < 15 then ⟨21, by decide⟩ else ⟨26, by decide⟩)))) else (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨7, by decide⟩ else ⟨4, by decide⟩) else (if k.val < 3 then ⟨10, by decide⟩ else ⟨11, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨1, by decide⟩ else ⟨8, by decide⟩) else (if k.val < 7 then ⟨9, by decide⟩ else ⟨0, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨5, by decide⟩ else ⟨6, by decide⟩) else (if k.val < 11 then ⟨17, by decide⟩ else ⟨15, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨19, by decide⟩ else ⟨25, by decide⟩) else (if k.val < 15 then ⟨23, by decide⟩ else ⟨27, by decide⟩)))))) else (if bi.val < 6 then (if bi.val < 5 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨12, by decide⟩ else ⟨13, by decide⟩) else (if k.val < 3 then ⟨2, by decide⟩ else ⟨14, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨15, by decide⟩ else ⟨5, by decide⟩) else (if k.val < 7 then ⟨16, by decide⟩ else ⟨17, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨8, by decide⟩ else ⟨18, by decide⟩) else (if k.val < 11 then ⟨0, by decide⟩ else ⟨1, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨3, by decide⟩ else ⟨28, by decide⟩) else (if k.val < 15 then ⟨29, by decide⟩ else ⟨22, by decide⟩)))) else (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨12, by decide⟩ else ⟨15, by decide⟩) else (if k.val < 3 then ⟨5, by decide⟩ else ⟨16, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨13, by decide⟩ else ⟨2, by decide⟩) else (if k.val < 7 then ⟨14, by decide⟩ else ⟨17, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨10, by decide⟩ else ⟨19, by decide⟩) else (if k.val < 11 then ⟨0, by decide⟩ else ⟨4, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨6, by decide⟩ else ⟨28, by decide⟩) else (if k.val < 15 then ⟨30, by decide⟩ else ⟨24, by decide⟩))))) else (if bi.val < 7 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨17, by decide⟩ else ⟨13, by decide⟩) else (if k.val < 3 then ⟨8, by decide⟩ else ⟨18, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨15, by decide⟩ else ⟨10, by decide⟩) else (if k.val < 7 then ⟨19, by decide⟩ else ⟨12, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨2, by decide⟩ else ⟨14, by decide⟩) else (if k.val < 11 then ⟨7, by decide⟩ else ⟨1, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨9, by decide⟩ else ⟨31, by decide⟩) else (if k.val < 15 then ⟨29, by decide⟩ else ⟨26, by decide⟩)))) else (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨17, by decide⟩ else ⟨15, by decide⟩) else (if k.val < 3 then ⟨10, by decide⟩ else ⟨19, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨13, by decide⟩ else ⟨8, by decide⟩) else (if k.val < 7 then ⟨18, by decide⟩ else ⟨12, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨5, by decide⟩ else ⟨16, by decide⟩) else (if k.val < 11 then ⟨7, by decide⟩ else ⟨4, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨11, by decide⟩ else ⟨31, by decide⟩) else (if k.val < 15 then ⟨30, by decide⟩ else ⟨27, by decide⟩))))))) else (if bi.val < 12 then (if bi.val < 10 then (if bi.val < 9 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨20, by decide⟩ else ⟨21, by decide⟩) else (if k.val < 3 then ⟨22, by decide⟩ else ⟨3, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨23, by decide⟩ else ⟨24, by decide⟩) else (if k.val < 7 then ⟨6, by decide⟩ else ⟨25, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨26, by decide⟩ else ⟨9, by decide⟩) else (if k.val < 11 then ⟨28, by decide⟩ else ⟨29, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨14, by decide⟩ else ⟨0, by decide⟩) else (if k.val < 15 then ⟨1, by decide⟩ else ⟨2, by decide⟩)))) else (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨20, by decide⟩ else ⟨23, by decide⟩) else (if k.val < 3 then ⟨24, by decide⟩ else ⟨6, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨21, by decide⟩ else ⟨22, by decide⟩) else (if k.val < 7 then ⟨3, by decide⟩ else ⟨25, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨27, by decide⟩ else ⟨11, by decide⟩) else (if k.val < 11 then ⟨28, by decide⟩ else ⟨30, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨16, by decide⟩ else ⟨0, by decide⟩) else (if k.val < 15 then ⟨4, by decide⟩ else ⟨5, by decide⟩))))) else (if bi.val < 11 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨25, by decide⟩ else ⟨21, by decide⟩) else (if k.val < 3 then ⟨26, by decide⟩ else ⟨9, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨23, by decide⟩ else ⟨27, by decide⟩) else (if k.val < 7 then ⟨11, by decide⟩ else ⟨20, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨22, by decide⟩ else ⟨3, by decide⟩) else (if k.val < 11 then ⟨31, by decide⟩ else ⟨29, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨18, by decide⟩ else ⟨7, by decide⟩) else (if k.val < 15 then ⟨1, by decide⟩ else ⟨8, by decide⟩)))) else (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨25, by decide⟩ else ⟨23, by decide⟩) else (if k.val < 3 then ⟨27, by decide⟩ else ⟨11, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨21, by decide⟩ else ⟨26, by decide⟩) else (if k.val < 7 then ⟨9, by decide⟩ else ⟨20, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨24, by decide⟩ else ⟨6, by decide⟩) else (if k.val < 11 then ⟨31, by decide⟩ else ⟨30, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨19, by decide⟩ else ⟨7, by decide⟩) else (if k.val < 15 then ⟨4, by decide⟩ else ⟨10, by decide⟩)))))) else (if bi.val < 14 then (if bi.val < 13 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨28, by decide⟩ else ⟨29, by decide⟩) else (if k.val < 3 then ⟨22, by decide⟩ else ⟨14, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨30, by decide⟩ else ⟨24, by decide⟩) else (if k.val < 7 then ⟨16, by decide⟩ else ⟨31, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨26, by decide⟩ else ⟨18, by decide⟩) else (if k.val < 11 then ⟨20, by decide⟩ else ⟨21, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨3, by decide⟩ else ⟨12, by decide⟩) else (if k.val < 15 then ⟨13, by decide⟩ else ⟨2, by decide⟩)))) else (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨28, by decide⟩ else ⟨30, by decide⟩) else (if k.val < 3 then ⟨24, by decide⟩ else ⟨16, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨29, by decide⟩ else ⟨22, by decide⟩) else (if k.val < 7 then ⟨14, by decide⟩ else ⟨31, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨27, by decide⟩ else ⟨19, by decide⟩) else (if k.val < 11 then ⟨20, by decide⟩ else ⟨23, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨6, by decide⟩ else ⟨12, by decide⟩) else (if k.val < 15 then ⟨15, by decide⟩ else ⟨5, by decide⟩))))) else (if bi.val < 15 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨31, by decide⟩ else ⟨29, by decide⟩) else (if k.val < 3 then ⟨26, by decide⟩ else ⟨18, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨30, by decide⟩ else ⟨27, by decide⟩) else (if k.val < 7 then ⟨19, by decide⟩ else ⟨28, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨22, by decide⟩ else ⟨14, by decide⟩) else (if k.val < 11 then ⟨25, by decide⟩ else ⟨21, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨9, by decide⟩ else ⟨17, by decide⟩) else (if k.val < 15 then ⟨13, by decide⟩ else ⟨8, by decide⟩)))) else (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨31, by decide⟩ else ⟨30, by decide⟩) else (if k.val < 3 then ⟨27, by decide⟩ else ⟨19, by decide⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨29, by decide⟩ else ⟨26, by decide⟩) else (if k.val < 7 then ⟨18, by decide⟩ else ⟨28, by decide⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨24, by decide⟩ else ⟨16, by decide⟩) else (if k.val < 11 then ⟨25, by decide⟩ else ⟨23, by decide⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨11, by decide⟩ else ⟨17, by decide⟩) else (if k.val < 15 then ⟨15, by decide⟩ else ⟨10, by decide⟩))))))))
lemma getB2Edge_extractBallB2 (bi : Fin 16) (k : Fin 16) (g : Q4Bits) :
    getB2Edge (extractBallB2 bi g) k = getQ4E g (ballEdge bi k) := by
  fin_cases bi <;> fin_cases k <;> rfl

def b2CycleEdges (j : Fin 16) : Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 :=
  match j.val with
  | 0 => (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨14, by decide⟩)
  | 1 => (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩)
  | 2 => (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩)
  | 3 => (⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩)
  | 4 => (⟨5, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩)
  | 5 => (⟨8, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩)
  | 6 => (⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩)
  | 7 => (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩)
  | 8 => (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩)
  | 9 => (⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩)
  | 10 => (⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩)
  | 11 => (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩)
  | 12 => (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩)
  | 13 => (⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩)
  | 14 => (⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩)
  | _ => (⟨1, by decide⟩, ⟨2, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩)

private lemma isB2C6Free_of_all (b : B2Bits)
    (h : ∀ j : Fin 16, let (k0,k1,k2,k3,k4,k5) := b2CycleEdges j
      (!(getB2Edge b k0 && getB2Edge b k1 && getB2Edge b k2 && getB2Edge b k3 && getB2Edge b k4 && getB2Edge b k5)) = true) :
    isB2C6Free b = true := by
  have h0 : (!(b.b01 && b.b08 && b.b13 && b.b23 && b.b2a && b.b8a)) = true := h 0
  have h1 : (!(b.b01 && b.b02 && b.b19 && b.b2a && b.b89 && b.b8a)) = true := h 1
  have h2 : (!(b.b01 && b.b04 && b.b19 && b.b4c && b.b89 && b.b8c)) = true := h 2
  have h3 : (!(b.b01 && b.b04 && b.b13 && b.b23 && b.b26 && b.b46)) = true := h 3
  have h4 : (!(b.b15 && b.b19 && b.b45 && b.b4c && b.b89 && b.b8c)) = true := h 4
  have h5 : (!(b.b26 && b.b2a && b.b46 && b.b4c && b.b8a && b.b8c)) = true := h 5
  have h6 : (!(b.b13 && b.b15 && b.b23 && b.b26 && b.b45 && b.b46)) = true := h 6
  have h7 : (!(b.b02 && b.b08 && b.b26 && b.b46 && b.b4c && b.b8c)) = true := h 7
  have h8 : (!(b.b04 && b.b08 && b.b26 && b.b2a && b.b46 && b.b8a)) = true := h 8
  have h9 : (!(b.b13 && b.b19 && b.b23 && b.b2a && b.b89 && b.b8a)) = true := h 9
  have h10 : (!(b.b04 && b.b08 && b.b15 && b.b19 && b.b45 && b.b89)) = true := h 10
  have h11 : (!(b.b01 && b.b02 && b.b15 && b.b26 && b.b45 && b.b46)) = true := h 11
  have h12 : (!(b.b02 && b.b04 && b.b13 && b.b15 && b.b23 && b.b45)) = true := h 12
  have h13 : (!(b.b02 && b.b08 && b.b13 && b.b19 && b.b23 && b.b89)) = true := h 13
  have h14 : (!(b.b01 && b.b08 && b.b15 && b.b45 && b.b4c && b.b8c)) = true := h 14
  have h15 : (!(b.b02 && b.b04 && b.b2a && b.b4c && b.b8a && b.b8c)) = true := h 15
  simp only [isB2C6Free, b2IsC6FreeBool, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩

private def ballC6Cid (bi : Fin 16) (j : Fin 16) : Fin 128 :=
  (if bi.val < 8 then (if bi.val < 4 then (if bi.val < 2 then (if bi.val < 1 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨70, by decide⟩ else ⟨125, by decide⟩) else (if j.val < 3 then ⟨71, by decide⟩ else ⟨83, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨36, by decide⟩ else ⟨93, by decide⟩) else (if j.val < 7 then ⟨124, by decide⟩ else ⟨68, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨45, by decide⟩ else ⟨112, by decide⟩) else (if j.val < 11 then ⟨105, by decide⟩ else ⟨55, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨52, by decide⟩ else ⟨12, by decide⟩) else (if j.val < 15 then ⟨92, by decide⟩ else ⟨110, by decide⟩)))) else (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨65, by decide⟩ else ⟨91, by decide⟩) else (if j.val < 3 then ⟨113, by decide⟩ else ⟨56, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨31, by decide⟩ else ⟨117, by decide⟩) else (if j.val < 7 then ⟨66, by decide⟩ else ⟨15, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨95, by decide⟩ else ⟨85, by decide⟩) else (if j.val < 11 then ⟨105, by decide⟩ else ⟨84, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨52, by decide⟩ else ⟨12, by decide⟩) else (if j.val < 15 then ⟨62, by decide⟩ else ⟨50, by decide⟩))))) else (if bi.val < 3 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨70, by decide⟩ else ⟨123, by decide⟩) else (if j.val < 3 then ⟨22, by decide⟩ else ⟨83, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨37, by decide⟩ else ⟨19, by decide⟩) else (if j.val < 7 then ⟨61, by decide⟩ else ⟨120, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨45, by decide⟩ else ⟨7, by decide⟩) else (if j.val < 11 then ⟨77, by decide⟩ else ⟨102, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨1, by decide⟩ else ⟨108, by decide⟩) else (if j.val < 15 then ⟨98, by decide⟩ else ⟨73, by decide⟩)))) else (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨65, by decide⟩ else ⟨127, by decide⟩) else (if j.val < 3 then ⟨35, by decide⟩ else ⟨56, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨20, by decide⟩ else ⟨8, by decide⟩) else (if j.val < 7 then ⟨57, by decide⟩ else ⟨13, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨95, by decide⟩ else ⟨11, by decide⟩) else (if j.val < 11 then ⟨77, by decide⟩ else ⟨72, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨1, by decide⟩ else ⟨108, by decide⟩) else (if j.val < 15 then ⟨76, by decide⟩ else ⟨122, by decide⟩)))))) else (if bi.val < 6 then (if bi.val < 5 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨42, by decide⟩ else ⟨79, by decide⟩) else (if j.val < 3 then ⟨0, by decide⟩ else ⟨103, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨118, by decide⟩ else ⟨28, by decide⟩) else (if j.val < 7 then ⟨57, by decide⟩ else ⟨68, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨27, by decide⟩ else ⟨96, by decide⟩) else (if j.val < 11 then ⟨116, by decide⟩ else ⟨55, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨104, by decide⟩ else ⟨126, by decide⟩) else (if j.val < 15 then ⟨92, by decide⟩ else ⟨9, by decide⟩)))) else (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨78, by decide⟩ else ⟨59, by decide⟩) else (if j.val < 3 then ⟨54, by decide⟩ else ⟨74, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨64, by decide⟩ else ⟨80, by decide⟩) else (if j.val < 7 then ⟨61, by decide⟩ else ⟨15, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨109, by decide⟩ else ⟨33, by decide⟩) else (if j.val < 11 then ⟨116, by decide⟩ else ⟨84, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨104, by decide⟩ else ⟨126, by decide⟩) else (if j.val < 15 then ⟨62, by decide⟩ else ⟨43, by decide⟩))))) else (if bi.val < 7 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨42, by decide⟩ else ⟨18, by decide⟩) else (if j.val < 3 then ⟨47, by decide⟩ else ⟨103, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨2, by decide⟩ else ⟨114, by decide⟩) else (if j.val < 7 then ⟨66, by decide⟩ else ⟨120, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨27, by decide⟩ else ⟨106, by decide⟩) else (if j.val < 11 then ⟨38, by decide⟩ else ⟨102, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨87, by decide⟩ else ⟨39, by decide⟩) else (if j.val < 15 then ⟨98, by decide⟩ else ⟨51, by decide⟩)))) else (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨78, by decide⟩ else ⟨5, by decide⟩) else (if j.val < 3 then ⟨99, by decide⟩ else ⟨74, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨29, by decide⟩ else ⟨121, by decide⟩) else (if j.val < 7 then ⟨124, by decide⟩ else ⟨13, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨109, by decide⟩ else ⟨26, by decide⟩) else (if j.val < 11 then ⟨38, by decide⟩ else ⟨72, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨87, by decide⟩ else ⟨39, by decide⟩) else (if j.val < 15 then ⟨76, by decide⟩ else ⟨82, by decide⟩))))))) else (if bi.val < 12 then (if bi.val < 10 then (if bi.val < 9 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨48, by decide⟩ else ⟨125, by decide⟩) else (if j.val < 3 then ⟨71, by decide⟩ else ⟨30, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨64, by decide⟩ else ⟨114, by decide⟩) else (if j.val < 7 then ⟨32, by decide⟩ else ⟨16, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨89, by decide⟩ else ⟨11, by decide⟩) else (if j.val < 11 then ⟨69, by decide⟩ else ⟨63, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨67, by decide⟩ else ⟨111, by decide⟩) else (if j.val < 15 then ⟨53, by decide⟩ else ⟨110, by decide⟩)))) else (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨25, by decide⟩ else ⟨91, by decide⟩) else (if j.val < 3 then ⟨113, by decide⟩ else ⟨3, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨118, by decide⟩ else ⟨121, by decide⟩) else (if j.val < 7 then ⟨6, by decide⟩ else ⟨97, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨17, by decide⟩ else ⟨7, by decide⟩) else (if j.val < 11 then ⟨69, by decide⟩ else ⟨119, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨67, by decide⟩ else ⟨111, by decide⟩) else (if j.val < 15 then ⟨100, by decide⟩ else ⟨50, by decide⟩))))) else (if bi.val < 11 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨48, by decide⟩ else ⟨123, by decide⟩) else (if j.val < 3 then ⟨22, by decide⟩ else ⟨30, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨29, by decide⟩ else ⟨28, by decide⟩) else (if j.val < 7 then ⟨10, by decide⟩ else ⟨46, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨89, by decide⟩ else ⟨85, by decide⟩) else (if j.val < 11 then ⟨41, by decide⟩ else ⟨94, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨21, by decide⟩ else ⟨107, by decide⟩) else (if j.val < 15 then ⟨86, by decide⟩ else ⟨73, by decide⟩)))) else (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨25, by decide⟩ else ⟨127, by decide⟩) else (if j.val < 3 then ⟨35, by decide⟩ else ⟨3, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨2, by decide⟩ else ⟨80, by decide⟩) else (if j.val < 7 then ⟨34, by decide⟩ else ⟨75, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨17, by decide⟩ else ⟨112, by decide⟩) else (if j.val < 11 then ⟨41, by decide⟩ else ⟨44, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨21, by decide⟩ else ⟨107, by decide⟩) else (if j.val < 15 then ⟨60, by decide⟩ else ⟨122, by decide⟩)))))) else (if bi.val < 14 then (if bi.val < 13 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨115, by decide⟩ else ⟨79, by decide⟩) else (if j.val < 3 then ⟨0, by decide⟩ else ⟨40, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨31, by decide⟩ else ⟨19, by decide⟩) else (if j.val < 7 then ⟨34, by decide⟩ else ⟨16, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨90, by decide⟩ else ⟨26, by decide⟩) else (if j.val < 11 then ⟨81, by decide⟩ else ⟨63, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨58, by decide⟩ else ⟨49, by decide⟩) else (if j.val < 15 then ⟨53, by decide⟩ else ⟨9, by decide⟩)))) else (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨4, by decide⟩ else ⟨59, by decide⟩) else (if j.val < 3 then ⟨54, by decide⟩ else ⟨14, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨36, by decide⟩ else ⟨8, by decide⟩) else (if j.val < 7 then ⟨10, by decide⟩ else ⟨97, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨101, by decide⟩ else ⟨106, by decide⟩) else (if j.val < 11 then ⟨81, by decide⟩ else ⟨119, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨58, by decide⟩ else ⟨49, by decide⟩) else (if j.val < 15 then ⟨100, by decide⟩ else ⟨43, by decide⟩))))) else (if bi.val < 15 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨115, by decide⟩ else ⟨18, by decide⟩) else (if j.val < 3 then ⟨47, by decide⟩ else ⟨40, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨20, by decide⟩ else ⟨93, by decide⟩) else (if j.val < 7 then ⟨6, by decide⟩ else ⟨46, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨90, by decide⟩ else ⟨33, by decide⟩) else (if j.val < 11 then ⟨23, by decide⟩ else ⟨94, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨24, by decide⟩ else ⟨88, by decide⟩) else (if j.val < 15 then ⟨86, by decide⟩ else ⟨51, by decide⟩)))) else (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then ⟨4, by decide⟩ else ⟨5, by decide⟩) else (if j.val < 3 then ⟨99, by decide⟩ else ⟨14, by decide⟩)) else (if j.val < 6 then (if j.val < 5 then ⟨37, by decide⟩ else ⟨117, by decide⟩) else (if j.val < 7 then ⟨32, by decide⟩ else ⟨75, by decide⟩))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then ⟨101, by decide⟩ else ⟨96, by decide⟩) else (if j.val < 11 then ⟨23, by decide⟩ else ⟨44, by decide⟩)) else (if j.val < 14 then (if j.val < 13 then ⟨24, by decide⟩ else ⟨88, by decide⟩) else (if j.val < 15 then ⟨60, by decide⟩ else ⟨82, by decide⟩))))))))
private def checkBallC6Map : Bool :=
  allFin16 fun bi => allFin16 fun j =>
    let (k0,k1,k2,k3,k4,k5) := b2CycleEdges j
    let (c0,c1,c2,c3,c4,c5) := c6CyclesQ4 (ballC6Cid bi j)
    let f0 := ballEdge bi k0; let f1 := ballEdge bi k1; let f2 := ballEdge bi k2
    let f3 := ballEdge bi k3; let f4 := ballEdge bi k4; let f5 := ballEdge bi k5
    in6 c0 f0 f1 f2 f3 f4 f5 && in6 c1 f0 f1 f2 f3 f4 f5 && in6 c2 f0 f1 f2 f3 f4 f5 &&
    in6 c3 f0 f1 f2 f3 f4 f5 && in6 c4 f0 f1 f2 f3 f4 f5 && in6 c5 f0 f1 f2 f3 f4 f5
private lemma checkBallC6Map_ok : checkBallC6Map = true := by decide

lemma isB2C6Free_of_isQ4C6Free (g : Q4Bits) (hc : isQ4C6Free g) (bi : Fin 16) :
    isB2C6Free (extractBallB2 bi g) = true := by
  apply isB2C6Free_of_all
  intro j
  have hmap := allFin16_ok (allFin16_ok checkBallC6Map_ok bi) j
  dsimp only at hmap
  rcases hq : b2CycleEdges j with ⟨k0,k1,k2,k3,k4,k5⟩
  rcases hcid : c6CyclesQ4 (ballC6Cid bi j) with ⟨c0,c1,c2,c3,c4,c5⟩
  rw [hq, hcid] at hmap
  dsimp only at hmap ⊢
  simp only [Bool.and_eq_true] at hmap
  rcases hmap with ⟨⟨⟨⟨⟨hm0, hm1⟩, hm2⟩, hm3⟩, hm4⟩, hm5⟩
  by_cases hbt : (getB2Edge (extractBallB2 bi g) k0 && getB2Edge (extractBallB2 bi g) k1 &&
    getB2Edge (extractBallB2 bi g) k2 && getB2Edge (extractBallB2 bi g) k3 &&
    getB2Edge (extractBallB2 bi g) k4 && getB2Edge (extractBallB2 bi g) k5) = true
  · exfalso
    simp only [Bool.and_eq_true, getB2Edge_extractBallB2] at hbt
    rcases hbt with ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩
    have hbad := hc (ballC6Cid bi j)
    rw [hcid] at hbad
    exact hbad ⟨mem_of_in6 hm0 e0 e1 e2 e3 e4 e5, mem_of_in6 hm1 e0 e1 e2 e3 e4 e5,
      mem_of_in6 hm2 e0 e1 e2 e3 e4 e5, mem_of_in6 hm3 e0 e1 e2 e3 e4 e5,
      mem_of_in6 hm4 e0 e1 e2 e3 e4 e5, mem_of_in6 hm5 e0 e1 e2 e3 e4 e5⟩
  · have hbf := Bool.eq_false_iff.mpr hbt; simp [hbf]

def maxQ3_12 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : Tri) : ℕ :=
  max1 t0 fun e0 => max1 t1 fun e1 => max1 t2 fun e2 => max1 t3 fun e3 =>
  max1 t4 fun e4 => max1 t5 fun e5 => max1 t6 fun e6 => max1 t7 fun e7 =>
  max1 t8 fun e8 => max1 t9 fun e9 => max1 t10 fun e10 => max1 t11 fun e11 =>
    q3Lookup e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11

def maxQ3Tri (st : State32) (fk : ℕ) : ℕ :=
  match fk with
  | 0 => maxQ3_12 st.b0.t1 st.b0.t2 st.b0.t3 st.b1.t0 st.b1.t1 st.b1.t5 st.b1.t6 st.b2.t2 st.b2.t5 st.b2.t6 st.b3.t2 st.b3.t5
  | 1 => maxQ3_12 st.b0.t4 st.b0.t5 st.b0.t6 st.b1.t2 st.b1.t3 st.b1.t7 st.b2.t0 st.b2.t3 st.b2.t7 st.b3.t0 st.b3.t3 st.b3.t6
  | 2 => maxQ3_12 st.b0.t0 st.b0.t2 st.b0.t3 st.b0.t5 st.b0.t6 st.b1.t4 st.b1.t6 st.b2.t0 st.b2.t4 st.b2.t6 st.b3.t0 st.b3.t4
  | 3 => maxQ3_12 st.b0.t7 st.b1.t0 st.b1.t1 st.b1.t2 st.b1.t3 st.b2.t1 st.b2.t2 st.b2.t3 st.b3.t1 st.b3.t2 st.b3.t3 st.b3.t7
  | 4 => maxQ3_12 st.b0.t0 st.b0.t1 st.b0.t3 st.b0.t4 st.b0.t6 st.b0.t7 st.b1.t1 st.b1.t3 st.b2.t4 st.b2.t5 st.b2.t7 st.b3.t1
  | 5 => maxQ3_12 st.b1.t4 st.b1.t5 st.b1.t6 st.b1.t7 st.b2.t0 st.b2.t1 st.b2.t2 st.b2.t3 st.b3.t4 st.b3.t5 st.b3.t6 st.b3.t7
  | 6 => maxQ3_12 st.b0.t0 st.b0.t1 st.b0.t2 st.b0.t4 st.b0.t5 st.b0.t7 st.b1.t0 st.b1.t2 st.b1.t4 st.b1.t5 st.b1.t7 st.b2.t1
  | 7 => maxQ3_12 st.b2.t4 st.b2.t5 st.b2.t6 st.b2.t7 st.b3.t0 st.b3.t1 st.b3.t2 st.b3.t3 st.b3.t4 st.b3.t5 st.b3.t6 st.b3.t7
  | _ => 0

def allKnown12 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : Tri) : Bool :=
  !(isTriU t0 || isTriU t1 || isTriU t2 || isTriU t3 || isTriU t4 || isTriU t5 || isTriU t6 || isTriU t7 || isTriU t8 || isTriU t9 || isTriU t10 || isTriU t11)

def facetAllKnown (st : State32) (fk : ℕ) : Bool :=
  match fk with
  | 0 => allKnown12 st.b0.t1 st.b0.t2 st.b0.t3 st.b1.t0 st.b1.t1 st.b1.t5 st.b1.t6 st.b2.t2 st.b2.t5 st.b2.t6 st.b3.t2 st.b3.t5
  | 1 => allKnown12 st.b0.t4 st.b0.t5 st.b0.t6 st.b1.t2 st.b1.t3 st.b1.t7 st.b2.t0 st.b2.t3 st.b2.t7 st.b3.t0 st.b3.t3 st.b3.t6
  | 2 => allKnown12 st.b0.t0 st.b0.t2 st.b0.t3 st.b0.t5 st.b0.t6 st.b1.t4 st.b1.t6 st.b2.t0 st.b2.t4 st.b2.t6 st.b3.t0 st.b3.t4
  | 3 => allKnown12 st.b0.t7 st.b1.t0 st.b1.t1 st.b1.t2 st.b1.t3 st.b2.t1 st.b2.t2 st.b2.t3 st.b3.t1 st.b3.t2 st.b3.t3 st.b3.t7
  | 4 => allKnown12 st.b0.t0 st.b0.t1 st.b0.t3 st.b0.t4 st.b0.t6 st.b0.t7 st.b1.t1 st.b1.t3 st.b2.t4 st.b2.t5 st.b2.t7 st.b3.t1
  | 5 => allKnown12 st.b1.t4 st.b1.t5 st.b1.t6 st.b1.t7 st.b2.t0 st.b2.t1 st.b2.t2 st.b2.t3 st.b3.t4 st.b3.t5 st.b3.t6 st.b3.t7
  | 6 => allKnown12 st.b0.t0 st.b0.t1 st.b0.t2 st.b0.t4 st.b0.t5 st.b0.t7 st.b1.t0 st.b1.t2 st.b1.t4 st.b1.t5 st.b1.t7 st.b2.t1
  | 7 => allKnown12 st.b2.t4 st.b2.t5 st.b2.t6 st.b2.t7 st.b3.t0 st.b3.t1 st.b3.t2 st.b3.t3 st.b3.t4 st.b3.t5 st.b3.t6 st.b3.t7
  | _ => false

def maxB2_16 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : Tri) : ℕ :=
  max1 t0 fun b0 => max1 t1 fun b1 => max1 t2 fun b2 => max1 t3 fun b3 =>
  max1 t4 fun b4 => max1 t5 fun b5 => max1 t6 fun b6 => max1 t7 fun b7 =>
  max1 t8 fun b8 => max1 t9 fun b9 => max1 t10 fun b10 => max1 t11 fun b11 =>
  max1 t12 fun b12 => max1 t13 fun b13 => max1 t14 fun b14 => max1 t15 fun b15 =>
    b2Lookup b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15

def maxB2Tri (st : State32) (bi : ℕ) : ℕ :=
  match bi with
  | 0 => maxB2_16 st.b0.t0 st.b0.t1 st.b0.t2 st.b0.t3 st.b0.t4 st.b0.t5 st.b0.t6 st.b0.t7 st.b1.t0 st.b1.t1 st.b1.t4 st.b1.t5 st.b1.t6 st.b2.t4 st.b2.t5 st.b2.t6
  | 1 => maxB2_16 st.b0.t0 st.b0.t4 st.b0.t5 st.b0.t6 st.b0.t1 st.b0.t2 st.b0.t3 st.b0.t7 st.b1.t2 st.b1.t3 st.b1.t4 st.b1.t7 st.b2.t0 st.b2.t4 st.b2.t7 st.b3.t0
  | 2 => maxB2_16 st.b0.t7 st.b0.t1 st.b1.t0 st.b1.t1 st.b0.t4 st.b1.t2 st.b1.t3 st.b0.t0 st.b0.t2 st.b0.t3 st.b2.t1 st.b1.t5 st.b2.t2 st.b3.t1 st.b2.t5 st.b3.t2
  | 3 => maxB2_16 st.b0.t7 st.b0.t4 st.b1.t2 st.b1.t3 st.b0.t1 st.b1.t0 st.b1.t1 st.b0.t0 st.b0.t5 st.b0.t6 st.b2.t1 st.b1.t7 st.b2.t3 st.b3.t1 st.b2.t7 st.b3.t3
  | 4 => maxB2_16 st.b1.t4 st.b1.t5 st.b0.t2 st.b1.t6 st.b1.t7 st.b0.t5 st.b2.t0 st.b2.t1 st.b1.t0 st.b2.t2 st.b0.t0 st.b0.t1 st.b0.t3 st.b3.t4 st.b3.t5 st.b2.t6
  | 5 => maxB2_16 st.b1.t4 st.b1.t7 st.b0.t5 st.b2.t0 st.b1.t5 st.b0.t2 st.b1.t6 st.b2.t1 st.b1.t2 st.b2.t3 st.b0.t0 st.b0.t4 st.b0.t6 st.b3.t4 st.b3.t6 st.b3.t0
  | 6 => maxB2_16 st.b2.t1 st.b1.t5 st.b1.t0 st.b2.t2 st.b1.t7 st.b1.t2 st.b2.t3 st.b1.t4 st.b0.t2 st.b1.t6 st.b0.t7 st.b0.t1 st.b1.t1 st.b3.t7 st.b3.t5 st.b3.t2
  | 7 => maxB2_16 st.b2.t1 st.b1.t7 st.b1.t2 st.b2.t3 st.b1.t5 st.b1.t0 st.b2.t2 st.b1.t4 st.b0.t5 st.b2.t0 st.b0.t7 st.b0.t4 st.b1.t3 st.b3.t7 st.b3.t6 st.b3.t3
  | 8 => maxB2_16 st.b2.t4 st.b2.t5 st.b2.t6 st.b0.t3 st.b2.t7 st.b3.t0 st.b0.t6 st.b3.t1 st.b3.t2 st.b1.t1 st.b3.t4 st.b3.t5 st.b1.t6 st.b0.t0 st.b0.t1 st.b0.t2
  | 9 => maxB2_16 st.b2.t4 st.b2.t7 st.b3.t0 st.b0.t6 st.b2.t5 st.b2.t6 st.b0.t3 st.b3.t1 st.b3.t3 st.b1.t3 st.b3.t4 st.b3.t6 st.b2.t0 st.b0.t0 st.b0.t4 st.b0.t5
  | 10 => maxB2_16 st.b3.t1 st.b2.t5 st.b3.t2 st.b1.t1 st.b2.t7 st.b3.t3 st.b1.t3 st.b2.t4 st.b2.t6 st.b0.t3 st.b3.t7 st.b3.t5 st.b2.t2 st.b0.t7 st.b0.t1 st.b1.t0
  | 11 => maxB2_16 st.b3.t1 st.b2.t7 st.b3.t3 st.b1.t3 st.b2.t5 st.b3.t2 st.b1.t1 st.b2.t4 st.b3.t0 st.b0.t6 st.b3.t7 st.b3.t6 st.b2.t3 st.b0.t7 st.b0.t4 st.b1.t2
  | 12 => maxB2_16 st.b3.t4 st.b3.t5 st.b2.t6 st.b1.t6 st.b3.t6 st.b3.t0 st.b2.t0 st.b3.t7 st.b3.t2 st.b2.t2 st.b2.t4 st.b2.t5 st.b0.t3 st.b1.t4 st.b1.t5 st.b0.t2
  | 13 => maxB2_16 st.b3.t4 st.b3.t6 st.b3.t0 st.b2.t0 st.b3.t5 st.b2.t6 st.b1.t6 st.b3.t7 st.b3.t3 st.b2.t3 st.b2.t4 st.b2.t7 st.b0.t6 st.b1.t4 st.b1.t7 st.b0.t5
  | 14 => maxB2_16 st.b3.t7 st.b3.t5 st.b3.t2 st.b2.t2 st.b3.t6 st.b3.t3 st.b2.t3 st.b3.t4 st.b2.t6 st.b1.t6 st.b3.t1 st.b2.t5 st.b1.t1 st.b2.t1 st.b1.t5 st.b1.t0
  | 15 => maxB2_16 st.b3.t7 st.b3.t6 st.b3.t3 st.b2.t3 st.b3.t5 st.b3.t2 st.b2.t2 st.b3.t4 st.b3.t0 st.b2.t0 st.b3.t1 st.b2.t7 st.b1.t3 st.b2.t1 st.b1.t7 st.b1.t2
  | _ => 0

def stateMatches (st : State32) (g : Q4Bits) : Prop :=
  ∀ e : Fin 32, matchTri (getE st e.val) (getQ4E g e)

private lemma stateMatches_setE (st : State32) (g : Q4Bits) (e : Fin 32) (t : Tri)
    (hs : stateMatches st g) (ht : matchTri t (getQ4E g e)) :
    stateMatches (setE st e.val t) g := by
  intro e'
  by_cases he : e' = e
  · subst he; rw [getE_setE_self]; exact ht
  · rw [getE_setE_ne st he]; exact hs e'

private lemma evalQ3Fast_le_maxQ3_12 {t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : Tri}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool}
    (h0 : matchTri t0 b0) (h1 : matchTri t1 b1) (h2 : matchTri t2 b2) (h3 : matchTri t3 b3)
    (h4 : matchTri t4 b4) (h5 : matchTri t5 b5) (h6 : matchTri t6 b6) (h7 : matchTri t7 b7)
    (h8 : matchTri t8 b8) (h9 : matchTri t9 b9) (h10 : matchTri t10 b10) (h11 : matchTri t11 b11) :
    q3Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 ≤ maxQ3_12 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 := by
  rw [← q3Lookup_eq_q3Fast]
  dsimp only [maxQ3_12]
  refine le_trans ?_ (le_max1 _ _ _ h0)
  refine le_trans ?_ (le_max1 _ _ _ h1)
  refine le_trans ?_ (le_max1 _ _ _ h2)
  refine le_trans ?_ (le_max1 _ _ _ h3)
  refine le_trans ?_ (le_max1 _ _ _ h4)
  refine le_trans ?_ (le_max1 _ _ _ h5)
  refine le_trans ?_ (le_max1 _ _ _ h6)
  refine le_trans ?_ (le_max1 _ _ _ h7)
  refine le_trans ?_ (le_max1 _ _ _ h8)
  refine le_trans ?_ (le_max1 _ _ _ h9)
  refine le_trans ?_ (le_max1 _ _ _ h10)
  exact le_max1 _ _ _ h11

private lemma maxQ3_12_eq_of_allKnown {t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : Tri}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool}
    (h0 : matchTri t0 b0) (h1 : matchTri t1 b1) (h2 : matchTri t2 b2) (h3 : matchTri t3 b3)
    (h4 : matchTri t4 b4) (h5 : matchTri t5 b5) (h6 : matchTri t6 b6) (h7 : matchTri t7 b7)
    (h8 : matchTri t8 b8) (h9 : matchTri t9 b9) (h10 : matchTri t10 b10) (h11 : matchTri t11 b11)
    (hk : allKnown12 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 = true) :
    maxQ3_12 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 = q3Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 := by
  rw [← q3Lookup_eq_q3Fast]
  simp only [allKnown12, Bool.not_eq_true', Bool.or_eq_false_iff] at hk
  rcases hk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨u0, u1⟩, u2⟩, u3⟩, u4⟩, u5⟩, u6⟩, u7⟩, u8⟩, u9⟩, u10⟩, u11⟩
  dsimp only [maxQ3_12]
  rw [max1_eq_of_isTriU_false _ _ _ h0 u0, max1_eq_of_isTriU_false _ _ _ h1 u1,
      max1_eq_of_isTriU_false _ _ _ h2 u2, max1_eq_of_isTriU_false _ _ _ h3 u3,
      max1_eq_of_isTriU_false _ _ _ h4 u4, max1_eq_of_isTriU_false _ _ _ h5 u5,
      max1_eq_of_isTriU_false _ _ _ h6 u6, max1_eq_of_isTriU_false _ _ _ h7 u7,
      max1_eq_of_isTriU_false _ _ _ h8 u8, max1_eq_of_isTriU_false _ _ _ h9 u9,
      max1_eq_of_isTriU_false _ _ _ h10 u10, max1_eq_of_isTriU_false _ _ _ h11 u11]

private lemma evalQ3Fast_le_maxQ3Tri (st : State32) (g : Q4Bits) (hs : stateMatches st g) (fk : Fin 8) :
    evalQ3Fast (extractFacetQ3 fk g) ≤ maxQ3Tri st fk.val := by
  fin_cases fk
  · exact evalQ3Fast_le_maxQ3_12 (hs 1) (hs 2) (hs 3) (hs 8) (hs 9) (hs 13) (hs 14) (hs 18) (hs 21) (hs 22) (hs 26) (hs 29)
  · exact evalQ3Fast_le_maxQ3_12 (hs 4) (hs 5) (hs 6) (hs 10) (hs 11) (hs 15) (hs 16) (hs 19) (hs 23) (hs 24) (hs 27) (hs 30)
  · exact evalQ3Fast_le_maxQ3_12 (hs 0) (hs 2) (hs 3) (hs 5) (hs 6) (hs 12) (hs 14) (hs 16) (hs 20) (hs 22) (hs 24) (hs 28)
  · exact evalQ3Fast_le_maxQ3_12 (hs 7) (hs 8) (hs 9) (hs 10) (hs 11) (hs 17) (hs 18) (hs 19) (hs 25) (hs 26) (hs 27) (hs 31)
  · exact evalQ3Fast_le_maxQ3_12 (hs 0) (hs 1) (hs 3) (hs 4) (hs 6) (hs 7) (hs 9) (hs 11) (hs 20) (hs 21) (hs 23) (hs 25)
  · exact evalQ3Fast_le_maxQ3_12 (hs 12) (hs 13) (hs 14) (hs 15) (hs 16) (hs 17) (hs 18) (hs 19) (hs 28) (hs 29) (hs 30) (hs 31)
  · exact evalQ3Fast_le_maxQ3_12 (hs 0) (hs 1) (hs 2) (hs 4) (hs 5) (hs 7) (hs 8) (hs 10) (hs 12) (hs 13) (hs 15) (hs 17)
  · exact evalQ3Fast_le_maxQ3_12 (hs 20) (hs 21) (hs 22) (hs 23) (hs 24) (hs 25) (hs 26) (hs 27) (hs 28) (hs 29) (hs 30) (hs 31)

private lemma maxQ3Tri_eq_evalQ3Fast_of_allKnown (st : State32) (g : Q4Bits) (hs : stateMatches st g) (fk : Fin 8)
    (hk : facetAllKnown st fk.val = true) : maxQ3Tri st fk.val = evalQ3Fast (extractFacetQ3 fk g) := by
  fin_cases fk
  · exact maxQ3_12_eq_of_allKnown (hs 1) (hs 2) (hs 3) (hs 8) (hs 9) (hs 13) (hs 14) (hs 18) (hs 21) (hs 22) (hs 26) (hs 29) hk
  · exact maxQ3_12_eq_of_allKnown (hs 4) (hs 5) (hs 6) (hs 10) (hs 11) (hs 15) (hs 16) (hs 19) (hs 23) (hs 24) (hs 27) (hs 30) hk
  · exact maxQ3_12_eq_of_allKnown (hs 0) (hs 2) (hs 3) (hs 5) (hs 6) (hs 12) (hs 14) (hs 16) (hs 20) (hs 22) (hs 24) (hs 28) hk
  · exact maxQ3_12_eq_of_allKnown (hs 7) (hs 8) (hs 9) (hs 10) (hs 11) (hs 17) (hs 18) (hs 19) (hs 25) (hs 26) (hs 27) (hs 31) hk
  · exact maxQ3_12_eq_of_allKnown (hs 0) (hs 1) (hs 3) (hs 4) (hs 6) (hs 7) (hs 9) (hs 11) (hs 20) (hs 21) (hs 23) (hs 25) hk
  · exact maxQ3_12_eq_of_allKnown (hs 12) (hs 13) (hs 14) (hs 15) (hs 16) (hs 17) (hs 18) (hs 19) (hs 28) (hs 29) (hs 30) (hs 31) hk
  · exact maxQ3_12_eq_of_allKnown (hs 0) (hs 1) (hs 2) (hs 4) (hs 5) (hs 7) (hs 8) (hs 10) (hs 12) (hs 13) (hs 15) (hs 17) hk
  · exact maxQ3_12_eq_of_allKnown (hs 20) (hs 21) (hs 22) (hs 23) (hs 24) (hs 25) (hs 26) (hs 27) (hs 28) (hs 29) (hs 30) (hs 31) hk

private lemma evalB2Fast_le_maxB2_16 {t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : Tri}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool}
    (h0 : matchTri t0 b0) (h1 : matchTri t1 b1) (h2 : matchTri t2 b2) (h3 : matchTri t3 b3)
    (h4 : matchTri t4 b4) (h5 : matchTri t5 b5) (h6 : matchTri t6 b6) (h7 : matchTri t7 b7)
    (h8 : matchTri t8 b8) (h9 : matchTri t9 b9) (h10 : matchTri t10 b10) (h11 : matchTri t11 b11)
    (h12 : matchTri t12 b12) (h13 : matchTri t13 b13) (h14 : matchTri t14 b14) (h15 : matchTri t15 b15) :
    b2Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 ≤
      maxB2_16 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 := by
  rw [← b2Lookup_eq_b2Fast]
  dsimp only [maxB2_16]
  refine le_trans ?_ (le_max1 _ _ _ h0)
  refine le_trans ?_ (le_max1 _ _ _ h1)
  refine le_trans ?_ (le_max1 _ _ _ h2)
  refine le_trans ?_ (le_max1 _ _ _ h3)
  refine le_trans ?_ (le_max1 _ _ _ h4)
  refine le_trans ?_ (le_max1 _ _ _ h5)
  refine le_trans ?_ (le_max1 _ _ _ h6)
  refine le_trans ?_ (le_max1 _ _ _ h7)
  refine le_trans ?_ (le_max1 _ _ _ h8)
  refine le_trans ?_ (le_max1 _ _ _ h9)
  refine le_trans ?_ (le_max1 _ _ _ h10)
  refine le_trans ?_ (le_max1 _ _ _ h11)
  refine le_trans ?_ (le_max1 _ _ _ h12)
  refine le_trans ?_ (le_max1 _ _ _ h13)
  refine le_trans ?_ (le_max1 _ _ _ h14)
  exact le_max1 _ _ _ h15

private lemma evalB2Fast_le_maxB2Tri (st : State32) (g : Q4Bits) (hs : stateMatches st g) (bi : Fin 16) :
    evalB2Fast (extractBallB2 bi g) ≤ maxB2Tri st bi.val := by
  fin_cases bi
  · exact evalB2Fast_le_maxB2_16 (hs 0) (hs 1) (hs 2) (hs 3) (hs 4) (hs 5) (hs 6) (hs 7) (hs 8) (hs 9) (hs 12) (hs 13) (hs 14) (hs 20) (hs 21) (hs 22)
  · exact evalB2Fast_le_maxB2_16 (hs 0) (hs 4) (hs 5) (hs 6) (hs 1) (hs 2) (hs 3) (hs 7) (hs 10) (hs 11) (hs 12) (hs 15) (hs 16) (hs 20) (hs 23) (hs 24)
  · exact evalB2Fast_le_maxB2_16 (hs 7) (hs 1) (hs 8) (hs 9) (hs 4) (hs 10) (hs 11) (hs 0) (hs 2) (hs 3) (hs 17) (hs 13) (hs 18) (hs 25) (hs 21) (hs 26)
  · exact evalB2Fast_le_maxB2_16 (hs 7) (hs 4) (hs 10) (hs 11) (hs 1) (hs 8) (hs 9) (hs 0) (hs 5) (hs 6) (hs 17) (hs 15) (hs 19) (hs 25) (hs 23) (hs 27)
  · exact evalB2Fast_le_maxB2_16 (hs 12) (hs 13) (hs 2) (hs 14) (hs 15) (hs 5) (hs 16) (hs 17) (hs 8) (hs 18) (hs 0) (hs 1) (hs 3) (hs 28) (hs 29) (hs 22)
  · exact evalB2Fast_le_maxB2_16 (hs 12) (hs 15) (hs 5) (hs 16) (hs 13) (hs 2) (hs 14) (hs 17) (hs 10) (hs 19) (hs 0) (hs 4) (hs 6) (hs 28) (hs 30) (hs 24)
  · exact evalB2Fast_le_maxB2_16 (hs 17) (hs 13) (hs 8) (hs 18) (hs 15) (hs 10) (hs 19) (hs 12) (hs 2) (hs 14) (hs 7) (hs 1) (hs 9) (hs 31) (hs 29) (hs 26)
  · exact evalB2Fast_le_maxB2_16 (hs 17) (hs 15) (hs 10) (hs 19) (hs 13) (hs 8) (hs 18) (hs 12) (hs 5) (hs 16) (hs 7) (hs 4) (hs 11) (hs 31) (hs 30) (hs 27)
  · exact evalB2Fast_le_maxB2_16 (hs 20) (hs 21) (hs 22) (hs 3) (hs 23) (hs 24) (hs 6) (hs 25) (hs 26) (hs 9) (hs 28) (hs 29) (hs 14) (hs 0) (hs 1) (hs 2)
  · exact evalB2Fast_le_maxB2_16 (hs 20) (hs 23) (hs 24) (hs 6) (hs 21) (hs 22) (hs 3) (hs 25) (hs 27) (hs 11) (hs 28) (hs 30) (hs 16) (hs 0) (hs 4) (hs 5)
  · exact evalB2Fast_le_maxB2_16 (hs 25) (hs 21) (hs 26) (hs 9) (hs 23) (hs 27) (hs 11) (hs 20) (hs 22) (hs 3) (hs 31) (hs 29) (hs 18) (hs 7) (hs 1) (hs 8)
  · exact evalB2Fast_le_maxB2_16 (hs 25) (hs 23) (hs 27) (hs 11) (hs 21) (hs 26) (hs 9) (hs 20) (hs 24) (hs 6) (hs 31) (hs 30) (hs 19) (hs 7) (hs 4) (hs 10)
  · exact evalB2Fast_le_maxB2_16 (hs 28) (hs 29) (hs 22) (hs 14) (hs 30) (hs 24) (hs 16) (hs 31) (hs 26) (hs 18) (hs 20) (hs 21) (hs 3) (hs 12) (hs 13) (hs 2)
  · exact evalB2Fast_le_maxB2_16 (hs 28) (hs 30) (hs 24) (hs 16) (hs 29) (hs 22) (hs 14) (hs 31) (hs 27) (hs 19) (hs 20) (hs 23) (hs 6) (hs 12) (hs 15) (hs 5)
  · exact evalB2Fast_le_maxB2_16 (hs 31) (hs 29) (hs 26) (hs 18) (hs 30) (hs 27) (hs 19) (hs 28) (hs 22) (hs 14) (hs 25) (hs 21) (hs 9) (hs 17) (hs 13) (hs 8)
  · exact evalB2Fast_le_maxB2_16 (hs 31) (hs 30) (hs 27) (hs 19) (hs 29) (hs 26) (hs 18) (hs 28) (hs 24) (hs 16) (hs 25) (hs 23) (hs 11) (hs 17) (hs 15) (hs 10)

inductive CertTree
  | boundOk
  | c6Fail (cid : ℕ)
  | symFail (fk : ℕ)
  | forceZero (e cid : ℕ) (sub : CertTree)
  | evalFacet (fk mx newCurUb : ℕ) (sub : CertTree)
  | evalBall (bi mx newCurUb : ℕ) (sub : CertTree)
  | branch (e : ℕ) (t1 t0 : CertTree)
  deriving DecidableEq

def checkFZ (st : State32) (e cid : ℕ) : Bool :=
  let (e0, e1, e2, e3, e4, e5) := c6CyclesQ4Nat cid
  let chk (x : ℕ) := Nat.beq x e || isTriO (getE st x)
  isTriU (getE st e) && (Nat.beq e e0 || Nat.beq e e1 || Nat.beq e e2 || Nat.beq e e3 || Nat.beq e e4 || Nat.beq e e5) &&
  chk e0 && chk e1 && chk e2 && chk e3 && chk e4 && chk e5

def checkTree (r0Score : ℕ) (st : State32) (ubF : UbF7) (ubB : UbB16) (curUb : ℕ) : CertTree → Bool
  | .boundOk => Nat.ble curUb M_target_shift
  | .c6Fail cid =>
      let (e0, e1, e2, e3, e4, e5) := c6CyclesQ4Nat cid
      Nat.blt cid 128 &&
      isTriO (getE st e0) && isTriO (getE st e1) && isTriO (getE st e2) &&
      isTriO (getE st e3) && isTriO (getE st e4) && isTriO (getE st e5)
  | .symFail fk =>
      Nat.blt fk 8 && !(Nat.beq fk 6) && facetAllKnown st fk && Nat.blt r0Score (maxQ3Tri st fk)
  | .forceZero e cid sub =>
      Nat.blt e 32 && Nat.blt cid 128 && checkFZ st e cid && checkTree r0Score (setE st e .z) ubF ubB curUb sub
  | .evalFacet fk mx newCurUb sub =>
      let old := getUbF ubF fk
      Nat.blt fk 8 && !(Nat.beq fk 6) && Nat.ble (maxQ3Tri st fk) mx && Nat.blt mx old && Nat.beq curUb (newCurUb + (old - mx)) &&
      checkTree r0Score st (setUbF ubF fk mx) ubB newCurUb sub
  | .evalBall bi mx newCurUb sub =>
      let old := getUbB ubB bi
      Nat.blt bi 16 && Nat.ble (maxB2Tri st bi) mx && Nat.blt mx old && Nat.beq curUb (newCurUb + (old - mx)) &&
      checkTree r0Score st ubF (setUbB ubB bi mx) newCurUb sub
  | .branch e t1 t0 =>
      Nat.blt e 32 && isTriU (getE st e) &&
      checkTree r0Score (setE st e .o) ubF ubB curUb t1 &&
      checkTree r0Score (setE st e .z) ubF ubB curUb t0

def allUState8 : State8 := { t0 := .u, t1 := .u, t2 := .u, t3 := .u, t4 := .u, t5 := .u, t6 := .u, t7 := .u }
def initState (ri : Fin 116) : State32 :=
  let q := q3RepBits ri
  let s0 : State32 := { b0 := allUState8, b1 := allUState8, b2 := allUState8, b3 := allUState8 }
  let s1 := setE s0 0 (if q.e01 then .o else .z)
  let s2 := setE s1 1 (if q.e02 then .o else .z)
  let s3 := setE s2 2 (if q.e04 then .o else .z)
  let s4 := setE s3 4 (if q.e13 then .o else .z)
  let s5 := setE s4 5 (if q.e15 then .o else .z)
  let s6 := setE s5 7 (if q.e23 then .o else .z)
  let s7 := setE s6 8 (if q.e26 then .o else .z)
  let s8 := setE s7 10 (if q.e37 then .o else .z)
  let s9 := setE s8 12 (if q.e45 then .o else .z)
  let s10 := setE s9 13 (if q.e46 then .o else .z)
  let s11 := setE s10 15 (if q.e57 then .o else .z)
  let s12 := setE s11 17 (if q.e67 then .o else .z)
  s12

def initUbF (r0Score : ℕ) : UbF7 :=
  let m := Nat.min r0Score M3_shift
  { u0 := m, u1 := m, u2 := m, u3 := m, u4 := m, u5 := m, u7 := m }

def initUbB : UbB16 :=
  let b8 : UbB8 := { n0 := M4_shift, n1 := M4_shift, n2 := M4_shift, n3 := M4_shift, n4 := M4_shift, n5 := M4_shift, n6 := M4_shift, n7 := M4_shift }
  { lo := b8, hi := b8 }

def evalQ3Lookup (q : Q3Bits) : ℕ :=
  q3Lookup q.e01 q.e02 q.e04 q.e13 q.e15 q.e23 q.e26 q.e37 q.e45 q.e46 q.e57 q.e67

lemma evalQ3Lookup_eq_fast (q : Q3Bits) : evalQ3Lookup q = evalQ3Fast q :=
  q3Lookup_eq_q3Fast q.e01 q.e02 q.e04 q.e13 q.e15 q.e23 q.e26 q.e37 q.e45 q.e46 q.e57 q.e67

def checkRoot (ri : Fin 116) (r0Score initCurUb : ℕ) (t : CertTree) : Bool :=
  Nat.beq (evalQ3Lookup (q3RepBits ri)) r0Score &&
  Nat.beq initCurUb (r0Score + 7 * Nat.min r0Score M3_shift + 16 * M4_shift) &&
  checkTree r0Score (initState ri) (initUbF r0Score) initUbB initCurUb t

def validBounds (r0Score : ℕ) (ubF : UbF7) (ubB : UbB16) (curUb : ℕ) (g : Q4Bits) : Prop :=
  evalQ3Fast (extractFacetQ3 6 g) = r0Score ∧
  (∀ fk : Fin 8, fk.val ≠ 6 → evalQ3Fast (extractFacetQ3 fk g) ≤ getUbF ubF fk.val) ∧
  (∀ bi : Fin 16, evalB2Fast (extractBallB2 bi g) ≤ getUbB ubB bi.val) ∧
  curUb = r0Score + ubFSum ubF + ubBSum ubB

private lemma score_le_of_validBounds {r0Score : ℕ} {ubF : UbF7} {ubB : UbB16} {curUb : ℕ} {g : Q4Bits}
    (hc : isQ4C6Free g) (hv : validBounds r0Score ubF ubB curUb g) (hle : curUb ≤ M_target_shift) :
    q4ScoreGauged g ≤ M_target := by
  rcases hv with ⟨hr0, hf, hb, hcur⟩
  have hnat :
      (∑ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g)) + (∑ bi : Fin 16, evalB2Fast (extractBallB2 bi g)) ≤ M_target_shift := by
    have hsum16 : ∀ (f : Fin 16 → ℕ), (∑ v : Fin 16, f v) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 := fun f => by simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc, add_assoc]
    rw [Fin.sum_univ_eight, hsum16]
    have q0 : evalQ3Fast (extractFacetQ3 0 g) ≤ ubF.u0 := hf 0 (by decide)
    have q1 : evalQ3Fast (extractFacetQ3 1 g) ≤ ubF.u1 := hf 1 (by decide)
    have q2 : evalQ3Fast (extractFacetQ3 2 g) ≤ ubF.u2 := hf 2 (by decide)
    have q3 : evalQ3Fast (extractFacetQ3 3 g) ≤ ubF.u3 := hf 3 (by decide)
    have q4 : evalQ3Fast (extractFacetQ3 4 g) ≤ ubF.u4 := hf 4 (by decide)
    have q5 : evalQ3Fast (extractFacetQ3 5 g) ≤ ubF.u5 := hf 5 (by decide)
    have q6 : evalQ3Fast (extractFacetQ3 6 g) = r0Score := hr0
    have q7 : evalQ3Fast (extractFacetQ3 7 g) ≤ ubF.u7 := hf 7 (by decide)
    have p0 : evalB2Fast (extractBallB2 0 g) ≤ ubB.lo.n0 := by simpa [getUbB] using hb 0
    have p1 : evalB2Fast (extractBallB2 1 g) ≤ ubB.lo.n1 := by simpa [getUbB] using hb 1
    have p2 : evalB2Fast (extractBallB2 2 g) ≤ ubB.lo.n2 := by simpa [getUbB] using hb 2
    have p3 : evalB2Fast (extractBallB2 3 g) ≤ ubB.lo.n3 := by simpa [getUbB] using hb 3
    have p4 : evalB2Fast (extractBallB2 4 g) ≤ ubB.lo.n4 := by simpa [getUbB] using hb 4
    have p5 : evalB2Fast (extractBallB2 5 g) ≤ ubB.lo.n5 := by simpa [getUbB] using hb 5
    have p6 : evalB2Fast (extractBallB2 6 g) ≤ ubB.lo.n6 := by simpa [getUbB] using hb 6
    have p7 : evalB2Fast (extractBallB2 7 g) ≤ ubB.lo.n7 := by simpa [getUbB] using hb 7
    have p8 : evalB2Fast (extractBallB2 8 g) ≤ ubB.hi.n0 := by simpa [getUbB] using hb 8
    have p9 : evalB2Fast (extractBallB2 9 g) ≤ ubB.hi.n1 := by simpa [getUbB] using hb 9
    have p10 : evalB2Fast (extractBallB2 10 g) ≤ ubB.hi.n2 := by simpa [getUbB] using hb 10
    have p11 : evalB2Fast (extractBallB2 11 g) ≤ ubB.hi.n3 := by simpa [getUbB] using hb 11
    have p12 : evalB2Fast (extractBallB2 12 g) ≤ ubB.hi.n4 := by simpa [getUbB] using hb 12
    have p13 : evalB2Fast (extractBallB2 13 g) ≤ ubB.hi.n5 := by simpa [getUbB] using hb 13
    have p14 : evalB2Fast (extractBallB2 14 g) ≤ ubB.hi.n6 := by simpa [getUbB] using hb 14
    have p15 : evalB2Fast (extractBallB2 15 g) ≤ ubB.hi.n7 := by simpa [getUbB] using hb 15
    dsimp only [ubFSum, ubBSum, sumB8] at hcur
    omega
  have hfq : ∀ fk : Fin 8, (evalQ3Fast (extractFacetQ3 fk g) : ℤ) = evalQ3G (extractFacetQ3 fk g) + (Q3_OFF : ℤ) := fun fk => by
    rw [evalQ3Fast_eq, isQ3C6Free_of_isQ4C6Free g hc fk]; rfl
  have hfb : ∀ bi : Fin 16, (evalB2Fast (extractBallB2 bi g) : ℤ) = evalB2G (extractBallB2 bi g) + (B2_OFF : ℤ) := fun bi => by
    rw [evalB2Fast_eq, isB2C6Free_of_isQ4C6Free g hc bi]; rfl
  have hZ := Int.ofNat_le.mpr hnat
  push_cast at hZ
  simp_rw [hfq, hfb, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hZ
  unfold q4ScoreGauged
  dsimp only [Q3_OFF, B2_OFF, M_target_shift, M_target] at hZ ⊢
  omega

lemma checkTree_sound (r0Score : ℕ) (t : CertTree) :
    ∀ (st : State32) (ubF : UbF7) (ubB : UbB16) (curUb : ℕ),
      checkTree r0Score st ubF ubB curUb t = true →
      ∀ (g : Q4Bits), isQ4C6Free g → stateMatches st g →
        (∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ r0Score) →
        validBounds r0Score ubF ubB curUb g →
        q4ScoreGauged g ≤ M_target := by
  induction t with
  | boundOk =>
    intro st ubF ubB curUb hchk g hc _hs _hmax hv
    dsimp only [checkTree] at hchk
    exact score_le_of_validBounds hc hv (Nat.le_of_ble_eq_true hchk)
  | c6Fail cid =>
    intro st ubF ubB curUb hchk g hc hs _hmax _hv
    dsimp only [checkTree] at hchk
    simp only [Bool.and_eq_true] at hchk
    rcases hchk with ⟨⟨⟨⟨⟨⟨hcid_lt, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩
    have hlt : cid < 128 := by simpa [Nat.blt_eq] using hcid_lt
    let cidF : Fin 128 := ⟨cid, hlt⟩
    have hnat : c6CyclesQ4Nat cidF.val = let (a,b,c,d,e,f) := c6CyclesQ4 cidF; (a.val, b.val, c.val, d.val, e.val, f.val) := c6CyclesQ4Nat_eq cidF
    rcases hc6 : c6CyclesQ4 cidF with ⟨e0, e1, e2, e3, e4, e5⟩
    rw [hc6] at hnat; dsimp only at hnat
    change c6CyclesQ4Nat cid = (e0.val, e1.val, e2.val, e3.val, e4.val, e5.val) at hnat
    rw [hnat] at h0 h1 h2 h3 h4 h5; dsimp only at h0 h1 h2 h3 h4 h5
    have g0 := hs e0; rw [eq_o_of_isTriO h0] at g0
    have g1 := hs e1; rw [eq_o_of_isTriO h1] at g1
    have g2 := hs e2; rw [eq_o_of_isTriO h2] at g2
    have g3 := hs e3; rw [eq_o_of_isTriO h3] at g3
    have g4 := hs e4; rw [eq_o_of_isTriO h4] at g4
    have g5 := hs e5; rw [eq_o_of_isTriO h5] at g5
    have hbad := hc cidF; rw [hc6] at hbad
    exact absurd ⟨g0, g1, g2, g3, g4, g5⟩ hbad
  | symFail fk =>
    intro st ubF ubB curUb hchk g _hc hs hmax _hv
    dsimp only [checkTree] at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at hchk
    rcases hchk with ⟨⟨⟨hfk_lt, _⟩, hkn⟩, hlt⟩
    let fkF : Fin 8 := ⟨fk, hfk_lt⟩
    have heq : maxQ3Tri st fkF.val = evalQ3Fast (extractFacetQ3 fkF g) :=
      maxQ3Tri_eq_evalQ3Fast_of_allKnown st g hs fkF hkn
    have hm := hmax fkF
    change maxQ3Tri st fk = evalQ3Fast (extractFacetQ3 fkF g) at heq
    omega
  | forceZero e cid sub ih =>
    intro st ubF ubB curUb hchk g hc hs hmax hv
    dsimp only [checkTree] at hchk
    simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
    rcases hchk with ⟨⟨⟨he_lt, hcid_lt⟩, hfz⟩, hsub⟩
    let eF : Fin 32 := ⟨e, he_lt⟩
    let cidF : Fin 128 := ⟨cid, hcid_lt⟩
    have hge_false : getQ4E g eF = false := by
      dsimp only [checkFZ] at hfz
      have hnat := c6CyclesQ4Nat_eq cidF
      rcases hc6 : c6CyclesQ4 cidF with ⟨e0, e1, e2, e3, e4, e5⟩
      rw [hc6] at hnat; dsimp only at hnat
      change c6CyclesQ4Nat cid = (e0.val, e1.val, e2.val, e3.val, e4.val, e5.val) at hnat
      rw [hnat] at hfz; dsimp only at hfz
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hfz
      rcases hfz with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩
      by_contra hnt
      have htrue : getQ4E g eF = true := Bool.eq_true_of_not_eq_false hnt
      have chk_mem : ∀ x : Fin 32, (x.val = e ∨ isTriO (getE st x.val) = true) → getQ4E g x = true := by
        intro x hx; rcases hx with hxv | hxo
        · have : x = eF := Fin.ext hxv; subst this; exact htrue
        · have := hs x; rw [eq_o_of_isTriO hxo] at this; exact this
      have hbad := hc cidF; rw [hc6] at hbad
      exact hbad ⟨chk_mem e0 h0, chk_mem e1 h1, chk_mem e2 h2, chk_mem e3 h3, chk_mem e4 h4, chk_mem e5 h5⟩
    exact ih (setE st eF.val .z) ubF ubB curUb hsub g hc (stateMatches_setE st g eF .z hs hge_false) hmax hv
  | evalFacet fk mx newCurUb sub ih =>
    intro st ubF ubB curUb hchk g hc hs hmax hv
    dsimp only [checkTree] at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.beq_eq] at hchk
    rcases hchk with ⟨⟨⟨⟨⟨hfk_lt, hne6⟩, hmx_b⟩, hlt⟩, hdiff⟩, hsub⟩
    have hmx : maxQ3Tri st fk ≤ mx := Nat.le_of_ble_eq_true hmx_b
    let fkF : Fin 8 := ⟨fk, hfk_lt⟩
    have hne6' : fkF.val ≠ 6 := fun h => by have hb : Nat.beq fk 6 = true := Nat.beq_eq.mpr h; rw [hb] at hne6; exact Bool.noConfusion hne6
    have hv' : validBounds r0Score (setUbF ubF fk mx) ubB newCurUb g := by
      rcases hv with ⟨hr0, hf, hb, hcur⟩
      refine ⟨hr0, ?_, hb, ?_⟩
      · intro fk' hne6''
        by_cases heq : fk' = fkF
        · rw [heq]; change evalQ3Fast (extractFacetQ3 fkF g) ≤ getUbF (setUbF ubF fkF.val mx) fkF.val
          rw [getUbF_setUbF_self ubF fkF hne6']; exact le_trans (evalQ3Fast_le_maxQ3Tri st g hs fkF) hmx
        · change evalQ3Fast (extractFacetQ3 fk' g) ≤ getUbF (setUbF ubF fkF.val mx) fk'.val
          rw [getUbF_setUbF_ne ubF heq]; exact hf fk' hne6''
      · have hsum := ubFSum_setUbF ubF fkF hne6' mx hlt
        change ubFSum (setUbF ubF fk mx) + (getUbF ubF fk - mx) = ubFSum ubF at hsum
        omega
    exact ih st _ ubB _ hsub g hc hs hmax hv'
  | evalBall bi mx newCurUb sub ih =>
    intro st ubF ubB curUb hchk g hc hs hmax hv
    dsimp only [checkTree] at hchk
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hchk
    rcases hchk with ⟨⟨⟨⟨hbi_lt, hmx_b⟩, hlt⟩, hdiff⟩, hsub⟩
    have hmx : maxB2Tri st bi ≤ mx := Nat.le_of_ble_eq_true hmx_b
    let biF : Fin 16 := ⟨bi, hbi_lt⟩
    have hv' : validBounds r0Score ubF (setUbB ubB bi mx) newCurUb g := by
      rcases hv with ⟨hr0, hf, hb, hcur⟩
      refine ⟨hr0, hf, ?_, ?_⟩
      · intro bi'
        by_cases heq : bi' = biF
        · rw [heq]; change evalB2Fast (extractBallB2 biF g) ≤ getUbB (setUbB ubB biF.val mx) biF.val
          rw [getUbB_setUbB_self]; exact le_trans (evalB2Fast_le_maxB2Tri st g hs biF) hmx
        · change evalB2Fast (extractBallB2 bi' g) ≤ getUbB (setUbB ubB biF.val mx) bi'.val
          rw [getUbB_setUbB_ne ubB heq]; exact hb bi'
      · have hsum := ubBSum_setUbB ubB biF mx hlt
        change ubBSum (setUbB ubB bi mx) + (getUbB ubB bi - mx) = ubBSum ubB at hsum
        omega
    exact ih st ubF _ _ hsub g hc hs hmax hv'
  | branch e t1 t0 ih1 ih0 =>
    intro st ubF ubB curUb hchk g hc hs hmax hv
    dsimp only [checkTree] at hchk
    simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
    rcases hchk with ⟨⟨⟨he_lt, _⟩, ht1⟩, ht0⟩
    let eF : Fin 32 := ⟨e, he_lt⟩
    cases hge : getQ4E g eF with
    | true => exact ih1 (setE st eF.val .o) ubF ubB curUb ht1 g hc (stateMatches_setE st g eF .o hs hge) hmax hv
    | false => exact ih0 (setE st eF.val .z) ubF ubB curUb ht0 g hc (stateMatches_setE st g eF .z hs hge) hmax hv

private lemma stateMatches_init (ri : Fin 116) (g : Q4Bits) (hf : extractFacetQ3 6 g = q3RepBits ri) :
    stateMatches (initState ri) g := by
  have hf' : ∀ k : Fin 12, getQ3Edge (q3RepBits ri) k = getQ4E g (facetEdge 6 k) := fun k => by
    rw [← hf, getQ3Edge_extractFacetQ3]
  have hin : ∀ (st : State32) (e : Fin 32) (b : Bool), stateMatches st g → b = getQ4E g e → stateMatches (setE st e.val (if b then .o else .z)) g := by
    intro st e b hst hb; apply stateMatches_setE st g e _ hst
    cases b with | true => exact hb.symm | false => exact hb.symm
  dsimp only [initState]
  have hm0 : stateMatches { b0 := allUState8, b1 := allUState8, b2 := allUState8, b3 := allUState8 } g := by
    intro e; fin_cases e <;> trivial
  have hm1 := hin _ ⟨0, by decide⟩ _ hm0 (hf' 0)
  have hm2 := hin _ ⟨1, by decide⟩ _ hm1 (hf' 1)
  have hm3 := hin _ ⟨2, by decide⟩ _ hm2 (hf' 2)
  have hm4 := hin _ ⟨4, by decide⟩ _ hm3 (hf' 3)
  have hm5 := hin _ ⟨5, by decide⟩ _ hm4 (hf' 4)
  have hm6 := hin _ ⟨7, by decide⟩ _ hm5 (hf' 5)
  have hm7 := hin _ ⟨8, by decide⟩ _ hm6 (hf' 6)
  have hm8 := hin _ ⟨10, by decide⟩ _ hm7 (hf' 7)
  have hm9 := hin _ ⟨12, by decide⟩ _ hm8 (hf' 8)
  have hm10 := hin _ ⟨13, by decide⟩ _ hm9 (hf' 9)
  have hm11 := hin _ ⟨15, by decide⟩ _ hm10 (hf' 10)
  have hm12 := hin _ ⟨17, by decide⟩ _ hm11 (hf' 11)
  exact hm12

theorem checkRoot_sound (ri : Fin 116) (r0Score initCurUb : ℕ) (t : CertTree)
    (hchk : checkRoot ri r0Score initCurUb t = true)
    (g : Q4Bits) (hc : isQ4C6Free g)
    (hf : extractFacetQ3 6 g = q3RepBits ri)
    (hmax : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ evalQ3Fast (extractFacetQ3 6 g)) :
    q4ScoreGauged g ≤ M_target := by
  simp only [checkRoot, Bool.and_eq_true, Nat.beq_eq] at hchk
  rcases hchk with ⟨⟨hr0, hcu⟩, htree⟩
  rw [evalQ3Lookup_eq_fast] at hr0
  refine checkTree_sound r0Score t (initState ri) (initUbF r0Score) initUbB initCurUb htree g hc ?_ ?_ ?_
  · exact stateMatches_init ri g hf
  · intro fk; rw [← hr0, ← hf]; exact hmax fk
  · refine ⟨by rw [hf, hr0], ?_, ?_, ?_⟩
    · intro fk hne6
      have h1 : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ r0Score := fun fk => by rw [← hr0, ← hf]; exact hmax fk
      fin_cases fk <;> simp [getUbF, initUbF] at hne6 ⊢ <;> exact ⟨h1 _, evalQ3Fast_le_M3 _⟩
    · intro bi
      have h2 := evalB2Fast_le_M4 (extractBallB2 bi g)
      fin_cases bi <;> simpa [getUbB, initUbB] using h2
    · dsimp only [ubFSum, initUbF, ubBSum, initUbB, sumB8] at hcu ⊢; omega

theorem checkTree_of_branch {r0 : ℕ} {st st1 st0 : State32} {ubF : UbF7} {ubB : UbB16} {curUb e : ℕ} {t1 t0 : CertTree}
    (h1 : checkTree r0 st1 ubF ubB curUb t1 = true)
    (h0 : checkTree r0 st0 ubF ubB curUb t0 = true)
    (h1eq : setE st e .o = st1) (h0eq : setE st e .z = st0)
    (he : (Nat.blt e 32 && isTriU (getE st e)) = true) :
    checkTree r0 st ubF ubB curUb (.branch e t1 t0) = true := by
  dsimp only [checkTree]; rw [h1eq, h0eq]; simp [he, h1, h0]

theorem checkTree_of_forceZero {r0 : ℕ} {st st' : State32} {ubF : UbF7} {ubB : UbB16} {curUb e cid : ℕ} {sub : CertTree}
    (hsub : checkTree r0 st' ubF ubB curUb sub = true)
    (hsteq : setE st e .z = st')
    (hfz : (Nat.blt e 32 && Nat.blt cid 128 && checkFZ st e cid) = true) :
    checkTree r0 st ubF ubB curUb (.forceZero e cid sub) = true := by
  dsimp only [checkTree]; rw [hsteq]; simp [hfz, hsub]

theorem checkTree_of_evalFacet {r0 : ℕ} {st : State32} {ubF ubF' : UbF7} {ubB : UbB16} {curUb fk mx newCurUb : ℕ} {sub : CertTree}
    (hsub : checkTree r0 st ubF' ubB newCurUb sub = true)
    (hufeq : setUbF ubF fk mx = ubF')
    (hg : (Nat.blt fk 8 && !(Nat.beq fk 6) &&
      (let old := getUbF ubF fk; Nat.ble (maxQ3Tri st fk) mx && Nat.blt mx old && Nat.beq curUb (newCurUb + (old - mx)))) = true) :
    checkTree r0 st ubF ubB curUb (.evalFacet fk mx newCurUb sub) = true := by
  dsimp only [checkTree] at ⊢; rw [hufeq]
  simp only [Bool.and_eq_true] at hg ⊢
  rcases hg with ⟨⟨h1, h2⟩, ⟨⟨h3, h4⟩, h5⟩⟩
  exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hsub⟩

theorem checkTree_of_evalBall {r0 : ℕ} {st : State32} {ubF : UbF7} {ubB ubB' : UbB16} {curUb bi mx newCurUb : ℕ} {sub : CertTree}
    (hsub : checkTree r0 st ubF ubB' newCurUb sub = true)
    (hubeq : setUbB ubB bi mx = ubB')
    (hg : (Nat.blt bi 16 &&
      (let old := getUbB ubB bi; Nat.ble (maxB2Tri st bi) mx && Nat.blt mx old && Nat.beq curUb (newCurUb + (old - mx)))) = true) :
    checkTree r0 st ubF ubB curUb (.evalBall bi mx newCurUb sub) = true := by
  dsimp only [checkTree] at ⊢; rw [hubeq]
  simp only [Bool.and_eq_true] at hg ⊢
  rcases hg with ⟨h1, ⟨⟨h2, h3⟩, h4⟩⟩
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hsub⟩

theorem checkRoot_of_tree (ri : Fin 116) (r0Score initCurUb : ℕ) (st0 : State32) (ubF0 : UbF7) (ubB0 : UbB16) (t : CertTree)
    (ht : checkTree r0Score st0 ubF0 ubB0 initCurUb t = true)
    (hr0 : Nat.beq (evalQ3Lookup (q3RepBits ri)) r0Score = true)
    (hcu : Nat.beq initCurUb (r0Score + 7 * Nat.min r0Score M3_shift + 16 * M4_shift) = true)
    (hst : initState ri = st0) (huf : initUbF r0Score = ubF0) (hub : initUbB = ubB0) :
    checkRoot ri r0Score initCurUb t = true := by
  dsimp only [checkRoot]; rw [hst, huf, hub]; simp [hr0, hcu, ht]

theorem checkRoot_of_branch1 (ri : Fin 116) (r0Score initCurUb e : ℕ) (st1 st0 : State32) (ubF0 : UbF7) (ubB0 : UbB16) (t1 t0 : CertTree)
    (h1 : checkTree r0Score st1 ubF0 ubB0 initCurUb t1 = true)
    (h0 : checkTree r0Score st0 ubF0 ubB0 initCurUb t0 = true)
    (hr0 : Nat.beq (evalQ3Lookup (q3RepBits ri)) r0Score = true)
    (hcu : Nat.beq initCurUb (r0Score + 7 * Nat.min r0Score M3_shift + 16 * M4_shift) = true)
    (he : (Nat.blt e 32 && isTriU (getE (initState ri) e)) = true)
    (hst1 : setE (initState ri) e .o = st1) (hst0 : setE (initState ri) e .z = st0)
    (huf : initUbF r0Score = ubF0) (hub : initUbB = ubB0) :
    checkRoot ri r0Score initCurUb (.branch e t1 t0) = true := by
  dsimp only [checkRoot, checkTree]; rw [huf, hub, hst1, hst0]; simp [hr0, hcu, he, h1, h0]

theorem checkRoot_of_branch2 (ri : Fin 116) (r0Score initCurUb e1 e2a e2b : ℕ)
    (st11 st10 st01 st00 : State32) (ubF0 : UbF7) (ubB0 : UbB16) (t11 t10 t01 t00 : CertTree)
    (h11 : checkTree r0Score st11 ubF0 ubB0 initCurUb t11 = true)
    (h10 : checkTree r0Score st10 ubF0 ubB0 initCurUb t10 = true)
    (h01 : checkTree r0Score st01 ubF0 ubB0 initCurUb t01 = true)
    (h00 : checkTree r0Score st00 ubF0 ubB0 initCurUb t00 = true)
    (hr0 : Nat.beq (evalQ3Lookup (q3RepBits ri)) r0Score = true)
    (hcu : Nat.beq initCurUb (r0Score + 7 * Nat.min r0Score M3_shift + 16 * M4_shift) = true)
    (he1 : (Nat.blt e1 32 && isTriU (getE (initState ri) e1)) = true)
    (he2a : (Nat.blt e2a 32 && isTriU (getE (setE (initState ri) e1 .o) e2a)) = true)
    (he2b : (Nat.blt e2b 32 && isTriU (getE (setE (initState ri) e1 .z) e2b)) = true)
    (hst11 : setE (setE (initState ri) e1 .o) e2a .o = st11)
    (hst10 : setE (setE (initState ri) e1 .o) e2a .z = st10)
    (hst01 : setE (setE (initState ri) e1 .z) e2b .o = st01)
    (hst00 : setE (setE (initState ri) e1 .z) e2b .z = st00)
    (huf : initUbF r0Score = ubF0) (hub : initUbB = ubB0) :
    checkRoot ri r0Score initCurUb (.branch e1 (.branch e2a t11 t10) (.branch e2b t01 t00)) = true := by
  dsimp only [checkRoot, checkTree]; rw [huf, hub, hst11, hst10, hst01, hst00]
  simp [hr0, hcu, he1, he2a, he2b, h11, h10, h01, h00]

end PPL033_C6Cert
