/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# PPL 033 — Coupled `Q_3 + B_2(Q_4)` Flag-Algebra Sum-of-Squares Certificate

Zero `sorry`, zero custom axioms, zero `native_decide`: every local bound and dot-product table
is verified in Lean 4 kernel arithmetic (`decide`).

- Asymptotic density bound: `(M3 + M4) / (24 * D_edge) = 1447121170 / 2400000000 ≈ 0.6029671542 < 0.6030 < 0.60318`.
-/

namespace PPL033_B2Q4Cert

def D_edge : ℤ := 100000000
def M3 : ℤ := 897230798
def M4 : ℤ := 549890372
private def M3_shift : ℕ := 897230798
private def M4_shift : ℕ := 12549890372
def K_Q3 : ℤ := 101444909
def K_B4 : ℤ := 50128370
def K_Q2 : ℤ := 173258785

private lemma list_all_bool {P : Bool → Bool} (h : [false, true].all P = true) (b : Bool) :
    P b = true := by
  cases b <;> simp_all

private lemma list_all_tri {P : Bool × Bool → Bool} (h : [(false, false), (false, true), (true, false)].all P = true)
    (a b : Bool) (hnot : !(a && b) = true) : P (a, b) = true := by
  cases a <;> cases b <;> simp_all

private def allFin8 (P : Fin 8 → Bool) : Bool :=
  [0, 1, 2, 3, 4, 5, 6, 7].all fun i => if h : i < 8 then P ⟨i, h⟩ else true

private lemma allFin8_spec {P : Fin 8 → Bool} (h : allFin8 P = true) (x : Fin 8) : P x = true := by
  fin_cases x <;> simp_all [allFin8]

private def lamShift (e0 e1 e2 f01 f10 f02 f20 f12 f21 : Bool) : ℕ :=
  if e0 then
  if e1 then
    if e2 then
      (if f01 then (if f10 then 100000000 else (if f02 then (if f20 then 100000000 else (if f12 then 100000000 else (if f21 then 100000000 else 43661149))) else (if f20 then (if f12 then 100000000 else (if f21 then 100000000 else 36173528)) else (if f12 then (if f21 then 100000000 else 36173528) else (if f21 then 50952411 else 74990145))))) else (if f10 then (if f02 then (if f20 then 100000000 else (if f12 then 100000000 else (if f21 then 100000000 else 36173528))) else (if f20 then (if f12 then 100000000 else (if f21 then 100000000 else 50952411)) else (if f12 then (if f21 then 100000000 else 43661149) else (if f21 then 36173528 else 74990145)))) else (if f02 then (if f20 then 100000000 else (if f12 then (if f21 then 100000000 else 50952411) else (if f21 then 36173528 else 74990145))) else (if f20 then (if f12 then (if f21 then 100000000 else 36173528) else (if f21 then 43661149 else 74990145)) else (if f12 then (if f21 then 100000000 else 74990145) else (if f21 then 74990145 else 254056116))))))
    else
      (if f01 then (if f10 then 100000000 else (if f02 then (if f20 then (if f12 then (if f21 then 147562156 else 170566318) else (if f21 then 170029561 else 147269747)) else (if f12 then (if f21 then 186839802 else 139345574) else (if f21 then 183444462 else 169614124))) else (if f20 then (if f12 then (if f21 then 122510372 else 148891376) else (if f21 then 148636847 else 146983252)) else (if f12 then (if f21 then 153682032 else 166331627) else (if f21 then 181430969 else 100000000))))) else (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 147562156 else 186839802) else (if f21 then 122510372 else 153682032)) else (if f12 then (if f21 then 170566318 else 139345574) else (if f21 then 148891376 else 166331627))) else (if f20 then (if f12 then (if f21 then 170029561 else 183444462) else (if f21 then 148636847 else 181430969)) else (if f12 then (if f21 then 147269747 else 169614124) else (if f21 then 146983252 else 100000000)))) else (if f02 then (if f20 then (if f12 then (if f21 then 100000000 else 157575686) else (if f21 then 94028590 else 92440424)) else (if f12 then (if f21 then 157575686 else 100000000) else (if f21 then 104410309 else 97511927))) else (if f20 then (if f12 then (if f21 then 94028590 else 104410309) else (if f21 then 100000000 else 112478708)) else (if f12 then (if f21 then 92440424 else 97511927) else (if f21 then 112478708 else 48946932))))))
  else
    if e2 then
      (if f01 then (if f10 then (if f02 then (if f20 then 100000000 else (if f12 then (if f21 then 147562156 else 170029561) else (if f21 then 170566318 else 147269747))) else (if f20 then (if f12 then (if f21 then 147562156 else 122510372) else (if f21 then 186839802 else 153682032)) else (if f12 then (if f21 then 100000000 else 94028590) else (if f21 then 157575686 else 92440424)))) else (if f02 then (if f20 then 100000000 else (if f12 then (if f21 then 186839802 else 183444462) else (if f21 then 139345574 else 169614124))) else (if f20 then (if f12 then (if f21 then 170566318 else 148891376) else (if f21 then 139345574 else 166331627)) else (if f12 then (if f21 then 157575686 else 104410309) else (if f21 then 100000000 else 97511927))))) else (if f10 then (if f02 then (if f20 then 100000000 else (if f12 then (if f21 then 122510372 else 148636847) else (if f21 then 148891376 else 146983252))) else (if f20 then (if f12 then (if f21 then 170029561 else 148636847) else (if f21 then 183444462 else 181430969)) else (if f12 then (if f21 then 94028590 else 100000000) else (if f21 then 104410309 else 112478708)))) else (if f02 then (if f20 then 100000000 else (if f12 then (if f21 then 153682032 else 181430969) else (if f21 then 166331627 else 100000000))) else (if f20 then (if f12 then (if f21 then 147269747 else 146983252) else (if f21 then 169614124 else 100000000)) else (if f12 then (if f21 then 92440424 else 112478708) else (if f21 then 97511927 else 48946932))))))
    else
      (if f01 then (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 73867090 else 100000000) else (if f21 then 100000000 else 104054374)) else (if f12 then (if f21 then 134299104 else 160396609) else (if f21 then 164534342 else 163561680))) else (if f20 then (if f12 then (if f21 then 61244063 else 66341567) else (if f21 then 72336442 else 101183043)) else (if f12 then (if f21 then 92368623 else 89818769) else (if f21 then 131182819 else 119138650)))) else (if f02 then (if f20 then (if f12 then (if f21 then 134299104 else 164534342) else (if f21 then 160396609 else 163561680)) else (if f12 then (if f21 then 71778672 else 100000000) else (if f21 then 100000000 else 96040832))) else (if f20 then (if f12 then (if f21 then 106982138 else 121461553) else (if f21 then 117595498 else 106876564)) else (if f12 then (if f21 then 145553794 else 153554125) else (if f21 then 174384887 else 143847067))))) else (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 61244063 else 72336442) else (if f21 then 66341567 else 101183043)) else (if f12 then (if f21 then 106982138 else 117595498) else (if f21 then 121461553 else 106876564))) else (if f20 then (if f12 then (if f21 then 119238386 else 100000000) else (if f21 then 100000000 else 128418564)) else (if f12 then (if f21 then 108306280 else 90789767) else (if f21 then 125901520 else 49769497)))) else (if f02 then (if f20 then (if f12 then (if f21 then 92368623 else 131182819) else (if f21 then 89818769 else 119138650)) else (if f12 then (if f21 then 145553794 else 174384887) else (if f21 then 153554125 else 143847067))) else (if f20 then (if f12 then (if f21 then 108306280 else 125901520) else (if f21 then 90789767 else 49769497)) else (if f12 then (if f21 then 96728365 else 113999312) else (if f21 then 113999312 else 100000000))))))
else
  if e1 then
    if e2 then
      (if f01 then (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 100000000 else 147562156) else (if f21 then 147562156 else 100000000)) else (if f12 then (if f21 then 100000000 else 170029561) else (if f21 then 122510372 else 94028590))) else (if f20 then (if f12 then (if f21 then 100000000 else 170566318) else (if f21 then 186839802 else 157575686)) else (if f12 then (if f21 then 100000000 else 147269747) else (if f21 then 153682032 else 92440424)))) else (if f02 then (if f20 then (if f12 then (if f21 then 100000000 else 122510372) else (if f21 then 170029561 else 94028590)) else (if f12 then (if f21 then 100000000 else 148636847) else (if f21 then 148636847 else 100000000))) else (if f20 then (if f12 then (if f21 then 100000000 else 148891376) else (if f21 then 183444462 else 104410309)) else (if f12 then (if f21 then 100000000 else 146983252) else (if f21 then 181430969 else 112478708))))) else (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 100000000 else 186839802) else (if f21 then 170566318 else 157575686)) else (if f12 then (if f21 then 100000000 else 183444462) else (if f21 then 148891376 else 104410309))) else (if f20 then (if f12 then (if f21 then 100000000 else 139345574) else (if f21 then 139345574 else 100000000)) else (if f12 then (if f21 then 100000000 else 169614124) else (if f21 then 166331627 else 97511927)))) else (if f02 then (if f20 then (if f12 then (if f21 then 100000000 else 153682032) else (if f21 then 147269747 else 92440424)) else (if f12 then (if f21 then 100000000 else 181430969) else (if f21 then 146983252 else 112478708))) else (if f20 then (if f12 then (if f21 then 100000000 else 166331627) else (if f21 then 169614124 else 97511927)) else (if f12 then 100000000 else (if f21 then 100000000 else 48946932))))))
    else
      (if f01 then (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 73867090 else 134299104) else (if f21 then 61244063 else 92368623)) else (if f12 then (if f21 then 100000000 else 160396609) else (if f21 then 66341567 else 89818769))) else (if f20 then (if f12 then (if f21 then 100000000 else 164534342) else (if f21 then 72336442 else 131182819)) else (if f12 then (if f21 then 104054374 else 163561680) else (if f21 then 101183043 else 119138650)))) else (if f02 then (if f20 then (if f12 then (if f21 then 61244063 else 106982138) else (if f21 then 119238386 else 108306280)) else (if f12 then (if f21 then 72336442 else 117595498) else (if f21 then 100000000 else 90789767))) else (if f20 then (if f12 then (if f21 then 66341567 else 121461553) else (if f21 then 100000000 else 125901520)) else (if f12 then (if f21 then 101183043 else 106876564) else (if f21 then 128418564 else 49769497))))) else (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 134299104 else 71778672) else (if f21 then 106982138 else 145553794)) else (if f12 then (if f21 then 164534342 else 100000000) else (if f21 then 121461553 else 153554125))) else (if f20 then (if f12 then (if f21 then 160396609 else 100000000) else (if f21 then 117595498 else 174384887)) else (if f12 then (if f21 then 163561680 else 96040832) else (if f21 then 106876564 else 143847067)))) else (if f02 then (if f20 then (if f12 then (if f21 then 92368623 else 145553794) else (if f21 then 108306280 else 96728365)) else (if f12 then (if f21 then 131182819 else 174384887) else (if f21 then 125901520 else 113999312))) else (if f20 then (if f12 then (if f21 then 89818769 else 153554125) else (if f21 then 90789767 else 113999312)) else (if f12 then (if f21 then 119138650 else 143847067) else (if f21 then 49769497 else 100000000))))))
  else
    if e2 then
      (if f01 then (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 73867090 else 61244063) else (if f21 then 134299104 else 92368623)) else (if f12 then (if f21 then 61244063 else 119238386) else (if f21 then 106982138 else 108306280))) else (if f20 then (if f12 then (if f21 then 134299104 else 106982138) else (if f21 then 71778672 else 145553794)) else (if f12 then (if f21 then 92368623 else 108306280) else (if f21 then 145553794 else 96728365)))) else (if f02 then (if f20 then (if f12 then (if f21 then 100000000 else 66341567) else (if f21 then 160396609 else 89818769)) else (if f12 then (if f21 then 72336442 else 100000000) else (if f21 then 117595498 else 90789767))) else (if f20 then (if f12 then (if f21 then 164534342 else 121461553) else (if f21 then 100000000 else 153554125)) else (if f12 then (if f21 then 131182819 else 125901520) else (if f21 then 174384887 else 113999312))))) else (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 100000000 else 72336442) else (if f21 then 164534342 else 131182819)) else (if f12 then (if f21 then 66341567 else 100000000) else (if f21 then 121461553 else 125901520))) else (if f20 then (if f12 then (if f21 then 160396609 else 117595498) else (if f21 then 100000000 else 174384887)) else (if f12 then (if f21 then 89818769 else 90789767) else (if f21 then 153554125 else 113999312)))) else (if f02 then (if f20 then (if f12 then (if f21 then 104054374 else 101183043) else (if f21 then 163561680 else 119138650)) else (if f12 then (if f21 then 101183043 else 128418564) else (if f21 then 106876564 else 49769497))) else (if f20 then (if f12 then (if f21 then 163561680 else 106876564) else (if f21 then 96040832 else 143847067)) else (if f12 then (if f21 then 119138650 else 49769497) else (if f21 then 143847067 else 100000000))))))
    else
      (if f01 then (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 179555012 else 81921976) else (if f21 then 81921976 else 86048721)) else (if f12 then (if f21 then 81921976 else 48390438) else (if f21 then 53140498 else 53212836))) else (if f20 then (if f12 then (if f21 then 81921976 else 53140498) else (if f21 then 68273978 else 70457857)) else (if f12 then (if f21 then 86048721 else 53212836) else (if f21 then 70457857 else 63363405)))) else (if f02 then (if f20 then (if f12 then (if f21 then 81921976 else 53140498) else (if f21 then 48390438 else 53212836)) else (if f12 then (if f21 then 68273978 else 100000000) else 100000000)) else (if f20 then (if f12 then (if f21 then 53140498 else 102313932) else (if f21 then 100000000 else 94300349)) else (if f12 then (if f21 then 70457857 else 94300349) else (if f21 then 102602778 else 96642568))))) else (if f10 then (if f02 then (if f20 then (if f12 then (if f21 then 81921976 else 68273978) else (if f21 then 53140498 else 70457857)) else (if f12 then (if f21 then 53140498 else 100000000) else (if f21 then 102313932 else 94300349))) else (if f20 then (if f12 then (if f21 then 48390438 else 100000000) else (if f21 then 100000000 else 102602778)) else (if f12 then (if f21 then 53212836 else 100000000) else (if f21 then 94300349 else 96642568)))) else (if f02 then (if f20 then (if f12 then (if f21 then 86048721 else 70457857) else (if f21 then 53212836 else 63363405)) else (if f12 then (if f21 then 70457857 else 102602778) else (if f21 then 94300349 else 96642568))) else (if f20 then (if f12 then (if f21 then 53212836 else 94300349) else (if f21 then 100000000 else 96642568)) else (if f12 then (if f21 then 63363405 else 96642568) else (if f21 then 96642568 else 98464420))))))

def lam23 (e0 e1 e2 f01 f10 f02 f20 f12 f21 : Bool) : ℤ :=
  (lamShift e0 e1 e2 f01 f10 f02 f20 f12 f21 : ℤ) - 100000000

private def checkLamSwap01 : Bool :=
  [false, true].all fun e0 => [false, true].all fun e1 => [false, true].all fun e2 =>
  [false, true].all fun f01 => [false, true].all fun f10 =>
  [false, true].all fun f02 => [false, true].all fun f20 =>
  [false, true].all fun f12 => [false, true].all fun f21 =>
    decide (lamShift e0 e1 e2 f01 f10 f02 f20 f12 f21 = lamShift e1 e0 e2 f10 f01 f12 f21 f02 f20)
private lemma checkLamSwap01_ok : checkLamSwap01 = true := by decide

lemma lam23_swap01 (e0 e1 e2 f01 f10 f02 f20 f12 f21 : Bool) :
    lam23 e0 e1 e2 f01 f10 f02 f20 f12 f21 = lam23 e1 e0 e2 f10 f01 f12 f21 f02 f20 := by
  have h := list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool
    (list_all_bool (list_all_bool (list_all_bool (list_all_bool checkLamSwap01_ok e0) e1) e2)
      f01) f10) f02) f20) f12) f21
  simp only [decide_eq_true_eq] at h
  simp only [lam23, h]

private def checkLamSwap12 : Bool :=
  [false, true].all fun e0 => [false, true].all fun e1 => [false, true].all fun e2 =>
  [false, true].all fun f01 => [false, true].all fun f10 =>
  [false, true].all fun f02 => [false, true].all fun f20 =>
  [false, true].all fun f12 => [false, true].all fun f21 =>
    decide (lamShift e0 e1 e2 f01 f10 f02 f20 f12 f21 = lamShift e0 e2 e1 f02 f20 f01 f10 f21 f12)
private lemma checkLamSwap12_ok : checkLamSwap12 = true := by decide

lemma lam23_swap12 (e0 e1 e2 f01 f10 f02 f20 f12 f21 : Bool) :
    lam23 e0 e1 e2 f01 f10 f02 f20 f12 f21 = lam23 e0 e2 e1 f02 f20 f01 f10 f21 f12 := by
  have h := list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool
    (list_all_bool (list_all_bool (list_all_bool (list_all_bool checkLamSwap12_ok e0) e1) e2)
      f01) f10) f02) f20) f12) f21
  simp only [decide_eq_true_eq] at h
  simp only [lam23, h]

def mkFlag (a b o : Bool) : Fin 8 :=
  ⟨(if a then 4 else 0) + (if b then 2 else 0) + (if o then 1 else 0), by
    cases a <;> cases b <;> cases o <;> simp⟩

def flipF (f : Fin 8) : Fin 8 :=
  ⟨(f.val / 2 % 2) * 4 + (f.val / 4) * 2 + (f.val % 2), by omega⟩

lemma flipF_mkFlag (a b o : Bool) : flipF (mkFlag a b o) = mkFlag b a o := by
  cases a <;> cases b <;> cases o <;> decide

private def sort3 (x y z : Fin 8) : Fin 8 × Fin 8 × Fin 8 :=
  let (x1, y1) := if x.val ≤ y.val then (x, y) else (y, x)
  let (y2, z1) := if y1.val ≤ z.val then (y1, z) else (z, y1)
  let (x2, y3) := if x1.val ≤ y2.val then (x1, y2) else (y2, x1)
  (x2, y3, z1)

private def phiSorted (e : Bool) (a b c : Fin 8) : ℕ :=
  match e, a.val, b.val, c.val with
  | false, 0, 0, 2 => 180842080
  | false, 0, 0, 4 => 219157920
  | false, 0, 0, 3 => 230947781
  | false, 0, 0, 5 => 169052219
  | false, 0, 1, 2 => 184560548
  | false, 0, 1, 4 => 215439452
  | false, 0, 1, 3 => 228693310
  | false, 0, 1, 5 => 171306690
  | false, 0, 2, 2 => 159043452
  | false, 0, 4, 4 => 240956548
  | false, 0, 2, 3 => 222984369
  | false, 0, 4, 5 => 177015631
  | false, 0, 2, 5 => 160773426
  | false, 0, 3, 4 => 239226574
  | false, 0, 2, 6 => 222791374
  | false, 0, 4, 6 => 177208626
  | false, 0, 2, 7 => 211020547
  | false, 0, 4, 7 => 188979453
  | false, 0, 3, 6 => 222529656
  | false, 0, 5, 6 => 177470344
  | false, 0, 3, 7 => 236769933
  | false, 0, 5, 7 => 163230067
  | false, 1, 1, 2 => 174990034
  | false, 1, 1, 4 => 225009966
  | false, 1, 1, 3 => 230631990
  | false, 1, 1, 5 => 169368010
  | false, 1, 2, 2 => 162229257
  | false, 1, 4, 4 => 237770743
  | false, 1, 2, 3 => 214002249
  | false, 1, 4, 5 => 185997751
  | false, 1, 2, 5 => 162971486
  | false, 1, 3, 4 => 237028514
  | false, 1, 2, 6 => 200783635
  | false, 1, 4, 6 => 199216365
  | false, 1, 2, 7 => 206748725
  | false, 1, 4, 7 => 193251275
  | false, 1, 3, 6 => 239341668
  | false, 1, 5, 6 => 160658332
  | false, 1, 3, 7 => 238420645
  | false, 1, 5, 7 => 161579355
  | false, 2, 2, 2 => 133690878
  | false, 4, 4, 4 => 266309122
  | false, 2, 2, 3 => 212887478
  | false, 4, 4, 5 => 187112522
  | false, 2, 2, 4 => 187854546
  | false, 2, 4, 4 => 212145454
  | false, 2, 2, 5 => 149500527
  | false, 3, 4, 4 => 250499473
  | false, 2, 2, 6 => 240073638
  | false, 4, 4, 6 => 159926362
  | false, 2, 3, 4 => 234359618
  | false, 2, 4, 5 => 165640382
  | false, 2, 3, 5 => 200771828
  | false, 3, 4, 5 => 199228172
  | false, 2, 3, 6 => 262765998
  | false, 4, 5, 6 => 137234002
  | false, 2, 3, 7 => 247975630
  | false, 4, 5, 7 => 152024370
  | false, 2, 5, 6 => 210612902
  | false, 3, 4, 6 => 189387098
  | false, 2, 5, 7 => 179908905
  | false, 3, 4, 7 => 220091095
  | false, 2, 6, 6 => 257456950
  | false, 4, 6, 6 => 142543050
  | false, 2, 6, 7 => 238507915
  | false, 4, 6, 7 => 161492085
  | false, 2, 7, 7 => 209370869
  | false, 4, 7, 7 => 190629131
  | false, 3, 3, 3 => 102737742
  | false, 5, 5, 5 => 297262258
  | false, 3, 3, 5 => 167936965
  | false, 3, 5, 5 => 232063035
  | false, 3, 6, 6 => 220243636
  | false, 5, 6, 6 => 179756364
  | false, 3, 6, 7 => 231151664
  | false, 5, 6, 7 => 168848336
  | false, 3, 7, 7 => 230617365
  | false, 5, 7, 7 => 169382635
  | true, 0, 0, 2 => 142453592
  | true, 0, 0, 4 => 257546408
  | true, 0, 0, 3 => 192817629
  | true, 0, 0, 5 => 207182371
  | true, 0, 1, 2 => 156414931
  | true, 0, 1, 4 => 243585069
  | true, 0, 1, 3 => 236640472
  | true, 0, 1, 5 => 163359528
  | true, 0, 2, 3 => 142645483
  | true, 0, 4, 5 => 257354517
  | true, 0, 2, 5 => 157777427
  | true, 0, 3, 4 => 242222573
  | true, 0, 2, 6 => 141921424
  | true, 0, 4, 6 => 258078576
  | true, 0, 3, 3 => 204901837
  | true, 0, 5, 5 => 195098163
  | true, 0, 3, 6 => 193127963
  | true, 0, 5, 6 => 206872037
  | true, 1, 1, 2 => 231083652
  | true, 1, 1, 4 => 168916348
  | true, 1, 1, 3 => 278821561
  | true, 1, 1, 5 => 121178439
  | true, 1, 2, 2 => 238867066
  | true, 1, 4, 4 => 161132934
  | true, 1, 2, 5 => 159626983
  | true, 1, 3, 4 => 240373017
  | true, 1, 2, 6 => 167210189
  | true, 1, 4, 6 => 232789811
  | true, 1, 3, 3 => 284949235
  | true, 1, 5, 5 => 115050765
  | true, 1, 3, 6 => 234762293
  | true, 1, 5, 6 => 165237707
  | true, 2, 2, 2 => 375592283
  | true, 4, 4, 4 => 24407717
  | true, 2, 2, 4 => 259527109
  | true, 2, 4, 4 => 140472891
  | true, 2, 2, 5 => 219107465
  | true, 3, 4, 4 => 180892535
  | true, 2, 3, 3 => 149451884
  | true, 4, 5, 5 => 250548116
  | true, 2, 3, 4 => 191922347
  | true, 2, 4, 5 => 208077653
  | true, 2, 3, 5 => 150621259
  | true, 3, 4, 5 => 249378741
  | true, 2, 3, 6 => 139257386
  | true, 4, 5, 6 => 260742614
  | true, 2, 5, 5 => 174475042
  | true, 3, 3, 4 => 225524958
  | true, 2, 5, 6 => 161394050
  | true, 3, 4, 6 => 238605950
  | true, 2, 6, 6 => 148846797
  | true, 4, 6, 6 => 251153203
  | true, 3, 3, 3 => 223653187
  | true, 5, 5, 5 => 176346813
  | true, 3, 3, 5 => 194539526
  | true, 3, 5, 5 => 205460474
  | true, 3, 3, 6 => 198695333
  | true, 5, 5, 6 => 201304667
  | true, 3, 6, 6 => 200050325
  | true, 5, 6, 6 => 199949675
  | _, _, _, _ => 200000000

private def phiShift (e : Bool) (f1 f2 f3 : Fin 8) : ℕ :=
  let s := sort3 f1 f2 f3; phiSorted e s.1 s.2.1 s.2.2

def phiFlip (e : Bool) (f1 f2 f3 : Fin 8) : ℤ :=
  (phiShift e f1 f2 f3 : ℤ) - 200000000

private def checkPhiAntisymm : Bool :=
  [false, true].all fun e => allFin8 fun f1 => allFin8 fun f2 => allFin8 fun f3 =>
    decide (phiShift e f1 f2 f3 + phiShift e (flipF f1) (flipF f2) (flipF f3) = 400000000)
private lemma checkPhiAntisymm_ok : checkPhiAntisymm = true := by decide

lemma phiFlip_antisymm (e : Bool) (f1 f2 f3 : Fin 8) :
    phiFlip e f1 f2 f3 + phiFlip e (flipF f1) (flipF f2) (flipF f3) = 0 := by
  have h := allFin8_spec (allFin8_spec (allFin8_spec (list_all_bool checkPhiAntisymm_ok e) f1) f2) f3
  simp only [decide_eq_true_eq] at h
  unfold phiFlip; omega

private def checkPhiSwap12 : Bool :=
  [false, true].all fun e => allFin8 fun f1 => allFin8 fun f2 => allFin8 fun f3 =>
    decide (phiShift e f1 f2 f3 = phiShift e f2 f1 f3)
private lemma checkPhiSwap12_ok : checkPhiSwap12 = true := by decide

lemma phiFlip_swap12 (e : Bool) (f1 f2 f3 : Fin 8) :
    phiFlip e f1 f2 f3 = phiFlip e f2 f1 f3 := by
  have h := allFin8_spec (allFin8_spec (allFin8_spec (list_all_bool checkPhiSwap12_ok e) f1) f2) f3
  simp only [decide_eq_true_eq] at h
  simp only [phiFlip, h]

private def checkPhiSwap23 : Bool :=
  [false, true].all fun e => allFin8 fun f1 => allFin8 fun f2 => allFin8 fun f3 =>
    decide (phiShift e f1 f2 f3 = phiShift e f1 f3 f2)
private lemma checkPhiSwap23_ok : checkPhiSwap23 = true := by decide

lemma phiFlip_swap23 (e : Bool) (f1 f2 f3 : Fin 8) :
    phiFlip e f1 f2 f3 = phiFlip e f1 f3 f2 := by
  have h := allFin8_spec (allFin8_spec (allFin8_spec (list_all_bool checkPhiSwap23_ok e) f1) f2) f3
  simp only [decide_eq_true_eq] at h
  simp only [phiFlip, h]

def q3W0 (s : Fin 4) (t : Fin 8) : ℤ :=
  match s.val, t.val with
  | 0, k => match k with | 0 => -5201 | 1 => 1546 | 2 => -4878 | 3 => -2296 | 4 => 3122 | 5 => 420 | 6 => 3471 | 7 => 0 | _ => 0
  | 1, k => match k with | 0 => -3930 | 1 => 1167 | 2 => -3292 | 3 => -843 | 4 => 1965 | 5 => -575 | 6 => 2623 | 7 => 0 | _ => 0
  | 2, k => match k with | 0 => -412 | 1 => 105 | 2 => -3700 | 3 => 2169 | 4 => 3561 | 5 => -2317 | 6 => 275 | 7 => 0 | _ => 0
  | 3, k => match k with | 0 => 1410 | 1 => -403 | 2 => 2735 | 3 => 3389 | 4 => -2259 | 5 => -2881 | 6 => -941 | 7 => 0 | _ => 0
  | _, _ => 0

def q3U1 (s : Fin 5) (t : Fin 8) : ℤ :=
  match s.val, t.val with
  | 0, k => match k with | 0 => 3858 | 1 => 2648 | 2 => 206 | 3 => -2219 | 4 => -2889 | 5 => 1134 | 6 => -4808 | 7 => -565 | _ => 0
  | 1, k => match k with | 0 => -1822 | 1 => -3219 | 2 => -5296 | 3 => -1122 | 4 => 252 | 5 => -1803 | 6 => -283 | 7 => 3191 | _ => 0
  | 2, k => match k with | 0 => -1494 | 1 => 757 | 2 => 2193 | 3 => 4719 | 4 => 4562 | 5 => -1186 | 6 => 4175 | 7 => -2429 | _ => 0
  | 3, k => match k with | 0 => -1956 | 1 => -237 | 2 => -802 | 3 => -4041 | 4 => 5706 | 5 => 6521 | 6 => 3871 | 7 => -1355 | _ => 0
  | 4, k => match k with | 0 => -3404 | 1 => -1950 | 2 => -2691 | 3 => -719 | 4 => 6298 | 5 => 2351 | 6 => 4745 | 7 => -76 | _ => 0
  | _, _ => 0

lemma q3W0_sq_le (t : Fin 8) :
    q3W0 0 t ^ 2 + q3W0 1 t ^ 2 + q3W0 2 t ^ 2 + q3W0 3 t ^ 2 ≤ K_Q3 := by
  fin_cases t <;> decide

lemma q3U1_sq_le (t : Fin 8) :
    q3U1 0 t ^ 2 + q3U1 1 t ^ 2 + q3U1 2 t ^ 2 + q3U1 3 t ^ 2 + q3U1 4 t ^ 2 ≤ K_Q3 := by
  fin_cases t <;> decide

private def q3W0DotShift (t1 t2 : Fin 8) : ℕ :=
  (200000000 + (q3W0 0 t1 * q3W0 0 t2 + q3W0 1 t1 * q3W0 1 t2 + q3W0 2 t1 * q3W0 2 t2 + q3W0 3 t1 * q3W0 3 t2)).toNat

private def q3U1DotShift (t1 t2 : Fin 8) : ℕ :=
  (100000000 + (q3U1 0 t1 * q3U1 0 t2 + q3U1 1 t1 * q3U1 1 t2 + q3U1 2 t1 * q3U1 2 t2 + q3U1 3 t1 * q3U1 3 t2 + q3U1 4 t1 * q3U1 4 t2)).toNat

private lemma q3W0DotShift_coe (t1 t2 : Fin 8) :
    (q3W0DotShift t1 t2 : ℤ) = 200000000 + (q3W0 0 t1 * q3W0 0 t2 + q3W0 1 t1 * q3W0 1 t2 + q3W0 2 t1 * q3W0 2 t2 + q3W0 3 t1 * q3W0 3 t2) := by
  fin_cases t1 <;> fin_cases t2 <;> decide

private lemma q3U1DotShift_coe (t1 t2 : Fin 8) :
    (q3U1DotShift t1 t2 : ℤ) = 100000000 + (q3U1 0 t1 * q3U1 0 t2 + q3U1 1 t1 * q3U1 1 t2 + q3U1 2 t1 * q3U1 2 t2 + q3U1 3 t1 * q3U1 3 t2 + q3U1 4 t1 * q3U1 4 t2) := by
  fin_cases t1 <;> fin_cases t2 <;> decide

def q3EdgeTerm (e a1 b1 o1 a2 b2 o2 : Bool) : ℤ :=
  let t1 := mkFlag a1 b1 o1
  let t2 := mkFlag a2 b2 o2
  if e then D_edge + (q3W0 0 t1 * q3W0 0 t2 + q3W0 1 t1 * q3W0 1 t2 + q3W0 2 t1 * q3W0 2 t2 + q3W0 3 t1 * q3W0 3 t2)
  else q3U1 0 t1 * q3U1 0 t2 + q3U1 1 t1 * q3U1 1 t2 + q3U1 2 t1 * q3U1 2 t2 + q3U1 3 t1 * q3U1 3 t2 + q3U1 4 t1 * q3U1 4 t2

private def q3EdgeShift (e a1 b1 o1 a2 b2 o2 : Bool) : ℕ :=
  if e then q3W0DotShift (mkFlag a1 b1 o1) (mkFlag a2 b2 o2)
  else q3U1DotShift (mkFlag a1 b1 o1) (mkFlag a2 b2 o2)

private lemma q3EdgeTerm_eq_shift (e a1 b1 o1 a2 b2 o2 : Bool) :
    q3EdgeTerm e a1 b1 o1 a2 b2 o2 = (q3EdgeShift e a1 b1 o1 a2 b2 o2 : ℤ) - 100000000 := by
  unfold q3EdgeTerm q3EdgeShift
  by_cases he : e
  · simp only [he, ↓reduceIte, q3W0DotShift_coe, D_edge]; ring
  · simp only [he, ↓reduceIte, Bool.false_eq_true, q3U1DotShift_coe]; ring

def q3IsC4FreeBool (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool) : Bool :=
  !(y00 && y01 && z00 && z01) && !(y10 && y11 && z10 && z11) &&
  !(x00 && x01 && z00 && z10) && !(x10 && x11 && z01 && z11) &&
  !(x00 && x10 && y00 && y10) && !(x01 && x11 && y01 && y11)

def q3LocalBool (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool) : ℤ :=
  (q3EdgeTerm x00 y00 y10 x10 z00 z10 x01 + q3EdgeTerm y00 x00 x10 y10 z00 z01 y01 + q3EdgeTerm z00 x00 x01 z10 y00 y01 z01 - 3 * lam23 x00 y00 z00 y10 x10 z10 x01 z01 y01) +
  (q3EdgeTerm x00 y10 y00 x10 z10 z00 x01 + q3EdgeTerm y10 x00 x10 y00 z10 z11 y11 + q3EdgeTerm z10 x00 x01 z00 y10 y11 z11 - 3 * lam23 x00 y10 z10 y00 x10 z00 x01 z11 y11) +
  (q3EdgeTerm x01 y01 y11 x11 z00 z10 x00 + q3EdgeTerm y01 x01 x11 y11 z00 z01 y00 + q3EdgeTerm z00 x01 x00 z10 y01 y00 z01 - 3 * lam23 x01 y01 z00 y11 x11 z10 x00 z01 y00) +
  (q3EdgeTerm x01 y11 y01 x11 z10 z00 x00 + q3EdgeTerm y11 x01 x11 y01 z10 z11 y10 + q3EdgeTerm z10 x01 x00 z00 y11 y10 z11 - 3 * lam23 x01 y11 z10 y01 x11 z00 x00 z11 y10) +
  (q3EdgeTerm x10 y00 y10 x00 z01 z11 x11 + q3EdgeTerm y00 x10 x00 y10 z01 z00 y01 + q3EdgeTerm z01 x10 x11 z11 y00 y01 z00 - 3 * lam23 x10 y00 z01 y10 x00 z11 x11 z00 y01) +
  (q3EdgeTerm x10 y10 y00 x00 z11 z01 x11 + q3EdgeTerm y10 x10 x00 y00 z11 z10 y11 + q3EdgeTerm z11 x10 x11 z01 y10 y11 z10 - 3 * lam23 x10 y10 z11 y00 x00 z01 x11 z10 y11) +
  (q3EdgeTerm x11 y01 y11 x01 z01 z11 x10 + q3EdgeTerm y01 x11 x01 y11 z01 z00 y00 + q3EdgeTerm z01 x11 x10 z11 y01 y00 z00 - 3 * lam23 x11 y01 z01 y11 x01 z11 x10 z00 y00) +
  (q3EdgeTerm x11 y11 y01 x01 z11 z01 x10 + q3EdgeTerm y11 x11 x01 y01 z11 z10 y10 + q3EdgeTerm z11 x11 x10 z01 y11 y10 z10 - 3 * lam23 x11 y11 z11 y01 x01 z01 x10 z10 y10)

private def q3PosShift (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool) : ℕ :=
  q3EdgeShift x00 y00 y10 x10 z00 z10 x01 + q3EdgeShift y00 x00 x10 y10 z00 z01 y01 + q3EdgeShift z00 x00 x01 z10 y00 y01 z01 +
  q3EdgeShift x00 y10 y00 x10 z10 z00 x01 + q3EdgeShift y10 x00 x10 y00 z10 z11 y11 + q3EdgeShift z10 x00 x01 z00 y10 y11 z11 +
  q3EdgeShift x01 y01 y11 x11 z00 z10 x00 + q3EdgeShift y01 x01 x11 y11 z00 z01 y00 + q3EdgeShift z00 x01 x00 z10 y01 y00 z01 +
  q3EdgeShift x01 y11 y01 x11 z10 z00 x00 + q3EdgeShift y11 x01 x11 y01 z10 z11 y10 + q3EdgeShift z10 x01 x00 z00 y11 y10 z11 +
  q3EdgeShift x10 y00 y10 x00 z01 z11 x11 + q3EdgeShift y00 x10 x00 y10 z01 z00 y01 + q3EdgeShift z01 x10 x11 z11 y00 y01 z00 +
  q3EdgeShift x10 y10 y00 x00 z11 z01 x11 + q3EdgeShift y10 x10 x00 y00 z11 z10 y11 + q3EdgeShift z11 x10 x11 z01 y10 y11 z10 +
  q3EdgeShift x11 y01 y11 x01 z01 z11 x10 + q3EdgeShift y01 x11 x01 y11 z01 z00 y00 + q3EdgeShift z01 x11 x10 z11 y01 y00 z00 +
  q3EdgeShift x11 y11 y01 x01 z11 z01 x10 + q3EdgeShift y11 x11 x01 y01 z11 z10 y10 + q3EdgeShift z11 x11 x10 z01 y11 y10 z10

private def q3LamSum (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool) : ℕ :=
  lamShift x00 y00 z00 y10 x10 z10 x01 z01 y01 + lamShift x00 y10 z10 y00 x10 z00 x01 z11 y11 +
  lamShift x01 y01 z00 y11 x11 z10 x00 z01 y00 + lamShift x01 y11 z10 y01 x11 z00 x00 z11 y10 +
  lamShift x10 y00 z01 y10 x00 z11 x11 z00 y01 + lamShift x10 y10 z11 y00 x00 z01 x11 z10 y11 +
  lamShift x11 y01 z01 y11 x01 z11 x10 z00 y00 + lamShift x11 y11 z11 y01 x01 z01 x10 z10 y10

private lemma q3LocalBool_eq_shift (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool) :
    q3LocalBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 =
      (q3PosShift x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : ℤ) -
      3 * (q3LamSum x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : ℤ) := by
  unfold q3LocalBool q3PosShift q3LamSum
  simp_rw [q3EdgeTerm_eq_shift]
  unfold lam23
  push_cast
  ring

private def checkQ3Slice (x00 x01 x10 x11 : Bool) : Bool :=
  [false, true].all fun y00 => [false, true].all fun y01 =>
  [false, true].all fun y10 => [false, true].all fun y11 =>
  [false, true].all fun z00 => [false, true].all fun z01 =>
  [false, true].all fun z10 => [false, true].all fun z11 =>
    !q3IsC4FreeBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 ||
    decide (q3PosShift x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 ≤ M3_shift + 3 * q3LamSum x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11)

private lemma checkQ3_0000 : checkQ3Slice false false false false = true := by decide
private lemma checkQ3_0001 : checkQ3Slice false false false true = true := by decide
private lemma checkQ3_0010 : checkQ3Slice false false true false = true := by decide
private lemma checkQ3_0011 : checkQ3Slice false false true true = true := by decide
private lemma checkQ3_0100 : checkQ3Slice false true false false = true := by decide
private lemma checkQ3_0101 : checkQ3Slice false true false true = true := by decide
private lemma checkQ3_0110 : checkQ3Slice false true true false = true := by decide
private lemma checkQ3_0111 : checkQ3Slice false true true true = true := by decide
private lemma checkQ3_1000 : checkQ3Slice true false false false = true := by decide
private lemma checkQ3_1001 : checkQ3Slice true false false true = true := by decide
private lemma checkQ3_1010 : checkQ3Slice true false true false = true := by decide
private lemma checkQ3_1011 : checkQ3Slice true false true true = true := by decide
private lemma checkQ3_1100 : checkQ3Slice true true false false = true := by decide
private lemma checkQ3_1101 : checkQ3Slice true true false true = true := by decide
private lemma checkQ3_1110 : checkQ3Slice true true true false = true := by decide
private lemma checkQ3_1111 : checkQ3Slice true true true true = true := by decide

lemma q3LocalBool_le_M3 (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool)
    (hc4 : q3IsC4FreeBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 = true) :
    q3LocalBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 ≤ M3 := by
  have hslice : checkQ3Slice x00 x01 x10 x11 = true := by
    cases x00 <;> cases x01 <;> cases x10 <;> cases x11
    · exact checkQ3_0000
    · exact checkQ3_0001
    · exact checkQ3_0010
    · exact checkQ3_0011
    · exact checkQ3_0100
    · exact checkQ3_0101
    · exact checkQ3_0110
    · exact checkQ3_0111
    · exact checkQ3_1000
    · exact checkQ3_1001
    · exact checkQ3_1010
    · exact checkQ3_1011
    · exact checkQ3_1100
    · exact checkQ3_1101
    · exact checkQ3_1110
    · exact checkQ3_1111
  have h := list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool
    (list_all_bool (list_all_bool (list_all_bool hslice y00) y01) y10) y11) z00) z01) z10) z11
  simp only [hc4, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
  rw [q3LocalBool_eq_shift]
  have hZ := Int.ofNat_le.mpr h
  push_cast at hZ
  change _ ≤ M3; dsimp only [M3_shift, M3] at hZ ⊢; omega

def isCanonRoot (a b ab ba : Bool) : Bool :=
  !(a && b && ab && ba) && (if a != b then !a else if ab != ba then !ab else true)

def rcIdx (a b ab ba : Bool) : Fin 9 :=
  let (a', b', ab', ba') := if (if a != b then a else if ab != ba then ab else false) then (b, a, ba, ab) else (a, b, ab, ba)
  match a', b', ab', ba' with
  | false, false, false, false => ⟨0, by decide⟩
  | false, false, false, true  => ⟨1, by decide⟩
  | false, false, true,  true  => ⟨2, by decide⟩
  | false, true,  false, false => ⟨3, by decide⟩
  | false, true,  false, true  => ⟨4, by decide⟩
  | false, true,  true,  false => ⟨5, by decide⟩
  | false, true,  true,  true  => ⟨6, by decide⟩
  | true,  true,  false, false => ⟨7, by decide⟩
  | true,  true,  false, true  => ⟨8, by decide⟩
  | _, _, _, _ => ⟨0, by decide⟩

lemma rcIdx_swap (a b ab ba : Bool) : rcIdx a b ab ba = rcIdx b a ba ab := by
  cases a <;> cases b <;> cases ab <;> cases ba <;> rfl

def b4V (s : Fin 5) (c : Fin 9) : ℤ :=
  match s.val, c.val with
  | 0, k => match k with | 0 => -4037 | 1 => -6318 | 2 => -4737 | 3 => 217 | 4 => -941 | 5 => 2042 | 6 => -1106 | 7 => 5061 | 8 => 2902 | _ => 0
  | 1, k => match k with | 0 => -40 | 1 => -141 | 2 => -359 | 3 => -493 | 4 => 381 | 5 => 55 | 6 => -11 | 7 => -732 | 8 => 183 | _ => 0
  | 2, k => match k with | 0 => -1190 | 1 => -1233 | 2 => -1635 | 3 => -774 | 4 => 475 | 5 => 578 | 6 => -185 | 7 => -71 | 8 => 819 | _ => 0
  | 3, k => match k with | 0 => -1876 | 1 => -1930 | 2 => -2080 | 3 => -320 | 4 => -2 | 5 => 873 | 6 => -302 | 7 => 1401 | 8 => 1052 | _ => 0
  | 4, k => match k with | 0 => 1273 | 1 => 2224 | 2 => 2165 | 3 => 821 | 4 => -254 | 5 => -709 | 6 => 281 | 7 => -495 | 8 => -1164 | _ => 0
  | _, _ => 0

lemma b4V_sq_le (c : Fin 9) :
    b4V 0 c ^ 2 + b4V 1 c ^ 2 + b4V 2 c ^ 2 + b4V 3 c ^ 2 + b4V 4 c ^ 2 ≤ K_B4 := by
  fin_cases c <;> decide

def b4Pair (a b ab ba c d cd dc : Bool) : ℤ :=
  let c1 := rcIdx a b ab ba
  let c2 := rcIdx c d cd dc
  b4V 0 c1 * b4V 0 c2 + b4V 1 c1 * b4V 1 c2 + b4V 2 c1 * b4V 2 c2 + b4V 3 c1 * b4V 3 c2 + b4V 4 c1 * b4V 4 c2

private def b4DotShift (c1 c2 : Fin 9) : ℕ :=
  match c1.val, c2.val with
  | 0, r => match r with | 0 => 122854974 | 1 => 133430508 | 2 => 127741404 | 3 => 101710204 | 4 => 102898737 | 5 => 88526121 | 6 => 105609777 | 7 => 76424102 | 8 => 83847372 | _ => 100000000
  | 1, r => match r with | 0 => 133430508 | 1 => 150128370 | 2 => 140824300 | 3 => 102096353 | 4 => 104744806 | 5 => 83116509 | 6 => 108425168 | 7 => 64410547 | 8 => 76010438 | _ => 100000000
  | 2, r => match r with | 0 => 127741404 | 1 => 140824300 | 2 => 134254900 | 3 => 102857613 | 4 => 102998363 | 5 => 86011446 | 6 => 106782071 | 7 => 72419161 | 8 => 80140244 | _ => 100000000
  | 3, r => match r with | 0 => 101710204 | 1 => 102096353 | 2 => 102857613 | 3 => 101665655 | 4 => 99032426 | 5 => 99107178 | 6 => 100235952 | 7 => 100659352 | 8 => 98613325 | _ => 100000000
  | 4, r => match r with | 0 => 102898737 | 1 => 104744806 | 2 => 102998363 | 3 => 99032426 | 4 => 101320787 | 5 => 98552323 | 6 => 100877910 | 7 => 95047910 | 8 => 98021518 | _ => 100000000
  | 5, r => match r with | 0 => 88526121 | 1 => 83116509 | 2 => 86011446 | 3 => 99107178 | 4 => 98552323 | 5 => 105771683 | 6 => 97171138 | 7 => 111827292 | 8 => 108153003 | _ => 100000000
  | 6, r => match r with | 0 => 105609777 | 1 => 108425168 | 2 => 106782071 | 3 => 100235952 | 4 => 100877910 | 5 => 97171138 | 6 => 101427747 | 7 => 93861524 | 8 => 95992072 | _ => 100000000
  | 7, r => match r with | 0 => 76424102 | 1 => 64410547 | 2 => 72419161 | 3 => 100659352 | 4 => 95047910 | 5 => 111827292 | 6 => 93861524 | 7 => 128362412 | 8 => 116544949 | _ => 100000000
  | 8, r => match r with | 0 => 83847372 | 1 => 76010438 | 2 => 80140244 | 3 => 98613325 | 4 => 98021518 | 5 => 108153003 | 6 => 95992072 | 7 => 116544949 | 8 => 111587454 | _ => 100000000
  | _, _ => 100000000

private lemma b4DotShift_coe (c1 c2 : Fin 9) :
    (b4DotShift c1 c2 : ℤ) = 100000000 +
      (b4V 0 c1 * b4V 0 c2 + b4V 1 c1 * b4V 1 c2 + b4V 2 c1 * b4V 2 c2 + b4V 3 c1 * b4V 3 c2 + b4V 4 c1 * b4V 4 c2) := by
  fin_cases c1 <;> fin_cases c2 <;> decide

private lemma b4Pair_eq_shift (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = (b4DotShift (rcIdx a b ab ba) (rcIdx c d cd dc) : ℤ) - 100000000 := by
  unfold b4Pair; rw [b4DotShift_coe]; ring

def q2W (r : Fin 9) (s : Fin 8) (b4 b3 b2 b1 b0 : Bool) : ℤ :=
  match r.val, s.val with
  | 0, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 670 else 342) else (if b0 then -926 else -652))
    else
      (if b1 then (if b0 then 190 else 356) else (if b0 then -38 else 351))
  else
    if b2 then
      (if b1 then (if b0 then -293 else 195) else (if b0 then -1384 else -645))
    else
      (if b1 then (if b0 then 21 else -446) else (if b0 then 241 else -59))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 177 else -2915) else (if b0 then -2534 else -1104))
    else
      (if b1 then (if b0 then -1079 else 738) else (if b0 then 439 else 198))
  else
    if b2 then
      (if b1 then (if b0 then 1427 else -1147) else (if b0 then 1528 else 1769))
    else
      (if b1 then (if b0 then 102 else 569) else (if b0 then 1224 else 337))
  | 0, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 665 else 862) else (if b0 then -148 else -1429))
    else
      (if b1 then (if b0 then 1767 else 279) else (if b0 then 2466 else -416))
  else
    if b2 then
      (if b1 then (if b0 then -940 else 175) else (if b0 then -2381 else 431))
    else
      (if b1 then (if b0 then 97 else -1434) else (if b0 then 1089 else 405))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1236 else 1917) else (if b0 then 463 else 1381))
    else
      (if b1 then (if b0 then -275 else 88) else (if b0 then 655 else -553))
  else
    if b2 then
      (if b1 then (if b0 then -1160 else 19) else (if b0 then -1899 else 476))
    else
      (if b1 then (if b0 then 157 else -86) else (if b0 then -208 else 228))
  | 0, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 628 else -786) else (if b0 then 188 else -2791))
    else
      (if b1 then (if b0 then -332 else -1731) else (if b0 then 357 else -286))
  else
    if b2 then
      (if b1 then (if b0 then 297 else 1062) else (if b0 then -345 else -178))
    else
      (if b1 then (if b0 then 162 else -71) else (if b0 then 1081 else -1825))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -345 else -2117) else (if b0 then -2483 else -189))
    else
      (if b1 then (if b0 then 1169 else 1247) else (if b0 then -386 else 1519))
  else
    if b2 then
      (if b1 then (if b0 then -795 else -883) else (if b0 then 992 else 1572))
    else
      (if b1 then (if b0 then 189 else 926) else (if b0 then 677 else 679))
  | 0, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 847 else 254) else (if b0 then 271 else -471))
    else
      (if b1 then (if b0 then 520 else 487) else (if b0 then 1421 else 184))
  else
    if b2 then
      (if b1 then (if b0 then -323 else -901) else (if b0 then -1491 else 334))
    else
      (if b1 then (if b0 then -168 else -459) else (if b0 then 1486 else -788))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 724 else -341) else (if b0 then -1531 else -1153))
    else
      (if b1 then (if b0 then 1331 else 887) else (if b0 then 767 else -1948))
  else
    if b2 then
      (if b1 then (if b0 then -702 else -697) else (if b0 then -624 else 866))
    else
      (if b1 then (if b0 then -642 else -288) else (if b0 then 16 else 132))
  | 0, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -821 else 522) else (if b0 then -281 else 2251))
    else
      (if b1 then (if b0 then -645 else 776) else (if b0 then 29 else 603))
  else
    if b2 then
      (if b1 then (if b0 then 522 else 369) else (if b0 then 50 else 343))
    else
      (if b1 then (if b0 then 78 else 456) else (if b0 then -84 else -1593))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1041 else 1665) else (if b0 then 2391 else 1454))
    else
      (if b1 then (if b0 then -467 else -1396) else (if b0 then 1198 else -964))
  else
    if b2 then
      (if b1 then (if b0 then 929 else 1083) else (if b0 then 198 else 563))
    else
      (if b1 then (if b0 then -433 else -1944) else (if b0 then 151 else -286))
  | 0, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -359 else -677) else (if b0 then 109 else 423))
    else
      (if b1 then (if b0 then -2272 else 656) else (if b0 then 617 else -348))
  else
    if b2 then
      (if b1 then (if b0 then 1654 else -14) else (if b0 then -720 else 1315))
    else
      (if b1 then (if b0 then -108 else 1317) else (if b0 then 1108 else -2028))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -545 else -1486) else (if b0 then 1015 else 318))
    else
      (if b1 then (if b0 then 1235 else -100) else (if b0 then 459 else 1166))
  else
    if b2 then
      (if b1 then (if b0 then -239 else 332) else (if b0 then 1424 else -899))
    else
      (if b1 then (if b0 then 577 else 51) else (if b0 then 710 else 262))
  | 0, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -772 else -137) else (if b0 then -139 else -512))
    else
      (if b1 then (if b0 then -326 else 2456) else (if b0 then -122 else 1049))
  else
    if b2 then
      (if b1 then (if b0 then 288 else 270) else (if b0 then -86 else -349))
    else
      (if b1 then (if b0 then -17 else -2006) else (if b0 then -262 else -605))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 481 else 1562) else (if b0 then 1070 else 571))
    else
      (if b1 then (if b0 then 2264 else -98) else (if b0 then 22 else -1672))
  else
    if b2 then
      (if b1 then (if b0 then -3099 else -672) else (if b0 then -1247 else 218))
    else
      (if b1 then (if b0 then 195 else 352) else (if b0 then 571 else -818))
  | 0, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -673 else -535) else (if b0 then 460 else 468))
    else
      (if b1 then (if b0 then 447 else -2348) else (if b0 then -95 else -1140))
  else
    if b2 then
      (if b1 then (if b0 then -694 else -875) else (if b0 then 4181 else -1463))
    else
      (if b1 then (if b0 then 25 else 772) else (if b0 then -1967 else 660))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -369 else 1321) else (if b0 then -438 else -296))
    else
      (if b1 then (if b0 then 873 else -104) else (if b0 then 88 else 790))
  else
    if b2 then
      (if b1 then (if b0 then -426 else -808) else (if b0 then -115 else -553))
    else
      (if b1 then (if b0 then 378 else -722) else (if b0 then -1347 else -350))
  | 1, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1430 else -440) else (if b0 then 160 else 600))
    else
      (if b1 then (if b0 then 476 else -3628) else (if b0 then 229 else 266))
  else
    if b2 then
      (if b1 then (if b0 then 2112 else 30) else (if b0 then -850 else -794))
    else
      (if b1 then (if b0 then 164 else 197) else (if b0 then 477 else -1777))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 965 else 2401) else (if b0 then 1444 else 1391))
    else
      (if b1 then (if b0 then 1229 else -2855) else (if b0 then 291 else 243))
  else
    if b2 then
      (if b1 then (if b0 then -1791 else -441) else (if b0 then 183 else 720))
    else
      (if b1 then (if b0 then -1352 else -583) else (if b0 then -165 else -1755))
  | 1, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 696 else 761) else (if b0 then -498 else 422))
    else
      (if b1 then (if b0 then 2126 else -298) else (if b0 then 190 else 764))
  else
    if b2 then
      (if b1 then (if b0 then -867 else 673) else (if b0 then 507 else -817))
    else
      (if b1 then (if b0 then 725 else 194) else (if b0 then 317 else -141))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1335 else -640) else (if b0 then 2486 else 2429))
    else
      (if b1 then (if b0 then -1833 else -2545) else (if b0 then 185 else -1303))
  else
    if b2 then
      (if b1 then (if b0 then 716 else -718) else (if b0 then 15 else -927))
    else
      (if b1 then (if b0 then -493 else 1871) else (if b0 then -47 else 816))
  | 1, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 581 else -727) else (if b0 then -1195 else 1238))
    else
      (if b1 then (if b0 then 348 else -3162) else (if b0 then 854 else -1122))
  else
    if b2 then
      (if b1 then (if b0 then -1042 else -1011) else (if b0 then 1164 else -2258))
    else
      (if b1 then (if b0 then -1029 else 2044) else (if b0 then -344 else 736))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1476 else -1864) else (if b0 then -1737 else -253))
    else
      (if b1 then (if b0 then -577 else 1792) else (if b0 then -1573 else 696))
  else
    if b2 then
      (if b1 then (if b0 then 1020 else 725) else (if b0 then 1172 else -291))
    else
      (if b1 then (if b0 then 247 else 1706) else (if b0 then -12 else 352))
  | 1, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 431 else 287) else (if b0 then 1548 else 619))
    else
      (if b1 then (if b0 then 636 else 665) else (if b0 then 754 else -1120))
  else
    if b2 then
      (if b1 then (if b0 then -33 else -91) else (if b0 then -1044 else -1063))
    else
      (if b1 then (if b0 then 331 else -158) else (if b0 then -1320 else -1664))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -873 else -487) else (if b0 then 1241 else -1623))
    else
      (if b1 then (if b0 then -454 else -1323) else (if b0 then 550 else -659))
  else
    if b2 then
      (if b1 then (if b0 then 74 else 1845) else (if b0 then 1283 else 72))
    else
      (if b1 then (if b0 then 175 else 141) else (if b0 then -146 else 1196))
  | 1, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1054 else 1976) else (if b0 then 1434 else 720))
    else
      (if b1 then (if b0 then 2777 else 2640) else (if b0 then -1387 else 468))
  else
    if b2 then
      (if b1 then (if b0 then -2903 else -225) else (if b0 then -910 else -757))
    else
      (if b1 then (if b0 then 609 else 521) else (if b0 then 641 else 977))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1992 else 907) else (if b0 then 2097 else 219))
    else
      (if b1 then (if b0 then -765 else -1082) else (if b0 then -890 else 1128))
  else
    if b2 then
      (if b1 then (if b0 then 909 else -797) else (if b0 then 118 else -1094))
    else
      (if b1 then (if b0 then -103 else 1877) else (if b0 then 468 else -206))
  | 1, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1005 else -842) else (if b0 then 1118 else 631))
    else
      (if b1 then (if b0 then -474 else 1270) else (if b0 then -2075 else 62))
  else
    if b2 then
      (if b1 then (if b0 then -2670 else -1232) else (if b0 then -160 else -120))
    else
      (if b1 then (if b0 then -1547 else 381) else (if b0 then 152 else 2472))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -999 else -1322) else (if b0 then -2868 else -489))
    else
      (if b1 then (if b0 then 1099 else 4874) else (if b0 then 267 else -584))
  else
    if b2 then
      (if b1 then (if b0 then 1036 else -661) else (if b0 then -985 else -583))
    else
      (if b1 then (if b0 then -372 else 861) else (if b0 then -820 else 725))
  | 1, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 644 else -403) else (if b0 then 303 else 347))
    else
      (if b1 then (if b0 then -98 else -2323) else (if b0 then 1038 else 561))
  else
    if b2 then
      (if b1 then (if b0 then 805 else -1478) else (if b0 then -87 else 1190))
    else
      (if b1 then (if b0 then -228 else 350) else (if b0 then 2157 else -556))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1372 else 1729) else (if b0 then -578 else 134))
    else
      (if b1 then (if b0 then 202 else -153) else (if b0 then -1378 else -755))
  else
    if b2 then
      (if b1 then (if b0 then -934 else 316) else (if b0 then -2551 else 1003))
    else
      (if b1 then (if b0 then 1065 else -322) else (if b0 then 692 else -590))
  | 1, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1870 else -936) else (if b0 then 1330 else -1744))
    else
      (if b1 then (if b0 then -967 else -4674) else (if b0 then 1106 else -181))
  else
    if b2 then
      (if b1 then (if b0 then 969 else 727) else (if b0 then 721 else -189))
    else
      (if b1 then (if b0 then -1957 else 43) else (if b0 then -199 else -2425))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1513 else 570) else (if b0 then 31 else -1127))
    else
      (if b1 then (if b0 then -2586 else -304) else (if b0 then 19 else 617))
  else
    if b2 then
      (if b1 then (if b0 then 270 else 1116) else (if b0 then -771 else 55))
    else
      (if b1 then (if b0 then 169 else 234) else (if b0 then 193 else -437))
  | 2, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -216 else 920) else (if b0 then 237 else 34))
    else
      (if b1 then (if b0 then 453 else 567) else (if b0 then 725 else 244))
  else
    if b2 then
      (if b1 then (if b0 then -916 else -165) else (if b0 then 139 else -1657))
    else
      (if b1 then (if b0 then -359 else -624) else (if b0 then -352 else 655))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 293 else -332) else (if b0 then 36 else -107))
    else
      (if b1 then (if b0 then -1387 else 407) else (if b0 then -261 else 240))
  else
    if b2 then
      (if b1 then (if b0 then 2078 else 1119) else (if b0 then -311 else -978))
    else
      (if b1 then (if b0 then 587 else 631) else (if b0 then 531 else 393))
  | 2, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 32 else 118) else (if b0 then 658 else 233))
    else
      (if b1 then (if b0 then -370 else 238) else (if b0 then 1535 else 752))
  else
    if b2 then
      (if b1 then (if b0 then -113 else -609) else (if b0 then 259 else 471))
    else
      (if b1 then (if b0 then -553 else -382) else (if b0 then 95 else -652))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1710 else 1616) else (if b0 then 1676 else -448))
    else
      (if b1 then (if b0 then -261 else 354) else (if b0 then 1178 else 1300))
  else
    if b2 then
      (if b1 then (if b0 then 757 else 597) else (if b0 then 2722 else -656))
    else
      (if b1 then (if b0 then -1309 else -1832) else (if b0 then -2015 else -1110))
  | 2, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -287 else -318) else (if b0 then -1635 else -116))
    else
      (if b1 then (if b0 then 243 else 1065) else (if b0 then 1854 else 371))
  else
    if b2 then
      (if b1 then (if b0 then -31 else 953) else (if b0 then 2538 else 515))
    else
      (if b1 then (if b0 then 321 else -1407) else (if b0 then -610 else 235))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 668 else 278) else (if b0 then 535 else -567))
    else
      (if b1 then (if b0 then 574 else 1569) else (if b0 then -131 else 871))
  else
    if b2 then
      (if b1 then (if b0 then -381 else 2015) else (if b0 then 260 else -1253))
    else
      (if b1 then (if b0 then -642 else -619) else (if b0 then -1022 else -441))
  | 2, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 404 else 758) else (if b0 then -770 else -689))
    else
      (if b1 then (if b0 then 1411 else -275) else (if b0 then 1166 else 542))
  else
    if b2 then
      (if b1 then (if b0 then -1714 else 128) else (if b0 then -997 else -1159))
    else
      (if b1 then (if b0 then -637 else 112) else (if b0 then 164 else -745))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 440 else 1877) else (if b0 then -1340 else -283))
    else
      (if b1 then (if b0 then 1362 else 894) else (if b0 then 804 else 355))
  else
    if b2 then
      (if b1 then (if b0 then -1528 else 462) else (if b0 then -217 else 655))
    else
      (if b1 then (if b0 then -455 else -1111) else (if b0 then -191 else -273))
  | 2, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 156 else 211) else (if b0 then -1948 else -185))
    else
      (if b1 then (if b0 then 496 else -809) else (if b0 then -158 else -1399))
  else
    if b2 then
      (if b1 then (if b0 then 396 else 31) else (if b0 then -1347 else -686))
    else
      (if b1 then (if b0 then 997 else 2851) else (if b0 then 48 else 137))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1457 else -139) else (if b0 then -1066 else 311))
    else
      (if b1 then (if b0 then -184 else -1536) else (if b0 then -1747 else -1985))
  else
    if b2 then
      (if b1 then (if b0 then -905 else 1542) else (if b0 then -1071 else 548))
    else
      (if b1 then (if b0 then 84 else -204) else (if b0 then 930 else 17))
  | 2, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 303 else 320) else (if b0 then -204 else 553))
    else
      (if b1 then (if b0 then 1139 else 1102) else (if b0 then 231 else 276))
  else
    if b2 then
      (if b1 then (if b0 then -677 else 44) else (if b0 then -1001 else 1344))
    else
      (if b1 then (if b0 then 285 else 446) else (if b0 then 118 else -440))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 101 else 585) else (if b0 then -261 else -242))
    else
      (if b1 then (if b0 then 102 else -134) else (if b0 then 160 else 908))
  else
    if b2 then
      (if b1 then (if b0 then -778 else 654) else (if b0 then -81 else 331))
    else
      (if b1 then (if b0 then -1115 else -1558) else (if b0 then -885 else -958))
  | 2, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then -424 else 449) else (if b0 then 183 else 279))
    else
      (if b1 then (if b0 then -1819 else -581) else (if b0 then 778 else -241))
  else
    if b2 then
      (if b1 then (if b0 then 1361 else 169) else (if b0 then 1601 else -440))
    else
      (if b1 then (if b0 then -234 else -1140) else (if b0 then 14 else 583))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 695 else 24) else (if b0 then 1190 else -24))
    else
      (if b1 then (if b0 then -2071 else -513) else (if b0 then -233 else -854))
  else
    if b2 then
      (if b1 then (if b0 then 3030 else -91) else (if b0 then 484 else 1226))
    else
      (if b1 then (if b0 then 360 else 707) else (if b0 then -295 else 191))
  | 2, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 264 else -789) else (if b0 then 999 else 556))
    else
      (if b1 then (if b0 then -698 else 108) else (if b0 then 188 else -438))
  else
    if b2 then
      (if b1 then (if b0 then 180 else 598) else (if b0 then -2595 else 2230))
    else
      (if b1 then (if b0 then -516 else -419) else (if b0 then 2393 else 1500))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 314 else -709) else (if b0 then 943 else -631))
    else
      (if b1 then (if b0 then -409 else -26) else (if b0 then 304 else 185))
  else
    if b2 then
      (if b1 then (if b0 then 542 else 254) else (if b0 then 1844 else -1908))
    else
      (if b1 then (if b0 then -202 else 16) else (if b0 then -567 else -709))
  | 3, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -1527) else (if b0 then 0 else -854))
    else
      (if b1 then (if b0 then -2771 else 2301) else (if b0 then -1231 else 673))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -466) else (if b0 then 0 else -1916))
    else
      (if b1 then (if b0 then -974 else 661) else (if b0 then -1903 else 2030))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 765 else -2994) else (if b0 then -723 else -454))
    else
      (if b1 then (if b0 then -97 else 1826) else (if b0 then 357 else 2031))
  else
    if b2 then
      (if b1 then (if b0 then 660 else -673) else (if b0 then 4947 else -964))
    else
      (if b1 then (if b0 then -258 else -704) else (if b0 then -1370 else -210))
  | 3, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 632) else (if b0 then 0 else -606))
    else
      (if b1 then (if b0 then -2561 else 2163) else (if b0 then -887 else 889))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 204) else (if b0 then 0 else -397))
    else
      (if b1 then (if b0 then -132 else 291) else (if b0 then -87 else -596))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1321 else -405) else (if b0 then 1545 else 414))
    else
      (if b1 then (if b0 then 1380 else 956) else (if b0 then -946 else -468))
  else
    if b2 then
      (if b1 then (if b0 then 494 else 625) else (if b0 then 704 else 1777))
    else
      (if b1 then (if b0 then -1027 else 959) else (if b0 then 1493 else 437))
  | 3, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 1843) else (if b0 then 0 else 710))
    else
      (if b1 then (if b0 then -96 else 720) else (if b0 then -1616 else -901))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -735) else (if b0 then 0 else 2490))
    else
      (if b1 then (if b0 then -506 else -769) else (if b0 then -489 else 590))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -721 else -1258) else (if b0 then -572 else -747))
    else
      (if b1 then (if b0 then 58 else -58) else (if b0 then 460 else -1845))
  else
    if b2 then
      (if b1 then (if b0 then -665 else 1037) else (if b0 then -821 else 29))
    else
      (if b1 then (if b0 then -169 else -39) else (if b0 then 160 else -885))
  | 3, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 1744) else (if b0 then 0 else -53))
    else
      (if b1 then (if b0 then -767 else -2716) else (if b0 then -2244 else 539))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -43) else (if b0 then 0 else -1497))
    else
      (if b1 then (if b0 then -676 else 721) else (if b0 then -3676 else 1509))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -2372 else -728) else (if b0 then 3046 else -213))
    else
      (if b1 then (if b0 then 1 else -2443) else (if b0 then 18 else -1399))
  else
    if b2 then
      (if b1 then (if b0 then 656 else 637) else (if b0 then 1216 else -539))
    else
      (if b1 then (if b0 then -1579 else -3) else (if b0 then 404 else -179))
  | 3, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 1277) else (if b0 then 0 else 1684))
    else
      (if b1 then (if b0 then 1124 else 1078) else (if b0 then 1220 else 551))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 47) else (if b0 then 0 else 1604))
    else
      (if b1 then (if b0 then 1375 else 1463) else (if b0 then 1361 else -884))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -738 else 19) else (if b0 then -1473 else -85))
    else
      (if b1 then (if b0 then -134 else 87) else (if b0 then -762 else -216))
  else
    if b2 then
      (if b1 then (if b0 then -1187 else 308) else (if b0 then -2810 else 368))
    else
      (if b1 then (if b0 then -877 else -764) else (if b0 then 114 else -801))
  | 3, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -620) else (if b0 then 0 else -617))
    else
      (if b1 then (if b0 then 1461 else -2485) else (if b0 then -1539 else -591))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -1359) else (if b0 then 0 else -3033))
    else
      (if b1 then (if b0 then -1558 else 1596) else (if b0 then -1704 else 2650))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -2570 else -2228) else (if b0 then -1422 else -786))
    else
      (if b1 then (if b0 then -82 else -1007) else (if b0 then -263 else 302))
  else
    if b2 then
      (if b1 then (if b0 then -464 else 1061) else (if b0 then 3183 else -683))
    else
      (if b1 then (if b0 then 152 else 665) else (if b0 then 439 else -347))
  | 3, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 897) else (if b0 then 0 else 868))
    else
      (if b1 then (if b0 then -2555 else 2303) else (if b0 then -818 else 700))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 316) else (if b0 then 0 else -557))
    else
      (if b1 then (if b0 then 261 else -1634) else (if b0 then -711 else 259))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -219 else -1495) else (if b0 then 1502 else 1226))
    else
      (if b1 then (if b0 then 1723 else 387) else (if b0 then -182 else 646))
  else
    if b2 then
      (if b1 then (if b0 then 1322 else 956) else (if b0 then 1094 else 228))
    else
      (if b1 then (if b0 then 1305 else 895) else (if b0 then -162 else -216))
  | 3, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -987) else (if b0 then 0 else 24))
    else
      (if b1 then (if b0 then -1310 else 501) else (if b0 then 407 else 612))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 652) else (if b0 then 0 else -1400))
    else
      (if b1 then (if b0 then -486 else -877) else (if b0 then -1060 else 120))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 322 else -86) else (if b0 then 1187 else 1110))
    else
      (if b1 then (if b0 then -2306 else -100) else (if b0 then -283 else 46))
  else
    if b2 then
      (if b1 then (if b0 then 1137 else 981) else (if b0 then 1965 else -586))
    else
      (if b1 then (if b0 then 2805 else -379) else (if b0 then 1437 else 2127))
  | 4, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 188) else (if b0 then 0 else -167))
    else
      (if b1 then (if b0 then 344 else -2021) else (if b0 then 530 else 2244))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 753) else (if b0 then 0 else 1179))
    else
      (if b1 then (if b0 then 2424 else 2505) else (if b0 then 963 else 526))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -980 else -413) else (if b0 then 211 else -384))
    else
      (if b1 then (if b0 then -418 else -1) else (if b0 then 394 else -72))
  else
    if b2 then
      (if b1 then (if b0 then -753 else -583) else (if b0 then -588 else -196))
    else
      (if b1 then (if b0 then 254 else -58) else (if b0 then 233 else 2338))
  | 4, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -416) else (if b0 then 0 else 1704))
    else
      (if b1 then (if b0 then 1112 else -1612) else (if b0 then 1520 else 1444))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 2101) else (if b0 then 0 else -2752))
    else
      (if b1 then (if b0 then 2781 else -562) else (if b0 then 272 else -1268))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1589 else 803) else (if b0 then -1002 else 2663))
    else
      (if b1 then (if b0 then -221 else 948) else (if b0 then -391 else 1826))
  else
    if b2 then
      (if b1 then (if b0 then -2487 else 1703) else (if b0 then -1587 else 2326))
    else
      (if b1 then (if b0 then 901 else 11) else (if b0 then -311 else 1916))
  | 4, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -1043) else (if b0 then 0 else 506))
    else
      (if b1 then (if b0 then 2068 else -887) else (if b0 then 1228 else -299))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 868) else (if b0 then 0 else -1042))
    else
      (if b1 then (if b0 then 2989 else 3453) else (if b0 then 2298 else 1201))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -4023 else -2003) else (if b0 then 886 else -189))
    else
      (if b1 then (if b0 then -725 else -840) else (if b0 then -1058 else 417))
  else
    if b2 then
      (if b1 then (if b0 then -153 else 943) else (if b0 then -451 else -456))
    else
      (if b1 then (if b0 then -1562 else 2333) else (if b0 then 964 else -64))
  | 4, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -7) else (if b0 then 0 else 596))
    else
      (if b1 then (if b0 then -858 else 340) else (if b0 then -342 else -479))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 185) else (if b0 then 0 else -1928))
    else
      (if b1 then (if b0 then -2110 else -3675) else (if b0 then -2280 else -479))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 3391 else 1809) else (if b0 then 982 else 2702))
    else
      (if b1 then (if b0 then 1200 else 448) else (if b0 then 2270 else 820))
  else
    if b2 then
      (if b1 then (if b0 then -19 else 773) else (if b0 then 52 else 1901))
    else
      (if b1 then (if b0 then -702 else -135) else (if b0 then -2090 else 35))
  | 4, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -230) else (if b0 then 0 else 283))
    else
      (if b1 then (if b0 then 537 else -2386) else (if b0 then 852 else -342))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1089) else (if b0 then 0 else 77))
    else
      (if b1 then (if b0 then 3377 else 2718) else (if b0 then 1350 else 19))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1794 else -544) else (if b0 then 273 else 377))
    else
      (if b1 then (if b0 then -1704 else 300) else (if b0 then 353 else 2201))
  else
    if b2 then
      (if b1 then (if b0 then -853 else 309) else (if b0 then -610 else 593))
    else
      (if b1 then (if b0 then -1110 else 1628) else (if b0 then -2144 else 572))
  | 4, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 1699) else (if b0 then 0 else 1152))
    else
      (if b1 then (if b0 then 2912 else -9879) else (if b0 then 578 else 389))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1642) else (if b0 then 0 else 4159))
    else
      (if b1 then (if b0 then 4465 else 4287) else (if b0 then 2271 else 24))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1663 else 1220) else (if b0 then 1542 else 2639))
    else
      (if b1 then (if b0 then 580 else -2916) else (if b0 then -807 else -603))
  else
    if b2 then
      (if b1 then (if b0 then -1680 else -810) else (if b0 then -974 else 694))
    else
      (if b1 then (if b0 then -1024 else 2243) else (if b0 then 754 else 3967))
  | 4, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 193) else (if b0 then 0 else 1218))
    else
      (if b1 then (if b0 then 4608 else -4741) else (if b0 then 300 else -91))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -288) else (if b0 then 0 else 427))
    else
      (if b1 then (if b0 then 579 else 2269) else (if b0 then 2510 else 65))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 115 else -353) else (if b0 then 2078 else 1470))
    else
      (if b1 then (if b0 then -1218 else -3559) else (if b0 then 805 else -341))
  else
    if b2 then
      (if b1 then (if b0 then 407 else 211) else (if b0 then 176 else -188))
    else
      (if b1 then (if b0 then 33 else 390) else (if b0 then -66 else 1353))
  | 4, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 339) else (if b0 then 0 else -873))
    else
      (if b1 then (if b0 then 2760 else -2121) else (if b0 then -1916 else -387))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -1066) else (if b0 then 0 else -874))
    else
      (if b1 then (if b0 then 681 else 1743) else (if b0 then 1664 else 877))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1406 else -1033) else (if b0 then -688 else -819))
    else
      (if b1 then (if b0 then 137 else -1369) else (if b0 then -159 else 284))
  else
    if b2 then
      (if b1 then (if b0 then 611 else 506) else (if b0 then 1232 else 644))
    else
      (if b1 then (if b0 then -2061 else -1129) else (if b0 then 394 else 2645))
  | 5, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -457) else (if b0 then 0 else -924))
    else
      (if b1 then (if b0 then -2771 else -1085) else (if b0 then -1920 else 61))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 949) else (if b0 then 0 else -334))
    else
      (if b1 then (if b0 then -406 else -73) else (if b0 then -1302 else 944))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 267 else 694) else (if b0 then 1772 else -1440))
    else
      (if b1 then (if b0 then -12 else -1341) else (if b0 then -1142 else 789))
  else
    if b2 then
      (if b1 then (if b0 then -1212 else 289) else (if b0 then 3081 else 1489))
    else
      (if b1 then (if b0 then -288 else 92) else (if b0 then 1358 else -346))
  | 5, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -2658) else (if b0 then 0 else -3319))
    else
      (if b1 then (if b0 then 904 else 36) else (if b0 then -702 else -1524))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -241) else (if b0 then 0 else -2110))
    else
      (if b1 then (if b0 then 906 else -198) else (if b0 then -808 else 1159))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -92 else -129) else (if b0 then -2856 else -1440))
    else
      (if b1 then (if b0 then -1215 else -1196) else (if b0 then 196 else -190))
  else
    if b2 then
      (if b1 then (if b0 then -839 else -201) else (if b0 then 1930 else -270))
    else
      (if b1 then (if b0 then -1900 else 548) else (if b0 then 378 else -1088))
  | 5, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -56) else (if b0 then 0 else 721))
    else
      (if b1 then (if b0 then -2935 else -422) else (if b0 then -1348 else 119))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1061) else (if b0 then 0 else 875))
    else
      (if b1 then (if b0 then -243 else -1532) else (if b0 then 155 else 141))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1489 else 14) else (if b0 then 1161 else -275))
    else
      (if b1 then (if b0 then 532 else 76) else (if b0 then 741 else -413))
  else
    if b2 then
      (if b1 then (if b0 then -331 else 1233) else (if b0 then 2405 else -1869))
    else
      (if b1 then (if b0 then -1261 else 879) else (if b0 then -171 else 297))
  | 5, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 554) else (if b0 then 0 else 2397))
    else
      (if b1 then (if b0 then 3716 else 1115) else (if b0 then -172 else 323))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -2235) else (if b0 then 0 else -2368))
    else
      (if b1 then (if b0 then -733 else 526) else (if b0 then -207 else 964))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1461 else -739) else (if b0 then -891 else -614))
    else
      (if b1 then (if b0 then -1586 else 897) else (if b0 then -1604 else 120))
  else
    if b2 then
      (if b1 then (if b0 then -872 else -200) else (if b0 then -3092 else 143))
    else
      (if b1 then (if b0 then -2784 else -2023) else (if b0 then 469 else -1147))
  | 5, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -639) else (if b0 then 0 else 92))
    else
      (if b1 then (if b0 then -1670 else -748) else (if b0 then 56 else -187))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 395) else (if b0 then 0 else 225))
    else
      (if b1 then (if b0 then -601 else -2367) else (if b0 then 227 else -2273))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 408 else 339) else (if b0 then 637 else 367))
    else
      (if b1 then (if b0 then -1820 else -2183) else (if b0 then 50 else -833))
  else
    if b2 then
      (if b1 then (if b0 then -1170 else -1730) else (if b0 then 1584 else 675))
    else
      (if b1 then (if b0 then -203 else -1652) else (if b0 then -2041 else 713))
  | 5, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -233) else (if b0 then 0 else -660))
    else
      (if b1 then (if b0 then 570 else -1518) else (if b0 then 203 else -1631))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 417) else (if b0 then 0 else 262))
    else
      (if b1 then (if b0 then 1207 else 631) else (if b0 then 1174 else 1650))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -456 else -295) else (if b0 then -1201 else 428))
    else
      (if b1 then (if b0 then -56 else 367) else (if b0 then -206 else -1157))
  else
    if b2 then
      (if b1 then (if b0 then -588 else -784) else (if b0 then -150 else 310))
    else
      (if b1 then (if b0 then -170 else 204) else (if b0 then -103 else -1185))
  | 5, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -476) else (if b0 then 0 else 1569))
    else
      (if b1 then (if b0 then -2107 else -1399) else (if b0 then -102 else 816))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 846) else (if b0 then 0 else 2332))
    else
      (if b1 then (if b0 then 495 else -1473) else (if b0 then -1636 else 420))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 217 else 136) else (if b0 then 296 else 257))
    else
      (if b1 then (if b0 then -543 else 1218) else (if b0 then 356 else -929))
  else
    if b2 then
      (if b1 then (if b0 then -537 else 579) else (if b0 then 998 else 1104))
    else
      (if b1 then (if b0 then -402 else -697) else (if b0 then 1996 else -565))
  | 5, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -783) else (if b0 then 0 else -893))
    else
      (if b1 then (if b0 then -811 else -927) else (if b0 then -12 else 543))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -972) else (if b0 then 0 else -1512))
    else
      (if b1 then (if b0 then -637 else -18) else (if b0 then 829 else 1047))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 666 else 101) else (if b0 then 696 else 217))
    else
      (if b1 then (if b0 then -1002 else -100) else (if b0 then -16 else -649))
  else
    if b2 then
      (if b1 then (if b0 then 901 else 446) else (if b0 then 1552 else -1076))
    else
      (if b1 then (if b0 then 1080 else 1316) else (if b0 then 127 else -627))
  | 6, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -1127) else (if b0 then 0 else 932))
    else
      (if b1 then (if b0 then -1032 else -1824) else (if b0 then 2223 else 152))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1354) else (if b0 then 0 else 2634))
    else
      (if b1 then (if b0 then 324 else 2493) else (if b0 then 2278 else 2255))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -109 else -738) else (if b0 then -1141 else -1370))
    else
      (if b1 then (if b0 then -238 else -1733) else (if b0 then -1659 else -1959))
  else
    if b2 then
      (if b1 then (if b0 then 1493 else 241) else (if b0 then 1567 else -47))
    else
      (if b1 then (if b0 then 210 else 1041) else (if b0 then -1527 else 229))
  | 6, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 1387) else (if b0 then 0 else -81))
    else
      (if b1 then (if b0 then -1123 else -1036) else (if b0 then -1471 else -593))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 861) else (if b0 then 0 else 1035))
    else
      (if b1 then (if b0 then 1983 else 405) else (if b0 then -1107 else -1334))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1523 else -481) else (if b0 then 72 else -117))
    else
      (if b1 then (if b0 then 945 else -435) else (if b0 then 181 else -903))
  else
    if b2 then
      (if b1 then (if b0 then -50 else 369) else (if b0 then -722 else 1107))
    else
      (if b1 then (if b0 then -373 else -309) else (if b0 then 1998 else 659))
  | 6, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 1813) else (if b0 then 0 else 1810))
    else
      (if b1 then (if b0 then 4496 else 867) else (if b0 then -1314 else -855))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -1717) else (if b0 then 0 else -1522))
    else
      (if b1 then (if b0 then -103 else 3692) else (if b0 then -1389 else 252))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -2902 else -2502) else (if b0 then -1074 else -950))
    else
      (if b1 then (if b0 then 725 else -1686) else (if b0 then 261 else 440))
  else
    if b2 then
      (if b1 then (if b0 then -4356 else -4953) else (if b0 then -4506 else -4820))
    else
      (if b1 then (if b0 then 1602 else -1722) else (if b0 then 607 else -899))
  | 6, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -1289) else (if b0 then 0 else 1519))
    else
      (if b1 then (if b0 then 47 else -1193) else (if b0 then -191 else 740))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1067) else (if b0 then 0 else 2359))
    else
      (if b1 then (if b0 then 419 else 4277) else (if b0 then 1917 else 2316))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -623 else -1832) else (if b0 then -1203 else -1259))
    else
      (if b1 then (if b0 then -147 else -2180) else (if b0 then -415 else 1287))
  else
    if b2 then
      (if b1 then (if b0 then 560 else -1322) else (if b0 then 456 else -1877))
    else
      (if b1 then (if b0 then -364 else 948) else (if b0 then -32 else 141))
  | 6, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 1217) else (if b0 then 0 else -1549))
    else
      (if b1 then (if b0 then -921 else 3067) else (if b0 then 586 else -1040))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1027) else (if b0 then 0 else -2862))
    else
      (if b1 then (if b0 then -2363 else -9535) else (if b0 then -1504 else -4082))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 2631 else 4045) else (if b0 then 2125 else 2411))
    else
      (if b1 then (if b0 then -1038 else 3266) else (if b0 then -1718 else 1095))
  else
    if b2 then
      (if b1 then (if b0 then 321 else 3603) else (if b0 then 1508 else 3876))
    else
      (if b1 then (if b0 then -1407 else -2760) else (if b0 then -2016 else -3671))
  | 6, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -654) else (if b0 then 0 else -421))
    else
      (if b1 then (if b0 then 1270 else -3752) else (if b0 then -799 else -1160))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -1333) else (if b0 then 0 else 409))
    else
      (if b1 then (if b0 then 2363 else 6210) else (if b0 then 328 else -151))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -3000 else -2205) else (if b0 then -320 else -273))
    else
      (if b1 then (if b0 then -2305 else -2479) else (if b0 then -364 else -1875))
  else
    if b2 then
      (if b1 then (if b0 then -261 else -1424) else (if b0 then -1620 else -1179))
    else
      (if b1 then (if b0 then 1503 else 2663) else (if b0 then 3360 else 3849))
  | 6, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else -648) else (if b0 then 0 else -1247))
    else
      (if b1 then (if b0 then 2089 else -4285) else (if b0 then 259 else -959))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1335) else (if b0 then 0 else -1637))
    else
      (if b1 then (if b0 then 2527 else 1568) else (if b0 then 4126 else -3310))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -3652 else -640) else (if b0 then -2363 else -1698))
    else
      (if b1 then (if b0 then 743 else -771) else (if b0 then -518 else -184))
  else
    if b2 then
      (if b1 then (if b0 then -621 else 1589) else (if b0 then 656 else 2625))
    else
      (if b1 then (if b0 then -427 else 872) else (if b0 then -280 else 1183))
  | 6, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then (if b0 then 0 else 481) else (if b0 then 0 else -820))
    else
      (if b1 then (if b0 then -1268 else -382) else (if b0 then 555 else 651))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1446) else (if b0 then 0 else 957))
    else
      (if b1 then (if b0 then 368 else -1737) else (if b0 then 62 else -1713))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -415 else 71) else (if b0 then 631 else 324))
    else
      (if b1 then (if b0 then -219 else -1500) else (if b0 then -73 else 812))
  else
    if b2 then
      (if b1 then (if b0 then 1570 else 2067) else (if b0 then 1076 else 2332))
    else
      (if b1 then (if b0 then 758 else 1) else (if b0 then -383 else -473))
  | 7, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else -1350))
    else
      (if b1 then 0 else (if b0 then -975 else -520))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -876) else (if b0 then 0 else -3587))
    else
      (if b1 then (if b0 then -24 else -582) else (if b0 then -3613 else -2358))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 3347 else 431) else (if b0 then 3851 else 1558))
    else
      (if b1 then (if b0 then 341 else -2756) else (if b0 then 1370 else -477))
  else
    if b2 then
      (if b1 then (if b0 then -486 else 351) else (if b0 then 459 else -1146))
    else
      (if b1 then (if b0 then 335 else -261) else (if b0 then -179 else 105))
  | 7, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 363))
    else
      (if b1 then 0 else (if b0 then -1372 else -319))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 355) else (if b0 then 0 else -2194))
    else
      (if b1 then (if b0 then -923 else -403) else (if b0 then -2622 else -2183))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 2106 else 24) else (if b0 then 2836 else 1273))
    else
      (if b1 then (if b0 then -1045 else -2594) else (if b0 then 59 else -1335))
  else
    if b2 then
      (if b1 then (if b0 then 2085 else 533) else (if b0 then 548 else 853))
    else
      (if b1 then (if b0 then -109 else -592) else (if b0 then 135 else -1408))
  | 7, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 227))
    else
      (if b1 then 0 else (if b0 then -543 else -109))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 298) else (if b0 then 0 else -1211))
    else
      (if b1 then (if b0 then -173 else -97) else (if b0 then -1344 else -1222))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1152 else -147) else (if b0 then 1434 else 1752))
    else
      (if b1 then (if b0 then 249 else -2482) else (if b0 then -129 else 912))
  else
    if b2 then
      (if b1 then (if b0 then -535 else 198) else (if b0 then -118 else -1783))
    else
      (if b1 then (if b0 then -493 else 124) else (if b0 then -1891 else -3))
  | 7, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 3625))
    else
      (if b1 then 0 else (if b0 then 1362 else 3911))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 2404) else (if b0 then 0 else 1498))
    else
      (if b1 then (if b0 then 706 else 3780) else (if b0 then 1207 else 347))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1616 else -4589) else (if b0 then -1464 else -2470))
    else
      (if b1 then (if b0 then -194 else -2483) else (if b0 then -634 else 220))
  else
    if b2 then
      (if b1 then (if b0 then 244 else 1118) else (if b0 then 1345 else 329))
    else
      (if b1 then (if b0 then 426 else -431) else (if b0 then -636 else -4307))
  | 7, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 596))
    else
      (if b1 then 0 else (if b0 then -2059 else -1288))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -116) else (if b0 then 0 else -1696))
    else
      (if b1 then (if b0 then -2375 else -1493) else (if b0 then -2357 else -1913))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 1719 else 1335) else (if b0 then 2616 else 1790))
    else
      (if b1 then (if b0 then -277 else -1227) else (if b0 then 512 else -1520))
  else
    if b2 then
      (if b1 then (if b0 then 303 else 75) else (if b0 then 440 else 1271))
    else
      (if b1 then (if b0 then -324 else -224) else (if b0 then 231 else -1150))
  | 7, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 1267))
    else
      (if b1 then 0 else (if b0 then 1795 else 2575))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 1136) else (if b0 then 0 else 567))
    else
      (if b1 then (if b0 then 2456 else 2601) else (if b0 then 807 else -217))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1009 else -3125) else (if b0 then -1163 else -1425))
    else
      (if b1 then (if b0 then 664 else -2421) else (if b0 then 423 else 1506))
  else
    if b2 then
      (if b1 then (if b0 then 764 else 443) else (if b0 then -239 else 645))
    else
      (if b1 then (if b0 then -483 else -158) else (if b0 then -1138 else -1968))
  | 7, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 409))
    else
      (if b1 then 0 else (if b0 then -82 else 1858))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 911) else (if b0 then 0 else -615))
    else
      (if b1 then (if b0 then 246 else 1984) else (if b0 then -641 else 557))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -626 else -2280) else (if b0 then 858 else -644))
    else
      (if b1 then (if b0 then -669 else -1402) else (if b0 then -44 else 398))
  else
    if b2 then
      (if b1 then (if b0 then -846 else 400) else (if b0 then 1951 else 449))
    else
      (if b1 then (if b0 then 102 else -638) else (if b0 then 818 else -284))
  | 7, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else -219))
    else
      (if b1 then 0 else (if b0 then -555 else -606))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -886) else (if b0 then 0 else -1165))
    else
      (if b1 then (if b0 then -1311 else -756) else (if b0 then -1238 else -360))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -1422 else 906) else (if b0 then 1375 else 1949))
    else
      (if b1 then (if b0 then 695 else -45) else (if b0 then -826 else -231))
  else
    if b2 then
      (if b1 then (if b0 then 1001 else -101) else (if b0 then 36 else -690))
    else
      (if b1 then (if b0 then 1633 else 530) else (if b0 then -1204 else 1097))
  | 8, 0 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 906))
    else
      (if b1 then 0 else (if b0 then 220 else 2079))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 3640) else (if b0 then 0 else 917))
    else
      (if b1 then (if b0 then 3209 else 4080) else (if b0 then 3327 else 4760))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -4206 else -4245) else (if b0 then -1351 else -2552))
    else
      (if b1 then (if b0 then 1651 else -2795) else (if b0 then 468 else -176))
  else
    if b2 then
      (if b1 then (if b0 then -2349 else 848) else (if b0 then 125 else 362))
    else
      (if b1 then (if b0 then 2471 else 733) else (if b0 then 2227 else 1670))
  | 8, 1 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 648))
    else
      (if b1 then 0 else (if b0 then 1459 else 2396))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -1137) else (if b0 then 0 else -3407))
    else
      (if b1 then (if b0 then -244 else 1975) else (if b0 then -827 else 490))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -258 else -2227) else (if b0 then 2299 else -50))
    else
      (if b1 then (if b0 then -1047 else 765) else (if b0 then 933 else 3000))
  else
    if b2 then
      (if b1 then (if b0 then 2062 else -973) else (if b0 then -1434 else -2979))
    else
      (if b1 then (if b0 then -651 else -795) else (if b0 then 400 else -349))
  | 8, 2 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 4288))
    else
      (if b1 then 0 else (if b0 then 4106 else 1788))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 3663) else (if b0 then 0 else 1679))
    else
      (if b1 then (if b0 then 4163 else 2379) else (if b0 then 5496 else 7047))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -7414 else -4004) else (if b0 then -3901 else -3557))
    else
      (if b1 then (if b0 then -2093 else -5734) else (if b0 then 224 else -2085))
  else
    if b2 then
      (if b1 then (if b0 then 1026 else -155) else (if b0 then -4332 else -761))
    else
      (if b1 then (if b0 then 1144 else 22) else (if b0 then 2382 else -378))
  | 8, 3 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 1559))
    else
      (if b1 then 0 else (if b0 then 2463 else 1367))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -2248) else (if b0 then 0 else -1656))
    else
      (if b1 then (if b0 then -1518 else -1654) else (if b0 then -1588 else -679))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 668 else 720) else (if b0 then 362 else 158))
    else
      (if b1 then (if b0 then 1402 else 806) else (if b0 then 337 else 268))
  else
    if b2 then
      (if b1 then (if b0 then -445 else -44) else (if b0 then -3169 else -2288))
    else
      (if b1 then (if b0 then -549 else -931) else (if b0 then -2274 else -1861))
  | 8, 4 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 692))
    else
      (if b1 then 0 else (if b0 then -150 else -115))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 352) else (if b0 then 0 else 1072))
    else
      (if b1 then (if b0 then -432 else -569) else (if b0 then 1425 else 321))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -7 else 165) else (if b0 then -433 else -452))
    else
      (if b1 then (if b0 then -945 else -1058) else (if b0 then -2004 else -1299))
  else
    if b2 then
      (if b1 then (if b0 then 1549 else 92) else (if b0 then 77 else 476))
    else
      (if b1 then (if b0 then -838 else 1231) else (if b0 then -196 else -723))
  | 8, 5 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else -2383))
    else
      (if b1 then 0 else (if b0 then -1972 else -857))
  else
    if b2 then
      (if b1 then (if b0 then 0 else -2704) else (if b0 then 0 else -2553))
    else
      (if b1 then (if b0 then -2499 else -698) else (if b0 then -1931 else -4404))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 4226 else 1688) else (if b0 then 3625 else 2632))
    else
      (if b1 then (if b0 then -1273 else 3415) else (if b0 then -1807 else 2831))
  else
    if b2 then
      (if b1 then (if b0 then 3382 else -2090) else (if b0 then 2374 else -700))
    else
      (if b1 then (if b0 then -1625 else 456) else (if b0 then -820 else 184))
  | 8, 6 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else -420))
    else
      (if b1 then 0 else (if b0 then -1296 else -659))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 168) else (if b0 then 0 else -129))
    else
      (if b1 then (if b0 then -502 else 666) else (if b0 then 266 else -382))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then 733 else -389) else (if b0 then 1312 else 276))
    else
      (if b1 then (if b0 then -2133 else -362) else (if b0 then -284 else 534))
  else
    if b2 then
      (if b1 then (if b0 then 4545 else -135) else (if b0 then 1734 else 182))
    else
      (if b1 then (if b0 then -298 else 648) else (if b0 then 1000 else 182))
  | 8, 7 => if b4 then
  if b3 then
    if b2 then
      (if b1 then 0 else (if b0 then 0 else 391))
    else
      (if b1 then 0 else (if b0 then -246 else 1377))
  else
    if b2 then
      (if b1 then (if b0 then 0 else 2335) else (if b0 then 0 else 664))
    else
      (if b1 then (if b0 then 1841 else 2736) else (if b0 then 2832 else 2942))
else
  if b3 then
    if b2 then
      (if b1 then (if b0 then -2342 else -2804) else (if b0 then -642 else -1691))
    else
      (if b1 then (if b0 then 111 else -1691) else (if b0 then -1209 else -140))
  else
    if b2 then
      (if b1 then (if b0 then -966 else -1) else (if b0 then 524 else 427))
    else
      (if b1 then (if b0 then 46 else 1220) else (if b0 then 143 else 876))
  | _, _ => 0

private def checkQ2Sq (r : Fin 9) : Bool :=
  [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
  [false, true].all fun b1 => [false, true].all fun b0 =>
    decide (q2W r 0 b4 b3 b2 b1 b0 ^ 2 + q2W r 1 b4 b3 b2 b1 b0 ^ 2 +
            q2W r 2 b4 b3 b2 b1 b0 ^ 2 + q2W r 3 b4 b3 b2 b1 b0 ^ 2 +
            q2W r 4 b4 b3 b2 b1 b0 ^ 2 + q2W r 5 b4 b3 b2 b1 b0 ^ 2 +
            q2W r 6 b4 b3 b2 b1 b0 ^ 2 + q2W r 7 b4 b3 b2 b1 b0 ^ 2 ≤ K_Q2)
private lemma checkQ2Sq_ok (r : Fin 9) : checkQ2Sq r = true := by fin_cases r <;> decide

lemma q2W_sq_le (r : Fin 9) (b4 b3 b2 b1 b0 : Bool) :
    q2W r 0 b4 b3 b2 b1 b0 ^ 2 + q2W r 1 b4 b3 b2 b1 b0 ^ 2 +
    q2W r 2 b4 b3 b2 b1 b0 ^ 2 + q2W r 3 b4 b3 b2 b1 b0 ^ 2 +
    q2W r 4 b4 b3 b2 b1 b0 ^ 2 + q2W r 5 b4 b3 b2 b1 b0 ^ 2 +
    q2W r 6 b4 b3 b2 b1 b0 ^ 2 + q2W r 7 b4 b3 b2 b1 b0 ^ 2 ≤ K_Q2 := by
  have h2 := checkQ2Sq_ok r; unfold checkQ2Sq at h2
  have h3 := list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool h2 b4) b3) b2) b1) b0
  simp only [decide_eq_true_eq] at h3; exact h3

private def q2DotShift0 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 103854753 else 100804200) else (if b0 then 99618059 else 94541562)) else (if b1 then (if b0 then 102830333 else 98561048) else (if b0 then 102955020 else 99522031))) else (if b2 then (if b1 then (if b0 then 98313903 else 100233326) else (if b0 then 93479827 else 100525918)) else (if b1 then (if b0 then 100009048 else 98496106) else (if b0 then 104020412 else 100475044)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98911217 else 94775064) else (if b0 then 92895372 else 97533902)) else (if b1 then (if b0 then 98560389 else 103415049) else (if b0 then 99912399 else 100200855))) else (if b2 then (if b1 then (if b0 then 101093054 else 98153499) else (if b0 then 100221678 else 103286879)) else (if b1 then (if b0 then 99491079 else 102453509) else (if b0 then 101207326 else 101923420))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100804200 else 102578127) else (if b0 then 99029266 else 101327725)) else (if b1 then (if b0 then 102988137 else 102727182) else (if b0 then 101857996 else 101049531))) else (if b2 then (if b1 then (if b0 then 98258590 else 99787185) else (if b0 then 95655193 else 100494985)) else (if b1 then (if b0 then 100023578 else 97758805) else (if b0 then 100843193 else 101834425)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100494053 else 103187295) else (if b0 then 101743929 else 101292381)) else (if b1 then (if b0 then 96956080 else 98981462) else (if b0 then 101477481 else 96416128))) else (if b2 then (if b1 then (if b0 then 101233890 else 101006010) else (if b0 then 97319102 else 101168180)) else (if b1 then (if b0 then 99012996 else 98608229) else (if b0 then 99951824 else 99784274)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99618059 else 99029266) else (if b0 then 101309928 else 99862919)) else (if b1 then (if b0 then 99825579 else 97867585) else (if b0 then 100154789 else 98855052))) else (if b2 then (if b1 then (if b0 then 100053073 else 99203770) else (if b0 then 103007735 else 100013015)) else (if b1 then (if b0 then 99931299 else 101136862) else (if b0 then 99497570 else 100052322)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99561845 else 101685870) else (if b0 then 100484809 else 99880480)) else (if b1 then (if b0 then 101973053 else 100125559) else (if b0 then 99382650 else 100649946))) else (if b2 then (if b1 then (if b0 then 98458277 else 100158012) else (if b0 then 99103527 else 98280804)) else (if b1 then (if b0 then 100075203 else 99752649) else (if b0 then 98364942 else 99879244))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 94541562 else 101327725) else (if b0 then 99862919 else 116205765)) else (if b1 then (if b0 then 95995926 else 103638969) else (if b0 then 95179458 else 101216715))) else (if b2 then (if b1 then (if b0 then 102259918 else 97360071) else (if b0 then 107778703 else 100966467)) else (if b1 then (if b0 then 99624979 else 105726243) else (if b0 then 94062898 else 101099399)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103966523 else 108168166) else (if b0 then 113700357 else 102793509)) else (if b1 then (if b0 then 95927487 else 92311726) else (if b0 then 102414621 else 96888158))) else (if b2 then (if b1 then (if b0 then 106654125 else 106057622) else (if b0 then 100875341 else 93887686)) else (if b1 then (if b0 then 98830478 else 92430597) else (if b0 then 97319624 else 97219259)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 102830333 else 102988137) else (if b0 then 99825579 else 95995926)) else (if b1 then (if b0 then 109423107 else 97547401) else (if b0 then 103547376 else 99072417))) else (if b2 then (if b1 then (if b0 then 93518102 else 98839829) else (if b0 then 98369566 else 97122701)) else (if b1 then (if b0 then 100246028 else 94878970) else (if b0 then 99126848 else 107027916)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98585684 else 105742555) else (if b0 then 95972016 else 99714871)) else (if b1 then (if b0 then 96760539 else 101456032) else (if b0 then 99984393 else 96414031))) else (if b2 then (if b1 then (if b0 then 98883965 else 98151416) else (if b0 then 93273042 else 102466752)) else (if b1 then (if b0 then 98973948 else 100199478) else (if b0 then 97149810 else 100009542))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98561048 else 102727182) else (if b0 then 97867585 else 103638969)) else (if b1 then (if b0 then 97547401 else 116015659) else (if b0 then 101099230 else 106086270))) else (if b2 then (if b1 then (if b0 then 102788960 else 100835916) else (if b0 then 88252351 else 104068193)) else (if b1 then (if b0 then 99561529 else 93818922) else (if b0 then 103878806 else 97265214)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103165995 else 104047351) else (if b0 then 108957149 else 103192219)) else (if b1 then (if b0 then 102122157 else 97415300) else (if b0 then 102458884 else 90393616))) else (if b2 then (if b1 then (if b0 then 95171867 else 102090955) else (if b0 then 96288287 else 100144174)) else (if b1 then (if b0 then 99074182 else 99520088) else (if b0 then 104361685 else 97835247)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 102955020 else 101857996) else (if b0 then 100154789 else 95179458)) else (if b1 then (if b0 then 103547376 else 101099230) else (if b0 then 108634729 else 98903261))) else (if b2 then (if b1 then (if b0 then 98406590 else 99575201) else (if b0 then 91109677 else 102501289)) else (if b1 then (if b0 then 99992835 else 96800323) else (if b0 then 106073868 else 97943336)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97521234 else 102413126) else (if b0 then 98782732 else 101938442)) else (if b1 then (if b0 then 102060845 else 101814222) else (if b0 then 102857554 else 97223353))) else (if b2 then (if b1 then (if b0 then 96101883 else 99179767) else (if b0 then 95773851 else 102385967)) else (if b1 then (if b0 then 99822229 else 99688373) else (if b0 then 100205737 else 101265823))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99522031 else 101049531) else (if b0 then 98855052 else 101216715)) else (if b1 then (if b0 then 99072417 else 106086270) else (if b0 then 98903261 else 103296623))) else (if b2 then (if b1 then (if b0 then 100976269 else 101034238) else (if b0 then 95753194 else 100757601)) else (if b1 then (if b0 then 99928060 else 97208126) else (if b0 then 101127131 else 98545889)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102550801 else 100375802) else (if b0 then 102056695 else 100582419)) else (if b1 then (if b0 then 100314576 else 99237766) else (if b0 then 100618553 else 95865092))) else (if b2 then (if b1 then (if b0 then 98959787 else 100467494) else (if b0 then 99374623 else 101644098)) else (if b1 then (if b0 then 99110048 else 99920015) else (if b0 then 102304006 else 99130817)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98313903 else 98258590) else (if b0 then 100053073 else 102259918)) else (if b1 then (if b0 then 93518102 else 102788960) else (if b0 then 98406590 else 100976269))) else (if b2 then (if b1 then (if b0 then 104734767 else 101239274) else (if b0 then 98931618 else 102891963)) else (if b1 then (if b0 then 99844883 else 102908662) else (if b0 then 101825232 else 94530948)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100810248 else 96477877) else (if b0 then 103603348 else 100996450)) else (if b1 then (if b0 then 102337013 else 98934744) else (if b0 then 100223096 else 101937713))) else (if b2 then (if b1 then (if b0 then 100155684 else 101762761) else (if b0 then 104012858 else 98474915)) else (if b1 then (if b0 then 100608193 else 99954199) else (if b0 then 102385217 else 100137338))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100233326 else 99787185) else (if b0 then 99203770 else 97360071)) else (if b1 then (if b0 then 98839829 else 100835916) else (if b0 then 99575201 else 101034238))) else (if b2 then (if b1 then (if b0 then 101239274 else 102983177) else (if b0 then 96637381 else 100753732)) else (if b1 then (if b0 then 100348311 else 98932943) else (if b0 then 101650583 else 97530933)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99644005 else 97727091) else (if b0 then 99869599 else 101809774)) else (if b1 then (if b0 then 99441509 else 100235253) else (if b0 then 99463807 else 101795431))) else (if b2 then (if b1 then (if b0 then 99745644 else 100390450) else (if b0 then 101398424 else 102080521)) else (if b1 then (if b0 then 100380570 else 101347545) else (if b0 then 102285412 else 100683969)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 93479827 else 95655193) else (if b0 then 103007735 else 107778703)) else (if b1 then (if b0 then 98369566 else 88252351) else (if b0 then 91109677 else 95753194))) else (if b2 then (if b1 then (if b0 then 98931618 else 96637381) else (if b0 then 127935780 else 92413446)) else (if b1 then (if b0 then 100122224 else 107215290) else (if b0 then 85481521 else 105113884)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100597784 else 107250718) else (if b0 then 103009461 else 98581161)) else (if b1 then (if b0 then 102303044 else 96592152) else (if b0 then 96917898 else 105982136))) else (if b2 then (if b1 then (if b0 then 100811887 else 99380725) else (if b0 then 101605958 else 92929391)) else (if b1 then (if b0 then 101503590 else 96344334) else (if b0 then 92359248 else 96963715))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100525918 else 100494985) else (if b0 then 100013015 else 100966467)) else (if b1 then (if b0 then 97122701 else 104068193) else (if b0 then 102501289 else 100757601))) else (if b2 then (if b1 then (if b0 then 102891963 else 100753732) else (if b0 then 92413446 else 104854070)) else (if b1 then (if b0 then 99797406 else 100987869) else (if b0 then 105015187 else 96306614)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99668711 else 99108578) else (if b0 then 104186805 else 102106492)) else (if b1 then (if b0 then 100210411 else 99212236) else (if b0 then 101202113 else 99343329))) else (if b2 then (if b1 then (if b0 then 100195818 else 102897061) else (if b0 then 100354901 else 98817460)) else (if b1 then (if b0 then 99742974 else 99668620) else (if b0 then 101762535 else 100848093)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100009048 else 100023578) else (if b0 then 99931299 else 99624979)) else (if b1 then (if b0 then 100246028 else 99561529) else (if b0 then 99992835 else 99928060))) else (if b2 then (if b1 then (if b0 then 99844883 else 100348311) else (if b0 then 100122224 else 99797406)) else (if b1 then (if b0 then 100082980 else 99863880) else (if b0 then 99865231 else 99996335)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99828959 else 100135897) else (if b0 then 99894397 else 100335820)) else (if b1 then (if b0 then 99729967 else 99978010) else (if b0 then 99927064 else 100370913))) else (if b2 then (if b1 then (if b0 then 100046900 else 99991648) else (if b0 then 99993397 else 100315972)) else (if b1 then (if b0 then 100065890 else 100020829) else (if b0 then 100004230 else 100071567))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98496106 else 97758805) else (if b0 then 101136862 else 105726243)) else (if b1 then (if b0 then 94878970 else 93818922) else (if b0 then 96800323 else 97208126))) else (if b2 then (if b1 then (if b0 then 102908662 else 98932943) else (if b0 then 107215290 else 100987869)) else (if b1 then (if b0 then 99863880 else 109033439) else (if b0 then 98000043 else 98262677)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99892838 else 95546556) else (if b0 then 101287739 else 98762568)) else (if b1 then (if b0 then 97727571 else 98397014) else (if b0 then 99714884 else 106550927))) else (if b2 then (if b1 then (if b0 then 107402244 else 102522280) else (if b0 then 106636060 else 96227857)) else (if b1 then (if b0 then 100473736 else 97853203) else (if b0 then 98515573 else 100999295)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 104020412 else 100843193) else (if b0 then 99497570 else 94062898)) else (if b1 then (if b0 then 99126848 else 103878806) else (if b0 then 106073868 else 101127131))) else (if b2 then (if b1 then (if b0 then 101825232 else 101650583) else (if b0 then 85481521 else 105015187)) else (if b1 then (if b0 then 99865231 else 98000043) else (if b0 then 109793212 else 94030111)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99308069 else 93795896) else (if b0 then 96439306 else 99983016)) else (if b1 then (if b0 then 101779290 else 103176487) else (if b0 then 101770670 else 98449850))) else (if b2 then (if b1 then (if b0 then 98485132 else 99796283) else (if b0 then 100559404 else 103918152)) else (if b1 then (if b0 then 99326924 else 102164267) else (if b0 then 104098028 else 102476746))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100475044 else 101834425) else (if b0 then 100052322 else 101099399)) else (if b1 then (if b0 then 107027916 else 97265214) else (if b0 then 97943336 else 98545889))) else (if b2 then (if b1 then (if b0 then 94530948 else 97530933) else (if b0 then 105113884 else 96306614)) else (if b1 then (if b0 then 99996335 else 98262677) else (if b0 then 94030111 else 111571133)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98460492 else 105368716) else (if b0 then 99271211 else 98375989)) else (if b1 then (if b0 then 94215844 else 99434645) else (if b0 then 97544932 else 99231166))) else (if b2 then (if b1 then (if b0 then 102048588 else 99710844) else (if b0 then 95297314 else 96966544)) else (if b1 then (if b0 then 99869656 else 100772477) else (if b0 then 95680513 else 98917418)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98911217 else 100494053) else (if b0 then 99561845 else 103966523)) else (if b1 then (if b0 then 98585684 else 103165995) else (if b0 then 97521234 else 102550801))) else (if b2 then (if b1 then (if b0 then 100810248 else 99644005) else (if b0 then 100597784 else 99668711)) else (if b1 then (if b0 then 99828959 else 99892838) else (if b0 then 99308069 else 98460492)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103950454 else 100405122) else (if b0 then 101339553 else 99052288)) else (if b1 then (if b0 then 100316881 else 98826333) else (if b0 then 100931674 else 96049411))) else (if b2 then (if b1 then (if b0 then 101216285 else 100494887) else (if b0 then 100696270 else 101194374)) else (if b1 then (if b0 then 98483084 else 98063258) else (if b0 then 100793690 else 98934330))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 94775064 else 103187295) else (if b0 then 101685870 else 108168166)) else (if b1 then (if b0 then 105742555 else 104047351) else (if b0 then 102413126 else 100375802))) else (if b2 then (if b1 then (if b0 then 96477877 else 97727091) else (if b0 then 107250718 else 99108578)) else (if b1 then (if b0 then 100135897 else 95546556) else (if b0 then 93795896 else 105368716)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100405122 else 125935390) else (if b0 then 117618230 else 109108071)) else (if b1 then (if b0 then 101766302 else 92608860) else (if b0 then 101994773 else 90905464))) else (if b2 then (if b1 then (if b0 then 92037527 else 104679727) else (if b0 then 86132094 else 94015939)) else (if b1 then (if b0 then 99048009 else 92597885) else (if b0 then 92903509 else 95366678)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 92895372 else 101743929) else (if b0 then 100484809 else 113700357)) else (if b1 then (if b0 then 95972016 else 108957149) else (if b0 then 98782732 else 102056695))) else (if b2 then (if b1 then (if b0 then 103603348 else 99869599) else (if b0 then 103009461 else 104186805)) else (if b1 then (if b0 then 99894397 else 101287739) else (if b0 then 96439306 else 99271211)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101339553 else 117618230) else (if b0 then 123228625 else 110211371)) else (if b1 then (if b0 then 99843507 else 90217710) else (if b0 then 102290299 else 95196446))) else (if b2 then (if b1 then (if b0 then 97744961 else 108736188) else (if b0 then 94375877 else 91417742)) else (if b1 then (if b0 then 99921276 else 92756543) else (if b0 then 97379240 else 96223701))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 97533902 else 101292381) else (if b0 then 99880480 else 102793509)) else (if b1 then (if b0 then 99714871 else 103192219) else (if b0 then 101938442 else 100582419))) else (if b2 then (if b1 then (if b0 then 100996450 else 101809774) else (if b0 then 98581161 else 102106492)) else (if b1 then (if b0 then 100335820 else 98762568) else (if b0 then 99983016 else 98375989)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99052288 else 109108071) else (if b0 then 110211371 else 107120004)) else (if b1 then (if b0 then 99803905 else 95961624) else (if b0 then 101482870 else 98757248))) else (if b2 then (if b1 then (if b0 then 97413624 else 103798769) else (if b0 then 96285280 else 98229660)) else (if b1 then (if b0 then 100362075 else 97014454) else (if b0 then 99385142 else 98966287)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98560389 else 96956080) else (if b0 then 101973053 else 95927487)) else (if b1 then (if b0 then 96760539 else 102122157) else (if b0 then 102060845 else 100314576))) else (if b2 then (if b1 then (if b0 then 102337013 else 99441509) else (if b0 then 102303044 else 100210411)) else (if b1 then (if b0 then 99729967 else 97727571) else (if b0 then 101779290 else 94215844)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100316881 else 101766302) else (if b0 then 99843507 else 99803905)) else (if b1 then (if b0 then 112009127 else 102033606) else (if b0 then 100049868 else 97915816))) else (if b2 then (if b1 then (if b0 then 88798508 else 96949921) else (if b0 then 97945188 else 99588260)) else (if b1 then (if b0 then 100899486 else 101246320) else (if b0 then 100472359 else 98842750))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 103415049 else 98981462) else (if b0 then 100125559 else 92311726)) else (if b1 then (if b0 then 101456032 else 97415300) else (if b0 then 101814222 else 99237766))) else (if b2 then (if b1 then (if b0 then 98934744 else 100235253) else (if b0 then 96592152 else 99212236)) else (if b1 then (if b0 then 99978010 else 98397014) else (if b0 then 103176487 else 99434645)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98826333 else 92608860) else (if b0 then 90217710 else 95961624)) else (if b1 then (if b0 then 102033606 else 104873402) else (if b0 then 98850993 else 101574617))) else (if b2 then (if b1 then (if b0 then 98412029 else 96040666) else (if b0 then 101359446 else 103415936)) else (if b1 then (if b0 then 100243667 else 104060936) else (if b0 then 101545753 else 101722187)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99912399 else 101477481) else (if b0 then 99382650 else 102414621)) else (if b1 then (if b0 then 99984393 else 102458884) else (if b0 then 102857554 else 100618553))) else (if b2 then (if b1 then (if b0 then 100223096 else 99463807) else (if b0 then 96917898 else 101202113)) else (if b1 then (if b0 then 99927064 else 99714884) else (if b0 then 101770670 else 97544932)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100931674 else 101994773) else (if b0 then 102290299 else 101482870)) else (if b1 then (if b0 then 100049868 else 98850993) else (if b0 then 103013144 else 97057315))) else (if b2 then (if b1 then (if b0 then 100532664 else 100679085) else (if b0 then 99418693 else 101363766)) else (if b1 then (if b0 then 99365908 else 97253834) else (if b0 then 100552860 else 99865267))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100200855 else 96416128) else (if b0 then 100649946 else 96888158)) else (if b1 then (if b0 then 96414031 else 90393616) else (if b0 then 97223353 else 95865092))) else (if b2 then (if b1 then (if b0 then 101937713 else 101795431) else (if b0 then 105982136 else 99343329)) else (if b1 then (if b0 then 100370913 else 106550927) else (if b0 then 98449850 else 99231166)))) else (if b3 then (if b2 then (if b1 then (if b0 then 96049411 else 90905464) else (if b0 then 95196446 else 98757248)) else (if b1 then (if b0 then 97915816 else 101574617) else (if b0 then 97057315 else 112155614))) else (if b2 then (if b1 then (if b0 then 104754675 else 99607230) else (if b0 then 107538737 else 98395602)) else (if b1 then (if b0 then 102533856 else 102902396) else (if b0 then 100018025 else 102387299)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101093054 else 101233890) else (if b0 then 98458277 else 106654125)) else (if b1 then (if b0 then 98883965 else 95171867) else (if b0 then 96101883 else 98959787))) else (if b2 then (if b1 then (if b0 then 100155684 else 99745644) else (if b0 then 100811887 else 100195818)) else (if b1 then (if b0 then 100046900 else 107402244) else (if b0 then 98485132 else 102048588)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101216285 else 92037527) else (if b0 then 97744961 else 97413624)) else (if b1 then (if b0 then 88798508 else 98412029) else (if b0 then 100532664 else 104754675))) else (if b2 then (if b1 then (if b0 then 115212197 else 102885965) else (if b0 then 107789753 else 100412415)) else (if b1 then (if b0 then 98958370 else 97776288) else (if b0 then 100213363 else 101939720))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98153499 else 101006010) else (if b0 then 100158012 else 106057622)) else (if b1 then (if b0 then 98151416 else 102090955) else (if b0 then 99179767 else 100467494))) else (if b2 then (if b1 then (if b0 then 101762761 else 100390450) else (if b0 then 99380725 else 102897061)) else (if b1 then (if b0 then 99991648 else 102522280) else (if b0 then 99796283 else 99710844)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100494887 else 104679727) else (if b0 then 108736188 else 103798769)) else (if b1 then (if b0 then 96949921 else 96040666) else (if b0 then 100679085 else 99607230))) else (if b2 then (if b1 then (if b0 then 102885965 else 104969029) else (if b0 then 99388401 else 96599912)) else (if b1 then (if b0 then 99452737 else 96987213) else (if b0 then 99087094 else 99535974)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100221678 else 97319102) else (if b0 then 99103527 else 100875341)) else (if b1 then (if b0 then 93273042 else 96288287) else (if b0 then 95773851 else 99374623))) else (if b2 then (if b1 then (if b0 then 104012858 else 101398424) else (if b0 then 101605958 else 100354901)) else (if b1 then (if b0 then 99993397 else 106636060) else (if b0 then 100559404 else 95297314)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100696270 else 86132094) else (if b0 then 94375877 else 96285280)) else (if b1 then (if b0 then 97945188 else 101359446) else (if b0 then 99418693 else 107538737))) else (if b2 then (if b1 then (if b0 then 107789753 else 99388401) else (if b0 then 110949639 else 101441195)) else (if b1 then (if b0 then 100895088 else 101462848) else (if b0 then 103410670 else 102049920))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 103286879 else 101168180) else (if b0 then 98280804 else 93887686)) else (if b1 then (if b0 then 102466752 else 100144174) else (if b0 then 102385967 else 101644098))) else (if b2 then (if b1 then (if b0 then 98474915 else 102080521) else (if b0 then 92929391 else 98817460)) else (if b1 then (if b0 then 100315972 else 96227857) else (if b0 then 103918152 else 96966544)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101194374 else 94015939) else (if b0 then 91417742 else 98229660)) else (if b1 then (if b0 then 99588260 else 103415936) else (if b0 then 101363766 else 98395602))) else (if b2 then (if b1 then (if b0 then 100412415 else 96599912) else (if b0 then 101441195 else 108055580)) else (if b1 then (if b0 then 99067280 else 101507570) else (if b0 then 103460440 else 101505051)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99491079 else 99012996) else (if b0 then 100075203 else 98830478)) else (if b1 then (if b0 then 98973948 else 99074182) else (if b0 then 99822229 else 99110048))) else (if b2 then (if b1 then (if b0 then 100608193 else 100380570) else (if b0 then 101503590 else 99742974)) else (if b1 then (if b0 then 100065890 else 100473736) else (if b0 then 99326924 else 99869656)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98483084 else 99048009) else (if b0 then 99921276 else 100362075)) else (if b1 then (if b0 then 100899486 else 100243667) else (if b0 then 99365908 else 102533856))) else (if b2 then (if b1 then (if b0 then 98958370 else 99452737) else (if b0 then 100895088 else 99067280)) else (if b1 then (if b0 then 101184265 else 101071349) else (if b0 then 100156339 else 100096959))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 102453509 else 98608229) else (if b0 then 99752649 else 92430597)) else (if b1 then (if b0 then 100199478 else 99520088) else (if b0 then 99688373 else 99920015))) else (if b2 then (if b1 then (if b0 then 99954199 else 101347545) else (if b0 then 96344334 else 99668620)) else (if b1 then (if b0 then 100020829 else 97853203) else (if b0 then 102164267 else 100772477)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98063258 else 92597885) else (if b0 then 92756543 else 97014454)) else (if b1 then (if b0 then 101246320 else 104060936) else (if b0 then 97253834 else 102902396))) else (if b2 then (if b1 then (if b0 then 97776288 else 96987213) else (if b0 then 101462848 else 101507570)) else (if b1 then (if b0 then 101071349 else 105698502) else (if b0 then 102252830 else 101296993)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101207326 else 99951824) else (if b0 then 98364942 else 97319624)) else (if b1 then (if b0 then 97149810 else 104361685) else (if b0 then 100205737 else 102304006))) else (if b2 then (if b1 then (if b0 then 102385217 else 102285412) else (if b0 then 92359248 else 101762535)) else (if b1 then (if b0 then 100004230 else 98515573) else (if b0 then 104098028 else 95680513)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100793690 else 92903509) else (if b0 then 97379240 else 99385142)) else (if b1 then (if b0 then 100472359 else 101545753) else (if b0 then 100552860 else 100018025))) else (if b2 then (if b1 then (if b0 then 100213363 else 99087094) else (if b0 then 103410670 else 103460440)) else (if b1 then (if b0 then 100156339 else 102252830) else (if b0 then 104667376 else 100974065))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101923420 else 99784274) else (if b0 then 99879244 else 97219259)) else (if b1 then (if b0 then 100009542 else 97835247) else (if b0 then 101265823 else 99130817))) else (if b2 then (if b1 then (if b0 then 100137338 else 100683969) else (if b0 then 96963715 else 100848093)) else (if b1 then (if b0 then 100071567 else 100999295) else (if b0 then 102476746 else 98917418)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98934330 else 95366678) else (if b0 then 96223701 else 98966287)) else (if b1 then (if b0 then 98842750 else 101722187) else (if b0 then 99865267 else 102387299))) else (if b2 then (if b1 then (if b0 then 101939720 else 99535974) else (if b0 then 102049920 else 101505051)) else (if b1 then (if b0 then 100096959 else 101296993) else (if b0 then 100974065 else 101586082)))))))
private lemma checkQ2_0_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift0 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨0, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨0, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨0, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨0, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨0, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨0, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

private def q2DotShift1 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 109085215 else 96355420) else (if b0 then 99902291 else 97706932)) else (if b1 then (if b0 then 98314690 else 78758743) else (if b0 then 107564823 else 99244754))) else (if b2 then (if b1 then (if b0 then 109870665 else 101767664) else (if b0 then 101775874 else 97857305)) else (if b1 then (if b0 then 97390359 else 100909971) else (if b0 then 100322562 else 88664254)))) else (if b3 then (if b2 then (if b1 then (if b0 then 94408520 else 104247117) else (if b0 then 103678690 else 101072633)) else (if b1 then (if b0 then 94946874 else 90192015) else (if b0 then 99685850 else 99626527))) else (if b2 then (if b1 then (if b0 then 96465858 else 103880829) else (if b0 then 99286974 else 102734142)) else (if b1 then (if b0 then 99426756 else 98907032) else (if b0 then 100798826 else 97069623))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 96355420 else 107035664) else (if b0 then 101388902 else 101718730)) else (if b1 then (if b0 then 108169048 else 113317504) else (if b0 then 97192278 else 101774515))) else (if b2 then (if b1 then (if b0 then 94439409 else 101715739) else (if b0 then 97310736 else 99366650)) else (if b1 then (if b0 then 105752239 else 99057016) else (if b0 then 100358230 else 102004935)))) else (if b3 then (if b2 then (if b1 then (if b0 then 106128400 else 101346928) else (if b0 then 109637898 else 102799911)) else (if b1 then (if b0 then 98255600 else 91741233) else (if b0 then 99868262 else 100653781))) else (if b2 then (if b1 then (if b0 then 101660168 else 97459848) else (if b0 then 102259319 else 97083427)) else (if b1 then (if b0 then 99612680 else 103375288) else (if b0 then 101159339 else 101109820)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99902291 else 101388902) else (if b0 then 109264922 else 98888205)) else (if b1 then (if b0 then 101722562 else 102661265) else (if b0 then 97565368 else 99938799))) else (if b2 then (if b1 then (if b0 then 96348515 else 99555973) else (if b0 then 96053171 else 100222114)) else (if b1 then (if b0 then 97879099 else 98584056) else (if b0 then 99764205 else 97101502)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100543286 else 103281113) else (if b0 then 102656565 else 95111885)) else (if b1 then (if b0 then 97849695 else 100068031) else (if b0 then 101315547 else 100392407))) else (if b2 then (if b1 then (if b0 then 100790376 else 101974821) else (if b0 then 97876953 else 99192516)) else (if b1 then (if b0 then 99988796 else 101022430) else (if b0 then 100006056 else 100498766))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 97706932 else 101718730) else (if b0 then 98888205 else 106532395)) else (if b1 then (if b0 then 105360068 else 104242068) else (if b0 then 97864915 else 99286105))) else (if b2 then (if b1 then (if b0 then 94405372 else 96273913) else (if b0 then 98454977 else 95847211)) else (if b1 then (if b0 then 102131552 else 103294727) else (if b0 then 100829989 else 105054990)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100614414 else 97986176) else (if b0 then 99978767 else 102402894)) else (if b1 then (if b0 then 103691269 else 101386108) else (if b0 then 97662121 else 99155284))) else (if b2 then (if b1 then (if b0 then 101049336 else 98644426) else (if b0 then 102284095 else 98821684)) else (if b1 then (if b0 then 99160792 else 104013970) else (if b0 then 99499008 else 101334005)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98314690 else 108169048) else (if b0 then 101722562 else 105360068)) else (if b1 then (if b0 then 114153150 else 108438800) else (if b0 then 97250305 else 102038401))) else (if b2 then (if b1 then (if b0 then 90966502 else 100436352) else (if b0 then 97274459 else 94444096)) else (if b1 then (if b0 then 105811072 else 102307382) else (if b0 then 101630818 else 101993070)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104155091 else 101248567) else (if b0 then 113366848 else 106622524)) else (if b1 then (if b0 then 96034041 else 88006510) else (if b0 then 97852805 else 100055197))) else (if b2 then (if b1 then (if b0 then 102935395 else 96679241) else (if b0 then 103132973 else 95403267)) else (if b1 then (if b0 then 98128090 else 108993195) else (if b0 then 101158375 else 101347275))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 78758743 else 113317504) else (if b0 then 102661265 else 104242068)) else (if b1 then (if b0 then 108438800 else 159516762) else (if b0 then 83035982 else 102467295))) else (if b2 then (if b1 then (if b0 then 78414948 else 100703629) else (if b0 then 92784433 else 105525135)) else (if b1 then (if b0 then 111982503 else 93504552) else (if b0 then 96189601 else 121399940)))) else (if b3 then (if b2 then (if b1 then (if b0 then 115232445 else 91084898) else (if b0 then 103429519 else 98863747)) else (if b1 then (if b0 then 108603834 else 109680066) else (if b0 then 105330476 else 97973950))) else (if b2 then (if b1 then (if b0 then 107731532 else 91854585) else (if b0 then 105069134 else 92416499)) else (if b1 then (if b0 then 100379070 else 101959999) else (if b0 then 98238002 else 109596306)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 107564823 else 97192278) else (if b0 then 97565368 else 97864915)) else (if b1 then (if b0 then 97250305 else 83035982) else (if b0 then 109916447 else 98007772))) else (if b2 then (if b1 then (if b0 then 110878183 else 101341105) else (if b0 then 102409850 else 99258255)) else (if b1 then (if b0 then 99510350 else 100606073) else (if b0 then 99694812 else 89196488)))) else (if b3 then (if b2 then (if b1 then (if b0 then 94261096 else 102379438) else (if b0 then 102732215 else 98943797)) else (if b1 then (if b0 then 95228287 else 90287627) else (if b0 then 98444202 else 99451551))) else (if b2 then (if b1 then (if b0 then 96571422 else 105812189) else (if b0 then 100392572 else 103623571)) else (if b1 then (if b0 then 102146755 else 97319815) else (if b0 then 101817091 else 98641142))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99244754 else 101774515) else (if b0 then 99938799 else 99286105)) else (if b1 then (if b0 then 102038401 else 102467295) else (if b0 then 98007772 else 103738086))) else (if b2 then (if b1 then (if b0 then 99857560 else 100615985) else (if b0 then 99409412 else 103228727)) else (if b1 then (if b0 then 101796749 else 98540227) else (if b0 then 103788946 else 101194991)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102245061 else 103995865) else (if b0 then 103316113 else 104678723)) else (if b1 then (if b0 then 100373882 else 96532329) else (if b0 then 100191189 else 98982778))) else (if b2 then (if b1 then (if b0 then 98760098 else 96015594) else (if b0 then 96010788 else 99733744)) else (if b1 then (if b0 then 99286190 else 99911136) else (if b0 then 100618649 else 98118779)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 109870665 else 94439409) else (if b0 then 96348515 else 94405372)) else (if b1 then (if b0 then 90966502 else 78414948) else (if b0 then 110878183 else 99857560))) else (if b2 then (if b1 then (if b0 then 123442381 else 103993622) else (if b0 then 100284339 else 104712106)) else (if b1 then (if b0 then 101061778 else 95916916) else (if b0 then 100411484 else 83423347)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99076323 else 110425045) else (if b0 then 103798085 else 100834714)) else (if b1 then (if b0 then 101744316 else 84062875) else (if b0 then 102855014 else 99214226))) else (if b2 then (if b1 then (if b0 then 88636167 else 104289124) else (if b0 then 98596670 else 108218397)) else (if b1 then (if b0 then 99622193 else 87583977) else (if b0 then 101284464 else 92943581))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101767664 else 101715739) else (if b0 then 99555973 else 96273913)) else (if b1 then (if b0 then 100436352 else 100703629) else (if b0 then 101341105 else 100615985))) else (if b2 then (if b1 then (if b0 then 103993622 else 105765693) else (if b0 then 100288534 else 100227852)) else (if b1 then (if b0 then 102186167 else 97011710) else (if b0 then 97031347 else 95052589)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102412607 else 100853688) else (if b0 then 107297946 else 101615715)) else (if b1 then (if b0 then 96067501 else 90754054) else (if b0 then 103595291 else 100516821))) else (if b2 then (if b1 then (if b0 then 99486049 else 99940647) else (if b0 then 103110771 else 99207335)) else (if b1 then (if b0 then 98392281 else 98667053) else (if b0 then 100011312 else 99739281)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101775874 else 97310736) else (if b0 then 96053171 else 98454977)) else (if b1 then (if b0 then 97274459 else 92784433) else (if b0 then 102409850 else 99409412))) else (if b2 then (if b1 then (if b0 then 100284339 else 100288534) else (if b0 then 104805491 else 99210412)) else (if b1 then (if b0 then 96987024 else 101940559) else (if b0 then 99794165 else 101048240)))) else (if b3 then (if b2 then (if b1 then (if b0 then 95071864 else 95620099) else (if b0 then 95338777 else 100503798)) else (if b1 then (if b0 then 96466597 else 104602442) else (if b0 then 98342038 else 100208471))) else (if b2 then (if b1 then (if b0 then 102278364 else 100536718) else (if b0 then 99593077 else 99545333)) else (if b1 then (if b0 then 101186501 else 101633625) else (if b0 then 100039146 else 100874279))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 97857305 else 99366650) else (if b0 then 100222114 else 95847211)) else (if b1 then (if b0 then 94444096 else 105525135) else (if b0 then 99258255 else 103228727))) else (if b2 then (if b1 then (if b0 then 104712106 else 100227852) else (if b0 then 99210412 else 109565728)) else (if b1 then (if b0 then 101072268 else 95205942) else (if b0 then 103643149 else 100393535)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101850505 else 104764900) else (if b0 then 97488417 else 99472936)) else (if b1 then (if b0 then 103483562 else 101815728) else (if b0 then 101583264 else 98201679))) else (if b2 then (if b1 then (if b0 then 96480337 else 98186240) else (if b0 then 92971141 else 102847514)) else (if b1 then (if b0 then 102090538 else 92980649) else (if b0 then 100882830 else 98110069)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 97390359 else 105752239) else (if b0 then 97879099 else 102131552)) else (if b1 then (if b0 then 105811072 else 111982503) else (if b0 then 99510350 else 101796749))) else (if b2 then (if b1 then (if b0 then 101061778 else 102186167) else (if b0 then 96987024 else 101072268)) else (if b1 then (if b0 then 108366846 else 97581315) else (if b0 then 100277981 else 99941521)))) else (if b3 then (if b2 then (if b1 then (if b0 then 106452564 else 102774418) else (if b0 then 110022296 else 104777114)) else (if b1 then (if b0 then 102164798 else 87835570) else (if b0 then 101304458 else 98715935))) else (if b2 then (if b1 then (if b0 then 97835741 else 97552930) else (if b0 then 102945704 else 99668612)) else (if b1 then (if b0 then 99163813 else 98978664) else (if b0 then 100920962 else 100080148))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100909971 else 99057016) else (if b0 then 98584056 else 103294727)) else (if b1 then (if b0 then 102307382 else 93504552) else (if b0 then 100606073 else 98540227))) else (if b2 then (if b1 then (if b0 then 95916916 else 97011710) else (if b0 then 101940559 else 95205942)) else (if b1 then (if b0 then 97581315 else 104820296) else (if b0 then 100799157 else 102541847)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97164059 else 97214292) else (if b0 then 96819108 else 100410784)) else (if b1 then (if b0 then 98758511 else 104042367) else (if b0 then 95947659 else 101449300))) else (if b2 then (if b1 then (if b0 then 102412280 else 100455731) else (if b0 then 100992005 else 98917140)) else (if b1 then (if b0 then 100299854 else 104916229) else (if b0 then 100138824 else 100286697)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100322562 else 100358230) else (if b0 then 99764205 else 100829989)) else (if b1 then (if b0 then 101630818 else 96189601) else (if b0 then 99694812 else 103788946))) else (if b2 then (if b1 then (if b0 then 100411484 else 97031347) else (if b0 then 99794165 else 103643149)) else (if b1 then (if b0 then 100277981 else 100799157) else (if b0 then 107314989 else 101336254)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100163921 else 106222919) else (if b0 then 100091584 else 104242254)) else (if b1 then (if b0 then 101429951 else 98739073) else (if b0 then 96506531 else 99216278))) else (if b2 then (if b1 then (if b0 then 97595878 else 96725416) else (if b0 then 92572158 else 101417301)) else (if b1 then (if b0 then 101023854 else 100134941) else (if b0 then 101732829 else 96514216))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 88664254 else 102004935) else (if b0 then 97101502 else 105054990)) else (if b1 then (if b0 then 101993070 else 121399940) else (if b0 then 89196488 else 101194991))) else (if b2 then (if b1 then (if b0 then 83423347 else 95052589) else (if b0 then 101048240 else 100393535)) else (if b1 then (if b0 then 99941521 else 102541847) else (if b0 then 101336254 else 119743276)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102748279 else 90536708) else (if b0 then 88945296 else 101363794)) else (if b1 then (if b0 then 106533365 else 120766246) else (if b0 then 97894467 else 99942707))) else (if b2 then (if b1 then (if b0 then 107022874 else 93053758) else (if b0 then 99368771 else 95316226)) else (if b1 then (if b0 then 100340429 else 105366975) else (if b0 then 98111363 else 104251210)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 94408520 else 106128400) else (if b0 then 100543286 else 100614414)) else (if b1 then (if b0 then 104155091 else 115232445) else (if b0 then 94261096 else 102245061))) else (if b2 then (if b1 then (if b0 then 99076323 else 102412607) else (if b0 then 95071864 else 101850505)) else (if b1 then (if b0 then 106452564 else 97164059) else (if b0 then 100163921 else 102748279)))) else (if b3 then (if b2 then (if b1 then (if b0 then 114791773 else 106240604) else (if b0 then 107343538 else 102335969)) else (if b1 then (if b0 then 105894727 else 92797885) else (if b0 then 101697694 else 104454742))) else (if b2 then (if b1 then (if b0 then 97394405 else 94802835) else (if b0 then 103192205 else 99242843)) else (if b1 then (if b0 then 97285703 else 97265058) else (if b0 then 100558693 else 95989439))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 104247117 else 101346928) else (if b0 then 103281113 else 97986176)) else (if b1 then (if b0 then 101248567 else 91084898) else (if b0 then 102379438 else 103995865))) else (if b2 then (if b1 then (if b0 then 110425045 else 100853688) else (if b0 then 95620099 else 104764900)) else (if b1 then (if b0 then 102774418 else 97214292) else (if b0 then 106222919 else 90536708)))) else (if b3 then (if b2 then (if b1 then (if b0 then 106240604 else 115770740) else (if b0 then 109221188 else 103481611)) else (if b1 then (if b0 then 102149080 else 84215339) else (if b0 then 99712577 else 101282391))) else (if b2 then (if b1 then (if b0 then 91298136 else 98484211) else (if b0 then 94179401 else 104373365)) else (if b1 then (if b0 then 98859813 else 94294965) else (if b0 then 102542379 else 91610933)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 103678690 else 109637898) else (if b0 then 102656565 else 99978767)) else (if b1 then (if b0 then 113366848 else 103429519) else (if b0 then 102732215 else 103316113))) else (if b2 then (if b1 then (if b0 then 103798085 else 107297946) else (if b0 then 95338777 else 97488417)) else (if b1 then (if b0 then 110022296 else 96819108) else (if b0 then 100091584 else 88945296)))) else (if b3 then (if b2 then (if b1 then (if b0 then 107343538 else 109221188) else (if b0 then 125780460 else 108221722)) else (if b1 then (if b0 then 92703614 else 68627387) else (if b0 then 102459952 else 99580708))) else (if b2 then (if b1 then (if b0 then 96997013 else 98684955) else (if b0 then 104380984 else 98129874)) else (if b1 then (if b0 then 96850824 else 102681204) else (if b0 then 102423719 else 98183359))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101072633 else 102799911) else (if b0 then 95111885 else 102402894)) else (if b1 then (if b0 then 106622524 else 98863747) else (if b0 then 98943797 else 104678723))) else (if b2 then (if b1 then (if b0 then 100834714 else 101615715) else (if b0 then 100503798 else 99472936)) else (if b1 then (if b0 then 104777114 else 100410784) else (if b0 then 104242254 else 101363794)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102335969 else 103481611) else (if b0 then 108221722 else 112108227)) else (if b1 then (if b0 then 100376549 else 89242505) else (if b0 then 99827927 else 97802574))) else (if b2 then (if b1 then (if b0 then 98132742 else 93397985) else (if b0 then 98946753 else 98824522)) else (if b1 then (if b0 then 96686953 else 102756413) else (if b0 then 100275005 else 97524495)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 94946874 else 98255600) else (if b0 then 97849695 else 103691269)) else (if b1 then (if b0 then 96034041 else 108603834) else (if b0 then 95228287 else 100373882))) else (if b2 then (if b1 then (if b0 then 101744316 else 96067501) else (if b0 then 96466597 else 103483562)) else (if b1 then (if b0 then 102164798 else 98758511) else (if b0 then 101429951 else 106533365)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105894727 else 102149080) else (if b0 then 92703614 else 100376549)) else (if b1 then (if b0 then 113930601 else 107662342) else (if b0 then 101323248 else 99331832))) else (if b2 then (if b1 then (if b0 then 95420588 else 96579272) else (if b0 then 99244405 else 102975859)) else (if b1 then (if b0 then 98468155 else 93645740) else (if b0 then 98338060 else 97566556))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 90192015 else 91741233) else (if b0 then 100068031 else 101386108)) else (if b1 then (if b0 then 88006510 else 109680066) else (if b0 then 90287627 else 96532329))) else (if b2 then (if b1 then (if b0 then 84062875 else 90754054) else (if b0 then 104602442 else 101815728)) else (if b1 then (if b0 then 87835570 else 104042367) else (if b0 then 98739073 else 120766246)))) else (if b3 then (if b2 then (if b1 then (if b0 then 92797885 else 84215339) else (if b0 then 68627387 else 89242505)) else (if b1 then (if b0 then 107662342 else 144632068) else (if b0 then 97621300 else 100602494))) else (if b2 then (if b1 then (if b0 then 109147771 else 99197658) else (if b0 then 95538296 else 97858874)) else (if b1 then (if b0 then 103409741 else 101917109) else (if b0 then 96094740 else 105961941)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99685850 else 99868262) else (if b0 then 101315547 else 97662121)) else (if b1 then (if b0 then 97852805 else 105330476) else (if b0 then 98444202 else 100191189))) else (if b2 then (if b1 then (if b0 then 102855014 else 103595291) else (if b0 then 98342038 else 101583264)) else (if b1 then (if b0 then 101304458 else 95947659) else (if b0 then 96506531 else 97894467)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101697694 else 99712577) else (if b0 then 102459952 else 99827927)) else (if b1 then (if b0 then 101323248 else 97621300) else (if b0 then 105658369 else 98264665))) else (if b2 then (if b1 then (if b0 then 98807303 else 99731763) else (if b0 then 102050736 else 99972278)) else (if b1 then (if b0 then 97751069 else 96578013) else (if b0 then 98296497 else 100925991))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99626527 else 100653781) else (if b0 then 100392407 else 99155284)) else (if b1 then (if b0 then 100055197 else 97973950) else (if b0 then 99451551 else 98982778))) else (if b2 then (if b1 then (if b0 then 99214226 else 100516821) else (if b0 then 100208471 else 98201679)) else (if b1 then (if b0 then 98715935 else 101449300) else (if b0 then 99216278 else 99942707)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104454742 else 101282391) else (if b0 then 99580708 else 97802574)) else (if b1 then (if b0 then 99331832 else 100602494) else (if b0 then 98264665 else 105239709))) else (if b2 then (if b1 then (if b0 then 100585081 else 100054136) else (if b0 then 102153781 else 99515967)) else (if b1 then (if b0 then 99771692 else 100516795) else (if b0 then 100712413 else 97487168)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 96465858 else 101660168) else (if b0 then 100790376 else 101049336)) else (if b1 then (if b0 then 102935395 else 107731532) else (if b0 then 96571422 else 98760098))) else (if b2 then (if b1 then (if b0 then 88636167 else 99486049) else (if b0 then 102278364 else 96480337)) else (if b1 then (if b0 then 97835741 else 102412280) else (if b0 then 97595878 else 107022874)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97394405 else 91298136) else (if b0 then 96997013 else 98132742)) else (if b1 then (if b0 then 95420588 else 109147771) else (if b0 then 98807303 else 100585081))) else (if b2 then (if b1 then (if b0 then 107611046 else 99748680) else (if b0 then 102234635 else 95234870)) else (if b1 then (if b0 then 100905235 else 107096460) else (if b0 then 99220493 else 105171921))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 103880829 else 97459848) else (if b0 then 101974821 else 98644426)) else (if b1 then (if b0 then 96679241 else 91854585) else (if b0 then 105812189 else 96015594))) else (if b2 then (if b1 then (if b0 then 104289124 else 99940647) else (if b0 then 100536718 else 98186240)) else (if b1 then (if b0 then 97552930 else 100455731) else (if b0 then 96725416 else 93053758)))) else (if b3 then (if b2 then (if b1 then (if b0 then 94802835 else 98484211) else (if b0 then 98684955 else 93397985)) else (if b1 then (if b0 then 96579272 else 99197658) else (if b0 then 99731763 else 100054136))) else (if b2 then (if b1 then (if b0 then 99748680 else 107057097) else (if b0 then 102015849 else 101905540)) else (if b1 then (if b0 then 102305283 else 98505022) else (if b0 then 100431525 else 101660712)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99286974 else 102259319) else (if b0 then 97876953 else 102284095)) else (if b1 then (if b0 then 103132973 else 105069134) else (if b0 then 100392572 else 96010788))) else (if b2 then (if b1 then (if b0 then 98596670 else 103110771) else (if b0 then 99593077 else 92971141)) else (if b1 then (if b0 then 102945704 else 100992005) else (if b0 then 92572158 else 99368771)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103192205 else 94179401) else (if b0 then 104380984 else 98946753)) else (if b1 then (if b0 then 99244405 else 95538296) else (if b0 then 102050736 else 102153781))) else (if b2 then (if b1 then (if b0 then 102234635 else 102015849) else (if b0 then 111139578 else 97713284)) else (if b1 then (if b0 then 97766350 else 102116120) else (if b0 then 98716547 else 102741671))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 102734142 else 97083427) else (if b0 then 99192516 else 98821684)) else (if b1 then (if b0 then 95403267 else 92416499) else (if b0 then 103623571 else 99733744))) else (if b2 then (if b1 then (if b0 then 108218397 else 99207335) else (if b0 then 99545333 else 102847514)) else (if b1 then (if b0 then 99668612 else 98917140) else (if b0 then 101417301 else 95316226)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99242843 else 104373365) else (if b0 then 98129874 else 98824522)) else (if b1 then (if b0 then 102975859 else 97858874) else (if b0 then 99972278 else 99515967))) else (if b2 then (if b1 then (if b0 then 95234870 else 101905540) else (if b0 then 97713284 else 104013353)) else (if b1 then (if b0 then 100831342 else 94494032) else (if b0 then 100588508 else 97150532)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99426756 else 99612680) else (if b0 then 99988796 else 99160792)) else (if b1 then (if b0 then 98128090 else 100379070) else (if b0 then 102146755 else 99286190))) else (if b2 then (if b1 then (if b0 then 99622193 else 98392281) else (if b0 then 101186501 else 102090538)) else (if b1 then (if b0 then 99163813 else 100299854) else (if b0 then 101023854 else 100340429)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97285703 else 98859813) else (if b0 then 96850824 else 96686953)) else (if b1 then (if b0 then 98468155 else 103409741) else (if b0 then 97751069 else 99771692))) else (if b2 then (if b1 then (if b0 then 100905235 else 102305283) else (if b0 then 97766350 else 100831342)) else (if b1 then (if b0 then 103474366 else 99494863) else (if b0 then 101244170 else 101316031))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98907032 else 103375288) else (if b0 then 101022430 else 104013970)) else (if b1 then (if b0 then 108993195 else 101959999) else (if b0 then 97319815 else 99911136))) else (if b2 then (if b1 then (if b0 then 87583977 else 98667053) else (if b0 then 101633625 else 92980649)) else (if b1 then (if b0 then 98978664 else 104916229) else (if b0 then 100134941 else 105366975)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97265058 else 94294965) else (if b0 then 102681204 else 102756413)) else (if b1 then (if b0 then 93645740 else 101917109) else (if b0 then 96578013 else 100516795))) else (if b2 then (if b1 then (if b0 then 107096460 else 98505022) else (if b0 then 102116120 else 94494032)) else (if b1 then (if b0 then 99494863 else 111193737) else (if b0 then 99961954 else 103644334)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100798826 else 101159339) else (if b0 then 100006056 else 99499008)) else (if b1 then (if b0 then 101158375 else 98238002) else (if b0 then 101817091 else 100618649))) else (if b2 then (if b1 then (if b0 then 101284464 else 100011312) else (if b0 then 100039146 else 100882830)) else (if b1 then (if b0 then 100920962 else 100138824) else (if b0 then 101732829 else 98111363)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100558693 else 102542379) else (if b0 then 102423719 else 100275005)) else (if b1 then (if b0 then 98338060 else 96094740) else (if b0 then 98296497 else 100712413))) else (if b2 then (if b1 then (if b0 then 99220493 else 100431525) else (if b0 then 98716547 else 100588508)) else (if b1 then (if b0 then 101244170 else 99961954) else (if b0 then 101458431 else 98888854))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 97069623 else 101109820) else (if b0 then 100498766 else 101334005)) else (if b1 then (if b0 then 101347275 else 109596306) else (if b0 then 98641142 else 98118779))) else (if b2 then (if b1 then (if b0 then 92943581 else 99739281) else (if b0 then 100874279 else 98110069)) else (if b1 then (if b0 then 100080148 else 100286697) else (if b0 then 96514216 else 104251210)))) else (if b3 then (if b2 then (if b1 then (if b0 then 95989439 else 91610933) else (if b0 then 98183359 else 97524495)) else (if b1 then (if b0 then 97566556 else 105961941) else (if b0 then 100925991 else 97487168))) else (if b2 then (if b1 then (if b0 then 105171921 else 101660712) else (if b0 then 102741671 else 97150532)) else (if b1 then (if b0 then 101316031 else 103644334) else (if b0 then 98888854 else 106407331)))))))
private lemma checkQ2_1_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift1 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨1, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨1, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨1, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨1, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨1, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨1, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

private def q2DotShift2 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100658882 else 99933758) else (if b0 then 99948473 else 99922235)) else (if b1 then (if b0 then 101400092 else 99950947) else (if b0 then 99596591 else 99935787))) else (if b2 then (if b1 then (if b0 then 98837782 else 99898737) else (if b0 then 96969731 else 100832439)) else (if b1 then (if b0 then 99915252 else 101524255) else (if b0 then 100989456 else 99506091)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99569003 else 100760165) else (if b0 then 98849964 else 99875955)) else (if b1 then (if b0 then 101449080 else 99764719) else (if b0 then 100411481 else 100259603))) else (if b2 then (if b1 then (if b0 then 97548865 else 99930097) else (if b0 then 100081973 else 99976732)) else (if b1 then (if b0 then 99301045 else 98734447) else (if b0 then 99889291 else 99340085))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99933758 else 102507055) else (if b0 then 99049602 else 99397912)) else (if b1 then (if b0 then 101568491 else 99838464) else (if b0 then 101383958 else 100636578))) else (if b2 then (if b1 then (if b0 then 98190577 else 99194988) else (if b0 then 100757399 else 95817150)) else (if b1 then (if b0 then 99623167 else 100476178) else (if b0 then 98171759 else 98852598)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100381638 else 101947658) else (if b0 then 98526875 else 100289752)) else (if b1 then (if b0 then 98929664 else 100018123) else (if b0 then 99888084 else 99708626))) else (if b2 then (if b1 then (if b0 then 101456937 else 101102729) else (if b0 then 98298409 else 102195210)) else (if b1 then (if b0 then 100226786 else 99482263) else (if b0 then 100658906 else 100506071)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99948473 else 99049602) else (if b0 then 108623068 else 101735631)) else (if b1 then (if b0 then 96151383 else 100114151) else (if b0 then 97843591 else 101716002))) else (if b2 then (if b1 then (if b0 then 100874602 else 98462423) else (if b0 then 97350163 else 103177016)) else (if b1 then (if b0 then 96958096 else 95543028) else (if b0 then 103125749 else 101343717)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103022144 else 98532357) else (if b0 then 104558054 else 99633591)) else (if b1 then (if b0 then 97062353 else 99975307) else (if b0 then 103939945 else 102924926))) else (if b2 then (if b1 then (if b0 then 105807687 else 94107625) else (if b0 then 105492919 else 98064109)) else (if b1 then (if b0 then 100605727 else 101672215) else (if b0 then 98366499 else 99782984))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99922235 else 99397912) else (if b0 then 101735631 else 101270633)) else (if b1 then (if b0 then 98571343 else 100797687) else (if b0 then 99842430 else 99867714))) else (if b2 then (if b1 then (if b0 then 101159227 else 100051989) else (if b0 then 99157099 else 102779478)) else (if b1 then (if b0 then 99881580 else 99144001) else (if b0 then 101358719 else 101084391)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100721631 else 99001451) else (if b0 then 102162127 else 99603844)) else (if b1 then (if b0 then 98172260 else 99350825) else (if b0 then 100242532 else 100699372))) else (if b2 then (if b1 then (if b0 then 102227934 else 99817316) else (if b0 then 102056647 else 98870822)) else (if b1 then (if b0 then 99458921 else 99814196) else (if b0 then 98739698 else 99120151)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101400092 else 101568491) else (if b0 then 96151383 else 98571343)) else (if b1 then (if b0 then 107731381 else 101874930) else (if b0 then 100494558 else 101051770))) else (if b2 then (if b1 then (if b0 then 94024889 else 99903449) else (if b0 then 96267944 else 97999285)) else (if b1 then (if b0 then 100826120 else 103963011) else (if b0 then 98350998 else 97003180)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98192183 else 103016282) else (if b0 then 93986614 else 99942907)) else (if b1 then (if b0 then 105607068 else 101732905) else (if b0 then 100075881 else 101814226))) else (if b2 then (if b1 then (if b0 then 91187745 else 102925519) else (if b0 then 95817987 else 100169919)) else (if b1 then (if b0 then 98210065 else 96072698) else (if b0 then 100853882 else 99161086))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99950947 else 99838464) else (if b0 then 100114151 else 100797687)) else (if b1 then (if b0 then 101874930 else 103806093) else (if b0 then 102380935 else 102092049))) else (if b2 then (if b1 then (if b0 then 98054350 else 100731052) else (if b0 then 101893780 else 102572321)) else (if b1 then (if b0 then 99769596 else 96828142) else (if b0 then 99469790 else 99898923)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102083663 else 100642864) else (if b0 then 101342801 else 98734190)) else (if b1 then (if b0 then 100808552 else 103130357) else (if b0 then 101529610 else 104398105))) else (if b2 then (if b1 then (if b0 then 99545722 else 102349017) else (if b0 then 101503199 else 96777836)) else (if b1 then (if b0 then 97935020 else 97607132) else (if b0 then 97168121 else 98307049)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99596591 else 101383958) else (if b0 then 97843591 else 99842430)) else (if b1 then (if b0 then 100494558 else 102380935) else (if b0 then 108397675 else 102665982))) else (if b2 then (if b1 then (if b0 then 97980190 else 101110842) else (if b0 then 104780603 else 99620848)) else (if b1 then (if b0 then 98372511 else 95170120) else (if b0 then 99431359 else 99653363)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105442066 else 104986331) else (if b0 then 103239451 else 97611209)) else (if b1 then (if b0 then 99610582 else 104597527) else (if b0 then 102502459 else 104092010))) else (if b2 then (if b1 then (if b0 then 102603031 else 105886564) else (if b0 then 105055544 else 97309659)) else (if b1 then (if b0 then 96666729 else 95427691) else (if b0 then 94486975 else 97236465))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99935787 else 100636578) else (if b0 then 101716002 else 99867714)) else (if b1 then (if b0 then 101051770 else 102092049) else (if b0 then 102665982 else 103339747))) else (if b2 then (if b1 then (if b0 then 97603334 else 99590833) else (if b0 then 102988854 else 99972729)) else (if b1 then (if b0 then 98236644 else 95691996) else (if b0 then 98762038 else 98242305)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103604912 else 102915375) else (if b0 then 101460815 else 99053534)) else (if b1 then (if b0 then 101380279 else 103679064) else (if b0 then 103620553 else 104704118))) else (if b2 then (if b1 then (if b0 then 100190510 else 99653874) else (if b0 then 102501563 else 99023145)) else (if b1 then (if b0 then 98250528 else 97622482) else (if b0 then 96905711 else 98925915)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98837782 else 98190577) else (if b0 then 100874602 else 101159227)) else (if b1 then (if b0 then 94024889 else 98054350) else (if b0 then 97980190 else 97603334))) else (if b2 then (if b1 then (if b0 then 106290448 else 100291159) else (if b0 then 103329715 else 102056166)) else (if b1 then (if b0 then 101263713 else 99666493) else (if b0 then 100438427 else 102158936)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99120580 else 96349663) else (if b0 then 103601702 else 100792021)) else (if b1 then (if b0 then 95913554 else 96785820) else (if b0 then 97669442 else 96468019))) else (if b2 then (if b1 then (if b0 then 105031530 else 98142945) else (if b0 then 100962533 else 101204216)) else (if b1 then (if b0 then 101651716 else 103491552) else (if b0 then 100564225 else 101034664))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99898737 else 99194988) else (if b0 then 98462423 else 100051989)) else (if b1 then (if b0 then 99903449 else 100731052) else (if b0 then 101110842 else 99590833))) else (if b2 then (if b1 then (if b0 then 100291159 else 101711761) else (if b0 then 100743390 else 101626059)) else (if b1 then (if b0 then 100315722 else 98673846) else (if b0 then 100879947 else 101398002)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99867693 else 99177331) else (if b0 then 100032205 else 99331511)) else (if b1 then (if b0 then 100513365 else 101171191) else (if b0 then 99399030 else 99988924))) else (if b2 then (if b1 then (if b0 then 99411339 else 101644314) else (if b0 then 99761364 else 98548367)) else (if b1 then (if b0 then 99923848 else 100333633) else (if b0 then 99742075 else 99722600)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 96969731 else 100757399) else (if b0 then 97350163 else 99157099)) else (if b1 then (if b0 then 96267944 else 101893780) else (if b0 then 104780603 else 102988854))) else (if b2 then (if b1 then (if b0 then 103329715 else 100743390) else (if b0 then 119635491 else 95441667)) else (if b1 then (if b0 then 100592801 else 91107118) else (if b0 then 91893794 else 98558156)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103899664 else 100686518) else (if b0 then 104288166 else 100134546)) else (if b1 then (if b0 then 97729936 else 104688346) else (if b0 then 100165893 else 102144281))) else (if b2 then (if b1 then (if b0 then 106483696 else 101427071) else (if b0 then 99051420 else 101705604)) else (if b1 then (if b0 then 100670318 else 102074599) else (if b0 then 97780760 else 102001765))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100832439 else 95817150) else (if b0 then 103177016 else 102779478)) else (if b1 then (if b0 then 97999285 else 102572321) else (if b0 then 99620848 else 99972729))) else (if b2 then (if b1 then (if b0 then 102056166 else 101626059) else (if b0 then 95441667 else 112019428)) else (if b1 then (if b0 then 99889376 else 98210501) else (if b0 then 105579677 else 101995191)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101683635 else 98568951) else (if b0 then 104518111 else 98067119)) else (if b1 then (if b0 then 101154862 else 100305564) else (if b0 then 102181936 else 103622112))) else (if b2 then (if b1 then (if b0 then 97938696 else 99356895) else (if b0 then 106707794 else 95181786)) else (if b1 then (if b0 then 96442473 else 96831017) else (if b0 then 94904077 else 95950957)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99915252 else 99623167) else (if b0 then 96958096 else 99881580)) else (if b1 then (if b0 then 100826120 else 99769596) else (if b0 then 98372511 else 98236644))) else (if b2 then (if b1 then (if b0 then 101263713 else 100315722) else (if b0 then 100592801 else 99889376)) else (if b1 then (if b0 then 102339746 else 103364792) else (if b0 then 98616977 else 99776178)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97134833 else 98507499) else (if b0 then 98183328 else 100856730)) else (if b1 then (if b0 then 100500206 else 98156172) else (if b0 then 97089565 else 97632507))) else (if b2 then (if b1 then (if b0 then 97573705 else 101234653) else (if b0 then 96672440 else 101232757)) else (if b1 then (if b0 then 100382862 else 100474463) else (if b0 then 101753858 else 100570152))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101524255 else 100476178) else (if b0 then 95543028 else 99144001)) else (if b1 then (if b0 then 103963011 else 96828142) else (if b0 then 95170120 else 95691996))) else (if b2 then (if b1 then (if b0 then 99666493 else 98673846) else (if b0 then 91107118 else 98210501)) else (if b1 then (if b0 then 103364792 else 112329771) else (if b0 then 100230845 else 98327486)))) else (if b3 then (if b2 then (if b1 then (if b0 then 93240625 else 99543266) else (if b0 then 93527190 else 102074455)) else (if b1 then (if b0 then 102363335 else 93660163) else (if b0 then 95216140 else 93809681))) else (if b2 then (if b1 then (if b0 then 92170644 else 100975569) else (if b0 then 94350193 else 103808981)) else (if b1 then (if b0 then 100402516 else 98963425) else (if b0 then 104685541 else 100469229)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100989456 else 98171759) else (if b0 then 103125749 else 101358719)) else (if b1 then (if b0 then 98350998 else 99469790) else (if b0 then 99431359 else 98762038))) else (if b2 then (if b1 then (if b0 then 100438427 else 100879947) else (if b0 then 91893794 else 105579677)) else (if b1 then (if b0 then 98616977 else 100230845) else (if b0 then 106274798 else 102994288)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100427108 else 98774689) else (if b0 then 101791731 else 98770615)) else (if b1 then (if b0 then 99332130 else 98920952) else (if b0 then 101074782 else 100008543))) else (if b2 then (if b1 then (if b0 then 100526459 else 99267181) else (if b0 then 104532376 else 96670368)) else (if b1 then (if b0 then 99380137 else 99653784) else (if b0 then 98793008 else 98174261))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99506091 else 98852598) else (if b0 then 101343717 else 101084391)) else (if b1 then (if b0 then 97003180 else 99898923) else (if b0 then 99653363 else 98242305))) else (if b2 then (if b1 then (if b0 then 102158936 else 101398002) else (if b0 then 98558156 else 101995191)) else (if b1 then (if b0 then 99776178 else 98327486) else (if b0 then 102994288 else 104266637)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99538311 else 96069922) else (if b0 then 102131921 else 99488196)) else (if b1 then (if b0 then 96490906 else 99248911) else (if b0 then 98441646 else 98357963))) else (if b2 then (if b1 then (if b0 then 104714176 else 100724477) else (if b0 then 101181401 else 96786886)) else (if b1 then (if b0 then 101835046 else 103383752) else (if b0 then 101058035 else 100552587)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99569003 else 100381638) else (if b0 then 103022144 else 100721631)) else (if b1 then (if b0 then 98192183 else 102083663) else (if b0 then 105442066 else 103604912))) else (if b2 then (if b1 then (if b0 then 99120580 else 99867693) else (if b0 then 103899664 else 101683635)) else (if b1 then (if b0 then 97134833 else 93240625) else (if b0 then 100427108 else 99538311)))) else (if b3 then (if b2 then (if b1 then (if b0 then 106364444 else 103733330) else (if b0 then 105294241 else 98006910)) else (if b1 then (if b0 then 98840630 else 104025762) else (if b0 then 104699219 else 105479761))) else (if b2 then (if b1 then (if b0 then 104492541 else 100733908) else (if b0 then 107109359 else 97530835)) else (if b1 then (if b0 then 97256314 else 96786090) else (if b0 then 94115739 else 97590933))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100760165 else 101947658) else (if b0 then 98532357 else 99001451)) else (if b1 then (if b0 then 103016282 else 100642864) else (if b0 then 104986331 else 102915375))) else (if b2 then (if b1 then (if b0 then 96349663 else 99177331) else (if b0 then 100686518 else 98568951)) else (if b1 then (if b0 then 98507499 else 99543266) else (if b0 then 98774689 else 96069922)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103733330 else 107186896) else (if b0 then 99685476 else 98884743)) else (if b1 then (if b0 then 103080277 else 102692396) else (if b0 then 103578295 else 103585027))) else (if b2 then (if b1 then (if b0 then 96918549 else 102006570) else (if b0 then 102972679 else 101645360)) else (if b1 then (if b0 then 96145168 else 93695117) else (if b0 then 95672773 else 97385217)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98849964 else 98526875) else (if b0 then 104558054 else 102162127)) else (if b1 then (if b0 then 93986614 else 101342801) else (if b0 then 103239451 else 101460815))) else (if b2 then (if b1 then (if b0 then 103601702 else 100032205) else (if b0 then 104288166 else 104518111)) else (if b1 then (if b0 then 98183328 else 93527190) else (if b0 then 101791731 else 102131921)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105294241 else 99685476) else (if b0 then 108401923 else 98429218)) else (if b1 then (if b0 then 95313987 else 101286773) else (if b0 then 102647431 else 103214942))) else (if b2 then (if b1 then (if b0 then 108471819 else 99816567) else (if b0 then 108458435 else 96306418)) else (if b1 then (if b0 then 98532863 else 99590379) else (if b0 then 94705020 else 98074292))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99875955 else 100289752) else (if b0 then 99633591 else 99603844)) else (if b1 then (if b0 then 99942907 else 98734190) else (if b0 then 97611209 else 99053534))) else (if b2 then (if b1 then (if b0 then 100792021 else 99331511) else (if b0 then 100134546 else 98067119)) else (if b1 then (if b0 then 100856730 else 102074455) else (if b0 then 98770615 else 99488196)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98006910 else 98884743) else (if b0 then 98429218 else 101167753)) else (if b1 then (if b0 then 99780308 else 98238684) else (if b0 then 98578659 else 97864288))) else (if b2 then (if b1 then (if b0 then 99579068 else 98502764) else (if b0 then 97239153 else 102188470)) else (if b1 then (if b0 then 101431178 else 101705133) else (if b0 then 102347687 else 101462453)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 101449080 else 98929664) else (if b0 then 97062353 else 98172260)) else (if b1 then (if b0 then 105607068 else 100808552) else (if b0 then 99610582 else 101380279))) else (if b2 then (if b1 then (if b0 then 95913554 else 100513365) else (if b0 then 97729936 else 101154862)) else (if b1 then (if b0 then 100500206 else 102363335) else (if b0 then 99332130 else 96490906)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98840630 else 103080277) else (if b0 then 95313987 else 99780308)) else (if b1 then (if b0 then 108676992 else 102803344) else (if b0 then 101770378 else 102462109))) else (if b2 then (if b1 then (if b0 then 88210763 else 99945539) else (if b0 then 98006843 else 99874846)) else (if b1 then (if b0 then 97747134 else 96142346) else (if b0 then 99524106 else 98913235))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99764719 else 100018123) else (if b0 then 99975307 else 99350825)) else (if b1 then (if b0 then 101732905 else 103130357) else (if b0 then 104597527 else 103679064))) else (if b2 then (if b1 then (if b0 then 96785820 else 101171191) else (if b0 then 104688346 else 100305564)) else (if b1 then (if b0 then 98156172 else 93660163) else (if b0 then 98920952 else 99248911)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104025762 else 102692396) else (if b0 then 101286773 else 98238684)) else (if b1 then (if b0 then 102803344 else 106193059) else (if b0 then 103597599 else 105602429))) else (if b2 then (if b1 then (if b0 then 99075753 else 101825265) else (if b0 then 102410627 else 96523931)) else (if b1 then (if b0 then 98202413 else 97802853) else (if b0 then 96584722 else 98853731)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100411481 else 99888084) else (if b0 then 103939945 else 100242532)) else (if b1 then (if b0 then 100075881 else 101529610) else (if b0 then 102502459 else 103620553))) else (if b2 then (if b1 then (if b0 then 97669442 else 99399030) else (if b0 then 100165893 else 102181936)) else (if b1 then (if b0 then 97089565 else 95216140) else (if b0 then 101074782 else 98441646)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104699219 else 103578295) else (if b0 then 102647431 else 98578659)) else (if b1 then (if b0 then 101770378 else 103597599) else (if b0 then 105343696 else 105508376))) else (if b2 then (if b1 then (if b0 then 100086120 else 98027875) else (if b0 then 105385040 else 98403167)) else (if b1 then (if b0 then 97552637 else 96812299) else (if b0 then 95598114 else 97985108))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100259603 else 99708626) else (if b0 then 102924926 else 100699372)) else (if b1 then (if b0 then 101814226 else 104398105) else (if b0 then 104092010 else 104704118))) else (if b2 then (if b1 then (if b0 then 96468019 else 99988924) else (if b0 then 102144281 else 103622112)) else (if b1 then (if b0 then 97632507 else 93809681) else (if b0 then 100008543 else 98357963)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105479761 else 103585027) else (if b0 then 103214942 else 97864288)) else (if b1 then (if b0 then 102462109 else 105602429) else (if b0 then 105508376 else 108160496))) else (if b2 then (if b1 then (if b0 then 99211180 else 100621401) else (if b0 then 105593576 else 95866426)) else (if b1 then (if b0 then 96194503 else 95225744) else (if b0 then 94047378 else 96972406)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 97548865 else 101456937) else (if b0 then 105807687 else 102227934)) else (if b1 then (if b0 then 91187745 else 99545722) else (if b0 then 102603031 else 100190510))) else (if b2 then (if b1 then (if b0 then 105031530 else 99411339) else (if b0 then 106483696 else 97938696)) else (if b1 then (if b0 then 97573705 else 92170644) else (if b0 then 100526459 else 104714176)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104492541 else 96918549) else (if b0 then 108471819 else 99579068)) else (if b1 then (if b0 then 88210763 else 99075753) else (if b0 then 100086120 else 99211180))) else (if b2 then (if b1 then (if b0 then 118270051 else 99261176) else (if b0 then 105145053 else 98874863)) else (if b1 then (if b0 then 102941481 else 105405467) else (if b0 then 98905009 else 101485940))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99930097 else 101102729) else (if b0 then 94107625 else 99817316)) else (if b1 then (if b0 then 102925519 else 102349017) else (if b0 then 105886564 else 99653874))) else (if b2 then (if b1 then (if b0 then 98142945 else 101644314) else (if b0 then 101427071 else 99356895)) else (if b1 then (if b0 then 101234653 else 100975569) else (if b0 then 99267181 else 100724477)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100733908 else 102006570) else (if b0 then 99816567 else 98502764)) else (if b1 then (if b0 then 99945539 else 101825265) else (if b0 then 98027875 else 100621401))) else (if b2 then (if b1 then (if b0 then 99261176 else 108760516) else (if b0 then 100420547 else 96757093)) else (if b1 then (if b0 then 97687790 else 96458045) else (if b0 then 97981759 else 97964571)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100081973 else 98298409) else (if b0 then 105492919 else 102056647)) else (if b1 then (if b0 then 95817987 else 101503199) else (if b0 then 105055544 else 102501563))) else (if b2 then (if b1 then (if b0 then 100962533 else 99761364) else (if b0 then 99051420 else 106707794)) else (if b1 then (if b0 then 96672440 else 94350193) else (if b0 then 104532376 else 101181401)))) else (if b3 then (if b2 then (if b1 then (if b0 then 107109359 else 102972679) else (if b0 then 108458435 else 97239153)) else (if b1 then (if b0 then 98006843 else 102410627) else (if b0 then 105385040 else 105593576))) else (if b2 then (if b1 then (if b0 then 105145053 else 100420547) else (if b0 then 112408888 else 94511924)) else (if b1 then (if b0 then 95988263 else 95613576) else (if b0 then 92013083 else 95645377))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99976732 else 102195210) else (if b0 then 98064109 else 98870822)) else (if b1 then (if b0 then 100169919 else 96777836) else (if b0 then 97309659 else 99023145))) else (if b2 then (if b1 then (if b0 then 101204216 else 98548367) else (if b0 then 101705604 else 95181786)) else (if b1 then (if b0 then 101232757 else 103808981) else (if b0 then 96670368 else 96786886)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97530835 else 101645360) else (if b0 then 96306418 else 102188470)) else (if b1 then (if b0 then 99874846 else 96523931) else (if b0 then 98403167 else 95866426))) else (if b2 then (if b1 then (if b0 then 98874863 else 96757093) else (if b0 then 94511924 else 108939259)) else (if b1 then (if b0 then 101294762 else 100841340) else (if b0 then 102894854 else 101996720)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99301045 else 100226786) else (if b0 then 100605727 else 99458921)) else (if b1 then (if b0 then 98210065 else 97935020) else (if b0 then 96666729 else 98250528))) else (if b2 then (if b1 then (if b0 then 101651716 else 99923848) else (if b0 then 100670318 else 96442473)) else (if b1 then (if b0 then 100382862 else 100402516) else (if b0 then 99380137 else 101835046)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97256314 else 96145168) else (if b0 then 98532863 else 101431178)) else (if b1 then (if b0 then 97747134 else 98202413) else (if b0 then 97552637 else 96194503))) else (if b2 then (if b1 then (if b0 then 102941481 else 97687790) else (if b0 then 95988263 else 101294762)) else (if b1 then (if b0 then 104097924 else 105642710) else (if b0 then 104765590 else 103372594))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 98734447 else 99482263) else (if b0 then 101672215 else 99814196)) else (if b1 then (if b0 then 96072698 else 97607132) else (if b0 then 95427691 else 97622482))) else (if b2 then (if b1 then (if b0 then 103491552 else 100333633) else (if b0 then 102074599 else 96831017)) else (if b1 then (if b0 then 100474463 else 98963425) else (if b0 then 99653784 else 103383752)))) else (if b3 then (if b2 then (if b1 then (if b0 then 96786090 else 93695117) else (if b0 then 99590379 else 101705133)) else (if b1 then (if b0 then 96142346 else 97802853) else (if b0 then 96812299 else 95225744))) else (if b2 then (if b1 then (if b0 then 105405467 else 96458045) else (if b0 then 95613576 else 100841340)) else (if b1 then (if b0 then 105642710 else 108340952) else (if b0 then 105842833 else 104470574)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99889291 else 100658906) else (if b0 then 98366499 else 98739698)) else (if b1 then (if b0 then 100853882 else 97168121) else (if b0 then 94486975 else 96905711))) else (if b2 then (if b1 then (if b0 then 100564225 else 99742075) else (if b0 then 97780760 else 94904077)) else (if b1 then (if b0 then 101753858 else 104685541) else (if b0 then 98793008 else 101058035)))) else (if b3 then (if b2 then (if b1 then (if b0 then 94115739 else 95672773) else (if b0 then 94705020 else 102347687)) else (if b1 then (if b0 then 99524106 else 96584722) else (if b0 then 95598114 else 94047378))) else (if b2 then (if b1 then (if b0 then 98905009 else 97981759) else (if b0 then 92013083 else 102894854)) else (if b1 then (if b0 then 104765590 else 105842833) else (if b0 then 107479790 else 104157476))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 99340085 else 100506071) else (if b0 then 99782984 else 99120151)) else (if b1 then (if b0 then 99161086 else 98307049) else (if b0 then 97236465 else 98925915))) else (if b2 then (if b1 then (if b0 then 101034664 else 99722600) else (if b0 then 102001765 else 95950957)) else (if b1 then (if b0 then 100570152 else 100469229) else (if b0 then 98174261 else 100552587)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97590933 else 97385217) else (if b0 then 98074292 else 101462453)) else (if b1 then (if b0 then 98913235 else 98853731) else (if b0 then 97985108 else 96972406))) else (if b2 then (if b1 then (if b0 then 101485940 else 97964571) else (if b0 then 95645377 else 101996720)) else (if b1 then (if b0 then 103372594 else 104470574) else (if b0 then 104157476 else 103112774)))))))
private lemma checkQ2_2_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift2 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨2, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨2, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨2, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨2, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨2, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨2, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

private def q2DotShift3 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 112963245) else (if b0 then 100000000 else 105425080)) else (if b1 then (if b0 then 100628852 else 98932255) else (if b0 then 95803994 else 99907553))) else (if b2 then (if b1 then (if b0 then 100000000 else 99953440) else (if b0 then 100000000 else 109464069)) else (if b1 then (if b0 then 102728006 else 99293354) else (if b0 then 98741656 else 97584599)))) else (if b3 then (if b2 then (if b1 then (if b0 then 94337863 else 100877242) else (if b0 then 105514833 else 99589640)) else (if b1 then (if b0 then 104830192 else 94629682) else (if b0 then 99042214 else 90833684))) else (if b2 then (if b1 then (if b0 then 98058353 else 104069571) else (if b0 then 86978493 else 103384817)) else (if b1 then (if b0 then 93867540 else 101392947) else (if b0 then 102344787 else 95552785)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 105425080) else (if b0 then 100000000 else 105574006)) else (if b1 then (if b0 then 102633090 else 102738941) else (if b0 then 102864155 else 100133066))) else (if b2 then (if b1 then (if b0 then 100000000 else 100962356) else (if b0 then 100000000 else 107779508)) else (if b1 then (if b0 then 104080026 else 98714557) else (if b0 then 104226226 else 96070465)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98320504 else 102054658) else (if b0 then 98842680 else 101050381)) else (if b1 then (if b0 then 100552843 else 99050902) else (if b0 then 99308339 else 97325085))) else (if b2 then (if b1 then (if b0 then 98092242 else 101615888) else (if b0 then 89002081 else 101020514)) else (if b1 then (if b0 then 100435799 else 99063414) else (if b0 then 100172395 else 98024430)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100628852) else (if b0 then 100000000 else 102633090)) else (if b1 then (if b0 then 126476689 else 81139150) else (if b0 then 108238613 else 92697124))) else (if b2 then (if b1 then (if b0 then 100000000 else 97278212) else (if b0 then 100000000 else 107863930)) else (if b1 then (if b0 then 102843141 else 106243843) else (if b0 then 110607881 else 96746272)))) else (if b3 then (if b2 then (if b1 then (if b0 then 91939087 else 110711356) else (if b0 then 86639544 else 94602447)) else (if b1 then (if b0 then 95076449 else 92139963) else (if b0 then 100970502 else 95308448))) else (if b2 then (if b1 then (if b0 then 89587422 else 97844750) else (if b0 then 79757666 else 98131865)) else (if b1 then (if b0 then 96799881 else 97823424) else (if b0 then 98948424 else 96043225))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98932255) else (if b0 then 100000000 else 102738941)) else (if b1 then (if b0 then 81139150 else 130760345) else (if b0 then 103639700 else 105340161))) else (if b2 then (if b1 then (if b0 then 100000000 else 103438755) else (if b0 then 100000000 else 107873171)) else (if b1 then (if b0 then 104656483 else 93047053) else (if b0 then 108598057 else 92826633)))) else (if b3 then (if b2 then (if b1 then (if b0 then 115788671 else 95377270) else (if b0 then 98993005 else 105132664)) else (if b1 then (if b0 then 105672868 else 116300224) else (if b0 then 98328761 else 106659797))) else (if b2 then (if b1 then (if b0 then 103814343 else 99208438) else (if b0 then 101577035 else 105435748)) else (if b1 then (if b0 then 104439419 else 99829670) else (if b0 then 98473753 else 100877981)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 95803994) else (if b0 then 100000000 else 102864155)) else (if b1 then (if b0 then 108238613 else 103639700) else (if b0 then 114640816 else 99887747))) else (if b2 then (if b1 then (if b0 then 100000000 else 103832667) else (if b0 then 100000000 else 108556656)) else (if b1 then (if b0 then 107314680 else 98861261) else (if b0 then 115891984 else 88370234)))) else (if b3 then (if b2 then (if b1 then (if b0 then 107739528 else 112351389) else (if b0 then 93254597 else 102431636)) else (if b1 then (if b0 then 96414137 else 103778689) else (if b0 then 99124695 else 102797827))) else (if b2 then (if b1 then (if b0 then 96999257 else 95529008) else (if b0 then 83461853 else 101848228)) else (if b1 then (if b0 then 103815204 else 97243869) else (if b0 then 99377877 else 102301917))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99907553) else (if b0 then 100000000 else 100133066)) else (if b1 then (if b0 then 92697124 else 105340161) else (if b0 then 99887747 else 103862998))) else (if b2 then (if b1 then (if b0 then 100000000 else 101956086) else (if b0 then 100000000 else 96736833)) else (if b1 then (if b0 then 100882363 else 99967393) else (if b0 then 97711718 else 99319613)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102216323 else 98594144) else (if b0 then 104850715 else 102575955)) else (if b1 then (if b0 then 100879276 else 101667037) else (if b0 then 98429484 else 102041949))) else (if b2 then (if b1 then (if b0 then 103077526 else 100323931) else (if b0 then 103889249 else 101021720)) else (if b1 then (if b0 then 100271652 else 99992854) else (if b0 then 101048272 else 101862317)))))))
  else
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99953440) else (if b0 then 100000000 else 100962356)) else (if b1 then (if b0 then 97278212 else 103438755) else (if b0 then 103832667 else 101956086))) else (if b2 then (if b1 then (if b0 then 100000000 else 103174896) else (if b0 then 100000000 else 102154512)) else (if b1 then (if b0 then 102775485 else 97097199) else (if b0 then 102850440 else 94951085)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104143609 else 104768771) else (if b0 then 104053363 else 103029539)) else (if b1 then (if b0 then 99430145 else 100921481) else (if b0 then 99381355 else 100187872))) else (if b2 then (if b1 then (if b0 then 101987646 else 99165817) else (if b0 then 95558578 else 101449063)) else (if b1 then (if b0 then 102096285 else 99648563) else (if b0 then 101102509 else 102597654)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 109464069) else (if b0 then 100000000 else 107779508)) else (if b1 then (if b0 then 107863930 else 107873171) else (if b0 then 108556656 else 96736833))) else (if b2 then (if b1 then (if b0 then 100000000 else 102154512) else (if b0 then 100000000 else 126311928)) else (if b1 then (if b0 then 109136557 else 95267772) else (if b0 then 117197352 else 85789610)))) else (if b3 then (if b2 then (if b1 then (if b0 then 106047658 else 111595800) else (if b0 then 94239581 else 99175053)) else (if b1 then (if b0 then 102083374 else 102752823) else (if b0 then 100883009 else 92108001))) else (if b2 then (if b1 then (if b0 then 93076650 else 98040011) else (if b0 then 68855781 else 105375863)) else (if b1 then (if b0 then 96323391 else 97665206) else (if b0 then 98755614 else 95203343)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102728006) else (if b0 then 100000000 else 104080026)) else (if b1 then (if b0 then 102843141 else 104656483) else (if b0 then 107314680 else 100882363))) else (if b2 then (if b1 then (if b0 then 100000000 else 102775485) else (if b0 then 100000000 else 109136557)) else (if b1 then (if b0 then 106301418 else 98744297) else (if b0 then 109453212 else 91447907)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103824475 else 107247242) else (if b0 then 98735839 else 101797757)) else (if b1 then (if b0 then 101396219 else 101614238) else (if b0 then 98984266 else 99341610))) else (if b2 then (if b1 then (if b0 then 98068233 else 98160880) else (if b0 then 85189784 else 102968480)) else (if b1 then (if b0 then 99074458 else 98912089) else (if b0 then 99515364 else 99064823))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99293354) else (if b0 then 100000000 else 98714557)) else (if b1 then (if b0 then 106243843 else 93047053) else (if b0 then 98861261 else 99967393))) else (if b2 then (if b1 then (if b0 then 100000000 else 97097199) else (if b0 then 100000000 else 95267772)) else (if b1 then (if b0 then 98744297 else 109759474) else (if b0 then 97805398 else 104210335)))) else (if b3 then (if b2 then (if b1 then (if b0 then 94628351 else 97335786) else (if b0 then 94687948 else 95885685)) else (if b1 then (if b0 then 99173648 else 97743832) else (if b0 then 98630954 else 100686507))) else (if b2 then (if b1 then (if b0 then 95929953 else 99120365) else (if b0 then 102441053 else 99058669)) else (if b1 then (if b0 then 92889293 else 98655114) else (if b0 then 99569022 else 97301753)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98741656) else (if b0 then 100000000 else 104226226)) else (if b1 then (if b0 then 110607881 else 108598057) else (if b0 then 115891984 else 97711718))) else (if b2 then (if b1 then (if b0 then 100000000 else 102850440) else (if b0 then 100000000 else 117197352)) else (if b1 then (if b0 then 109453212 else 97805398) else (if b0 then 123766133 else 84323095)))) else (if b3 then (if b2 then (if b1 then (if b0 then 110690570 else 114000583) else (if b0 then 88416259 else 101151588)) else (if b1 then (if b0 then 101209154 else 107115958) else (if b0 then 98952275 else 100904002))) else (if b2 then (if b1 then (if b0 then 93644758 else 95269307) else (if b0 then 74347088 else 105770808)) else (if b1 then (if b0 then 101113608 else 98878809) else (if b0 then 98912935 else 98852463))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 97584599) else (if b0 then 100000000 else 96070465)) else (if b1 then (if b0 then 96746272 else 92826633) else (if b0 then 88370234 else 99319613))) else (if b2 then (if b1 then (if b0 then 100000000 else 94951085) else (if b0 then 100000000 else 85789610)) else (if b1 then (if b0 then 91447907 else 104210335) else (if b0 then 84323095 else 114986734)))) else (if b3 then (if b2 then (if b1 then (if b0 then 90584707 else 86004267) else (if b0 then 99935714 else 96512463)) else (if b1 then (if b0 then 99087032 else 96759072) else (if b0 then 101482648 else 102366295))) else (if b2 then (if b1 then (if b0 then 101941476 else 102739075) else (if b0 then 122411516 else 94041217)) else (if b1 then (if b0 then 99458594 else 100595730) else (if b0 then 98226164 else 98508817)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 94337863) else (if b0 then 100000000 else 98320504)) else (if b1 then (if b0 then 91939087 else 115788671) else (if b0 then 107739528 else 102216323))) else (if b2 then (if b1 then (if b0 then 100000000 else 104143609) else (if b0 then 100000000 else 106047658)) else (if b1 then (if b0 then 103824475 else 94628351) else (if b0 then 110690570 else 90584707)))) else (if b3 then (if b2 then (if b1 then (if b0 then 115777680 else 105820070) else (if b0 then 99470040 else 103415083)) else (if b1 then (if b0 then 100894348 else 110903211) else (if b0 then 99836081 else 104840766))) else (if b2 then (if b1 then (if b0 then 102225989 else 95204583) else (if b0 then 96708642 else 104112658)) else (if b1 then (if b0 then 103187201 else 99300253) else (if b0 then 99136385 else 103694426))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100877242) else (if b0 then 100000000 else 102054658)) else (if b1 then (if b0 then 110711356 else 95377270) else (if b0 then 112351389 else 98594144))) else (if b2 then (if b1 then (if b0 then 100000000 else 104768771) else (if b0 then 100000000 else 111595800)) else (if b1 then (if b0 then 107247242 else 97335786) else (if b0 then 114000583 else 86004267)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105820070 else 118447375) else (if b0 then 100833682 else 102107659)) else (if b1 then (if b0 then 97460407 else 97672528) else (if b0 then 99590402 else 95801522))) else (if b2 then (if b1 then (if b0 then 97119959 else 96121913) else (if b0 then 76101498 else 103760693)) else (if b1 then (if b0 then 100002977 else 98969060) else (if b0 then 102144405 else 102593292)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 105514833) else (if b0 then 100000000 else 98842680)) else (if b1 then (if b0 then 86639544 else 98993005) else (if b0 then 93254597 else 104850715))) else (if b2 then (if b1 then (if b0 then 100000000 else 104053363) else (if b0 then 100000000 else 94239581)) else (if b1 then (if b0 then 98735839 else 94687948) else (if b0 then 88416259 else 99935714)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99470040 else 100833682) else (if b0 then 120371840 else 105148277)) else (if b1 then (if b0 then 102336811 else 94514997) else (if b0 then 98959154 else 95516131))) else (if b2 then (if b1 then (if b0 then 108408128 else 103437275) else (if b0 then 105273094 else 101860091)) else (if b1 then (if b0 then 100252175 else 103077976) else (if b0 then 105106474 else 104661605))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99589640) else (if b0 then 100000000 else 101050381)) else (if b1 then (if b0 then 94602447 else 105132664) else (if b0 then 102431636 else 102575955))) else (if b2 then (if b1 then (if b0 then 100000000 else 103029539) else (if b0 then 100000000 else 99175053)) else (if b1 then (if b0 then 101797757 else 95885685) else (if b0 then 101151588 else 96512463)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103415083 else 102107659) else (if b0 then 105148277 else 104341087)) else (if b1 then (if b0 then 100200399 else 101278034) else (if b0 then 98833050 else 101184420))) else (if b2 then (if b1 then (if b0 then 103610344 else 101054812) else (if b0 then 99659203 else 101401104)) else (if b1 then (if b0 then 104823077 else 100965244) else (if b0 then 102076224 else 103412461)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 104830192) else (if b0 then 100000000 else 100552843)) else (if b1 then (if b0 then 95076449 else 105672868) else (if b0 then 96414137 else 100879276))) else (if b2 then (if b1 then (if b0 then 100000000 else 99430145) else (if b0 then 100000000 else 102083374)) else (if b1 then (if b0 then 101396219 else 99173648) else (if b0 then 101209154 else 99087032)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100894348 else 97460407) else (if b0 then 102336811 else 100200399)) else (if b1 then (if b0 then 110228219 else 102104668) else (if b0 then 99149275 else 100059906))) else (if b2 then (if b1 then (if b0 then 100432776 else 100245292) else (if b0 then 97914465 else 104297765)) else (if b1 then (if b0 then 94481624 else 103853348) else (if b0 then 98558792 else 95430679))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 94629682) else (if b0 then 100000000 else 99050902)) else (if b1 then (if b0 then 92139963 else 116300224) else (if b0 then 103778689 else 101667037))) else (if b2 then (if b1 then (if b0 then 100000000 else 100921481) else (if b0 then 100000000 else 102752823)) else (if b1 then (if b0 then 101614238 else 97743832) else (if b0 then 107115958 else 96759072)))) else (if b3 then (if b2 then (if b1 then (if b0 then 110903211 else 97672528) else (if b0 then 94514997 else 101278034)) else (if b1 then (if b0 then 102104668 else 111401212) else (if b0 then 99833265 else 106708461))) else (if b2 then (if b1 then (if b0 then 100875279 else 96982506) else (if b0 then 103560303 else 102120276)) else (if b1 then (if b0 then 102409551 else 99289033) else (if b0 then 97290887 else 100506389)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99042214) else (if b0 then 100000000 else 99308339)) else (if b1 then (if b0 then 100970502 else 98328761) else (if b0 then 99124695 else 98429484))) else (if b2 then (if b1 then (if b0 then 100000000 else 99381355) else (if b0 then 100000000 else 100883009)) else (if b1 then (if b0 then 98984266 else 98630954) else (if b0 then 98952275 else 101482648)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99836081 else 99590402) else (if b0 then 98959154 else 98833050)) else (if b1 then (if b0 then 99149275 else 99833265) else (if b0 then 101997315 else 100248489))) else (if b2 then (if b1 then (if b0 then 99938355 else 98691621) else (if b0 then 101293211 else 98002003)) else (if b1 then (if b0 then 100370247 else 99175104) else (if b0 then 97599892 else 99240300))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 90833684) else (if b0 then 100000000 else 97325085)) else (if b1 then (if b0 then 95308448 else 106659797) else (if b0 then 102797827 else 102041949))) else (if b2 then (if b1 then (if b0 then 100000000 else 100187872) else (if b0 then 100000000 else 92108001)) else (if b1 then (if b0 then 99341610 else 100686507) else (if b0 then 100904002 else 102366295)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104840766 else 95801522) else (if b0 then 95516131 else 101184420)) else (if b1 then (if b0 then 100059906 else 106708461) else (if b0 then 100248489 else 110262503))) else (if b2 then (if b1 then (if b0 then 102441027 else 96452805) else (if b0 then 111896786 else 97745614)) else (if b1 then (if b0 then 103684860 else 99124106) else (if b0 then 95727814 else 101278748)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98058353) else (if b0 then 100000000 else 98092242)) else (if b1 then (if b0 then 89587422 else 103814343) else (if b0 then 96999257 else 103077526))) else (if b2 then (if b1 then (if b0 then 100000000 else 101987646) else (if b0 then 100000000 else 93076650)) else (if b1 then (if b0 then 98068233 else 95929953) else (if b0 then 93644758 else 101941476)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102225989 else 97119959) else (if b0 then 108408128 else 103610344)) else (if b1 then (if b0 then 100432776 else 100875279) else (if b0 then 99938355 else 102441027))) else (if b2 then (if b1 then (if b0 then 106216915 else 101114166) else (if b0 then 110495488 else 99383959)) else (if b1 then (if b0 then 104283909 else 101383648) else (if b0 then 101072657 else 103793021))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 104069571) else (if b0 then 100000000 else 101615888)) else (if b1 then (if b0 then 97844750 else 99208438) else (if b0 then 95529008 else 100323931))) else (if b2 then (if b1 then (if b0 then 100000000 else 99165817) else (if b0 then 100000000 else 98040011)) else (if b1 then (if b0 then 98160880 else 99120365) else (if b0 then 95269307 else 102739075)))) else (if b3 then (if b2 then (if b1 then (if b0 then 95204583 else 96121913) else (if b0 then 103437275 else 101054812)) else (if b1 then (if b0 then 100245292 else 96982506) else (if b0 then 98691621 else 96452805))) else (if b2 then (if b1 then (if b0 then 101114166 else 105421574) else (if b0 then 102519096 else 100477910)) else (if b1 then (if b0 then 102241124 else 101984887) else (if b0 then 104034119 else 100647903)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 86978493) else (if b0 then 100000000 else 89002081)) else (if b1 then (if b0 then 79757666 else 101577035) else (if b0 then 83461853 else 103889249))) else (if b2 then (if b1 then (if b0 then 100000000 else 95558578) else (if b0 then 100000000 else 68855781)) else (if b1 then (if b0 then 85189784 else 102441053) else (if b0 then 74347088 else 122411516)))) else (if b3 then (if b2 then (if b1 then (if b0 then 96708642 else 76101498) else (if b0 then 105273094 else 99659203)) else (if b1 then (if b0 then 97914465 else 103560303) else (if b0 then 101293211 else 111896786))) else (if b2 then (if b1 then (if b0 then 110495488 else 102519096) else (if b0 then 150206772 else 91692740)) else (if b1 then (if b0 then 106107032 else 101718749) else (if b0 then 98357060 else 104867259))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103384817) else (if b0 then 100000000 else 101020514)) else (if b1 then (if b0 then 98131865 else 105435748) else (if b0 then 101848228 else 101021720))) else (if b2 then (if b1 then (if b0 then 100000000 else 101449063) else (if b0 then 100000000 else 105375863)) else (if b1 then (if b0 then 102968480 else 99058669) else (if b0 then 105770808 else 94041217)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104112658 else 103760693) else (if b0 then 101860091 else 101401104)) else (if b1 then (if b0 then 104297765 else 102120276) else (if b0 then 98002003 else 97745614))) else (if b2 then (if b1 then (if b0 then 99383959 else 100477910) else (if b0 then 91692740 else 105375680)) else (if b1 then (if b0 then 97497171 else 102074092) else (if b0 then 102623722 else 99696368)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 93867540) else (if b0 then 100000000 else 100435799)) else (if b1 then (if b0 then 96799881 else 104439419) else (if b0 then 103815204 else 100271652))) else (if b2 then (if b1 then (if b0 then 100000000 else 102096285) else (if b0 then 100000000 else 96323391)) else (if b1 then (if b0 then 99074458 else 92889293) else (if b0 then 101113608 else 99458594)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103187201 else 100002977) else (if b0 then 100252175 else 104823077)) else (if b1 then (if b0 then 94481624 else 102409551) else (if b0 then 100370247 else 103684860))) else (if b2 then (if b1 then (if b0 then 104283909 else 102241124) else (if b0 then 106107032 else 97497171)) else (if b1 then (if b0 then 114006378 else 100084055) else (if b0 then 101941318 else 106371675))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 101392947) else (if b0 then 100000000 else 99063414)) else (if b1 then (if b0 then 97823424 else 99829670) else (if b0 then 97243869 else 99992854))) else (if b2 then (if b1 then (if b0 then 100000000 else 99648563) else (if b0 then 100000000 else 97665206)) else (if b1 then (if b0 then 98912089 else 98655114) else (if b0 then 98878809 else 100595730)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99300253 else 98969060) else (if b0 then 103077976 else 100965244)) else (if b1 then (if b0 then 103853348 else 99289033) else (if b0 then 99175104 else 99124106))) else (if b2 then (if b1 then (if b0 then 101383648 else 101984887) else (if b0 then 101718749 else 102074092)) else (if b1 then (if b0 then 100084055 else 103387414) else (if b0 then 101904041 else 99983731)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102344787) else (if b0 then 100000000 else 100172395)) else (if b1 then (if b0 then 98948424 else 98473753) else (if b0 then 99377877 else 101048272))) else (if b2 then (if b1 then (if b0 then 100000000 else 101102509) else (if b0 then 100000000 else 98755614)) else (if b1 then (if b0 then 99515364 else 99569022) else (if b0 then 98912935 else 98226164)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99136385 else 102144405) else (if b0 then 105106474 else 102076224)) else (if b1 then (if b0 then 98558792 else 97290887) else (if b0 then 97599892 else 95727814))) else (if b2 then (if b1 then (if b0 then 101072657 else 104034119) else (if b0 then 98357060 else 102623722)) else (if b1 then (if b0 then 101941318 else 101904041) else (if b0 then 106591695 else 103574069))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 95552785) else (if b0 then 100000000 else 98024430)) else (if b1 then (if b0 then 96043225 else 100877981) else (if b0 then 102301917 else 101862317))) else (if b2 then (if b1 then (if b0 then 100000000 else 102597654) else (if b0 then 100000000 else 95203343)) else (if b1 then (if b0 then 99064823 else 97301753) else (if b0 then 98852463 else 98508817)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103694426 else 102593292) else (if b0 then 104661605 else 103412461)) else (if b1 then (if b0 then 95430679 else 100506389) else (if b0 then 99240300 else 101278748))) else (if b2 then (if b1 then (if b0 then 103793021 else 100647903) else (if b0 then 104867259 else 99696368)) else (if b1 then (if b0 then 106371675 else 99983731) else (if b0 then 103574069 else 106383130)))))))
private lemma checkQ2_3_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift3 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨3, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨3, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨3, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨3, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨3, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨3, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

private def q2DotShift4 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 104387969) else (if b0 then 100000000 else 100559095)) else (if b1 then (if b0 then 104100124 else 83343732) else (if b0 then 98383348 else 100727193))) else (if b2 then (if b1 then (if b0 then 100000000 else 100483259) else (if b0 then 100000000 else 109301342)) else (if b1 then (if b0 then 103347990 else 104816245) else (if b0 then 102283493 else 99723340)))) else (if b3 then (if b2 then (if b1 then (if b0 then 107432654 else 103444358) else (if b0 then 102250418 else 103401233)) else (if b1 then (if b0 then 101949836 else 94304166) else (if b0 then 99973513 else 97285913))) else (if b2 then (if b1 then (if b0 then 98680290 else 96957985) else (if b0 then 99956767 else 100682585)) else (if b1 then (if b0 then 99130230 else 100681102) else (if b0 then 101077352 else 107475152)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100559095) else (if b0 then 100000000 else 107195603)) else (if b1 then (if b0 then 109082099 else 81365726) else (if b0 then 105864146 else 102227405))) else (if b2 then (if b1 then (if b0 then 100000000 else 106783426) else (if b0 then 100000000 else 99533406)) else (if b1 then (if b0 then 110798970 else 105130756) else (if b0 then 104709325 else 97420282)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100216984 else 103225272) else (if b0 then 104276214 else 111768904)) else (if b1 then (if b0 then 98624375 else 95043470) else (if b0 then 100375042 else 103088207))) else (if b2 then (if b1 then (if b0 then 93584725 else 102906726) else (if b0 then 95040888 else 105074607)) else (if b1 then (if b0 then 100629791 else 105633765) else (if b0 then 98510795 else 106933623)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 104100124) else (if b0 then 100000000 else 109082099)) else (if b1 then (if b0 then 143987045 else 37636778) else (if b0 then 102940400 else 101631980))) else (if b2 then (if b1 then (if b0 then 100000000 else 105328671) else (if b0 then 100000000 else 108552453)) else (if b1 then (if b0 then 131281081 else 139740272) else (if b0 then 130839062 else 104465709)))) else (if b3 then (if b2 then (if b1 then (if b0 then 87195508 else 93839346) else (if b0 then 112261501 else 112520529)) else (if b1 then (if b0 then 92621044 else 70423724) else (if b0 then 96675317 else 100803053))) else (if b2 then (if b1 then (if b0 then 94886917 else 103156135) else (if b0 then 98103170 else 103195527)) else (if b1 then (if b0 then 89347134 else 111019686) else (if b0 then 105348724 else 128166374))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 83343732) else (if b0 then 100000000 else 81365726)) else (if b1 then (if b0 then 37636778 else 237848713) else (if b0 then 90171716 else 91464840))) else (if b2 then (if b1 then (if b0 then 100000000 else 79191081) else (if b0 then 100000000 else 60881063)) else (if b1 then (if b0 then 30892784 else 28240375) else (if b0 then 53716224 else 97302111)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99552007 else 95042128) else (if b0 then 76459445 else 65367257)) else (if b1 then (if b0 then 106071990 else 147239477) else (if b0 then 105195093 else 98830689))) else (if b2 then (if b1 then (if b0 then 121066568 else 103050525) else (if b0 then 111794427 else 88951876)) else (if b1 then (if b0 then 116160552 else 72486829) else (if b0 then 95608821 else 39675575)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98383348) else (if b0 then 100000000 else 105864146)) else (if b1 then (if b0 then 102940400 else 90171716) else (if b0 then 109037292 else 103828496))) else (if b2 then (if b1 then (if b0 then 100000000 else 108428204) else (if b0 then 100000000 else 100093820)) else (if b1 then (if b0 then 114230830 else 108105278) else (if b0 then 104553148 else 98359294)))) else (if b3 then (if b2 then (if b1 then (if b0 then 93126476 else 100038308) else (if b0 then 102406434 else 106544814)) else (if b1 then (if b0 then 96397380 else 100381150) else (if b0 then 97919390 else 103849270))) else (if b2 then (if b1 then (if b0 then 92892912 else 102062100) else (if b0 then 93314104 else 101837594)) else (if b1 then (if b0 then 102247272 else 107860748) else (if b0 then 99383762 else 102179248))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100727193) else (if b0 then 100000000 else 102227405)) else (if b1 then (if b0 then 101631980 else 91464840) else (if b0 then 103828496 else 107865849))) else (if b2 then (if b1 then (if b0 then 100000000 else 105080479) else (if b0 then 100000000 else 101797756)) else (if b1 then (if b0 then 109837914 else 105394637) else (if b0 then 102508099 else 98877218)))) else (if b3 then (if b2 then (if b1 then (if b0 then 96879064 else 101057668) else (if b0 then 98874934 else 102826749)) else (if b1 then (if b0 then 99251066 else 101019984) else (if b0 then 99102173 else 100891527))) else (if b2 then (if b1 then (if b0 then 94138600 else 99862865) else (if b0 then 95835775 else 101979725)) else (if b1 then (if b0 then 103450204 else 99970014) else (if b0 then 101666724 else 108216348)))))))
  else
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100483259) else (if b0 then 100000000 else 106783426)) else (if b1 then (if b0 then 105328671 else 79191081) else (if b0 then 108428204 else 105080479))) else (if b2 then (if b1 then (if b0 then 100000000 else 110870244) else (if b0 then 100000000 else 101566338)) else (if b1 then (if b0 then 119988640 else 110510478) else (if b0 then 105571903 else 97792360)))) else (if b3 then (if b2 then (if b1 then (if b0 then 95301598 else 102585841) else (if b0 then 101968604 else 110835114)) else (if b1 then (if b0 then 98115071 else 99367729) else (if b0 then 97973774 else 105498093))) else (if b2 then (if b1 then (if b0 then 89615466 else 102506850) else (if b0 then 92213503 else 105848180)) else (if b1 then (if b0 then 99895901 else 108526598) else (if b0 then 98474396 else 109664441)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 109301342) else (if b0 then 100000000 else 99533406)) else (if b1 then (if b0 then 108552453 else 60881063) else (if b0 then 100093820 else 101797756))) else (if b2 then (if b1 then (if b0 then 100000000 else 101566338) else (if b0 then 100000000 else 132015908)) else (if b1 then (if b0 then 114640129 else 125471793) else (if b0 then 111554630 else 103144296)))) else (if b3 then (if b2 then (if b1 then (if b0 then 108927854 else 101686794) else (if b0 then 108112582 else 99554296)) else (if b1 then (if b0 then 100198408 else 84973730) else (if b0 then 95420003 else 90142263))) else (if b2 then (if b1 then (if b0 then 98739469 else 88455893) else (if b0 then 98944406 else 92466663)) else (if b1 then (if b0 then 98272093 else 108337909) else (if b0 then 106753871 else 112291676)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103347990) else (if b0 then 100000000 else 110798970)) else (if b1 then (if b0 then 131281081 else 30892784) else (if b0 then 114230830 else 109837914))) else (if b2 then (if b1 then (if b0 then 100000000 else 119988640) else (if b0 then 100000000 else 114640129)) else (if b1 then (if b0 then 159135314 else 153405340) else (if b0 then 132055705 else 103155390)))) else (if b3 then (if b2 then (if b1 then (if b0 then 74501770 else 94130426) else (if b0 then 106842721 else 113558501)) else (if b1 then (if b0 then 89896509 else 84178134) else (if b0 then 89862265 else 109156138))) else (if b2 then (if b1 then (if b0 then 81111117 else 102404046) else (if b0 then 87235498 else 106050391)) else (if b1 then (if b0 then 90228715 else 122117898) else (if b0 then 103347619 else 132959493))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 104816245) else (if b0 then 100000000 else 105130756)) else (if b1 then (if b0 then 139740272 else 28240375) else (if b0 then 108105278 else 105394637))) else (if b2 then (if b1 then (if b0 then 100000000 else 110510478) else (if b0 then 100000000 else 125471793)) else (if b1 then (if b0 then 153405340 else 165972006) else (if b0 then 140574064 else 109768250)))) else (if b3 then (if b2 then (if b1 then (if b0 then 72148240 else 86099787) else (if b0 then 111410553 else 101204999)) else (if b1 then (if b0 then 87493824 else 72770769) else (if b0 then 88260441 else 100338369))) else (if b2 then (if b1 then (if b0 then 91520787 else 96726012) else (if b0 then 94383753 else 94923937)) else (if b1 then (if b0 then 86391858 else 121358210) else (if b0 then 109709883 else 130671698)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102283493) else (if b0 then 100000000 else 104709325)) else (if b1 then (if b0 then 130839062 else 53716224) else (if b0 then 104553148 else 102508099))) else (if b2 then (if b1 then (if b0 then 100000000 else 105571903) else (if b0 then 100000000 else 111554630)) else (if b1 then (if b0 then 132055705 else 140574064) else (if b0 then 127529494 else 105716292)))) else (if b3 then (if b2 then (if b1 then (if b0 then 80951557 else 90524561) else (if b0 then 107669097 else 102588665)) else (if b1 then (if b0 then 91322872 else 79876791) else (if b0 then 93066013 else 100734605))) else (if b2 then (if b1 then (if b0 then 95361567 else 100255595) else (if b0 then 97303488 else 98038116)) else (if b1 then (if b0 then 91330080 else 112008069) else (if b0 then 106428149 else 120124341))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99723340) else (if b0 then 100000000 else 97420282)) else (if b1 then (if b0 then 104465709 else 97302111) else (if b0 then 98359294 else 98877218))) else (if b2 then (if b1 then (if b0 then 100000000 else 97792360) else (if b0 then 100000000 else 103144296)) else (if b1 then (if b0 then 103155390 else 109768250) else (if b0 then 105716292 else 104330633)))) else (if b3 then (if b2 then (if b1 then (if b0 then 93823699 else 94582502) else (if b0 then 101549119 else 94347871)) else (if b1 then (if b0 then 98637358 else 96077746) else (if b0 then 98245265 else 98009047))) else (if b2 then (if b1 then (if b0 then 103088561 else 98740122) else (if b0 then 102193407 else 96069792)) else (if b1 then (if b0 then 95600414 else 101942123) else (if b0 then 102994388 else 101220357)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 107432654) else (if b0 then 100000000 else 100216984)) else (if b1 then (if b0 then 87195508 else 99552007) else (if b0 then 93126476 else 96879064))) else (if b2 then (if b1 then (if b0 then 100000000 else 95301598) else (if b0 then 100000000 else 108927854)) else (if b1 then (if b0 then 74501770 else 72148240) else (if b0 then 80951557 else 93823699)))) else (if b3 then (if b2 then (if b1 then (if b0 then 139142797 else 117737760) else (if b0 then 104431864 else 111100525)) else (if b1 then (if b0 then 111435508 else 99521117) else (if b0 then 110529889 else 92882173))) else (if b2 then (if b1 then (if b0 then 103165054 else 94104280) else (if b0 then 102851314 else 103940041)) else (if b1 then (if b0 then 105412824 else 92637618) else (if b0 then 93839161 else 97048071))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103444358) else (if b0 then 100000000 else 103225272)) else (if b1 then (if b0 then 93839346 else 95042128) else (if b0 then 100038308 else 101057668))) else (if b2 then (if b1 then (if b0 then 100000000 else 102585841) else (if b0 then 100000000 else 101686794)) else (if b1 then (if b0 then 94130426 else 86099787) else (if b0 then 90524561 else 94582502)))) else (if b3 then (if b2 then (if b1 then (if b0 then 117737760 else 111075902) else (if b0 then 100819929 else 110905075)) else (if b1 then (if b0 then 105541155 else 102204393) else (if b0 then 104452419 else 100038140))) else (if b2 then (if b1 then (if b0 then 96225614 else 99364339) else (if b0 then 97774680 else 106226203)) else (if b1 then (if b0 then 103949293 else 97994988) else (if b0 then 95644848 else 102083139)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102250418) else (if b0 then 100000000 else 104276214)) else (if b1 then (if b0 then 112261501 else 76459445) else (if b0 then 102406434 else 98874934))) else (if b2 then (if b1 then (if b0 then 100000000 else 101968604) else (if b0 then 100000000 else 108112582)) else (if b1 then (if b0 then 106842721 else 111410553) else (if b0 then 107669097 else 101549119)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104431864 else 100819929) else (if b0 then 110041566 else 107526951)) else (if b1 then (if b0 then 98473202 else 87877287) else (if b0 then 102400825 else 98096915))) else (if b2 then (if b1 then (if b0 then 99780824 else 98690832) else (if b0 then 98967258 else 99489059)) else (if b1 then (if b0 then 96682000 else 107401530) else (if b0 then 99331645 else 105816196))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103401233) else (if b0 then 100000000 else 111768904)) else (if b1 then (if b0 then 112520529 else 65367257) else (if b0 then 106544814 else 102826749))) else (if b2 then (if b1 then (if b0 then 100000000 else 110835114) else (if b0 then 100000000 else 99554296)) else (if b1 then (if b0 then 113558501 else 101204999) else (if b0 then 102588665 else 94347871)))) else (if b3 then (if b2 then (if b1 then (if b0 then 111100525 else 110905075) else (if b0 then 107526951 else 124513661)) else (if b1 then (if b0 then 101936963 else 92201421) else (if b0 then 104457952 else 105531707))) else (if b2 then (if b1 then (if b0 then 88986630 else 104544039) else (if b0 then 92674710 else 112743319)) else (if b1 then (if b0 then 99315904 else 107276842) else (if b0 then 94014771 else 114818394)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 101949836) else (if b0 then 100000000 else 98624375)) else (if b1 then (if b0 then 92621044 else 106071990) else (if b0 then 96397380 else 99251066))) else (if b2 then (if b1 then (if b0 then 100000000 else 98115071) else (if b0 then 100000000 else 100198408)) else (if b1 then (if b0 then 89896509 else 87493824) else (if b0 then 91322872 else 98637358)))) else (if b3 then (if b2 then (if b1 then (if b0 then 111435508 else 105541155) else (if b0 then 98473202 else 101936963)) else (if b1 then (if b0 then 106931499 else 102882339) else (if b0 then 101340924 else 96662227))) else (if b2 then (if b1 then (if b0 then 101019599 else 98927244) else (if b0 then 101414822 else 101888942)) else (if b1 then (if b0 then 100959726 else 96065523) else (if b0 then 100989499 else 98728263))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 94304166) else (if b0 then 100000000 else 95043470)) else (if b1 then (if b0 then 70423724 else 147239477) else (if b0 then 100381150 else 101019984))) else (if b2 then (if b1 then (if b0 then 100000000 else 99367729) else (if b0 then 100000000 else 84973730)) else (if b1 then (if b0 then 84178134 else 72770769) else (if b0 then 79876791 else 96077746)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99521117 else 102204393) else (if b0 then 87877287 else 92201421)) else (if b1 then (if b0 then 102882339 else 124938707) else (if b0 then 101346406 else 104991671))) else (if b2 then (if b1 then (if b0 then 100121093 else 102180208) else (if b0 then 99242440 else 101381584)) else (if b1 then (if b0 then 107208524 else 92095689) else (if b0 then 94812503 else 82050966)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99973513) else (if b0 then 100000000 else 100375042)) else (if b1 then (if b0 then 96675317 else 105195093) else (if b0 then 97919390 else 99102173))) else (if b2 then (if b1 then (if b0 then 100000000 else 97973774) else (if b0 then 100000000 else 95420003)) else (if b1 then (if b0 then 89862265 else 88260441) else (if b0 then 93066013 else 98245265)))) else (if b3 then (if b2 then (if b1 then (if b0 then 110529889 else 104452419) else (if b0 then 102400825 else 104457952)) else (if b1 then (if b0 then 101340924 else 101346406) else (if b0 then 108029545 else 101621793))) else (if b2 then (if b1 then (if b0 then 102079616 else 100713589) else (if b0 then 101500523 else 103206563)) else (if b1 then (if b0 then 100595643 else 96456127) else (if b0 then 92968105 else 97988335))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 97285913) else (if b0 then 100000000 else 103088207)) else (if b1 then (if b0 then 100803053 else 98830689) else (if b0 then 103849270 else 100891527))) else (if b2 then (if b1 then (if b0 then 100000000 else 105498093) else (if b0 then 100000000 else 90142263)) else (if b1 then (if b0 then 109156138 else 100338369) else (if b0 then 100734605 else 98009047)))) else (if b3 then (if b2 then (if b1 then (if b0 then 92882173 else 100038140) else (if b0 then 98096915 else 105531707)) else (if b1 then (if b0 then 96662227 else 104991671) else (if b0 then 101621793 else 109590696))) else (if b2 then (if b1 then (if b0 then 94603897 else 105419037) else (if b0 then 96533631 else 106763771)) else (if b1 then (if b0 then 97977729 else 102663496) else (if b0 then 93064322 else 102488970)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98680290) else (if b0 then 100000000 else 93584725)) else (if b1 then (if b0 then 94886917 else 121066568) else (if b0 then 92892912 else 94138600))) else (if b2 then (if b1 then (if b0 then 100000000 else 89615466) else (if b0 then 100000000 else 98739469)) else (if b1 then (if b0 then 81111117 else 91520787) else (if b0 then 95361567 else 103088561)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103165054 else 96225614) else (if b0 then 99780824 else 88986630)) else (if b1 then (if b0 then 101019599 else 100121093) else (if b0 then 102079616 else 94603897))) else (if b2 then (if b1 then (if b0 then 110864927 else 97536938) else (if b0 then 107438682 else 93041694)) else (if b1 then (if b0 then 99241585 else 93973920) else (if b0 then 101266210 else 88497811))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 96957985) else (if b0 then 100000000 else 102906726)) else (if b1 then (if b0 then 103156135 else 103050525) else (if b0 then 102062100 else 99862865))) else (if b2 then (if b1 then (if b0 then 100000000 else 102506850) else (if b0 then 100000000 else 88455893)) else (if b1 then (if b0 then 102404046 else 96726012) else (if b0 then 100255595 else 98740122)))) else (if b3 then (if b2 then (if b1 then (if b0 then 94104280 else 99364339) else (if b0 then 98690832 else 104544039)) else (if b1 then (if b0 then 98927244 else 102180208) else (if b0 then 100713589 else 105419037))) else (if b2 then (if b1 then (if b0 then 97536938 else 105779014) else (if b0 then 98516024 else 105022204)) else (if b1 then (if b0 then 98821256 else 100345449) else (if b0 then 97540212 else 100453928)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99956767) else (if b0 then 100000000 else 95040888)) else (if b1 then (if b0 then 98103170 else 111794427) else (if b0 then 93314104 else 95835775))) else (if b2 then (if b1 then (if b0 then 100000000 else 92213503) else (if b0 then 100000000 else 98944406)) else (if b1 then (if b0 then 87235498 else 94383753) else (if b0 then 97303488 else 102193407)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102851314 else 97774680) else (if b0 then 98967258 else 92674710)) else (if b1 then (if b0 then 101414822 else 99242440) else (if b0 then 101500523 else 96533631))) else (if b2 then (if b1 then (if b0 then 107438682 else 98516024) else (if b0 then 105939994 else 96451028)) else (if b1 then (if b0 then 98229851 else 94457394) else (if b0 then 100860345 else 94899238))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100682585) else (if b0 then 100000000 else 105074607)) else (if b1 then (if b0 then 103195527 else 88951876) else (if b0 then 101837594 else 101979725))) else (if b2 then (if b1 then (if b0 then 100000000 else 105848180) else (if b0 then 100000000 else 92466663)) else (if b1 then (if b0 then 106050391 else 94923937) else (if b0 then 98038116 else 96069792)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103940041 else 106226203) else (if b0 then 99489059 else 112743319)) else (if b1 then (if b0 then 101888942 else 101381584) else (if b0 then 103206563 else 106763771))) else (if b2 then (if b1 then (if b0 then 93041694 else 105022204) else (if b0 then 96451028 else 110553794)) else (if b1 then (if b0 then 98721338 else 100438121) else (if b0 then 94336300 else 108635397)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99130230) else (if b0 then 100000000 else 100629791)) else (if b1 then (if b0 then 89347134 else 116160552) else (if b0 then 102247272 else 103450204))) else (if b2 then (if b1 then (if b0 then 100000000 else 99895901) else (if b0 then 100000000 else 98272093)) else (if b1 then (if b0 then 90228715 else 86391858) else (if b0 then 91330080 else 95600414)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105412824 else 103949293) else (if b0 then 96682000 else 99315904)) else (if b1 then (if b0 then 100959726 else 107208524) else (if b0 then 100595643 else 97977729))) else (if b2 then (if b1 then (if b0 then 99241585 else 98821256) else (if b0 then 98229851 else 98721338)) else (if b1 then (if b0 then 110338451 else 94681630) else (if b0 then 100533915 else 92291742))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100681102) else (if b0 then 100000000 else 105633765)) else (if b1 then (if b0 then 111019686 else 72486829) else (if b0 then 107860748 else 99970014))) else (if b2 then (if b1 then (if b0 then 100000000 else 108526598) else (if b0 then 100000000 else 108337909)) else (if b1 then (if b0 then 122117898 else 121358210) else (if b0 then 112008069 else 101942123)))) else (if b3 then (if b2 then (if b1 then (if b0 then 92637618 else 97994988) else (if b0 then 107401530 else 107276842)) else (if b1 then (if b0 then 96065523 else 92095689) else (if b0 then 96456127 else 102663496))) else (if b2 then (if b1 then (if b0 then 93973920 else 100345449) else (if b0 then 94457394 else 100438121)) else (if b1 then (if b0 then 94681630 else 114572773) else (if b0 then 100244451 else 107102097)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 101077352) else (if b0 then 100000000 else 98510795)) else (if b1 then (if b0 then 105348724 else 95608821) else (if b0 then 99383762 else 101666724))) else (if b2 then (if b1 then (if b0 then 100000000 else 98474396) else (if b0 then 100000000 else 106753871)) else (if b1 then (if b0 then 103347619 else 109709883) else (if b0 then 106428149 else 102994388)))) else (if b3 then (if b2 then (if b1 then (if b0 then 93839161 else 95644848) else (if b0 then 99331645 else 94014771)) else (if b1 then (if b0 then 100989499 else 94812503) else (if b0 then 92968105 else 93064322))) else (if b2 then (if b1 then (if b0 then 101266210 else 97540212) else (if b0 then 100860345 else 94336300)) else (if b1 then (if b0 then 100533915 else 100244451) else (if b0 then 110773250 else 102531614))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 107475152) else (if b0 then 100000000 else 106933623)) else (if b1 then (if b0 then 128166374 else 39675575) else (if b0 then 102179248 else 108216348))) else (if b2 then (if b1 then (if b0 then 100000000 else 109664441) else (if b0 then 100000000 else 112291676)) else (if b1 then (if b0 then 132959493 else 130671698) else (if b0 then 120124341 else 101220357)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97048071 else 102083139) else (if b0 then 105816196 else 114818394)) else (if b1 then (if b0 then 98728263 else 82050966) else (if b0 then 97988335 else 102488970))) else (if b2 then (if b1 then (if b0 then 88497811 else 100453928) else (if b0 then 94899238 else 108635397)) else (if b1 then (if b0 then 92291742 else 107102097) else (if b0 then 102531614 else 134033528)))))))
private lemma checkQ2_4_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift4 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨4, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨4, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨4, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨4, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨4, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨4, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

private def q2DotShift5 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 108886140) else (if b0 then 100000000 else 110579099)) else (if b1 then (if b0 then 103658804 else 103264930) else (if b0 then 102698421 else 103881124))) else (if b2 then (if b1 then (if b0 then 100000000 else 98918093) else (if b0 then 100000000 else 104269189)) else (if b1 then (if b0 then 97750879 else 103017573) else (if b0 then 102330354 else 97062406)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98450505 else 99323829) else (if b0 then 105409740 else 103534364)) else (if b1 then (if b0 then 104545580 else 105092445) else (if b0 then 98929934 else 101986294))) else (if b2 then (if b1 then (if b0 then 102754157 else 100885657) else (if b0 then 88946905 else 100034522)) else (if b1 then (if b0 then 103225135 else 97640846) else (if b0 then 98922733 else 102978335)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 110579099) else (if b0 then 100000000 else 121838261)) else (if b1 then (if b0 then 103239645 else 102817293) else (if b0 then 102441676 else 107716483))) else (if b2 then (if b1 then (if b0 then 100000000 else 97287179) else (if b0 then 100000000 else 107123389)) else (if b1 then (if b0 then 95929510 else 97951577) else (if b0 then 99439239 else 96119285)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97714423 else 98374685) else (if b0 then 107237250 else 104400623)) else (if b1 then (if b0 then 100537942 else 108970799) else (if b0 then 97807569 else 99700381))) else (if b2 then (if b1 then (if b0 then 100208988 else 101678129) else (if b0 then 85494621 else 101066060)) else (if b1 then (if b0 then 97488129 else 91325403) else (if b0 then 101390049 else 101916676)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103658804) else (if b0 then 100000000 else 103239645)) else (if b1 then (if b0 then 139129508 else 112504379) else (if b0 then 108249776 else 96527211))) else (if b2 then (if b1 then (if b0 then 100000000 else 84316972) else (if b0 then 100000000 else 83736759)) else (if b1 then (if b0 then 101098729 else 113905096) else (if b0 then 104718096 else 104602654)))) else (if b3 then (if b2 then (if b1 then (if b0 then 87439059 else 94070353) else (if b0 then 82852985 else 100127565)) else (if b1 then (if b0 then 96444099 else 107114493) else (if b0 then 94268331 else 102515358))) else (if b2 then (if b1 then (if b0 then 102350617 else 95515983) else (if b0 then 68566484 else 99242762)) else (if b1 then (if b0 then 92649383 else 93419550) else (if b0 then 97864574 else 94674059))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103264930) else (if b0 then 100000000 else 102817293)) else (if b1 then (if b0 then 112504379 else 108280188) else (if b0 then 102238784 else 101159667))) else (if b2 then (if b1 then (if b0 then 100000000 else 94810916) else (if b0 then 100000000 else 94850000)) else (if b1 then (if b0 then 98273693 else 104195142) else (if b0 then 100655720 else 97670197)))) else (if b3 then (if b2 then (if b1 then (if b0 then 96915679 else 98322820) else (if b0 then 96778503 else 99457078)) else (if b1 then (if b0 then 101111265 else 101844508) else (if b0 then 98937060 else 103725885))) else (if b2 then (if b1 then (if b0 then 102135998 else 100196562) else (if b0 then 88472067 else 97800354)) else (if b1 then (if b0 then 97643204 else 97974520) else (if b0 then 97908164 else 101569173)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102698421) else (if b0 then 100000000 else 102441676)) else (if b1 then (if b0 then 108249776 else 102238784) else (if b0 then 106080785 else 100305447))) else (if b2 then (if b1 then (if b0 then 100000000 else 97333437) else (if b0 then 100000000 else 101196362)) else (if b1 then (if b0 then 100765667 else 102399823) else (if b0 then 103301678 else 97170284)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97696218 else 98810329) else (if b0 then 96944221 else 104330606)) else (if b1 then (if b0 then 100385748 else 102986797) else (if b0 then 101256930 else 98975611))) else (if b2 then (if b1 then (if b0 then 103371268 else 97638096) else (if b0 then 89957338 else 99826510)) else (if b1 then (if b0 then 104047602 else 98605930) else (if b0 then 96936803 else 101089551))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103881124) else (if b0 then 100000000 else 107716483)) else (if b1 then (if b0 then 96527211 else 101159667) else (if b0 then 100305447 else 106100622))) else (if b2 then (if b1 then (if b0 then 100000000 else 99238075) else (if b0 then 100000000 else 103147026)) else (if b1 then (if b0 then 96530613 else 98486615) else (if b0 then 98261482 else 97264561)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101067933 else 100585470) else (if b0 then 106770178 else 101436519)) else (if b1 then (if b0 then 100846460 else 102788910) else (if b0 then 99810165 else 101259669))) else (if b2 then (if b1 then (if b0 then 102112528 else 102722936) else (if b0 then 98139646 else 100010848)) else (if b1 then (if b0 then 102402380 else 98743668) else (if b0 then 101885261 else 102299771)))))))
  else
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98918093) else (if b0 then 100000000 else 97287179)) else (if b1 then (if b0 then 84316972 else 94810916) else (if b0 then 97333437 else 99238075))) else (if b2 then (if b1 then (if b0 then 100000000 else 109070042) else (if b0 then 100000000 else 110053064)) else (if b1 then (if b0 then 102080650 else 95276879) else (if b0 then 97975609 else 97739449)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104627957 else 102383988) else (if b0 then 104917832 else 100390934)) else (if b1 then (if b0 then 104162903 else 97509850) else (if b0 then 103490723 else 99121548))) else (if b2 then (if b1 then (if b0 then 98612320 else 101123959) else (if b0 then 111819958 else 101551268)) else (if b1 then (if b0 then 103527980 else 102972978) else (if b0 then 100684024 else 102731460)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 104269189) else (if b0 then 100000000 else 107123389)) else (if b1 then (if b0 then 83736759 else 94850000) else (if b0 then 101196362 else 103147026))) else (if b2 then (if b1 then (if b0 then 100000000 else 110053064) else (if b0 then 100000000 else 118780342)) else (if b1 then (if b0 then 102045556 else 94081021) else (if b0 then 98055612 else 94397088)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104338845 else 101966021) else (if b0 then 108026658 else 105198618)) else (if b1 then (if b0 then 106613382 else 103510413) else (if b0 then 105226177 else 97816140))) else (if b2 then (if b1 then (if b0 then 100918467 else 101961277) else (if b0 then 104622689 else 102532910)) else (if b1 then (if b0 then 106933690 else 100439133) else (if b0 then 101465068 else 104867614)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 97750879) else (if b0 then 100000000 else 95929510)) else (if b1 then (if b0 then 101098729 else 98273693) else (if b0 then 100765667 else 96530613))) else (if b2 then (if b1 then (if b0 then 100000000 else 102080650) else (if b0 then 100000000 else 102045556)) else (if b1 then (if b0 then 104050854 else 101303483) else (if b0 then 99853328 else 102824499)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99404905 else 99582826) else (if b0 then 94934736 else 100081902)) else (if b1 then (if b0 then 101333061 else 101206463) else (if b0 then 101544617 else 98577617))) else (if b2 then (if b1 then (if b0 then 99605249 else 99643486) else (if b0 then 100552067 else 100700581)) else (if b1 then (if b0 then 99772486 else 101784171) else (if b0 then 101498337 else 98184244))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103017573) else (if b0 then 100000000 else 97951577)) else (if b1 then (if b0 then 113905096 else 104195142) else (if b0 then 102399823 else 98486615))) else (if b2 then (if b1 then (if b0 then 100000000 else 95276879) else (if b0 then 100000000 else 94081021)) else (if b1 then (if b0 then 101303483 else 110839136) else (if b0 then 102507079 else 105776493)))) else (if b3 then (if b2 then (if b1 then (if b0 then 95363990 else 98374014) else (if b0 then 95474668 else 99507488)) else (if b1 then (if b0 then 103682665 else 104296515) else (if b0 then 97293206 else 103297602))) else (if b2 then (if b1 then (if b0 then 103476163 else 100763856) else (if b0 then 88740127 else 99874350)) else (if b1 then (if b0 then 101810629 else 102516055) else (if b0 then 102158348 else 97590481)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102330354) else (if b0 then 100000000 else 99439239)) else (if b1 then (if b0 then 104718096 else 100655720) else (if b0 then 103301678 else 98261482))) else (if b2 then (if b1 then (if b0 then 100000000 else 97975609) else (if b0 then 100000000 else 98055612)) else (if b1 then (if b0 then 99853328 else 102507079) else (if b0 then 107208484 else 99258719)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100014298 else 98947643) else (if b0 then 99192249 else 103468095)) else (if b1 then (if b0 then 100986912 else 100398220) else (if b0 then 100949225 else 98471801))) else (if b2 then (if b1 then (if b0 then 103054694 else 98128009) else (if b0 then 95279265 else 95779203)) else (if b1 then (if b0 then 103598340 else 102088186) else (if b0 then 94058470 else 100788278))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 97062406) else (if b0 then 100000000 else 96119285)) else (if b1 then (if b0 then 104602654 else 97670197) else (if b0 then 97170284 else 97264561))) else (if b2 then (if b1 then (if b0 then 100000000 else 97739449) else (if b0 then 100000000 else 94397088)) else (if b1 then (if b0 then 102824499 else 105776493) else (if b0 then 99258719 else 112345232)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98055623 else 98700773) else (if b0 then 95090922 else 96548157)) else (if b1 then (if b0 then 99893901 else 104197725) else (if b0 then 97386559 else 99496729))) else (if b2 then (if b1 then (if b0 then 99403209 else 103369742) else (if b0 then 100699923 else 99281342)) else (if b1 then (if b0 then 95807290 else 104072455) else (if b0 then 107588591 else 92878885)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98450505) else (if b0 then 100000000 else 97714423)) else (if b1 then (if b0 then 87439059 else 96915679) else (if b0 then 97696218 else 101067933))) else (if b2 then (if b1 then (if b0 then 100000000 else 104627957) else (if b0 then 100000000 else 104338845)) else (if b1 then (if b0 then 99404905 else 95363990) else (if b0 then 100014298 else 98055623)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105296440 else 101667301) else (if b0 then 105101676 else 100390438)) else (if b1 then (if b0 then 101715683 else 97694322) else (if b0 then 103304779 else 98991767))) else (if b2 then (if b1 then (if b0 then 100809022 else 102298135) else (if b0 then 110708394 else 97087531)) else (if b1 then (if b0 then 102914441 else 104196749) else (if b0 then 99119936 else 102416791))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 99323829) else (if b0 then 100000000 else 98374685)) else (if b1 then (if b0 then 94070353 else 98322820) else (if b0 then 98810329 else 100585470))) else (if b2 then (if b1 then (if b0 then 100000000 else 102383988) else (if b0 then 100000000 else 101966021)) else (if b1 then (if b0 then 99582826 else 98374014) else (if b0 then 98947643 else 98700773)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101667301 else 101275237) else (if b0 then 102953685 else 99691318)) else (if b1 then (if b0 then 100552399 else 97869057) else (if b0 then 100502418 else 100344649))) else (if b2 then (if b1 then (if b0 then 99701676 else 100160157) else (if b0 then 105081608 else 101115196)) else (if b1 then (if b0 then 102120691 else 100918375) else (if b0 then 100167474 else 101203134)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 105409740) else (if b0 then 100000000 else 107237250)) else (if b1 then (if b0 then 82852985 else 96778503) else (if b0 then 96944221 else 106770178))) else (if b2 then (if b1 then (if b0 then 100000000 else 104917832) else (if b0 then 100000000 else 108026658)) else (if b1 then (if b0 then 94934736 else 95474668) else (if b0 then 99192249 else 95090922)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105101676 else 102953685) else (if b0 then 115858724 else 101735614)) else (if b1 then (if b0 then 103529350 else 98788123) else (if b0 then 100079561 else 101486583))) else (if b2 then (if b1 then (if b0 then 101070223 else 103017251) else (if b0 then 108059387 else 100747859)) else (if b1 then (if b0 then 106640134 else 100833244) else (if b0 then 100213192 else 105134744))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103534364) else (if b0 then 100000000 else 104400623)) else (if b1 then (if b0 then 100127565 else 99457078) else (if b0 then 104330606 else 101436519))) else (if b2 then (if b1 then (if b0 then 100000000 else 100390934) else (if b0 then 100000000 else 105198618)) else (if b1 then (if b0 then 100081902 else 99507488) else (if b0 then 103468095 else 96548157)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100390438 else 99691318) else (if b0 then 101735614 else 105030832)) else (if b1 then (if b0 then 101545491 else 102728863) else (if b0 then 102161523 else 97996842))) else (if b2 then (if b1 then (if b0 then 102956327 else 98932128) else (if b0 then 95131671 else 99101454)) else (if b1 then (if b0 then 105190656 else 99666268) else (if b0 then 97006619 else 102160770)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 104545580) else (if b0 then 100000000 else 100537942)) else (if b1 then (if b0 then 96444099 else 101111265) else (if b0 then 100385748 else 100846460))) else (if b2 then (if b1 then (if b0 then 100000000 else 104162903) else (if b0 then 100000000 else 106613382)) else (if b1 then (if b0 then 101333061 else 103682665) else (if b0 then 100986912 else 99893901)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101715683 else 100552399) else (if b0 then 103529350 else 101545491)) else (if b1 then (if b0 then 108889178 else 103478356) else (if b0 then 102456980 else 102546943))) else (if b2 then (if b1 then (if b0 then 103791946 else 103645118) else (if b0 then 98829952 else 98321896)) else (if b1 then (if b0 then 105571634 else 105064237) else (if b0 then 101198934 else 103006967))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 105092445) else (if b0 then 100000000 else 108970799)) else (if b1 then (if b0 then 107114493 else 101844508) else (if b0 then 102986797 else 102788910))) else (if b2 then (if b1 then (if b0 then 100000000 else 97509850) else (if b0 then 100000000 else 103510413)) else (if b1 then (if b0 then 101206463 else 104296515) else (if b0 then 100398220 else 104197725)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97694322 else 97869057) else (if b0 then 98788123 else 102728863)) else (if b1 then (if b0 then 103478356 else 110432784) else (if b0 then 100164990 else 99572641))) else (if b2 then (if b1 then (if b0 then 103415544 else 103916639) else (if b0 then 88516797 else 98404915)) else (if b1 then (if b0 then 99848647 else 100174031) else (if b0 then 104970661 else 98142103)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98929934) else (if b0 then 100000000 else 97807569)) else (if b1 then (if b0 then 94268331 else 98937060) else (if b0 then 101256930 else 99810165))) else (if b2 then (if b1 then (if b0 then 100000000 else 103490723) else (if b0 then 100000000 else 105226177)) else (if b1 then (if b0 then 101544617 else 97293206) else (if b0 then 100949225 else 97386559)))) else (if b3 then (if b2 then (if b1 then (if b0 then 103304779 else 100502418) else (if b0 then 100079561 else 102161523)) else (if b1 then (if b0 then 102456980 else 100164990) else (if b0 then 104636405 else 98439561))) else (if b2 then (if b1 then (if b0 then 102230117 else 101139011) else (if b0 then 104042007 else 97012471)) else (if b1 then (if b0 then 103352109 else 103504763) else (if b0 then 98271977 else 102330401))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 101986294) else (if b0 then 100000000 else 99700381)) else (if b1 then (if b0 then 102515358 else 103725885) else (if b0 then 98975611 else 101259669))) else (if b2 then (if b1 then (if b0 then 100000000 else 99121548) else (if b0 then 100000000 else 97816140)) else (if b1 then (if b0 then 98577617 else 103297602) else (if b0 then 98471801 else 99496729)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98991767 else 100344649) else (if b0 then 101486583 else 97996842)) else (if b1 then (if b0 then 102546943 else 99572641) else (if b0 then 98439561 else 104160370))) else (if b2 then (if b1 then (if b0 then 100804255 else 101253815) else (if b0 then 97619592 else 100766941)) else (if b1 then (if b0 then 100358808 else 100296198) else (if b0 then 101009162 else 101382349)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102754157) else (if b0 then 100000000 else 100208988)) else (if b1 then (if b0 then 102350617 else 102135998) else (if b0 then 103371268 else 102112528))) else (if b2 then (if b1 then (if b0 then 100000000 else 98612320) else (if b0 then 100000000 else 100918467)) else (if b1 then (if b0 then 99605249 else 103476163) else (if b0 then 103054694 else 99403209)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100809022 else 99701676) else (if b0 then 101070223 else 102956327)) else (if b1 then (if b0 then 103791946 else 103415544) else (if b0 then 102230117 else 100804255))) else (if b2 then (if b1 then (if b0 then 105857624 else 102160663) else (if b0 then 95644073 else 96381451)) else (if b1 then (if b0 then 106314619 else 104274724) else (if b0 then 99175704 else 101835109))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100885657) else (if b0 then 100000000 else 101678129)) else (if b1 then (if b0 then 95515983 else 100196562) else (if b0 then 97638096 else 102722936))) else (if b2 then (if b1 then (if b0 then 100000000 else 101123959) else (if b0 then 100000000 else 101961277)) else (if b1 then (if b0 then 99643486 else 100763856) else (if b0 then 98128009 else 103369742)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102298135 else 100160157) else (if b0 then 103017251 else 98932128)) else (if b1 then (if b0 then 103645118 else 103916639) else (if b0 then 101139011 else 101253815))) else (if b2 then (if b1 then (if b0 then 102160663 else 105825924) else (if b0 then 102733558 else 96900044)) else (if b1 then (if b0 then 100034047 else 104286244) else (if b0 then 104835849 else 99803068)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 88946905) else (if b0 then 100000000 else 85494621)) else (if b1 then (if b0 then 68566484 else 88472067) else (if b0 then 89957338 else 98139646))) else (if b2 then (if b1 then (if b0 then 100000000 else 111819958) else (if b0 then 100000000 else 104622689)) else (if b1 then (if b0 then 100552067 else 88740127) else (if b0 then 95279265 else 100699923)))) else (if b3 then (if b2 then (if b1 then (if b0 then 110708394 else 105081608) else (if b0 then 108059387 else 95131671)) else (if b1 then (if b0 then 98829952 else 88516797) else (if b0 then 104042007 else 97619592))) else (if b2 then (if b1 then (if b0 then 95644073 else 102733558) else (if b0 then 134498214 else 99583948)) else (if b1 then (if b0 then 102000007 else 108409661) else (if b0 then 102023753 else 100865111))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100034522) else (if b0 then 100000000 else 101066060)) else (if b1 then (if b0 then 99242762 else 97800354) else (if b0 then 99826510 else 100010848))) else (if b2 then (if b1 then (if b0 then 100000000 else 101551268) else (if b0 then 100000000 else 102532910)) else (if b1 then (if b0 then 100700581 else 99874350) else (if b0 then 95779203 else 99281342)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97087531 else 101115196) else (if b0 then 100747859 else 99101454)) else (if b1 then (if b0 then 98321896 else 98404915) else (if b0 then 97012471 else 100766941))) else (if b2 then (if b1 then (if b0 then 96381451 else 96900044) else (if b0 then 99583948 else 108731948)) else (if b1 then (if b0 then 100247252 else 94819524) else (if b0 then 102963995 else 99224269)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103225135) else (if b0 then 100000000 else 97488129)) else (if b1 then (if b0 then 92649383 else 97643204) else (if b0 then 104047602 else 102402380))) else (if b2 then (if b1 then (if b0 then 100000000 else 103527980) else (if b0 then 100000000 else 106933690)) else (if b1 then (if b0 then 99772486 else 101810629) else (if b0 then 103598340 else 95807290)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102914441 else 102120691) else (if b0 then 106640134 else 105190656)) else (if b1 then (if b0 then 105571634 else 99848647) else (if b0 then 103352109 else 100358808))) else (if b2 then (if b1 then (if b0 then 106314619 else 100034047) else (if b0 then 102000007 else 100247252)) else (if b1 then (if b0 then 114431834 else 105458067) else (if b0 then 97567232 else 104592260))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 97640846) else (if b0 then 100000000 else 91325403)) else (if b1 then (if b0 then 93419550 else 97974520) else (if b0 then 98605930 else 98743668))) else (if b2 then (if b1 then (if b0 then 100000000 else 102972978) else (if b0 then 100000000 else 100439133)) else (if b1 then (if b0 then 101784171 else 102516055) else (if b0 then 102088186 else 104072455)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104196749 else 100918375) else (if b0 then 100833244 else 99666268)) else (if b1 then (if b0 then 105064237 else 100174031) else (if b0 then 103504763 else 100296198))) else (if b2 then (if b1 then (if b0 then 104274724 else 104286244) else (if b0 then 108409661 else 94819524)) else (if b1 then (if b0 then 105458067 else 110162323) else (if b0 then 101359624 else 100102445)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98922733) else (if b0 then 100000000 else 101390049)) else (if b1 then (if b0 then 97864574 else 97908164) else (if b0 then 96936803 else 101885261))) else (if b2 then (if b1 then (if b0 then 100000000 else 100684024) else (if b0 then 100000000 else 101465068)) else (if b1 then (if b0 then 101498337 else 102158348) else (if b0 then 94058470 else 107588591)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99119936 else 100167474) else (if b0 then 100213192 else 97006619)) else (if b1 then (if b0 then 101198934 else 104970661) else (if b0 then 98271977 else 101009162))) else (if b2 then (if b1 then (if b0 then 99175704 else 104835849) else (if b0 then 102023753 else 102963995)) else (if b1 then (if b0 then 97567232 else 101359624) else (if b0 then 110412685 else 95989591))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102978335) else (if b0 then 100000000 else 101916676)) else (if b1 then (if b0 then 94674059 else 101569173) else (if b0 then 101089551 else 102299771))) else (if b2 then (if b1 then (if b0 then 100000000 else 102731460) else (if b0 then 100000000 else 104867614)) else (if b1 then (if b0 then 98184244 else 97590481) else (if b0 then 100788278 else 92878885)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102416791 else 101203134) else (if b0 then 105134744 else 102160770)) else (if b1 then (if b0 then 103006967 else 98142103) else (if b0 then 102330401 else 101382349))) else (if b2 then (if b1 then (if b0 then 101835109 else 99803068) else (if b0 then 100865111 else 99224269)) else (if b1 then (if b0 then 104592260 else 100102445) else (if b0 then 95989591 else 105332226)))))))
private lemma checkQ2_5_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift5 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨5, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨5, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨5, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨5, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨5, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨5, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

private def q2DotShift6 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 110702458) else (if b0 then 100000000 else 98964665)) else (if b1 then (if b0 then 103781111 else 112507649) else (if b0 then 94653150 else 96929753))) else (if b2 then (if b1 then (if b0 then 100000000 else 97132052) else (if b0 then 100000000 else 90437443)) else (if b1 then (if b0 then 95776782 else 81415671) else (if b0 then 86219309 else 89531796)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100882971 else 104803607) else (if b0 then 105619416 else 105651089)) else (if b1 then (if b0 then 102740270 else 106477144) else (if b0 then 101576669 else 103162778))) else (if b2 then (if b1 then (if b0 then 91347700 else 98245167) else (if b0 then 91462599 else 100178021)) else (if b1 then (if b0 then 100565614 else 88389155) else (if b0 then 100980199 else 90865364)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98964665) else (if b0 then 100000000 else 111262697)) else (if b1 then (if b0 then 106665028 else 100626495) else (if b0 then 98173110 else 102527580))) else (if b2 then (if b1 then (if b0 then 100000000 else 95825095) else (if b0 then 100000000 else 108717202)) else (if b1 then (if b0 then 99803911 else 127094303) else (if b0 then 99606242 else 118102657)))) else (if b3 then (if b2 then (if b1 then (if b0 then 95904743 else 87442177) else (if b0 then 94431795 else 93332736)) else (if b1 then (if b0 then 102621922 else 90233061) else (if b0 then 101801408 else 99655536))) else (if b2 then (if b1 then (if b0 then 93461445 else 80563709) else (if b0 then 90701506 else 77597986)) else (if b1 then (if b0 then 104030226 else 101384346) else (if b0 then 101836504 else 101725647)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103781111) else (if b0 then 100000000 else 106665028)) else (if b1 then (if b0 then 130975264 else 90831021) else (if b0 then 91723951 else 93355596))) else (if b2 then (if b1 then (if b0 then 100000000 else 88282796) else (if b0 then 100000000 else 87909531)) else (if b1 then (if b0 then 106984940 else 135919163) else (if b0 then 103079762 else 99238012)))) else (if b3 then (if b2 then (if b1 then (if b0 then 75410185 else 82013900) else (if b0 then 88111471 else 90689663)) else (if b1 then (if b0 then 102295539 else 88729310) else (if b0 then 102793236 else 100270749))) else (if b2 then (if b1 then (if b0 then 75041978 else 72577701) else (if b0 then 75515866 else 74505927)) else (if b1 then (if b0 then 108739153 else 99319449) else (if b0 then 108084338 else 106328610))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 112507649) else (if b0 then 100000000 else 100626495)) else (if b1 then (if b0 then 90831021 else 148566352) else (if b0 then 100031114 else 103736268))) else (if b2 then (if b1 then (if b0 then 100000000 else 95755116) else (if b0 then 100000000 else 86326112)) else (if b1 then (if b0 then 69683400 else 34532580) else (if b0 then 69953518 else 97609174)))) else (if b3 then (if b2 then (if b1 then (if b0 then 135136476 else 125255223) else (if b0 then 120113041 else 118869424)) else (if b1 then (if b0 then 102623755 else 127945395) else (if b0 then 101904020 else 114226434))) else (if b2 then (if b1 then (if b0 then 96908860 else 105255817) else (if b0 then 100920358 else 101171548)) else (if b1 then (if b0 then 93412188 else 73604004) else (if b0 then 83836079 else 67363060)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 94653150) else (if b0 then 100000000 else 98173110)) else (if b1 then (if b0 then 91723951 else 100031114) else (if b0 then 110225550 else 102622653))) else (if b2 then (if b1 then (if b0 then 100000000 else 106610936) else (if b0 then 100000000 else 103985465)) else (if b1 then (if b0 then 95444550 else 88170766) else (if b0 then 108111018 else 102122287)))) else (if b3 then (if b2 then (if b1 then (if b0 then 108692820 else 106710327) else (if b0 then 100237772 else 99986377)) else (if b1 then (if b0 then 98460577 else 102281618) else (if b0 then 94891514 else 98692278))) else (if b2 then (if b1 then (if b0 then 110116469 else 111561558) else (if b0 then 113324443 else 110146601)) else (if b1 then (if b0 then 97264707 else 101331628) else (if b0 then 88723834 else 95511358))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 96929753) else (if b0 then 100000000 else 102527580)) else (if b1 then (if b0 then 93355596 else 103736268) else (if b0 then 102622653 else 105424060))) else (if b2 then (if b1 then (if b0 then 100000000 else 102092131) else (if b0 then 100000000 else 107528513)) else (if b1 then (if b0 then 96804069 else 100225392) else (if b0 then 100876090 else 109111769)))) else (if b3 then (if b2 then (if b1 then (if b0 then 106882624 else 99967568) else (if b0 then 100650020 else 99390277)) else (if b1 then (if b0 then 101572998 else 99064758) else (if b0 then 101768443 else 102555159))) else (if b2 then (if b1 then (if b0 then 105981895 else 100800836) else (if b0 then 105238652 else 98405882)) else (if b1 then (if b0 then 99236790 else 101461022) else (if b0 then 96258644 else 98427586)))))))
  else
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 97132052) else (if b0 then 100000000 else 95825095)) else (if b1 then (if b0 then 88282796 else 95755116) else (if b0 then 106610936 else 102092131))) else (if b2 then (if b1 then (if b0 then 100000000 else 113365974) else (if b0 then 100000000 else 105301854)) else (if b1 then (if b0 then 101098976 else 83459825) else (if b0 then 110177667 else 93056405)))) else (if b3 then (if b2 then (if b1 then (if b0 then 104084631 else 107269543) else (if b0 then 99444291 else 99373760)) else (if b1 then (if b0 then 101771489 else 101308189) else (if b0 then 94942351 else 101740232))) else (if b2 then (if b1 then (if b0 then 112174009 else 118446420) else (if b0 then 115863262 else 119591376)) else (if b1 then (if b0 then 93901700 else 99892922) else (if b0 then 91099427 else 94566008)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 90437443) else (if b0 then 100000000 else 108717202)) else (if b1 then (if b0 then 87909531 else 86326112) else (if b0 then 103985465 else 107528513))) else (if b2 then (if b1 then (if b0 then 100000000 else 105301854) else (if b0 then 100000000 else 127844489)) else (if b1 then (if b0 then 107995858 else 137055891) else (if b0 then 109234440 else 125038934)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97908023 else 85681621) else (if b0 then 94125345 else 90823999)) else (if b1 then (if b0 then 99503097 else 81873949) else (if b0 then 99987447 else 93449269))) else (if b2 then (if b1 then (if b0 then 113325300 else 93919301) else (if b0 then 106291428 else 90289420)) else (if b1 then (if b0 then 102936131 else 114841175) else (if b0 then 104282331 else 112677559)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 95776782) else (if b0 then 100000000 else 99803911)) else (if b1 then (if b0 then 106984940 else 69683400) else (if b0 then 95444550 else 96804069))) else (if b2 then (if b1 then (if b0 then 100000000 else 101098976) else (if b0 then 100000000 else 107995858)) else (if b1 then (if b0 then 121912126 else 143551189) else (if b0 then 114267415 else 99323945)))) else (if b3 then (if b2 then (if b1 then (if b0 then 74295067 else 81937261) else (if b0 then 87863029 else 88380532)) else (if b1 then (if b0 then 100463603 else 81760389) else (if b0 then 101484291 else 90884306))) else (if b2 then (if b1 then (if b0 then 98701117 else 93663310) else (if b0 then 94393380 else 97436536)) else (if b1 then (if b0 then 105087104 else 115317576) else (if b0 then 115246341 else 122117806))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 81415671) else (if b0 then 100000000 else 127094303)) else (if b1 then (if b0 then 135919163 else 34532580) else (if b0 then 88170766 else 100225392))) else (if b2 then (if b1 then (if b0 then 100000000 else 83459825) else (if b0 then 100000000 else 137055891)) else (if b1 then (if b0 then 143551189 else 273258785) else (if b0 then 131040934 else 151686922)))) else (if b3 then (if b2 then (if b1 then (if b0 then 37010627 else 27503541) else (if b0 then 61023902 else 59735595)) else (if b1 then (if b0 then 98966079 else 34815556) else (if b0 then 108561342 else 78095946))) else (if b2 then (if b1 then (if b0 then 81632204 else 32513116) else (if b0 then 63648897 else 30293861)) else (if b1 then (if b0 then 125493414 else 144386429) else (if b0 then 139420950 else 159703561)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 86219309) else (if b0 then 100000000 else 99606242)) else (if b1 then (if b0 then 103079762 else 69953518) else (if b0 then 108111018 else 100876090))) else (if b2 then (if b1 then (if b0 then 100000000 else 110177667) else (if b0 then 100000000 else 109234440)) else (if b1 then (if b0 then 114267415 else 131040934) else (if b0 then 131416263 else 103029906)))) else (if b3 then (if b2 then (if b1 then (if b0 then 84239340 else 89371479) else (if b0 then 83495157 else 85213158)) else (if b1 then (if b0 then 100980049 else 85697243) else (if b0 then 95185033 else 95422318))) else (if b2 then (if b1 then (if b0 then 107547110 else 105284342) else (if b0 then 111475842 else 106523374)) else (if b1 then (if b0 then 98862631 else 115545073) else (if b0 then 96360359 else 112946545))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 89531796) else (if b0 then 100000000 else 118102657)) else (if b1 then (if b0 then 99238012 else 97609174) else (if b0 then 102122287 else 109111769))) else (if b2 then (if b1 then (if b0 then 100000000 else 93056405) else (if b0 then 100000000 else 125038934)) else (if b1 then (if b0 then 99323945 else 151686922) else (if b0 then 103029906 else 142867935)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102123988 else 79922090) else (if b0 then 92388898 else 89176373)) else (if b1 then (if b0 then 100545916 else 83362650) else (if b0 then 104029602 else 94910048))) else (if b2 then (if b1 then (if b0 then 101727852 else 72448518) else (if b0 then 94491733 else 64528236)) else (if b1 then (if b0 then 106163149 else 112497459) else (if b0 then 103274966 else 111035639)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100882971) else (if b0 then 100000000 else 95904743)) else (if b1 then (if b0 then 75410185 else 135136476) else (if b0 then 108692820 else 106882624))) else (if b2 then (if b1 then (if b0 then 100000000 else 104084631) else (if b0 then 100000000 else 97908023)) else (if b1 then (if b0 then 74295067 else 37010627) else (if b0 then 84239340 else 102123988)))) else (if b3 then (if b2 then (if b1 then (if b0 then 140572633 else 128780355) else (if b0 then 118799616 else 117097755)) else (if b1 then (if b0 then 98135809 else 126570352) else (if b0 then 97900264 else 108351052))) else (if b2 then (if b1 then (if b0 then 115449538 else 121699616) else (if b0 then 119706423 else 116656649)) else (if b1 then (if b0 then 89156974 else 86328259) else (if b0 then 81179320 else 76163015))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 104803607) else (if b0 then 100000000 else 87442177)) else (if b1 then (if b0 then 82013900 else 125255223) else (if b0 then 106710327 else 99967568))) else (if b2 then (if b1 then (if b0 then 100000000 else 107269543) else (if b0 then 100000000 else 85681621)) else (if b1 then (if b0 then 81937261 else 27503541) else (if b0 then 89371479 else 79922090)))) else (if b3 then (if b2 then (if b1 then (if b0 then 128780355 else 132030924) else (if b0 then 116556816 else 117214909)) else (if b1 then (if b0 then 98569199 else 128764426) else (if b0 then 95424186 else 107160483))) else (if b2 then (if b1 then (if b0 then 111177868 else 131302815) else (if b0 then 118957972 else 131764210)) else (if b1 then (if b0 then 88004745 else 84357955) else (if b0 then 83294285 else 77378062)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 105619416) else (if b0 then 100000000 else 94431795)) else (if b1 then (if b0 then 88111471 else 120113041) else (if b0 then 100237772 else 100650020))) else (if b2 then (if b1 then (if b0 then 100000000 else 99444291) else (if b0 then 100000000 else 94125345)) else (if b1 then (if b0 then 87863029 else 61023902) else (if b0 then 83495157 else 92388898)))) else (if b3 then (if b2 then (if b1 then (if b0 then 118799616 else 116556816) else (if b0 then 114507705 else 113517176)) else (if b1 then (if b0 then 96375741 else 114988240) else (if b0 then 99768583 else 104023421))) else (if b2 then (if b1 then (if b0 then 105521289 else 112323000) else (if b0 then 105302673 else 111450439)) else (if b1 then (if b0 then 96467342 else 90721890) else (if b0 then 96333508 else 88455615))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 105651089) else (if b0 then 100000000 else 93332736)) else (if b1 then (if b0 then 90689663 else 118869424) else (if b0 then 99986377 else 99390277))) else (if b2 then (if b1 then (if b0 then 100000000 else 99373760) else (if b0 then 100000000 else 90823999)) else (if b1 then (if b0 then 88380532 else 59735595) else (if b0 then 85213158 else 89176373)))) else (if b3 then (if b2 then (if b1 then (if b0 then 117097755 else 117214909) else (if b0 then 113517176 else 113253800)) else (if b1 then (if b0 then 96505895 else 116145676) else (if b0 then 99339374 else 104478588))) else (if b2 then (if b1 then (if b0 then 103801922 else 113043576) else (if b0 then 104957064 else 112842235)) else (if b1 then (if b0 then 95860359 else 90190660) else (if b0 then 95895354 else 88222154)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 102740270) else (if b0 then 100000000 else 102621922)) else (if b1 then (if b0 then 102295539 else 102623755) else (if b0 then 98460577 else 101572998))) else (if b2 then (if b1 then (if b0 then 100000000 else 101771489) else (if b0 then 100000000 else 99503097)) else (if b1 then (if b0 then 100463603 else 98966079) else (if b0 then 100980049 else 100545916)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98135809 else 98569199) else (if b0 then 96375741 else 96505895)) else (if b1 then (if b0 then 108487382 else 101179123) else (if b0 then 103069534 else 102613443))) else (if b2 then (if b1 then (if b0 then 95820170 else 97165116) else (if b0 then 98031442 else 97972694)) else (if b1 then (if b0 then 98325281 else 95446773) else (if b0 then 96919960 else 95816860))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 106477144) else (if b0 then 100000000 else 90233061)) else (if b1 then (if b0 then 88729310 else 127945395) else (if b0 then 102281618 else 99064758))) else (if b2 then (if b1 then (if b0 then 100000000 else 101308189) else (if b0 then 100000000 else 81873949)) else (if b1 then (if b0 then 81760389 else 34815556) else (if b0 then 85697243 else 83362650)))) else (if b3 then (if b2 then (if b1 then (if b0 then 126570352 else 128764426) else (if b0 then 114988240 else 116145676)) else (if b1 then (if b0 then 101179123 else 130444148) else (if b0 then 99061212 else 107388511))) else (if b2 then (if b1 then (if b0 then 103376993 else 121626425) else (if b0 then 111022827 else 121878168)) else (if b1 then (if b0 then 88761891 else 82877465) else (if b0 then 86700203 else 78791062)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 101576669) else (if b0 then 100000000 else 101801408)) else (if b1 then (if b0 then 102793236 else 101904020) else (if b0 then 94891514 else 101768443))) else (if b2 then (if b1 then (if b0 then 100000000 else 94942351) else (if b0 then 100000000 else 99987447)) else (if b1 then (if b0 then 101484291 else 108561342) else (if b0 then 95185033 else 104029602)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97900264 else 95424186) else (if b0 then 99768583 else 99339374)) else (if b1 then (if b0 then 103069534 else 99061212) else (if b0 then 106383061 else 101504599))) else (if b2 then (if b1 then (if b0 then 95895341 else 92277256) else (if b0 then 93484939 else 92039477)) else (if b1 then (if b0 then 102189265 else 100694769) else (if b0 then 105480085 else 103773691))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 103162778) else (if b0 then 100000000 else 99655536)) else (if b1 then (if b0 then 100270749 else 114226434) else (if b0 then 98692278 else 102555159))) else (if b2 then (if b1 then (if b0 then 100000000 else 101740232) else (if b0 then 100000000 else 93449269)) else (if b1 then (if b0 then 90884306 else 78095946) else (if b0 then 95422318 else 94910048)))) else (if b3 then (if b2 then (if b1 then (if b0 then 108351052 else 107160483) else (if b0 then 104023421 else 104478588)) else (if b1 then (if b0 then 102613443 else 107388511) else (if b0 then 101504599 else 111910909))) else (if b2 then (if b1 then (if b0 then 98154417 else 103315253) else (if b0 then 101628213 else 102421382)) else (if b1 then (if b0 then 96497115 else 90527143) else (if b0 then 92646099 else 86903851)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 91347700) else (if b0 then 100000000 else 93461445)) else (if b1 then (if b0 then 75041978 else 96908860) else (if b0 then 110116469 else 105981895))) else (if b2 then (if b1 then (if b0 then 100000000 else 112174009) else (if b0 then 100000000 else 113325300)) else (if b1 then (if b0 then 98701117 else 81632204) else (if b0 then 107547110 else 101727852)))) else (if b3 then (if b2 then (if b1 then (if b0 then 115449538 else 111177868) else (if b0 then 105521289 else 103801922)) else (if b1 then (if b0 then 95820170 else 103376993) else (if b0 then 95895341 else 98154417))) else (if b2 then (if b1 then (if b0 then 124541588 else 124962959) else (if b0 then 124447959 else 123402309)) else (if b1 then (if b0 then 93761325 else 107480630) else (if b0 then 93006751 else 100643718))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 98245167) else (if b0 then 100000000 else 80563709)) else (if b1 then (if b0 then 72577701 else 105255817) else (if b0 then 111561558 else 100800836))) else (if b2 then (if b1 then (if b0 then 100000000 else 118446420) else (if b0 then 100000000 else 93919301)) else (if b1 then (if b0 then 93663310 else 32513116) else (if b0 then 105284342 else 72448518)))) else (if b3 then (if b2 then (if b1 then (if b0 then 121699616 else 131302815) else (if b0 then 112323000 else 113043576)) else (if b1 then (if b0 then 97165116 else 121626425) else (if b0 then 92277256 else 103315253))) else (if b2 then (if b1 then (if b0 then 124962959 else 148280930) else (if b0 then 132833295 else 151387503)) else (if b1 then (if b0 then 86138065 else 95063953) else (if b0 then 84120219 else 86759212)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 91462599) else (if b0 then 100000000 else 90701506)) else (if b1 then (if b0 then 75515866 else 100920358) else (if b0 then 113324443 else 105238652))) else (if b2 then (if b1 then (if b0 then 100000000 else 115863262) else (if b0 then 100000000 else 106291428)) else (if b1 then (if b0 then 94393380 else 63648897) else (if b0 then 111475842 else 94491733)))) else (if b3 then (if b2 then (if b1 then (if b0 then 119706423 else 118957972) else (if b0 then 105302673 else 104957064)) else (if b1 then (if b0 then 98031442 else 111022827) else (if b0 then 93484939 else 101628213))) else (if b2 then (if b1 then (if b0 then 124447959 else 132833295) else (if b0 then 129975321 else 131976325)) else (if b1 then (if b0 then 89192660 else 102142933) else (if b0 then 84335785 else 92494087))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100178021) else (if b0 then 100000000 else 77597986)) else (if b1 then (if b0 then 74505927 else 101171548) else (if b0 then 110146601 else 98405882))) else (if b2 then (if b1 then (if b0 then 100000000 else 119591376) else (if b0 then 100000000 else 90289420)) else (if b1 then (if b0 then 97436536 else 30293861) else (if b0 then 106523374 else 64528236)))) else (if b3 then (if b2 then (if b1 then (if b0 then 116656649 else 131764210) else (if b0 then 111450439 else 112842235)) else (if b1 then (if b0 then 97972694 else 121878168) else (if b0 then 92039477 else 102421382))) else (if b2 then (if b1 then (if b0 then 123402309 else 151387503) else (if b0 then 131976325 else 156725453)) else (if b1 then (if b0 then 85960019 else 94583549) else (if b0 then 86014267 else 88022845)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100565614) else (if b0 then 100000000 else 104030226)) else (if b1 then (if b0 then 108739153 else 93412188) else (if b0 then 97264707 else 99236790))) else (if b2 then (if b1 then (if b0 then 100000000 else 93901700) else (if b0 then 100000000 else 102936131)) else (if b1 then (if b0 then 105087104 else 125493414) else (if b0 then 98862631 else 106163149)))) else (if b3 then (if b2 then (if b1 then (if b0 then 89156974 else 88004745) else (if b0 then 96467342 else 95860359)) else (if b1 then (if b0 then 98325281 else 88761891) else (if b0 then 102189265 else 96497115))) else (if b2 then (if b1 then (if b0 then 93761325 else 86138065) else (if b0 then 89192660 else 85960019)) else (if b1 then (if b0 then 107877680 else 104744374) else (if b0 then 107633976 else 108397230))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 88389155) else (if b0 then 100000000 else 101384346)) else (if b1 then (if b0 then 99319449 else 73604004) else (if b0 then 101331628 else 101461022))) else (if b2 then (if b1 then (if b0 then 100000000 else 99892922) else (if b0 then 100000000 else 114841175)) else (if b1 then (if b0 then 115317576 else 144386429) else (if b0 then 115545073 else 112497459)))) else (if b3 then (if b2 then (if b1 then (if b0 then 86328259 else 84357955) else (if b0 then 90721890 else 90190660)) else (if b1 then (if b0 then 95446773 else 82877465) else (if b0 then 100694769 else 90527143))) else (if b2 then (if b1 then (if b0 then 107480630 else 95063953) else (if b0 then 102142933 else 94583549)) else (if b1 then (if b0 then 104744374 else 120512704) else (if b0 then 110984718 else 123129454)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 100980199) else (if b0 then 100000000 else 101836504)) else (if b1 then (if b0 then 108084338 else 83836079) else (if b0 then 88723834 else 96258644))) else (if b2 then (if b1 then (if b0 then 100000000 else 91099427) else (if b0 then 100000000 else 104282331)) else (if b1 then (if b0 then 115246341 else 139420950) else (if b0 then 96360359 else 103274966)))) else (if b3 then (if b2 then (if b1 then (if b0 then 81179320 else 83294285) else (if b0 then 96333508 else 95895354)) else (if b1 then (if b0 then 96919960 else 86700203) else (if b0 then 105480085 else 92646099))) else (if b2 then (if b1 then (if b0 then 93006751 else 84120219) else (if b0 then 84335785 else 86014267)) else (if b1 then (if b0 then 107633976 else 110984718) else (if b0 then 122272151 else 120600089))))) else (if b4 then (if b3 then (if b2 then (if b1 then (if b0 then 100000000 else 90865364) else (if b0 then 100000000 else 101725647)) else (if b1 then (if b0 then 106328610 else 67363060) else (if b0 then 95511358 else 98427586))) else (if b2 then (if b1 then (if b0 then 100000000 else 94566008) else (if b0 then 100000000 else 112677559)) else (if b1 then (if b0 then 122117806 else 159703561) else (if b0 then 112946545 else 111035639)))) else (if b3 then (if b2 then (if b1 then (if b0 then 76163015 else 77378062) else (if b0 then 88455615 else 88222154)) else (if b1 then (if b0 then 95816860 else 78791062) else (if b0 then 103773691 else 86903851))) else (if b2 then (if b1 then (if b0 then 100643718 else 86759212) else (if b0 then 92494087 else 88022845)) else (if b1 then (if b0 then 108397230 else 123129454) else (if b0 then 120600089 else 131229064)))))))
private lemma checkQ2_6_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift6 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨6, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨6, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨6, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨6, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨6, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨6, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

private def q2DotShift7 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then 100000000 else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 117322170)) else (if b1 then 100000000 else (if b0 then 106767311 else 118126348))) else (if b2 then (if b1 then (if b0 then 100000000 else 112030420) else (if b0 then 100000000 else 108912554)) else (if b1 then (if b0 then 104301305 else 117702551) else (if b0 then 107622701 else 102262918)))) else (if b3 then (if b2 then (if b1 then (if b0 then 89928029 else 78463719) else (if b0 then 90984548 else 88373891)) else (if b1 then (if b0 then 98763958 else 88852427) else (if b0 then 96848375 else 102379422))) else (if b2 then (if b1 then (if b0 then 102759353 else 104609025) else (if b0 then 105177615 else 104554105)) else (if b1 then (if b0 then 99819548 else 97892525) else (if b0 then 96849966 else 80198335)))))))
    else
      (if a1 then 100000000 else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 106767311)) else (if b1 then 100000000 else (if b0 then 112759157 else 113788728))) else (if b2 then (if b1 then (if b0 then 100000000 else 106174466) else (if b0 then 100000000 else 114412176)) else (if b1 then (if b0 then 112351345 else 114321171) else (if b0 then 116535065 else 110133764)))) else (if b3 then (if b2 then (if b1 then (if b0 then 87761753 else 84702440) else (if b0 then 81274243 else 85146546)) else (if b1 then (if b0 then 102133186 else 102532585) else (if b0 then 97956956 else 108029638))) else (if b2 then (if b1 then (if b0 then 98497383 else 101005716) else (if b0 then 99181656 else 100250219)) else (if b1 then (if b0 then 99556286 else 100348117) else (if b0 then 98232691 else 94214639))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 118126348)) else (if b1 then 100000000 else (if b0 then 113788728 else 127788932))) else (if b2 then (if b1 then (if b0 then 100000000 else 115015999) else (if b0 then 100000000 else 111763596)) else (if b1 then (if b0 then 113721674 else 127990317) else (if b0 then 112255342 else 106571087)))) else (if b3 then (if b2 then (if b1 then (if b0 then 86279515 else 67285037) else (if b0 then 85607567 else 80580074)) else (if b1 then (if b0 then 99772564 else 85588786) else (if b0 then 97651839 else 108150097))) else (if b2 then (if b1 then (if b0 then 99998766 else 105846900) else (if b0 then 107280662 else 103081088)) else (if b1 then (if b0 then 99953899 else 97000489) else (if b0 then 96790328 else 78771348)))))))
  else
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 112030420)) else (if b1 then 100000000 else (if b0 then 106174466 else 115015999))) else (if b2 then (if b1 then (if b0 then 100000000 else 109680290) else (if b0 then 100000000 else 106916429)) else (if b1 then (if b0 then 105790197 else 115030145) else (if b0 then 106438375 else 102562458)))) else (if b3 then (if b2 then (if b1 then (if b0 then 92931476 else 81970546) else (if b0 then 92479944 else 89531385)) else (if b1 then (if b0 then 98499342 else 90939342) else (if b0 then 98371135 else 103198963))) else (if b2 then (if b1 then (if b0 then 100768221 else 103576849) else (if b0 then 104413593 else 103171956)) else (if b1 then (if b0 then 98680015 else 97815002) else (if b0 then 98604645 else 85720344)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 108912554)) else (if b1 then 100000000 else (if b0 then 114412176 else 111763596))) else (if b2 then (if b1 then (if b0 then 100000000 else 106916429) else (if b0 then 100000000 else 126324085)) else (if b1 then (if b0 then 110174818 else 112419198) else (if b0 then 128439695 else 118445550)))) else (if b3 then (if b2 then (if b1 then (if b0 then 80902144 else 88015717) else (if b0 then 68808931 else 80078420)) else (if b1 then (if b0 then 100925452 else 116486116) else (if b0 then 94523690 else 107321284))) else (if b2 then (if b1 then (if b0 then 97455614 else 99002193) else (if b0 then 97185405 else 103629089)) else (if b1 then (if b0 then 98583140 else 101504491) else (if b0 then 101545724 else 95995463)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 104301305)) else (if b1 then 100000000 else (if b0 then 112351345 else 113721674))) else (if b2 then (if b1 then (if b0 then 100000000 else 105790197) else (if b0 then 100000000 else 110174818)) else (if b1 then (if b0 then 114832668 else 114484509) else (if b0 then 112636671 else 107147294)))) else (if b3 then (if b2 then (if b1 then (if b0 then 92183751 else 84158830) else (if b0 then 85347397 else 86276100)) else (if b1 then (if b0 then 101989250 else 97819046) else (if b0 then 100382326 else 108950682))) else (if b2 then (if b1 then (if b0 then 97988360 else 101395365) else (if b0 then 99253930 else 99361457)) else (if b1 then (if b0 then 97946093 else 99519116) else (if b0 then 98193937 else 94646652))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 117702551)) else (if b1 then 100000000 else (if b0 then 114321171 else 127990317))) else (if b2 then (if b1 then (if b0 then 100000000 else 115030145) else (if b0 then 100000000 else 112419198)) else (if b1 then (if b0 then 114484509 else 128300984) else (if b0 then 113134452 else 107351239)))) else (if b3 then (if b2 then (if b1 then (if b0 then 85848764 else 67077589) else (if b0 then 84674913 else 79943646)) else (if b1 then (if b0 then 99753109 else 86291730) else (if b0 then 97667843 else 108709489))) else (if b2 then (if b1 then (if b0 then 99516377 else 105697977) else (if b0 then 107172573 else 102932282)) else (if b1 then (if b0 then 99702327 else 97006272) else (if b0 then 97057435 else 79431539)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 107622701)) else (if b1 then 100000000 else (if b0 then 116535065 else 112255342))) else (if b2 then (if b1 then (if b0 then 100000000 else 106438375) else (if b0 then 100000000 else 128439695)) else (if b1 then (if b0 then 112636671 else 113134452) else (if b0 then 131342061 else 120726942)))) else (if b3 then (if b2 then (if b1 then (if b0 then 79278889 else 87709896) else (if b0 then 65599320 else 78328099)) else (if b1 then (if b0 then 101696299 else 118990407) else (if b0 then 94488999 else 109092425))) else (if b2 then (if b1 then (if b0 then 96508021 else 98466989) else (if b0 then 96161672 else 102788566)) else (if b1 then (if b0 then 98539068 else 101961624) else (if b0 then 101569990 else 98064226))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 102262918)) else (if b1 then 100000000 else (if b0 then 110133764 else 106571087))) else (if b2 then (if b1 then (if b0 then 100000000 else 102562458) else (if b0 then 100000000 else 118445550)) else (if b1 then (if b0 then 107147294 else 107351239) else (if b0 then 120726942 else 116085853)))) else (if b3 then (if b2 then (if b1 then (if b0 then 85451112 else 94046711) else (if b0 then 77698867 else 86373850)) else (if b1 then (if b0 then 100868541 else 116440647) else (if b0 then 95779988 else 105886751))) else (if b2 then (if b1 then (if b0 then 95755862 else 98174347) else (if b0 then 98616195 else 101060263)) else (if b1 then (if b0 then 100391842 else 101523321) else (if b0 then 102911596 else 103409109)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 89928029)) else (if b1 then 100000000 else (if b0 then 87761753 else 86279515))) else (if b2 then (if b1 then (if b0 then 100000000 else 92931476) else (if b0 then 100000000 else 80902144)) else (if b1 then (if b0 then 92183751 else 85848764) else (if b0 then 79278889 else 85451112)))) else (if b3 then (if b2 then (if b1 then (if b0 then 125963207 else 114665207) else (if b0 then 122753782 else 112015281)) else (if b1 then (if b0 then 97251578 else 93459714) else (if b0 then 107538233 else 90132727))) else (if b2 then (if b1 then (if b0 then 101842539 else 99837671) else (if b0 then 100377770 else 101717258)) else (if b1 then (if b0 then 98315624 else 97853423) else (if b0 then 105636756 else 102976467))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 78463719)) else (if b1 then 100000000 else (if b0 then 84702440 else 67285037))) else (if b2 then (if b1 then (if b0 then 100000000 else 81970546) else (if b0 then 100000000 else 88015717)) else (if b1 then (if b0 then 84158830 else 67077589) else (if b0 then 87709896 else 94046711)))) else (if b3 then (if b2 then (if b1 then (if b0 then 114665207 else 138833953) else (if b0 then 114651588 else 121856225)) else (if b1 then (if b0 then 100685749 else 119592619) else (if b0 then 102233884 else 90766553))) else (if b2 then (if b1 then (if b0 then 99652294 else 92716709) else (if b0 then 90974733 else 96311166)) else (if b1 then (if b0 then 100583099 else 103962462) else (if b0 then 104031443 else 126032879)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 90984548)) else (if b1 then 100000000 else (if b0 then 81274243 else 85607567))) else (if b2 then (if b1 then (if b0 then 100000000 else 92479944) else (if b0 then 100000000 else 68808931)) else (if b1 then (if b0 then 85347397 else 84674913) else (if b0 then 65599320 else 77698867)))) else (if b3 then (if b2 then (if b1 then (if b0 then 122753782 else 114651588) else (if b0 then 137895563 else 124205772)) else (if b1 then (if b0 then 97875412 else 80446984) else (if b0 then 105860325 else 89658802))) else (if b2 then (if b1 then (if b0 then 103471691 else 101395785) else (if b0 then 104335900 else 96978677)) else (if b1 then (if b0 then 101697371 else 97903893) else (if b0 then 98887075 else 103257500))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 88373891)) else (if b1 then 100000000 else (if b0 then 85146546 else 80580074))) else (if b2 then (if b1 then (if b0 then 100000000 else 89531385) else (if b0 then 100000000 else 80078420)) else (if b1 then (if b0 then 86276100 else 79943646) else (if b0 then 78328099 else 86373850)))) else (if b3 then (if b2 then (if b1 then (if b0 then 112015281 else 121856225) else (if b0 then 124205772 else 122666359)) else (if b1 then (if b0 then 100459782 else 96257314) else (if b0 then 102281706 else 93038422))) else (if b2 then (if b1 then (if b0 then 102306460 else 97859329) else (if b0 then 97825735 else 95085954)) else (if b1 then (if b0 then 101692561 else 101389596) else (if b0 then 97312613 else 112071089)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 98763958)) else (if b1 then 100000000 else (if b0 then 102133186 else 99772564))) else (if b2 then (if b1 then (if b0 then 100000000 else 98499342) else (if b0 then 100000000 else 100925452)) else (if b1 then (if b0 then 101989250 else 99753109) else (if b0 then 101696299 else 100868541)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97251578 else 100685749) else (if b0 then 97875412 else 100459782)) else (if b1 then (if b0 then 102756154 else 101273616) else (if b0 then 100090804 else 102411043))) else (if b2 then (if b1 then (if b0 then 99159932 else 99330698) else (if b0 then 97732772 else 97506318)) else (if b1 then (if b0 then 100858472 else 101396437) else (if b0 then 97246770 else 102306185))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 88852427)) else (if b1 then 100000000 else (if b0 then 102532585 else 85588786))) else (if b2 then (if b1 then (if b0 then 100000000 else 90939342) else (if b0 then 100000000 else 116486116)) else (if b1 then (if b0 then 97819046 else 86291730) else (if b0 then 118990407 else 116440647)))) else (if b3 then (if b2 then (if b1 then (if b0 then 93459714 else 119592619) else (if b0 then 80446984 else 96257314)) else (if b1 then (if b0 then 101273616 else 135984384) else (if b0 then 96412185 else 99639171))) else (if b2 then (if b1 then (if b0 then 95572566 else 92661829) else (if b0 then 91568542 else 100834683)) else (if b1 then (if b0 then 100875756 else 104545361) else (if b0 then 107794789 else 120589080)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 96848375)) else (if b1 then 100000000 else (if b0 then 97956956 else 97651839))) else (if b2 then (if b1 then (if b0 then 100000000 else 98371135) else (if b0 then 100000000 else 94523690)) else (if b1 then (if b0 then 100382326 else 97667843) else (if b0 then 94488999 else 95779988)))) else (if b3 then (if b2 then (if b1 then (if b0 then 107538233 else 102233884) else (if b0 then 105860325 else 102281706)) else (if b1 then (if b0 then 100090804 else 96412185) else (if b0 then 103424263 else 99042709))) else (if b2 then (if b1 then (if b0 then 99060220 else 100069578) else (if b0 then 99832257 else 99975499)) else (if b1 then (if b0 then 98522489 else 99273530) else (if b0 then 101005308 else 100476913))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 102379422)) else (if b1 then 100000000 else (if b0 then 108029638 else 108150097))) else (if b2 then (if b1 then (if b0 then 100000000 else 103198963) else (if b0 then 100000000 else 107321284)) else (if b1 then (if b0 then 108950682 else 108709489) else (if b0 then 109092425 else 105886751)))) else (if b3 then (if b2 then (if b1 then (if b0 then 90132727 else 90766553) else (if b0 then 89658802 else 93038422)) else (if b1 then (if b0 then 102411043 else 99639171) else (if b0 then 99042709 else 107680099))) else (if b2 then (if b1 then (if b0 then 97136192 else 100283243) else (if b0 then 98977209 else 97231713)) else (if b1 then (if b0 then 99058279 else 100659263) else (if b0 then 96579386 else 99297072)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 102759353)) else (if b1 then 100000000 else (if b0 then 98497383 else 99998766))) else (if b2 then (if b1 then (if b0 then 100000000 else 100768221) else (if b0 then 100000000 else 97455614)) else (if b1 then (if b0 then 97988360 else 99516377) else (if b0 then 96508021 else 95755862)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101842539 else 99652294) else (if b0 then 103471691 else 102306460)) else (if b1 then (if b0 then 99159932 else 95572566) else (if b0 then 99060220 else 97136192))) else (if b2 then (if b1 then (if b0 then 107322404 else 101029257) else (if b0 then 99647030 else 103176991)) else (if b1 then (if b0 then 101058781 else 99602716) else (if b0 then 98528299 else 95450346))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 104609025)) else (if b1 then 100000000 else (if b0 then 101005716 else 105846900))) else (if b2 then (if b1 then (if b0 then 100000000 else 103576849) else (if b0 then 100000000 else 99002193)) else (if b1 then (if b0 then 101395365 else 105697977) else (if b0 then 98466989 else 98174347)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99837671 else 92716709) else (if b0 then 101395785 else 97859329)) else (if b1 then (if b0 then 99330698 else 92661829) else (if b0 then 100069578 else 100283243))) else (if b2 then (if b1 then (if b0 then 101029257 else 102068493) else (if b0 then 102637426 else 100697541)) else (if b1 then (if b0 then 100075740 else 98740023) else (if b0 then 98885655 else 93288100)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 105177615)) else (if b1 then 100000000 else (if b0 then 99181656 else 107280662))) else (if b2 then (if b1 then (if b0 then 100000000 else 104413593) else (if b0 then 100000000 else 97185405)) else (if b1 then (if b0 then 99253930 else 107172573) else (if b0 then 96161672 else 98616195)))) else (if b3 then (if b2 then (if b1 then (if b0 then 100377770 else 90974733) else (if b0 then 104335900 else 97825735)) else (if b1 then (if b0 then 97732772 else 91568542) else (if b0 then 99832257 else 98977209))) else (if b2 then (if b1 then (if b0 then 99647030 else 102637426) else (if b0 then 106392352 else 101850573)) else (if b1 then (if b0 then 100955844 else 97675002) else (if b0 then 101285733 else 92933810))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 104554105)) else (if b1 then 100000000 else (if b0 then 100250219 else 103081088))) else (if b2 then (if b1 then (if b0 then 100000000 else 103171956) else (if b0 then 100000000 else 103629089)) else (if b1 then (if b0 then 99361457 else 102932282) else (if b0 then 102788566 else 101060263)))) else (if b3 then (if b2 then (if b1 then (if b0 then 101717258 else 96311166) else (if b0 then 96978677 else 95085954)) else (if b1 then (if b0 then 97506318 else 100834683) else (if b0 then 99975499 else 97231713))) else (if b2 then (if b1 then (if b0 then 103176991 else 100697541) else (if b0 then 101850573 else 108037422)) else (if b1 then (if b0 then 98737975 else 98392463) else (if b0 then 104240331 else 93651536)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 99819548)) else (if b1 then 100000000 else (if b0 then 99556286 else 99953899))) else (if b2 then (if b1 then (if b0 then 100000000 else 98680015) else (if b0 then 100000000 else 98583140)) else (if b1 then (if b0 then 97946093 else 99702327) else (if b0 then 98539068 else 100391842)))) else (if b3 then (if b2 then (if b1 then (if b0 then 98315624 else 100583099) else (if b0 then 101697371 else 101692561)) else (if b1 then (if b0 then 100858472 else 100875756) else (if b0 then 98522489 else 99058279))) else (if b2 then (if b1 then (if b0 then 101058781 else 100075740) else (if b0 then 100955844 else 98737975)) else (if b1 then (if b0 then 103563989 else 100681659) else (if b0 then 99178761 else 101440921))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 97892525)) else (if b1 then 100000000 else (if b0 then 100348117 else 97000489))) else (if b2 then (if b1 then (if b0 then 100000000 else 97815002) else (if b0 then 100000000 else 101504491)) else (if b1 then (if b0 then 99519116 else 97006272) else (if b0 then 101961624 else 101523321)))) else (if b3 then (if b2 then (if b1 then (if b0 then 97853423 else 103962462) else (if b0 then 97903893 else 101389596)) else (if b1 then (if b0 then 101396437 else 104545361) else (if b0 then 99273530 else 100659263))) else (if b2 then (if b1 then (if b0 then 99602716 else 98740023) else (if b0 then 97675002 else 98392463)) else (if b1 then (if b0 then 100681659 else 101382806) else (if b0 then 98974487 else 103993222)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 96849966)) else (if b1 then 100000000 else (if b0 then 98232691 else 96790328))) else (if b2 then (if b1 then (if b0 then 100000000 else 98604645) else (if b0 then 100000000 else 101545724)) else (if b1 then (if b0 then 98193937 else 97057435) else (if b0 then 101569990 else 102911596)))) else (if b3 then (if b2 then (if b1 then (if b0 then 105636756 else 104031443) else (if b0 then 98887075 else 97312613)) else (if b1 then (if b0 then 97246770 else 107794789) else (if b0 then 101005308 else 96579386))) else (if b2 then (if b1 then (if b0 then 98528299 else 98885655) else (if b0 then 101285733 else 104240331)) else (if b1 then (if b0 then 99178761 else 98974487) else (if b0 then 107497788 else 102956884))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 80198335)) else (if b1 then 100000000 else (if b0 then 94214639 else 78771348))) else (if b2 then (if b1 then (if b0 then 100000000 else 85720344) else (if b0 then 100000000 else 95995463)) else (if b1 then (if b0 then 94646652 else 79431539) else (if b0 then 98064226 else 103409109)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102976467 else 126032879) else (if b0 then 103257500 else 112071089)) else (if b1 then (if b0 then 102306185 else 120589080) else (if b0 then 100476913 else 99297072))) else (if b2 then (if b1 then (if b0 then 95450346 else 93288100) else (if b0 then 92933810 else 93651536)) else (if b1 then (if b0 then 101440921 else 103993222) else (if b0 then 102956884 else 127023336)))))))
private lemma checkQ2_7_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift7 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨7, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨7, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨7, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨7, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨7, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨7, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

private def q2DotShift8 (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : Bool) : ℕ :=
  if a4 then
  if a3 then
    if a2 then
      (if a1 then 100000000 else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 128544999)) else (if b1 then 100000000 else (if b0 then 127634707 else 116012117))) else (if b2 then (if b1 then (if b0 then 100000000 else 122293017) else (if b0 then 100000000 else 110380341)) else (if b1 then (if b0 then 124820468 else 114658488) else (if b0 then 130152787 else 145816681)))) else (if b3 then (if b2 then (if b1 then (if b0 then 53973376 else 73822954) else (if b0 then 74362543 else 75287453)) else (if b1 then (if b0 then 97347164 else 65253390) else (if b0 then 105080361 else 85337675))) else (if b2 then (if b1 then (if b0 then 93639711 else 104504991) else (if b0 then 69540577 else 93655429)) else (if b1 then (if b0 then 109302084 else 98761909) else (if b0 then 110400053 else 96091993)))))))
    else
      (if a1 then 100000000 else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 127634707)) else (if b1 then 100000000 else (if b0 then 130754102 else 116884169))) else (if b2 then (if b1 then (if b0 then 100000000 else 113132721) else (if b0 then 100000000 else 102923729)) else (if b1 then (if b0 then 118894962 else 109399111) else (if b0 then 120733453 else 137432593)))) else (if b3 then (if b2 then (if b1 then (if b0 then 61195200 else 78990285) else (if b0 then 79305151 else 80085508)) else (if b1 then (if b0 then 99084083 else 73252067) else (if b0 then 107743464 else 90391848))) else (if b2 then (if b1 then (if b0 then 93054061 else 102305037) else (if b0 then 65273609 else 87941355)) else (if b1 then (if b0 then 106643980 else 94574824) else (if b0 then 105568432 else 93016732))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 116012117)) else (if b1 then 100000000 else (if b0 then 116884169 else 118206774))) else (if b2 then (if b1 then (if b0 then 100000000 else 113701167) else (if b0 then 100000000 else 97545551)) else (if b1 then (if b0 then 116512423 else 119199253) else (if b0 then 117806755 else 130782108)))) else (if b3 then (if b2 then (if b1 then (if b0 then 70965624 else 74593493) else (if b0 then 91414069 else 83716627)) else (if b1 then (if b0 then 101856197 else 81976611) else (if b0 then 104371053 else 100639004))) else (if b2 then (if b1 then (if b0 then 93881308 else 100962534) else (if b0 then 82281841 else 90139751)) else (if b1 then (if b0 then 106621121 else 99106297) else (if b0 then 107001982 else 100427646)))))))
  else
    if a2 then
      (if a1 then (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 122293017)) else (if b1 then 100000000 else (if b0 then 113132721 else 113701167))) else (if b2 then (if b1 then (if b0 then 100000000 else 145929411) else (if b0 then 100000000 else 125893928)) else (if b1 then (if b0 then 141439352 else 133225646) else (if b0 then 149132683 else 162935625)))) else (if b3 then (if b2 then (if b1 then (if b0 then 39549366 else 59676123) else (if b0 then 66132188 else 66204946)) else (if b1 then (if b0 then 99392117 else 52524988) else (if b0 then 102015628 else 79359081))) else (if b2 then (if b1 then (if b0 then 83772014 else 109382897) else (if b0 then 88463914 else 110148657)) else (if b1 then (if b0 then 119315621 else 107903361) else (if b0 then 124138891 else 110598531)))))) else (if a0 then 100000000 else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 110380341)) else (if b1 then 100000000 else (if b0 then 102923729 else 97545551))) else (if b2 then (if b1 then (if b0 then 100000000 else 125893928) else (if b0 then 100000000 else 126134445)) else (if b1 then (if b0 then 120481471 else 106648716) else (if b0 then 126029537 else 129242117)))) else (if b3 then (if b2 then (if b1 then (if b0 then 71021663 else 89835429) else (if b0 then 73464852 else 83233847)) else (if b1 then (if b0 then 101831027 else 72939711) else (if b0 then 98767292 else 76891168))) else (if b2 then (if b1 then (if b0 then 85078860 else 109356391) else (if b0 then 97120671 else 115550038)) else (if b1 then (if b0 then 110633059 else 105841352) else (if b0 then 110293781 else 104480965)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 124820468)) else (if b1 then 100000000 else (if b0 then 118894962 else 116512423))) else (if b2 then (if b1 then (if b0 then 100000000 else 141439352) else (if b0 then 100000000 else 120481471)) else (if b1 then (if b0 then 140065020 else 131718123) else (if b0 then 145458712 else 161997573)))) else (if b3 then (if b2 then (if b1 then (if b0 then 39450054 else 59903093) else (if b0 then 67601941 else 67141410)) else (if b1 then (if b0 then 99576716 else 54741599) else (if b0 then 104993326 else 82577228))) else (if b2 then (if b1 then (if b0 then 83724897 else 107629266) else (if b0 then 81655773 else 104432086)) else (if b1 then (if b0 then 118341310 else 104300409) else (if b0 then 122312156 else 108069442))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 114658488)) else (if b1 then 100000000 else (if b0 then 109399111 else 119199253))) else (if b2 then (if b1 then (if b0 then 100000000 else 133225646) else (if b0 then 100000000 else 106648716)) else (if b1 then (if b0 then 131718123 else 137682599) else (if b0 then 136104892 else 148962672)))) else (if b3 then (if b2 then (if b1 then (if b0 then 54721893 else 58362752) else (if b0 then 85982625 else 74742947)) else (if b1 then (if b0 then 97679477 else 68483629) else (if b0 then 102632207 else 98539130))) else (if b2 then (if b1 then (if b0 then 94807391 else 102556022) else (if b0 then 93501191 else 99074608)) else (if b1 then (if b0 then 113964037 else 105763488) else (if b0 then 121045266 else 111104060)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 130152787)) else (if b1 then 100000000 else (if b0 then 120733453 else 117806755))) else (if b2 then (if b1 then (if b0 then 100000000 else 149132683) else (if b0 then 100000000 else 126029537)) else (if b1 then (if b0 then 145458712 else 136104892) else (if b0 then 158330984 else 172431535)))) else (if b3 then (if b2 then (if b1 then (if b0 then 29803929 else 53500465) else (if b0 then 62503146 else 61308682)) else (if b1 then (if b0 then 93487754 else 44287169) else (if b0 then 98615578 else 77476532))) else (if b2 then (if b1 then (if b0 then 90975100 else 106972107) else (if b0 then 80296236 else 106406571)) else (if b1 then (if b0 then 117913359 else 109196543) else (if b0 then 125756109 else 107866158))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 145816681)) else (if b1 then 100000000 else (if b0 then 137432593 else 130782108))) else (if b2 then (if b1 then (if b0 then 100000000 else 162935625) else (if b0 then 100000000 else 129242117)) else (if b1 then (if b0 then 161997573 else 148962672) else (if b0 then 172431535 else 201318495)))) else (if b3 then (if b2 then (if b1 then (if b0 then 1369269 else 34515745) else (if b0 then 48466164 else 45837745)) else (if b1 then (if b0 then 98088716 else 25899962) else (if b0 then 107900909 else 72256702))) else (if b2 then (if b1 then (if b0 then 78386256 else 111779821) else (if b0 then 61965328 else 100876501)) else (if b1 then (if b0 then 127014179 else 105615344) else (if b0 then 132713590 else 107843292)))))))
else
  if a3 then
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 53973376)) else (if b1 then 100000000 else (if b0 then 61195200 else 70965624))) else (if b2 then (if b1 then (if b0 then 100000000 else 39549366) else (if b0 then 100000000 else 71021663)) else (if b1 then (if b0 then 39450054 else 54721893) else (if b0 then 29803929 else 1369269)))) else (if b3 then (if b2 then (if b1 then (if b0 then 197051998 else 162009816) else (if b0 then 152040535 else 152512380)) else (if b1 then (if b0 then 102583524 else 172742856) else (if b0 then 91356210 else 128295671))) else (if b2 then (if b1 then (if b0 then 121319220 else 88874527) else (if b0 then 139920577 else 99531520)) else (if b1 then (if b0 then 73739034 else 95873279) else (if b0 then 68285004 else 93489825))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 73822954)) else (if b1 then 100000000 else (if b0 then 78990285 else 74593493))) else (if b2 then (if b1 then (if b0 then 100000000 else 59676123) else (if b0 then 100000000 else 89835429)) else (if b1 then (if b0 then 59903093 else 58362752) else (if b0 then 53500465 else 34515745)))) else (if b3 then (if b2 then (if b1 then (if b0 then 162009816 else 150420276) else (if b0 then 123832721 else 134303014)) else (if b1 then (if b0 then 102926730 else 144172708) else (if b0 then 95400929 else 107356647))) else (if b2 then (if b1 then (if b0 then 107855987 else 95698630) else (if b0 then 119602736 else 104126061)) else (if b1 then (if b0 then 83090194 else 95200363) else (if b0 then 76274305 else 91525860)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 74362543)) else (if b1 then 100000000 else (if b0 then 79305151 else 91414069))) else (if b2 then (if b1 then (if b0 then 100000000 else 66132188) else (if b0 then 100000000 else 73464852)) else (if b1 then (if b0 then 67601941 else 85982625) else (if b0 then 62503146 else 48466164)))) else (if b3 then (if b2 then (if b1 then (if b0 then 152040535 else 123832721) else (if b0 then 137921069 else 128450305)) else (if b1 then (if b0 then 96959565 else 141643053) else (if b0 then 95481796 else 126980707))) else (if b2 then (if b1 then (if b0 then 121922766 else 89413588) else (if b0 then 122797322 else 92023664)) else (if b1 then (if b0 then 84555269 else 97946081) else (if b0 then 86128115 else 98398826))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 75287453)) else (if b1 then 100000000 else (if b0 then 80085508 else 83716627))) else (if b2 then (if b1 then (if b0 then 100000000 else 66204946) else (if b0 then 100000000 else 83233847)) else (if b1 then (if b0 then 67141410 else 74742947) else (if b0 then 61308682 else 45837745)))) else (if b3 then (if b2 then (if b1 then (if b0 then 152512380 else 134303014) else (if b0 then 128450305 else 129259802)) else (if b1 then (if b0 then 99805510 else 139843841) else (if b0 then 96131311 else 116180305))) else (if b2 then (if b1 then (if b0 then 113260958 else 92850904) else (if b0 then 120466986 else 98841122)) else (if b1 then (if b0 then 85512350 else 96703390) else (if b0 then 83429169 else 96186118)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 97347164)) else (if b1 then 100000000 else (if b0 then 99084083 else 101856197))) else (if b2 then (if b1 then (if b0 then 100000000 else 99392117) else (if b0 then 100000000 else 101831027)) else (if b1 then (if b0 then 99576716 else 97679477) else (if b0 then 93487754 else 98088716)))) else (if b3 then (if b2 then (if b1 then (if b0 then 102583524 else 102926730) else (if b0 then 96959565 else 99805510)) else (if b1 then (if b0 then 117243827 else 104952734) else (if b0 then 104465123 else 97777195))) else (if b2 then (if b1 then (if b0 then 75620777 else 105542980) else (if b0 then 99596386 else 102202143)) else (if b1 then (if b0 then 105098403 else 97700693) else (if b0 then 94196256 else 101462638))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 65253390)) else (if b1 then 100000000 else (if b0 then 73252067 else 81976611))) else (if b2 then (if b1 then (if b0 then 100000000 else 52524988) else (if b0 then 100000000 else 72939711)) else (if b1 then (if b0 then 54741599 else 68483629) else (if b0 then 44287169 else 25899962)))) else (if b3 then (if b2 then (if b1 then (if b0 then 172742856 else 144172708) else (if b0 then 141643053 else 139843841)) else (if b1 then (if b0 then 104952734 else 157697756) else (if b0 then 96489445 else 126043957))) else (if b2 then (if b1 then (if b0 then 111800035 else 90554676) else (if b0 then 127351041 else 95546672)) else (if b1 then (if b0 then 80960669 else 94423802) else (if b0 then 75393558 else 95578945)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 105080361)) else (if b1 then 100000000 else (if b0 then 107743464 else 104371053))) else (if b2 then (if b1 then (if b0 then 100000000 else 102015628) else (if b0 then 100000000 else 98767292)) else (if b1 then (if b0 then 104993326 else 102632207) else (if b0 then 98615578 else 107900909)))) else (if b3 then (if b2 then (if b1 then (if b0 then 91356210 else 95400929) else (if b0 then 95481796 else 96131311)) else (if b1 then (if b0 then 104465123 else 96489445) else (if b0 then 110076860 else 99845091))) else (if b2 then (if b1 then (if b0 then 91566017 else 103071318) else (if b0 then 91112159 else 96191554)) else (if b1 then (if b0 then 105265033 else 94342562) else (if b0 then 102600303 else 99749746))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 85337675)) else (if b1 then 100000000 else (if b0 then 90391848 else 100639004))) else (if b2 then (if b1 then (if b0 then 100000000 else 79359081) else (if b0 then 100000000 else 76891168)) else (if b1 then (if b0 then 82577228 else 98539130) else (if b0 then 77476532 else 72256702)))) else (if b3 then (if b2 then (if b1 then (if b0 then 128295671 else 107356647) else (if b0 then 126980707 else 116180305)) else (if b1 then (if b0 then 97777195 else 126043957) else (if b0 then 99845091 else 123456743))) else (if b2 then (if b1 then (if b0 then 114465515 else 91134887) else (if b0 then 111332295 else 89410173)) else (if b1 then (if b0 then 91402347 else 97057713) else (if b0 then 93679310 else 100383091)))))))
  else
    if a2 then
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 93639711)) else (if b1 then 100000000 else (if b0 then 93054061 else 93881308))) else (if b2 then (if b1 then (if b0 then 100000000 else 83772014) else (if b0 then 100000000 else 85078860)) else (if b1 then (if b0 then 83724897 else 94807391) else (if b0 then 90975100 else 78386256)))) else (if b3 then (if b2 then (if b1 then (if b0 then 121319220 else 107855987) else (if b0 then 121922766 else 113260958)) else (if b1 then (if b0 then 75620777 else 111800035) else (if b0 then 91566017 else 114465515))) else (if b2 then (if b1 then (if b0 then 146447852 else 88323791) else (if b0 then 109238027 else 92028970)) else (if b1 then (if b0 then 86078650 else 102291411) else (if b0 then 100379457 else 95281184))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 104504991)) else (if b1 then 100000000 else (if b0 then 102305037 else 100962534))) else (if b2 then (if b1 then (if b0 then 100000000 else 109382897) else (if b0 then 100000000 else 109356391)) else (if b1 then (if b0 then 107629266 else 102556022) else (if b0 then 106972107 else 111779821)))) else (if b3 then (if b2 then (if b1 then (if b0 then 88874527 else 95698630) else (if b0 then 89413588 else 92850904)) else (if b1 then (if b0 then 105542980 else 90554676) else (if b0 then 103071318 else 91134887))) else (if b2 then (if b1 then (if b0 then 88323791 else 106086584) else (if b0 then 97122988 else 104905965)) else (if b1 then (if b0 then 105935005 else 100504185) else (if b0 then 102790767 else 101419689)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 69540577)) else (if b1 then 100000000 else (if b0 then 65273609 else 82281841))) else (if b2 then (if b1 then (if b0 then 100000000 else 88463914) else (if b0 then 100000000 else 97120671)) else (if b1 then (if b0 then 81655773 else 93501191) else (if b0 then 80296236 else 61965328)))) else (if b3 then (if b2 then (if b1 then (if b0 then 139920577 else 119602736) else (if b0 then 122797322 else 120466986)) else (if b1 then (if b0 then 99596386 else 127351041) else (if b0 then 91112159 else 111332295))) else (if b2 then (if b1 then (if b0 then 109238027 else 97122988) else (if b0 then 139803903 else 113778648)) else (if b1 then (if b0 then 93611478 else 107026933) else (if b0 then 96439417 else 109399978))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 93655429)) else (if b1 then 100000000 else (if b0 then 87941355 else 90139751))) else (if b2 then (if b1 then (if b0 then 100000000 else 110148657) else (if b0 then 100000000 else 115550038)) else (if b1 then (if b0 then 104432086 else 99074608) else (if b0 then 106406571 else 100876501)))) else (if b3 then (if b2 then (if b1 then (if b0 then 99531520 else 104126061) else (if b0 then 92023664 else 98841122)) else (if b1 then (if b0 then 102202143 else 95546672) else (if b0 then 96191554 else 89410173))) else (if b2 then (if b1 then (if b0 then 92028970 else 104905965) else (if b0 then 113778648 else 115751579)) else (if b1 then (if b0 then 103923377 else 105652669) else (if b0 then 103728549 else 106124065)))))))
    else
      (if a1 then (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 109302084)) else (if b1 then 100000000 else (if b0 then 106643980 else 106621121))) else (if b2 then (if b1 then (if b0 then 100000000 else 119315621) else (if b0 then 100000000 else 110633059)) else (if b1 then (if b0 then 118341310 else 113964037) else (if b0 then 117913359 else 127014179)))) else (if b3 then (if b2 then (if b1 then (if b0 then 73739034 else 83090194) else (if b0 then 84555269 else 85512350)) else (if b1 then (if b0 then 105098403 else 80960669) else (if b0 then 105265033 else 91402347))) else (if b2 then (if b1 then (if b0 then 86078650 else 105935005) else (if b0 then 93611478 else 103923377)) else (if b1 then (if b0 then 111573568 else 100955513) else (if b0 then 110421277 else 105235960))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 98761909)) else (if b1 then 100000000 else (if b0 then 94574824 else 99106297))) else (if b2 then (if b1 then (if b0 then 100000000 else 107903361) else (if b0 then 100000000 else 105841352)) else (if b1 then (if b0 then 104300409 else 105763488) else (if b0 then 109196543 else 105615344)))) else (if b3 then (if b2 then (if b1 then (if b0 then 95873279 else 95200363) else (if b0 then 97946081 else 96703390)) else (if b1 then (if b0 then 97700693 else 94423802) else (if b0 then 94342562 else 97057713))) else (if b2 then (if b1 then (if b0 then 102291411 else 100504185) else (if b0 then 107026933 else 105652669)) else (if b1 then (if b0 then 100955513 else 105668160) else (if b0 then 103691153 else 103606387)))))) else (if a0 then (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 110400053)) else (if b1 then 100000000 else (if b0 then 105568432 else 107001982))) else (if b2 then (if b1 then (if b0 then 100000000 else 124138891) else (if b0 then 100000000 else 110293781)) else (if b1 then (if b0 then 122312156 else 121045266) else (if b0 then 125756109 else 132713590)))) else (if b3 then (if b2 then (if b1 then (if b0 then 68285004 else 76274305) else (if b0 then 86128115 else 83429169)) else (if b1 then (if b0 then 94196256 else 75393558) else (if b0 then 102600303 else 93679310))) else (if b2 then (if b1 then (if b0 then 100379457 else 102790767) else (if b0 then 96439417 else 103728549)) else (if b1 then (if b0 then 110421277 else 103691153) else (if b0 then 117695794 else 107209104))))) else (if b4 then (if b3 then (if b2 then (if b1 then 100000000 else (if b0 then 100000000 else 96091993)) else (if b1 then 100000000 else (if b0 then 93016732 else 100427646))) else (if b2 then (if b1 then (if b0 then 100000000 else 110598531) else (if b0 then 100000000 else 104480965)) else (if b1 then (if b0 then 108069442 else 111104060) else (if b0 then 107866158 else 107843292)))) else (if b3 then (if b2 then (if b1 then (if b0 then 93489825 else 91525860) else (if b0 then 98398826 else 96186118)) else (if b1 then (if b0 then 101462638 else 95578945) else (if b0 then 99749746 else 100383091))) else (if b2 then (if b1 then (if b0 then 95281184 else 101419689) else (if b0 then 109399978 else 106124065)) else (if b1 then (if b0 then 105235960 else 103606387) else (if b0 then 107209104 else 107873991)))))))
private lemma checkQ2_8_ok :
    ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
     [false, true].all fun a1 => [false, true].all fun a0 =>
     [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
     [false, true].all fun b1 => [false, true].all fun b0 =>
       decide ((q2DotShift8 a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : ℤ) = 100000000 +
         (q2W ⟨8, by decide⟩ 0 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 0 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 1 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 1 b4 b3 b2 b1 b0 +
          q2W ⟨8, by decide⟩ 2 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 2 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 3 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 3 b4 b3 b2 b1 b0 +
          q2W ⟨8, by decide⟩ 4 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 4 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 5 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 5 b4 b3 b2 b1 b0 +
          q2W ⟨8, by decide⟩ 6 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 6 b4 b3 b2 b1 b0 + q2W ⟨8, by decide⟩ 7 a4 a3 a2 a1 a0 * q2W ⟨8, by decide⟩ 7 b4 b3 b2 b1 b0))) = true := by decide

def q2Term (a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 : Bool) : ℤ :=
  if isCanonRoot a b ab ba then
    let r := rcIdx a b ab ba
    q2W r 0 k4 k3 k2 k1 k0 * q2W r 0 l4 l3 l2 l1 l0 + q2W r 1 k4 k3 k2 k1 k0 * q2W r 1 l4 l3 l2 l1 l0 +
    q2W r 2 k4 k3 k2 k1 k0 * q2W r 2 l4 l3 l2 l1 l0 + q2W r 3 k4 k3 k2 k1 k0 * q2W r 3 l4 l3 l2 l1 l0 +
    q2W r 4 k4 k3 k2 k1 k0 * q2W r 4 l4 l3 l2 l1 l0 + q2W r 5 k4 k3 k2 k1 k0 * q2W r 5 l4 l3 l2 l1 l0 +
    q2W r 6 k4 k3 k2 k1 k0 * q2W r 6 l4 l3 l2 l1 l0 + q2W r 7 k4 k3 k2 k1 k0 * q2W r 7 l4 l3 l2 l1 l0
  else 0

private def q2DotShift (a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 : Bool) : ℕ :=
  if isCanonRoot a b ab ba then
    match (rcIdx a b ab ba).val with
    | 0 => q2DotShift0 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | 1 => q2DotShift1 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | 2 => q2DotShift2 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | 3 => q2DotShift3 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | 4 => q2DotShift4 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | 5 => q2DotShift5 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | 6 => q2DotShift6 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | 7 => q2DotShift7 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | 8 => q2DotShift8 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
    | _ => 100000000
  else 100000000

private lemma q2Term_eq_shift (a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 : Bool) :
    q2Term a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 =
      (q2DotShift a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 : ℤ) - 100000000 := by
  unfold q2Term q2DotShift
  by_cases hc : isCanonRoot a b ab ba = true
  · simp only [hc, ↓reduceIte]
    have extract : ∀ {P : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool},
        ([false, true].all fun a4 => [false, true].all fun a3 => [false, true].all fun a2 =>
         [false, true].all fun a1 => [false, true].all fun a0 =>
         [false, true].all fun b4 => [false, true].all fun b3 => [false, true].all fun b2 =>
         [false, true].all fun b1 => [false, true].all fun b0 =>
           P a4 a3 a2 a1 a0 b4 b3 b2 b1 b0) = true → P k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 = true :=
      fun h => list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool
        (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool h k4) k3) k2) k1) k0) l4) l3) l2) l1) l0
    have hr : ∀ r : Fin 9,
        q2W r 0 k4 k3 k2 k1 k0 * q2W r 0 l4 l3 l2 l1 l0 + q2W r 1 k4 k3 k2 k1 k0 * q2W r 1 l4 l3 l2 l1 l0 +
        q2W r 2 k4 k3 k2 k1 k0 * q2W r 2 l4 l3 l2 l1 l0 + q2W r 3 k4 k3 k2 k1 k0 * q2W r 3 l4 l3 l2 l1 l0 +
        q2W r 4 k4 k3 k2 k1 k0 * q2W r 4 l4 l3 l2 l1 l0 + q2W r 5 k4 k3 k2 k1 k0 * q2W r 5 l4 l3 l2 l1 l0 +
        q2W r 6 k4 k3 k2 k1 k0 * q2W r 6 l4 l3 l2 l1 l0 + q2W r 7 k4 k3 k2 k1 k0 * q2W r 7 l4 l3 l2 l1 l0 =
        ((match r.val with
          | 0 => q2DotShift0 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | 1 => q2DotShift1 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | 2 => q2DotShift2 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | 3 => q2DotShift3 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | 4 => q2DotShift4 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | 5 => q2DotShift5 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | 6 => q2DotShift6 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | 7 => q2DotShift7 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | 8 => q2DotShift8 k4 k3 k2 k1 k0 l4 l3 l2 l1 l0
          | _ => 100000000 : ℕ) : ℤ) - 100000000 := by
      intro r; fin_cases r
      · have h := extract checkQ2_0_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
      · have h := extract checkQ2_1_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
      · have h := extract checkQ2_2_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
      · have h := extract checkQ2_3_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
      · have h := extract checkQ2_4_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
      · have h := extract checkQ2_5_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
      · have h := extract checkQ2_6_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
      · have h := extract checkQ2_7_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
      · have h := extract checkQ2_8_ok; simp only [decide_eq_true_eq] at h
        exact eq_sub_iff_add_eq'.mpr h.symm
    exact hr (rcIdx a b ab ba)
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]; ring

def b24LocalBool (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) : ℤ :=
  6 * (lam23 e0 e1 e2 f01 f10 f02 f20 f12 f21 + lam23 e0 e1 e3 f01 f10 f03 f30 f13 f31 +
       lam23 e0 e2 e3 f02 f20 f03 f30 f23 f32 + lam23 e1 e2 e3 f12 f21 f13 f31 f23 f32) +
  6 * (phiFlip e0 (mkFlag e1 f01 f10) (mkFlag e2 f02 f20) (mkFlag e3 f03 f30) +
       phiFlip e1 (mkFlag e0 f10 f01) (mkFlag e2 f12 f21) (mkFlag e3 f13 f31) +
       phiFlip e2 (mkFlag e0 f20 f02) (mkFlag e1 f21 f12) (mkFlag e3 f23 f32) +
       phiFlip e3 (mkFlag e0 f30 f03) (mkFlag e1 f31 f13) (mkFlag e2 f32 f23)) +
  8 * (b4Pair e0 e1 f01 f10 e2 e3 f23 f32 +
       b4Pair e0 e2 f02 f20 e1 e3 f13 f31 +
       b4Pair e0 e3 f03 f30 e1 e2 f12 f21) +
  2 * (q2Term e0 e1 f01 f10 e2 f02 f12 f20 f21 e3 f03 f13 f30 f31 +
       q2Term e1 e0 f10 f01 e2 f12 f02 f21 f20 e3 f13 f03 f31 f30 +
       q2Term e0 e2 f02 f20 e1 f01 f21 f10 f12 e3 f03 f23 f30 f32 +
       q2Term e2 e0 f20 f02 e1 f21 f01 f12 f10 e3 f23 f03 f32 f30 +
       q2Term e0 e3 f03 f30 e1 f01 f31 f10 f13 e2 f02 f32 f20 f23 +
       q2Term e3 e0 f30 f03 e1 f31 f01 f13 f10 e2 f32 f02 f23 f20 +
       q2Term e1 e2 f12 f21 e0 f10 f20 f01 f02 e3 f13 f23 f31 f32 +
       q2Term e2 e1 f21 f12 e0 f20 f10 f02 f01 e3 f23 f13 f32 f31 +
       q2Term e1 e3 f13 f31 e0 f10 f30 f01 f03 e2 f12 f32 f21 f23 +
       q2Term e3 e1 f31 f13 e0 f30 f10 f03 f01 e2 f32 f12 f23 f21 +
       q2Term e2 e3 f23 f32 e0 f20 f30 f02 f03 e1 f21 f31 f12 f13 +
       q2Term e3 e2 f32 f23 e0 f30 f20 f03 f02 e1 f31 f21 f13 f12)

private def b24LocalShift (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) : ℕ :=
  6 * (lamShift e0 e1 e2 f01 f10 f02 f20 f12 f21 + lamShift e0 e1 e3 f01 f10 f03 f30 f13 f31 +
       lamShift e0 e2 e3 f02 f20 f03 f30 f23 f32 + lamShift e1 e2 e3 f12 f21 f13 f31 f23 f32) +
  6 * (phiShift e0 (mkFlag e1 f01 f10) (mkFlag e2 f02 f20) (mkFlag e3 f03 f30) +
       phiShift e1 (mkFlag e0 f10 f01) (mkFlag e2 f12 f21) (mkFlag e3 f13 f31) +
       phiShift e2 (mkFlag e0 f20 f02) (mkFlag e1 f21 f12) (mkFlag e3 f23 f32) +
       phiShift e3 (mkFlag e0 f30 f03) (mkFlag e1 f31 f13) (mkFlag e2 f32 f23)) +
  8 * (b4DotShift (rcIdx e0 e1 f01 f10) (rcIdx e2 e3 f23 f32) +
       b4DotShift (rcIdx e0 e2 f02 f20) (rcIdx e1 e3 f13 f31) +
       b4DotShift (rcIdx e0 e3 f03 f30) (rcIdx e1 e2 f12 f21)) +
  2 * (q2DotShift e0 e1 f01 f10 e2 f02 f12 f20 f21 e3 f03 f13 f30 f31 +
       q2DotShift e1 e0 f10 f01 e2 f12 f02 f21 f20 e3 f13 f03 f31 f30 +
       q2DotShift e0 e2 f02 f20 e1 f01 f21 f10 f12 e3 f03 f23 f30 f32 +
       q2DotShift e2 e0 f20 f02 e1 f21 f01 f12 f10 e3 f23 f03 f32 f30 +
       q2DotShift e0 e3 f03 f30 e1 f01 f31 f10 f13 e2 f02 f32 f20 f23 +
       q2DotShift e3 e0 f30 f03 e1 f31 f01 f13 f10 e2 f32 f02 f23 f20 +
       q2DotShift e1 e2 f12 f21 e0 f10 f20 f01 f02 e3 f13 f23 f31 f32 +
       q2DotShift e2 e1 f21 f12 e0 f20 f10 f02 f01 e3 f23 f13 f32 f31 +
       q2DotShift e1 e3 f13 f31 e0 f10 f30 f01 f03 e2 f12 f32 f21 f23 +
       q2DotShift e3 e1 f31 f13 e0 f30 f10 f03 f01 e2 f32 f12 f23 f21 +
       q2DotShift e2 e3 f23 f32 e0 f20 f30 f02 f03 e1 f21 f31 f12 f13 +
       q2DotShift e3 e2 f32 f23 e0 f30 f20 f03 f02 e1 f31 f21 f13 f12)

private lemma b24LocalBool_eq_shift (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) :
    b24LocalBool e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 =
      (b24LocalShift e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : ℤ) - 12000000000 := by
  unfold b24LocalBool b24LocalShift
  simp_rw [b4Pair_eq_shift, q2Term_eq_shift]
  unfold lam23 phiFlip
  push_cast
  ring

def c4FreeB24 (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) : Bool :=
  !(e0 && e1 && f01 && f10) && !(e0 && e2 && f02 && f20) &&
  !(e0 && e3 && f03 && f30) && !(e1 && e2 && f12 && f21) &&
  !(e1 && e3 && f13 && f31) && !(e2 && e3 && f23 && f32)

private lemma b4Pair_symm (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair c d cd dc a b ab ba := by
  dsimp only [b4Pair]; ring

private lemma b4Pair_swap1 (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair b a ba ab c d cd dc := by
  dsimp only [b4Pair]; rw [rcIdx_swap a b ab ba]

private lemma b4Pair_swap2 (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair a b ab ba d c dc cd := by
  dsimp only [b4Pair]; rw [rcIdx_swap c d cd dc]

private lemma q2Term_symm (a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 : Bool) :
    q2Term a b ab ba k4 k3 k2 k1 k0 l4 l3 l2 l1 l0 = q2Term a b ab ba l4 l3 l2 l1 l0 k4 k3 k2 k1 k0 := by
  dsimp only [q2Term]; split_ifs <;> ring

private lemma bool4_swap (a b x y : Bool) : (a && b && x && y) = (b && a && y && x) := by
  cases a <;> cases b <;> cases x <;> cases y <;> rfl

private lemma c4FreeB24_swap01 (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) :
    c4FreeB24 e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 =
    c4FreeB24 e1 e0 e2 e3 f10 f01 f12 f21 f13 f31 f02 f20 f03 f30 f23 f32 := by
  dsimp only [c4FreeB24]; rw [bool4_swap e0 e1 f01 f10]; ac_rfl

private lemma c4FreeB24_swap12 (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) :
    c4FreeB24 e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 =
    c4FreeB24 e0 e2 e1 e3 f02 f20 f01 f10 f03 f30 f21 f12 f23 f32 f13 f31 := by
  dsimp only [c4FreeB24]; rw [bool4_swap e1 e2 f12 f21]; ac_rfl

private lemma c4FreeB24_swap23 (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) :
    c4FreeB24 e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 =
    c4FreeB24 e0 e1 e3 e2 f01 f10 f03 f30 f02 f20 f13 f31 f12 f21 f32 f23 := by
  dsimp only [c4FreeB24]; rw [bool4_swap e2 e3 f23 f32]; ac_rfl

private lemma b24LocalBool_swap01 (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) :
    b24LocalBool e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 =
    b24LocalBool e1 e0 e2 e3 f10 f01 f12 f21 f13 f31 f02 f20 f03 f30 f23 f32 := by
  dsimp only [b24LocalBool]
  rw [lam23_swap01 e0 e1 e2, lam23_swap01 e0 e1 e3]
  rw [phiFlip_swap12 e2, phiFlip_swap12 e3]
  rw [b4Pair_swap1 e0 e1 f01 f10 e2 e3 f23 f32]
  rw [b4Pair_symm e1 e2 f12 f21 e0 e3 f03 f30]
  rw [b4Pair_symm e1 e3 f13 f31 e0 e2 f02 f20]
  rw [q2Term_symm e2 e3 f23 f32 e0 f20 f30 f02 f03 e1 f21 f31 f12 f13]
  rw [q2Term_symm e3 e2 f32 f23 e0 f30 f20 f03 f02 e1 f31 f21 f13 f12]
  ring

private lemma b24LocalBool_swap12 (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) :
    b24LocalBool e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 =
    b24LocalBool e0 e2 e1 e3 f02 f20 f01 f10 f03 f30 f21 f12 f23 f32 f13 f31 := by
  dsimp only [b24LocalBool]
  rw [lam23_swap12 e0 e1 e2, lam23_swap01 e1 e2 e3]
  rw [phiFlip_swap12 e0, phiFlip_swap23 e3]
  rw [b4Pair_swap2 e0 e3 f03 f30 e1 e2 f12 f21]
  rw [q2Term_symm e0 e3 f03 f30 e1 f01 f31 f10 f13 e2 f02 f32 f20 f23]
  rw [q2Term_symm e3 e0 f30 f03 e1 f31 f01 f13 f10 e2 f32 f02 f23 f20]
  ring

private lemma b24LocalBool_swap23 (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) :
    b24LocalBool e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 =
    b24LocalBool e0 e1 e3 e2 f01 f10 f03 f30 f02 f20 f13 f31 f12 f21 f32 f23 := by
  dsimp only [b24LocalBool]
  rw [lam23_swap12 e0 e2 e3, lam23_swap12 e1 e2 e3]
  rw [phiFlip_swap23 e0, phiFlip_swap23 e1]
  rw [b4Pair_swap2 e0 e1 f01 f10 e2 e3 f23 f32]
  rw [q2Term_symm e0 e1 f01 f10 e2 f02 f12 f20 f21 e3 f03 f13 f30 f31]
  rw [q2Term_symm e1 e0 f10 f01 e2 f12 f02 f21 f20 e3 f13 f03 f31 f30]
  ring

private def checkB24Step (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool) : Bool :=
  if c4FreeB24 e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 then
    decide (b24LocalShift e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 ≤ M4_shift)
  else true

private def checkB24_0000_s (f01 f10 f02 f20 : Bool) : Bool :=
  [false, true].all fun f03 => [false, true].all fun f30 =>
  [false, true].all fun f12 => [false, true].all fun f21 =>
  [false, true].all fun f13 => [false, true].all fun f31 =>
  [false, true].all fun f23 => [false, true].all fun f32 =>
    checkB24Step false false false false f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32
private lemma checkB24_0000_00 : checkB24_0000_s false false false false = true := by decide
private lemma checkB24_0000_01 : checkB24_0000_s false false false true = true := by decide
private lemma checkB24_0000_02 : checkB24_0000_s false false true false = true := by decide
private lemma checkB24_0000_03 : checkB24_0000_s false false true true = true := by decide
private lemma checkB24_0000_04 : checkB24_0000_s false true false false = true := by decide
private lemma checkB24_0000_05 : checkB24_0000_s false true false true = true := by decide
private lemma checkB24_0000_06 : checkB24_0000_s false true true false = true := by decide
private lemma checkB24_0000_07 : checkB24_0000_s false true true true = true := by decide
private lemma checkB24_0000_08 : checkB24_0000_s true false false false = true := by decide
private lemma checkB24_0000_09 : checkB24_0000_s true false false true = true := by decide
private lemma checkB24_0000_10 : checkB24_0000_s true false true false = true := by decide
private lemma checkB24_0000_11 : checkB24_0000_s true false true true = true := by decide
private lemma checkB24_0000_12 : checkB24_0000_s true true false false = true := by decide
private lemma checkB24_0000_13 : checkB24_0000_s true true false true = true := by decide
private lemma checkB24_0000_14 : checkB24_0000_s true true true false = true := by decide
private lemma checkB24_0000_15 : checkB24_0000_s true true true true = true := by decide
private lemma b24_sorted_0000 (f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool)
    (h : c4FreeB24 false false false false f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 = true) :
    b24LocalBool false false false false f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 ≤ M4 := by
  have hs : checkB24_0000_s f01 f10 f02 f20 = true := by
    cases f01 <;> cases f10 <;> cases f02 <;> cases f20
    · exact checkB24_0000_00
    · exact checkB24_0000_01
    · exact checkB24_0000_02
    · exact checkB24_0000_03
    · exact checkB24_0000_04
    · exact checkB24_0000_05
    · exact checkB24_0000_06
    · exact checkB24_0000_07
    · exact checkB24_0000_08
    · exact checkB24_0000_09
    · exact checkB24_0000_10
    · exact checkB24_0000_11
    · exact checkB24_0000_12
    · exact checkB24_0000_13
    · exact checkB24_0000_14
    · exact checkB24_0000_15
  have he := list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool
    (list_all_bool (list_all_bool (list_all_bool hs f03) f30) f12) f21) f13) f31) f23) f32
  simp only [checkB24Step, h, ↓reduceIte, decide_eq_true_eq] at he
  rw [b24LocalBool_eq_shift]; have hZ := Int.ofNat_le.mpr he; dsimp only [M4_shift, M4] at hZ ⊢; omega

private def checkB24_0001_s (f01 f10 f02 f20 : Bool) : Bool :=
  [false, true].all fun f03 => [false, true].all fun f30 =>
  [false, true].all fun f12 => [false, true].all fun f21 =>
  [false, true].all fun f13 => [false, true].all fun f31 =>
  [false, true].all fun f23 => [false, true].all fun f32 =>
    checkB24Step false false false true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32
private lemma checkB24_0001_00 : checkB24_0001_s false false false false = true := by decide
private lemma checkB24_0001_01 : checkB24_0001_s false false false true = true := by decide
private lemma checkB24_0001_02 : checkB24_0001_s false false true false = true := by decide
private lemma checkB24_0001_03 : checkB24_0001_s false false true true = true := by decide
private lemma checkB24_0001_04 : checkB24_0001_s false true false false = true := by decide
private lemma checkB24_0001_05 : checkB24_0001_s false true false true = true := by decide
private lemma checkB24_0001_06 : checkB24_0001_s false true true false = true := by decide
private lemma checkB24_0001_07 : checkB24_0001_s false true true true = true := by decide
private lemma checkB24_0001_08 : checkB24_0001_s true false false false = true := by decide
private lemma checkB24_0001_09 : checkB24_0001_s true false false true = true := by decide
private lemma checkB24_0001_10 : checkB24_0001_s true false true false = true := by decide
private lemma checkB24_0001_11 : checkB24_0001_s true false true true = true := by decide
private lemma checkB24_0001_12 : checkB24_0001_s true true false false = true := by decide
private lemma checkB24_0001_13 : checkB24_0001_s true true false true = true := by decide
private lemma checkB24_0001_14 : checkB24_0001_s true true true false = true := by decide
private lemma checkB24_0001_15 : checkB24_0001_s true true true true = true := by decide
private lemma b24_sorted_0001 (f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool)
    (h : c4FreeB24 false false false true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 = true) :
    b24LocalBool false false false true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 ≤ M4 := by
  have hs : checkB24_0001_s f01 f10 f02 f20 = true := by
    cases f01 <;> cases f10 <;> cases f02 <;> cases f20
    · exact checkB24_0001_00
    · exact checkB24_0001_01
    · exact checkB24_0001_02
    · exact checkB24_0001_03
    · exact checkB24_0001_04
    · exact checkB24_0001_05
    · exact checkB24_0001_06
    · exact checkB24_0001_07
    · exact checkB24_0001_08
    · exact checkB24_0001_09
    · exact checkB24_0001_10
    · exact checkB24_0001_11
    · exact checkB24_0001_12
    · exact checkB24_0001_13
    · exact checkB24_0001_14
    · exact checkB24_0001_15
  have he := list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool
    (list_all_bool (list_all_bool (list_all_bool hs f03) f30) f12) f21) f13) f31) f23) f32
  simp only [checkB24Step, h, ↓reduceIte, decide_eq_true_eq] at he
  rw [b24LocalBool_eq_shift]; have hZ := Int.ofNat_le.mpr he; dsimp only [M4_shift, M4] at hZ ⊢; omega

private def checkB24_0011_s (f01 f10 f02 f20 : Bool) : Bool :=
  [false, true].all fun f03 => [false, true].all fun f30 =>
  [false, true].all fun f12 => [false, true].all fun f21 =>
  [false, true].all fun f13 => [false, true].all fun f31 =>
  [(false, false), (false, true), (true, false)].all fun p23 =>
    checkB24Step false false true true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 p23.1 p23.2
private lemma checkB24_0011_00 : checkB24_0011_s false false false false = true := by decide
private lemma checkB24_0011_01 : checkB24_0011_s false false false true = true := by decide
private lemma checkB24_0011_02 : checkB24_0011_s false false true false = true := by decide
private lemma checkB24_0011_03 : checkB24_0011_s false false true true = true := by decide
private lemma checkB24_0011_04 : checkB24_0011_s false true false false = true := by decide
private lemma checkB24_0011_05 : checkB24_0011_s false true false true = true := by decide
private lemma checkB24_0011_06 : checkB24_0011_s false true true false = true := by decide
private lemma checkB24_0011_07 : checkB24_0011_s false true true true = true := by decide
private lemma checkB24_0011_08 : checkB24_0011_s true false false false = true := by decide
private lemma checkB24_0011_09 : checkB24_0011_s true false false true = true := by decide
private lemma checkB24_0011_10 : checkB24_0011_s true false true false = true := by decide
private lemma checkB24_0011_11 : checkB24_0011_s true false true true = true := by decide
private lemma checkB24_0011_12 : checkB24_0011_s true true false false = true := by decide
private lemma checkB24_0011_13 : checkB24_0011_s true true false true = true := by decide
private lemma checkB24_0011_14 : checkB24_0011_s true true true false = true := by decide
private lemma checkB24_0011_15 : checkB24_0011_s true true true true = true := by decide
private lemma b24_sorted_0011 (f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool)
    (h : c4FreeB24 false false true true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 = true) :
    b24LocalBool false false true true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 ≤ M4 := by
  have h23 : !(f23 && f32) = true := by
    cases f23 <;> cases f32 <;> simp_all [c4FreeB24]
  have hs : checkB24_0011_s f01 f10 f02 f20 = true := by
    cases f01 <;> cases f10 <;> cases f02 <;> cases f20
    · exact checkB24_0011_00
    · exact checkB24_0011_01
    · exact checkB24_0011_02
    · exact checkB24_0011_03
    · exact checkB24_0011_04
    · exact checkB24_0011_05
    · exact checkB24_0011_06
    · exact checkB24_0011_07
    · exact checkB24_0011_08
    · exact checkB24_0011_09
    · exact checkB24_0011_10
    · exact checkB24_0011_11
    · exact checkB24_0011_12
    · exact checkB24_0011_13
    · exact checkB24_0011_14
    · exact checkB24_0011_15
  have he := list_all_tri (list_all_bool (list_all_bool (list_all_bool (list_all_bool (list_all_bool
    (list_all_bool hs f03) f30) f12) f21) f13) f31) f23 f32 h23
  simp only [checkB24Step, h, ↓reduceIte, decide_eq_true_eq] at he
  rw [b24LocalBool_eq_shift]; have hZ := Int.ofNat_le.mpr he; dsimp only [M4_shift, M4] at hZ ⊢; omega

private def checkB24_0111_s (f01 f10 f12 f21 : Bool) : Bool :=
  [false, true].all fun f02 => [false, true].all fun f20 =>
  [false, true].all fun f03 => [false, true].all fun f30 =>
  [(false, false), (false, true), (true, false)].all fun p13 =>
  [(false, false), (false, true), (true, false)].all fun p23 =>
    checkB24Step false true true true f01 f10 f02 f20 f03 f30 f12 f21 p13.1 p13.2 p23.1 p23.2
private lemma checkB24_0111_0_0 : checkB24_0111_s false false false false = true := by decide
private lemma checkB24_0111_0_1 : checkB24_0111_s false false false true = true := by decide
private lemma checkB24_0111_0_2 : checkB24_0111_s false false true false = true := by decide
private lemma checkB24_0111_1_0 : checkB24_0111_s false true false false = true := by decide
private lemma checkB24_0111_1_1 : checkB24_0111_s false true false true = true := by decide
private lemma checkB24_0111_1_2 : checkB24_0111_s false true true false = true := by decide
private lemma checkB24_0111_2_0 : checkB24_0111_s true false false false = true := by decide
private lemma checkB24_0111_2_1 : checkB24_0111_s true false false true = true := by decide
private lemma checkB24_0111_2_2 : checkB24_0111_s true false true false = true := by decide
private lemma checkB24_0111_3_0 : checkB24_0111_s true true false false = true := by decide
private lemma checkB24_0111_3_1 : checkB24_0111_s true true false true = true := by decide
private lemma checkB24_0111_3_2 : checkB24_0111_s true true true false = true := by decide
private lemma b24_sorted_0111 (f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool)
    (h : c4FreeB24 false true true true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 = true) :
    b24LocalBool false true true true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 ≤ M4 := by
  have h12 : !(f12 && f21) = true := by cases f12 <;> cases f21 <;> simp_all [c4FreeB24]
  have h13 : !(f13 && f31) = true := by cases f13 <;> cases f31 <;> simp_all [c4FreeB24]
  have h23 : !(f23 && f32) = true := by cases f23 <;> cases f32 <;> simp_all [c4FreeB24]
  have hs : checkB24_0111_s f01 f10 f12 f21 = true := by
    cases f01 <;> cases f10 <;> cases f12 <;> cases f21
    · exact checkB24_0111_0_0
    · exact checkB24_0111_0_1
    · exact checkB24_0111_0_2
    · simp_all
    · exact checkB24_0111_1_0
    · exact checkB24_0111_1_1
    · exact checkB24_0111_1_2
    · simp_all
    · exact checkB24_0111_2_0
    · exact checkB24_0111_2_1
    · exact checkB24_0111_2_2
    · simp_all
    · exact checkB24_0111_3_0
    · exact checkB24_0111_3_1
    · exact checkB24_0111_3_2
    · simp_all
  have he := list_all_tri (list_all_tri (list_all_bool (list_all_bool (list_all_bool (list_all_bool hs f02) f20) f03) f30) f13 f31 h13) f23 f32 h23
  simp only [checkB24Step, h, ↓reduceIte, decide_eq_true_eq] at he
  rw [b24LocalBool_eq_shift]; have hZ := Int.ofNat_le.mpr he; dsimp only [M4_shift, M4] at hZ ⊢; omega

private def checkB24_1111_s (f01 f10 : Bool) : Bool :=
  [(false, false), (false, true), (true, false)].all fun p02 =>
  [(false, false), (false, true), (true, false)].all fun p03 =>
  [(false, false), (false, true), (true, false)].all fun p12 =>
  [(false, false), (false, true), (true, false)].all fun p13 =>
  [(false, false), (false, true), (true, false)].all fun p23 =>
    checkB24Step true true true true f01 f10 p02.1 p02.2 p03.1 p03.2 p12.1 p12.2 p13.1 p13.2 p23.1 p23.2
private lemma checkB24_1111_0 : checkB24_1111_s false false = true := by decide
private lemma checkB24_1111_1 : checkB24_1111_s false true = true := by decide
private lemma checkB24_1111_2 : checkB24_1111_s true false = true := by decide
private lemma b24_sorted_1111 (f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool)
    (h : c4FreeB24 true true true true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 = true) :
    b24LocalBool true true true true f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 ≤ M4 := by
  have h01 : !(f01 && f10) = true := by cases f01 <;> cases f10 <;> simp_all [c4FreeB24]
  have h02 : !(f02 && f20) = true := by cases f02 <;> cases f20 <;> simp_all [c4FreeB24]
  have h03 : !(f03 && f30) = true := by cases f03 <;> cases f30 <;> simp_all [c4FreeB24]
  have h12 : !(f12 && f21) = true := by cases f12 <;> cases f21 <;> simp_all [c4FreeB24]
  have h13 : !(f13 && f31) = true := by cases f13 <;> cases f31 <;> simp_all [c4FreeB24]
  have h23 : !(f23 && f32) = true := by cases f23 <;> cases f32 <;> simp_all [c4FreeB24]
  have hs : checkB24_1111_s f01 f10 = true := by
    cases f01 <;> cases f10
    · exact checkB24_1111_0
    · exact checkB24_1111_1
    · exact checkB24_1111_2
    · simp_all
  have he := list_all_tri (list_all_tri (list_all_tri (list_all_tri (list_all_tri hs f02 f20 h02) f03 f30 h03) f12 f21 h12) f13 f31 h13) f23 f32 h23
  simp only [checkB24Step, h, ↓reduceIte, decide_eq_true_eq] at he
  rw [b24LocalBool_eq_shift]; have hZ := Int.ofNat_le.mpr he; dsimp only [M4_shift, M4] at hZ ⊢; omega

private lemma b24_le_of_sorted_star (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool)
    (h01 : (!e0 || e1) = true) (h12 : (!e1 || e2) = true) (h23 : (!e2 || e3) = true)
    (hc4 : c4FreeB24 e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 = true) :
    b24LocalBool e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 ≤ M4 := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;> try contradiction
  · exact b24_sorted_0000 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 hc4
  · exact b24_sorted_0001 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 hc4
  · exact b24_sorted_0011 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 hc4
  · exact b24_sorted_0111 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 hc4
  · exact b24_sorted_1111 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 hc4

lemma b24LocalBool_le_M4 (e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 : Bool)
    (hc4 : c4FreeB24 e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 = true) :
    b24LocalBool e0 e1 e2 e3 f01 f10 f02 f20 f03 f30 f12 f21 f13 f31 f23 f32 ≤ M4 := by
  -- Sort (e0, e1) if e0 = true ∧ e1 = false:
  by_cases s01 : e0 = true ∧ e1 = false
  · rw [b24LocalBool_swap01]; rw [c4FreeB24_swap01] at hc4
    rcases s01 with ⟨rfl, rfl⟩
    -- Now (false, true, e2, e3). Sort (e2, e3):
    by_cases s23 : e2 = true ∧ e3 = false
    · rw [b24LocalBool_swap23]; rw [c4FreeB24_swap23] at hc4
      rcases s23 with ⟨rfl, rfl⟩
      -- (false, true, false, true) -> swap12 -> (false, false, true, true)!
      rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
      exact b24_le_of_sorted_star false false true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
    · -- (false, true, e2, e3) with !e2 || e3:
      by_cases h12 : e2 = false
      · rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
        -- Now (false, e2=false, true, e3): must have e3=true because ¬(e2=true ∧ e3=false)? Wait if e2=false, e3 can be false or true!
        by_cases h3 : e3 = false
        · rw [b24LocalBool_swap23]; rw [c4FreeB24_swap23] at hc4
          subst h12; subst h3
          exact b24_le_of_sorted_star false false false true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
        · have : e3 = true := by cases e3 <;> simp_all
          subst h12; subst this
          exact b24_le_of_sorted_star false false true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · have h2t : e2 = true := by cases e2 <;> simp_all
        have h3t : e3 = true := by cases e3 <;> simp_all
        subst h2t; subst h3t
        exact b24_le_of_sorted_star false true true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
  · -- !e0 || e1 holds! First sort (e2, e3):
    by_cases s23 : e2 = true ∧ e3 = false
    · rw [b24LocalBool_swap23]; rw [c4FreeB24_swap23] at hc4
      rcases s23 with ⟨rfl, rfl⟩
      -- (e0, e1, false, true) with !e0 || e1. Case split on e0, e1:
      cases e0 <;> cases e1 <;> try (exfalso; exact s01 ⟨rfl, rfl⟩)
      · exact b24_le_of_sorted_star false false false true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
        exact b24_le_of_sorted_star false false true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
        rw [b24LocalBool_swap01]; rw [c4FreeB24_swap01] at hc4
        exact b24_le_of_sorted_star false true true true _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
    · -- Both !e0||e1 and !e2||e3 hold! Check all 9 pairs:
      cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;>
        try (exfalso; first | exact s01 ⟨rfl, rfl⟩ | exact s23 ⟨rfl, rfl⟩)
      · exact b24_le_of_sorted_star false false false false _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · exact b24_le_of_sorted_star false false false true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · exact b24_le_of_sorted_star false false true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
        rw [b24LocalBool_swap23]; rw [c4FreeB24_swap23] at hc4
        exact b24_le_of_sorted_star false false false true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
        exact b24_le_of_sorted_star false false true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · exact b24_le_of_sorted_star false true  true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
        rw [b24LocalBool_swap01]; rw [c4FreeB24_swap01] at hc4
        rw [b24LocalBool_swap23]; rw [c4FreeB24_swap23] at hc4
        rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
        exact b24_le_of_sorted_star false false true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · rw [b24LocalBool_swap12]; rw [c4FreeB24_swap12] at hc4
        rw [b24LocalBool_swap01]; rw [c4FreeB24_swap01] at hc4
        exact b24_le_of_sorted_star false true  true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4
      · exact b24_le_of_sorted_star true  true  true  true  _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hc4

end PPL033_B2Q4Cert
