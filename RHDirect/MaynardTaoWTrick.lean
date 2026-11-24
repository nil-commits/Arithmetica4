/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Maynard–Tao campaign, wave 1: the W-trick

The *W-trick* restricts the sieve to a residue class `n ≡ b [MOD W]` where `W = ∏_{p ≤ D₀} p`
is a primorial, chosen so that every shift `b + h` (`h ∈ H`) is coprime to `W`. This removes the
local obstructions at small primes and is the standard first step of the Maynard–Tao sieve.

Everything here is unconditional and on native Mathlib objects (`Nat.Prime`, `Nat.Coprime`,
`primorial`, `Nat.ModEq`). The key ingredients:
* `exists_modEq_of_primes` — CRT over a finite set of distinct primes;
* `exists_residue_avoiding_neg` — admissibility gives, at each prime `p`, a residue class avoiding
  all `-h mod p`;
* `exists_W_trick_residue` — the W-trick itself.
-/
import RHDirect.MaynardTaoTuples
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum.Prime

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false

noncomputable section

namespace RHDirect.MaynardTao

open Finset

/-- The W-trick modulus: the primorial `W(D₀) = ∏_{p ≤ D₀} p`. -/
def W (D₀ : ℕ) : ℕ := primorial D₀

theorem W_pos (D₀ : ℕ) : 0 < W D₀ := primorial_pos D₀

/-- A prime divides `W(D₀)` iff it is at most `D₀`. -/
theorem prime_dvd_W_iff {p D₀ : ℕ} (hp : Nat.Prime p) : p ∣ W D₀ ↔ p ≤ D₀ :=
  Nat.Prime.dvd_primorial_iff hp

/-! ### CRT over a finite set of distinct primes -/

private theorem coprime_prod_of_prime_not_mem {p : ℕ} (hp : Nat.Prime p)
    (s : Finset ℕ) (hs : ∀ q ∈ s, Nat.Prime q) (hps : p ∉ s) :
    (∏ q ∈ s, q).Coprime p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.Coprime]
  | @insert q s hq ih =>
    have hqp : q ≠ p := by
      intro heq
      apply hps
      rw [heq]
      exact Finset.mem_insert.mpr (Or.inl rfl)
    have hqcop : q.Coprime p :=
      (Nat.coprime_primes (hs q (Finset.mem_insert.mpr (Or.inl rfl))) hp).mpr hqp
    have hscop : (∏ x ∈ s, x).Coprime p :=
      ih (fun r hr => hs r (Finset.mem_insert.mpr (Or.inr hr)))
        (fun h => hps (Finset.mem_insert.mpr (Or.inr h)))
    rw [Finset.prod_insert hq]
    exact Nat.Coprime.mul_left hqcop hscop

/-- Chinese Remainder Theorem over a finite set of distinct primes: any assignment of residues
`a p` is realized by some `b` modulo each `p ∈ P`. -/
theorem exists_modEq_of_primes (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (a : ℕ → ℕ) : ∃ b : ℕ, ∀ p ∈ P, b ≡ a p [MOD p] := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert p s hp ih =>
    have hP' : ∀ q ∈ s, Nat.Prime q :=
      fun q hq => hP q (Finset.mem_insert.mpr (Or.inr hq))
    obtain ⟨b, hb⟩ := ih hP'
    have hcop : (∏ q ∈ s, q).Coprime p :=
      coprime_prod_of_prime_not_mem (hP p (Finset.mem_insert.mpr (Or.inl rfl))) s hP' hp
    obtain ⟨b', hb'1, hb'2⟩ := Nat.chineseRemainder hcop b (a p)
    refine ⟨b', ?_⟩
    intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with (rfl | hq)
    · exact hb'2
    · exact Nat.ModEq.trans
        (Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem id hq) hb'1) (hb q hq)

/-! ### Choosing a residue avoiding the negated tuple -/

/-- Admissibility at a prime `p` yields a residue `r` such that `r + h ≢ 0 [MOD p]` for every
`h ∈ H` (equivalently, `r mod p` avoids every `-h mod p`). -/
theorem exists_residue_avoiding_neg {H : Finset ℕ} (hadm : Admissible H) (p : ℕ)
    (hp : Nat.Prime p) : ∃ r : ℕ, ∀ h ∈ H, ¬(r + h ≡ 0 [MOD p]) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : (H.image (fun h : ℕ => (-(h : ZMod p)))).card < p := by
    have heq : (H.image (fun h : ℕ => (-(h : ZMod p)))).card =
        (H.image (fun h : ℕ => (h : ZMod p))).card := by
      have himg : H.image (fun h : ℕ => (-(h : ZMod p))) =
          (H.image (fun h : ℕ => (h : ZMod p))).image Neg.neg := by
        ext x
        simp only [mem_image]
        constructor
        · rintro ⟨a, ha, hx⟩
          exact ⟨(a : ZMod p), ⟨a, ha, rfl⟩, hx⟩
        · rintro ⟨y, ⟨a, ha, hy⟩, hx⟩
          refine ⟨a, ha, ?_⟩
          rw [hy]
          exact hx
      rw [himg, Finset.card_image_of_injective _ neg_injective]
    rw [heq]
    exact hadm p hp
  have hmiss : ∃ r : ZMod p, r ∉ H.image (fun h : ℕ => (-(h : ZMod p))) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hsub : (univ : Finset (ZMod p)) ⊆ H.image (fun h : ℕ => (-(h : ZMod p))) :=
      fun x _ => hall x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hle
    omega
  obtain ⟨r, hr⟩ := hmiss
  refine ⟨r.val, ?_⟩
  intro h hh hcontra
  have hdvd : p ∣ r.val + h := Nat.modEq_zero_iff_dvd.mp hcontra
  have hz : ((r.val + h : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (r.val + h) p).mpr hdvd
  have hrval : ((r.val : ℕ) : ZMod p) = r := ZMod.natCast_zmod_val r
  have hsum : (r : ZMod p) + (h : ZMod p) = 0 := by
    have := hz
    simp only [Nat.cast_add] at this
    rwa [hrval] at this
  have hneg : r = -(h : ZMod p) := eq_neg_iff_add_eq_zero.mpr hsum
  apply hr
  rw [mem_image]
  exact ⟨h, hh, hneg.symm⟩

/-! ### The W-trick -/

/-- **The W-trick.** For an admissible tuple `H` and any cutoff `D₀`, there is a residue `b`
such that every shift `b + h` (`h ∈ H`) is coprime to `W(D₀) = ∏_{p ≤ D₀} p`. -/
theorem exists_W_trick_residue {H : Finset ℕ} (hadm : Admissible H) (D₀ : ℕ) :
    ∃ b : ℕ, ∀ h ∈ H, Nat.Coprime (b + h) (W D₀) := by
  classical
  let P : Finset ℕ := (range (D₀ + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (mem_filter.mp hp).2
  have hchoice : ∀ p : ℕ, ∃ r : ℕ, Nat.Prime p → ∀ h ∈ H, ¬(r + h ≡ 0 [MOD p]) := by
    intro p
    by_cases hp : Nat.Prime p
    · obtain ⟨r, hr⟩ := exists_residue_avoiding_neg hadm p hp
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose a ha using hchoice
  obtain ⟨b, hb⟩ := exists_modEq_of_primes P hP a
  refine ⟨b, ?_⟩
  intro h hh
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd
  -- some prime p divides both b + h and W D₀
  have hgcd_ne_one : Nat.gcd (b + h) (W D₀) ≠ 1 := hgcd
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd_ne_one
  have hpb : p ∣ b + h := Nat.dvd_trans hpdvd (Nat.gcd_dvd_left (b + h) (W D₀))
  have hpW : p ∣ W D₀ := Nat.dvd_trans hpdvd (Nat.gcd_dvd_right (b + h) (W D₀))
  have hpD : p ≤ D₀ := (prime_dvd_W_iff hp).mp hpW
  have hpP : p ∈ P := by
    rw [mem_filter, mem_range]
    exact ⟨Nat.lt_succ_iff.mpr hpD, hp⟩
  have havoid := ha p hp h hh
  have hmod : b + h ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpb
  have hbmod : b ≡ a p [MOD p] := hb p hpP
  have hsum : b + h ≡ a p + h [MOD p] := Nat.ModEq.add hbmod (Nat.ModEq.refl h)
  have hzero : a p + h ≡ 0 [MOD p] := Nat.ModEq.trans (Nat.ModEq.symm hsum) hmod
  exact havoid hzero

end RHDirect.MaynardTao
