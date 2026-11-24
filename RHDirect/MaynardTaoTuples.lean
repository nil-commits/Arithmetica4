/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Maynard–Tao campaign, wave 1: admissible prime tuples

This file builds the *combinatorial* foundation of the Maynard–Tao bounded-gaps-between-primes
theorem, entirely unconditionally on native Mathlib objects (`Nat.Prime`, `ZMod`, `Finset`):

* `Admissible H` — the standard Hardy–Littlewood admissibility condition: for every prime `p`,
  the residues of `H` modulo `p` do not cover all `p` residue classes.
* a computable `Bool` checker `admissibleBool` (only primes `p ≤ |H|` need checking) together with
  a proved bridge `admissible_of_admissibleBool`;
* concrete kernel-checked witnesses `mtTuple50` (card 50, diameter 246 — the Polymath8b headline)
  and `mtTuple105` (card 105, diameter 600 — Maynard's original 2015 bound);
* general existence `exists_admissible_card` of an admissible tuple of any size `k ≥ 1`;
* the diameter pigeonhole `prime_pair_of_two_prime_shifts`: two prime shifts of a tuple yield a
  prime pair whose gap is at most the tuple diameter.

The analytic input (multidimensional Selberg sieve weights + Bombieri–Vinogradov asymptotics)
is isolated in `RHDirect.MaynardTaoReduction`; nothing here depends on it.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Prime

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false

noncomputable section

namespace RHDirect.MaynardTao

open Finset

/-! ### Admissibility -/

/-- A finite tuple `H` of natural numbers is **admissible** if for every prime `p` the residues
`{h mod p : h ∈ H}` do not cover all `p` residue classes. This is the standard Hardy–Littlewood
/ Maynard–Tao admissibility condition, stated on Mathlib's native `ZMod p`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (H.image (fun h : ℕ => (h : ZMod p))).card < p

/-- Computable admissibility checker. It suffices to test primes `p ≤ H.card`: for `p > H.card`
the image has at most `H.card < p` elements automatically. Built from computable `List` operations
and pure `Nat` modular arithmetic so that concrete witnesses reduce by kernel computation (`rfl`). -/
def admissibleBool (H : Finset ℕ) : Bool :=
  ((List.range (H.card + 1)).filter (fun p => decide (Nat.Prime p))).all
    (fun p => decide ((H.image (fun h => h % p)).card < p))

/-- Bridge from the computational checker to the native `ZMod` definition. -/
theorem admissible_of_admissibleBool {H : Finset ℕ} (h : admissibleBool H = true) :
    Admissible H := by
  dsimp only [admissibleBool] at h
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hpc : p ≤ H.card
  · have hmem : p ∈ (List.range (H.card + 1)).filter (fun p => decide (Nat.Prime p)) := by
      rw [List.mem_filter, List.mem_range]
      exact ⟨Nat.lt_succ_iff.mpr hpc, decide_eq_true hp⟩
    have hcheck : (H.image (fun h => h % p)).card < p :=
      of_decide_eq_true ((List.all_eq_true.mp h) p hmem)
    have heq : (H.image (fun h : ℕ => (h : ZMod p))).card =
        (H.image (fun h => h % p)).card := by
      have himg : H.image (fun h => h % p) =
          (H.image (fun h : ℕ => (h : ZMod p))).image ZMod.val := by
        ext x
        simp only [mem_image]
        constructor
        · rintro ⟨a, ha, hx⟩
          refine ⟨(a : ZMod p), ⟨a, ha, rfl⟩, ?_⟩
          rw [ZMod.val_natCast]
          exact hx
        · rintro ⟨y, ⟨a, ha, hy⟩, hx⟩
          refine ⟨a, ha, ?_⟩
          have hv : y.val = a % p := by rw [← hy, ZMod.val_natCast]
          omega
      rw [himg, Finset.card_image_of_injective _ (ZMod.val_injective p)]
    rw [heq]
    exact hcheck
  · have hle : (H.image (fun h : ℕ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
    omega

/-- Admissibility is monotone under taking subsets. -/
theorem Admissible.mono {H₁ H₂ : Finset ℕ} (hsub : H₁ ⊆ H₂) (h : Admissible H₂) :
    Admissible H₁ := by
  intro p hp
  calc (H₁.image (fun h : ℕ => (h : ZMod p))).card
      ≤ (H₂.image (fun h : ℕ => (h : ZMod p))).card :=
        Finset.card_le_card (Finset.image_mono _ hsub)
    _ < p := h p hp

/-- The empty tuple is admissible. -/
theorem admissible_empty : Admissible (∅ : Finset ℕ) := by
  intro p hp
  simpa using hp.pos

/-! ### Diameter -/

/-- The diameter of a nonempty tuple: `max H - min H`. -/
def diam (H : Finset ℕ) (h : H.Nonempty) : ℕ := H.max' h - H.min' h

/-- Two prime shifts of a tuple yield a prime pair whose gap is bounded by the diameter.
This is the elementary pigeonhole at the heart of the Maynard–Tao conclusion. -/
theorem prime_pair_of_two_prime_shifts {H : Finset ℕ} (hH : H.Nonempty)
    {n a b : ℕ} (ha : a ∈ H) (hb : b ∈ H) (hab : a < b)
    (hpa : Nat.Prime (n + a)) (hpb : Nat.Prime (n + b)) :
    ∃ p q : ℕ, n ≤ p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ diam H hH := by
  refine ⟨n + a, n + b, ?_, ?_, hpa, hpb, ?_⟩
  · omega
  · omega
  · have hmin : H.min' hH ≤ a := Finset.min'_le _ _ ha
    have hmax : b ≤ H.max' hH := Finset.le_max' _ _ hb
    have h1 : b - a ≤ H.max' hH - H.min' hH :=
      le_trans (Nat.sub_le_sub_right hmax a) (Nat.sub_le_sub_left hmin (H.max' hH))
    have h2 : (n + b) - (n + a) = b - a := Nat.add_sub_add_left n b a
    simp only [diam]
    omega

/-! ### Concrete witnesses -/

/-- The Polymath8b admissible 50-tuple of diameter 246 (min 0, max 246).
Found by `tools/maynard_tuple_search.py`; admissibility is kernel-checked below. -/
def mtTuple50 : Finset ℕ :=
  {0, 2, 6, 8, 12, 18, 20, 26, 30, 32, 36, 42, 48, 50, 56, 62, 68, 72, 78, 86,
   90, 96, 98, 102, 110, 116, 120, 128, 132, 138, 140, 146, 152, 156, 158, 162,
   168, 176, 182, 186, 188, 198, 200, 210, 212, 216, 230, 240, 242, 246}

theorem mtTuple50_card : mtTuple50.card = 50 := by rfl

theorem mtTuple50_nonempty : mtTuple50.Nonempty := ⟨0, by decide⟩

theorem mtTuple50_max : mtTuple50.max' mtTuple50_nonempty = 246 := by
  rw [Finset.max'_eq_iff mtTuple50 mtTuple50_nonempty 246]
  exact ⟨by decide, by decide⟩

theorem mtTuple50_min : mtTuple50.min' mtTuple50_nonempty = 0 := by
  rw [Finset.min'_eq_iff mtTuple50 mtTuple50_nonempty 0]
  exact ⟨by decide, by decide⟩

theorem mtTuple50_diam : diam mtTuple50 mtTuple50_nonempty = 246 := by
  simp only [diam, mtTuple50_max, mtTuple50_min]

theorem mtTuple50_admissibleBool : admissibleBool mtTuple50 = true := by rfl

theorem mtTuple50_admissible : Admissible mtTuple50 :=
  admissible_of_admissibleBool mtTuple50_admissibleBool

/-- Maynard's original admissible 105-tuple of diameter 600 (min 6, max 606). -/
def mtTuple105 : Finset ℕ :=
  {6, 8, 12, 18, 20, 26, 30, 32, 36, 42, 48, 50, 56, 62, 68, 72, 78, 86, 90, 96,
   98, 102, 110, 116, 120, 128, 132, 138, 140, 146, 152, 156, 158, 162, 168, 176,
   182, 186, 188, 198, 200, 210, 212, 216, 230, 240, 242, 246, 252, 260, 266, 270,
   272, 278, 282, 288, 306, 308, 312, 320, 336, 338, 342, 348, 350, 362, 366, 372,
   380, 386, 392, 396, 410, 420, 422, 426, 428, 438, 440, 450, 452, 462, 468, 470,
   476, 488, 492, 498, 506, 510, 512, 516, 530, 536, 546, 548, 552, 558, 572, 578,
   582, 590, 596, 600, 606}

theorem mtTuple105_card : mtTuple105.card = 105 := by rfl

theorem mtTuple105_nonempty : mtTuple105.Nonempty := ⟨6, by decide⟩

theorem mtTuple105_max : mtTuple105.max' mtTuple105_nonempty = 606 := by
  rw [Finset.max'_eq_iff mtTuple105 mtTuple105_nonempty 606]
  exact ⟨by decide, by decide⟩

theorem mtTuple105_min : mtTuple105.min' mtTuple105_nonempty = 6 := by
  rw [Finset.min'_eq_iff mtTuple105 mtTuple105_nonempty 6]
  exact ⟨by decide, by decide⟩

theorem mtTuple105_diam : diam mtTuple105 mtTuple105_nonempty = 600 := by
  simp only [diam, mtTuple105_max, mtTuple105_min]

theorem mtTuple105_admissibleBool : admissibleBool mtTuple105 = true := by rfl

theorem mtTuple105_admissible : Admissible mtTuple105 :=
  admissible_of_admissibleBool mtTuple105_admissibleBool

/-! ### General existence -/

/-- For every `k ≥ 1` there exists an admissible tuple of exactly `k` elements.
Construction: `k` distinct primes all larger than `k`. For a prime `p ≤ k` none of the elements
is divisible by `p`, so the residue `0` is missed; for `p > k` there are fewer than `p` elements. -/
theorem exists_admissible_card (k : ℕ) (_hk : 1 ≤ k) :
    ∃ H : Finset ℕ, H.card = k ∧ Admissible H := by
  classical
  suffices ∀ j ≤ k, ∃ H : Finset ℕ, H.card = j ∧
      (∀ h ∈ H, Nat.Prime h ∧ k < h) ∧ Admissible H by
    obtain ⟨H, hc, _, ha⟩ := this k (le_rfl)
    exact ⟨H, hc, ha⟩
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨∅, by simp, by simp, admissible_empty⟩
  | succ j ih =>
    intro hjk
    have hjk' : j ≤ k := by omega
    obtain ⟨H, hc, hprime, ha⟩ := ih hjk'
    obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (k + ∑ h ∈ H, h + 1)
    have hsum_nn : 0 ≤ ∑ h ∈ H, h := Finset.sum_nonneg (fun _ _ => Nat.zero_le _)
    have hqk : k < q := by omega
    have hqgt : ∀ h ∈ H, h < q := by
      intro h hh
      have hle : h ≤ ∑ x ∈ H, x :=
        Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hh
      omega
    have hqH : q ∉ H := by
      intro hh
      have := hqgt q hh
      omega
    refine ⟨insert q H, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hqH, hc]
    · intro h hh
      rw [mem_insert] at hh
      rcases hh with (rfl | hh)
      · exact ⟨hq, hqk⟩
      · exact hprime h hh
    · intro p hp
      haveI : NeZero p := ⟨hp.ne_zero⟩
      by_cases hpk : p ≤ k
      · have hp2 : 2 ≤ p := hp.two_le
        have h0 : (0 : ZMod p) ∉ (insert q H).image (fun h : ℕ => (h : ZMod p)) := by
          intro hh
          rw [mem_image] at hh
          obtain ⟨h, hh, heq⟩ := hh
          have hdvd : p ∣ h := (ZMod.natCast_eq_zero_iff h p).mp heq
          have hph : Nat.Prime h ∧ k < h := by
            rw [mem_insert] at hh
            rcases hh with (rfl | hh)
            · exact ⟨hq, hqk⟩
            · exact hprime h hh
          have := Nat.Prime.eq_one_or_self_of_dvd hph.1 p hdvd
          rcases this with (h1 | hh)
          · omega
          · omega
        have hsub : (insert q H).image (fun h : ℕ => (h : ZMod p)) ⊆
            (univ : Finset (ZMod p)).erase 0 := by
          intro x hx
          simp only [mem_erase, mem_univ, and_true]
          intro hx0
          apply h0
          simpa [hx0] using hx
        calc ((insert q H).image (fun h : ℕ => (h : ZMod p))).card
            ≤ ((univ : Finset (ZMod p)).erase 0).card := Finset.card_le_card hsub
          _ = p - 1 := by
            rw [Finset.card_erase_of_mem (mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card]
          _ < p := Nat.sub_one_lt hp.ne_zero
      · have hle : ((insert q H).image (fun h : ℕ => (h : ZMod p))).card ≤
            (insert q H).card := Finset.card_image_le
        have hcard : (insert q H).card = j + 1 := by
          rw [Finset.card_insert_of_notMem hqH, hc]
        omega

/-! ### Translation invariance -/

/-- Admissibility is invariant under translating the whole tuple. -/
theorem Admissible.translate {H : Finset ℕ} (h : Admissible H) (t : ℕ) :
    Admissible (H.image (fun x => x + t)) := by
  intro p hp
  have heq : (H.image (fun x => x + t)).image (fun h : ℕ => (h : ZMod p)) =
      (H.image (fun h : ℕ => (h : ZMod p))).image (fun x => x + (t : ZMod p)) := by
    simp only [Finset.image_image]
    congr 1
    ext x
    exact Nat.cast_add x t
  rw [heq, Finset.card_image_of_injective _ (fun a b hab => add_right_cancel hab)]
  exact h p hp

end RHDirect.MaynardTao
