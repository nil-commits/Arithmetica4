/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Maynard–Tao campaign, wave 1: the combinatorial reduction & the analytic-core bridge

This file isolates the *combinatorial* heart of the Maynard–Tao argument and packages the
remaining *analytic* input as an explicit hypothesis structure, in the transparent
parameterized-architecture style of the `rh-direct` library.

For nonnegative sieve weights `w` on the W-tricked interval `n ∈ [N, 2N), n ≡ b [MOD W]`, set
* `S₁ H w N W b = ∑ w(n) · #{h ∈ H : n + h prime}` (prime-weighted sum),
* `S₂ w N W b   = ∑ w(n)` (plain sum).

The unconditional combinatorial theorem `exists_prime_pair_of_S₁_gt_S₂` shows that `S₁ > S₂`
forces two prime shifts of `H`, hence a prime pair of gap `≤ diam H` above `N`. The general
`m`-tuple version `exists_m_primes` is also proved.

The deep analytic content — constructing multidimensional Selberg weights from a smooth test
function `F` and proving `S₁ > S₂` for large `N` via Bombieri–Vinogradov (`ϑ = 1/2`),
Siegel–Walfisz, sharp Brun–Titchmarsh and Mertens, with `M_k > 4` — is captured by the explicit
structure `AnalyticCore H`. The bridge `bounded_gaps_of_analyticCore` and its concrete
instantiations `maynard_tao_246_of_core` / `maynard_tao_600_of_core` reduce the landmark headline
to that single, clearly-stated analytic hypothesis. Wave 2 (see
`forensics_and_plans/maynard_tao_wave2_selberg_spec.md`) discharges `AnalyticCore`.
-/
import RHDirect.MaynardTaoTuples
import RHDirect.MaynardTaoWTrick
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Prime

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false

noncomputable section

namespace RHDirect.MaynardTao

open Finset

/-! ### The W-tricked interval and the sieve sums -/

/-- The W-tricked dyadic interval `{n ∈ [N, 2N) : n ≡ b [MOD W]}`. -/
def wInterval (N W b : ℕ) : Finset ℕ :=
  (Ico N (2 * N)).filter (fun n => n ≡ b [MOD W])

/-- The number of prime shifts of `n` by the tuple `H`. -/
def primeShiftCount (H : Finset ℕ) (n : ℕ) : ℕ :=
  (H.filter (fun h => Nat.Prime (n + h))).card

/-- The prime-weighted sieve sum `S₁ = ∑ w(n) · #{prime shifts}`. -/
def S₁ (H : Finset ℕ) (w : ℕ → ℝ) (N W b : ℕ) : ℝ :=
  ∑ n ∈ wInterval N W b, w n * (primeShiftCount H n : ℝ)

/-- The plain sieve sum `S₂ = ∑ w(n)`. -/
def S₂ (w : ℕ → ℝ) (N W b : ℕ) : ℝ :=
  ∑ n ∈ wInterval N W b, w n

/-! ### The combinatorial core -/

/-- If `S₁ > S₂` for nonnegative weights, some `n` in the W-tricked interval has two distinct
prime shifts. This is the elementary pigeonhole underlying Maynard–Tao. -/
theorem exists_two_prime_shifts_of_S₁_gt_S₂ {H : Finset ℕ} {w : ℕ → ℝ} {N W b : ℕ}
    (hw : ∀ n ∈ wInterval N W b, 0 ≤ w n)
    (hgt : S₁ H w N W b > S₂ w N W b) :
    ∃ n ∈ wInterval N W b, ∃ a b : ℕ,
      a ∈ H ∧ b ∈ H ∧ a < b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b) := by
  have hdiff : S₁ H w N W b - S₂ w N W b =
      ∑ n ∈ wInterval N W b, w n * ((primeShiftCount H n : ℝ) - 1) := by
    simp only [S₁, S₂]
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext n
    ring
  have hpos : 0 < ∑ n ∈ wInterval N W b, w n * ((primeShiftCount H n : ℝ) - 1) := by
    linarith
  have hterm_exists : ∃ n ∈ wInterval N W b,
      0 < w n * ((primeShiftCount H n : ℝ) - 1) := by
    by_contra hall
    simp only [not_exists] at hall
    have hsum : ∑ n ∈ wInterval N W b, w n * ((primeShiftCount H n : ℝ) - 1) ≤ 0 :=
      Finset.sum_nonpos (fun n hn => not_lt.mp (fun h => hall n ⟨hn, h⟩))
    linarith
  obtain ⟨n, hn, hterm⟩ := hterm_exists
  have hcount_real : (1 : ℝ) < (primeShiftCount H n : ℝ) := by
    by_contra h
    have hle : (primeShiftCount H n : ℝ) - 1 ≤ 0 := by linarith
    have hprod : w n * ((primeShiftCount H n : ℝ) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hw n hn) hle
    linarith
  have hcount_nat : 1 < primeShiftCount H n := by exact_mod_cast hcount_real
  have h1 : 1 < (H.filter (fun h => Nat.Prime (n + h))).card := by
    simpa [primeShiftCount] using hcount_nat
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
  rw [mem_filter] at ha hb
  rcases lt_or_gt_of_ne hab with (hab' | hab')
  · exact ⟨n, hn, a, b, ha.1, hb.1, hab', ha.2, hb.2⟩
  · exact ⟨n, hn, b, a, hb.1, ha.1, hab', hb.2, ha.2⟩

/-- **Unconditional combinatorial reduction.** `S₁ > S₂` for nonnegative weights yields a prime
pair `p < q` with `N ≤ p` and gap `q - p ≤ diam H`. -/
theorem exists_prime_pair_of_S₁_gt_S₂ {H : Finset ℕ} (hH : H.Nonempty)
    {w : ℕ → ℝ} {N W b : ℕ} (hw : ∀ n ∈ wInterval N W b, 0 ≤ w n)
    (hgt : S₁ H w N W b > S₂ w N W b) :
    ∃ p q : ℕ, N ≤ p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ diam H hH := by
  obtain ⟨n, hn, a, b, haH, hbH, hab, hpa, hpb⟩ :=
    exists_two_prime_shifts_of_S₁_gt_S₂ hw hgt
  obtain ⟨p, q, hpN, hpq, hp, hq, hgap⟩ :=
    prime_pair_of_two_prime_shifts hH haH hbH hab hpa hpb
  have hnN : N ≤ n := (mem_Ico.mp (mem_filter.mp hn).1).1
  exact ⟨p, q, le_trans hnN hpN, hpq, hp, hq, hgap⟩

/-- General `m`-tuple combinatorics: if at least `m` shifts of `n` are prime, there is an
`m`-element set of primes, all of the form `n + h` (`h ∈ H`), lying in an interval of length
`diam H`. -/
theorem exists_m_primes {H : Finset ℕ} (hH : H.Nonempty) {n m : ℕ}
    (hm : m ≤ primeShiftCount H n) :
    ∃ P : Finset ℕ, P.card = m ∧ (∀ p ∈ P, Nat.Prime p) ∧
      ∃ L : ℕ, n ≤ L ∧ ∀ p ∈ P, L ≤ p ∧ p ≤ L + diam H hH := by
  classical
  let F : Finset ℕ := H.filter (fun h => Nat.Prime (n + h))
  have hFcard : m ≤ F.card := by simpa [F, primeShiftCount] using hm
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hFcard
  let P : Finset ℕ := S.image (fun h => n + h)
  have hPcard : P.card = m := by
    rw [Finset.card_image_of_injective _ (fun a b hab => Nat.add_left_cancel hab)]
    exact hScard
  have hPprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    rw [mem_image] at hp
    obtain ⟨h, hh, rfl⟩ := hp
    exact (mem_filter.mp (hSsub hh)).2
  refine ⟨P, hPcard, hPprime, n + H.min' hH, ?_, ?_⟩
  · omega
  · intro p hp
    rw [mem_image] at hp
    obtain ⟨h, hh, rfl⟩ := hp
    have hHmem : h ∈ H := (mem_filter.mp (hSsub hh)).1
    have hmin : H.min' hH ≤ h := Finset.min'_le _ _ hHmem
    have hmax : h ≤ H.max' hH := Finset.le_max' _ _ hHmem
    constructor
    · omega
    · simp only [diam]
      omega

/-! ### The analytic core (explicit hypothesis) and the headline bridge -/

/-- The **Maynard–Tao analytic core** for an admissible tuple `H`: the existence of nonnegative
sieve weights `w`, a W-trick modulus `W` and residue `b` (with every shift coprime to `W`), such
that the prime-weighted sum dominates the plain sum, `S₁ > S₂`, on all sufficiently large dyadic
W-tricked intervals.

This is exactly the deep analytic step of Maynard's theorem: constructing the multidimensional
Selberg weights from a smooth test function `F` on the simplex and evaluating `S₁, S₂`
asymptotically via Bombieri–Vinogradov (`ϑ = 1/2`), Siegel–Walfisz, sharp Brun–Titchmarsh and
Mertens, using `M_k = sup_F J_k(F)/I_k(F) > 4`. It is stated as an explicit hypothesis on native
Mathlib objects; wave 2 discharges it (see the campaign spec). -/
structure AnalyticCore (H : Finset ℕ) where
  W : ℕ
  b : ℕ
  w : ℕ → ℝ
  w_nonneg : ∀ n, 0 ≤ w n
  w_trick : ∀ h ∈ H, Nat.Coprime (b + h) W
  dominance : ∃ N₀ : ℕ, ∀ N ≥ N₀, S₁ H w N W b > S₂ w N W b

/-- **Conditional headline bridge.** The analytic core for `H` implies bounded prime gaps with
gap bound `diam H`, occurring arbitrarily far out. -/
theorem bounded_gaps_of_analyticCore {H : Finset ℕ} (hH : H.Nonempty)
    (core : AnalyticCore H) :
    ∃ H' : ℕ, H' ≤ diam H hH ∧
      ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H' := by
  refine ⟨diam H hH, le_rfl, ?_⟩
  intro N
  obtain ⟨N₀, hN₀⟩ := core.dominance
  let N' := max N N₀
  have hgt : S₁ H core.w N' core.W core.b > S₂ core.w N' core.W core.b :=
    hN₀ N' (le_max_right N N₀)
  obtain ⟨p, q, hpN', hpq, hp, hq, hgap⟩ :=
    exists_prime_pair_of_S₁_gt_S₂ hH (fun n _ => core.w_nonneg n) hgt
  exact ⟨p, q, le_trans (le_max_left N N₀) hpN', hpq, hp, hq, hgap⟩

/-- The Polymath8b headline `H ≤ 246`, reduced to the analytic core for the admissible 50-tuple. -/
theorem maynard_tao_246_of_core (core : AnalyticCore mtTuple50) :
    ∃ H : ℕ, H ≤ 246 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H := by
  obtain ⟨H', hH'le, hH'⟩ := bounded_gaps_of_analyticCore mtTuple50_nonempty core
  refine ⟨H', ?_, hH'⟩
  rwa [mtTuple50_diam] at hH'le

/-- Maynard's original headline `H ≤ 600`, reduced to the analytic core for the admissible
105-tuple. -/
theorem maynard_tao_600_of_core (core : AnalyticCore mtTuple105) :
    ∃ H : ℕ, H ≤ 600 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H := by
  obtain ⟨H', hH'le, hH'⟩ := bounded_gaps_of_analyticCore mtTuple105_nonempty core
  refine ⟨H', ?_, hH'⟩
  rwa [mtTuple105_diam] at hH'le

/-! ### General `m`-tuples in bounded intervals -/

/-- If `S₁ > m · S₂` for nonnegative weights, some `n` in the W-tricked interval has more than
`m` prime shifts (the general pigeonhole). -/
theorem exists_count_gt_of_S₁_gt {H : Finset ℕ} {w : ℕ → ℝ} {N W b : ℕ} {m : ℕ}
    (hw : ∀ n ∈ wInterval N W b, 0 ≤ w n)
    (hgt : S₁ H w N W b > (m : ℝ) * S₂ w N W b) :
    ∃ n ∈ wInterval N W b, m < primeShiftCount H n := by
  have hdiff : S₁ H w N W b - (m : ℝ) * S₂ w N W b =
      ∑ n ∈ wInterval N W b, w n * ((primeShiftCount H n : ℝ) - (m : ℝ)) := by
    simp only [S₁, S₂]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    ext n
    ring
  have hpos : 0 < ∑ n ∈ wInterval N W b, w n * ((primeShiftCount H n : ℝ) - (m : ℝ)) := by
    linarith
  have hterm_exists : ∃ n ∈ wInterval N W b,
      0 < w n * ((primeShiftCount H n : ℝ) - (m : ℝ)) := by
    by_contra hall
    simp only [not_exists] at hall
    have hsum : ∑ n ∈ wInterval N W b, w n * ((primeShiftCount H n : ℝ) - (m : ℝ)) ≤ 0 :=
      Finset.sum_nonpos (fun n hn => not_lt.mp (fun h => hall n ⟨hn, h⟩))
    linarith
  obtain ⟨n, hn, hterm⟩ := hterm_exists
  have hcount_real : (m : ℝ) < (primeShiftCount H n : ℝ) := by
    by_contra h
    have hle : (primeShiftCount H n : ℝ) - (m : ℝ) ≤ 0 := by linarith
    have hprod : w n * ((primeShiftCount H n : ℝ) - (m : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hw n hn) hle
    linarith
  have hcount_nat : m < primeShiftCount H n := by exact_mod_cast hcount_real
  exact ⟨n, hn, hcount_nat⟩

/-- The **general `m`-tuple analytic core**: weights giving `S₁ > (m-1) · S₂` on all large
W-tricked intervals (average prime-shift count exceeding `m-1`, forcing `m` prime shifts). -/
structure MAnalyticCore (H : Finset ℕ) (m : ℕ) where
  W : ℕ
  b : ℕ
  w : ℕ → ℝ
  w_nonneg : ∀ n, 0 ≤ w n
  w_trick : ∀ h ∈ H, Nat.Coprime (b + h) W
  dominance : ∃ N₀ : ℕ, ∀ N ≥ N₀, S₁ H w N W b > ((m - 1 : ℕ) : ℝ) * S₂ w N W b

/-- **General `m`-tuple headline bridge.** The `m`-tuple analytic core for `H` implies that
arbitrarily far out there is an interval of length `≤ diam H` containing `m` primes. -/
theorem bounded_m_tuples_of_analyticCore {H : Finset ℕ} (hH : H.Nonempty) {m : ℕ}
    (hm : 1 ≤ m) (core : MAnalyticCore H m) :
    ∃ H' : ℕ, H' ≤ diam H hH ∧
      ∀ N : ℕ, ∃ L : ℕ, N ≤ L ∧ ∃ P : Finset ℕ, P.card = m ∧
        (∀ p ∈ P, Nat.Prime p) ∧ (∀ p ∈ P, L ≤ p ∧ p ≤ L + H') := by
  refine ⟨diam H hH, le_rfl, ?_⟩
  intro N
  obtain ⟨N₀, hN₀⟩ := core.dominance
  let N' := max N N₀
  have hgt : S₁ H core.w N' core.W core.b > ((m - 1 : ℕ) : ℝ) * S₂ core.w N' core.W core.b :=
    hN₀ N' (le_max_right N N₀)
  obtain ⟨n, hn, hcount⟩ :=
    exists_count_gt_of_S₁_gt (m := m - 1) (fun n _ => core.w_nonneg n) hgt
  have hmcount : m ≤ primeShiftCount H n := by omega
  obtain ⟨P, hPcard, hPprime, L, hLn, hL⟩ := exists_m_primes hH hmcount
  have hnN' : N' ≤ n := (mem_Ico.mp (mem_filter.mp hn).1).1
  have hnN : N ≤ n := le_trans (le_max_left N N₀) hnN'
  refine ⟨L, ?_, P, hPcard, hPprime, ?_⟩
  · omega
  · intro p hp
    have hbound := hL p hp
    exact ⟨hbound.1, by simpa using hbound.2⟩

end RHDirect.MaynardTao
