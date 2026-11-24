import RHDirect.Interfaces
import RHDirect.HostFieldSupply
import RHDirect.TaylorWilesWindow
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# RHDirect.Stage2RamifiedPrimes

Compact, direct, zero-`sorry`, zero-`axiom` Lean 4 formalization of the **odd ramified primes
(`l ∣ M`, `B_ram`)** branch of `Stage2GaloisWire.ThreePartPatchingWindow` against
`RHDirect.Interfaces`, `RHDirect.HostFieldSupply`, `RHDirect.TaylorWilesWindow`, and targeted
Mathlib `v4.33.1`.

## Contents

1. **Prime-Divisor Counting (`ω(M) ≤ log₂ M`, `ω_odd(M) ≤ log₃ M`) & Cyclotomic `QS` Splitting**:
   - Exact prime-product divisibility `∏ p ∈ M.primeFactors, p ∣ M` and `∏ p ∈ oddPrimeFactors M, p ∣ ordCompl[2] M`.
   - Exponential and logarithmic bounds `2 ^ ω(M) ≤ M`, `3 ^ ω_odd(M) ≤ ordCompl[2] M ≤ M`,
     `ω(M) ≤ log₂ M`, `ω_odd(M) ≤ log₃ M ≤ log₂ M`, and `∑_{l ∣ M, odd} log l ≤ log M`.
   - Local prime-power valuation bound `M.factorization p ≤ log_p M ≤ log₂ M`.
   - Exact odd prime-factor preservation along the cyclotomic 2-tower `HostFieldSupply.QS`:
     `oddPrimeFactors (QS (zpowers χ) e) = oddPrimeFactors M` for primitive `χ`, and
     `ω_odd(N) ≤ ω_odd(M) + 2` for every conductor `N ∣ 2^(e+2) * M * q * d`.

2. **Local Tame & Wild Ramification Conductors and Inertia-Coinvariant Rank Bounds**:
   - Inertia invariants `V^I`, augmentation `I·V`, and inertia coinvariants `V_I = V / I·V`
     for finite inertia actions `ρ : I →* (V ≃ₗ[K] V)`.
   - Exact Reynolds/Maschke averaging projection `reynoldsProj ρ` in tame characteristic
     `(|I| : K) ≠ 0`, proving `V_I ≃ₗ[K] V^I` (`finrank_inertiaCoinvariants_eq_invariants_of_tame`)
     and `tameConductorExp ρ = dim(V / V^I) = dim V - dim V_I ≤ dim V`.
   - Higher ramification filtrations `RamificationFiltration I`, Swan conductor `sw(V)`, and
     Artin conductor exponent `a(V) = dim(V / V^I) + sw(V)`, proving `sw(V) = 0` for tame
     representations, `a(V) ≤ dim(V) * (1 + ∑ |G_i| / |G_0|) ≤ cutoff * dim(V)`.
   - Exact `p`-adic unit filtration cardinalities `Nat.card (unitFiltration p a k) = p ^ (a - k)`
     in `(ZMod (p^a))ˣ` and the telescoping cyclotomic Artin conductor identity
     `1 + ∑_{m=1}^{a-1} (p^m - p^{m-1}) * |U_m| / |U_0| = a`.

3. **Local Ramified Obstruction Modules & Exact `B_ram` Sum Bounds**:
   - `LocalRamifiedObstruction S E l k`: bounds `S.shaLen E l k` via a uniformizer power
     `ϖ ^ condExp ∈ ann(Obs)` and generator rank `genRank` using
     `TaylorWilesWindow.length_le_of_pow_mem_annihilator`.
   - `RamifiedPrimeRealization S E t M n N C_ram`: directly discharges BOTH odd-ramified
     conjuncts of `Stage2GaloisWire.ThreePartPatchingWindow` (`shaLen ≠ ⊤` and
     `∑_{l ∈ Pram} log l * ∑_{k ∈ [1, t)} (shaLen E l k).toNat ≤ minusBound C_ram M n N t`).
   - Sharp `ω_odd(M)`-factored and linear-in-`k` variants (`ramified_sum_le_log_mul_uniform`,
     `ramified_sum_le_minusBound_of_linear_k`).

4. **Absorption of the Odd Ramified-Prime Contribution into `√(exp(x^ε))` on `PageN` Windows**:
   - Explicit `ω_odd(M)`-controlled constant bound `∑_{l ∣ M, odd} l^3 ≤ log₃(M) * M^3`.
   - Direct absorption `minusBound C_ram M n N t ≤ (1 / 3) * √(exp(x^ε)) ≤ √(exp(x^ε))` on
     `PageN` + `WinPair` windows (`ramified_absorbed_in_sqrt_exp`,
     `ramified_realization_absorbed_on_winPair_pageN`), plus direct assembly into
     `TaylorWilesWindow.vvle_of_three_parts`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open scoped BigOperators
open Real Finset Filter RHDirect

namespace RHDirect
namespace Stage2RamifiedPrimes

/-! ## Section 1: Prime-Divisor Counting (`ω(M) ≤ log₂ M`, `ω_odd(M) ≤ log₃ M`) & `QS` Splitting -/

/-- The finite set of odd prime divisors of `M`. -/
def oddPrimeFactors (M : ℕ) : Finset ℕ := M.primeFactors.erase 2

/-- Number of distinct prime divisors `ω(M)`. -/
def omega (M : ℕ) : ℕ := M.primeFactors.card

/-- Number of distinct odd prime divisors `ω_odd(M)`. -/
def omegaOdd (M : ℕ) : ℕ := (oddPrimeFactors M).card

theorem mem_oddPrimeFactors_iff {M p : ℕ} :
    p ∈ oddPrimeFactors M ↔ p.Prime ∧ p ≠ 2 ∧ p ∣ M ∧ M ≠ 0 := by
  simp only [oddPrimeFactors, Finset.mem_erase, Nat.mem_primeFactors]
  tauto

theorem oddPrimeFactors_subset_primeFactors (M : ℕ) :
    oddPrimeFactors M ⊆ M.primeFactors :=
  Finset.erase_subset 2 M.primeFactors

theorem omegaOdd_le_omega (M : ℕ) : omegaOdd M ≤ omega M :=
  Finset.card_le_card (oddPrimeFactors_subset_primeFactors M)

theorem three_le_of_mem_oddPrimeFactors {M p : ℕ} (hp : p ∈ oddPrimeFactors M) : 3 ≤ p := by
  obtain ⟨hprime, hne2, _, _⟩ := mem_oddPrimeFactors_iff.mp hp
  have h2 := hprime.two_le
  omega

/-- The product of all distinct prime factors of `M ≠ 0` divides `M`. -/
theorem prod_primeFactors_dvd {M : ℕ} (hM : M ≠ 0) :
    (∏ p ∈ M.primeFactors, p) ∣ M := by
  have hfac : ∏ p ∈ M.primeFactors, p ^ M.factorization p = M :=
    Nat.prod_factorization_pow_eq_self hM
  conv_rhs => rw [← hfac]
  refine Finset.prod_dvd_prod_of_dvd (fun p : ℕ => p)
    (fun p : ℕ => p ^ M.factorization p) fun p hp => ?_
  have hpos : 1 ≤ M.factorization p := by
    have hne : M.factorization p ≠ 0 := (Finsupp.mem_support_iff.mp hp)
    omega
  simpa only [pow_one] using pow_dvd_pow p hpos

/-- The product of all distinct odd prime factors of `M ≠ 0` divides `ordCompl[2] M`. -/
theorem prod_oddPrimeFactors_dvd_ordCompl {M : ℕ} (hM : M ≠ 0) :
    (∏ p ∈ oddPrimeFactors M, p) ∣ ordCompl[2] M := by
  have hdvdM : (∏ p ∈ oddPrimeFactors M, p) ∣ M :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (oddPrimeFactors_subset_primeFactors M)).trans
      (prod_primeFactors_dvd hM)
  have hcop : (∏ p ∈ oddPrimeFactors M, p).Coprime (2 ^ M.factorization 2) := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    obtain ⟨hprime, hne2, _, _⟩ := mem_oddPrimeFactors_iff.mp hp
    exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hne2).pow_right _
  refine hcop.dvd_of_dvd_mul_left ?_
  rwa [Nat.ordProj_mul_ordCompl_eq_self]

/-- Exponential bound `2 ^ ω(M) ≤ M` for every `M > 0`. -/
theorem two_pow_omega_le {M : ℕ} (hM : 0 < M) : 2 ^ omega M ≤ M := by
  have h1 : 2 ^ omega M ≤ ∏ p ∈ M.primeFactors, p := by
    rw [omega, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  exact h1.trans (Nat.le_of_dvd hM (prod_primeFactors_dvd hM.ne'))

/-- Sharp odd-prime exponential bound `3 ^ ω_odd(M) ≤ ordCompl[2] M` for every `M > 0`. -/
theorem three_pow_omegaOdd_le_ordCompl {M : ℕ} (hM : 0 < M) :
    3 ^ omegaOdd M ≤ ordCompl[2] M := by
  have h1 : 3 ^ omegaOdd M ≤ ∏ p ∈ oddPrimeFactors M, p := by
    rw [omegaOdd, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => three_le_of_mem_oddPrimeFactors hp
  have hpos : 0 < ordCompl[2] M := Nat.ordCompl_pos 2 hM.ne'
  exact h1.trans (Nat.le_of_dvd hpos (prod_oddPrimeFactors_dvd_ordCompl hM.ne'))

/-- Odd-prime exponential bound `3 ^ ω_odd(M) ≤ M` for every `M > 0`. -/
theorem three_pow_omegaOdd_le {M : ℕ} (hM : 0 < M) : 3 ^ omegaOdd M ≤ M :=
  (three_pow_omegaOdd_le_ordCompl hM).trans (Nat.ordCompl_le M 2)

/-- Explicit prime-divisor count bound `ω(M) ≤ log₂ M` (`Real.logb 2 M`). -/
theorem omega_le_log2 {M : ℕ} (hM : 0 < M) :
    (omega M : ℝ) ≤ Real.logb 2 (M : ℝ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : (2 : ℝ) ^ omega M ≤ (M : ℝ) := by exact_mod_cast two_pow_omega_le hM
  have hlog := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at hlog
  rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact hlog

/-- Explicit odd prime-divisor count bound `ω_odd(M) ≤ log₃ M` (`Real.logb 3 M`). -/
theorem omegaOdd_le_log3 {M : ℕ} (hM : 0 < M) :
    (omegaOdd M : ℝ) ≤ Real.logb 3 (M : ℝ) := by
  have h3 : (3 : ℝ) ^ omegaOdd M ≤ (M : ℝ) := by exact_mod_cast three_pow_omegaOdd_le hM
  have hlog := Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at hlog
  rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
  exact hlog

/-- Odd prime-divisor count bound `ω_odd(M) ≤ log₂ M`. -/
theorem omegaOdd_le_log2 {M : ℕ} (hM : 0 < M) :
    (omegaOdd M : ℝ) ≤ Real.logb 2 (M : ℝ) :=
  le_trans (by exact_mod_cast omegaOdd_le_omega M) (omega_le_log2 hM)

/-- Prime-power valuation bound `v_p(M) ≤ log_p M` and `v_p(M) ≤ log₂ M`. -/
theorem factorization_le_logb {M p : ℕ} (hM : 0 < M) (hp : p.Prime) :
    (M.factorization p : ℝ) ≤ Real.logb (p : ℝ) (M : ℝ) ∧
      (M.factorization p : ℝ) ≤ Real.logb 2 (M : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h2p : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hdvd : p ^ M.factorization p ∣ M := Nat.ordProj_dvd M p
  have hpow : (p : ℝ) ^ M.factorization p ≤ (M : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hM hdvd
  have hlogp : (M.factorization p : ℝ) * Real.log (p : ℝ) ≤ Real.log (M : ℝ) := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  have h1 : (M.factorization p : ℝ) ≤ Real.logb (p : ℝ) (M : ℝ) := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos hp1)]
    exact hlogp
  have h2 : (M.factorization p : ℝ) ≤ Real.logb 2 (M : ℝ) := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    have hl2p : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) h2p
    exact le_trans (mul_le_mul_of_nonneg_left hl2p (Nat.cast_nonneg _)) hlogp
  exact ⟨h1, h2⟩

/-- The sum of logs of odd prime factors of `M > 0` is bounded by `log (ordCompl[2] M) ≤ log M`. -/
theorem sum_log_oddPrimeFactors_le_ordCompl {M : ℕ} (hM : 0 < M) :
    ∑ l ∈ oddPrimeFactors M, Real.log (l : ℝ) ≤ Real.log ((ordCompl[2] M : ℕ) : ℝ) := by
  have hprod_pos : (0 : ℝ) < ((∏ l ∈ oddPrimeFactors M, l : ℕ) : ℝ) := by
    have hpos : 0 < ∏ l ∈ oddPrimeFactors M, l :=
      Finset.prod_pos fun l hl => (mem_oddPrimeFactors_iff.mp hl).1.pos
    exact_mod_cast hpos
  have hcast : ∑ l ∈ oddPrimeFactors M, Real.log (l : ℝ) =
      Real.log ((∏ l ∈ oddPrimeFactors M, l : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro l hl
    exact_mod_cast (mem_oddPrimeFactors_iff.mp hl).1.ne_zero
  rw [hcast]
  refine Real.log_le_log hprod_pos ?_
  have hpos : 0 < ordCompl[2] M := Nat.ordCompl_pos 2 hM.ne'
  exact Nat.cast_le.mpr (Nat.le_of_dvd hpos (prod_oddPrimeFactors_dvd_ordCompl hM.ne'))

theorem sum_log_oddPrimeFactors_le {M : ℕ} (hM : 0 < M) :
    ∑ l ∈ oddPrimeFactors M, Real.log (l : ℝ) ≤ Real.log (M : ℝ) := by
  refine (sum_log_oddPrimeFactors_le_ordCompl hM).trans ?_
  have hpos : (0 : ℝ) < ((ordCompl[2] M : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.ordCompl_pos 2 hM.ne')
  exact Real.log_le_log hpos (Nat.cast_le.mpr (Nat.ordCompl_le M 2))

/-- Every odd prime factor of the minimal cyclotomic 2-tower conductor `HostFieldSupply.QS Ξ e`
already divides `M`. -/
theorem oddPrimeFactors_QS_subset {M : ℕ} [NeZero M]
    (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) :
    oddPrimeFactors (HostFieldSupply.QS Ξ e) ⊆ oddPrimeFactors M := by
  intro p hp
  obtain ⟨hprime, hne2, hdvdQ, _⟩ := mem_oddPrimeFactors_iff.mp hp
  have hdvdMul : p ∣ 2 ^ (e + 2) * M := hdvdQ.trans (HostFieldSupply.QS_dvd_mul Ξ e)
  have hdvdM : p ∣ M := (hprime.dvd_mul.mp hdvdMul).resolve_left fun h2 =>
    hne2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow h2))
  exact mem_oddPrimeFactors_iff.mpr ⟨hprime, hne2, hdvdM, NeZero.ne M⟩

/-- **Exact Odd Prime-Factor Invariance Along the Cyclotomic 2-Tower**:
For every primitive Dirichlet character `χ` mod `M` and tower level `e`,
`oddPrimeFactors (HostFieldSupply.QS (Subgroup.zpowers χ) e) = oddPrimeFactors M`. -/
theorem oddPrimeFactors_QS_zpowers_eq {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (hχ : χ.IsPrimitive) (e : ℕ) :
    oddPrimeFactors (HostFieldSupply.QS (Subgroup.zpowers χ) e) = oddPrimeFactors M := by
  apply Finset.Subset.antisymm (oddPrimeFactors_QS_subset _ e)
  intro p hp
  obtain ⟨hprime, hne2, hdvdM, _⟩ := mem_oddPrimeFactors_iff.mp hp
  have hMQ : M ∣ HostFieldSupply.QS (Subgroup.zpowers χ) e :=
    HostFieldSupply.primitive_conductor_dvd_QS χ hχ e
  exact mem_oddPrimeFactors_iff.mpr
    ⟨hprime, hne2, hdvdM.trans hMQ, (HostFieldSupply.QS_pos _ e).ne'⟩

/-- Conductor odd-prime decomposition: if `N ∣ 2^(e+2) * M * q * d` (with `q, d` prime), then
every odd prime dividing `N` either divides `M` or equals `q` or `d`, so `ω_odd(N) ≤ ω_odd(M) + 2`. -/
theorem oddPrimeFactors_dvd_conductor_subset {N M e q d : ℕ} (hM : M ≠ 0)
    (hq : q.Prime) (hd : d.Prime) (hN : N ∣ 2 ^ (e + 2) * M * q * d) :
    oddPrimeFactors N ⊆ insert q (insert d (oddPrimeFactors M)) := by
  intro p hp
  obtain ⟨hprime, hne2, hpN, _⟩ := mem_oddPrimeFactors_iff.mp hp
  have h1 : p ∣ 2 ^ (e + 2) * M * q * d := hpN.trans hN
  rcases hprime.dvd_mul.mp h1 with h2 | hpd
  · rcases hprime.dvd_mul.mp h2 with h3 | hpq
    · have hpM : p ∣ M := (hprime.dvd_mul.mp h3).resolve_left fun h2p =>
        hne2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow h2p))
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (mem_oddPrimeFactors_iff.mpr ⟨hprime, hne2, hpM, hM⟩))
    · have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hprime hq).mp hpq
      rw [hpeq]
      exact Finset.mem_insert_self q _
  · have hpeq : p = d := (Nat.prime_dvd_prime_iff_eq hprime hd).mp hpd
    rw [hpeq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self d _)

theorem omegaOdd_le_add_two_of_dvd_conductor {N M e q d : ℕ} (hM : M ≠ 0)
    (hq : q.Prime) (hd : d.Prime) (hN : N ∣ 2 ^ (e + 2) * M * q * d) :
    omegaOdd N ≤ omegaOdd M + 2 := by
  have hsub := oddPrimeFactors_dvd_conductor_subset hM hq hd hN
  calc omegaOdd N
      ≤ (insert q (insert d (oddPrimeFactors M))).card := Finset.card_le_card hsub
    _ ≤ (insert d (oddPrimeFactors M)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (oddPrimeFactors M).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ = omegaOdd M + 2 := by rfl

/-! ## Section 2: Local Tame & Wild Ramification Conductors and Inertia-Coinvariant Rank Bounds -/

section LocalRamification

variable {K : Type*} [Field K] {I : Type*} [Group I]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Inertia invariants `V^I = { v ∈ V | ∀ g ∈ I, ρ(g) v = v }`. -/
def inertiaInvariants (ρ : I →* (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ g : I, ρ g v = v}
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero (ρ g)
  smul_mem' c {x} hx g := by rw [map_smul, hx g]

theorem mem_inertiaInvariants_iff (ρ : I →* (V ≃ₗ[K] V)) (v : V) :
    v ∈ inertiaInvariants ρ ↔ ∀ g : I, ρ g v = v := Iff.rfl

/-- Inertia augmentation submodule `I·V = span_K { ρ(g) v - v | g ∈ I, v ∈ V }`. -/
def inertiaAugmentation (ρ : I →* (V ≃ₗ[K] V)) : Submodule K V :=
  Submodule.span K {w : V | ∃ (g : I) (v : V), w = ρ g v - v}

/-- Inertia coinvariants `V_I = V ⧸ (I·V)`. -/
abbrev inertiaCoinvariants (ρ : I →* (V ≃ₗ[K] V)) : Type _ :=
  V ⧸ inertiaAugmentation ρ

/-- Restrict an inertia action `ρ : I →* GL(V)` to a subgroup `H ≤ I`. -/
def restrictInertia (ρ : I →* (V ≃ₗ[K] V)) (H : Subgroup I) : H →* (V ≃ₗ[K] V) :=
  ρ.comp H.subtype

/-- Tame Artin conductor exponent `dim_K(V / V^I)`. -/
def tameConductorExp (ρ : I →* (V ≃ₗ[K] V)) : ℕ :=
  Module.finrank K (V ⧸ inertiaInvariants ρ)

theorem finrank_inertiaInvariants_le [FiniteDimensional K V] (ρ : I →* (V ≃ₗ[K] V)) :
    Module.finrank K (inertiaInvariants ρ) ≤ Module.finrank K V :=
  Submodule.finrank_le (inertiaInvariants ρ)

theorem finrank_inertiaCoinvariants_le [FiniteDimensional K V] (ρ : I →* (V ≃ₗ[K] V)) :
    Module.finrank K (inertiaCoinvariants ρ) ≤ Module.finrank K V := by
  dsimp only [inertiaCoinvariants]
  have h := Submodule.finrank_quotient_add_finrank (inertiaAugmentation ρ)
  omega

theorem tameConductorExp_add_invariants [FiniteDimensional K V] (ρ : I →* (V ≃ₗ[K] V)) :
    tameConductorExp ρ + Module.finrank K (inertiaInvariants ρ) = Module.finrank K V :=
  Submodule.finrank_quotient_add_finrank (inertiaInvariants ρ)

theorem tameConductorExp_eq_sub [FiniteDimensional K V] (ρ : I →* (V ≃ₗ[K] V)) :
    tameConductorExp ρ = Module.finrank K V - Module.finrank K (inertiaInvariants ρ) := by
  have h := tameConductorExp_add_invariants ρ
  omega

theorem tameConductorExp_le_dim [FiniteDimensional K V] (ρ : I →* (V ≃ₗ[K] V)) :
    tameConductorExp ρ ≤ Module.finrank K V := by
  have h := tameConductorExp_add_invariants ρ
  omega

theorem inertiaInvariants_eq_top_of_unramified (ρ : I →* (V ≃ₗ[K] V))
    (hunram : ∀ g : I, ρ g = LinearEquiv.refl K V) :
    inertiaInvariants ρ = ⊤ := by
  ext v
  simp [mem_inertiaInvariants_iff, hunram]

theorem inertiaAugmentation_eq_bot_of_unramified (ρ : I →* (V ≃ₗ[K] V))
    (hunram : ∀ g : I, ρ g = LinearEquiv.refl K V) :
    inertiaAugmentation ρ = ⊥ := by
  rw [inertiaAugmentation, Submodule.span_eq_bot]
  rintro w ⟨g, v, rfl⟩
  simp [hunram]

theorem tameConductorExp_eq_zero_of_unramified (ρ : I →* (V ≃ₗ[K] V))
    (hunram : ∀ g : I, ρ g = LinearEquiv.refl K V) :
    tameConductorExp ρ = 0 := by
  unfold tameConductorExp
  rw [inertiaInvariants_eq_top_of_unramified ρ hunram]
  have : Subsingleton (V ⧸ (⊤ : Submodule K V)) := Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

/-- **1-Dimensional Inertia Dichotomy**: on a 1-dimensional representation `V`, a ramified
inertia action has `V^I = ⊥` and `tameConductorExp ρ = 1`. -/
theorem tameConductorExp_one_dim_of_ramified [FiniteDimensional K V]
    (ρ : I →* (V ≃ₗ[K] V)) (hdim : Module.finrank K V = 1)
    (hram : ∃ g : I, ρ g ≠ LinearEquiv.refl K V) :
    Module.finrank K (inertiaInvariants ρ) = 0 ∧ tameConductorExp ρ = 1 := by
  have hadd := tameConductorExp_add_invariants ρ
  rw [hdim] at hadd
  have hne1 : Module.finrank K (inertiaInvariants ρ) ≠ 1 := by
    intro h1
    have htop : inertiaInvariants ρ = ⊤ :=
      Submodule.eq_top_of_finrank_eq (h1.trans hdim.symm)
    obtain ⟨g, hg⟩ := hram
    apply hg
    ext v
    have hv : v ∈ inertiaInvariants ρ := by rw [htop]; trivial
    exact hv g
  exact ⟨by omega, by omega⟩

/-- Monotonicity of inertia invariants along subgroup inclusion `H₁ ≤ H₂`. -/
theorem inertiaInvariants_antitone (ρ : I →* (V ≃ₗ[K] V)) {H₁ H₂ : Subgroup I} (h : H₁ ≤ H₂) :
    inertiaInvariants (restrictInertia ρ H₂) ≤ inertiaInvariants (restrictInertia ρ H₁) := by
  intro v hv g
  exact hv ⟨g.1, h g.2⟩

/-- Monotonicity of tame conductor exponents along subgroup inclusion `H₁ ≤ H₂`. -/
theorem tameConductorExp_mono [FiniteDimensional K V] (ρ : I →* (V ≃ₗ[K] V))
    {H₁ H₂ : Subgroup I} (h : H₁ ≤ H₂) :
    tameConductorExp (restrictInertia ρ H₁) ≤ tameConductorExp (restrictInertia ρ H₂) := by
  have h1 := tameConductorExp_add_invariants (restrictInertia ρ H₁)
  have h2 := tameConductorExp_add_invariants (restrictInertia ρ H₂)
  have hle : Module.finrank K (inertiaInvariants (restrictInertia ρ H₂)) ≤
      Module.finrank K (inertiaInvariants (restrictInertia ρ H₁)) :=
    Submodule.finrank_mono (inertiaInvariants_antitone ρ h)
  omega

/-- Reynolds / Maschke averaging projection `P_I(v) = (|I| : K)⁻¹ • ∑_{g ∈ I} ρ(g) v`
for finite tame inertia (`(|I| : K) ≠ 0`). -/
def reynoldsProj [Fintype I] (ρ : I →* (V ≃ₗ[K] V)) : V →ₗ[K] V :=
  ((Fintype.card I : K)⁻¹) • ∑ g : I, (ρ g).toLinearMap

theorem reynoldsProj_apply [Fintype I] (ρ : I →* (V ≃ₗ[K] V)) (v : V) :
    reynoldsProj ρ v = ((Fintype.card I : K)⁻¹) • ∑ g : I, ρ g v := by
  simp [reynoldsProj]

theorem map_reynoldsProj [Fintype I] (ρ : I →* (V ≃ₗ[K] V)) (h : I) (v : V) :
    ρ h (reynoldsProj ρ v) = reynoldsProj ρ v := by
  rw [reynoldsProj_apply, map_smul, map_sum]
  congr 1
  have hsum : (∑ g : I, ρ h (ρ g v)) = ∑ g : I, ρ (h * g) v := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul, LinearEquiv.mul_apply]
  rw [hsum]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)

theorem reynoldsProj_map [Fintype I] (ρ : I →* (V ≃ₗ[K] V)) (h : I) (v : V) :
    reynoldsProj ρ (ρ h v) = reynoldsProj ρ v := by
  rw [reynoldsProj_apply, reynoldsProj_apply]
  congr 1
  have hsum : (∑ g : I, ρ g (ρ h v)) = ∑ g : I, ρ (g * h) v := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul, LinearEquiv.mul_apply]
  rw [hsum]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun _ => rfl)

theorem reynoldsProj_apply_of_mem_invariants [Fintype I] (ρ : I →* (V ≃ₗ[K] V))
    (hcard : (Fintype.card I : K) ≠ 0) {v : V} (hv : v ∈ inertiaInvariants ρ) :
    reynoldsProj ρ v = v := by
  rw [reynoldsProj_apply]
  have hsum : (∑ g : I, ρ g v) = (Fintype.card I : K) • v := by
    calc (∑ g : I, ρ g v) = ∑ _g : I, v := Finset.sum_congr rfl fun g _ => hv g
      _ = Fintype.card I • v := by simp
      _ = (Fintype.card I : K) • v := (Nat.cast_smul_eq_nsmul K (Fintype.card I) v).symm
  rw [hsum, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem reynoldsProj_idempotent [Fintype I] (ρ : I →* (V ≃ₗ[K] V))
    (hcard : (Fintype.card I : K) ≠ 0) (v : V) :
    reynoldsProj ρ (reynoldsProj ρ v) = reynoldsProj ρ v :=
  reynoldsProj_apply_of_mem_invariants ρ hcard (fun h => map_reynoldsProj ρ h v)

theorem range_reynoldsProj [Fintype I] (ρ : I →* (V ≃ₗ[K] V))
    (hcard : (Fintype.card I : K) ≠ 0) :
    LinearMap.range (reynoldsProj ρ) = inertiaInvariants ρ := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩ h
    exact map_reynoldsProj ρ h w
  · intro hv
    exact ⟨v, reynoldsProj_apply_of_mem_invariants ρ hcard hv⟩

theorem ker_reynoldsProj [Fintype I] (ρ : I →* (V ≃ₗ[K] V))
    (hcard : (Fintype.card I : K) ≠ 0) :
    LinearMap.ker (reynoldsProj ρ) = inertiaAugmentation ρ := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have hdiff : v = -((Fintype.card I : K)⁻¹ • ∑ g : I, (ρ g v - v)) := by
      have h1 : (∑ g : I, (ρ g v - v)) = (∑ g : I, ρ g v) - (Fintype.card I : K) • v := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Nat.cast_smul_eq_nsmul K (Fintype.card I) v]
      rw [h1, smul_sub, smul_smul, inv_mul_cancel₀ hcard, one_smul]
      have h0 : ((Fintype.card I : K)⁻¹) • ∑ g : I, ρ g v = 0 := by
        rwa [← reynoldsProj_apply]
      rw [h0, zero_sub, neg_neg]
    rw [hdiff]
    refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => ?_))
    exact Submodule.subset_span ⟨g, v, rfl⟩
  · rw [inertiaAugmentation, Submodule.span_le]
    rintro w ⟨g, v, rfl⟩
    change reynoldsProj ρ (ρ g v - v) = 0
    rw [map_sub, reynoldsProj_map, sub_self]

/-- **Tame Inertia Invariant–Coinvariant Isomorphism (`V_I ≃ₗ[K] V^I`)**:
When `(|I| : K) ≠ 0`, the Reynolds projection identifies inertia coinvariants with inertia
invariants. -/
def inertiaCoinvariantsEquivInvariants [Fintype I] (ρ : I →* (V ≃ₗ[K] V))
    (hcard : (Fintype.card I : K) ≠ 0) :
    inertiaCoinvariants ρ ≃ₗ[K] inertiaInvariants ρ :=
  (Submodule.quotEquivOfEq _ _ (ker_reynoldsProj ρ hcard).symm).trans
    ((reynoldsProj ρ).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (range_reynoldsProj ρ hcard)))

/-- **Tame Inertia-Coinvariant Rank Identity**: when `(|I| : K) ≠ 0`,
`dim_K(V_I) = dim_K(V^I)` and `tameConductorExp ρ = dim_K(V) - dim_K(V_I)`. -/
theorem finrank_inertiaCoinvariants_eq_invariants_of_tame [Fintype I] [FiniteDimensional K V]
    (ρ : I →* (V ≃ₗ[K] V)) (hcard : (Fintype.card I : K) ≠ 0) :
    Module.finrank K (inertiaCoinvariants ρ) = Module.finrank K (inertiaInvariants ρ) ∧
      tameConductorExp ρ + Module.finrank K (inertiaCoinvariants ρ) = Module.finrank K V := by
  have heq : Module.finrank K (inertiaCoinvariants ρ) = Module.finrank K (inertiaInvariants ρ) :=
    (inertiaCoinvariantsEquivInvariants ρ hcard).finrank_eq
  exact ⟨heq, by rw [heq]; exact tameConductorExp_add_invariants ρ⟩

/-- A finite higher ramification filtration `I = G_0 ≥ G_1 ≥ ... ≥ G_cutoff = ⊥`. -/
structure RamificationFiltration (I : Type*) [Group I] where
  sub : ℕ → Subgroup I
  sub_zero : sub 0 = ⊤
  antitone : Antitone sub
  cutoff : ℕ
  cutoff_pos : 0 < cutoff
  sub_cutoff : sub cutoff = ⊥

/-- The **wild Swan conductor** `sw(ρ) = ∑_{i=1}^{cutoff-1} (|G_i| / |G_0|) · dim(V / V^{G_i})`. -/
def swanConductor (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I) : ℝ :=
  ∑ i ∈ Finset.Ico 1 F.cutoff,
    ((Nat.card (F.sub i) : ℝ) / (Nat.card (F.sub 0) : ℝ)) *
      (tameConductorExp (restrictInertia ρ (F.sub i)) : ℝ)

/-- The **Artin conductor exponent** `a(ρ) = dim(V / V^{I}) + sw(ρ)`. -/
def artinConductorExp (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I) : ℝ :=
  (tameConductorExp ρ : ℝ) + swanConductor ρ F

theorem swanConductor_nonneg (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I) :
    0 ≤ swanConductor ρ F :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem artinConductorExp_nonneg (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I) :
    0 ≤ artinConductorExp ρ F :=
  add_nonneg (Nat.cast_nonneg _) (swanConductor_nonneg ρ F)

/-- **Tame Vanishing of the Swan Conductor**: if wild inertia `F.sub 1` acts trivially on `V`,
then `sw(ρ) = 0` and `a(ρ) = dim(V / V^I) ≤ dim(V)`. -/
theorem swanConductor_eq_zero_of_tame (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I)
    (htame : ∀ g : I, g ∈ F.sub 1 → ρ g = LinearEquiv.refl K V) :
    swanConductor ρ F = 0 := by
  unfold swanConductor
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hsub : F.sub i ≤ F.sub 1 := F.antitone hi1
  have hunram : ∀ g : F.sub i, restrictInertia ρ (F.sub i) g = LinearEquiv.refl K V :=
    fun g => htame g.1 (hsub g.2)
  rw [tameConductorExp_eq_zero_of_unramified _ hunram]
  simp

theorem artinConductorExp_eq_tame_of_tame (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I)
    (htame : ∀ g : I, g ∈ F.sub 1 → ρ g = LinearEquiv.refl K V) :
    artinConductorExp ρ F = (tameConductorExp ρ : ℝ) := by
  rw [artinConductorExp, swanConductor_eq_zero_of_tame ρ F htame, add_zero]

/-- **Unramified Vanishing**: if `I` acts trivially on `V`, then `a(ρ) = 0`. -/
theorem artinConductorExp_eq_zero_of_unramified (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I)
    (hunram : ∀ g : I, ρ g = LinearEquiv.refl K V) :
    artinConductorExp ρ F = 0 := by
  rw [artinConductorExp_eq_tame_of_tame ρ F (fun g _ => hunram g),
    tameConductorExp_eq_zero_of_unramified ρ hunram]
  simp

/-- **Wild Swan Conductor Rank Bound**:
`sw(ρ) ≤ dim(V) · ∑_{i=1}^{cutoff-1} |G_i| / |G_0|`. -/
theorem swanConductor_le_dim_mul_sum_ratios [FiniteDimensional K V]
    (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I) :
    swanConductor ρ F ≤
      (Module.finrank K V : ℝ) *
        ∑ i ∈ Finset.Ico 1 F.cutoff, (Nat.card (F.sub i) : ℝ) / (Nat.card (F.sub 0) : ℝ) := by
  rw [swanConductor, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle : (tameConductorExp (restrictInertia ρ (F.sub i)) : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast tameConductorExp_le_dim (restrictInertia ρ (F.sub i))
  rw [mul_comm (Module.finrank K V : ℝ)]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- **Uniform Artin Conductor Exponent Bound**:
For any finite inertia group `I` with filtration `F`, `a(ρ) ≤ F.cutoff · dim(V)`. -/
theorem artinConductorExp_le_cutoff_mul_dim [Finite I] [FiniteDimensional K V]
    (ρ : I →* (V ≃ₗ[K] V)) (F : RamificationFiltration I) :
    artinConductorExp ρ F ≤ (F.cutoff : ℝ) * (Module.finrank K V : ℝ) := by
  have h0pos : 0 < Nat.card (F.sub 0) := Nat.card_pos
  have hratio : ∀ i ∈ Finset.Ico 1 F.cutoff,
      (Nat.card (F.sub i) : ℝ) / (Nat.card (F.sub 0) : ℝ) ≤ 1 := by
    intro i _
    rw [div_le_one (by exact_mod_cast h0pos)]
    exact_mod_cast Subgroup.card_le_of_le (F.antitone (Nat.zero_le i))
  have hsum : ∑ i ∈ Finset.Ico 1 F.cutoff, (Nat.card (F.sub i) : ℝ) / (Nat.card (F.sub 0) : ℝ) ≤
      ((F.cutoff - 1 : ℕ) : ℝ) := by
    calc ∑ i ∈ Finset.Ico 1 F.cutoff, (Nat.card (F.sub i) : ℝ) / (Nat.card (F.sub 0) : ℝ)
        ≤ ∑ _i ∈ Finset.Ico 1 F.cutoff, (1 : ℝ) := Finset.sum_le_sum hratio
      _ = ((F.cutoff - 1 : ℕ) : ℝ) := by simp
  have htame : (tameConductorExp ρ : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast tameConductorExp_le_dim ρ
  have hsw := (swanConductor_le_dim_mul_sum_ratios ρ F).trans
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  have hcut : (1 : ℝ) + ((F.cutoff - 1 : ℕ) : ℝ) = (F.cutoff : ℝ) := by
    have h1 := F.cutoff_pos
    have : 1 + (F.cutoff - 1) = F.cutoff := by omega
    exact_mod_cast this
  rw [artinConductorExp]
  nlinarith

end LocalRamification

/-! ### Exact `p`-adic Cyclotomic Unit Filtration & Telescoping Artin Conductor Identity -/

/-- Higher unit filtration subgroup `U_k = { u ∈ (ZMod (p^a))ˣ | u ≡ 1 (mod p^k) }` (`k ≤ a`). -/
def unitFiltration (p a k : ℕ) (hk : k ≤ a) : Subgroup (ZMod (p ^ a))ˣ :=
  (ZMod.unitsMap (pow_dvd_pow p hk)).ker

/-- **Exact Higher-Unit Subgroup Order**: for a prime `p` and `1 ≤ k ≤ a`,
`Nat.card (unitFiltration p a k hk) = p ^ (a - k)`. -/
theorem card_unitFiltration {p a k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hka : k ≤ a) :
    Nat.card (unitFiltration p a k hka) = p ^ (a - k) := by
  have ha1 : 1 ≤ a := le_trans hk1 hka
  have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  let f := ZMod.unitsMap (pow_dvd_pow p hka)
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective (pow_dvd_pow p hka)
  have hlag := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top] at hlag
  have hcard_a : Nat.card (ZMod (p ^ a))ˣ = p ^ (a - 1) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp ha1]
  have hcard_k : Nat.card (ZMod (p ^ k))ˣ = p ^ (k - 1) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hk1]
  rw [hcard_a, hcard_k] at hlag
  have hpos : 0 < p ^ (k - 1) * (p - 1) :=
    Nat.mul_pos (pow_pos hp.pos _) (Nat.sub_pos_of_lt hp.one_lt)
  have hsplit : p ^ (a - 1) * (p - 1) = p ^ (a - k) * (p ^ (k - 1) * (p - 1)) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hsplit] at hlag
  exact Nat.eq_of_mul_eq_mul_right hpos hlag

/-- **Exact Cyclotomic Local Artin Conductor Identity (`ℚ_p(ζ_{p^a}) / ℚ_p`)**:
Summing the lower-numbering ramification blocks `m ∈ [1, a)` (of length `p^m - p^{m-1}` with
subgroup `U_m` of order `p^{a-m}`) inside `G_0 = (ZMod (p^a))ˣ` evaluates telescopically to
`1 + ∑_{m=1}^{a-1} (p^m - p^{m-1}) · |U_m| / |G_0| = a`, matching `v_p(f_χ) = a`! -/
theorem cyclotomic_artin_conductor_exact {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (1 : ℝ) +
      ∑ m ∈ (Finset.Ico 1 a).attach,
        (((p ^ m.1 - p ^ (m.1 - 1) : ℕ) : ℝ) *
          ((Nat.card (unitFiltration p a m.1 (le_of_lt (Finset.mem_Ico.mp m.2).2)) : ℝ) /
            (Nat.card (ZMod (p ^ a))ˣ : ℝ))) = (a : ℝ) := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have hcard_a : Nat.card (ZMod (p ^ a))ˣ = p ^ (a - 1) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp ha]
  have hterm : ∀ m : {x // x ∈ Finset.Ico 1 a},
      (((p ^ m.1 - p ^ (m.1 - 1) : ℕ) : ℝ) *
        ((Nat.card (unitFiltration p a m.1 (le_of_lt (Finset.mem_Ico.mp m.2).2)) : ℝ) /
          (Nat.card (ZMod (p ^ a))ˣ : ℝ))) = 1 := by
    intro m
    have hm1 : 1 ≤ m.1 := (Finset.mem_Ico.mp m.2).1
    have hma : m.1 < a := (Finset.mem_Ico.mp m.2).2
    rw [card_unitFiltration hp hm1 (le_of_lt hma), hcard_a]
    have hsub : p ^ m.1 - p ^ (m.1 - 1) = p ^ (m.1 - 1) * (p - 1) := by
      cases hm : m.1 with
      | zero => omega
      | succ k => simp [pow_succ, Nat.mul_sub_left_distrib]
    rw [hsub]
    have hpow_eq : p ^ (m.1 - 1) * p ^ (a - m.1) = p ^ (a - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hden_pos : (0 : ℝ) < ((p ^ (a - 1) * (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (pow_pos hp.pos _) (Nat.sub_pos_of_lt hp.one_lt)
    rw [mul_div_assoc', div_eq_one_iff_eq hden_pos.ne']
    have hnat : (p ^ (m.1 - 1) * (p - 1)) * p ^ (a - m.1) = p ^ (a - 1) * (p - 1) := by
      calc (p ^ (m.1 - 1) * (p - 1)) * p ^ (a - m.1)
          = (p ^ (m.1 - 1) * p ^ (a - m.1)) * (p - 1) := by ring
        _ = p ^ (a - 1) * (p - 1) := by rw [hpow_eq]
    exact_mod_cast hnat
  have hsum : ∑ m ∈ (Finset.Ico 1 a).attach,
      (((p ^ m.1 - p ^ (m.1 - 1) : ℕ) : ℝ) *
        ((Nat.card (unitFiltration p a m.1 (le_of_lt (Finset.mem_Ico.mp m.2).2)) : ℝ) /
          (Nat.card (ZMod (p ^ a))ˣ : ℝ))) = ((a - 1 : ℕ) : ℝ) := by
    calc _ = ∑ _m ∈ (Finset.Ico 1 a).attach, (1 : ℝ) := Finset.sum_congr rfl fun m _ => hterm m
      _ = ((a - 1 : ℕ) : ℝ) := by simp
  rw [hsum]
  have h1a : 1 + (a - 1) = a := by omega
  exact_mod_cast h1a

/-- **Combined Cyclotomic Conductor & Valuation Bound**: for any `M > 0` and prime `p ∣ M`,
setting `a = M.factorization p`, the exact cyclotomic Artin conductor exponent at `p` equals
`a` and satisfies `a ≤ log_p M ≤ log₂ M`. -/
theorem cyclotomic_conductor_exp_le_logb {M p : ℕ} (hM : 0 < M) (hp : p.Prime) (hdvd : p ∣ M) :
    let a := M.factorization p
    1 ≤ a ∧
      (1 : ℝ) +
        ∑ m ∈ (Finset.Ico 1 a).attach,
          (((p ^ m.1 - p ^ (m.1 - 1) : ℕ) : ℝ) *
            ((Nat.card (unitFiltration p a m.1 (le_of_lt (Finset.mem_Ico.mp m.2).2)) : ℝ) /
              (Nat.card (ZMod (p ^ a))ˣ : ℝ))) = (a : ℝ) ∧
      (a : ℝ) ≤ Real.logb (p : ℝ) (M : ℝ) ∧
      (a : ℝ) ≤ Real.logb 2 (M : ℝ) := by
  have ha1 : 1 ≤ M.factorization p := by
    have hpos : 0 < M.factorization p := hp.factorization_pos_of_dvd hM.ne' hdvd
    omega
  obtain ⟨h1, h2⟩ := factorization_le_logb hM hp
  exact ⟨ha1, cyclotomic_artin_conductor_exact hp ha1, h1, h2⟩

/-! ## Section 3: Local Ramified Obstruction Modules & Exact `B_ram` Sum Bounds -/

/-- Local ramified Selmer obstruction data at an odd prime `l ∣ M` and weight `k`:
a local ring `R_l` with simple residue quotient `R_l ⧸ (ϖ)`, a finite-rank obstruction module
`Obs` generated by `genRank` elements (controlled by inertia coinvariants), killed by `ϖ ^ condExp`
(controlled by the local conductor exponent), dominating `S.shaLen E l k`. -/
structure LocalRamifiedObstruction (S : SelmerSystem) (E : Type) [Field E] [NumberField E]
    (l : Nat.Primes) (k : ℕ) where
  R_l : Type
  [commRing : CommRing R_l]
  ϖ : R_l
  [simpleResidue : IsSimpleModule R_l (R_l ⧸ Ideal.span ({ϖ} : Set R_l))]
  Obs : Type
  [addObs : AddCommGroup Obs]
  [modObs : Module R_l Obs]
  genRank : ℕ
  genMap : (Fin genRank → R_l) →ₗ[R_l] Obs
  gen_surj : Function.Surjective genMap
  condExp : ℕ
  ann_pow : ϖ ^ condExp ∈ Module.annihilator R_l Obs
  sha_le_obs : S.shaLen E l k ≤ Module.length R_l Obs

attribute [instance] LocalRamifiedObstruction.commRing LocalRamifiedObstruction.simpleResidue
  LocalRamifiedObstruction.addObs LocalRamifiedObstruction.modObs

/-- Effective integer upper bound `genRank * condExp` produced by a `LocalRamifiedObstruction`. -/
def LocalRamifiedObstruction.bound {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {l : Nat.Primes} {k : ℕ} (O : LocalRamifiedObstruction S E l k) : ℕ :=
  O.genRank * O.condExp

/-- **Local Ramified Selmer Finiteness & Length Bound**:
Discharges both `S.shaLen E l k ≠ ⊤` and `(S.shaLen E l k).toNat ≤ O.genRank * O.condExp`
directly via `TaylorWilesWindow.length_le_of_pow_mem_annihilator`. -/
theorem LocalRamifiedObstruction.shaLen_finite_and_le {S : SelmerSystem} {E : Type}
    [Field E] [NumberField E] {l : Nat.Primes} {k : ℕ}
    (O : LocalRamifiedObstruction S E l k) :
    S.shaLen E l k ≠ ⊤ ∧ (S.shaLen E l k).toNat ≤ O.bound := by
  have hobs : Module.length O.R_l O.Obs ≤ ((O.genRank * O.condExp : ℕ) : ℕ∞) :=
    TaylorWilesWindow.length_le_of_pow_mem_annihilator O.genMap O.gen_surj O.ann_pow
  have hsha : S.shaLen E l k ≤ ((O.genRank * O.condExp : ℕ) : ℕ∞) :=
    O.sha_le_obs.trans hobs
  exact ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hsha, ENat.toNat_le_of_le_natCast hsha⟩

/-- **Chaining Inertia-Coinvariant Rank + Local Conductor Valuation → Selmer Length Bound**:
If `O.genRank` is bounded by `dim_K(V_{I_l})` (for an inertia action `ρ` on a `d`-dimensional
`K`-space `V`) and `O.condExp` is bounded by `M.factorization l * c`, then
`(S.shaLen E l k).toNat ≤ d * c * log_l M ≤ d * c * log₂ M`. -/
theorem LocalRamifiedObstruction.shaLen_le_of_inertia_coinvariant_and_val
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {K I V : Type*} [Field K] [Group I] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {l : Nat.Primes} {k M c : ℕ} (hM : 0 < M)
    (ρ : I →* (V ≃ₗ[K] V)) (O : LocalRamifiedObstruction S E l k)
    (hrank : O.genRank ≤ Module.finrank K (inertiaCoinvariants ρ))
    (hcond : O.condExp ≤ M.factorization (l : ℕ) * c) :
    S.shaLen E l k ≠ ⊤ ∧
      ((S.shaLen E l k).toNat : ℝ) ≤
        (Module.finrank K V : ℝ) * (c : ℝ) * Real.logb (l : ℝ) (M : ℝ) ∧
      ((S.shaLen E l k).toNat : ℝ) ≤
        (Module.finrank K V : ℝ) * (c : ℝ) * Real.logb 2 (M : ℝ) := by
  obtain ⟨hfin, hle⟩ := O.shaLen_finite_and_le
  have hcoinv : O.genRank ≤ Module.finrank K V :=
    hrank.trans (finrank_inertiaCoinvariants_le ρ)
  have hnat : (S.shaLen E l k).toNat ≤ Module.finrank K V * (M.factorization (l : ℕ) * c) :=
    hle.trans (Nat.mul_le_mul hcoinv hcond)
  have hreal : ((S.shaLen E l k).toNat : ℝ) ≤
      (Module.finrank K V : ℝ) * (c : ℝ) * (M.factorization (l : ℕ) : ℝ) := by
    have h : ((S.shaLen E l k).toNat : ℝ) ≤
        ((Module.finrank K V * (M.factorization (l : ℕ) * c) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at h
    linarith
  obtain ⟨hvl1, hvl2⟩ := factorization_le_logb hM l.prop
  refine ⟨hfin, hreal.trans ?_, hreal.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left hvl1 (by positivity)
  · exact mul_le_mul_of_nonneg_left hvl2 (by positivity)

/-- Helper: mapping a `Finset Nat.Primes` of odd divisors of `M ≠ 0` injects into
`oddPrimeFactors M` via `Subtype.val`. -/
theorem sum_primes_le_sum_oddPrimeFactors {M : ℕ} (hM : M ≠ 0)
    (Pram : Finset Nat.Primes) (hP : ∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M)
    (f : ℕ → ℝ) (hf : ∀ l ∈ oddPrimeFactors M, 0 ≤ f l) :
    ∑ l ∈ Pram, f (l : ℕ) ≤ ∑ l ∈ oddPrimeFactors M, f l := by
  have hsub : Pram.image (fun l : Nat.Primes => (l : ℕ)) ⊆ oddPrimeFactors M := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨l, hl, rfl⟩
    exact mem_oddPrimeFactors_iff.mpr ⟨l.prop, (hP l hl).1, (hP l hl).2, hM⟩
  have hinj : Set.InjOn (fun l : Nat.Primes => (l : ℕ)) (Pram : Set Nat.Primes) :=
    fun _ _ _ _ h => Subtype.ext h
  rw [← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hf p hp

/-- **Exact Odd-Ramified Prime Sum Bound (`minusBound` Discharge)**:
If every odd prime `l ∣ M` and weight `1 ≤ k < t` satisfies the local inertia-coinvariant /
conductor bound `(S.shaLen E l k).toNat ≤ C_ram * l * n^2 * t * log(t * l * N)` (with `0 ≤ C_ram`,
`1 ≤ N`, `1 ≤ t`, `M ≠ 0`), then for EVERY finite set `Pram` of odd prime divisors of `M`:
`∑_{l ∈ Pram} log l * ∑_{k=1}^{t-1} (S.shaLen E l k).toNat ≤ TaylorWilesWindow.minusBound C_ram M n N t`! -/
theorem ramified_sum_le_minusBound {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {M n N t : ℕ} {C_ram : ℝ} (hM : M ≠ 0) (hN : 1 ≤ N) (ht : 1 ≤ t) (hC : 0 ≤ C_ram)
    (hbd : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t →
      ((S.shaLen E l k).toNat : ℝ) ≤
        C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) * Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)))
    (Pram : Finset Nat.Primes) (hP : ∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M) :
    ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
      TaylorWilesWindow.minusBound C_ram M n N t := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hterm : ∀ l ∈ Pram,
      Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
          Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) ^ 2 := by
    intro l hl
    obtain ⟨hne2, hdvd⟩ := hP l hl
    have hl_pos : (0 : ℝ) < (l : ℕ) := by exact_mod_cast l.prop.pos
    have hl1 : (1 : ℝ) ≤ (l : ℕ) := by exact_mod_cast l.prop.one_lt.le
    have hlog_nonneg : 0 ≤ Real.log ((l : ℕ) : ℝ) := Real.log_natCast_nonneg (l : ℕ)
    have hlog_le : Real.log ((l : ℕ) : ℝ) ≤ Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) := by
      refine Real.log_le_log hl_pos ?_
      calc ((l : ℕ) : ℝ) = 1 * ((l : ℕ) : ℝ) * 1 := by ring
        _ ≤ (t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ) := by gcongr
    have hlog_tlN_nonneg : 0 ≤ Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) :=
      hlog_nonneg.trans hlog_le
    have hsum_k : ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        (t : ℝ) * (C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) *
          Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ))) := by
      calc ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ)
          ≤ ∑ _k ∈ Finset.Ico 1 t,
              (C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) *
                Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ))) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk' := Finset.mem_Ico.mp hk
              exact hbd l k hne2 hdvd hk'.1 hk'.2
        _ = ((t - 1 : ℕ) : ℝ) * (C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) *
              Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ))) := by
              simp
        _ ≤ (t : ℝ) * (C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) *
              Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ))) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact_mod_cast Nat.sub_le t 1
    calc Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ)
        ≤ Real.log (l : ℕ) * ((t : ℝ) * (C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) *
            Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsum_k hlog_nonneg
      _ ≤ Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) *
            ((t : ℝ) * (C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) *
              Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)))) :=
          mul_le_mul_of_nonneg_right hlog_le (by positivity)
      _ = C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) ^ 2 := by ring
  have hsum1 :
      ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        ∑ l ∈ oddPrimeFactors M,
          C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    exact sum_primes_le_sum_oddPrimeFactors hM Pram hP
      (fun l => C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2)
      (fun _ _ => by positivity)
  have hsum2 :
      ∑ l ∈ oddPrimeFactors M,
        C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
          Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 =
      C_ram * ∑ l ∈ M.primeFactors.erase 2,
        (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
          Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 := by
    rw [oddPrimeFactors, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  have hfirst_nonneg : 0 ≤ 3 * (n : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (N : ℝ)) := by
    have hlog : 0 ≤ Real.log ((t : ℝ) * (N : ℝ)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le ht1 hN1)
    positivity
  unfold TaylorWilesWindow.minusBound
  linarith

/-- Linear-in-weight variant: if `(S.shaLen E l k).toNat ≤ 2 * C_ram * l * n^2 * k * log(t * l * N)`
for `1 ≤ k < t`, then `∑_{k=1}^{t-1} k ≤ t^2 / 2` still yields the exact same `minusBound`! -/
theorem ramified_sum_le_minusBound_of_linear_k {S : SelmerSystem} {E : Type} [Field E]
    [NumberField E] {M n N t : ℕ} {C_ram : ℝ} (hM : M ≠ 0) (hN : 1 ≤ N) (ht : 1 ≤ t)
    (hC : 0 ≤ C_ram)
    (hbd : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t →
      ((S.shaLen E l k).toNat : ℝ) ≤
        2 * C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (k : ℝ) * Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)))
    (Pram : Finset Nat.Primes) (hP : ∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M) :
    ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
      TaylorWilesWindow.minusBound C_ram M n N t := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hsum_Ico : 2 * ∑ k ∈ Finset.Ico 1 t, (k : ℝ) ≤ (t : ℝ) ^ 2 := by
    have hnat : 2 * ∑ k ∈ Finset.range t, k = t * (t - 1) := by
      have := Finset.sum_range_id_mul_two t
      linarith
    have hsub : ∑ k ∈ Finset.Ico 1 t, k ≤ ∑ k ∈ Finset.range t, k :=
      Finset.sum_le_sum_of_subset fun k hk =>
        Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
    have hle : 2 * ∑ k ∈ Finset.Ico 1 t, k ≤ t * t := by
      calc 2 * ∑ k ∈ Finset.Ico 1 t, k ≤ 2 * ∑ k ∈ Finset.range t, k := Nat.mul_le_mul_left 2 hsub
        _ = t * (t - 1) := hnat
        _ ≤ t * t := Nat.mul_le_mul_left t (Nat.sub_le t 1)
    have hleR : ((2 * ∑ k ∈ Finset.Ico 1 t, k : ℕ) : ℝ) ≤ ((t * t : ℕ) : ℝ) := by
      exact_mod_cast hle
    push_cast at hleR
    linarith [sq (t : ℝ)]
  have hterm : ∀ l ∈ Pram,
      Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
          Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) ^ 2 := by
    intro l hl
    obtain ⟨hne2, hdvd⟩ := hP l hl
    have hl_pos : (0 : ℝ) < (l : ℕ) := by exact_mod_cast l.prop.pos
    have hl1 : (1 : ℝ) ≤ (l : ℕ) := by exact_mod_cast l.prop.one_lt.le
    have hlog_nonneg : 0 ≤ Real.log ((l : ℕ) : ℝ) := Real.log_natCast_nonneg (l : ℕ)
    have hlog_le : Real.log ((l : ℕ) : ℝ) ≤ Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) := by
      refine Real.log_le_log hl_pos ?_
      calc ((l : ℕ) : ℝ) = 1 * ((l : ℕ) : ℝ) * 1 := by ring
        _ ≤ (t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ) := by gcongr
    have hlog_tlN_nonneg : 0 ≤ Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) :=
      hlog_nonneg.trans hlog_le
    set A : ℝ := C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 *
      Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) with hA
    have hA0 : 0 ≤ A := by positivity
    have hsum_k : ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤ A * (t : ℝ) ^ 2 := by
      calc ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ)
          ≤ ∑ k ∈ Finset.Ico 1 t, (2 * A * (k : ℝ)) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk' := Finset.mem_Ico.mp hk
              have hb := hbd l k hne2 hdvd hk'.1 hk'.2
              rw [hA]
              linarith
        _ = A * (2 * ∑ k ∈ Finset.Ico 1 t, (k : ℝ)) := by
              rw [← Finset.mul_sum]
              ring
        _ ≤ A * (t : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsum_Ico hA0
    calc Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ)
        ≤ Real.log (l : ℕ) * (A * (t : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsum_k hlog_nonneg
      _ ≤ Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) * (A * (t : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hlog_le (by positivity)
      _ = C_ram * ((l : ℕ) : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log ((t : ℝ) * ((l : ℕ) : ℝ) * (N : ℝ)) ^ 2 := by rw [hA]; ring
  have hsum1 :
      ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        ∑ l ∈ oddPrimeFactors M,
          C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    exact sum_primes_le_sum_oddPrimeFactors hM Pram hP
      (fun l => C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2)
      (fun _ _ => by positivity)
  have hsum2 :
      ∑ l ∈ oddPrimeFactors M,
        C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
          Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 =
      C_ram * ∑ l ∈ M.primeFactors.erase 2,
        (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
          Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ)) ^ 2 := by
    rw [oddPrimeFactors, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  have hfirst_nonneg : 0 ≤ 3 * (n : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (N : ℝ)) := by
    have hlog : 0 ≤ Real.log ((t : ℝ) * (N : ℝ)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le ht1 hN1)
    positivity
  unfold TaylorWilesWindow.minusBound
  linarith

/-- Uniform `ω_odd(M)` / `log M` odd-ramified sum bound: if every odd prime `l ∣ M` and weight
`1 ≤ k < t` has `(S.shaLen E l k).toNat ≤ U`, then the weighted odd-ramified sum is bounded by
`log M * (t * U)` (and by `log₃(M) * log M * (t * U)`). -/
theorem ramified_sum_le_log_mul_uniform {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {M t : ℕ} {U : ℝ} (hM : 0 < M) (hU : 0 ≤ U)
    (hbd : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t →
      ((S.shaLen E l k).toNat : ℝ) ≤ U)
    (Pram : Finset Nat.Primes) (hP : ∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M) :
    ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
      Real.log (M : ℝ) * ((t : ℝ) * U) := by
  have hterm : ∀ l ∈ Pram,
      Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        Real.log (l : ℕ) * ((t : ℝ) * U) := by
    intro l hl
    obtain ⟨hne2, hdvd⟩ := hP l hl
    refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg _)
    calc ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ)
        ≤ ∑ _k ∈ Finset.Ico 1 t, U := Finset.sum_le_sum fun k hk =>
            hbd l k hne2 hdvd (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2
      _ = ((t - 1 : ℕ) : ℝ) * U := by simp
      _ ≤ (t : ℝ) * U := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le t 1) hU
  calc ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ)
      ≤ ∑ l ∈ Pram, Real.log (l : ℕ) * ((t : ℝ) * U) := Finset.sum_le_sum hterm
    _ = (∑ l ∈ Pram, Real.log (l : ℕ)) * ((t : ℝ) * U) := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ l ∈ oddPrimeFactors M, Real.log (l : ℝ)) * ((t : ℝ) * U) :=
        mul_le_mul_of_nonneg_right
          (sum_primes_le_sum_oddPrimeFactors hM.ne' Pram hP (fun l => Real.log (l : ℝ))
            (fun l _ => Real.log_natCast_nonneg l))
          (by positivity)
    _ ≤ Real.log (M : ℝ) * ((t : ℝ) * U) :=
        mul_le_mul_of_nonneg_right (sum_log_oddPrimeFactors_le hM) (by positivity)

/-- Complete odd-ramified realization bundle mirroring `Stage2GaloisWire.PatchedOddUnramifiedRealization`:
supplies a `LocalRamifiedObstruction S E l k` at every odd prime `l ∣ M` and weight `1 ≤ k < t`
whose local inertia-coinvariant rank × conductor exponent fits inside the `minusBound` envelope. -/
structure RamifiedPrimeRealization (S : SelmerSystem) (E : Type) [Field E] [NumberField E]
    (t M n N : ℕ) (C_ram : ℝ) where
  M_ne_zero : M ≠ 0
  N_pos : 1 ≤ N
  t_pos : 1 ≤ t
  C_nonneg : 0 ≤ C_ram
  localObs : ∀ (l : Nat.Primes) (k : ℕ),
    (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t → LocalRamifiedObstruction S E l k
  bound_le : ∀ (l : Nat.Primes) (k : ℕ) (hne2 : (l : ℕ) ≠ 2) (hdvd : (l : ℕ) ∣ M)
    (hk1 : 0 < k) (hkt : k < t),
    ((localObs l k hne2 hdvd hk1 hkt).bound : ℝ) ≤
      C_ram * (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) * Real.log ((t : ℝ) * (l : ℝ) * (N : ℝ))

/-- **Direct Discharge of the Odd-Ramified Branch of `Stage2GaloisWire.ThreePartPatchingWindow`**:
Every `RamifiedPrimeRealization` produces BOTH required odd-ramified conjuncts (`shaLen ≠ ⊤`
and `∑_{l ∈ Pram} log l * ∑_k shaLen ≤ minusBound C_ram M n N t`). -/
theorem RamifiedPrimeRealization.discharges_threePart_ram_branch
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M n N : ℕ} {C_ram : ℝ} (R : RamifiedPrimeRealization S E t M n N C_ram) :
    (∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t →
      S.shaLen E l k ≠ ⊤) ∧
    (∀ Pram : Finset Nat.Primes, (∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M) →
      ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        TaylorWilesWindow.minusBound C_ram M n N t) := by
  refine ⟨fun l k hne2 hdvd hk1 hkt =>
    (R.localObs l k hne2 hdvd hk1 hkt).shaLen_finite_and_le.1, fun Pram hP => ?_⟩
  refine ramified_sum_le_minusBound R.M_ne_zero R.N_pos R.t_pos R.C_nonneg ?_ Pram hP
  intro l k hne2 hdvd hk1 hkt
  have h1 : ((S.shaLen E l k).toNat : ℝ) ≤ ((R.localObs l k hne2 hdvd hk1 hkt).bound : ℝ) := by
    exact_mod_cast (R.localObs l k hne2 hdvd hk1 hkt).shaLen_finite_and_le.2
  exact h1.trans (R.bound_le l k hne2 hdvd hk1 hkt)

/-- Direct plug-in into `TaylorWilesWindow.vvle_of_three_parts`: discharges the `B_ram` branch
from a `RamifiedPrimeRealization`. -/
theorem vvle_of_three_parts_with_ramified_realization
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M n N : ℕ} {B₂ C_ram B_patch : ℝ}
    (h2_fin : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) = 2 → 0 < k → k < t → S.shaLen E l k ≠ ⊤)
    (h2_sum : ∀ P2 : Finset Nat.Primes, (∀ l ∈ P2, (l : ℕ) = 2) →
      ∑ l ∈ P2, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤ B₂)
    (hram : RamifiedPrimeRealization S E t M n N C_ram)
    (hpat_fin : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → ¬((l : ℕ) ∣ M) → 0 < k → k < t →
      S.shaLen E l k ≠ ⊤)
    (hpat_sum : ∀ Ppat : Finset Nat.Primes, (∀ l ∈ Ppat, (l : ℕ) ≠ 2 ∧ ¬((l : ℕ) ∣ M)) →
      ∑ l ∈ Ppat, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤ B_patch) :
    VVle S E t (B₂ + TaylorWilesWindow.minusBound C_ram M n N t + B_patch) := by
  obtain ⟨hram_fin, hram_sum⟩ := hram.discharges_threePart_ram_branch
  exact TaylorWilesWindow.vvle_of_three_parts h2_fin h2_sum hram_fin hram_sum hpat_fin hpat_sum

/-! ## Section 4: Absorption of the Odd Ramified-Prime Contribution into `√(exp(x^ε))` on `PageN` Windows -/

/-- Explicit `ω_odd(M)`-controlled upper bound on the ramified cubic prime sum entering `minusBound`:
`∑_{l ∣ M, odd} l^3 ≤ ω_odd(M) · M^3 ≤ log₃(M) · M^3 ≤ log₂(M) · M^3`. -/
theorem sum_cube_oddPrimeFactors_le {M : ℕ} (hM : 0 < M) :
    ∑ l ∈ oddPrimeFactors M, (l : ℝ) ^ 3 ≤ (omegaOdd M : ℝ) * (M : ℝ) ^ 3 ∧
      (omegaOdd M : ℝ) * (M : ℝ) ^ 3 ≤ Real.logb 3 (M : ℝ) * (M : ℝ) ^ 3 ∧
      Real.logb 3 (M : ℝ) * (M : ℝ) ^ 3 ≤ Real.logb 2 (M : ℝ) * (M : ℝ) ^ 3 := by
  have h1 : ∑ l ∈ oddPrimeFactors M, (l : ℝ) ^ 3 ≤ (omegaOdd M : ℝ) * (M : ℝ) ^ 3 := by
    calc ∑ l ∈ oddPrimeFactors M, (l : ℝ) ^ 3
        ≤ ∑ _l ∈ oddPrimeFactors M, (M : ℝ) ^ 3 := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hdvd := (mem_oddPrimeFactors_iff.mp hl).2.2.1
          have hle : (l : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.le_of_dvd hM hdvd
          exact pow_le_pow_left₀ (Nat.cast_nonneg l) hle 3
      _ = (omegaOdd M : ℝ) * (M : ℝ) ^ 3 := by simp [omegaOdd]
  have h2 : (omegaOdd M : ℝ) * (M : ℝ) ^ 3 ≤ Real.logb 3 (M : ℝ) * (M : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right (omegaOdd_le_log3 hM) (by positivity)
  have h3 : Real.logb 3 (M : ℝ) * (M : ℝ) ^ 3 ≤ Real.logb 2 (M : ℝ) * (M : ℝ) ^ 3 := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Real.logb, Real.logb]
    have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_natCast_nonneg M
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    exact div_le_div_of_nonneg_left hlogM hlog2 hlog23
  exact ⟨h1, h2, h3⟩

/-- **Explicit Exponential Absorption of `K * exp(8 * x^(ε/4))` into `(1 / 3) * √(exp(x^ε))`**:
For every `ε > 0` and `K ≥ 0`, eventually `K * exp(8 * x^(ε/4)) ≤ (1 / 3) * √(exp(x^ε))`. -/
theorem exp_quarter_le_one_third_sqrt_exp (eps K : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0,
      K * Real.exp (8 * x ^ (eps / 4)) ≤ (1 / 3) * Real.sqrt (Real.exp (x ^ eps)) := by
  set C : ℝ := max (3 * K) 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  set T : ℝ := 2 * (8 + Real.log C + 1) with hTdef
  have hTpos : 0 < T := by linarith
  have h34 : 0 < 3 * eps / 4 := by positivity
  refine ⟨max 1 (T ^ (4 / (3 * eps))), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := by linarith
  set a := x ^ (eps / 4) with ha
  set b := x ^ (3 * eps / 4) with hb
  have ha1 : 1 ≤ a := Real.one_le_rpow hx1 (by positivity)
  have hmul : x ^ eps = a * b := by
    rw [ha, hb, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hbT : T ≤ b := by
    have h1 : T = (T ^ (4 / (3 * eps))) ^ (3 * eps / 4) := by
      rw [← Real.rpow_mul hTpos.le]
      have hne : 3 * eps ≠ 0 := by positivity
      have hexp : 4 / (3 * eps) * (3 * eps / 4) = 1 := by field_simp
      rw [hexp, Real.rpow_one]
    rw [h1, hb]
    exact Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx) h34.le
  have h3K : 3 * K ≤ C := le_max_left _ _
  have hstep1 : 3 * (K * Real.exp (8 * a)) ≤ C * Real.exp (8 * a) := by
    have := mul_le_mul_of_nonneg_right h3K (Real.exp_pos (8 * a)).le
    linarith
  have hstep2 : C * Real.exp (8 * a) ≤ Real.exp (x ^ eps / 2) := by
    rw [← Real.exp_log hCpos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hmul]
    have h1 : a * (8 + Real.log C + 1) ≤ a * b / 2 := by
      have := mul_le_mul_of_nonneg_left hbT (by linarith : (0 : ℝ) ≤ a)
      rw [hTdef] at this
      linarith
    nlinarith
  rw [Real.exp_half] at hstep2
  linarith

/-- **Ramified-Prime Contribution Absorbed into `(1 / 3) * √(exp(x^ε))` on `PageN` Windows**:
Combines `TaylorWilesWindow.log_conductor_mul_height_le_of_pageN`,
`TaylorWilesWindow.minusBound_le_exp_of_log_le`, and `exp_quarter_le_one_third_sqrt_exp` to prove
that for any character modulus `M > 0`, ramified constant `C_ram`, `0 < eps < 1/52`, and cutoff
exponent `Ct`, on every sufficiently large `PageN eps x e` scale the entire odd-ramified bound
`B_ram = minusBound C_ram M n N t` is absorbed into `(1 / 3) * √(exp(x^ε)) ≤ √(exp(x^ε))`! -/
theorem ramified_absorbed_in_sqrt_exp (eps Ct C_ram : ℝ) (M : ℕ)
    (heps : 0 < eps) (heps1 : eps < 1 / 52) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (n N t e q d : ℕ),
      1 ≤ N → N ≤ 2 ^ (e + 2) * M * q * d → n ≤ N →
      PageN eps x e → 1 ≤ t → (t : ℝ) ≤ x ^ Ct →
      Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) →
      TaylorWilesWindow.minusBound C_ram M n N t ≤ (1 / 3) * Real.sqrt (Real.exp (x ^ eps)) ∧
        TaylorWilesWindow.minusBound C_ram M n N t ≤ Real.sqrt (Real.exp (x ^ eps)) := by
  obtain ⟨K, _, hK⟩ := TaylorWilesWindow.minusBound_le_exp_of_log_le C_ram M
  obtain ⟨x1, hx1⟩ := TaylorWilesWindow.log_conductor_mul_height_le_of_pageN eps Ct M heps heps1
  obtain ⟨x2, hx2⟩ := exp_quarter_le_one_third_sqrt_exp eps K heps
  refine ⟨max x1 x2, fun x hx n N t e q d hN hNle hn hP ht htx hqd => ?_⟩
  have hNt := hx1 x (le_trans (le_max_left _ _) hx) N t e q d hN hNle hP ht htx hqd
  have hmb := hK n N t (x ^ (eps / 4)) hN ht hn hNt
  have habs := hx2 x (le_trans (le_max_right _ _) hx)
  have hthird : TaylorWilesWindow.minusBound C_ram M n N t ≤
      (1 / 3) * Real.sqrt (Real.exp (x ^ eps)) := hmb.trans habs
  have hsqrt0 : 0 ≤ Real.sqrt (Real.exp (x ^ eps)) := Real.sqrt_nonneg _
  exact ⟨hthird, by linarith⟩

/-- **End-to-End Odd Ramified-Prime Absorption on `WinPair` + `PageN` Windows**:
Given a primitive character `ψ : PChar`, `0 < eps < 1/52`, cutoff `1 ≤ Ct`, `PageN` tower height
`e : ℝ → ℕ`, and `C_ram : ℝ`, there exists `Y0 : ℝ` such that for EVERY `WinPair eps Y q d`
(`Y ≥ Y0`), EVERY `x ∈ [Y, Y²]`, EVERY host field `E` with conductor `1 ≤ N ≤ 2^(e x + 2) * ψ.N * q * d`
and degree `n ≤ N`, and EVERY `RamifiedPrimeRealization S E ⌊x^Ct⌋₊ ψ.N n N C_ram`, the entire
odd-ramified Selmer sum satisfies:
1. finiteness `S.shaLen E l k ≠ ⊤` for all odd `l ∣ ψ.N`, `1 ≤ k < ⌊x^Ct⌋₊`,
2. `∑_{l ∈ Pram} log l * ∑_{k ∈ [1, ⌊x^Ct⌋₊)} (S.shaLen E l k).toNat ≤ minusBound C_ram ψ.N n N ⌊x^Ct⌋₊`,
3. `∑_{l ∈ Pram} log l * ∑_{k ∈ [1, ⌊x^Ct⌋₊)} (S.shaLen E l k).toNat ≤ (1 / 3) * √(exp(x^ε)) ≤ √(exp(x^ε))`! -/
theorem ramified_realization_absorbed_on_winPair_pageN
    (S : SelmerSystem) (ψ : PChar) (eps Ct C_ram : ℝ)
    (heps : 0 < eps) (heps1 : eps < 1 / 52) (hCt : 1 ≤ Ct)
    (e : ℝ → ℕ) (he : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) :
    ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∀ q d : ℕ, WinPair eps Y q d →
      ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
        ∀ (E : Type) [Field E] [NumberField E] (n N : ℕ),
          1 ≤ N → N ≤ 2 ^ (e x + 2) * ψ.N * q * d → n ≤ N →
          RamifiedPrimeRealization S E ⌊x ^ Ct⌋₊ ψ.N n N C_ram →
          (∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ ψ.N →
            0 < k → k < ⌊x ^ Ct⌋₊ → S.shaLen E l k ≠ ⊤) ∧
          (∀ Pram : Finset Nat.Primes, (∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ ψ.N) →
            ∑ l ∈ Pram, Real.log (l : ℕ) *
              ∑ k ∈ Finset.Ico 1 ⌊x ^ Ct⌋₊, ((S.shaLen E l k).toNat : ℝ) ≤
              TaylorWilesWindow.minusBound C_ram ψ.N n N ⌊x ^ Ct⌋₊ ∧
            ∑ l ∈ Pram, Real.log (l : ℕ) *
              ∑ k ∈ Finset.Ico 1 ⌊x ^ Ct⌋₊, ((S.shaLen E l k).toNat : ℝ) ≤
              (1 / 3) * Real.sqrt (Real.exp (x ^ eps)) ∧
            ∑ l ∈ Pram, Real.log (l : ℕ) *
              ∑ k ∈ Finset.Ico 1 ⌊x ^ Ct⌋₊, ((S.shaLen E l k).toNat : ℝ) ≤
              Real.sqrt (Real.exp (x ^ eps))) := by
  obtain ⟨Y1, hY1⟩ := TaylorWilesWindow.log_mul_le_rpow_of_winPair eps heps
  obtain ⟨x0, hx0⟩ := ramified_absorbed_in_sqrt_exp eps Ct C_ram ψ.N heps heps1
  refine ⟨max (max Y1 x0) 2, fun Y hY q d hw x hxY _ E _ _ n N hN hNle hn hR => ?_⟩
  have hYY1 : Y1 ≤ Y := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hY)
  have hYx0 : x0 ≤ Y := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hY)
  have hY2 : (2 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hx2 : (2 : ℝ) ≤ x := hY2.trans hxY
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hqd : Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) :=
    (hY1 Y hYY1 q d hw).trans (Real.rpow_le_rpow hY0 hxY (by positivity))
  have hadm := TaylorWilesWindow.admissible_of_pageN heps heps1 hCt he x hx2
  have ht2 : 2 ≤ ⌊x ^ Ct⌋₊ := hadm.2.2.1
  have ht1 : 1 ≤ ⌊x ^ Ct⌋₊ := by omega
  have htx : (⌊x ^ Ct⌋₊ : ℝ) ≤ x ^ Ct := hadm.2.2.2
  obtain ⟨hmb_third, hmb_sqrt⟩ :=
    hx0 x (hYx0.trans hxY) n N ⌊x ^ Ct⌋₊ (e x) q d hN hNle hn (he x hx1) ht1 htx hqd
  obtain ⟨hfin, hsum⟩ := hR.discharges_threePart_ram_branch
  refine ⟨hfin, fun Pram hP => ?_⟩
  have h1 := hsum Pram hP
  exact ⟨h1, h1.trans hmb_third, h1.trans hmb_sqrt⟩

end Stage2RamifiedPrimes
end RHDirect

end
