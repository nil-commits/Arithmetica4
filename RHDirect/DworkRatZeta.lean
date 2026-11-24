/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign, Gap 2: the Hasse–Weil zeta function & its formal calculus

For a point-count sequence `N : ℕ → K` (where `N m = #V(𝔽_{q^m})`), the Hasse–Weil zeta
function is `Z(V,T) = exp(∑_{m≥1} N_m T^m/m)`. This file builds the formal exp/log calculus
polymorphically over any char-0 field `K` (so it applies to `ℚ`, `ℂ`, and `ℚ_[p]`), defines
the zeta function from point counts, and proves:
  * multiplicativity `Z(N₁+N₂) = Z(N₁)·Z(N₂)` (open/closed & disjoint-union decomposition),
  * the single Euler-factor identity `(1 - αT)·exp(∑ α^m T^m/m) = 1`,
  * the general eigenvalue-form rationality engine (a zeta whose counts are an alternating
    sum of geometric sequences is a rational function).
This is the variety-side foundation of Dwork's proof of Weil Conjecture I.
-/
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false

noncomputable section

namespace RHDirect.DworkRat

open PowerSeries Finset BigOperators

variable {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]

/-! ### Formal exp / log calculus (polymorphic over a char-0 field) -/

/-- Formal exponential `exp(f) := subst f (exp K)` for `f ∈ K[[T]]` with zero constant term. -/
def expSeries (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.subst f (PowerSeries.exp K)

/-- Formal logarithm series `L_α(T) = ∑_{r≥1} (α^r/r) T^r = -log(1 - αT)`. -/
def logSeries (α : K) : PowerSeries K :=
  PowerSeries.mk fun r => if r = 0 then 0 else α ^ r / (r : K)

theorem constantCoeff_logSeries (α : K) :
    PowerSeries.constantCoeff (logSeries α) = 0 := by
  simp [logSeries]

theorem coeff_logSeries (α : K) (r : ℕ) :
    PowerSeries.coeff r (logSeries α) = if r = 0 then 0 else α ^ r / (r : K) := by
  simp [logSeries]

theorem hasSubst_of_constantCoeff_zero {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.HasSubst f :=
  PowerSeries.HasSubst.of_constantCoeff_zero hf

theorem constantCoeff_expSeries {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff (expSeries f) = 1 := by
  change MvPowerSeries.constantCoeff (PowerSeries.subst f (PowerSeries.exp K)) = 1
  rw [PowerSeries.constantCoeff_subst (hasSubst_of_constantCoeff_zero hf)]
  rw [finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro d hd
    have hpow : MvPowerSeries.constantCoeff (f ^ d) = 0 := by
      change PowerSeries.constantCoeff (f ^ d) = 0
      rw [map_pow, hf, zero_pow hd]
    rw [hpow, smul_zero]

theorem derivative_expSeries {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.derivative K (expSeries f) = expSeries f * PowerSeries.derivative K f := by
  unfold expSeries
  rw [PowerSeries.derivative_subst (hasSubst_of_constantCoeff_zero hf), PowerSeries.derivative_exp]

theorem expSeries_zero : expSeries (0 : PowerSeries K) = 1 := by
  apply PowerSeries.derivative.ext
  · rw [derivative_expSeries (by simp), map_zero, mul_zero, PowerSeries.derivative_one]
  · rw [constantCoeff_expSeries (by simp), map_one]

theorem expSeries_mul_expSeries_neg {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) :
    expSeries f * expSeries (-f) = 1 := by
  have hnf : PowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_one]
    rw [Derivation.leibniz, derivative_expSeries hf, derivative_expSeries hnf, map_neg]
    simp only [smul_eq_mul]
    ring
  · rw [map_mul, constantCoeff_expSeries hf, constantCoeff_expSeries hnf, mul_one, map_one]

theorem expSeries_add {f g : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    expSeries (f + g) = expSeries f * expSeries g := by
  have hfg : PowerSeries.constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  have hneg : PowerSeries.constantCoeff (-(f + g)) = 0 := by rw [map_neg, hfg, neg_zero]
  have hprod : expSeries f * expSeries g * expSeries (-(f + g)) = 1 := by
    apply PowerSeries.derivative.ext
    · rw [PowerSeries.derivative_one]
      rw [Derivation.leibniz, Derivation.leibniz, derivative_expSeries hf,
        derivative_expSeries hg, derivative_expSeries hneg, map_neg, map_add]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, map_mul, constantCoeff_expSeries hf, constantCoeff_expSeries hg,
        constantCoeff_expSeries hneg, mul_one, mul_one, map_one]
  calc expSeries (f + g)
      = 1 * expSeries (f + g) := (one_mul _).symm
    _ = (expSeries f * expSeries g * expSeries (-(f + g))) * expSeries (f + g) := by rw [hprod]
    _ = expSeries f * expSeries g * (expSeries (f + g) * expSeries (-(f + g))) := by ring
    _ = expSeries f * expSeries g * 1 := by rw [expSeries_mul_expSeries_neg hfg]
    _ = expSeries f * expSeries g := mul_one _

theorem expSeries_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries K)
    (hf : ∀ i ∈ s, PowerSeries.constantCoeff (f i) = 0) :
    expSeries (∑ i ∈ s, f i) = ∏ i ∈ s, expSeries (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expSeries_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ha0 : PowerSeries.constantCoeff (f a) = 0 := hf a (Finset.mem_insert_self a s)
    have hs0 : PowerSeries.constantCoeff (∑ i ∈ s, f i) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [expSeries_add ha0 hs0, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Exact formal derivative identity `(1 - C α·X)·(d/dT)(logSeries α) = C α`. -/
theorem one_sub_C_mul_X_mul_deriv_logSeries (α : K) :
    (1 - PowerSeries.C α * PowerSeries.X) * PowerSeries.derivative K (logSeries α) =
      PowerSeries.C α := by
  have hderiv : PowerSeries.derivative K (logSeries α) = PowerSeries.mk fun n => α ^ (n + 1) := by
    ext n
    rw [PowerSeries.coeff_derivative, coeff_logSeries, if_neg (Nat.succ_ne_zero n),
      PowerSeries.coeff_mk]
    have hne : ((n + 1 : ℕ) : K) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    field_simp [hne]
    push_cast
    ring
  rw [hderiv, sub_mul, one_mul]
  ext n
  rw [map_sub, PowerSeries.coeff_C]
  rcases n with _ | n
  · rw [PowerSeries.coeff_mk, pow_one, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero, if_pos rfl]
  · rw [if_neg (Nat.succ_ne_zero n), PowerSeries.coeff_mk, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, pow_succ', sub_self]

/-- **Single Euler factor identity** `(1 - C α·X)·expSeries(logSeries α) = 1`. -/
theorem one_sub_C_mul_X_mul_expSeries_logSeries (α : K) :
    (1 - PowerSeries.C α * PowerSeries.X) * expSeries (logSeries α) = 1 := by
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_one, Derivation.leibniz,
      derivative_expSeries (constantCoeff_logSeries α)]
    have hd1 : PowerSeries.derivative K (1 - PowerSeries.C α * PowerSeries.X) =
        -PowerSeries.C α := by
      rw [map_sub, PowerSeries.derivative_one, Derivation.leibniz, PowerSeries.derivative_C,
        PowerSeries.derivative_X]
      simp
    rw [hd1]
    simp only [smul_eq_mul]
    calc (1 - PowerSeries.C α * PowerSeries.X) *
            (expSeries (logSeries α) * PowerSeries.derivative K (logSeries α)) +
          expSeries (logSeries α) * -PowerSeries.C α
        = expSeries (logSeries α) *
            ((1 - PowerSeries.C α * PowerSeries.X) * PowerSeries.derivative K (logSeries α) -
              PowerSeries.C α) := by ring
      _ = expSeries (logSeries α) * (PowerSeries.C α - PowerSeries.C α) := by
            rw [one_sub_C_mul_X_mul_deriv_logSeries]
      _ = 0 := by rw [sub_self, mul_zero]
  · rw [map_mul, map_sub, map_one, map_mul, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, mul_zero, sub_zero,
      constantCoeff_expSeries (constantCoeff_logSeries α), mul_one]

/-- **Linear factor identity** `expSeries(-logSeries α) = 1 - C α·X`. -/
theorem expSeries_neg_logSeries (α : K) :
    expSeries (-logSeries α) = 1 - PowerSeries.C α * PowerSeries.X := by
  calc expSeries (-logSeries α)
      = 1 * expSeries (-logSeries α) := (one_mul _).symm
    _ = ((1 - PowerSeries.C α * PowerSeries.X) * expSeries (logSeries α)) *
          expSeries (-logSeries α) := by rw [one_sub_C_mul_X_mul_expSeries_logSeries]
    _ = (1 - PowerSeries.C α * PowerSeries.X) *
          (expSeries (logSeries α) * expSeries (-logSeries α)) := by ring
    _ = (1 - PowerSeries.C α * PowerSeries.X) * 1 := by
          rw [expSeries_mul_expSeries_neg (constantCoeff_logSeries α)]
    _ = 1 - PowerSeries.C α * PowerSeries.X := mul_one _

/-! ### The Hasse–Weil zeta function from point counts -/

/-- The Hasse–Weil zeta function `Z(N,T) = exp(∑_{m≥1} N_m T^m/m)` of a point-count
sequence `N : ℕ → K`. For a variety `V/𝔽_q`, `N m = #V(𝔽_{q^m})`. -/
def zetaOfCounts (N : ℕ → K) : PowerSeries K :=
  expSeries (PowerSeries.mk fun r => if r = 0 then 0 else N r / (r : K))

/-- The logarithmic generating series `∑_{m≥1} N_m T^m/m` of a point-count sequence. -/
def zetaLog (N : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun r => if r = 0 then 0 else N r / (r : K)

theorem zetaOfCounts_eq_expSeries_zetaLog (N : ℕ → K) :
    zetaOfCounts N = expSeries (zetaLog N) := rfl

theorem constantCoeff_zetaLog (N : ℕ → K) :
    PowerSeries.constantCoeff (zetaLog N) = 0 := by
  simp [zetaLog]

theorem constantCoeff_zetaOfCounts (N : ℕ → K) :
    PowerSeries.constantCoeff (zetaOfCounts N) = 1 :=
  constantCoeff_expSeries (constantCoeff_zetaLog N)

/-- **Multiplicativity of the zeta function under addition of point counts.** This is the
formal engine behind `Z(X₁ ∪ X₂) = Z(X₁)·Z(X₂)` for disjoint unions and the open/closed
decomposition `Z(X) = Z(U)·Z(S)` (where counts add). -/
theorem zetaOfCounts_add (N₁ N₂ : ℕ → K) :
    zetaOfCounts (fun m => N₁ m + N₂ m) = zetaOfCounts N₁ * zetaOfCounts N₂ := by
  have hlog : zetaLog (fun m => N₁ m + N₂ m) = zetaLog N₁ + zetaLog N₂ := by
    ext r
    simp only [zetaLog, PowerSeries.coeff_mk, map_add]
    by_cases hr : r = 0
    · simp [hr]
    · simp only [if_neg hr]
      ring
  rw [zetaOfCounts_eq_expSeries_zetaLog, hlog,
    expSeries_add (constantCoeff_zetaLog N₁) (constantCoeff_zetaLog N₂),
    ← zetaOfCounts_eq_expSeries_zetaLog, ← zetaOfCounts_eq_expSeries_zetaLog]

/-- The zeta of the zero point-count sequence is `1`. -/
theorem zetaOfCounts_zero : zetaOfCounts (fun _ => (0 : K)) = 1 := by
  have hlog : zetaLog (fun _ => (0 : K)) = 0 := by
    ext r
    simp [zetaLog]
  rw [zetaOfCounts_eq_expSeries_zetaLog, hlog, expSeries_zero]

/-- Negation of counts inverts the zeta: `Z(-N) = Z(N)⁻¹` (used for the alternating /
inclusion–exclusion factors). -/
theorem zetaOfCounts_neg_mul (N : ℕ → K) :
    zetaOfCounts (fun m => -N m) * zetaOfCounts N = 1 := by
  have hlog : zetaLog (fun m => -N m) = -zetaLog N := by
    ext r
    simp only [zetaLog, PowerSeries.coeff_mk, map_neg]
    by_cases hr : r = 0
    · simp [hr]
    · simp only [if_neg hr]
      ring
  have h1 : zetaOfCounts (fun m => -N m) = expSeries (-zetaLog N) := by
    rw [zetaOfCounts_eq_expSeries_zetaLog, hlog]
  have h2 : zetaOfCounts N = expSeries (zetaLog N) := rfl
  rw [h1, h2, mul_comm]
  exact expSeries_mul_expSeries_neg (constantCoeff_zetaLog N)

/-! ### The eigenvalue-form rationality engine -/

/-- **General rationality identity.** For any finite set `S`, base `q`, and eigenvalues
`α : β → K`, a zeta whose point counts are `q^r + 1 - ∑_{i∈S} α_i^r` satisfies
`Z(T)·(1-T)·(1-qT) = ∏_{i∈S}(1-α_i T)`. This is the algebraic heart of Weil Conjecture I:
once point counts are expressed as an alternating sum of geometric sequences (as Dwork's
trace formula achieves), rationality is immediate. -/
theorem zeta_rationality_general {β : Type*} (S : Finset β) (q : K) (α : β → K) :
    zetaOfCounts (fun r => q ^ r + 1 - ∑ i ∈ S, (α i) ^ r) *
      (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) =
      ((∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial K) : PowerSeries K) := by
  have hlog_eq : zetaLog (fun r => q ^ r + 1 - ∑ i ∈ S, (α i) ^ r) =
      logSeries q + logSeries (1 : K) + ∑ i ∈ S, (-logSeries (α i)) := by
    ext r
    simp only [zetaLog, PowerSeries.coeff_mk, map_add, map_sum, map_neg, coeff_logSeries]
    by_cases hr : r = 0
    · simp [hr]
    · simp only [if_neg hr, one_pow, Finset.sum_neg_distrib, ← Finset.sum_div]
      ring
  have hsum0 : PowerSeries.constantCoeff (∑ i ∈ S, (-logSeries (α i))) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_neg, constantCoeff_logSeries, neg_zero]
  rw [zetaOfCounts_eq_expSeries_zetaLog, hlog_eq,
    expSeries_add (by rw [map_add, constantCoeff_logSeries, constantCoeff_logSeries, add_zero]) hsum0]
  rw [expSeries_add (constantCoeff_logSeries q) (constantCoeff_logSeries (1 : K))]
  rw [expSeries_sum S _ (fun i _ => by rw [map_neg, constantCoeff_logSeries, neg_zero])]
  have hprod_eq :
      ∏ i ∈ S, expSeries (-logSeries (α i)) =
        ((∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial K) : PowerSeries K) := by
    change ∏ i ∈ S, expSeries (-logSeries (α i)) =
      Polynomial.coeToPowerSeries.ringHom (∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X))
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [expSeries_neg_logSeries]
    simp [Polynomial.coeToPowerSeries.ringHom]
  rw [hprod_eq]
  have h1 : (1 - PowerSeries.X) * expSeries (logSeries (1 : K)) = 1 := by
    simpa using one_sub_C_mul_X_mul_expSeries_logSeries (1 : K)
  have hq : (1 - PowerSeries.C q * PowerSeries.X) * expSeries (logSeries q) = 1 :=
    one_sub_C_mul_X_mul_expSeries_logSeries q
  calc expSeries (logSeries q) * expSeries (logSeries (1 : K)) *
          ((∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial K) : PowerSeries K) *
          (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)
      = ((1 - PowerSeries.C q * PowerSeries.X) * expSeries (logSeries q)) *
          ((1 - PowerSeries.X) * expSeries (logSeries (1 : K))) *
          ((∏ i ∈ S, (1 - Polynomial.C (α i) * Polynomial.X) : Polynomial K) : PowerSeries K) := by ring
    _ = 1 * 1 * _ := by rw [hq, h1]
    _ = _ := by rw [one_mul, one_mul]

/-- A geometric point-count sequence `N_m = α^m` has zeta `1/(1-αT)`, i.e.
`zetaOfCounts (α^·) · (1 - C α·X) = 1`. -/
theorem zetaOfCounts_geometric (α : K) :
    zetaOfCounts (fun m => α ^ m) * (1 - PowerSeries.C α * PowerSeries.X) = 1 := by
  have hlog : zetaLog (fun m => α ^ m) = logSeries α := by
    ext r
    simp [zetaLog, logSeries]
  rw [zetaOfCounts_eq_expSeries_zetaLog, hlog, mul_comm]
  exact one_sub_C_mul_X_mul_expSeries_logSeries α

end RHDirect.DworkRat
