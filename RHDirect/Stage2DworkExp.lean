import RHDirect.PAdicChainValuation
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.Finite.Basic

/-!
# RHDirect.Stage2DworkExp

Deep **$p$-adic Dwork Exponential, Dieudonné–Dwork Integrality, Artin–Hasse Exponential,
and Crystalline Frobenius Overconvergence** engine built directly on top of
`RHDirect.PAdicChainValuation` and Mathlib `v4.33.1` (0 `sorry`, 0 custom `axiom`s).

## Contents

1. **Exact $p$-adic Convergence Radius of `exp_p(x)` & `log_p(1 + x)`**:
   - Exact prime-power Legendre formula `padicValNat_factorial_prime_pow`:
     `v_p((p^m)!) = (p^m - 1) / (p - 1)`.
   - Sharp norm upper bound `norm_expTerm_le` via `PAdicChainValuation.padicValNat_factorial_upper`
     and exact equality `norm_expTerm_prime_pow` along `k = p ^ m`.
   - Complete characterization of the $p$-adic exponential disk:
     `summable_expTerm_iff` (`Summable (expTerm x) ↔ ‖x‖ < ‖(p : K)‖ ^ (1 / (p - 1))`) and
     `tendsto_expTerm_zero_iff`, specialized to `ℚ_[p]` (`padic_summable_expTerm_iff`:
     `‖x‖ < (p : ℝ) ^ (-1 / (p - 1))`).
   - Analytic $p$-adic exponential `expP`: ultrametric isometry `norm_expP_sub_one_eq`
     (`‖expP x - 1‖ = ‖x‖`), unit norm `norm_expP_eq_one`, homomorphism law
     `expP_add` (`expP (x + y) = expP x * expP y`), and injectivity `expP_injective`.
   - Exact $p$-adic logarithm `logP` on the open unit disk:
     `summable_logTerm_iff` (`Summable (logTerm x) ↔ ‖x‖ < 1`), and ultrametric isometry
     `norm_logP_eq` on the crystalline disk `‖x‖ < r_p`.

2. **Frobenius-Lift Dieudonné–Dwork Integrality Criterion (`dieudonne_dwork_iff`)**:
   - Formal power series Frobenius operator `frobPS p hp f = f(X^p)` and twisted crystalline
     Frobenius `frobMapPS σ p hp f = f^σ(X^p)` (proved to be `RingHom`s agreeing with
     `PowerSeries.subst (X ^ p)`).
   - Full formal power series Dieudonné–Dwork Lemma for any ultrametric field `K` with a
     Frobenius lift `σ` satisfying `‖c^p - σ c‖ ≤ ‖p‖` on `O_K`:
     `IsIntegralPS f ↔ CongOneModP p (frobMapPS σ p hp f * (invOnePS f) ^ p)`.
   - Concrete specialization to `ℚ_[p]` (`padic_dieudonne_dwork_iff`) via Fermat's Little
     Theorem on `ℤ_[p] / p ℤ_[p]` (`padic_pow_prime_sub_le`).

3. **Artin–Hasse Exponential Integrality (`E_p(X) ∈ ℤ_p[[X]]`)**:
   - Formal `expPS` calculus (`expPS_add`, `expPS_nsmul`, `frobPS_expPS`, `map_expPS`).
   - Functional identity `A(X^p) - p A(X) = -p X` for `A(X) = ∑_{m ≥ 0} X^{p^m} / p^m`,
     giving `E_p(X^p) / E_p(X)^p = exp(-p X) ∈ 1 + p O_K[[X]]` via
     `PAdicChainValuation.padicValNat_factorial_upper`.
   - Deduction of `artinHasseExp_isIntegral_padic` (`E_p(X) ∈ ℤ_p[[X]]`), rational
     `p`-integrality `artinHasseExp_rat_den_not_dvd`, universal integrality in EVERY
     ultrametric field `K` (including ramified extensions like `ℚ_p(ϖ)` and `ℂ_p`:
     `artinHasseExp_isIntegral`), and unit-disk convergence `artinHasse_summable`.

4. **Dwork Splitting Function `θ(X) = exp(ϖ (X - X^p))` & Overconvergence Radius**:
   - Exact factorization `θ(X) = E_p(ϖ X) * exp(- ∑_{m ≥ 2} (ϖ X)^{p^m} / p^m)` for any
     Dwork uniformizer `ϖ^(p - 1) = -p`.
   - Direct application of `PAdicChainValuation.dwork_exp_weight_le` and
     `PAdicChainValuation.multiplicative_weight_le` (exploiting `PowerSeries K = MvPowerSeries Unit K`),
     proving the sharp Dwork decay bound
     `‖coeff n (dworkSplitting ϖ p)‖ ≤ ‖(p : K)‖ ^ (n * (p - 1) / p^2)`.
   - Overconvergence strictly beyond the closed unit disk (`dworkSplitting_summable`):
     `θ(x)` converges for all `‖x‖ < ‖(p : K)‖ ^ (-(p - 1) / p^2)` (in particular at `x = 1`!).

5. **Crystalline Frobenius Radius Bridge to `PAdicChainValuation.WtGe`**:
   - Direct transfer theorem `wtGe_implies_summable`: any series satisfying `WtGe ‖p‖ (-α) w`
     from `PAdicChainValuation` converges analytically on `‖x‖ < ‖p‖ ^ (-α)`, giving
     `dwork_exp_crystalline_radius` for `exp(B(x))`.
-/

open Real Finset Filter Topology
open scoped BigOperators
open RHDirect.PAdicChainValuation

namespace RHDirect.Stage2DworkExp

noncomputable section

/-! ## Section 1: Exact $p$-adic Convergence Radius of `exp_p(x)` & `log_p(1 + x)` -/

section PAdicExpLogRadius

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The $p$-adic exponential convergence radius `r_p(K) = ‖(p : K)‖ ^ (1 / (p - 1))`.
For `K = ℚ_[p]`, this equals `p ^ (-1 / (p - 1))`. -/
def expRadius (K : Type*) [NormedField K] (p : ℕ) : ℝ :=
  ‖(p : K)‖ ^ ((1 : ℝ) / ((p : ℝ) - 1))

/-- The `k`-th term `x^k / k!` of the $p$-adic exponential series. -/
def expTerm (x : K) (k : ℕ) : K :=
  (k.factorial : K)⁻¹ * x ^ k

/-- Base-`p` digits of `p ^ m` sum to `1` for every `p ≥ 2` and `m : ℕ`. -/
theorem digits_prime_pow_sum {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    (p.digits (p ^ m)).sum = 1 := by
  induction m with
  | zero =>
    rw [pow_zero, Nat.digits_of_lt p 1 (by omega) (by omega)]
    simp
  | succ m ih =>
    have hpos : 0 < p ^ (m + 1) := pow_pos (by omega) _
    rw [Nat.digits_def' (by omega) hpos, List.sum_cons]
    have hmod : p ^ (m + 1) % p = 0 := by
      rw [pow_succ]
      exact Nat.mul_mod_left _ _
    have hdiv : p ^ (m + 1) / p = p ^ m := by
      rw [pow_succ]
      exact Nat.mul_div_cancel _ (by omega)
    rw [hmod, hdiv, zero_add, ih]

/-- **Exact Legendre Formula at Prime Powers**:
For any prime `p` and `m : ℕ`, `(p - 1) * v_p((p^m)!) = p^m - 1`. -/
theorem sub_one_mul_padicValNat_factorial_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (p - 1) * padicValNat p (p ^ m).factorial = p ^ m - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [sub_one_mul_padicValNat_factorial, digits_prime_pow_sum hp.two_le m]

/-- Real-valued exact Legendre formula at prime powers:
`v_p((p^m)!) = (p^m - 1) / (p - 1)`. -/
theorem padicValNat_factorial_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (padicValNat p (p ^ m).factorial : ℝ) = ((p : ℝ) ^ m - 1) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hnat := sub_one_mul_padicValNat_factorial_prime_pow hp m
  have hcast : (((p - 1) * padicValNat p (p ^ m).factorial : ℕ) : ℝ) = ((p ^ m - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have h1 : 1 ≤ p ^ m := Nat.one_le_pow m p hp.pos
  rw [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_sub h1, Nat.cast_pow,
    Nat.cast_one] at hcast
  rw [eq_div_iff hpos.ne', mul_comm]
  exact hcast

omit [IsUltrametricDist K] in
theorem expRadius_pos [CharZero K] {p : ℕ} (hp : p.Prime) : 0 < expRadius K p :=
  Real.rpow_pos_of_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)) _

omit [IsUltrametricDist K] in
theorem expRadius_lt_one [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) :
    expRadius K p < 1 := by
  have hpos : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  exact Real.rpow_lt_one hpos.le hlt (div_pos one_pos hpm1)

/-- Exact ultrametric norm of the `k`-th exponential term `x^k / k!`. -/
theorem norm_expTerm [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) (x : K) (k : ℕ) :
    ‖expTerm x k‖ = ‖(p : K)‖ ^ (-(padicValNat p k.factorial : ℝ)) * ‖x‖ ^ k := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  unfold expTerm
  rw [norm_mul, norm_inv, norm_pow, norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero k),
    Real.rpow_neg hpi0.le, Real.rpow_natCast]

/-- **Sharp Upper Bound on `‖x^k / k!‖`** (via `PAdicChainValuation.padicValNat_factorial_upper`):
For `k ≥ 1`, `‖x^k / k!‖ ≤ expRadius K p * (‖x‖ / expRadius K p) ^ k`. -/
theorem norm_expTerm_le [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (x : K) {k : ℕ} (hk : k ≠ 0) :
    ‖expTerm x k‖ ≤ expRadius K p * (‖x‖ / expRadius K p) ^ k := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hrpos : 0 < expRadius K p := expRadius_pos hp
  rw [norm_expTerm hp hlt x k]
  have hv := padicValNat_factorial_upper hp hk
  have hrpow : ‖(p : K)‖ ^ (-(padicValNat p k.factorial : ℝ)) ≤
      ‖(p : K)‖ ^ (-(((k : ℝ) - 1) / ((p : ℝ) - 1))) :=
    Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (neg_le_neg hv)
  calc ‖(p : K)‖ ^ (-(padicValNat p k.factorial : ℝ)) * ‖x‖ ^ k
      ≤ ‖(p : K)‖ ^ (-(((k : ℝ) - 1) / ((p : ℝ) - 1))) * ‖x‖ ^ k :=
        mul_le_mul_of_nonneg_right hrpow (pow_nonneg (norm_nonneg x) k)
    _ = expRadius K p * (‖x‖ / expRadius K p) ^ k := by
        rw [div_pow, mul_div_assoc', eq_div_iff (pow_pos hrpos k).ne']
        unfold expRadius
        rw [← Real.rpow_natCast (‖(p : K)‖ ^ _), ← Real.rpow_mul hpi0.le]
        have hmul : ‖(p : K)‖ ^ (-(((k : ℝ) - 1) / ((p : ℝ) - 1))) * ‖x‖ ^ k *
            ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) * (k : ℝ)) =
            (‖(p : K)‖ ^ (-(((k : ℝ) - 1) / ((p : ℝ) - 1))) *
              ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) * (k : ℝ))) * ‖x‖ ^ k := by ring
        rw [hmul, ← Real.rpow_add hpi0]
        congr 2
        ring

/-- **Exact Norm Identity at Prime Powers `k = p ^ m`**:
`‖x^(p^m) / (p^m)!‖ = expRadius K p * (‖x‖ / expRadius K p) ^ (p ^ m)`. -/
theorem norm_expTerm_prime_pow [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (x : K) (m : ℕ) :
    ‖expTerm x (p ^ m)‖ = expRadius K p * (‖x‖ / expRadius K p) ^ (p ^ m) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hrpos : 0 < expRadius K p := expRadius_pos hp
  rw [norm_expTerm hp hlt x (p ^ m), padicValNat_factorial_prime_pow hp m]
  rw [div_pow, mul_div_assoc', eq_div_iff (pow_pos hrpos _).ne']
  unfold expRadius
  rw [← Real.rpow_natCast (‖(p : K)‖ ^ _), ← Real.rpow_mul hpi0.le]
  have hmul : ‖(p : K)‖ ^ (-(((p : ℝ) ^ m - 1) / ((p : ℝ) - 1))) * ‖x‖ ^ (p ^ m) *
      ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) * ((p ^ m : ℕ) : ℝ)) =
      (‖(p : K)‖ ^ (-(((p : ℝ) ^ m - 1) / ((p : ℝ) - 1))) *
        ‖(p : K)‖ ^ (1 / ((p : ℝ) - 1) * ((p ^ m : ℕ) : ℝ))) * ‖x‖ ^ (p ^ m) := by ring
  rw [hmul, ← Real.rpow_add hpi0]
  congr 2
  push_cast
  ring

/-- Uniform upper bound valid for ALL `k : ℕ` (including `k = 0`):
`‖expTerm x k‖ ≤ (‖x‖ / expRadius K p) ^ k` when `‖(p : K)‖ < 1` (since `expRadius K p < 1`). -/
theorem norm_expTerm_le_pow [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (x : K) (k : ℕ) :
    ‖expTerm x k‖ ≤ (‖x‖ / expRadius K p) ^ k := by
  rcases k with _ | k
  · simp [expTerm]
  · have hr1 : expRadius K p < 1 := expRadius_lt_one hp hlt
    have hrpos : 0 < expRadius K p := expRadius_pos hp
    calc ‖expTerm x (k + 1)‖
        ≤ expRadius K p * (‖x‖ / expRadius K p) ^ (k + 1) :=
          norm_expTerm_le hp hlt x (Nat.succ_ne_zero k)
      _ ≤ 1 * (‖x‖ / expRadius K p) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right hr1.le (pow_nonneg (div_nonneg (norm_nonneg x) hrpos.le) _)
      _ = (‖x‖ / expRadius K p) ^ (k + 1) := one_mul _

/-- Inside the $p$-adic exponential disk `‖x‖ < expRadius K p`, the norm series `∑ ‖x^k / k!‖`
is summable (dominated by a convergent geometric series). -/
theorem summable_norm_expTerm_of_norm_lt [CharZero K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < expRadius K p) :
    Summable (fun k => ‖expTerm x k‖) := by
  have hrpos : 0 < expRadius K p := expRadius_pos hp
  have hq0 : 0 ≤ ‖x‖ / expRadius K p := div_nonneg (norm_nonneg x) hrpos.le
  have hq1 : ‖x‖ / expRadius K p < 1 := (div_lt_one hrpos).mpr hx
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (norm_expTerm_le_pow hp hlt x)
    (summable_geometric_of_lt_one hq0 hq1)

/-- Inside the $p$-adic exponential disk `‖x‖ < expRadius K p`, `expTerm x k → 0`. -/
theorem tendsto_expTerm_zero_of_norm_lt [CharZero K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < expRadius K p) :
    Tendsto (expTerm x) atTop (nhds 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (summable_norm_expTerm_of_norm_lt hp hlt hx).tendsto_atTop_zero

/-- Outside or on the boundary `expRadius K p ≤ ‖x‖`, `expTerm x` does NOT tend to `0`
(witnessed along the prime-power subsequence `k = p ^ m`). -/
theorem not_tendsto_expTerm_zero_of_norm_ge [CharZero K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {x : K} (hx : expRadius K p ≤ ‖x‖) :
    ¬ Tendsto (expTerm x) atTop (nhds 0) := by
  intro ht
  have hnorm : Tendsto (fun k => ‖expTerm x k‖) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp ht
  have hrpos : 0 < expRadius K p := expRadius_pos hp
  have hev : ∀ᶠ k in atTop, ‖expTerm x k‖ < expRadius K p :=
    hnorm.eventually (gt_mem_nhds hrpos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hpow_ge : N ≤ p ^ N := (Nat.lt_pow_self hp.one_lt).le
  have hltN := hN (p ^ N) hpow_ge
  rw [norm_expTerm_prime_pow hp hlt x N] at hltN
  have hq1 : 1 ≤ ‖x‖ / expRadius K p := (one_le_div hrpos).mpr hx
  have hpow1 : 1 ≤ (‖x‖ / expRadius K p) ^ (p ^ N) := one_le_pow₀ hq1
  nlinarith

/-- **Exact Radius Characterization (Term-to-Zero)**:
`expTerm x k → 0 ↔ ‖x‖ < expRadius K p`. -/
theorem tendsto_expTerm_zero_iff [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) (x : K) :
    Tendsto (expTerm x) atTop (nhds 0) ↔ ‖x‖ < expRadius K p := by
  constructor
  · intro ht
    by_contra hge
    exact not_tendsto_expTerm_zero_of_norm_ge hp hlt (not_lt.mp hge) ht
  · exact tendsto_expTerm_zero_of_norm_lt hp hlt

/-- **Exact $p$-adic Convergence Radius Theorem for `exp_p(x)`**:
In any complete ultrametric field `K` of characteristic `0` with `‖(p : K)‖ < 1`,
`∑_{k ≥ 0} x^k / k!` converges if and only if `‖x‖ < ‖(p : K)‖ ^ (1 / (p - 1))`. -/
theorem summable_expTerm_iff [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) (x : K) :
    Summable (expTerm x) ↔ ‖x‖ < expRadius K p := by
  constructor
  · intro hs
    exact (tendsto_expTerm_zero_iff hp hlt x).mp hs.tendsto_atTop_zero
  · intro hx
    exact (summable_norm_expTerm_of_norm_lt hp hlt hx).of_norm

/-- Concrete `ℚ_[p]` specialization: `expRadius ℚ_[p] p = (p : ℝ) ^ (-1 / (p - 1))`. -/
theorem padic_expRadius_eq (p : ℕ) [Fact p.Prime] :
    expRadius ℚ_[p] p = (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := by
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  unfold expRadius
  rw [Padic.norm_p, ← Real.rpow_neg_one, ← Real.rpow_mul hp0.le]
  congr 1
  ring

/-- **Exact Convergence Radius of `exp_p` on `ℚ_[p]`**:
`∑_{k ≥ 0} x^k / k!` converges in `ℚ_[p]` if and only if `‖x‖ < p ^ (-1 / (p - 1))`. -/
theorem padic_summable_expTerm_iff (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    Summable (expTerm x) ↔ ‖x‖ < (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) := by
  have hp : p.Prime := Fact.out
  have hlt : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  rw [← padic_expRadius_eq p]
  exact summable_expTerm_iff hp hlt x

/-- The analytic $p$-adic exponential `exp_p(x) = ∑' k, x^k / k!`. -/
def expP (x : K) : K := ∑' k, expTerm x k

omit [IsUltrametricDist K] in
theorem expP_zero : expP (0 : K) = 1 := by
  unfold expP
  rw [tsum_eq_single 0]
  · simp [expTerm]
  · intro k hk
    simp [expTerm, zero_pow hk]

/-- Ultrametric closed-ball preservation for `tsum`: if `Summable f` and `∀ k, ‖f k‖ ≤ B`
(with `0 ≤ B`), then `‖∑' k, f k‖ ≤ B`. -/
theorem ultrametric_norm_tsum_le {α : Type*} {f : α → K} {B : ℝ} (hB : 0 ≤ B)
    (hs : Summable f) (hf : ∀ a, ‖f a‖ ≤ B) : ‖∑' a, f a‖ ≤ B := by
  have hlim : Tendsto (fun s : Finset α => ‖∑ a ∈ s, f a‖) atTop (nhds ‖∑' a, f a‖) :=
    continuous_norm.continuousAt.tendsto.comp hs.hasSum
  exact le_of_tendsto' hlim fun s => ultrametric_norm_sum_le s f hB fun a _ => hf a

/-- Tail norm bound on the exponential disk: for `‖x‖ < r_p`,
`‖expP x - 1 - x‖ ≤ ‖x‖ * (‖x‖ / expRadius K p)`. -/
theorem norm_expP_sub_one_sub_le [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < expRadius K p) :
    ‖expP x - 1 - x‖ ≤ ‖x‖ * (‖x‖ / expRadius K p) := by
  have hrpos : 0 < expRadius K p := expRadius_pos hp
  have hs : Summable (expTerm x) := (summable_expTerm_iff hp hlt x).mpr hx
  have hsplit : expP x - 1 - x = ∑' k, expTerm x (k + 2) := by
    unfold expP
    have h1 := hs.sum_add_tsum_nat_add 2
    have hsum2 : ∑ i ∈ Finset.range 2, expTerm x i = 1 + x := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [expTerm]
    rw [hsum2] at h1
    rw [← h1]
    ring
  rw [hsplit]
  have hs2 : Summable (fun k => expTerm x (k + 2)) := (summable_nat_add_iff 2).mpr hs
  have hB0 : 0 ≤ ‖x‖ * (‖x‖ / expRadius K p) :=
    mul_nonneg (norm_nonneg x) (div_nonneg (norm_nonneg x) hrpos.le)
  refine ultrametric_norm_tsum_le hB0 hs2 fun k => ?_
  have hbd := norm_expTerm_le hp hlt x (Nat.succ_ne_zero (k + 1))
  have hq0 : 0 ≤ ‖x‖ / expRadius K p := div_nonneg (norm_nonneg x) hrpos.le
  have hq1 : ‖x‖ / expRadius K p ≤ 1 := ((div_lt_one hrpos).mpr hx).le
  have hpow : (‖x‖ / expRadius K p) ^ (k + 2) ≤ (‖x‖ / expRadius K p) ^ 2 := by
    rw [pow_add]
    calc (‖x‖ / expRadius K p) ^ k * (‖x‖ / expRadius K p) ^ 2
        ≤ 1 * (‖x‖ / expRadius K p) ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) (sq_nonneg _)
      _ = (‖x‖ / expRadius K p) ^ 2 := one_mul _
  calc ‖expTerm x (k + 2)‖
      ≤ expRadius K p * (‖x‖ / expRadius K p) ^ (k + 2) := hbd
    _ ≤ expRadius K p * (‖x‖ / expRadius K p) ^ 2 :=
        mul_le_mul_of_nonneg_left hpow hrpos.le
    _ = ‖x‖ * (‖x‖ / expRadius K p) := by
        field_simp

/-- **Ultrametric Isometry of `exp_p(x) - 1`**:
For every `x` in the open disk `‖x‖ < expRadius K p`, `‖expP x - 1‖ = ‖x‖`. -/
theorem norm_expP_sub_one_eq [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < expRadius K p) :
    ‖expP x - 1‖ = ‖x‖ := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [expP_zero]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrpos : 0 < expRadius K p := expRadius_pos hp
    have hq : ‖x‖ / expRadius K p < 1 := (div_lt_one hrpos).mpr hx
    have hstrict : ‖expP x - 1 - x‖ < ‖x‖ := by
      calc ‖expP x - 1 - x‖
          ≤ ‖x‖ * (‖x‖ / expRadius K p) := norm_expP_sub_one_sub_le hp hlt hx
        _ < ‖x‖ * 1 := mul_lt_mul_of_pos_left hq hpos
        _ = ‖x‖ := mul_one _
    have hdecomp : expP x - 1 = x + (expP x - 1 - x) := by ring
    rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hstrict.ne',
      max_eq_left hstrict.le]

/-- On the convergence disk `‖x‖ < expRadius K p`, `expP x` is a $p$-adic unit: `‖expP x‖ = 1`. -/
theorem norm_expP_eq_one [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < expRadius K p) :
    ‖expP x‖ = 1 := by
  have h1 : ‖expP x - 1‖ < ‖(1 : K)‖ := by
    rw [norm_expP_sub_one_eq hp hlt hx, norm_one]
    exact hx.trans (expRadius_lt_one hp hlt)
  have hdecomp : expP x = 1 + (expP x - 1) := by ring
  rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le, norm_one]

omit [IsUltrametricDist K] in
/-- Binomial identity on `expTerm`: `expTerm (x + y) k = ∑_{i + j = k} expTerm x i * expTerm y j`. -/
lemma expTerm_add_eq_antidiagonal [CharZero K] (x y : K) (k : ℕ) :
    expTerm (x + y) k = ∑ ab ∈ Finset.antidiagonal k, expTerm x ab.1 * expTerm y ab.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => expTerm x i * expTerm y j) k]
  unfold expTerm
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hchoose : (k.choose i : K) * (i.factorial : K) * ((k - i).factorial : K) = (k.factorial : K) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
  have hkf : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hif : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hsubf : ((k - i).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - i))
  field_simp [hkf, hif, hsubf]
  linear_combination x ^ i * y ^ (k - i) * hchoose

/-- **Cauchy-Product Homomorphism Law for `exp_p`**:
For `‖x‖ < expRadius K p` and `‖y‖ < expRadius K p`, `expP (x + y) = expP x * expP y`. -/
theorem expP_add [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {x y : K} (hx : ‖x‖ < expRadius K p) (hy : ‖y‖ < expRadius K p) :
    expP (x + y) = expP x * expP y := by
  have hrpos : 0 < expRadius K p := expRadius_pos hp
  have hxy : ‖x + y‖ < expRadius K p :=
    (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
  have hsx : Summable (expTerm x) := (summable_expTerm_iff hp hlt x).mpr hx
  have hsy : Summable (expTerm y) := (summable_expTerm_iff hp hlt y).mpr hy
  have hsxy : Summable (expTerm (x + y)) := (summable_expTerm_iff hp hlt (x + y)).mpr hxy
  have htx : Tendsto (fun N => ∑ i ∈ Finset.range N, expTerm x i) atTop (nhds (expP x)) :=
    hsx.hasSum.tendsto_sum_nat
  have hty : Tendsto (fun N => ∑ j ∈ Finset.range N, expTerm y j) atTop (nhds (expP y)) :=
    hsy.hasSum.tendsto_sum_nat
  have htxy : Tendsto (fun N => ∑ k ∈ Finset.range N, expTerm (x + y) k) atTop (nhds (expP (x + y))) :=
    hsxy.hasSum.tendsto_sum_nat
  have hdiff_lim : Tendsto (fun N =>
      (∑ i ∈ Finset.range N, expTerm x i) * (∑ j ∈ Finset.range N, expTerm y j) -
        ∑ k ∈ Finset.range N, expTerm (x + y) k) atTop (nhds (expP x * expP y - expP (x + y))) :=
    (htx.mul hty).sub htxy
  set q := max (‖x‖ / expRadius K p) (‖y‖ / expRadius K p) with hqdef
  have hq0 : 0 ≤ q := le_trans (div_nonneg (norm_nonneg x) hrpos.le) (le_max_left _ _)
  have hq1 : q < 1 := max_lt ((div_lt_one hrpos).mpr hx) ((div_lt_one hrpos).mpr hy)
  have hdiff_zero : Tendsto (fun N =>
      (∑ i ∈ Finset.range N, expTerm x i) * (∑ j ∈ Finset.range N, expTerm y j) -
        ∑ k ∈ Finset.range N, expTerm (x + y) k) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    have hprod_eq : (∑ i ∈ Finset.range N, expTerm x i) * (∑ j ∈ Finset.range N, expTerm y j) =
        ∑ ab ∈ Finset.range N ×ˢ Finset.range N, expTerm x ab.1 * expTerm y ab.2 := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    have hsum_xy : ∑ k ∈ Finset.range N, expTerm (x + y) k =
        ∑ ab ∈ (Finset.range N ×ˢ Finset.range N).filter (fun ab : ℕ × ℕ => ab.1 + ab.2 < N),
          expTerm x ab.1 * expTerm y ab.2 := by
      simp_rw [expTerm_add_eq_antidiagonal]
      rw [Finset.sum_sigma' (Finset.range N) Finset.antidiagonal
        (fun _ ab => expTerm x ab.1 * expTerm y ab.2)]
      refine Finset.sum_bij (fun s _ => s.2) ?_ ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hs
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      · intro s₁ hs₁ s₂ hs₂ heq
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hs₁ hs₂
        have h1 : s₁.1 = s₂.1 := by rw [← hs₁.2, ← hs₂.2, heq]
        exact Sigma.ext h1 (by simpa [h1] using heq)
      · intro ab hab
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
        refine ⟨⟨ab.1 + ab.2, ab⟩, ?_, rfl⟩
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal, and_true]
        exact hab.2
      · intro _ _; rfl
    have hsub_eq : (∑ i ∈ Finset.range N, expTerm x i) * (∑ j ∈ Finset.range N, expTerm y j) -
        ∑ k ∈ Finset.range N, expTerm (x + y) k =
        ∑ ab ∈ (Finset.range N ×ˢ Finset.range N).filter (fun ab : ℕ × ℕ => ¬ ab.1 + ab.2 < N),
          expTerm x ab.1 * expTerm y ab.2 := by
      rw [hprod_eq, hsum_xy, ← Finset.sum_filter_add_sum_filter_not (Finset.range N ×ˢ Finset.range N)
        (fun ab : ℕ × ℕ => ab.1 + ab.2 < N)]
      ring
    rw [hsub_eq]
    refine ultrametric_norm_sum_le _ _ (pow_nonneg hq0 N) fun ab hab => ?_
    simp only [Finset.mem_filter, not_lt] at hab
    rw [norm_mul]
    have hx_bd : ‖expTerm x ab.1‖ ≤ q ^ ab.1 :=
      (norm_expTerm_le_pow hp hlt x ab.1).trans
        (pow_le_pow_left₀ (div_nonneg (norm_nonneg x) hrpos.le) (le_max_left _ _) _)
    have hy_bd : ‖expTerm y ab.2‖ ≤ q ^ ab.2 :=
      (norm_expTerm_le_pow hp hlt y ab.2).trans
        (pow_le_pow_left₀ (div_nonneg (norm_nonneg y) hrpos.le) (le_max_right _ _) _)
    calc ‖expTerm x ab.1‖ * ‖expTerm y ab.2‖
        ≤ q ^ ab.1 * q ^ ab.2 := mul_le_mul hx_bd hy_bd (norm_nonneg _) (pow_nonneg hq0 _)
      _ = q ^ (ab.1 + ab.2) := (pow_add q ab.1 ab.2).symm
      _ ≤ q ^ N := pow_le_pow_of_le_one hq0 hq1.le hab.2
  have hzero : expP x * expP y - expP (x + y) = 0 := tendsto_nhds_unique hdiff_lim hdiff_zero
  exact (sub_eq_zero.mp hzero).symm

/-- **Injectivity of `exp_p` on its Convergence Disk**:
If `‖x‖ < r_p`, `‖y‖ < r_p`, and `expP x = expP y`, then `x = y`. -/
theorem expP_injective [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {x y : K} (hx : ‖x‖ < expRadius K p) (hy : ‖y‖ < expRadius K p) (hxy : expP x = expP y) :
    x = y := by
  have hny : ‖-y‖ < expRadius K p := by rwa [norm_neg]
  have hsub : ‖x - y‖ < expRadius K p := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max x (-y)).trans_lt (max_lt hx hny)
  have h1 : expP (x - y) = 1 := by
    have hmul : expP (x - y) * expP y = expP y := by
      rw [← expP_add hp hlt hsub hy, sub_add_cancel, hxy]
    have hne : expP y ≠ 0 := norm_pos_iff.mp (by rw [norm_expP_eq_one hp hlt hy]; exact one_pos)
    exact mul_right_cancel₀ hne (by simpa using hmul)
  have hnorm : ‖x - y‖ = 0 := by
    rw [← norm_expP_sub_one_eq hp hlt hsub, h1, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The `k`-th term `(-1)^(k-1) x^k / k` of the $p$-adic logarithm `log_p(1 + x)`. -/
def logTerm (x : K) (k : ℕ) : K :=
  if k = 0 then 0 else (-1 : K) ^ (k - 1) * (k : K)⁻¹ * x ^ k

/-- Polynomial-in-`k` upper bound on `‖(k : K)⁻¹‖` via `p ^ v_p(k) ≤ k`:
`‖(k : K)⁻¹‖ ≤ (k : ℝ) ^ (Real.log (‖(p : K)‖⁻¹) / Real.log p)`. -/
theorem norm_natCast_inv_le_rpow [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {k : ℕ} (hk : 0 < k) :
    ‖(k : K)⁻¹‖ ≤ (k : ℝ) ^ (Real.log (‖(p : K)‖⁻¹) / Real.log (p : ℝ)) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hinv1 : 1 < ‖(p : K)‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hpi0, hlt⟩
  have hdvd : p ^ padicValNat p k ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
  have hleR : ((p : ℝ) ^ padicValNat p k) ≤ (k : ℝ) := by exact_mod_cast hdvd
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hv_le : (padicValNat p k : ℝ) ≤ Real.log (k : ℝ) / Real.log (p : ℝ) := by
    rw [le_div_iff₀ hlogp]
    have hlog := Real.log_le_log (pow_pos (by linarith) _) hleR
    rwa [Real.log_pow] at hlog
  rw [norm_inv, norm_natCast_eq_pow_padicValNat hp hlt hk.ne', ← inv_pow, ← Real.rpow_natCast]
  have h1 : (‖(p : K)‖⁻¹) ^ (padicValNat p k : ℝ) ≤
      (‖(p : K)‖⁻¹) ^ (Real.log (k : ℝ) / Real.log (p : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hinv1.le hv_le
  refine h1.trans_eq ?_
  rw [Real.rpow_def_of_pos (inv_pos.mpr hpi0), Real.rpow_def_of_pos hkpos]
  congr 1
  ring

/-- **Exact Convergence Radius of `log_p(1 + x)`**:
In any complete ultrametric field `K` of characteristic `0` with `‖(p : K)‖ < 1`,
`∑_{k ≥ 1} (-1)^(k-1) x^k / k` converges if and only if `‖x‖ < 1`. -/
theorem summable_logTerm_iff [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) (x : K) :
    Summable (logTerm x) ↔ ‖x‖ < 1 := by
  constructor
  · intro hs
    by_contra hge
    push Not at hge
    have hnorm : Tendsto (fun k => ‖logTerm x k‖) atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hs.tendsto_atTop_zero
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hnorm.eventually (gt_mem_nhds one_pos))
    have hge1 : 1 ≤ p ^ N := Nat.one_le_pow N p hp.pos
    have hpow_ge : N ≤ p ^ N := (Nat.lt_pow_self hp.one_lt).le
    have hlt1 := hN (p ^ N) hpow_ge
    unfold logTerm at hlt1
    rw [if_neg (by omega : p ^ N ≠ 0), norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, norm_inv, norm_pow, norm_natCast_eq_pow_padicValNat hp hlt (by omega : p ^ N ≠ 0)] at hlt1
    have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
    have hinv_ge : 1 ≤ (‖(p : K)‖ ^ padicValNat p (p ^ N))⁻¹ :=
      one_le_inv₀ (pow_pos hpi0 _) |>.mpr (pow_le_one₀ hpi0.le hlt.le)
    have hx_ge : 1 ≤ ‖x‖ ^ (p ^ N) := one_le_pow₀ hge
    have hprod : 1 ≤ (‖(p : K)‖ ^ padicValNat p (p ^ N))⁻¹ * ‖x‖ ^ (p ^ N) :=
      one_le_mul_of_one_le_of_one_le hinv_ge hx_ge
    linarith
  · intro hx
    by_cases hx0 : x = 0
    · subst hx0
      refine summable_of_ne_finset_zero (s := ∅) fun k _ => ?_
      unfold logTerm
      split_ifs with hk
      · rfl
      · simp [zero_pow hk]
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      set q := Real.sqrt ‖x‖ with hqdef
      have hqpos : 0 < q := Real.sqrt_pos.mpr hxpos
      have hq1 : q < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hx)
      have hqsq : q * q = ‖x‖ := Real.mul_self_sqrt hxpos.le
      set c := Real.log (‖(p : K)‖⁻¹) / Real.log (p : ℝ) with hcdef
      have hneglog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hqpos hq1)
      have hlittle : Tendsto (fun t : ℝ => t ^ c * Real.exp (-(-Real.log q) * t)) atTop (nhds 0) :=
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero c (-Real.log q) hneglog
      have hcomp : Tendsto (fun k : ℕ => (k : ℝ) ^ c * q ^ k) atTop (nhds 0) := by
        have hnat := hlittle.comp tendsto_natCast_atTop_atTop
        refine hnat.congr fun k => ?_
        dsimp only [Function.comp_apply]
        rw [neg_neg, ← Real.rpow_def_of_pos hqpos, Real.rpow_natCast]
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hcomp.eventually (gt_mem_nhds one_pos))
      have hgeom : Summable (fun k : ℕ => q ^ k) := summable_geometric_of_lt_one hqpos.le hq1
      have hsum_norm : Summable (fun k : ℕ => ‖logTerm x k‖) := by
        refine Summable.of_norm_bounded_eventually (g := fun k => q ^ k) hgeom ?_
        rw [Nat.cofinite_eq_atTop, eventually_atTop]
        refine ⟨max N 1, fun k hk => ?_⟩
        have hkN : N ≤ k := le_trans (le_max_left _ _) hk
        have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        unfold logTerm
        rw [if_neg (by omega : k ≠ 0), norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
          one_mul, norm_pow]
        have hkc := norm_natCast_inv_le_rpow hp hlt (by omega : 0 < k)
        have hqpow : ‖x‖ ^ k = q ^ k * q ^ k := by rw [← mul_pow, hqsq]
        have hkc_lt : (k : ℝ) ^ c * q ^ k < 1 := hN k hkN
        calc ‖(k : K)⁻¹‖ * ‖x‖ ^ k
            ≤ (k : ℝ) ^ c * (q ^ k * q ^ k) := by
              rw [hqpow]
              exact mul_le_mul_of_nonneg_right hkc (by positivity)
          _ = ((k : ℝ) ^ c * q ^ k) * q ^ k := by ring
          _ ≤ 1 * q ^ k := mul_le_mul_of_nonneg_right hkc_lt.le (pow_nonneg hqpos.le _)
          _ = q ^ k := one_mul _
      exact hsum_norm.of_norm

/-- The analytic $p$-adic logarithm `log_p(1 + x) = ∑'_{k ≥ 1} (-1)^(k-1) x^k / k`. -/
def logP (x : K) : K := ∑' k, logTerm x k

/-- On the crystalline exponential disk `‖x‖ < expRadius K p`, `‖logP x‖ = ‖x‖`. -/
theorem norm_logP_eq [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {x : K} (hx : ‖x‖ < expRadius K p) :
    ‖logP x‖ = ‖x‖ := by
  have hx1 : ‖x‖ < 1 := hx.trans (expRadius_lt_one hp hlt)
  by_cases hx0 : x = 0
  · subst hx0
    have hzero : logTerm (0 : K) = 0 := by
      funext k
      unfold logTerm
      split_ifs with hk
      · rfl
      · simp [zero_pow hk]
    simp [logP, hzero]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
    have hrpos : 0 < expRadius K p := expRadius_pos hp
    have hs : Summable (logTerm x) := (summable_logTerm_iff hp hlt x).mpr hx1
    have hsplit : logP x - x = ∑' k, logTerm x (k + 2) := by
      unfold logP
      have h1 := hs.sum_add_tsum_nat_add 2
      have hsum2 : ∑ i ∈ Finset.range 2, logTerm x i = x := by
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        simp [logTerm]
      rw [hsum2] at h1
      rw [← h1]
      ring
    have hs2 : Summable (fun k => logTerm x (k + 2)) := (summable_nat_add_iff 2).mpr hs
    have hB0 : 0 ≤ ‖x‖ * (‖x‖ / expRadius K p) :=
      mul_nonneg (norm_nonneg x) (div_nonneg (norm_nonneg x) hrpos.le)
    have htail : ‖logP x - x‖ ≤ ‖x‖ * (‖x‖ / expRadius K p) := by
      rw [hsplit]
      refine ultrametric_norm_tsum_le hB0 hs2 fun k => ?_
      set n := k + 2
      have hn0 : n ≠ 0 := by omega
      have hfac_dvd : n ∣ n.factorial := Nat.dvd_factorial (by omega) le_rfl
      have hv_le : padicValNat p n ≤ padicValNat p n.factorial := by
        have : Fact p.Prime := ⟨hp⟩
        exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
          (dvd_trans pow_padicValNat_dvd hfac_dvd)
      have hnorm_le : ‖logTerm x n‖ ≤ ‖expTerm x n‖ := by
        unfold logTerm expTerm
        rw [if_neg hn0, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
          norm_mul, norm_inv, norm_inv, norm_pow,
          norm_natCast_eq_pow_padicValNat hp hlt hn0,
          norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero n)]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg x) n)
        exact inv_anti₀ (pow_pos hpi0 _) (pow_le_pow_of_le_one hpi0.le hlt.le hv_le)
      have hbd := norm_expTerm_le hp hlt x hn0
      have hq0 : 0 ≤ ‖x‖ / expRadius K p := div_nonneg (norm_nonneg x) hrpos.le
      have hq1 : ‖x‖ / expRadius K p ≤ 1 := ((div_lt_one hrpos).mpr hx).le
      have hpow : (‖x‖ / expRadius K p) ^ n ≤ (‖x‖ / expRadius K p) ^ 2 := by
        change (‖x‖ / expRadius K p) ^ (k + 2) ≤ (‖x‖ / expRadius K p) ^ 2
        rw [pow_add]
        calc (‖x‖ / expRadius K p) ^ k * (‖x‖ / expRadius K p) ^ 2
            ≤ 1 * (‖x‖ / expRadius K p) ^ 2 :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) (sq_nonneg _)
          _ = (‖x‖ / expRadius K p) ^ 2 := one_mul _
      calc ‖logTerm x n‖
          ≤ ‖expTerm x n‖ := hnorm_le
        _ ≤ expRadius K p * (‖x‖ / expRadius K p) ^ n := hbd
        _ ≤ expRadius K p * (‖x‖ / expRadius K p) ^ 2 :=
            mul_le_mul_of_nonneg_left hpow hrpos.le
        _ = ‖x‖ * (‖x‖ / expRadius K p) := by field_simp
    have hq : ‖x‖ / expRadius K p < 1 := (div_lt_one hrpos).mpr hx
    have hstrict : ‖logP x - x‖ < ‖x‖ := by
      calc ‖logP x - x‖
          ≤ ‖x‖ * (‖x‖ / expRadius K p) := htail
        _ < ‖x‖ * 1 := mul_lt_mul_of_pos_left hq hpos
        _ = ‖x‖ := mul_one _
    have hdecomp : logP x = x + (logP x - x) := by ring
    rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hstrict.ne',
      max_eq_left hstrict.le]

end PAdicExpLogRadius

/-! ## Section 2: Frobenius-Lift Dieudonné–Dwork Lemma -/

section DieudonneDwork

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- A formal power series `f ∈ K[[X]]` is **integral** (`f ∈ O_K[[X]]`) if every coefficient
has norm `≤ 1`. -/
def IsIntegralPS (f : PowerSeries K) : Prop :=
  ∀ n : ℕ, ‖PowerSeries.coeff n f‖ ≤ 1

/-- `f ∈ K[[X]]` has all coefficients bounded by `B`. -/
def CoeffNormLe (B : ℝ) (f : PowerSeries K) : Prop :=
  ∀ n : ℕ, ‖PowerSeries.coeff n f‖ ≤ B

/-- `f ∈ 1 + p O_K[[X]]`: constant term `1` and all higher coefficients of norm `≤ ‖(p : K)‖`. -/
def CongOneModP (p : ℕ) (f : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff f = 1 ∧ ∀ n : ℕ, 1 ≤ n → ‖PowerSeries.coeff n f‖ ≤ ‖(p : K)‖

lemma coeffNormLe_add {B : ℝ} {f g : PowerSeries K} (hf : CoeffNormLe B f) (hg : CoeffNormLe B g) :
    CoeffNormLe B (f + g) := fun n => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

lemma coeffNormLe_sub {B : ℝ} {f g : PowerSeries K} (hf : CoeffNormLe B f) (hg : CoeffNormLe B g) :
    CoeffNormLe B (f - g) := fun n => by
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) ?_)
  rw [norm_neg]
  exact hg n

lemma coeffNormLe_mul {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) {f g : PowerSeries K}
    (hf : CoeffNormLe B₁ f) (hg : CoeffNormLe B₂ g) :
    CoeffNormLe (B₁ * B₂) (f * g) := fun n => by
  rw [PowerSeries.coeff_mul]
  refine ultrametric_norm_sum_le _ _ (mul_nonneg hB₁ hB₂) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf x.1) (hg x.2) (norm_nonneg _) hB₁

lemma coeffNormLe_sum {ι : Type*} (s : Finset ι) {B : ℝ} (hB : 0 ≤ B)
    {f : ι → PowerSeries K} (hf : ∀ i ∈ s, CoeffNormLe B (f i)) :
    CoeffNormLe B (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]
  exact ultrametric_norm_sum_le s _ hB fun i hi => hf i hi n

omit [IsUltrametricDist K] in
lemma isIntegralPS_one : IsIntegralPS (1 : PowerSeries K) := fun n => by
  rw [PowerSeries.coeff_one]
  split_ifs <;> simp

lemma isIntegralPS_mul {f g : PowerSeries K} (hf : IsIntegralPS f) (hg : IsIntegralPS g) :
    IsIntegralPS (f * g) := by
  simpa [IsIntegralPS, CoeffNormLe] using coeffNormLe_mul zero_le_one zero_le_one hf hg

lemma isIntegralPS_pow {f : PowerSeries K} (hf : IsIntegralPS f) (k : ℕ) :
    IsIntegralPS (f ^ k) := by
  induction k with
  | zero => simpa using isIntegralPS_one (K := K)
  | succ k ih => rw [pow_succ]; exact isIntegralPS_mul ih hf

omit [IsUltrametricDist K] in
lemma isIntegralPS_C_mul_X_pow {a : K} (ha : ‖a‖ ≤ 1) (m : ℕ) :
    IsIntegralPS (PowerSeries.C a * PowerSeries.X ^ m) := fun n => by
  rw [PowerSeries.coeff_C_mul_X_pow]
  split_ifs
  · exact ha
  · simp

/-- Multiplicative inverse of a power series `f` with `constantCoeff f = 1`. -/
def invOnePS (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.invOfUnit f 1

omit [IsUltrametricDist K] in
theorem mul_invOnePS {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 1) :
    f * invOnePS f = 1 :=
  PowerSeries.mul_invOfUnit f 1 (by simpa using hf)

omit [IsUltrametricDist K] in
theorem invOnePS_mul {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 1) :
    invOnePS f * f = 1 := by
  rw [mul_comm]
  exact mul_invOnePS hf

omit [IsUltrametricDist K] in
theorem constantCoeff_invOnePS {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.constantCoeff (invOnePS f) = 1 := by
  have h := congrArg PowerSeries.constantCoeff (mul_invOnePS hf)
  simp only [map_mul, hf, one_mul, map_one] at h
  exact h

/-- The inverse of an integral power series with constant term `1` is integral. -/
theorem isIntegralPS_invOnePS {f : PowerSeries K} (hf0 : PowerSeries.constantCoeff f = 1)
    (hf : IsIntegralPS f) : IsIntegralPS (invOnePS f) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_invOnePS hf0, norm_one]
    · have hmul : PowerSeries.coeff (n + 1) (f * invOnePS f) = 0 := by
        rw [mul_invOnePS hf0, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j (invOnePS f)) (n + 1),
        Finset.sum_range_succ'] at hmul
      simp only [Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff, hf0, one_mul] at hmul
      have hsolve : PowerSeries.coeff (n + 1) (invOnePS f) =
          -(∑ k ∈ Finset.range (n + 1),
            PowerSeries.coeff (k + 1) f * PowerSeries.coeff (n - k) (invOnePS f)) := by
        have hsub : ∀ k, n + 1 - (k + 1) = n - k := fun k => Nat.succ_sub_succ_eq_sub n k
        simp_rw [hsub] at hmul
        exact eq_neg_of_add_eq_zero_right hmul
      rw [hsolve, norm_neg]
      refine ultrametric_norm_sum_le _ _ zero_le_one fun k _ => ?_
      rw [norm_mul]
      have hlt : n - k < n + 1 := by omega
      calc ‖PowerSeries.coeff (k + 1) f‖ * ‖PowerSeries.coeff (n - k) (invOnePS f)‖
          ≤ 1 * 1 := mul_le_mul (hf (k + 1)) (ih (n - k) hlt) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- Truncation of a univariate power series strictly below degree `N`. -/
def truncPS (N : ℕ) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => if n < N then PowerSeries.coeff n f else 0

omit [IsUltrametricDist K] in
@[simp] theorem coeff_truncPS (N : ℕ) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (truncPS N f) = if n < N then PowerSeries.coeff n f else 0 := by
  simp [truncPS]

omit [IsUltrametricDist K] in
lemma isIntegralPS_truncPS (N : ℕ) {f : PowerSeries K} (hf : IsIntegralPS f) :
    IsIntegralPS (truncPS N f) := fun n => by
  rw [coeff_truncPS]
  split_ifs
  · exact hf n
  · simp

/-- `LowPS N f` means `f` vanishes strictly below degree `N`. -/
def LowPS (N : ℕ) (f : PowerSeries K) : Prop :=
  ∀ m < N, PowerSeries.coeff m f = 0

omit [IsUltrametricDist K] in
lemma lowPS_add {N : ℕ} {f g : PowerSeries K} (hf : LowPS N f) (hg : LowPS N g) :
    LowPS N (f + g) := fun m hm => by rw [map_add, hf m hm, hg m hm, add_zero]

omit [IsUltrametricDist K] in
lemma lowPS_mul_left {N : ℕ} {f g : PowerSeries K} (hf : LowPS N f) :
    LowPS N (f * g) := fun m hm => by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [hf x.1 (by omega), zero_mul]

omit [IsUltrametricDist K] in
lemma lowPS_mul_right {N : ℕ} {f g : PowerSeries K} (hg : LowPS N g) :
    LowPS N (f * g) := by
  rw [mul_comm]
  exact lowPS_mul_left hg

omit [IsUltrametricDist K] in
lemma lowPS_pow_sub {N : ℕ} {f g : PowerSeries K} (h : LowPS N (f - g)) (k : ℕ) :
    LowPS N (f ^ k - g ^ k) := by
  induction k with
  | zero => intro m _; simp
  | succ k ih =>
    have heq : f ^ (k + 1) - g ^ (k + 1) = (f ^ k - g ^ k) * f + g ^ k * (f - g) := by ring
    rw [heq]
    exact lowPS_add (lowPS_mul_left ih) (lowPS_mul_right h)

omit [IsUltrametricDist K] in
lemma lowPS_sub_truncPS (N : ℕ) (f : PowerSeries K) : LowPS N (f - truncPS N f) := fun m hm => by
  rw [map_sub, coeff_truncPS, if_pos hm, sub_self]

/-- Formal power series Frobenius endomorphism `f(X) ↦ f(X^p)`. -/
def frobPS {R : Type*} [CommSemiring R] (p : ℕ) (hp : 0 < p) : PowerSeries R →+* PowerSeries R where
  toFun f := PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) f else 0
  map_one' := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [if_neg hn]
      split_ifs with hdiv hq
      · obtain ⟨k, rfl⟩ := hdiv
        rw [Nat.mul_div_cancel_left k hp] at hq
        subst hq
        exact (hn (mul_zero p)).elim
      · rfl
      · rfl
  map_mul' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    split_ifs with hdiv
    · obtain ⟨m, rfl⟩ := hdiv
      rw [Nat.mul_div_cancel_left m hp]
      symm
      rw [← Finset.sum_filter_of_ne (p := fun x : ℕ × ℕ => p ∣ x.1)
        (fun x _ hx => by by_contra h; exact hx (by simp [h]))]
      refine Finset.sum_bij (fun x _ => (x.1 / p, x.2 / p)) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
        obtain ⟨hsum, a, ha⟩ := hx
        have hb : p ∣ x.2 := by
          have : x.2 = p * (m - a) := by
            have ham : a ≤ m := by nlinarith
            rw [Nat.mul_sub_left_distrib]
            omega
          exact ⟨m - a, this⟩
        obtain ⟨b, hb'⟩ := hb
        rw [Finset.mem_antidiagonal, ha, hb', Nat.mul_div_cancel_left a hp,
          Nat.mul_div_cancel_left b hp]
        nlinarith
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx₁ hx₂
        have h1d : p ∣ x₁.2 := by
          obtain ⟨a, ha⟩ := hx₁.2
          exact ⟨m - a, by rw [Nat.mul_sub_left_distrib]; omega⟩
        have h2d : p ∣ x₂.2 := by
          obtain ⟨a, ha⟩ := hx₂.2
          exact ⟨m - a, by rw [Nat.mul_sub_left_distrib]; omega⟩
        have hfst : x₁.1 / p = x₂.1 / p := congrArg Prod.fst heq
        have hsnd : x₁.2 / p = x₂.2 / p := congrArg Prod.snd heq
        ext
        · rw [← Nat.mul_div_cancel' hx₁.2, hfst, Nat.mul_div_cancel' hx₂.2]
        · rw [← Nat.mul_div_cancel' h1d, hsnd, Nat.mul_div_cancel' h2d]
      · intro y hy
        rw [Finset.mem_antidiagonal] at hy
        refine ⟨(p * y.1, p * y.2), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_antidiagonal]
          exact ⟨by rw [← Nat.mul_add, hy], dvd_mul_right p y.1⟩
        · ext <;> simp [Nat.mul_div_cancel_left _ hp]
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
        have h2d : p ∣ x.2 := by
          obtain ⟨a, ha⟩ := hx.2
          exact ⟨m - a, by rw [Nat.mul_sub_left_distrib]; omega⟩
        simp [hx.2, h2d]
    · symm
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      by_cases h1 : p ∣ x.1
      · have h2 : ¬ p ∣ x.2 := fun h2 => hdiv (hx ▸ dvd_add h1 h2)
        simp [h1, h2]
      · simp [h1]
  map_zero' := by ext n; simp
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add]
    split_ifs <;> simp

@[simp] theorem coeff_frobPS {R : Type*} [CommSemiring R] (p : ℕ) (hp : 0 < p)
    (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (frobPS p hp f) = if p ∣ n then PowerSeries.coeff (n / p) f else 0 := by
  simp [frobPS]

/-- `frobPS p hp f` agrees identically with formal substitution `f(X^p)`. -/
theorem frobPS_eq_subst {R : Type*} [CommRing R] (p : ℕ) (hp : 0 < p) (f : PowerSeries R) :
    frobPS p hp f = PowerSeries.subst (PowerSeries.X ^ p) f := by
  have hs : PowerSeries.HasSubst (PowerSeries.X ^ p : PowerSeries R) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
    change PowerSeries.constantCoeff (PowerSeries.X ^ p : PowerSeries R) = 0
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow hp.ne']
  ext n
  rw [coeff_frobPS]
  change (if p ∣ n then PowerSeries.coeff (n / p) f else 0) =
    MvPowerSeries.coeff (Finsupp.single () n) (PowerSeries.subst (PowerSeries.X ^ p) f)
  rw [PowerSeries.coeff_subst hs]
  have hpow : ∀ k : ℕ, MvPowerSeries.coeff (Finsupp.single () n)
      ((PowerSeries.X ^ p : PowerSeries R) ^ k) = if n = p * k then 1 else 0 := by
    intro k
    change PowerSeries.coeff n ((PowerSeries.X ^ p : PowerSeries R) ^ k) = _
    rw [← pow_mul, PowerSeries.coeff_X_pow]
  simp_rw [hpow, smul_eq_mul]
  split_ifs with hdiv
  · rw [finsum_eq_single _ (n / p)]
    · rw [if_pos (Nat.mul_div_cancel' hdiv).symm, mul_one]
    · intro k hk
      have hne : n ≠ p * k := by
        intro heq
        apply hk
        rw [heq, Nat.mul_div_cancel_left k hp]
      rw [if_neg hne, mul_zero]
  · symm
    refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
    have hne : n ≠ p * k := fun heq => hdiv ⟨k, heq⟩
    rw [if_neg hne, mul_zero]

/-- Twisted crystalline Frobenius operator `f(X) ↦ f^σ(X^p)` for a ring endomorphism `σ : R →+* R`. -/
def frobMapPS {R : Type*} [CommSemiring R] (σ : R →+* R) (p : ℕ) (hp : 0 < p) :
    PowerSeries R →+* PowerSeries R :=
  (PowerSeries.map σ).comp (frobPS p hp)

@[simp] theorem coeff_frobMapPS {R : Type*} [CommSemiring R] (σ : R →+* R) (p : ℕ) (hp : 0 < p)
    (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (frobMapPS σ p hp f) =
      if p ∣ n then σ (PowerSeries.coeff (n / p) f) else 0 := by
  simp only [frobMapPS, RingHom.comp_apply, PowerSeries.coeff_map, coeff_frobPS]
  split_ifs <;> simp

@[simp] theorem frobMapPS_id {R : Type*} [CommSemiring R] (p : ℕ) (hp : 0 < p) :
    frobMapPS (RingHom.id R) p hp = frobPS p hp := by
  ext f n
  simp

/-- **Frobenius-Lift Congruence for Integral Power Series**:
If `σ : K →+* K` is a Frobenius lift (`‖c^p - σ c‖ ≤ ‖p‖` for all `‖c‖ ≤ 1`), then for every
integral power series `f ∈ O_K[[X]]`, `f(X)^p ≡ f^σ(X^p) (mod p O_K[[X]])`. -/
theorem frobMapPS_pow_sub_norm_le {p : ℕ} (hp : p.Prime)
    (σ : K →+* K) (hflt : ∀ c : K, ‖c‖ ≤ 1 → ‖c ^ p - σ c‖ ≤ ‖(p : K)‖)
    {f : PowerSeries K} (hf : IsIntegralPS f) :
    CoeffNormLe ‖(p : K)‖ (f ^ p - frobMapPS σ p hp.pos f) := by
  have htrunc : ∀ N : ℕ, CoeffNormLe ‖(p : K)‖
      ((truncPS N f) ^ p - frobMapPS σ p hp.pos (truncPS N f)) := by
    intro N
    induction N with
    | zero =>
      intro n
      have hz : truncPS 0 f = 0 := by ext m; simp
      rw [hz, zero_pow hp.ne_zero, map_zero, sub_self, map_zero, norm_zero]
      exact norm_nonneg _
    | succ N ih =>
      set A := truncPS N f with hAdef
      set c := PowerSeries.coeff N f with hcdef
      set B := PowerSeries.C c * PowerSeries.X ^ N with hBdef
      have hAB : truncPS (N + 1) f = A + B := by
        ext m
        rw [coeff_truncPS, map_add, coeff_truncPS, PowerSeries.coeff_C_mul_X_pow]
        by_cases hltN : m < N
        · have hm : m < N + 1 := by omega
          have hne : m ≠ N := by omega
          simp [hltN, hm, hne]
        · by_cases heq : m = N
          · subst heq
            simp [c]
          · have hge : ¬ m < N + 1 := by omega
            simp [hltN, heq, hge]
      have hAint : IsIntegralPS A := isIntegralPS_truncPS N hf
      have hBint : IsIntegralPS B := isIntegralPS_C_mul_X_pow (hf N) N
      have hsplit : (A + B) ^ p - frobMapPS σ p hp.pos (A + B) =
          ((A + B) ^ p - A ^ p - B ^ p) + (A ^ p - frobMapPS σ p hp.pos A) +
            (B ^ p - frobMapPS σ p hp.pos B) := by
        rw [map_add]
        ring
      rw [hAB, hsplit]
      refine coeffNormLe_add (coeffNormLe_add ?_ ih) ?_
      · have hbin : (A + B) ^ p - A ^ p - B ^ p =
            ∑ j ∈ Finset.Ioo 0 p, A ^ j * B ^ (p - j) * (p.choose j : PowerSeries K) := by
          rw [add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, mul_one,
            Nat.cast_one, mul_one]
          have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
          rw [← Finset.add_sum_erase _ _ h0]
          simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
          have herase : (Finset.range p).erase 0 = Finset.Ioo 0 p := by
            ext j
            simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ioo]
            omega
          rw [herase]
          ring
        rw [hbin]
        refine coeffNormLe_sum _ (norm_nonneg _) fun j hj => ?_
        rw [Finset.mem_Ioo] at hj
        have hdvd : p ∣ p.choose j := hp.dvd_choose_self hj.1.ne' hj.2
        have hch : ‖((p.choose j : ℕ) : K)‖ ≤ ‖(p : K)‖ := by
          obtain ⟨q, hq⟩ := hdvd
          rw [hq, Nat.cast_mul, norm_mul]
          calc ‖(p : K)‖ * ‖(q : K)‖ ≤ ‖(p : K)‖ * 1 :=
                mul_le_mul_of_nonneg_left (norm_natCast_le_one q) (norm_nonneg _)
            _ = ‖(p : K)‖ := mul_one _
        intro n
        have hint := isIntegralPS_mul (isIntegralPS_pow hAint j) (isIntegralPS_pow hBint (p - j)) n
        rw [show (p.choose j : PowerSeries K) = PowerSeries.C ((p.choose j : ℕ) : K) by simp,
          mul_comm, PowerSeries.coeff_C_mul, norm_mul]
        calc ‖((p.choose j : ℕ) : K)‖ * ‖PowerSeries.coeff n (A ^ j * B ^ (p - j))‖
            ≤ ‖(p : K)‖ * 1 := mul_le_mul hch hint (norm_nonneg _) (norm_nonneg _)
          _ = ‖(p : K)‖ := mul_one _
      · intro n
        have hBp : B ^ p = PowerSeries.C (c ^ p) * PowerSeries.X ^ (p * N) := by
          rw [hBdef, mul_pow, ← map_pow, ← pow_mul, mul_comm N p]
        have hBf : frobMapPS σ p hp.pos B = PowerSeries.C (σ c) * PowerSeries.X ^ (p * N) := by
          ext m
          rw [coeff_frobMapPS, hBdef, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul_X_pow]
          by_cases hm : m = p * N
          · subst hm
            rw [if_pos (dvd_mul_right p N), Nat.mul_div_cancel_left N hp.pos, if_pos rfl, if_pos rfl]
          · rw [if_neg hm]
            split_ifs with hdiv hq
            · obtain ⟨k, rfl⟩ := hdiv
              rw [Nat.mul_div_cancel_left k hp.pos] at hq
              subst hq
              exact (hm rfl).elim
            · exact map_zero σ
            · rfl
        rw [hBp, hBf, ← sub_mul, ← map_sub, PowerSeries.coeff_C_mul_X_pow]
        split_ifs
        · exact hflt c (hf N)
        · simp
  intro n
  have hpow_eq : PowerSeries.coeff n (f ^ p) = PowerSeries.coeff n ((truncPS (n + 1) f) ^ p) := by
    have hlow := lowPS_pow_sub (lowPS_sub_truncPS (n + 1) f) p n (Nat.lt_succ_self n)
    rw [map_sub, sub_eq_zero] at hlow
    exact hlow
  have hfrob_eq : PowerSeries.coeff n (frobMapPS σ p hp.pos f) =
      PowerSeries.coeff n (frobMapPS σ p hp.pos (truncPS (n + 1) f)) := by
    rw [coeff_frobMapPS, coeff_frobMapPS]
    split_ifs with hdiv
    · rw [coeff_truncPS, if_pos (Nat.lt_succ_of_le (Nat.div_le_self n p))]
    · rfl
  rw [map_sub, hpow_eq, hfrob_eq, ← map_sub]
  exact htrunc (n + 1) n

omit [IsUltrametricDist K] in
/-- Coefficient identity for the `p`-th power when splitting off the `n`-th term (`n ≥ 1`):
if `constantCoeff f = 1` and `f₀ = truncPS n f`, then
- `coeff m (f^p) = coeff m (f₀^p)` for `m < n`, and
- `coeff n (f^p) = coeff n (f₀^p) + p * coeff n f`. -/
lemma coeff_pow_prime_split {p : ℕ} (hp : p.Prime) {f : PowerSeries K}
    (hf0 : PowerSeries.constantCoeff f = 1) {n : ℕ} (hn : 1 ≤ n) :
    (∀ m < n, PowerSeries.coeff m (f ^ p) = PowerSeries.coeff m ((truncPS n f) ^ p)) ∧
      PowerSeries.coeff n (f ^ p) =
        PowerSeries.coeff n ((truncPS n f) ^ p) + (p : K) * PowerSeries.coeff n f := by
  set f₀ := truncPS n f with hf0def
  set a := PowerSeries.coeff n f with hadef
  set g := f₀ + PowerSeries.C a * PowerSeries.X ^ n with hgdef
  have hfg : LowPS (n + 1) (f - g) := fun m hm => by
    rw [map_sub, map_add, coeff_truncPS, PowerSeries.coeff_C_mul_X_pow]
    by_cases hlt : m < n
    · have hne : m ≠ n := by omega
      simp [hlt, hne]
    · have heq : m = n := by omega
      subst heq
      simp [a]
  have hpow_fg : ∀ m ≤ n, PowerSeries.coeff m (f ^ p) = PowerSeries.coeff m (g ^ p) := by
    intro m hm
    have hlow := lowPS_pow_sub hfg p m (Nat.lt_succ_of_le hm)
    rw [map_sub, sub_eq_zero] at hlow
    exact hlow
  have hexp : g ^ p = f₀ ^ p +
      PowerSeries.C ((p : K) * a) * PowerSeries.X ^ n * f₀ ^ (p - 1) +
      ∑ j ∈ Finset.Icc 2 p,
        (PowerSeries.C a * PowerSeries.X ^ n) ^ j * f₀ ^ (p - j) * (p.choose j : PowerSeries K) := by
    rw [hgdef, add_comm, add_pow]
    have hp2 : 2 ≤ p := hp.two_le
    have hsplit : Finset.range (p + 1) = {0, 1} ∪ Finset.Icc 2 p := by
      ext j
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_Icc]
      omega
    have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 p) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj1
      simp only [Finset.mem_Icc] at hj2
      omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      pow_one, Nat.choose_one_right, map_mul, map_natCast]
    congr 1
    ring
  have htail_zero : ∀ m ≤ n, PowerSeries.coeff m
      (∑ j ∈ Finset.Icc 2 p,
        (PowerSeries.C a * PowerSeries.X ^ n) ^ j * f₀ ^ (p - j) *
          (p.choose j : PowerSeries K)) = 0 := by
    intro m hm
    rw [map_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hlow : LowPS (j * n) ((PowerSeries.C a * PowerSeries.X ^ n) ^ j) := by
      rw [mul_pow, ← pow_mul, mul_comm n j]
      intro k hk
      rw [← map_pow, PowerSeries.coeff_C_mul_X_pow, if_neg (by omega)]
    exact lowPS_mul_left (lowPS_mul_left hlow) m (by nlinarith)
  have hmid : ∀ m ≤ n, PowerSeries.coeff m
      (PowerSeries.C ((p : K) * a) * PowerSeries.X ^ n * f₀ ^ (p - 1)) =
      if m = n then (p : K) * a else 0 := by
    intro m hm
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    split_ifs with hle heq
    · have hmn : m - n = 0 := by omega
      rw [hmn, PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
      have hcf0 : PowerSeries.constantCoeff f₀ = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_truncPS, if_pos (by omega),
          PowerSeries.coeff_zero_eq_constantCoeff, hf0]
      rw [hcf0, one_pow, mul_one]
    · omega
    · omega
    · simp
  constructor
  · intro m hm
    rw [hpow_fg m hm.le, hexp, map_add, map_add, htail_zero m hm.le, add_zero,
      hmid m hm.le, if_neg hm.ne, add_zero]
  · rw [hpow_fg n le_rfl, hexp, map_add, map_add, htail_zero n le_rfl, add_zero,
      hmid n le_rfl, if_pos rfl]

/-- **Frobenius-Lift Dieudonné–Dwork Lemma (`dieudonne_dwork_iff`)**:
Let `K` be an ultrametric normed field of characteristic `0` with prime `p` and a Frobenius lift
`σ : K →+* K` satisfying `‖c^p - σ c‖ ≤ ‖(p : K)‖` for all `‖c‖ ≤ 1`.
Then for any formal power series `f ∈ 1 + X K[[X]]`:
`f ∈ O_K[[X]]  ↔  f^σ(X^p) / f(X)^p ∈ 1 + p O_K[[X]]`! -/
theorem dieudonne_dwork_iff [CharZero K] {p : ℕ} (hp : p.Prime)
    (σ : K →+* K) (hflt : ∀ c : K, ‖c‖ ≤ 1 → ‖c ^ p - σ c‖ ≤ ‖(p : K)‖)
    {f : PowerSeries K} (hf0 : PowerSeries.constantCoeff f = 1) :
    IsIntegralPS f ↔ CongOneModP p (frobMapPS σ p hp.pos f * (invOnePS f) ^ p) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  constructor
  · intro hf
    set g := frobMapPS σ p hp.pos f * (invOnePS f) ^ p with hgdef
    have hg0 : PowerSeries.constantCoeff g = 1 := by
      rw [hgdef, map_mul, map_pow, constantCoeff_invOnePS hf0, one_pow, mul_one,
        ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_frobMapPS, if_pos (dvd_zero p),
        Nat.zero_div, PowerSeries.coeff_zero_eq_constantCoeff, hf0, map_one]
    refine ⟨hg0, fun n hn => ?_⟩
    have hdiff : g - 1 = (frobMapPS σ p hp.pos f - f ^ p) * (invOnePS f) ^ p := by
      rw [hgdef, sub_mul, ← mul_pow, mul_invOnePS hf0, one_pow]
    have hcong : CoeffNormLe ‖(p : K)‖ (frobMapPS σ p hp.pos f - f ^ p) := by
      have h := frobMapPS_pow_sub_norm_le hp σ hflt hf
      intro m
      rw [show frobMapPS σ p hp.pos f - f ^ p = -(f ^ p - frobMapPS σ p hp.pos f) by ring,
        map_neg, norm_neg]
      exact h m
    have hinvp : IsIntegralPS ((invOnePS f) ^ p) :=
      isIntegralPS_pow (isIntegralPS_invOnePS hf0 hf) p
    have hprod := coeffNormLe_mul hpi0.le zero_le_one hcong hinvp n
    rw [mul_one, ← hdiff, map_sub, PowerSeries.coeff_one, if_neg (by omega : n ≠ 0), sub_zero] at hprod
    exact hprod
  · intro hg
    set g := frobMapPS σ p hp.pos f * (invOnePS f) ^ p with hgdef
    have heq : frobMapPS σ p hp.pos f = g * f ^ p := by
      rw [hgdef, mul_assoc, ← mul_pow, invOnePS_mul hf0, one_pow, mul_one]
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · rw [PowerSeries.coeff_zero_eq_constantCoeff, hf0, norm_one]
      · set m := n + 1 with hmdef
        set f₀ := truncPS m f with hf0def
        have hf₀_int : IsIntegralPS f₀ := fun k => by
          rw [coeff_truncPS]
          split_ifs with hk
          · exact ih k hk
          · simp
        have hsplit := coeff_pow_prime_split hp hf0 (by omega : 1 ≤ m)
        have hfrob_eq : PowerSeries.coeff m (frobMapPS σ p hp.pos f) =
            PowerSeries.coeff m (frobMapPS σ p hp.pos f₀) := by
          rw [coeff_frobMapPS, coeff_frobMapPS]
          split_ifs with hdiv
          · have hltm : m / p < m := Nat.div_lt_self (by omega) hp.one_lt
            rw [coeff_truncPS, if_pos hltm]
          · rfl
        have hmul_eq : PowerSeries.coeff m (g * f ^ p) =
            PowerSeries.coeff m (g * f₀ ^ p) + (p : K) * PowerSeries.coeff m f := by
          rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i g * PowerSeries.coeff j (f ^ p)) m,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i g * PowerSeries.coeff j (f₀ ^ p)) m]
          conv_lhs => rw [Finset.sum_range_succ']
          conv_rhs => rw [Finset.sum_range_succ']
          simp only [Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff, hg.1, one_mul]
          have hsum_eq : ∑ k ∈ Finset.range m,
              PowerSeries.coeff (k + 1) g * PowerSeries.coeff (m - (k + 1)) (f ^ p) =
              ∑ k ∈ Finset.range m,
              PowerSeries.coeff (k + 1) g * PowerSeries.coeff (m - (k + 1)) (f₀ ^ p) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsplit.1 (m - (k + 1)) (by omega)]
          rw [hsum_eq, hsplit.2]
          ring
        have hpa : (p : K) * PowerSeries.coeff m f =
            PowerSeries.coeff m (frobMapPS σ p hp.pos f₀ - f₀ ^ p) -
              PowerSeries.coeff m ((g - 1) * f₀ ^ p) := by
          have hc := congrArg (PowerSeries.coeff m) heq
          rw [hfrob_eq, hmul_eq] at hc
          have hsub : frobMapPS σ p hp.pos f₀ - f₀ ^ p - (g - 1) * f₀ ^ p =
              frobMapPS σ p hp.pos f₀ - g * f₀ ^ p := by ring
          rw [← map_sub, hsub, map_sub]
          linear_combination -hc
        have hterm1 : ‖PowerSeries.coeff m (frobMapPS σ p hp.pos f₀ - f₀ ^ p)‖ ≤ ‖(p : K)‖ := by
          rw [show frobMapPS σ p hp.pos f₀ - f₀ ^ p = -(f₀ ^ p - frobMapPS σ p hp.pos f₀) by ring,
            map_neg, norm_neg]
          exact frobMapPS_pow_sub_norm_le hp σ hflt hf₀_int m
        have hg1 : CoeffNormLe ‖(p : K)‖ (g - 1) := fun k => by
          rw [map_sub, PowerSeries.coeff_one]
          rcases k with _ | k
          · rw [if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff, hg.1, sub_self, norm_zero]
            exact hpi0.le
          · rw [if_neg (Nat.succ_ne_zero k), sub_zero]
            exact hg.2 (k + 1) (by omega)
        have hterm2 : ‖PowerSeries.coeff m ((g - 1) * f₀ ^ p)‖ ≤ ‖(p : K)‖ := by
          simpa using coeffNormLe_mul hpi0.le zero_le_one hg1 (isIntegralPS_pow hf₀_int p) m
        have hbd : ‖(p : K)‖ * ‖PowerSeries.coeff m f‖ ≤ ‖(p : K)‖ := by
          rw [← norm_mul, hpa, sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hterm1 ?_)
          rwa [norm_neg]
        exact le_of_mul_le_mul_left (by simpa using hbd) hpi0

/-- Multiplicative form of the Dieudonné–Dwork Lemma (without explicit inverse):
`f ∈ O_K[[X]] ↔ ∃ g ∈ 1 + p O_K[[X]], f^σ(X^p) = g(X) * f(X)^p`. -/
theorem dieudonne_dwork_exists_iff [CharZero K] {p : ℕ} (hp : p.Prime)
    (σ : K →+* K) (hflt : ∀ c : K, ‖c‖ ≤ 1 → ‖c ^ p - σ c‖ ≤ ‖(p : K)‖)
    {f : PowerSeries K} (hf0 : PowerSeries.constantCoeff f = 1) :
    IsIntegralPS f ↔ ∃ g : PowerSeries K, CongOneModP p g ∧ frobMapPS σ p hp.pos f = g * f ^ p := by
  rw [dieudonne_dwork_iff hp σ hflt hf0]
  constructor
  · intro hg
    refine ⟨frobMapPS σ p hp.pos f * (invOnePS f) ^ p, hg, ?_⟩
    rw [mul_assoc, ← mul_pow, invOnePS_mul hf0, one_pow, mul_one]
  · rintro ⟨g, hg, heq⟩
    have hgeq : frobMapPS σ p hp.pos f * (invOnePS f) ^ p = g := by
      rw [heq, mul_assoc, ← mul_pow, mul_invOnePS hf0, one_pow, mul_one]
    rwa [hgeq]

/-- **Fermat's Little Theorem in `ℤ_[p]`**:
Every `p`-adic integer `c ∈ ℚ_[p]` (`‖c‖ ≤ 1`) satisfies `‖c ^ p - c‖ ≤ ‖(p : ℚ_[p])‖`. -/
theorem padic_pow_prime_sub_le (p : ℕ) [Fact p.Prime] {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    ‖c ^ p - c‖ ≤ ‖(p : ℚ_[p])‖ := by
  have hp : p.Prime := Fact.out
  let z : ℤ_[p] := ⟨c, hc⟩
  have hzero : PadicInt.toZMod (z ^ p - z) = 0 := by
    rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  have hmem : z ^ p - z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]
    exact hzero
  have hnu : ¬ IsUnit (z ^ p - z) := (IsLocalRing.mem_maximalIdeal _).mp hmem
  have hne1 : ‖z ^ p - z‖ ≠ 1 := by rwa [PadicInt.isUnit_iff] at hnu
  have hval_eq : ((z ^ p - z : ℤ_[p]) : ℚ_[p]) = c ^ p - c := by
    change ((z : ℚ_[p]) ^ p - (z : ℚ_[p])) = c ^ p - c
    rfl
  have hlt1 : ‖c ^ p - c‖ < 1 := by
    have hle1 : ‖z ^ p - z‖ ≤ 1 := (z ^ p - z).2
    have hlt : ‖z ^ p - z‖ < 1 := lt_of_le_of_ne hle1 hne1
    rwa [PadicInt.norm_def, hval_eq] at hlt
  by_cases h0 : c ^ p - c = 0
  · rw [h0, norm_zero]
    exact norm_nonneg _
  · rw [Padic.norm_eq_zpow_neg_valuation h0] at hlt1 ⊢
    rw [Padic.norm_p]
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hvpos : (0 : ℤ) < (c ^ p - c).valuation := by
      by_contra hle
      push Not at hle
      have hge1 : (1 : ℝ) ≤ (p : ℝ) ^ (-(c ^ p - c).valuation) :=
        one_le_zpow₀ hp1.le (by omega)
      linarith
    have hle_neg1 : -(c ^ p - c).valuation ≤ (-1 : ℤ) := by omega
    calc (p : ℝ) ^ (-(c ^ p - c).valuation)
        ≤ (p : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hp1.le hle_neg1
      _ = (p : ℝ)⁻¹ := zpow_neg_one _

/-- **Classical Dieudonné–Dwork Lemma over `ℚ_[p]`**:
For any `f ∈ 1 + X ℚ_[p][[X]]`,
`f ∈ ℤ_[p][[X]]  ↔  f(X^p) / f(X)^p ∈ 1 + p ℤ_[p][[X]]`. -/
theorem padic_dieudonne_dwork_iff (p : ℕ) [Fact p.Prime] {f : PowerSeries ℚ_[p]}
    (hf0 : PowerSeries.constantCoeff f = 1) :
    IsIntegralPS f ↔ CongOneModP p (frobPS p (Fact.out : p.Prime).pos f * (invOnePS f) ^ p) := by
  have hp : p.Prime := Fact.out
  have h := dieudonne_dwork_iff (K := ℚ_[p]) hp (RingHom.id ℚ_[p])
    (fun c hc => padic_pow_prime_sub_le p hc) hf0
  simpa [frobMapPS_id] using h

end DieudonneDwork

/-! ## Section 3: Formal `expPS` Calculus & Artin–Hasse Exponential Integrality -/

section ArtinHasse

/-- Formal univariate exponential `exp(A) = subst A (PowerSeries.exp R)`.
Note that `PowerSeries R = MvPowerSeries Unit R` definitionally, so `expPS A = mvExp A`. -/
def expPS {R : Type*} [Field R] [CharZero R] (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.subst A (PowerSeries.exp R)

lemma coeff_pow_eq_zero_of_lt {R : Type*} [CommSemiring R] {A : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 0) :
    ∀ k m : ℕ, m < k → PowerSeries.coeff m (A ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    by_cases h1 : x.1 < k
    · rw [ih x.1 h1, zero_mul]
    · have hx2 : x.2 = 0 := by omega
      rw [hx2, PowerSeries.coeff_zero_eq_constantCoeff, hA, mul_zero]

theorem coeff_expPS_eq_sum {R : Type*} [Field R] [CharZero R] {A : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 0) (n : ℕ) :
    PowerSeries.coeff n (expPS A) =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : R)⁻¹ * PowerSeries.coeff n (A ^ k) := by
  have hs : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero hA
  unfold expPS
  change MvPowerSeries.coeff (Finsupp.single () n) (PowerSeries.subst A (PowerSeries.exp R)) = _
  rw [PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    change PowerSeries.coeff k (PowerSeries.exp R) • PowerSeries.coeff n (A ^ k) = _
    rw [smul_eq_mul, PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, one_div]
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hge
    apply hk
    change PowerSeries.coeff k (PowerSeries.exp R) • PowerSeries.coeff n (A ^ k) = 0
    rw [coeff_pow_eq_zero_of_lt hA k n (by omega), smul_zero]

theorem constantCoeff_expPS {R : Type*} [Field R] [CharZero R] {A : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.constantCoeff (expPS A) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_expPS_eq_sum hA 0]
  simp

theorem expPS_zero {R : Type*} [Field R] [CharZero R] :
    expPS (0 : PowerSeries R) = 1 := by
  ext n
  rw [coeff_expPS_eq_sum (by simp) n, PowerSeries.coeff_one]
  rcases n with _ | n
  · simp
  · rw [if_neg (Nat.succ_ne_zero n)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases k with _ | k
    · rw [pow_zero, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), mul_zero]
    · rw [zero_pow (Nat.succ_ne_zero k), map_zero, mul_zero]

/-- **Formal Exponential Addition Law**:
For `A, B ∈ X R[[X]]`, `exp(A + B) = exp(A) * exp(B)`. -/
theorem expPS_add {R : Type*} [Field R] [CharZero R] {A B : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0) :
    expPS (A + B) = expPS A * expPS B := by
  have hAB : PowerSeries.constantCoeff (A + B) = 0 := by rw [map_add, hA, hB, add_zero]
  ext n
  rw [coeff_expPS_eq_sum hAB n, PowerSeries.coeff_mul]
  have hLHS : ∑ k ∈ Finset.range (n + 1), (k.factorial : R)⁻¹ * PowerSeries.coeff n ((A + B) ^ k) =
      ∑ k ∈ Finset.range (n + 1), ∑ x ∈ Finset.antidiagonal k,
        (x.1.factorial : R)⁻¹ * (x.2.factorial : R)⁻¹ * PowerSeries.coeff n (A ^ x.1 * B ^ x.2) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [add_pow, map_sum, Finset.mul_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (i.factorial : R)⁻¹ * (j.factorial : R)⁻¹ *
          PowerSeries.coeff n (A ^ i * B ^ j)) k]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hch : (k.choose i : R) * (i.factorial : R) * ((k - i).factorial : R) =
        (k.factorial : R) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
    have hkf : (k.factorial : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hif : (i.factorial : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hsubf : ((k - i).factorial : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - i))
    rw [show (k.choose i : PowerSeries R) = PowerSeries.C (k.choose i : R) by simp,
      mul_comm _ (PowerSeries.C _), PowerSeries.coeff_C_mul]
    field_simp [hkf, hif, hsubf]
    linear_combination PowerSeries.coeff n (A ^ i * B ^ (k - i)) * hch
  rw [hLHS]
  have hRHS : ∑ p ∈ Finset.antidiagonal n,
      PowerSeries.coeff p.1 (expPS A) * PowerSeries.coeff p.2 (expPS B) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
        (a.factorial : R)⁻¹ * (b.factorial : R)⁻¹ * PowerSeries.coeff n (A ^ a * B ^ b) := by
    have h1 : ∀ p ∈ Finset.antidiagonal n,
        PowerSeries.coeff p.1 (expPS A) * PowerSeries.coeff p.2 (expPS B) =
        ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          ((a.factorial : R)⁻¹ * PowerSeries.coeff p.1 (A ^ a)) *
          ((b.factorial : R)⁻¹ * PowerSeries.coeff p.2 (B ^ b)) := by
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rw [coeff_expPS_eq_sum hA p.1, coeff_expPS_eq_sum hB p.2]
      have hA_ext : ∑ k ∈ Finset.range (p.1 + 1), (k.factorial : R)⁻¹ * PowerSeries.coeff p.1 (A ^ k) =
          ∑ a ∈ Finset.range (n + 1), (a.factorial : R)⁻¹ * PowerSeries.coeff p.1 (A ^ a) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun a _ ha => ?_
        rw [Finset.mem_range] at ha
        rw [coeff_pow_eq_zero_of_lt hA a p.1 (by omega), mul_zero]
      have hB_ext : ∑ k ∈ Finset.range (p.2 + 1), (k.factorial : R)⁻¹ * PowerSeries.coeff p.2 (B ^ k) =
          ∑ b ∈ Finset.range (n + 1), (b.factorial : R)⁻¹ * PowerSeries.coeff p.2 (B ^ b) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun b _ hb => ?_
        rw [Finset.mem_range] at hb
        rw [coeff_pow_eq_zero_of_lt hB b p.2 (by omega), mul_zero]
      rw [hA_ext, hB_ext, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hRHS, ← Finset.sum_product']
  symm
  rw [← Finset.sum_filter_of_ne (p := fun ab : ℕ × ℕ => ab.1 + ab.2 ≤ n)
    (fun ab _ hab => by
      by_contra hgt
      push Not at hgt
      apply hab
      have hzero : PowerSeries.coeff n (A ^ ab.1 * B ^ ab.2) = 0 := by
        rw [PowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        by_cases h1 : x.1 < ab.1
        · rw [coeff_pow_eq_zero_of_lt hA ab.1 x.1 h1, zero_mul]
        · rw [coeff_pow_eq_zero_of_lt hB ab.2 x.2 (by omega), mul_zero]
      rw [hzero, mul_zero])]
  symm
  rw [Finset.sum_sigma' (Finset.range (n + 1)) Finset.antidiagonal
    (fun _ x => (x.1.factorial : R)⁻¹ * (x.2.factorial : R)⁻¹ *
      PowerSeries.coeff n (A ^ x.1 * B ^ x.2))]
  refine Finset.sum_bij (fun s _ => s.2) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · intro s₁ hs₁ s₂ hs₂ heq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hs₁ hs₂
    have h1 : s₁.1 = s₂.1 := by rw [← hs₁.2, ← hs₂.2, heq]
    exact Sigma.ext h1 (by simpa [h1] using heq)
  · intro ab hab
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
    refine ⟨⟨ab.1 + ab.2, ab⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal, and_true]
    omega
  · intro _ _
    rfl

theorem expPS_nsmul {R : Type*} [Field R] [CharZero R] {A : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 0) (m : ℕ) :
    expPS ((m : R) • A) = (expPS A) ^ m := by
  induction m with
  | zero => simp [expPS_zero]
  | succ m ih =>
    have hsmul : ((m + 1 : ℕ) : R) • A = (m : R) • A + A := by
      rw [Nat.cast_succ, add_smul, one_smul]
    have hm0 : PowerSeries.constantCoeff ((m : R) • A) = 0 := by
      rw [PowerSeries.constantCoeff_smul, hA, smul_zero]
    rw [hsmul, expPS_add hm0 hA, ih, pow_succ]

theorem expPS_neg_mul {R : Type*} [Field R] [CharZero R] {A : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 0) :
    expPS (-A) * expPS A = 1 := by
  have hneg : PowerSeries.constantCoeff (-A) = 0 := by rw [map_neg, hA, neg_zero]
  rw [← expPS_add hneg hA, neg_add_cancel, expPS_zero]

theorem frobPS_expPS {R : Type*} [Field R] [CharZero R] (p : ℕ) (hp : 0 < p) {A : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 0) :
    frobPS p hp (expPS A) = expPS (frobPS p hp A) := by
  have hfA : PowerSeries.constantCoeff (frobPS p hp A) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_frobPS, if_pos (dvd_zero p),
      Nat.zero_div, PowerSeries.coeff_zero_eq_constantCoeff, hA]
  ext n
  rw [coeff_frobPS, coeff_expPS_eq_sum hfA n]
  split_ifs with hdiv
  · rw [coeff_expPS_eq_sum hA (n / p)]
    have hsub : Finset.range (n / p + 1) ⊆ Finset.range (n + 1) :=
      Finset.range_mono (Nat.succ_le_succ (Nat.div_le_self n p))
    rw [Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_pow, coeff_frobPS, if_pos hdiv]
    · intro k _ hk
      rw [Finset.mem_range] at hk
      rw [coeff_pow_eq_zero_of_lt hA k (n / p) (by omega), mul_zero]
  · symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← map_pow, coeff_frobPS, if_neg hdiv, mul_zero]

theorem map_expPS {R S : Type*} [Field R] [CharZero R] [Field S] [CharZero S]
    (φ : R →+* S) {A : PowerSeries R} (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.map φ (expPS A) = expPS (PowerSeries.map φ A) := by
  have hφA : PowerSeries.constantCoeff (PowerSeries.map φ A) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA, map_zero]
  ext n
  rw [PowerSeries.coeff_map, coeff_expPS_eq_sum hA n, coeff_expPS_eq_sum hφA n, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_inv₀, map_natCast, ← PowerSeries.coeff_map, map_pow]

theorem coeff_expPS_C_mul_X {R : Type*} [Field R] [CharZero R] (c : R) (n : ℕ) :
    PowerSeries.coeff n (expPS (PowerSeries.C c * PowerSeries.X)) =
      (n.factorial : R)⁻¹ * c ^ n := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C c * PowerSeries.X) = 0 := by simp
  rw [coeff_expPS_eq_sum h0 n, Finset.sum_eq_single n]
  · rw [mul_pow, ← map_pow, PowerSeries.coeff_C_mul_X_pow, if_pos rfl]
  · intro k _ hkn
    rw [mul_pow, ← map_pow, PowerSeries.coeff_C_mul_X_pow, if_neg hkn.symm, mul_zero]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

/-- Artin–Hasse exponent series `A_p(X) = ∑_{m ≥ 0} X^{p^m} / p^m`. -/
def artinHasseArg (R : Type*) [Field R] (p : ℕ) : PowerSeries R :=
  open Classical in
  PowerSeries.mk fun n => if ∃ m : ℕ, n = p ^ m then (n : R)⁻¹ else 0

/-- **Artin–Hasse Exponential Series** `E_p(X) = exp(∑_{m ≥ 0} X^{p^m} / p^m)`. -/
def artinHasseExp (R : Type*) [Field R] [CharZero R] (p : ℕ) : PowerSeries R :=
  expPS (artinHasseArg R p)

theorem constantCoeff_artinHasseArg {R : Type*} [Field R] {p : ℕ} (hp : p.Prime) :
    PowerSeries.constantCoeff (artinHasseArg R p) = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [artinHasseArg, PowerSeries.coeff_mk]
  rw [if_neg]
  rintro ⟨m, hm⟩
  exact absurd hm.symm (pow_ne_zero m hp.ne_zero)

theorem constantCoeff_artinHasseExp {R : Type*} [Field R] [CharZero R] {p : ℕ} (hp : p.Prime) :
    PowerSeries.constantCoeff (artinHasseExp R p) = 1 :=
  constantCoeff_expPS (constantCoeff_artinHasseArg hp)

theorem map_artinHasseArg {R S : Type*} [Field R] [Field S] (φ : R →+* S) (p : ℕ) :
    PowerSeries.map φ (artinHasseArg R p) = artinHasseArg S p := by
  classical
  ext n
  simp only [PowerSeries.coeff_map, artinHasseArg, PowerSeries.coeff_mk]
  split_ifs
  · rw [map_inv₀, map_natCast]
  · exact map_zero φ

theorem map_artinHasseExp {R S : Type*} [Field R] [CharZero R] [Field S] [CharZero S]
    (φ : R →+* S) {p : ℕ} (hp : p.Prime) :
    PowerSeries.map φ (artinHasseExp R p) = artinHasseExp S p := by
  unfold artinHasseExp
  rw [map_expPS φ (constantCoeff_artinHasseArg hp), map_artinHasseArg]

/-- **Artin–Hasse Functional Identity on the Exponent**:
`A_p(X^p) - p A_p(X) = -p X`. -/
theorem frobPS_artinHasseArg_sub {R : Type*} [Field R] [CharZero R] {p : ℕ} (hp : p.Prime) :
    frobPS p hp.pos (artinHasseArg R p) - (p : R) • artinHasseArg R p =
      PowerSeries.C (-(p : R)) * PowerSeries.X := by
  classical
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  ext n
  rw [map_sub, coeff_frobPS, PowerSeries.coeff_smul, smul_eq_mul,
    show PowerSeries.C (-(p : R)) * PowerSeries.X =
      PowerSeries.C (-(p : R)) * PowerSeries.X ^ 1 by simp,
    PowerSeries.coeff_C_mul_X_pow]
  simp only [artinHasseArg, PowerSeries.coeff_mk]
  rcases n with _ | _ | n
  · have hno : ¬ ∃ m : ℕ, 0 = p ^ m := fun ⟨m, hm⟩ => pow_ne_zero m hp.ne_zero hm.symm
    simp [hno]
  · have hndvd : ¬ p ∣ 1 := by
      intro hd
      have := Nat.le_of_dvd one_pos hd
      have := hp.two_le
      omega
    have hex1 : ∃ m : ℕ, 1 = p ^ m := ⟨0, (pow_zero p).symm⟩
    rw [if_neg hndvd, if_pos hex1, if_pos rfl]
    simp
  · set N := n + 2 with hNdef
    rw [if_neg (by omega : N ≠ 1)]
    by_cases hex : ∃ m : ℕ, N = p ^ m
    · obtain ⟨m, hm⟩ := hex
      rcases m with _ | k
      · rw [pow_zero] at hm; omega
      · have hdiv : p ∣ N := ⟨p ^ k, by rw [hm, pow_succ']⟩
        have hquot : N / p = p ^ k := by
          rw [hm, pow_succ', Nat.mul_div_cancel_left _ hp.pos]
        have hexk : ∃ j : ℕ, N / p = p ^ j := ⟨k, hquot⟩
        rw [if_pos hdiv, if_pos hexk, if_pos ⟨k + 1, hm⟩, hquot, hm]
        push_cast
        rw [pow_succ']
        have hpk0 : (p : R) ^ k ≠ 0 := pow_ne_zero k hp0
        field_simp [hp0, hpk0]
        ring
    · rw [if_neg hex, mul_zero, sub_zero]
      split_ifs with hdiv hexq
      · obtain ⟨k, hk⟩ := hexq
        exfalso
        apply hex
        refine ⟨k + 1, ?_⟩
        rw [pow_succ', ← hk, Nat.mul_div_cancel' hdiv]
      · rfl
      · rfl

/-- **Exact Artin–Hasse Frobenius Ratio Identity**:
`E_p(X^p) / E_p(X)^p = exp(-p X)`. -/
theorem artinHasseExp_frob_ratio {K : Type*} [NormedField K] [CharZero K] {p : ℕ} (hp : p.Prime) :
    frobPS p hp.pos (artinHasseExp K p) * (invOnePS (artinHasseExp K p)) ^ p =
      expPS (PowerSeries.C (-(p : K)) * PowerSeries.X) := by
  have hA0 := constantCoeff_artinHasseArg (R := K) hp
  have hfA0 : PowerSeries.constantCoeff (frobPS p hp.pos (artinHasseArg K p)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_frobPS, if_pos (dvd_zero p),
      Nat.zero_div, PowerSeries.coeff_zero_eq_constantCoeff, hA0]
  have hE0 := constantCoeff_artinHasseExp (R := K) hp
  have hinv_eq : invOnePS (artinHasseExp K p) = expPS (-artinHasseArg K p) := by
    have hmul : expPS (-artinHasseArg K p) * artinHasseExp K p = 1 := expPS_neg_mul hA0
    calc invOnePS (artinHasseExp K p)
        = 1 * invOnePS (artinHasseExp K p) := (one_mul _).symm
      _ = (expPS (-artinHasseArg K p) * artinHasseExp K p) * invOnePS (artinHasseExp K p) := by
          rw [hmul]
      _ = expPS (-artinHasseArg K p) * (artinHasseExp K p * invOnePS (artinHasseExp K p)) :=
          mul_assoc _ _ _
      _ = expPS (-artinHasseArg K p) := by rw [mul_invOnePS hE0, mul_one]
  rw [hinv_eq]
  unfold artinHasseExp
  rw [frobPS_expPS p hp.pos hA0, ← expPS_nsmul (by rw [map_neg, hA0, neg_zero])]
  have hsmul0 : PowerSeries.constantCoeff ((p : K) • (-artinHasseArg K p)) = 0 := by
    rw [PowerSeries.constantCoeff_smul, map_neg, hA0, neg_zero, smul_zero]
  rw [← expPS_add hfA0 hsmul0]
  congr 1
  rw [smul_neg, ← sub_eq_add_neg]
  exact frobPS_artinHasseArg_sub hp

/-- `exp(-p X) ∈ 1 + p O_K[[X]]` (directly via `PAdicChainValuation.padicValNat_factorial_upper`!). -/
theorem congOneModP_expPS_neg_p_mul_X {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) :
    CongOneModP p (expPS (PowerSeries.C (-(p : K)) * PowerSeries.X)) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  constructor
  · exact constantCoeff_expPS (by simp)
  · intro n hn
    rw [coeff_expPS_C_mul_X, norm_mul, norm_inv, norm_pow, norm_neg,
      norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero n)]
    have hv := padicValNat_factorial_upper hp (by omega : n ≠ 0)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hv_le : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) - 1 :=
      hv.trans (div_le_self (by linarith) (by linarith))
    rw [← Real.rpow_natCast ‖(p : K)‖ (padicValNat p n.factorial), ← Real.rpow_neg hpi0.le,
      ← Real.rpow_natCast ‖(p : K)‖ n, ← Real.rpow_add hpi0]
    calc ‖(p : K)‖ ^ (-(padicValNat p n.factorial : ℝ) + (n : ℝ))
        ≤ ‖(p : K)‖ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by linarith)
      _ = ‖(p : K)‖ := Real.rpow_one _

/-- **Artin–Hasse Integrality over `ℚ_[p]` (`E_p(X) ∈ ℤ_[p][[X]]`)**:
Proved directly by applying our Dieudonné–Dwork Lemma to `E_p(X^p) / E_p(X)^p = exp(-p X)`. -/
theorem artinHasseExp_isIntegral_padic (p : ℕ) [Fact p.Prime] :
    IsIntegralPS (artinHasseExp ℚ_[p] p) := by
  have hp : p.Prime := Fact.out
  have hlt : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  rw [padic_dieudonne_dwork_iff p (constantCoeff_artinHasseExp hp),
    artinHasseExp_frob_ratio hp]
  exact congOneModP_expPS_neg_p_mul_X hp hlt

/-- If `‖(q : ℚ_[p])‖ ≤ 1`, then `p` does not divide the reduced denominator `q.den`. -/
theorem not_dvd_den_of_padic_norm_le_one (p : ℕ) [Fact p.Prime] {q : ℚ}
    (hq : ‖(q : ℚ_[p])‖ ≤ 1) : ¬ p ∣ q.den := by
  have hp : p.Prime := Fact.out
  have hlt : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hpi0 : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  intro hdvd
  have hnum_ndvd : ¬ p ∣ q.num.natAbs := by
    intro h1
    have h2 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hdvd
    rw [q.reduced.gcd_eq_one] at h2
    have := Nat.le_of_dvd one_pos h2
    have := hp.two_le
    omega
  have hnum_norm : ‖(q.num : ℚ_[p])‖ = 1 := by
    have hnat : ‖((q.num.natAbs : ℕ) : ℚ_[p])‖ = 1 :=
      norm_natCast_eq_one_of_not_dvd hp hlt hnum_ndvd
    rcases Int.natAbs_eq q.num with h | h
    · conv_lhs => rw [h]
      simpa using hnat
    · conv_lhs => rw [h]
      simpa using hnat
  have hden_val : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hdvd
  have hden_lt : ‖(q.den : ℚ_[p])‖ < 1 := by
    rw [norm_natCast_eq_pow_padicValNat hp hlt q.den_nz]
    exact pow_lt_one₀ hpi0.le hlt (by omega)
  have hden_pos : 0 < ‖(q.den : ℚ_[p])‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr q.den_nz)
  have hgt : 1 < ‖(q : ℚ_[p])‖ := by
    rw [Rat.cast_def, norm_div, hnum_norm, one_div]
    exact one_lt_inv_iff₀.mpr ⟨hden_pos, hden_lt⟩
  linarith

/-- **Rational `p`-Integrality of Artin–Hasse Coefficients**:
No prime `p` divides the reduced denominator of any rational coefficient of `E_p(X) ∈ ℚ[[X]]`! -/
theorem artinHasseExp_rat_den_not_dvd {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ¬ p ∣ (PowerSeries.coeff n (artinHasseExp ℚ p)).den := by
  have : Fact p.Prime := ⟨hp⟩
  have hmap := map_artinHasseExp (Rat.castHom ℚ_[p]) hp
  have hcoeff := congrArg (PowerSeries.coeff n) hmap
  rw [PowerSeries.coeff_map] at hcoeff
  have hint := artinHasseExp_isIntegral_padic p n
  rw [← hcoeff] at hint
  exact not_dvd_den_of_padic_norm_le_one p hint

/-- **Universal Artin–Hasse Exponential Integrality**:
In EVERY ultrametric normed field `K` of characteristic `0` with `‖(p : K)‖ < 1`
(including `ℚ_[p]`, ramified extensions `ℚ_p(ϖ)`, and `ℂ_p`), every coefficient of `E_p(X)`
has norm `≤ 1`! -/
theorem artinHasseExp_isIntegral {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) :
    IsIntegralPS (artinHasseExp K p) := by
  intro n
  have hmap := map_artinHasseExp (Rat.castHom K) hp
  have hcoeff := congrArg (PowerSeries.coeff n) hmap
  rw [PowerSeries.coeff_map] at hcoeff
  rw [← hcoeff]
  set q := PowerSeries.coeff n (artinHasseExp ℚ p)
  have hndvd : ¬ p ∣ q.den := artinHasseExp_rat_den_not_dvd hp n
  change ‖(q : K)‖ ≤ 1
  rw [Rat.cast_def, norm_div, norm_natCast_eq_one_of_not_dvd hp hlt hndvd, div_one]
  exact norm_intCast_le_one q.num

/-- **Unit-Disk Analytic Convergence of the Artin–Hasse Exponential**:
In any complete ultrametric field `K`, `E_p(x) = ∑_{n ≥ 0} coeff_n(E_p) x^n` converges on the
entire open unit disk `‖x‖ < 1` (strictly extending `exp_p` beyond `r_p = ‖p‖^{1/(p-1)}`). -/
theorem artinHasse_summable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
    [CompleteSpace K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < 1) :
    Summable (fun n => PowerSeries.coeff n (artinHasseExp K p) * x ^ n) := by
  have hgeom : Summable (fun n : ℕ => ‖x‖ ^ n) := summable_geometric_of_lt_one (norm_nonneg x) hx
  refine Summable.of_norm_bounded (g := fun n => ‖x‖ ^ n) hgeom fun n => ?_
  rw [norm_mul, norm_pow]
  calc ‖PowerSeries.coeff n (artinHasseExp K p)‖ * ‖x‖ ^ n
      ≤ 1 * ‖x‖ ^ n :=
        mul_le_mul_of_nonneg_right (artinHasseExp_isIntegral hp hlt n) (pow_nonneg (norm_nonneg x) n)
    _ = ‖x‖ ^ n := one_mul _

end ArtinHasse

/-! ## Section 4: Dwork Splitting Function `θ(X) = exp(ϖ (X - X^p))` & Overconvergence -/

section DworkSplitting

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Univariate scaling endomorphism `f(X) ↦ f(ϖ X)`. -/
def scalePS {R : Type*} [CommSemiring R] (ϖ : R) : PowerSeries R →+* PowerSeries R where
  toFun f := PowerSeries.mk fun n => PowerSeries.coeff n f * ϖ ^ n
  map_one' := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · simp
  map_mul' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [← hx, pow_add]
    ring
  map_zero' := by ext n; simp
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add, add_mul]

@[simp] theorem coeff_scalePS {R : Type*} [CommSemiring R] (ϖ : R) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (scalePS ϖ f) = PowerSeries.coeff n f * ϖ ^ n := by
  simp [scalePS]

theorem scalePS_expPS {R : Type*} [Field R] [CharZero R] (ϖ : R) {A : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 0) :
    scalePS ϖ (expPS A) = expPS (scalePS ϖ A) := by
  have hsA : PowerSeries.constantCoeff (scalePS ϖ A) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_scalePS, pow_zero, mul_one,
      PowerSeries.coeff_zero_eq_constantCoeff, hA]
  ext n
  rw [coeff_scalePS, coeff_expPS_eq_sum hA n, coeff_expPS_eq_sum hsA n, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, coeff_scalePS]
  ring

/-- **Dwork Splitting Function** `θ(X) = exp(ϖ (X - X^p))`. -/
def dworkSplitting [CharZero K] (ϖ : K) (p : ℕ) : PowerSeries K :=
  expPS (PowerSeries.C ϖ * (PowerSeries.X - PowerSeries.X ^ p))

/-- Tail exponent `B_p(X) = - ∑_{m ≥ 2} (ϖ X)^{p^m} / p^m` separating `θ(X)` from `E_p(ϖ X)`. -/
def dworkTailArg (ϖ : K) (p : ℕ) : PowerSeries K :=
  open Classical in
  PowerSeries.mk fun n => if ∃ m : ℕ, 2 ≤ m ∧ n = p ^ m then -((n : K)⁻¹ * ϖ ^ n) else 0

omit [IsUltrametricDist K] in
theorem constantCoeff_dworkTailArg {p : ℕ} (hp : p.Prime) (ϖ : K) :
    PowerSeries.constantCoeff (dworkTailArg ϖ p) = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [dworkTailArg, PowerSeries.coeff_mk]
  rw [if_neg]
  rintro ⟨m, _, hm⟩
  exact pow_ne_zero m hp.ne_zero hm.symm

omit [IsUltrametricDist K] in
/-- Exact norm of a Dwork uniformizer `ϖ` satisfying `ϖ ^ (p - 1) = -p`:
`‖ϖ‖ = expRadius K p = ‖(p : K)‖ ^ (1 / (p - 1))`. -/
theorem norm_dworkPi [CharZero K] {p : ℕ} (hp : p.Prime) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    ‖ϖ‖ = expRadius K p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hnorm_pow : ‖ϖ‖ ^ (p - 1) = ‖(p : K)‖ := by
    rw [← norm_pow, hϖ, norm_neg]
  have hϖ0 : 0 ≤ ‖ϖ‖ := norm_nonneg ϖ
  unfold expRadius
  rw [← hnorm_pow, ← Real.rpow_natCast ‖ϖ‖ (p - 1), ← Real.rpow_mul hϖ0,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  have hcancel : ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1)) = 1 := mul_one_div_cancel hpos.ne'
  rw [hcancel, Real.rpow_one]

omit [IsUltrametricDist K] in
/-- **Exact Artin–Hasse / Dwork Splitting Exponent Decomposition**:
When `ϖ ^ (p - 1) = -p`, `A_p(ϖ X) + B_p(X) = ϖ (X - X^p)`. -/
theorem scalePS_artinHasseArg_add_dworkTailArg [CharZero K] {p : ℕ} (hp : p.Prime)
    {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    scalePS ϖ (artinHasseArg K p) + dworkTailArg ϖ p =
      PowerSeries.C ϖ * (PowerSeries.X - PowerSeries.X ^ p) := by
  classical
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp2 : 2 ≤ p := hp.two_le
  ext n
  rw [map_add, coeff_scalePS, mul_sub, map_sub,
    show PowerSeries.C ϖ * PowerSeries.X = PowerSeries.C ϖ * PowerSeries.X ^ 1 by simp,
    PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul_X_pow]
  simp only [artinHasseArg, dworkTailArg, PowerSeries.coeff_mk]
  by_cases hn1 : n = 1
  · subst hn1
    have h1 : ∃ m : ℕ, 1 = p ^ m := ⟨0, (pow_zero p).symm⟩
    have hno2 : ¬ ∃ m : ℕ, 2 ≤ m ∧ 1 = p ^ m := by
      rintro ⟨m, hm2, hm1⟩
      have : p ^ 2 ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm2
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    rw [if_pos h1, if_neg hno2, if_pos rfl, if_neg (by omega : (1 : ℕ) ≠ p)]
    simp
  · by_cases hnp : n = p
    · subst n
      have hp1 : ∃ m : ℕ, p = p ^ m := ⟨1, (pow_one p).symm⟩
      have hno2 : ¬ ∃ m : ℕ, 2 ≤ m ∧ p = p ^ m := by
        rintro ⟨m, hm2, hmp⟩
        have hlt : p ^ 1 < p ^ m := Nat.pow_lt_pow_right hp.one_lt (by omega)
        rw [pow_one] at hlt
        omega
      rw [if_pos hp1, if_neg hno2, if_neg hn1, if_pos rfl, add_zero, zero_sub]
      have hpow : ϖ ^ p = ϖ * ϖ ^ (p - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
      rw [hpow, hϖ]
      field_simp [hp0]
    · rw [if_neg hn1, if_neg hnp, sub_self]
      by_cases hex : ∃ m : ℕ, n = p ^ m
      · obtain ⟨m, hm⟩ := hex
        have hm2 : 2 ≤ m := by
          rcases m with _ | _ | m
          · rw [pow_zero] at hm; exact absurd hm hn1
          · rw [pow_one] at hm; exact absurd hm hnp
          · omega
        rw [if_pos ⟨m, hm⟩, if_pos ⟨m, hm2, hm⟩, add_neg_cancel]
      · have hno2 : ¬ ∃ m : ℕ, 2 ≤ m ∧ n = p ^ m := fun ⟨m, _, hm⟩ => hex ⟨m, hm⟩
        rw [if_neg hex, if_neg hno2, zero_mul, add_zero]

omit [IsUltrametricDist K] in
/-- **Exact Factorization of the Dwork Splitting Function**:
When `ϖ ^ (p - 1) = -p`, `θ(X) = E_p(ϖ X) * exp(B_p(X))`. -/
theorem dworkSplitting_eq_artinHasse_mul_tail [CharZero K] {p : ℕ} (hp : p.Prime)
    {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    dworkSplitting ϖ p = scalePS ϖ (artinHasseExp K p) * expPS (dworkTailArg ϖ p) := by
  have hA0 := constantCoeff_artinHasseArg (R := K) hp
  have hsA0 : PowerSeries.constantCoeff (scalePS ϖ (artinHasseArg K p)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_scalePS, pow_zero, mul_one,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0]
  have hB0 := constantCoeff_dworkTailArg hp ϖ
  unfold dworkSplitting artinHasseExp
  rw [scalePS_expPS ϖ hA0, ← expPS_add hsA0 hB0,
    scalePS_artinHasseArg_add_dworkTailArg hp hϖ]

/-- `wtDot` on `Unit →₀ ℕ` simplifies to `(m () : ℝ) * r`. -/
theorem wtDot_unit (m : Unit →₀ ℕ) (r : ℝ) :
    wtDot m (fun _ : Unit => r) = (m () : ℝ) * r := by
  unfold wtDot
  by_cases hm : m () = 0
  · have hm0 : m = 0 := by ext; exact hm
    subst hm0
    simp
  · have hsupp : m.support = {()} := by
      ext u
      cases u
      simp [hm]
    rw [Finsupp.sum, hsupp, Finset.sum_singleton]

/-- Sharp arithmetic inequality driving Dwork's overconvergence radius `(p - 1) / p^2`:
for all `p ≥ 2` and `m ≥ 2`, `1 + m * (p - 1) ≤ p^(m - 2) * (2 p - 1)` (equality at `m = 2`). -/
lemma dwork_exponent_nat_ineq {p : ℕ} (hp : 2 ≤ p) {m : ℕ} (hm : 2 ≤ m) :
    1 + m * (p - 1) ≤ p ^ (m - 2) * (2 * p - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_sub_cancel_left]
  induction k with
  | zero =>
    simp only [add_zero, pow_zero, one_mul]
    omega
  | succ k ih =>
    have hih := ih (by omega)
    rw [pow_succ']
    set S := p ^ k * (2 * p - 1) with hSdef
    have hge1 : 1 ≤ p ^ k := Nat.one_le_pow k p (by omega)
    have h2p : 3 ≤ 2 * p - 1 := by omega
    have hS3 : 3 ≤ S := by
      rw [hSdef]
      calc 3 = 1 * 3 := (one_mul 3).symm
        _ ≤ p ^ k * (2 * p - 1) := Nat.mul_le_mul hge1 h2p
    have hpS : p * S = S + (p - 1) * S := by
      calc p * S = (1 + (p - 1)) * S := by rw [Nat.add_sub_cancel' (by omega)]
        _ = S + (p - 1) * S := by rw [add_mul, one_mul]
    have hadd : p - 1 ≤ (p - 1) * S := Nat.le_mul_of_pos_right (p - 1) (by omega)
    have hlhs : 1 + (2 + (k + 1)) * (p - 1) = (1 + (2 + k) * (p - 1)) + (p - 1) := by ring
    rw [mul_assoc, ← hSdef, hpS, hlhs]
    omega

/-- Real-valued Dwork tail exponent bound: for every prime `p` and `m ≥ 2`,
`1 / (p - 1) + p^m * ((p - 1) / p^2) ≤ p^m / (p - 1) - m`. -/
lemma dwork_tail_exponent_bound {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 2 ≤ m) :
    1 / ((p : ℝ) - 1) + ((p : ℝ) ^ m) * (((p : ℝ) - 1) / (p : ℝ) ^ 2) ≤
      ((p : ℝ) ^ m) / ((p : ℝ) - 1) - (m : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hnat : ((1 + m * (p - 1) : ℕ) : ℝ) ≤ ((p ^ (m - 2) * (2 * p - 1) : ℕ) : ℝ) := by
    exact_mod_cast dwork_exponent_nat_ineq hp.two_le hm
  have h1p : 1 ≤ p := hp.one_le
  have h12p : 1 ≤ 2 * p := by have := hp.two_le; omega
  push_cast [Nat.cast_sub h1p, Nat.cast_sub h12p] at hnat
  have hpm : (p : ℝ) ^ m = (p : ℝ) ^ 2 * (p : ℝ) ^ (m - 2) := by
    rw [← pow_add, Nat.add_sub_of_le hm]
  have hmul : ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) *
      (1 / ((p : ℝ) - 1) + (p : ℝ) ^ m * (((p : ℝ) - 1) / (p : ℝ) ^ 2)) ≤
      ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) * ((p : ℝ) ^ m / ((p : ℝ) - 1) - (m : ℝ)) := by
    have hL : ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) *
        (1 / ((p : ℝ) - 1) + (p : ℝ) ^ m * (((p : ℝ) - 1) / (p : ℝ) ^ 2)) =
        (p : ℝ) ^ 2 + (p : ℝ) ^ m * ((p : ℝ) - 1) ^ 2 := by
      field_simp [hp0.ne', hpm1.ne']
    have hR : ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) * ((p : ℝ) ^ m / ((p : ℝ) - 1) - (m : ℝ)) =
        (p : ℝ) ^ 2 * (p : ℝ) ^ m - (m : ℝ) * (p : ℝ) ^ 2 * ((p : ℝ) - 1) := by
      field_simp [hpm1.ne']
    rw [hL, hR, hpm]
    nlinarith [sq_pos_of_pos hp0]
  exact le_of_mul_le_mul_left hmul (mul_pos (sq_pos_of_pos hp0) hpm1)

/-- The Dwork tail argument `B_p(X) = - ∑_{m ≥ 2} (ϖ X)^{p^m} / p^m` has Dwork weight
`≥ 1 / (p - 1)` at overconvergence slope `α = (p - 1) / p^2`. -/
theorem dworkTailArg_wtGe [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    WtGe ‖(p : K)‖ (fun _ : Unit => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) (1 / ((p : ℝ) - 1))
      (dworkTailArg ϖ p : MvPowerSeries Unit K) := by
  classical
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  intro n
  have hn_eq : n = Finsupp.single () (n ()) := by ext; simp
  unfold MonoWtGe
  rw [wtDot_unit]
  conv_lhs => rw [hn_eq]
  change ‖PowerSeries.coeff (n ()) (dworkTailArg ϖ p)‖ ≤ _
  simp only [dworkTailArg, PowerSeries.coeff_mk]
  split_ifs with hex
  · obtain ⟨m, hm2, hm⟩ := hex
    rw [norm_neg, norm_mul, norm_inv, norm_pow, norm_dworkPi hp hϖ, hm,
      norm_natCast_eq_pow_padicValNat hp hlt (pow_ne_zero m hp.ne_zero)]
    have hval : padicValNat p (p ^ m) = m := by
      have : Fact p.Prime := ⟨hp⟩
      exact padicValNat.prime_pow m
    rw [hval]
    unfold expRadius
    rw [← Real.rpow_natCast ‖(p : K)‖ m, ← Real.rpow_neg hpi0.le,
      ← Real.rpow_natCast (‖(p : K)‖ ^ _) (p ^ m), ← Real.rpow_mul hpi0.le,
      ← Real.rpow_add hpi0]
    refine Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le ?_
    have hbd := dwork_tail_exponent_bound hp hm2
    push_cast
    have hmul : 1 / ((p : ℝ) - 1) * (p : ℝ) ^ m = (p : ℝ) ^ m / ((p : ℝ) - 1) := by ring
    linarith
  · rw [norm_zero]
    exact Real.rpow_nonneg hpi0.le _

/-- `E_p(ϖ X)` has Dwork weight `≥ 0` at slope `(p - 1) / p^2` (since `1 / (p - 1) > (p - 1) / p^2`). -/
theorem scalePS_artinHasseExp_wtGe [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    WtGe ‖(p : K)‖ (fun _ : Unit => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
      (scalePS ϖ (artinHasseExp K p) : MvPowerSeries Unit K) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hslope : ((p : ℝ) - 1) / (p : ℝ) ^ 2 ≤ 1 / ((p : ℝ) - 1) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hp0) hpm1]
    nlinarith
  intro n
  have hn_eq : n = Finsupp.single () (n ()) := by ext; simp
  unfold MonoWtGe
  rw [wtDot_unit]
  conv_lhs => rw [hn_eq]
  change ‖PowerSeries.coeff (n ()) (scalePS ϖ (artinHasseExp K p))‖ ≤ _
  rw [coeff_scalePS, norm_mul, norm_pow, norm_dworkPi hp hϖ]
  unfold expRadius
  calc ‖PowerSeries.coeff (n ()) (artinHasseExp K p)‖ *
        (‖(p : K)‖ ^ (1 / ((p : ℝ) - 1))) ^ n ()
      ≤ 1 * (‖(p : K)‖ ^ (1 / ((p : ℝ) - 1))) ^ n () :=
        mul_le_mul_of_nonneg_right (artinHasseExp_isIntegral hp hlt (n ()))
          (pow_nonneg (Real.rpow_nonneg hpi0.le _) _)
    _ = ‖(p : K)‖ ^ ((n () : ℝ) * (1 / ((p : ℝ) - 1))) := by
        rw [one_mul, ← Real.rpow_natCast (‖(p : K)‖ ^ _), ← Real.rpow_mul hpi0.le, mul_comm]
    _ ≤ ‖(p : K)‖ ^ (0 - (n () : ℝ) * -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        have hnn : (0 : ℝ) ≤ (n () : ℝ) := Nat.cast_nonneg _
        nlinarith

/-- **Dwork Splitting Function Weight Theorem** (built directly on
`PAdicChainValuation.dwork_exp_weight_le` and `PAdicChainValuation.multiplicative_weight_le`!):
`θ(X) = exp(ϖ (X - X^p))` has Dwork weight `≥ 0` at slope `(p - 1) / p^2`. -/
theorem dworkSplitting_wtGe [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    WtGe ‖(p : K)‖ (fun _ : Unit => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
      (dworkSplitting ϖ p : MvPowerSeries Unit K) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hB_exp : WtGe ‖(p : K)‖ (fun _ : Unit => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) 0
      (expPS (dworkTailArg ϖ p) : MvPowerSeries Unit K) := fun κ =>
    dwork_exp_weight_le hp hlt (constantCoeff_dworkTailArg hp ϖ)
      (fun m _ => dworkTailArg_wtGe hp hlt hϖ m) κ le_rfl
  rw [dworkSplitting_eq_artinHasse_mul_tail hp hϖ]
  intro κ
  simpa using multiplicative_weight_le hpi0
    (fun m _ => scalePS_artinHasseExp_wtGe hp hlt hϖ m)
    (fun m _ => hB_exp m) κ le_rfl

/-- **Sharp Dwork Splitting Coefficient Decay Bound**:
For any `ϖ` with `ϖ ^ (p - 1) = -p`, every `n`-th coefficient of `θ(X) = exp(ϖ (X - X^p))`
satisfies `‖coeff n (θ(X))‖ ≤ ‖(p : K)‖ ^ (n * (p - 1) / p^2)`. -/
theorem norm_coeff_dworkSplitting_le [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) (n : ℕ) :
    ‖PowerSeries.coeff n (dworkSplitting ϖ p)‖ ≤
      ‖(p : K)‖ ^ ((n : ℝ) * (((p : ℝ) - 1) / (p : ℝ) ^ 2)) := by
  have h := dworkSplitting_wtGe hp hlt hϖ (Finsupp.single () n)
  unfold MonoWtGe at h
  rw [wtDot_unit, Finsupp.single_eq_same] at h
  simpa [sub_neg_eq_add] using h

/-- **Dwork Overconvergence Radius** `R_Dwork(K, p) = ‖(p : K)‖ ^ (-(p - 1) / p^2) > 1`. -/
def dworkOverconvRadius (K : Type*) [NormedField K] (p : ℕ) : ℝ :=
  ‖(p : K)‖ ^ (-(((p : ℝ) - 1) / (p : ℝ) ^ 2))

omit [IsUltrametricDist K] in
theorem one_lt_dworkOverconvRadius [CharZero K] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1) :
    1 < dworkOverconvRadius K p := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hexp : 0 < ((p : ℝ) - 1) / (p : ℝ) ^ 2 := div_pos hpm1 (sq_pos_of_pos hp0)
  unfold dworkOverconvRadius
  rw [Real.rpow_neg hpi0.le]
  exact one_lt_inv_iff₀.mpr ⟨Real.rpow_pos_of_pos hpi0 _, Real.rpow_lt_one hpi0.le hlt hexp⟩

end DworkSplitting

/-! ## Section 5: Crystalline Frobenius Radius Bridge to `PAdicChainValuation.WtGe` -/

section CrystallineFrobeniusRadius

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
/-- **Dwork Weight-to-Analytic-Radius Transfer (`wtGe_implies_summable_norm`)**:
If a univariate power series `f ∈ K[[X]]` satisfies `PAdicChainValuation.WtGe ‖p‖ (-α) w`,
then its evaluation series `∑' n, coeff n f * x ^ n` is norm-summable on the open disk
`‖x‖ < ‖(p : K)‖ ^ (-α)`. -/
theorem wtGe_implies_summable_norm [CharZero K] {p : ℕ} (hp : p.Prime)
    {α w : ℝ} {f : PowerSeries K}
    (hf : WtGe ‖(p : K)‖ (fun _ : Unit => -α) w (f : MvPowerSeries Unit K))
    {x : K} (hx : ‖x‖ < ‖(p : K)‖ ^ (-α)) :
    Summable (fun n => ‖PowerSeries.coeff n f * x ^ n‖) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hq0 : 0 ≤ ‖(p : K)‖ ^ α * ‖x‖ := mul_nonneg (Real.rpow_nonneg hpi0.le _) (norm_nonneg x)
  have hq1 : ‖(p : K)‖ ^ α * ‖x‖ < 1 := by
    calc ‖(p : K)‖ ^ α * ‖x‖
        < ‖(p : K)‖ ^ α * ‖(p : K)‖ ^ (-α) :=
          mul_lt_mul_of_pos_left hx (Real.rpow_pos_of_pos hpi0 _)
      _ = 1 := by rw [← Real.rpow_add hpi0, add_neg_cancel, Real.rpow_zero]
  have hgeom : Summable (fun n : ℕ => ‖(p : K)‖ ^ w * (‖(p : K)‖ ^ α * ‖x‖) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hgeom
  have hn := hf (Finsupp.single () n)
  unfold MonoWtGe at hn
  rw [wtDot_unit, Finsupp.single_eq_same] at hn
  change ‖PowerSeries.coeff n f‖ ≤ _ at hn
  rw [norm_mul, norm_pow, mul_pow, ← Real.rpow_natCast (‖(p : K)‖ ^ α),
    ← Real.rpow_mul hpi0.le, ← mul_assoc, ← Real.rpow_add hpi0]
  have hexp : w - (n : ℝ) * -α = w + α * (n : ℝ) := by ring
  rw [hexp] at hn
  exact mul_le_mul_of_nonneg_right hn (pow_nonneg (norm_nonneg x) n)

omit [IsUltrametricDist K] in
theorem wtGe_implies_summable [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    {α w : ℝ} {f : PowerSeries K}
    (hf : WtGe ‖(p : K)‖ (fun _ : Unit => -α) w (f : MvPowerSeries Unit K))
    {x : K} (hx : ‖x‖ < ‖(p : K)‖ ^ (-α)) :
    Summable (fun n => PowerSeries.coeff n f * x ^ n) :=
  (wtGe_implies_summable_norm hp hf hx).of_norm

/-- **Crystalline Frobenius Exponential Radius (`dwork_exp_crystalline_radius`)**:
If `B ∈ X K[[X]]` satisfies the Dwork threshold weight `WtGe ‖p‖ (-α) (1 / (p - 1))`,
then `exp(B)` satisfies `‖coeff n (exp B)‖ ≤ ‖(p : K)‖ ^ (n * α)` and converges analytically
on the entire open disk `‖x‖ < ‖(p : K)‖ ^ (-α)`. -/
theorem dwork_exp_crystalline_radius [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {α : ℝ} {B : PowerSeries K}
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hB : WtGe ‖(p : K)‖ (fun _ : Unit => -α) (1 / ((p : ℝ) - 1)) (B : MvPowerSeries Unit K)) :
    (∀ n : ℕ, ‖PowerSeries.coeff n (expPS B)‖ ≤ ‖(p : K)‖ ^ ((n : ℝ) * α)) ∧
      (∀ x : K, ‖x‖ < ‖(p : K)‖ ^ (-α) →
        Summable (fun n => PowerSeries.coeff n (expPS B) * x ^ n)) := by
  have hW : WtGe ‖(p : K)‖ (fun _ : Unit => -α) 0 (expPS B : MvPowerSeries Unit K) := fun κ =>
    dwork_exp_weight_le hp hlt hB0 (fun m _ => hB m) κ le_rfl
  constructor
  · intro n
    have hn := hW (Finsupp.single () n)
    unfold MonoWtGe at hn
    rw [wtDot_unit, Finsupp.single_eq_same] at hn
    simpa [sub_neg_eq_add] using hn
  · intro x hx
    exact wtGe_implies_summable hp hW hx

/-- **Overconvergence of the Dwork Splitting Function `θ(X) = exp(ϖ (X - X^p))`**:
In any complete ultrametric field `K` containing a Dwork root `ϖ ^ (p - 1) = -p`,
`θ(x) = ∑_{n ≥ 0} coeff_n(θ) x^n` converges strictly beyond the closed unit disk, for all
`‖x‖ < ‖(p : K)‖ ^ (-(p - 1) / p^2)` (`> 1`). -/
theorem dworkSplitting_summable [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K))
    {x : K} (hx : ‖x‖ < dworkOverconvRadius K p) :
    Summable (fun n => PowerSeries.coeff n (dworkSplitting ϖ p) * x ^ n) :=
  wtGe_implies_summable hp (dworkSplitting_wtGe hp hlt hϖ) hx

/-- **Convergence of Dwork's Splitting Function at `x = 1` (`θ(1) = ζ_p`)**:
Since `1 < dworkOverconvRadius K p`, the series `∑_{n ≥ 0} coeff_n(θ)` converges in `K`. -/
theorem dworkSplitting_summable_at_one [CharZero K] [CompleteSpace K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    Summable (fun n => PowerSeries.coeff n (dworkSplitting ϖ p)) := by
  have h := dworkSplitting_summable hp hlt hϖ (x := (1 : K))
    (by rw [norm_one]; exact one_lt_dworkOverconvRadius hp hlt)
  simpa using h

end CrystallineFrobeniusRadius

end

end RHDirect.Stage2DworkExp
