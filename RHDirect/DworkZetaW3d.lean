/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
Wave 3d, stages 1–2: the geometric series `∑ q^n T^n = (1 - qT)⁻¹` and its logarithm.
-/
import RHDirect.DworkZetaW3g2

/-!
# `RHDirect.DworkZetaW3d` (stages 1–2)

For `dim ≥ 1` the zeta function of `𝔸¹` over `𝔽_q` is `1/(1 - qT)`, so the first new ingredient is
the *parametrised* geometric series `geomSeq q = ∑ q^n T^n` and its logarithmic partner
`logSeries q = ∑ q^n T^n / n`.

* `one_sub_mul_geomSeq` : `(1 - qT) · geomSeq q = 1`
* `geomSeq_eq_inv`      : `geomSeq q = (1 - qT)⁻¹`
* `derivative_logSeries`: `(logSeries q)' = q · geomSeq q`
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

/-- A single-term sum of an `ite`, with a *non-constant* summand. -/
lemma sum_ite_range_single {M : Type*} [AddCommMonoid M] {N K : ℕ} (h : N < K) (f : ℕ → M) :
    ∑ k ∈ Finset.range K, (if k = N then f k else 0) = f N := by
  rw [Finset.sum_eq_single N]
  · simp
  · intro b _ hb; simp [hb]
  · intro hmem; exact absurd (Finset.mem_range.mpr h) hmem

/-- The geometric series `∑ q ^ n T ^ n`, i.e. `(1 - qT)⁻¹`. -/
def geomSeq (q : ℚ) : PowerSeries ℚ := PowerSeries.mk fun n => q ^ n

lemma coeff_geomSeq (q : ℚ) (n : ℕ) : (coeff n) (geomSeq q) = q ^ n :=
  PowerSeries.coeff_mk n _

/-- `(1 - qT) · ∑ q^n T^n = 1`. -/
theorem one_sub_mul_geomSeq (q : ℚ) :
    (1 - PowerSeries.C q * PowerSeries.X) * geomSeq q = 1 := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (coeff i) (1 - PowerSeries.C q * PowerSeries.X) * (coeff j) (geomSeq q)) n]
  rcases n with _ | m
  · simp [coeff_geomSeq]
  · have hcoeff : ∀ k : ℕ, (coeff k) (1 - PowerSeries.C q * PowerSeries.X)
        = (if k = 0 then (1 : ℚ) else 0) - (if k = 1 then q else 0) := by
      intro k
      rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
        show PowerSeries.X = PowerSeries.X ^ 1 by ring, PowerSeries.coeff_X_pow]
      by_cases h0 : k = 0
      · subst h0; simp
      · by_cases h1 : k = 1
        · subst h1; simp [h0]
        · simp [h0, h1]
    have hstep : ∀ k ∈ Finset.range (m + 1 + 1),
        (coeff k) (1 - PowerSeries.C q * PowerSeries.X) * (coeff (m + 1 - k)) (geomSeq q)
          = (if k = 0 then q ^ (m + 1 - k) else 0)
            - (if k = 1 then q * q ^ (m + 1 - k) else 0) := by
      intro k _
      rw [hcoeff k, coeff_geomSeq]
      by_cases h0 : k = 0
      · subst h0; simp
      · by_cases h1 : k = 1
        · subst h1; simp [h0]
        · simp [h0, h1]
    rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
      sum_ite_range_single (N := 0) (K := m + 1 + 1) (by omega),
      sum_ite_range_single (N := 1) (K := m + 1 + 1) (by omega)]
    rw [PowerSeries.coeff_one, if_neg (by omega), Nat.sub_zero, Nat.add_sub_cancel, pow_succ]
    ring

/-- `∑ q^n T^n` is the inverse of `1 - qT`. -/
theorem geomSeq_eq_inv (q : ℚ) :
    geomSeq q = (1 - PowerSeries.C q * PowerSeries.X)⁻¹ := by
  have h1 : constantCoeff (1 - PowerSeries.C q * PowerSeries.X : PowerSeries ℚ) = 1 := by
    rw [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, mul_zero, sub_zero]
  have hne : constantCoeff (1 - PowerSeries.C q * PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    rw [h1]; exact one_ne_zero
  have hinv : (1 - PowerSeries.C q * PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hne
  have hmul : (1 - PowerSeries.C q * PowerSeries.X) * geomSeq q = 1 := one_sub_mul_geomSeq q
  have hne' : (1 - PowerSeries.C q * PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    intro hh
    rw [hh, zero_mul] at hmul
    exact zero_ne_one hmul
  exact mul_left_cancel₀ hne' (hmul.trans hinv.symm)

/-- `∑ q ^ n T ^ n / n`: the logarithm of the geometric series. -/
def logSeries (q : ℚ) : PowerSeries ℚ := PowerSeries.mk fun n => q ^ n / n

lemma coeff_logSeries (q : ℚ) (n : ℕ) : (coeff n) (logSeries q) = q ^ n / n :=
  PowerSeries.coeff_mk n _

theorem derivative_logSeries (q : ℚ) :
    (d⁄dX ℚ) (logSeries q) = PowerSeries.C q * geomSeq q := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_logSeries, PowerSeries.coeff_C_mul, coeff_geomSeq]
  have hc : ((n + 1 : ℕ) : ℚ) = ((n : ℚ) + 1) := by push_cast; ring
  rw [hc, div_mul_cancel₀ _ (by positivity : ((n : ℚ) + 1) ≠ 0), pow_succ']

/-- `logSeries q` is `-log(1 - qT)`. -/
theorem logSeries_eq_neg_logOf (q : ℚ) :
    logSeries q = -PowerSeries.logOf (1 - PowerSeries.C q * PowerSeries.X) := by
  have h1 : constantCoeff (1 - PowerSeries.C q * PowerSeries.X : PowerSeries ℚ) = 1 := by
    rw [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, mul_zero, sub_zero]
  have hderiv : (d⁄dX ℚ) (1 - PowerSeries.C q * PowerSeries.X : PowerSeries ℚ)
      = -PowerSeries.C q := by
    rw [map_sub, PowerSeries.derivative_one, zero_sub, Derivation.leibniz,
      PowerSeries.derivative_C, PowerSeries.derivative_X]
    simp
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [derivative_logSeries, map_neg, deriv_logOf h1, hderiv, geomSeq_eq_inv]
    ring
  · rw [map_neg, PowerSeries.constantCoeff_logOf h1, neg_zero,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_logSeries]
    simp

/-- **`exp (logSeries q) = geomSeq q`**, i.e. `exp(∑ q^n T^n/n) = 1/(1 - qT)`. -/
theorem expSeries_logSeries (q : ℚ) : expSeries (logSeries q) = geomSeq q := by
  have h1 : constantCoeff (1 - PowerSeries.C q * PowerSeries.X : PowerSeries ℚ) = 1 := by
    rw [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, mul_zero, sub_zero]
  rw [logSeries_eq_neg_logOf, expSeries_neg_logOf h1]
  exact (geomSeq_eq_inv q).symm

/-! ## The zeta function of a point-count sequence -/

/-- The Hasse–Weil zeta function attached to a point-count sequence `N`: `exp(∑ N m · T^m / m)`. -/
def zetaSeq (N : ℕ → ℚ) : PowerSeries ℚ :=
  expSeries (PowerSeries.mk fun n => N n / n)

lemma constantCoeff_zetaSeqArg (N : ℕ → ℚ) :
    constantCoeff (PowerSeries.mk fun n => N n / n : PowerSeries ℚ) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk]
  simp

theorem zetaSeq_add (N₁ N₂ : ℕ → ℚ) :
    zetaSeq (N₁ + N₂) = zetaSeq N₁ * zetaSeq N₂ := by
  unfold zetaSeq
  have hmk : (PowerSeries.mk fun n => (N₁ + N₂) n / n : PowerSeries ℚ)
      = PowerSeries.mk (fun n => N₁ n / n) + PowerSeries.mk (fun n => N₂ n / n) := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add, Pi.add_apply]
    rw [add_div]
  rw [hmk, expSeries_add (constantCoeff_zetaSeqArg N₁) (constantCoeff_zetaSeqArg N₂)]

theorem zetaSeq_neg (N : ℕ → ℚ) : zetaSeq (-N) = (zetaSeq N)⁻¹ := by
  unfold zetaSeq
  have hmk : (PowerSeries.mk fun n => (-N) n / n : PowerSeries ℚ)
      = -(PowerSeries.mk fun n => N n / n) := by
    ext n
    simp only [PowerSeries.coeff_mk, Pi.neg_apply, map_neg]
    ring
  rw [hmk, expSeries_neg (constantCoeff_zetaSeqArg N)]

theorem zetaSeq_sub (N₁ N₂ : ℕ → ℚ) :
    zetaSeq (N₁ - N₂) = zetaSeq N₁ * (zetaSeq N₂)⁻¹ := by
  rw [sub_eq_add_neg, zetaSeq_add, zetaSeq_neg]

/-- **`Z(𝔸¹/𝔽_q, T) = 1/(1 - qT)`**: the point count is `N_m = q ^ m`. -/
theorem zeta_affine_line (q : ℚ) :
    zetaSeq (fun m => q ^ m) = geomSeq q :=
  expSeries_logSeries q

lemma zetaSeq_one : zetaSeq (fun _ => (1 : ℚ)) = geomSeq 1 := by
  simpa using zeta_affine_line 1

/-- **`Z(ℙ¹/𝔽_q, T) = 1/((1 - T)(1 - qT))`**: the point count is `N_m = q ^ m + 1`. -/
theorem zeta_projective_line (q : ℚ) :
    zetaSeq (fun m => q ^ m + 1) = geomSeq q * geomSeq 1 := by
  have h : (fun m => q ^ m + 1) = (fun m => q ^ m) + (fun _ => (1 : ℚ)) := by
    funext m; simp
  rw [h, zetaSeq_add, zeta_affine_line, zetaSeq_one]

/-- **`Z(𝔾_m/𝔽_q, T) = (1 - T)/(1 - qT)`**: the point count is `N_m = q ^ m - 1`. -/
theorem zeta_mult_group (q : ℚ) :
    zetaSeq (fun m => q ^ m - 1) = geomSeq q * (geomSeq 1)⁻¹ := by
  have h : (fun m => q ^ m - 1) = (fun m => q ^ m) - (fun _ => (1 : ℚ)) := by
    funext m; simp
  rw [h, zetaSeq_sub, zeta_affine_line, zetaSeq_one]

/-! ## Rationality, explicitly -/

lemma geomSeq_mul_one_sub (r : ℚ) :
    geomSeq r * (1 - PowerSeries.C r * PowerSeries.X) = 1 := by
  rw [geomSeq_eq_inv]
  refine PowerSeries.inv_mul_cancel _ ?_
  rw [show constantCoeff (1 - PowerSeries.C r * PowerSeries.X : PowerSeries ℚ) = 1 from by
    rw [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, mul_zero, sub_zero]]
  exact one_ne_zero

lemma one_sub_C_one_mul_X : (1 - PowerSeries.C (1 : ℚ) * PowerSeries.X : PowerSeries ℚ)
    = 1 - PowerSeries.X := by
  rw [map_one, one_mul]

/-- **`Z(ℙ¹, T) · (1 - T)(1 - qT) = 1`** — rationality with explicit numerator `1`. -/
theorem zeta_projective_line_den (q : ℚ) :
    zetaSeq (fun m => q ^ m + 1)
      * ((1 - PowerSeries.C q * PowerSeries.X) * (1 - PowerSeries.X)) = 1 := by
  have h1 : geomSeq (1 : ℚ) * (1 - PowerSeries.X) = 1 := by
    rw [← one_sub_C_one_mul_X]
    exact geomSeq_mul_one_sub 1
  calc zetaSeq (fun m => q ^ m + 1)
        * ((1 - PowerSeries.C q * PowerSeries.X) * (1 - PowerSeries.X))
      = (geomSeq q * geomSeq (1 : ℚ))
        * ((1 - PowerSeries.C q * PowerSeries.X) * (1 - PowerSeries.X)) := by
        rw [zeta_projective_line]
    _ = (geomSeq q * (1 - PowerSeries.C q * PowerSeries.X))
        * (geomSeq (1 : ℚ) * (1 - PowerSeries.X)) := by ring
    _ = 1 * 1 := by rw [geomSeq_mul_one_sub, h1]
    _ = 1 := one_mul 1

/-- **`Z(𝔾_m, T) · (1 - qT) = 1 - T`** — rationality with numerator `1 - T`. -/
theorem zeta_mult_group_den (q : ℚ) :
    zetaSeq (fun m => q ^ m - 1) * (1 - PowerSeries.C q * PowerSeries.X) = 1 - PowerSeries.X := by
  have hinv : (geomSeq (1 : ℚ))⁻¹ = (1 - PowerSeries.X) := by
    rw [geomSeq_eq_inv, one_sub_C_one_mul_X, eq_comm,
      PowerSeries.eq_inv_iff_mul_eq_one]
    · exact PowerSeries.mul_inv_cancel _ (by
        rw [show constantCoeff (1 - PowerSeries.X : PowerSeries ℚ) = 1 from by
          rw [map_sub, map_one, PowerSeries.constantCoeff_X, sub_zero]]
        exact one_ne_zero)
    · rw [PowerSeries.constantCoeff_inv]
      simp
  rw [zeta_mult_group, hinv]
  calc (geomSeq q * (1 - PowerSeries.X)) * (1 - PowerSeries.C q * PowerSeries.X)
      = (geomSeq q * (1 - PowerSeries.C q * PowerSeries.X)) * (1 - PowerSeries.X) := by ring
    _ = 1 * (1 - PowerSeries.X) := by rw [geomSeq_mul_one_sub]
    _ = 1 - PowerSeries.X := one_mul _

end

end HasseWeil
end RHDirect
