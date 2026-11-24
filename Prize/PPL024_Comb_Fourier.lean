import Prize.PPL024_Comb_Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Prize.PPL024_Comb_Fourier

Formalization of Bloom's Fourier-analytic / circle-method criterion (`Proposition 2` /
`prop-fourier` of `arXiv:2112.03726`, used in `Proposition 1` of `arXiv:2305.02689`).

Given a finite set `A ⊆ [M, N]` with `R(A) ∈ [2/k - 1/M, 2/k)`, `k ∣ [A]`,
every prime power `q ∈ 𝒬_A` bounded by `c * min(M/k, η M K² / (N² (log N)²))`,
and Bloom's interval-divisibility hypothesis on intervals of length `K`,
there exists a subset `S ⊆ A` with `R(S) = 1 / k`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Finset Filter Topology Complex
open scoped BigOperators Classical

namespace Prize.PPL024

/-! ## Section 1: Additive Character `e(x) = exp(2π i x)` and Cosine Bounds -/

/-- The additive character `e(x) = exp(2π i x)`. -/
def eChar (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * x)

lemma eChar_zero : eChar 0 = 1 := by
  simp [eChar]

lemma eChar_add (x y : ℝ) : eChar (x + y) = eChar x * eChar y := by
  unfold eChar
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

lemma eChar_int (m : ℤ) : eChar (m : ℝ) = 1 := by
  unfold eChar
  have h : (2 : ℂ) * Real.pi * Complex.I * (m : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [Complex.ofReal_intCast, h]
  exact Complex.exp_int_mul_two_pi_mul_I m

lemma eChar_add_int (x : ℝ) (m : ℤ) : eChar (x + (m : ℝ)) = eChar x := by
  rw [eChar_add, eChar_int, mul_one]

lemma eChar_mul_eq_pow (x : ℝ) (h : ℤ) : eChar ((h : ℝ) * x) = (eChar x) ^ h := by
  unfold eChar
  rw [← Complex.exp_int_mul]
  congr 1; push_cast; ring

lemma eChar_re (x : ℝ) : (eChar x).re = Real.cos (2 * Real.pi * x) := by
  unfold eChar
  rw [show (2 : ℂ) * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re (2 * Real.pi * x)

lemma norm_eChar (x : ℝ) : ‖eChar x‖ = 1 := by
  unfold eChar
  rw [show (2 : ℂ) * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

/-- Fundamental identity `1 + e(θ) = (2 cos(π θ)) * e(θ / 2)`. -/
lemma one_add_eChar (θ : ℝ) :
    1 + eChar θ = ((2 * Real.cos (Real.pi * θ) : ℝ) : ℂ) * eChar (θ / 2) := by
  have h1 : eChar (θ / 2) + eChar (-(θ / 2)) = ((2 * Real.cos (Real.pi * θ) : ℝ) : ℂ) := by
    unfold eChar
    have ha : (2 : ℂ) * Real.pi * Complex.I * ((θ / 2 : ℝ) : ℂ) =
        ((Real.pi * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hb : (2 : ℂ) * Real.pi * Complex.I * ((-(θ / 2) : ℝ) : ℂ) =
        -((Real.pi * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [ha, hb, Complex.exp_mul_I, show -((Real.pi * θ : ℝ) : ℂ) * Complex.I =
      ((-(Real.pi * θ) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
    push_cast; ring
  have h2 : (eChar (θ / 2) + eChar (-(θ / 2))) * eChar (θ / 2) = 1 + eChar θ := by
    rw [add_mul, ← eChar_add, ← eChar_add]
    have hsum1 : θ / 2 + θ / 2 = θ := by ring
    have hsum2 : -(θ / 2) + θ / 2 = 0 := by ring
    rw [hsum1, hsum2, eChar_zero, add_comm]
  rw [← h1, h2]

lemma norm_one_add_eChar (θ : ℝ) :
    ‖1 + eChar θ‖ = 2 * |Real.cos (Real.pi * θ)| := by
  rw [one_add_eChar, norm_mul, norm_eChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma one_add_eChar_half_int_nonneg (m : ℤ) :
    (1 + eChar ((m : ℝ) / 2)).im = 0 ∧ 0 ≤ (1 + eChar ((m : ℝ) / 2)).re := by
  have hsq : (eChar ((m : ℝ) / 2)) ^ 2 = 1 := by
    rw [sq, ← eChar_add, show (m : ℝ) / 2 + (m : ℝ) / 2 = (m : ℝ) by ring, eChar_int]
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · rw [h1]; norm_num
  · rw [h1]; norm_num

lemma prod_one_add_eChar (A : Finset ℕ) (t : ℝ) :
    ∏ n ∈ A, (1 + eChar (t / (n : ℝ))) =
      ((2 : ℝ) ^ A.card * ∏ n ∈ A, Real.cos (Real.pi * (t / (n : ℝ))) : ℝ) *
        eChar ((t / 2) * recSumReal A) := by
  have hprod : ∏ n ∈ A, (1 + eChar (t / (n : ℝ))) =
      ∏ n ∈ A, (((2 * Real.cos (Real.pi * (t / (n : ℝ))) : ℝ) : ℂ) * eChar ((t / (n : ℝ)) / 2)) :=
    Finset.prod_congr rfl fun n _ => one_add_eChar (t / (n : ℝ))
  rw [hprod, Finset.prod_mul_distrib]
  have hleft : ∏ n ∈ A, ((2 * Real.cos (Real.pi * (t / (n : ℝ))) : ℝ) : ℂ) =
      (((2 : ℝ) ^ A.card * ∏ n ∈ A, Real.cos (Real.pi * (t / (n : ℝ))) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const]
  have hright : ∏ n ∈ A, eChar ((t / (n : ℝ)) / 2) = eChar ((t / 2) * recSumReal A) := by
    unfold recSumReal
    rw [Finset.mul_sum]
    clear hprod hleft
    induction A using Finset.induction with
    | empty => simp [eChar_zero]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, eChar_add, ih]
      congr 2; ring
  rw [hleft, hright]

lemma prod_one_add_eChar_re (A : Finset ℕ) (t : ℝ) :
    (∏ n ∈ A, (1 + eChar (t / (n : ℝ)))).re =
      (2 : ℝ) ^ A.card * (∏ n ∈ A, Real.cos (Real.pi * (t / (n : ℝ)))) *
        Real.cos (Real.pi * t * recSumReal A) := by
  rw [prod_one_add_eChar, Complex.re_ofReal_mul, eChar_re]
  have harg : 2 * Real.pi * ((t / 2) * recSumReal A) = Real.pi * t * recSumReal A := by ring
  rw [harg]

/-- `sin(t) ≥ (2 / π) * t` for `t ∈ [0, π / 2]`. -/
lemma mul_le_sin_on_Icc {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi / 2) :
    2 / Real.pi * t ≤ Real.sin t :=
  Real.mul_le_sin ht0 ht1

/-- For `x ∈ [0, 1/2]`, `cos(π x) ≤ exp(-x^2)`. -/
lemma cos_pi_le_exp_neg_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.cos (Real.pi * x) ≤ Real.exp (-x ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 ≤ Real.pi * x / 2 := by positivity
  have ht1 : Real.pi * x / 2 ≤ Real.pi / 2 := by nlinarith
  have hsin : x ≤ Real.sin (Real.pi * x / 2) := by
    have h := mul_le_sin_on_Icc ht0 ht1
    have heq : 2 / Real.pi * (Real.pi * x / 2) = x := by field_simp [hpi.ne']
    linarith
  have hcos_eq : Real.cos (Real.pi * x) = 1 - 2 * (Real.sin (Real.pi * x / 2)) ^ 2 := by
    have h := Real.cos_two_mul' (Real.pi * x / 2)
    have harg : 2 * (Real.pi * x / 2) = Real.pi * x := by ring
    rw [harg] at h
    have hpyth := Real.sin_sq_add_cos_sq (Real.pi * x / 2)
    linarith
  have hsq : x ^ 2 ≤ (Real.sin (Real.pi * x / 2)) ^ 2 := by nlinarith
  have h1 : Real.cos (Real.pi * x) ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg x]
  have h2 : 1 - x ^ 2 ≤ Real.exp (-x ^ 2) := by
    linarith [Real.add_one_le_exp (-x ^ 2)]
  linarith

/-- Nearest residue modulo `n > 0`: `a = m * n + r` with `|r| ≤ n / 2`. -/
lemma exists_nearest_mod (a : ℤ) {n : ℕ} (hn : 0 < n) :
    ∃ m r : ℤ, a = m * (n : ℤ) + r ∧ |(r : ℝ)| ≤ (n : ℝ) / 2 := by
  have hnZ : (0 : ℤ) < (n : ℤ) := Nat.cast_pos.mpr hn
  set q : ℤ := a / (n : ℤ)
  set rem : ℤ := a % (n : ℤ)
  have hdiv : (n : ℤ) * q + rem = a := Int.mul_ediv_add_emod a (n : ℤ)
  have hrem0 : 0 ≤ rem := Int.emod_nonneg a hnZ.ne'
  have hrem_lt : rem < (n : ℤ) := Int.emod_lt_of_pos a hnZ
  by_cases hle : 2 * rem ≤ (n : ℤ)
  · refine ⟨q, rem, by linarith, ?_⟩
    rw [abs_of_nonneg (by exact_mod_cast hrem0)]
    have hleR : (2 : ℝ) * (rem : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
    linarith
  · refine ⟨q + 1, rem - (n : ℤ), by ring_nf; linarith, ?_⟩
    have hneg : rem - (n : ℤ) ≤ 0 := by omega
    rw [abs_of_nonpos (by exact_mod_cast hneg)]
    have hgtR : (n : ℝ) < (2 : ℝ) * (rem : ℝ) := by exact_mod_cast (by omega : (n : ℤ) < 2 * rem)
    push_cast
    linarith

/-- Cosine exponential decay at a nearest residue `a = m * n + r` with `|r| ≤ n / 2`. -/
lemma abs_cos_pi_div_le_exp {a m r : ℤ} {n : ℕ} (hn : 0 < n)
    (heq : a = m * (n : ℤ) + r) (hr : |(r : ℝ)| ≤ (n : ℝ) / 2) :
    |Real.cos (Real.pi * (a : ℝ) / (n : ℝ))| ≤ Real.exp (-((r : ℝ) / (n : ℝ)) ^ 2) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsplit : Real.pi * (a : ℝ) / (n : ℝ) = Real.pi * ((r : ℝ) / (n : ℝ)) + (m : ℤ) * Real.pi := by
    have haR : (a : ℝ) = (m : ℝ) * (n : ℝ) + (r : ℝ) := by exact_mod_cast heq
    rw [haR]; field_simp [hnR.ne']; ring
  rw [hsplit, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  set x : ℝ := |(r : ℝ)| / (n : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    dsimp only [x]
    rw [div_le_div_iff₀ hnR (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hcos_eq : |Real.cos (Real.pi * ((r : ℝ) / (n : ℝ)))| = Real.cos (Real.pi * x) := by
    have heven : Real.cos (Real.pi * ((r : ℝ) / (n : ℝ))) = Real.cos (Real.pi * x) := by
      dsimp only [x]
      rcases le_or_gt 0 (r : ℝ) with hr0 | hr0
      · rw [abs_of_nonneg hr0]
      · rw [abs_of_neg hr0, show Real.pi * (-(r : ℝ) / (n : ℝ)) = -(Real.pi * ((r : ℝ) / (n : ℝ))) by ring,
          Real.cos_neg]
    rw [heven, abs_of_nonneg]
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos, hx0], by nlinarith [Real.pi_pos, hx1]⟩
  rw [hcos_eq]
  have hsq : x ^ 2 = ((r : ℝ) / (n : ℝ)) ^ 2 := by
    dsimp only [x]; rw [div_pow, sq_abs, div_pow]
  rw [← hsq]
  exact cos_pi_le_exp_neg_sq hx0 hx1

/-! ## Section 2: Discrete Fourier Orthogonality & Counting Identity -/

/-- Symmetric residue system `H(Q) = [-(Q-1)/2, Q/2] ∩ ℤ` of exact cardinality `Q`. -/
def residueRange (Q : ℕ) : Finset ℤ :=
  Finset.Icc (-(((Q - 1) / 2 : ℕ) : ℤ)) (((Q / 2 : ℕ) : ℤ))

lemma card_residueRange {Q : ℕ} (hQ : 0 < Q) : (residueRange Q).card = Q := by
  unfold residueRange
  rw [Int.card_Icc]
  omega

lemma zero_mem_residueRange {Q : ℕ} (hQ : 0 < Q) : (0 : ℤ) ∈ residueRange Q := by
  unfold residueRange
  rw [Finset.mem_Icc]
  omega

/-- Discrete Fourier orthogonality over `residueRange Q`:
`∑_{h ∈ H(Q)} e(h * a / Q) = Q` if `Q ∣ a`, else `0`. -/
lemma sum_eChar_residueRange {Q : ℕ} (hQ : 0 < Q) (a : ℤ) :
    ∑ h ∈ residueRange Q, eChar ((h : ℝ) * (a : ℝ) / (Q : ℝ)) =
      if (Q : ℤ) ∣ a then (Q : ℂ) else 0 := by
  have hQR : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have hterm : ∀ h ∈ residueRange Q, eChar ((h : ℝ) * (((Q : ℤ) * m : ℤ) : ℝ) / (Q : ℝ)) = 1 := by
      intro h _
      have heq : (h : ℝ) * (((Q : ℤ) * m : ℤ) : ℝ) / (Q : ℝ) = ((h * m : ℤ) : ℝ) := by
        push_cast; field_simp [hQR.ne']
      rw [heq, eChar_int]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_residueRange hQ]
    simp
  · set ζ : ℂ := eChar ((a : ℝ) / (Q : ℝ))
    have hζ_ne1 : ζ ≠ 1 := by
      intro h1
      dsimp only [ζ, eChar] at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have h2piI : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
        exact Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have hdiv : ((a : ℝ) / (Q : ℝ) : ℂ) = (k : ℂ) := by
        apply mul_left_cancel₀ h2piI
        calc (2 : ℂ) * Real.pi * Complex.I * ((a : ℝ) / (Q : ℝ) : ℂ)
            = (2 : ℂ) * Real.pi * Complex.I * (((a : ℝ) / (Q : ℝ) : ℝ) : ℂ) := by push_cast; rfl
          _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
          _ = (2 : ℂ) * Real.pi * Complex.I * (k : ℂ) := by ring
      have hreal : (a : ℝ) / (Q : ℝ) = (k : ℝ) := by
        have := congrArg Complex.re hdiv
        simpa using this
      have haQ : (a : ℝ) = (Q : ℝ) * (k : ℝ) := by
        rw [div_eq_iff hQR.ne'] at hreal; linarith
      have haZ : a = (Q : ℤ) * k := by exact_mod_cast haQ
      exact hdvd ⟨k, haZ⟩
    -- Use shift invariance `(ζ - 1) * ∑_{h=L}^U ζ^h = ζ^{U+1} - ζ^L = 0`!
    set L : ℤ := -(((Q - 1) / 2 : ℕ) : ℤ)
    set U : ℤ := (((Q / 2 : ℕ) : ℤ))
    have hLU : L ≤ U := by omega
    have hULQ : U + 1 - L = (Q : ℤ) := by omega
    have hterm : ∀ h : ℤ, eChar ((h : ℝ) * (a : ℝ) / (Q : ℝ)) = ζ ^ h := fun h => by
      rw [show (h : ℝ) * (a : ℝ) / (Q : ℝ) = (h : ℝ) * ((a : ℝ) / (Q : ℝ)) by ring, eChar_mul_eq_pow]
    have hS : ∑ h ∈ residueRange Q, eChar ((h : ℝ) * (a : ℝ) / (Q : ℝ)) =
        ∑ h ∈ Finset.Icc L U, ζ ^ h :=
      Finset.sum_congr rfl fun h _ => hterm h
    rw [hS]
    have hζ_ne0 : ζ ≠ 0 := Complex.exp_ne_zero _
    have hshift : ζ * ∑ h ∈ Finset.Icc L U, ζ ^ h = ∑ h ∈ Finset.Icc (L + 1) (U + 1), ζ ^ h := by
      rw [Finset.mul_sum]
      have himg : Finset.Icc (L + 1) (U + 1) = (Finset.Icc L U).image (· + 1) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_image]
        constructor
        · intro hx; exact ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
        · rintro ⟨y, hy, rfl⟩; omega
      rw [himg, Finset.sum_image (fun _ _ _ _ h => by omega)]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [zpow_add_one₀ hζ_ne0, mul_comm]
    have hdiff : ∑ h ∈ Finset.Icc (L + 1) (U + 1), ζ ^ h - ∑ h ∈ Finset.Icc L U, ζ ^ h =
        ζ ^ (U + 1) - ζ ^ L := by
      have h1 : Finset.Icc L (U + 1) = insert (U + 1) (Finset.Icc L U) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have h2 : Finset.Icc L (U + 1) = insert L (Finset.Icc (L + 1) (U + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hs1 : ∑ h ∈ Finset.Icc L (U + 1), ζ ^ h = ζ ^ (U + 1) + ∑ h ∈ Finset.Icc L U, ζ ^ h := by
        rw [h1, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      have hs2 : ∑ h ∈ Finset.Icc L (U + 1), ζ ^ h = ζ ^ L + ∑ h ∈ Finset.Icc (L + 1) (U + 1), ζ ^ h := by
        rw [h2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      linear_combination hs1 - hs2
    have hpowQ : ζ ^ (U + 1) = ζ ^ L := by
      have hQ1 : ζ ^ (Q : ℤ) = 1 := by
        rw [← eChar_mul_eq_pow]
        have : ((Q : ℤ) : ℝ) * ((a : ℝ) / (Q : ℝ)) = (a : ℝ) := by
          push_cast; field_simp [hQR.ne']
        rw [this, eChar_int]
      calc ζ ^ (U + 1) = ζ ^ ((Q : ℤ) + L) := by congr 1; omega
        _ = ζ ^ (Q : ℤ) * ζ ^ L := zpow_add₀ hζ_ne0 _ _
        _ = ζ ^ L := by rw [hQ1, one_mul]
    have hmul0 : (ζ - 1) * ∑ h ∈ Finset.Icc L U, ζ ^ h = 0 := by
      calc (ζ - 1) * ∑ h ∈ Finset.Icc L U, ζ ^ h
          = ζ * ∑ h ∈ Finset.Icc L U, ζ ^ h - ∑ h ∈ Finset.Icc L U, ζ ^ h := by ring
        _ = ζ ^ (U + 1) - ζ ^ L := by rw [hshift, hdiff]
        _ = 0 := by rw [hpowQ, sub_self]
    exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hζ_ne1)

/-- Number of subsets `S ⊆ A` such that `k * R(S)` is an integer. -/
def countIntMultiple (A : Finset ℕ) (k : ℕ) : ℕ :=
  (A.powerset.filter (fun S => ∃ m : ℤ, (k : ℚ) * recSum S = (m : ℚ))).card

/-- **Bloom's Exact Fourier Counting Identity**:
`F(A) = (1 / [A]) * ∑_{h ∈ H([A])} ∏_{n ∈ A} (1 + e(k h / n))`. -/
theorem countIntMultiple_eq_fourier (A : Finset ℕ) (h0 : ∀ n ∈ A, 0 < n) (k : ℕ) :
    let Q := lcmSet (ppowersInSet A)
    (countIntMultiple A k : ℂ) =
      (1 / (Q : ℂ)) * ∑ h ∈ residueRange Q, ∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))) := by
  intro Q
  have h0_nmem : 0 ∉ A := fun h => Nat.lt_irrefl 0 (h0 0 h)
  have hQ_eq : Q = A.lcm id := lcmSet_ppowersInSet_eq h0_nmem
  have hQ_pos : 0 < Q := lcmSet_pos fun q hq => mem_ppowersInSet_pos h0_nmem hq
  have hQ_ne : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ_pos.ne'
  have hQR_ne : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ_pos.ne'
  -- Expand the product `∏ n ∈ A, (1 + e(k h / n)) = ∑ S ∈ A.powerset, ∏ n ∈ S, e(k h / n)`
  have hexpand : ∀ h : ℤ, ∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))) =
      ∑ S ∈ A.powerset, eChar ((h : ℝ) * ((∑ n ∈ S, k * (Q / n) : ℕ) : ℝ) / (Q : ℝ)) := by
    intro h
    have h1 := Finset.prod_add (fun n : ℕ => eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))
      (fun _ : ℕ => (1 : ℂ)) A
    have hcomm : ∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))) =
        ∏ n ∈ A, (eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)) + 1) :=
      Finset.prod_congr rfl fun _ _ => add_comm _ _
    rw [hcomm, h1]
    refine Finset.sum_congr rfl fun S hS => ?_
    simp only [Finset.prod_const_one, mul_one]
    have hSA : S ⊆ A := Finset.mem_powerset.mp hS
    -- Show `∏ n ∈ S, e(k h / n) = e(h * (∑ n ∈ S, k * (Q / n)) / Q)`
    have hsum_arg : (h : ℝ) * ((∑ n ∈ S, k * (Q / n) : ℕ) : ℝ) / (Q : ℝ) =
        ∑ n ∈ S, (k : ℝ) * (h : ℝ) / (n : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnA : n ∈ A := hSA hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (h0 n hnA).ne'
      have hdvd : n ∣ Q := by rw [hQ_eq]; exact Finset.dvd_lcm hnA
      have hmul : (n : ℝ) * ((Q / n : ℕ) : ℝ) = (Q : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' hdvd
      rw [Nat.cast_mul]
      field_simp [hn0, hQR_ne]
      linear_combination (k : ℝ) * (h : ℝ) * hmul
    rw [hsum_arg]
    clear h1 hcomm hsum_arg hSA hS
    induction S using Finset.induction with
    | empty => simp [eChar_zero]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, eChar_add, ih]
  calc (countIntMultiple A k : ℂ)
      = ∑ S ∈ A.powerset, (if ∃ m : ℤ, (k : ℚ) * recSum S = (m : ℚ) then (1 : ℂ) else 0) := by
        unfold countIntMultiple
        rw [Finset.sum_boole]
    _ = ∑ S ∈ A.powerset, (if (Q : ℤ) ∣ ((∑ n ∈ S, k * (Q / n) : ℕ) : ℤ) then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        have hSA : S ⊆ A := Finset.mem_powerset.mp hS
        have hiff : (∃ m : ℤ, (k : ℚ) * recSum S = (m : ℚ)) ↔
            (Q : ℤ) ∣ ((∑ n ∈ S, k * (Q / n) : ℕ) : ℤ) := by
          have hrat : (k : ℚ) * recSum S = ((∑ n ∈ S, k * (Q / n) : ℕ) : ℚ) / (Q : ℚ) := by
            unfold recSum
            rw [Finset.mul_sum, Nat.cast_sum, Finset.sum_div]
            refine Finset.sum_congr rfl fun n hn => ?_
            have hnA : n ∈ A := hSA hn
            have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (h0 n hnA).ne'
            have hQ0 : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ_pos.ne'
            have hdvd : n ∣ Q := by rw [hQ_eq]; exact Finset.dvd_lcm hnA
            have hmul : (n : ℚ) * ((Q / n : ℕ) : ℚ) = (Q : ℚ) := by
              exact_mod_cast Nat.mul_div_cancel' hdvd
            rw [Nat.cast_mul]
            field_simp [hn0, hQ0]
            linear_combination -(k : ℚ) * hmul
          rw [hrat]
          have hQ0 : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ_pos.ne'
          constructor
          · rintro ⟨m, hm⟩
            rw [div_eq_iff hQ0] at hm
            refine ⟨m, ?_⟩
            have hcast : (((∑ n ∈ S, k * (Q / n) : ℕ) : ℤ) : ℚ) = (((Q : ℤ) * m : ℤ) : ℚ) := by
              rw [Int.cast_natCast, Int.cast_mul, Int.cast_natCast]; linarith
            exact_mod_cast hcast
          · rintro ⟨m, hm⟩
            refine ⟨m, ?_⟩
            rw [div_eq_iff hQ0]
            have hcast : (((∑ n ∈ S, k * (Q / n) : ℕ) : ℤ) : ℚ) = (((Q : ℤ) * m : ℤ) : ℚ) := by
              exact_mod_cast hm
            rw [Int.cast_natCast, Int.cast_mul, Int.cast_natCast] at hcast
            linarith
        simp only [hiff]
    _ = ∑ S ∈ A.powerset,
          (1 / (Q : ℂ)) * ∑ h ∈ residueRange Q,
            eChar ((h : ℝ) * ((∑ n ∈ S, k * (Q / n) : ℕ) : ℝ) / (Q : ℝ)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        have horth := sum_eChar_residueRange hQ_pos ((∑ n ∈ S, k * (Q / n) : ℕ) : ℤ)
        simp only [Int.cast_natCast] at horth
        rw [horth]
        split_ifs
        · field_simp [hQ_ne]
        · simp
    _ = (1 / (Q : ℂ)) * ∑ h ∈ residueRange Q, ∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun h _ => (hexpand h).symm

/-! ## Section 3: Interval Divisibility and Bloom's Fourier Criterion (`prop-fourier`) -/

/-- An integer `n` divides some integer `x` in the closed interval `[z - K/2, z + K/2]`. -/
def dividesInInterval (z : ℤ) (K : ℝ) (n : ℕ) : Prop :=
  ∃ x : ℤ, |(x : ℝ) - (z : ℝ)| ≤ K / 2 ∧ (n : ℤ) ∣ x

/-- The set `𝒟_I` of prime powers `q ∈ 𝒬_A` for which few `n ∈ A_q` miss the interval
`[z - K/2, z + K/2]`. -/
def goodPrimePowers (A : Finset ℕ) (M η K : ℝ) (z : ℤ) : Finset ℕ :=
  (ppowersInSet A).filter fun q =>
    (((exactSlice A q).filter (fun n => ¬ dividesInInterval z K n)).card : ℝ) < η * M / (q : ℝ)

/-- Bloom's cosine product `C(B; k, h) = ∏_{n ∈ B} |cos(π k h / n)|`. -/
def cosProd (B : Finset ℕ) (k : ℕ) (h : ℤ) : ℝ :=
  ∏ n ∈ B, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))|

lemma cosProd_nonneg (B : Finset ℕ) (k : ℕ) (h : ℤ) : 0 ≤ cosProd B k h :=
  Finset.prod_nonneg fun _ _ => abs_nonneg _

lemma cosProd_le_one (B : Finset ℕ) (k : ℕ) (h : ℤ) : cosProd B k h ≤ 1 :=
  Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)

/-- Exponential upper bound on `C(B; k, h)` from elements of `B` missing the interval `[kh - K/2, kh + K/2]`. -/
lemma cosProd_le_exp_of_miss {B : Finset ℕ} {N k : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ n ∈ B, 1 ≤ n ∧ n ≤ N) (h : ℤ) :
    cosProd B k h ≤
      Real.exp (-(((B.filter (fun n => ¬ dividesInInterval ((k : ℤ) * h) K n)).card : ℝ) *
        (K ^ 2 / (4 * (N : ℝ) ^ 2)))) := by
  set Bmiss := B.filter (fun n => ¬ dividesInInterval ((k : ℤ) * h) K n)
  have h1 : cosProd B k h ≤ cosProd Bmiss k h := by
    unfold cosProd
    have hsub : Bmiss ⊆ B := Finset.filter_subset _ B
    rw [← Finset.prod_sdiff hsub]
    calc (∏ n ∈ B \ Bmiss, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))|) *
          (∏ n ∈ Bmiss, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))|)
        ≤ 1 * (∏ n ∈ Bmiss, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))|) :=
          mul_le_mul_of_nonneg_right
            (Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _))
            (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = ∏ n ∈ Bmiss, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))| := one_mul _
  refine h1.trans ?_
  unfold cosProd
  calc ∏ n ∈ Bmiss, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))|
      ≤ ∏ _n ∈ Bmiss, Real.exp (-(K ^ 2 / (4 * (N : ℝ) ^ 2))) := by
        refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun n hn => ?_
        have hnB := (Finset.mem_filter.mp hn).1
        have hmiss := (Finset.mem_filter.mp hn).2
        have hn1 : 1 ≤ n := (hB n hnB).1
        have hnN : n ≤ N := (hB n hnB).2
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hnN)
        obtain ⟨m, r, heq, hr⟩ := exists_nearest_mod ((k : ℤ) * h) (by omega : 0 < n)
        have hcos := abs_cos_pi_div_le_exp (by omega : 0 < n) heq hr
        have harg : Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ) =
            Real.pi * (((k : ℤ) * h : ℤ) : ℝ) / (n : ℝ) := by push_cast; ring
        rw [harg]
        refine hcos.trans (Real.exp_le_exp.mpr ?_)
        -- Since `¬ dividesInInterval (k * h) K n`, `|r| > K / 2`!
        have hr_gt : K / 2 < |(r : ℝ)| := by
          by_contra hle
          push Not at hle
          apply hmiss
          refine ⟨m * (n : ℤ), ?_, dvd_mul_left (n : ℤ) m⟩
          have hsub : ((m * (n : ℤ) : ℤ) : ℝ) - (((k : ℤ) * h : ℤ) : ℝ) = -(r : ℝ) := by
            have : ((k : ℤ) * h : ℤ) = m * (n : ℤ) + r := heq
            have hR : (((k : ℤ) * h : ℤ) : ℝ) = ((m * (n : ℤ) : ℤ) : ℝ) + (r : ℝ) := by
              exact_mod_cast this
            linarith
          rw [hsub, abs_neg]
          exact hle
        have hdiv : K / (2 * (N : ℝ)) ≤ |(r : ℝ)| / (n : ℝ) := by
          calc K / (2 * (N : ℝ)) = (K / 2) / (N : ℝ) := by ring
            _ ≤ |(r : ℝ)| / (N : ℝ) := div_le_div_of_nonneg_right hr_gt.le hNpos.le
            _ ≤ |(r : ℝ)| / (n : ℝ) := div_le_div_of_nonneg_left (abs_nonneg _)
                (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hnN)
        have hsq : K ^ 2 / (4 * (N : ℝ) ^ 2) ≤ ((r : ℝ) / (n : ℝ)) ^ 2 := by
          have hsq1 : (K / (2 * (N : ℝ))) ^ 2 ≤ (|(r : ℝ)| / (n : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hdiv 2
          have hsq2 : (|(r : ℝ)| / (n : ℝ)) ^ 2 = ((r : ℝ) / (n : ℝ)) ^ 2 := by
            rw [div_pow, sq_abs, div_pow]
          calc K ^ 2 / (4 * (N : ℝ) ^ 2) = (K / (2 * (N : ℝ))) ^ 2 := by ring
            _ ≤ ((r : ℝ) / (n : ℝ)) ^ 2 := hsq2 ▸ hsq1
        linarith
    _ = Real.exp (-((Bmiss.card : ℝ) * (K ^ 2 / (4 * (N : ℝ) ^ 2)))) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul]
        congr 1; ring

/-- Helper: `(1 + x)^m - 1 ≤ 2 * m * x` when `0 ≤ x` and `m * x ≤ 1 / 2`. -/
private lemma one_add_pow_sub_one_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hmx : (m : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ m - 1 ≤ 2 * (m : ℝ) * x := by
  have h1 : (1 + x) ^ m ≤ Real.exp ((m : ℝ) * x) := by
    calc (1 + x) ^ m ≤ (Real.exp x) ^ m := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) m
      _ = Real.exp ((m : ℝ) * x) := by rw [← Real.exp_nat_mul]
  -- `exp(u) - 1 ≤ 2 u` for `0 ≤ u ≤ 1/2` (since `exp(u) = 1 / exp(-u) ≤ 1 / (1 - u) ≤ 1 + 2 u`)
  set u := (m : ℝ) * x
  have hu0 : 0 ≤ u := by positivity
  have hexp_le : Real.exp u ≤ 1 + 2 * u := by
    have hpos : 0 < 1 - u := by linarith
    have hinv : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    rw [Real.exp_neg] at hinv
    have hle1 : Real.exp u ≤ (1 - u)⁻¹ := by
      have := inv_anti₀ hpos hinv
      rwa [inv_inv] at this
    refine hle1.trans ?_
    rw [inv_le_comm₀ hpos (by linarith)]
    rw [← one_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **Bloom's Fourier / Circle Method Proposition (`prop-fourier`, Section 3 of `arXiv:2112.03726`)**:
There exist absolute constants `c > 0` and `N₀ : ℕ` such that for all `N ≥ N₀`,
`M ∈ [N^{3/4}, N]`, `1 ≤ k ≤ c M`, `η ∈ (0, 1)`, `K ∈ [N^{3/4}, M/2]`, and `A ⊆ [M, N]` satisfying:
1. `2 / k - 1 / M ≤ R(A) < 2 / k`,
2. `k ∣ [A]`,
3. every `q ∈ 𝒬_A` satisfies `q ≤ c * min (M / k) (η * M * K² / (N² * (log N)²))`,
4. for every `z : ℤ`, either `#{n ∈ A : ¬ dividesInInterval z K n} ≥ M / log N`,
   or there exists `x : ℤ` with `|x - z| ≤ K / 2` divisible by all `q ∈ 𝒟_I(z)`,
there exists `S ⊆ A` with `R(S) = 1 / k`. -/
theorem bloom_fourier_prop :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N →
      ∀ (M K η : ℝ) (k : ℕ) (A : Finset ℕ),
        (N : ℝ) ^ (3 / 4 : ℝ) ≤ M → M ≤ (N : ℝ) →
        1 ≤ k → (k : ℝ) ≤ c * M →
        0 < η → η < 1 →
        (N : ℝ) ^ (3 / 4 : ℝ) ≤ K → K ≤ M / 2 →
        (∀ n ∈ A, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ)) →
        2 / (k : ℝ) - 1 / M ≤ recSumReal A → recSumReal A < 2 / (k : ℝ) →
        k ∣ lcmSet (ppowersInSet A) →
        (∀ q ∈ ppowersInSet A, (q : ℝ) ≤ c * min (M / (k : ℝ))
          (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2))) →
        (∀ z : ℤ,
          M / Real.log (N : ℝ) ≤ ((A.filter (fun n => ¬ dividesInInterval z K n)).card : ℝ) ∨
          ∃ x : ℤ, |(x : ℝ) - (z : ℝ)| ≤ K / 2 ∧
            ∀ q ∈ goodPrimePowers A M η K z, (q : ℤ) ∣ x) →
        ∃ S : Finset ℕ, S ⊆ A ∧ recSum S = 1 / (k : ℚ) := by
  obtain ⟨C_lcm, hClcm_pos, hClcm⟩ := lcmSet_ppow_le_exp
  set c : ℝ := min (1 / 64) (Real.log 2 / (16 * C_lcm)) with hc_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := lt_min (by norm_num) (by positivity)
  have hc_le_64 : c ≤ 1 / 64 := min_le_left _ _
  have hc_le_lcm : c ≤ Real.log 2 / (16 * C_lcm) := min_le_right _ _
  -- Find `N₀` large enough so that `N^{1/4} / (8 * log N) ≥ 4` (since `e^4 > 8`) and `N ≥ 16`.
  have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ) / Real.log (N : ℝ)) atTop atTop := by
    have hexp : Tendsto (fun u : ℝ => Real.exp u / u) atTop atTop := by
      simpa using Real.tendsto_exp_div_pow_atTop 1
    have hcomp : Tendsto (fun N : ℕ => (1 / 4 : ℝ) * (Real.exp ((1 / 4 : ℝ) * Real.log (N : ℝ)) /
        ((1 / 4 : ℝ) * Real.log (N : ℝ)))) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num)
        (hexp.comp (Filter.Tendsto.const_mul_atTop (by norm_num)
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)))
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    rw [Real.rpow_def_of_pos hNpos, mul_comm (Real.log (N : ℝ))]
    field_simp
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop 64)
  refine ⟨c, hc_pos, max N₁ 16, fun N hN M K η k A hMN34 hMN hk1 hkM hη0 hη1 hKN34 hKM hA hRA_lo hRA_hi hkQ hq_bd h4 => ?_⟩
  have hN16 : 16 ≤ N := le_trans (le_max_right _ _) hN
  have hN_N1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_ge1 : 1 ≤ Real.log (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 3 ≤ N)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by norm_num))
      _ ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) h3
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hM_ge2 : 2 ≤ M := by
    have h1 : (2 : ℝ) ^ 4 ≤ (N : ℝ) := by exact_mod_cast hN16
    have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_natCast (2 : ℝ) 4, ← Real.rpow_mul (by positivity)] at this
      norm_num at this; exact this
    have h3 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
    linarith
  have hM_pos : 0 < M := by linarith
  have hK_pos : 0 < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hN_pos _) hKN34
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
  have hA_pos : ∀ n ∈ A, 0 < n := fun n hn => by
    have : (2 : ℝ) ≤ (n : ℝ) := le_trans hM_ge2 (hA n hn).1
    exact_mod_cast (by linarith : (0 : ℝ) < (n : ℝ))
  have h0_nmem : 0 ∉ A := fun h => Nat.lt_irrefl 0 (hA_pos 0 h)
  have hA_bounds : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N := fun n hn =>
    ⟨hA_pos n hn, by exact_mod_cast (hA n hn).2⟩
  set 𝒬 := ppowersInSet A
  set Q := lcmSet 𝒬
  have hQ_eq : Q = A.lcm id := lcmSet_ppowersInSet_eq h0_nmem
  have hQ_pos : 0 < Q := lcmSet_pos fun q hq => mem_ppowersInSet_pos h0_nmem hq
  have hQR_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ_pos
  -- Lower bound `|A| ≥ M / k ≥ 64`
  have hRA_ge : 1 / (k : ℝ) ≤ recSumReal A := by
    have h1 : 1 / M ≤ 1 / (k : ℝ) := by
      refine one_div_le_one_div_of_le hk_pos ?_
      have : c * M ≤ M := by nlinarith
      linarith
    have h2 : 2 / (k : ℝ) - 1 / (k : ℝ) = 1 / (k : ℝ) := by ring
    linarith
  have hcardA_ge : M / (k : ℝ) ≤ (A.card : ℝ) := by
    have h1 := recSumReal_le_card_div hM_pos (fun n hn => (hA n hn).1)
    rw [le_div_iff₀ hM_pos] at h1
    have h2 : M * (1 / (k : ℝ)) ≤ M * recSumReal A := mul_le_mul_of_nonneg_left hRA_ge hM_pos.le
    have : M * (1 / (k : ℝ)) = M / (k : ℝ) := by ring
    linarith
  have hcardA_ge64 : (64 : ℝ) ≤ (A.card : ℝ) := by
    have h1 : 64 ≤ M / (k : ℝ) := by
      rw [le_div_iff₀ hk_pos]
      nlinarith
    linarith
  have hAne : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0 : ℝ) < (A.card : ℝ)))
  -- Show `Q ≥ M > K`
  have hQ_ge_M : M ≤ (Q : ℝ) := by
    obtain ⟨n₀, hn₀⟩ := hAne
    have hdvd : n₀ ∣ Q := by rw [hQ_eq]; exact Finset.dvd_lcm hn₀
    have hle : n₀ ≤ Q := Nat.le_of_dvd hQ_pos hdvd
    exact le_trans (hA n₀ hn₀).1 (by exact_mod_cast hle)
  -- Define `X := c * min (M / k) (η * M * K² / (N² (log N)²))`
  set X : ℝ := c * min (M / (k : ℝ)) (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2))
  have hX_le1 : X ≤ c * (M / (k : ℝ)) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hc_pos.le
  have hX_le2 : X ≤ c * (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2)) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hc_pos.le
  -- Bound `Q ≤ exp(C_lcm * max X 2)` (note `X ≥ 2` whenever `𝒬` is nonempty since `2 ≤ q ≤ X`!)
  have hQ_le_exp : (Q : ℝ) ≤ Real.exp (C_lcm * X) := by
    by_cases h𝒬ne : 𝒬.Nonempty
    · obtain ⟨q₀, hq₀⟩ := h𝒬ne
      have hq2 : (2 : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast (mem_ppowersInSet_isPrimePow h0_nmem hq₀).two_le
      have hX2 : 2 ≤ X := hq2.trans (hq_bd q₀ hq₀)
      exact hClcm X hX2 𝒬 fun q hq => ⟨mem_ppowersInSet_isPrimePow h0_nmem hq, hq_bd q hq⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at h𝒬ne
      have hQ1 : Q = 1 := by simp [Q, h𝒬ne, lcmSet]
      rw [hQ1, Nat.cast_one]
      have hX0 : 0 ≤ X := mul_nonneg hc_pos.le (le_min (by positivity) (by positivity))
      exact Real.one_le_exp (by positivity)
  -- Step 1: It suffices to show `countIntMultiple A k > 1`!
  suffices hF_gt1 : (1 : ℝ) < (countIntMultiple A k : ℝ) by
    have hF2 : 2 ≤ countIntMultiple A k := by
      have : 1 < countIntMultiple A k := by exact_mod_cast hF_gt1
      omega
    -- `∅` is one element of the filtered powerset, so there is another `S ≠ ∅`!
    set Fset := A.powerset.filter (fun S => ∃ m : ℤ, (k : ℚ) * recSum S = (m : ℚ))
    have hemp : (∅ : Finset ℕ) ∈ Fset := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset A), 0, by simp [recSum]⟩
    have hne_sdiff : (Fset.erase ∅).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hemp]
      change 0 < countIntMultiple A k - 1
      omega
    obtain ⟨S, hS⟩ := hne_sdiff
    have hSne : S ≠ ∅ := (Finset.mem_erase.mp hS).1
    have hSF := Finset.mem_filter.mp (Finset.mem_erase.mp hS).2
    have hSA : S ⊆ A := Finset.mem_powerset.mp hSF.1
    obtain ⟨m, hm⟩ := hSF.2
    have hSpos : 0 < recSumReal S :=
      recSumReal_pos_of_nonempty (fun n hn => hA_pos n (hSA hn)) (Finset.nonempty_iff_ne_empty.mpr hSne)
    have hSle : recSumReal S < 2 / (k : ℝ) := lt_of_le_of_lt (recSumReal_mono hSA) hRA_hi
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      have hmR : (k : ℝ) * recSumReal S = (m : ℝ) := by
        rw [← recSum_cast_real]
        exact_mod_cast hm
      linarith [mul_pos hk_pos hSpos]
    have hm_lt2 : (m : ℝ) < 2 := by
      have hmR : (k : ℝ) * recSumReal S = (m : ℝ) := by
        rw [← recSum_cast_real]
        exact_mod_cast hm
      have h1 : (k : ℝ) * recSumReal S < (k : ℝ) * (2 / (k : ℝ)) :=
        mul_lt_mul_of_pos_left hSle hk_pos
      have h2 : (k : ℝ) * (2 / (k : ℝ)) = 2 := by field_simp [hk_pos.ne']
      linarith
    have hm1 : m = 1 := by
      have h0m : (0 : ℤ) < m := by exact_mod_cast hm_pos
      have hm2 : m < 2 := by exact_mod_cast hm_lt2
      omega
    subst hm1
    refine ⟨S, hSA, ?_⟩
    have hkQ0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Int.cast_one] at hm
    calc recSum S = ((k : ℚ) * recSum S) / (k : ℚ) := by field_simp [hkQ0]
      _ = 1 / (k : ℚ) := by rw [hm]
  -- Step 2: Apply the Fourier identity and take real parts!
  have hFour := congrArg Complex.re (countIntMultiple_eq_fourier A hA_pos k)
  simp only [Complex.natCast_re] at hFour
  rw [show (1 / (Q : ℂ)) = (((1 / (Q : ℝ) : ℝ) : ℂ)) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.re_sum] at hFour
  -- Partition `residueRange Q` into:
  --  - `h = 0` (contributes `2^{|A|}`),
  --  - `h = Q / 2` when `2 ∣ Q` (contributes `≥ 0`),
  --  - Major arcs `ℳ = {h ∈ J : ∃ t : ℤ, |k * h - t * Q| ≤ K / 2}` (every term has `.re ≥ 0`!),
  --  - Minor arcs `𝔪 = J \ ℳ` (each term has `.re ≥ -2^{|A|} * cosProd A k h`)!
  set J : Finset ℤ := (residueRange Q).filter (fun h => h ≠ 0 ∧ 2 * |h| < (Q : ℤ))
  set majorArc : Finset ℤ := J.filter (fun h => ∃ t : ℤ, |(k : ℝ) * (h : ℝ) - (t : ℝ) * (Q : ℝ)| ≤ K / 2)
  set minorArc : Finset ℤ := J.filter (fun h => ¬ ∃ t : ℤ, |(k : ℝ) * (h : ℝ) - (t : ℝ) * (Q : ℝ)| ≤ K / 2)
  -- Show `(∏ n ∈ A, (1 + e(k h / n))).re ≥ 0` for `h ∈ residueRange Q \ (insert 0 minorArc)`!
  have hnonneg_outside : ∀ h ∈ residueRange Q, h ≠ 0 → h ∉ minorArc →
      0 ≤ (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re := by
    intro h hH hne0 hnotm
    by_cases hJ : h ∈ J
    · -- Then `h ∈ majorArc`!
      have hmaj : ∃ t : ℤ, |(k : ℝ) * (h : ℝ) - (t : ℝ) * (Q : ℝ)| ≤ K / 2 := by
        by_contra hno
        exact hnotm (Finset.mem_filter.mpr ⟨hJ, hno⟩)
      obtain ⟨t, ht⟩ := hmaj
      obtain ⟨Q', hQ'⟩ := hkQ
      set r : ℤ := h - t * (Q' : ℤ)
      have hkr_eq : (k : ℝ) * (r : ℝ) = (k : ℝ) * (h : ℝ) - (t : ℝ) * (Q : ℝ) := by
        dsimp only [r]
        have hQR : (Q : ℝ) = (k : ℝ) * (Q' : ℝ) := by exact_mod_cast hQ'
        push_cast; rw [hQR]; ring
      have hkr_le : |(k : ℝ) * (r : ℝ)| ≤ K / 2 := by
        rw [hkr_eq]; exact ht
      -- `e(k h / n) = e(k r / n)` since `k h / n = k r / n + t * (Q / n)` and `n ∣ Q`!
      have heq_prod : ∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))) =
          ∏ n ∈ A, (1 + eChar (((k : ℝ) * (r : ℝ)) / (n : ℝ))) := by
        refine Finset.prod_congr rfl fun n hn => ?_
        congr 1
        have hdvd : n ∣ Q := by rw [hQ_eq]; exact Finset.dvd_lcm hn
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hA_pos n hn).ne'
        have hmul : (n : ℝ) * ((Q / n : ℕ) : ℝ) = (Q : ℝ) := by
          exact_mod_cast Nat.mul_div_cancel' hdvd
        have harg : (k : ℝ) * (h : ℝ) / (n : ℝ) =
            ((k : ℝ) * (r : ℝ)) / (n : ℝ) + ((t * ((Q / n : ℕ) : ℤ) : ℤ) : ℝ) := by
          have hQR : (Q : ℝ) = (k : ℝ) * (Q' : ℝ) := by exact_mod_cast hQ'
          have hrR : (r : ℝ) = (h : ℝ) - (t : ℝ) * (Q' : ℝ) := by dsimp only [r]; push_cast; ring
          rw [Int.cast_mul, Int.cast_natCast, hrR]
          field_simp [hn0]
          calc (k : ℝ) * (h : ℝ) = (k : ℝ) * ((h : ℝ) - (t : ℝ) * (Q' : ℝ)) + (t : ℝ) * ((k : ℝ) * (Q' : ℝ)) := by ring
            _ = (k : ℝ) * ((h : ℝ) - (t : ℝ) * (Q' : ℝ)) + (t : ℝ) * ((n : ℝ) * ((Q / n : ℕ) : ℝ)) := by rw [← hQR, hmul]
            _ = (k : ℝ) * ((h : ℝ) - (t : ℝ) * (Q' : ℝ)) + (n : ℝ) * (t : ℝ) * ((Q / n : ℕ) : ℝ) := by ring
        rw [harg, eChar_add_int]
      rw [heq_prod, prod_one_add_eChar_re]
      refine mul_nonneg (mul_nonneg (by positivity) ?_) ?_
      · refine Finset.prod_nonneg fun n hn => ?_
        have hnM : M ≤ (n : ℝ) := (hA n hn).1
        have hbound : |Real.pi * (((k : ℝ) * (r : ℝ)) / (n : ℝ))| ≤ Real.pi / 2 := by
          rw [abs_mul, abs_of_pos Real.pi_pos, abs_div,
            abs_of_pos (Nat.cast_pos.mpr (hA_pos n hn) : (0 : ℝ) < (n : ℝ))]
          have h1 : |((k : ℝ) * (r : ℝ))| / (n : ℝ) ≤ (K / 2) / M := by
            calc |((k : ℝ) * (r : ℝ))| / (n : ℝ)
                ≤ (K / 2) / (n : ℝ) := div_le_div_of_nonneg_right hkr_le (Nat.cast_nonneg n)
              _ ≤ (K / 2) / M := div_le_div_of_nonneg_left (by positivity) hM_pos hnM
          have h2 : (K / 2) / M ≤ 1 / 4 := by
            rw [div_le_iff₀ hM_pos]; linarith
          nlinarith [Real.pi_pos]
        exact Real.cos_nonneg_of_mem_Icc (abs_le.mp hbound)
      · -- `cos(π * (k * r) * R(A)) = cos(π * r * (2 - k * R(A))) ≥ 0`!
        set ε := 2 - (k : ℝ) * recSumReal A
        have hε0 : 0 < ε := by
          dsimp only [ε]
          have : (k : ℝ) * recSumReal A < 2 := by
            have := mul_lt_mul_of_pos_left hRA_hi hk_pos
            rwa [show (k : ℝ) * (2 / (k : ℝ)) = 2 by field_simp [hk_pos.ne']] at this
          linarith
        have hε_le : ε ≤ (k : ℝ) / M := by
          dsimp only [ε]
          have := mul_le_mul_of_nonneg_left hRA_lo hk_pos.le
          have heq : (k : ℝ) * (2 / (k : ℝ) - 1 / M) = 2 - (k : ℝ) / M := by
            field_simp [hk_pos.ne']
          linarith
        have hcos_eq : Real.cos (Real.pi * ((k : ℝ) * (r : ℝ)) * recSumReal A) =
            Real.cos (Real.pi * (r : ℝ) * ε) := by
          have harg : Real.pi * ((k : ℝ) * (r : ℝ)) * recSumReal A =
              -(Real.pi * (r : ℝ) * ε) + ((2 * r : ℤ) : ℝ) * Real.pi := by
            dsimp only [ε]; push_cast; ring
          rw [harg, Real.cos_add_int_mul_pi, Real.cos_neg]
          have heven : (-1 : ℝ) ^ (2 * r) = 1 := by
            rw [zpow_mul]; norm_num
          rw [heven, one_mul]
        rw [hcos_eq]
        have hbound : |Real.pi * (r : ℝ) * ε| ≤ Real.pi / 2 := by
          rw [show Real.pi * (r : ℝ) * ε = Real.pi * ((r : ℝ) * ε) by ring,
            abs_mul, abs_of_pos Real.pi_pos, abs_mul, abs_of_pos hε0]
          have hr_le : |(r : ℝ)| ≤ K / (2 * (k : ℝ)) := by
            rw [abs_mul, abs_of_pos hk_pos] at hkr_le
            rw [le_div_iff₀ (by positivity)]
            linarith
          have hrε : |(r : ℝ)| * ε ≤ 1 / 4 := by
            calc |(r : ℝ)| * ε ≤ (K / (2 * (k : ℝ))) * ((k : ℝ) / M) :=
                  mul_le_mul hr_le hε_le hε0.le (by positivity)
              _ = K / (2 * M) := by field_simp [hk_pos.ne']
              _ ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
          nlinarith [Real.pi_pos]
        exact Real.cos_nonneg_of_mem_Icc (abs_le.mp hbound)
    · -- Then `h ∈ residueRange Q`, `h ≠ 0`, `¬ (2 * |h| < Q)`, so `Q` is even and `h = Q / 2`!
      have hge : (Q : ℤ) ≤ 2 * |h| := by
        by_contra hlt
        push Not at hlt
        exact hJ (Finset.mem_filter.mpr ⟨hH, hne0, hlt⟩)
      have hHbounds := Finset.mem_Icc.mp hH
      have h2h : 2 * h = (Q : ℤ) := by
        rcases le_or_gt 0 h with hh0 | hh0
        · rw [abs_of_nonneg hh0] at hge; omega
        · rw [abs_of_neg hh0] at hge; omega
      -- Every factor `1 + e(k h / n)` has `.im = 0` and `.re ≥ 0`!
      have hfac : ∀ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))).im = 0 ∧
          0 ≤ (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))).re := by
        intro n hn
        have hdvd : n ∣ Q := by rw [hQ_eq]; exact Finset.dvd_lcm hn
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hA_pos n hn).ne'
        have hmul : (n : ℝ) * ((Q / n : ℕ) : ℝ) = (Q : ℝ) := by
          exact_mod_cast Nat.mul_div_cancel' hdvd
        have h2hR : 2 * (h : ℝ) = (Q : ℝ) := by exact_mod_cast h2h
        have harg : (k : ℝ) * (h : ℝ) / (n : ℝ) = (((k * (Q / n) : ℕ) : ℤ) : ℝ) / 2 := by
          rw [Int.cast_natCast, Nat.cast_mul]
          field_simp [hn0]
          linarith [h2hR, hmul]
        rw [harg]
        exact one_add_eChar_half_int_nonneg _
      have hprod_nn : ∀ B : Finset ℕ, (∀ n ∈ B, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))).im = 0 ∧
          0 ≤ (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))).re) →
          (∏ n ∈ B, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).im = 0 ∧
          0 ≤ (∏ n ∈ B, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re := by
        intro B
        induction B using Finset.induction with
        | empty => intro _; simp
        | insert a s ha ih =>
          intro hB
          rw [Finset.prod_insert ha]
          have h1 := hB a (Finset.mem_insert_self a s)
          have h2 := ih fun n hn => hB n (Finset.mem_insert_of_mem hn)
          rw [Complex.mul_im, Complex.mul_re, h1.1, h2.1]
          constructor
          · ring
          · nlinarith [h1.2, h2.2]
      exact (hprod_nn A hfac).2
  -- Step 3: Deduce `(F(A) : ℝ) ≥ (2^{|A|} / Q) * (1 - ∑_{h ∈ minorArc} cosProd A k h)`!
  have hF_lower : ((2 : ℝ) ^ A.card / (Q : ℝ)) * (1 - ∑ h ∈ minorArc, cosProd A k h) ≤
      (countIntMultiple A k : ℝ) := by
    rw [hFour]
    have h0_mem : (0 : ℤ) ∈ residueRange Q := zero_mem_residueRange hQ_pos
    have hm_sub : minorArc ⊆ residueRange Q :=
      (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have h0_nmem_m : (0 : ℤ) ∉ minorArc := fun h =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1 rfl
    have hsplit_sum : ∑ h ∈ residueRange Q, (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re =
        (∏ n ∈ A, (1 + eChar ((k : ℝ) * (0 : ℝ) / (n : ℝ)))).re +
        (∑ h ∈ minorArc, (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re) +
        (∑ h ∈ (residueRange Q \ insert 0 minorArc),
          (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re) := by
      have hins : insert (0 : ℤ) minorArc ⊆ residueRange Q :=
        Finset.insert_subset h0_mem hm_sub
      rw [← Finset.sum_sdiff hins, Finset.sum_insert h0_nmem_m]
      ring
    rw [hsplit_sum]
    have hzero_val : (∏ n ∈ A, (1 + eChar ((k : ℝ) * (0 : ℝ) / (n : ℝ)))).re = (2 : ℝ) ^ A.card := by
      have h1 : ∏ n ∈ A, (1 + eChar ((k : ℝ) * (0 : ℝ) / (n : ℝ))) = ((2 : ℝ) ^ A.card : ℂ) := by
        have : ∀ n ∈ A, 1 + eChar ((k : ℝ) * (0 : ℝ) / (n : ℝ)) = (2 : ℂ) := fun n _ => by
          simp [eChar_zero]; norm_num
        rw [Finset.prod_congr rfl this, Finset.prod_const]
        norm_cast
      rw [h1]; norm_cast
    have hrest_nn : 0 ≤ ∑ h ∈ (residueRange Q \ insert 0 minorArc),
        (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re := by
      refine Finset.sum_nonneg fun h hh => ?_
      have hh' := Finset.mem_sdiff.mp hh
      have hnot := Finset.mem_insert.not.mp hh'.2
      push Not at hnot
      exact hnonneg_outside h hh'.1 hnot.1 hnot.2
    have hminor_ge : -((2 : ℝ) ^ A.card * ∑ h ∈ minorArc, cosProd A k h) ≤
        ∑ h ∈ minorArc, (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun h _ => ?_
      have hnorm : ‖∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))‖ =
          (2 : ℝ) ^ A.card * cosProd A k h := by
        rw [norm_prod]
        have h1 : ∀ n ∈ A, ‖1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))‖ =
            2 * |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))| := fun n _ => by
          rw [norm_one_add_eChar]
          congr 2; ring
        rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const]
        rfl
      have hre_ge := neg_abs_le (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re
      have habs_le := Complex.abs_re_le_norm (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ))))
      linarith
    have htot : (2 : ℝ) ^ A.card * (1 - ∑ h ∈ minorArc, cosProd A k h) ≤
        (∏ n ∈ A, (1 + eChar ((k : ℝ) * (0 : ℝ) / (n : ℝ)))).re +
        (∑ h ∈ minorArc, (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re) +
        (∑ h ∈ (residueRange Q \ insert 0 minorArc),
          (∏ n ∈ A, (1 + eChar ((k : ℝ) * (h : ℝ) / (n : ℝ)))).re) := by
      rw [hzero_val]; linarith
    have := mul_le_mul_of_nonneg_left htot (one_div_nonneg.mpr hQR_pos.le)
    linarith [show (1 / (Q : ℝ)) * ((2 : ℝ) ^ A.card * (1 - ∑ h ∈ minorArc, cosProd A k h)) =
      ((2 : ℝ) ^ A.card / (Q : ℝ)) * (1 - ∑ h ∈ minorArc, cosProd A k h) by ring]
  -- Step 4: Bound `∑_{h ∈ minorArc} cosProd A k h ≤ 1 / 4` by splitting into `𝔪₁` and `𝔪₂`!
  set m1 := minorArc.filter (fun h =>
    M / Real.log (N : ℝ) ≤ ((A.filter (fun n => ¬ dividesInInterval ((k : ℤ) * h) K n)).card : ℝ))
  set m2 := minorArc.filter (fun h =>
    ¬ (M / Real.log (N : ℝ) ≤ ((A.filter (fun n => ¬ dividesInInterval ((k : ℤ) * h) K n)).card : ℝ)))
  have hsum_split : ∑ h ∈ minorArc, cosProd A k h =
      (∑ h ∈ m1, cosProd A k h) + (∑ h ∈ m2, cosProd A k h) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- Step 4a: Bound `∑_{h ∈ m1} cosProd A k h ≤ 1 / 8`
  have hm1_bound : ∑ h ∈ m1, cosProd A k h ≤ 1 / 8 := by
    have hcard_m1 : (m1.card : ℝ) ≤ (Q : ℝ) := by
      have hsub : m1 ⊆ residueRange Q :=
        (Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      have := Finset.card_le_card hsub
      rw [card_residueRange hQ_pos] at this
      exact_mod_cast this
    have hterm_m1 : ∀ h ∈ m1, cosProd A k h ≤
        Real.exp (-(K ^ 2 * M / (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ)))) := by
      intro h hh
      have hcond := (Finset.mem_filter.mp hh).2
      refine (cosProd_le_exp_of_miss hK_pos.le hA_bounds h).trans (Real.exp_le_exp.mpr ?_)
      have h1 : (M / Real.log (N : ℝ)) * (K ^ 2 / (4 * (N : ℝ) ^ 2)) ≤
          ((A.filter (fun n => ¬ dividesInInterval ((k : ℤ) * h) K n)).card : ℝ) *
            (K ^ 2 / (4 * (N : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcond (by positivity)
      have heq : (M / Real.log (N : ℝ)) * (K ^ 2 / (4 * (N : ℝ) ^ 2)) =
          K ^ 2 * M / (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ)) := by ring
      linarith
    calc ∑ h ∈ m1, cosProd A k h
        ≤ ∑ _h ∈ m1, Real.exp (-(K ^ 2 * M / (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ)))) :=
          Finset.sum_le_sum hterm_m1
      _ = (m1.card : ℝ) * Real.exp (-(K ^ 2 * M / (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ)))) := by simp
      _ ≤ (Q : ℝ) * Real.exp (-(K ^ 2 * M / (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ)))) := by gcongr
      _ ≤ Real.exp (C_lcm * X) * Real.exp (-(K ^ 2 * M / (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ)))) := by gcongr
      _ = Real.exp (C_lcm * X - K ^ 2 * M / (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ))) := by
          rw [← Real.exp_add]; rfl
      _ ≤ Real.exp (-4) := by
          apply Real.exp_le_exp.mpr
          -- Show `C_lcm * X ≤ (1/8) * K^2 * M / (N^2 * log N)`
          have hCX : C_lcm * X ≤ K ^ 2 * M / (8 * (N : ℝ) ^ 2 * Real.log (N : ℝ)) := by
            have hη_log : η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2) ≤
                K ^ 2 * M / ((N : ℝ) ^ 2 * Real.log (N : ℝ)) := by
              have h1 : η * M * K ^ 2 ≤ K ^ 2 * M := by
                have := mul_le_mul_of_nonneg_right hη1.le (by positivity : 0 ≤ M * K ^ 2)
                linarith
              have h2 : (N : ℝ) ^ 2 * Real.log (N : ℝ) ≤ (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2 :=
                mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg (N : ℝ))
              exact div_le_div₀ (by positivity) h1 (by positivity) h2
            have hC_c : C_lcm * c ≤ 1 / 8 := by
              have hlog2_lt1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
              have := mul_le_mul_of_nonneg_left hc_le_lcm hClcm_pos.le
              have heq : C_lcm * (Real.log 2 / (16 * C_lcm)) = Real.log 2 / 16 := by
                field_simp [hClcm_pos.ne']
              linarith
            calc C_lcm * X
                ≤ C_lcm * (c * (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2))) :=
                  mul_le_mul_of_nonneg_left hX_le2 hClcm_pos.le
              _ = (C_lcm * c) * (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2)) := by ring
              _ ≤ (1 / 8) * (K ^ 2 * M / ((N : ℝ) ^ 2 * Real.log (N : ℝ))) :=
                  mul_le_mul hC_c hη_log (by positivity) (by norm_num)
              _ = K ^ 2 * M / (8 * (N : ℝ) ^ 2 * Real.log (N : ℝ)) := by ring
          -- Show `K^2 * M / (8 * N^2 * log N) ≥ 4` (since `K^2 * M ≥ N^{9/4}`, ratio `≥ N^{1/4} / (8 * log N) ≥ 64/8 = 8 ≥ 4`!)
          have hKM_big : (4 : ℝ) ≤ K ^ 2 * M / (8 * (N : ℝ) ^ 2 * Real.log (N : ℝ)) := by
            have hpow : (N : ℝ) ^ (9 / 4 : ℝ) ≤ K ^ 2 * M := by
              have hK2 : ((N : ℝ) ^ (3 / 4 : ℝ)) ^ 2 ≤ K ^ 2 :=
                pow_le_pow_left₀ (by positivity) hKN34 2
              have hprod : ((N : ℝ) ^ (3 / 4 : ℝ)) ^ 2 * (N : ℝ) ^ (3 / 4 : ℝ) = (N : ℝ) ^ (9 / 4 : ℝ) := by
                rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hN_pos.le, ← Real.rpow_add hN_pos]
                congr 1; norm_num
              nlinarith [mul_le_mul hK2 hMN34 (by positivity) (by positivity)]
            have hpow2 : (N : ℝ) ^ (9 / 4 : ℝ) / (N : ℝ) ^ 2 = (N : ℝ) ^ (1 / 4 : ℝ) := by
              rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_sub hN_pos]
              congr 1; norm_num
            have h64 : 64 ≤ (N : ℝ) ^ (1 / 4 : ℝ) / Real.log (N : ℝ) := hN₁ N hN_N1
            calc (4 : ℝ) ≤ 64 / 8 := by norm_num
              _ ≤ ((N : ℝ) ^ (1 / 4 : ℝ) / Real.log (N : ℝ)) / 8 := by linarith
              _ = (N : ℝ) ^ (9 / 4 : ℝ) / (8 * (N : ℝ) ^ 2 * Real.log (N : ℝ)) := by
                  rw [← hpow2]; ring
              _ ≤ K ^ 2 * M / (8 * (N : ℝ) ^ 2 * Real.log (N : ℝ)) := by gcongr
          linarith [show K ^ 2 * M / (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ)) =
            2 * (K ^ 2 * M / (8 * (N : ℝ) ^ 2 * Real.log (N : ℝ))) by ring]
      _ ≤ 1 / 8 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 4) (by norm_num : (0 : ℝ) < 1 / 8)]
          have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have h2 : (16 : ℝ) ≤ Real.exp 4 := by
            calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
              _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
              _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
          linarith
  -- Step 4b: Bound `∑_{h ∈ m2} cosProd A k h ≤ 1 / 8`
  have hm2_bound : ∑ h ∈ m2, cosProd A k h ≤ 1 / 8 := by
    -- Pointwise bound on `cosProd A k h` for every `h ∈ m2`:
    -- `cosProd A k h ≤ (N : ℝ) ^ (-4 * (𝒬 \ 𝒟_h).card)`!
    set L : ℕ := ⌊Real.log (N : ℝ) / Real.log 2⌋₊ + 1
    have hL_pos : 1 ≤ L := by omega
    have hL_le : (L : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have h1 : (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 :=
        Nat.floor_le (by positivity)
      have hlog2_ge : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hlogN_ge : (2.7 : ℝ) ≤ Real.log (N : ℝ) := by
        have h16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
        calc (2.7 : ℝ) ≤ 4 * Real.log 2 := by linarith
          _ = Real.log ((2 : ℝ) ^ 4) := by rw [Real.log_pow]; norm_num
          _ = Real.log 16 := by norm_num
          _ ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) h16
      have hdiv : Real.log (N : ℝ) / Real.log 2 ≤ 1.5 * Real.log (N : ℝ) := by
        rw [div_le_iff₀ hlog2_pos]; nlinarith
      dsimp only [L]; push_cast; linarith
    have homega_le_L : ∀ n ∈ A, omega n ≤ L := by
      intro n hn
      have hn1 : 1 ≤ n := hA_pos n hn
      have hnN : n ≤ N := (hA_bounds n hn).2
      have h1 : (omega n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
        unfold omega
        exact RHDirect.Stage2DirichletAP.card_primeFactors_le_log_div_log_two hn1
      have h2 : Real.log (n : ℝ) / Real.log 2 ≤ Real.log (N : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)) hlog2_pos.le
      have h3 : (omega n : ℝ) < (L : ℝ) := by
        dsimp only [L]; push_cast
        linarith [Nat.lt_floor_add_one (Real.log (N : ℝ) / Real.log 2)]
      exact le_of_lt (by exact_mod_cast h3)
    have hcos_m2 : ∀ h ∈ m2,
        cosProd A k h ≤ ((N : ℝ)⁻¹) ^ (4 * (𝒬 \ goodPrimePowers A M η K ((k : ℤ) * h)).card) := by
      intro h _
      set 𝒟 := goodPrimePowers A M η K ((k : ℤ) * h)
      -- Raise both sides to the `L`-th power!
      refine le_of_pow_le_pow_left₀ (by omega : L ≠ 0) (by positivity) ?_
      have hpow_le : (cosProd A k h) ^ L ≤ ∏ q ∈ 𝒬, cosProd (exactSlice A q) k h := by
        unfold cosProd
        rw [← Finset.prod_pow]
        -- Swap product over `q ∈ 𝒬` and `n ∈ A`: `∏ q ∈ 𝒬, ∏ n ∈ A_q, f n = ∏ n ∈ A, (f n)^(omega n)`!
        have hswap : ∏ q ∈ 𝒬, ∏ n ∈ exactSlice A q, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))| =
            ∏ n ∈ A, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))| ^ (omega n) := by
          have h1 : ∀ q ∈ 𝒬, ∏ n ∈ exactSlice A q, |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))| =
              ∏ n ∈ A, (if ppowDiv q n then |Real.cos (Real.pi * (k : ℝ) * (h : ℝ) / (n : ℝ))| else 1) := by
            intro q _; unfold exactSlice; rw [Finset.prod_filter]
          rw [Finset.prod_congr rfl h1, Finset.prod_comm]
          refine Finset.prod_congr rfl fun n hn => ?_
          rw [← Finset.prod_filter]
          have hfilt : 𝒬.filter (fun q => ppowDiv q n) = exactPrimePowers n := by
            ext q
            simp only [Finset.mem_filter]
            have hn0 : n ≠ 0 := (hA_pos n hn).ne'
            rw [ppowDiv_iff_mem_exactPrimePowers hn0]
            exact ⟨fun h => h.2, fun h => ⟨Finset.mem_biUnion.mpr ⟨n, hn, h⟩, h⟩⟩
          rw [hfilt, Finset.prod_const, card_exactPrimePowers]
        rw [hswap]
        refine Finset.prod_le_prod (fun _ _ => pow_nonneg (abs_nonneg _) _) fun n hn => ?_
        exact pow_le_pow_of_le_one (abs_nonneg _) (Real.abs_cos_le_one _) (homega_le_L n hn)
      have hdrop : ∏ q ∈ 𝒬, cosProd (exactSlice A q) k h ≤
          ∏ q ∈ 𝒬 \ 𝒟, cosProd (exactSlice A q) k h := by
        have hsub : 𝒬 \ 𝒟 ⊆ 𝒬 := Finset.sdiff_subset
        rw [← Finset.prod_sdiff hsub]
        calc (∏ q ∈ 𝒬 \ (𝒬 \ 𝒟), cosProd (exactSlice A q) k h) *
              (∏ q ∈ 𝒬 \ 𝒟, cosProd (exactSlice A q) k h)
            ≤ 1 * (∏ q ∈ 𝒬 \ 𝒟, cosProd (exactSlice A q) k h) :=
              mul_le_mul_of_nonneg_right
                (Finset.prod_le_one (fun _ _ => cosProd_nonneg _ _ _) (fun _ _ => cosProd_le_one _ _ _))
                (Finset.prod_nonneg fun _ _ => cosProd_nonneg _ _ _)
          _ = ∏ q ∈ 𝒬 \ 𝒟, cosProd (exactSlice A q) k h := one_mul _
      refine (hpow_le.trans hdrop).trans ?_
      -- For each `q ∈ 𝒬 \ 𝒟`, `cosProd (exactSlice A q) k h ≤ ((N : ℝ)⁻¹)^(4 * L)`!
      have hterm_q : ∀ q ∈ 𝒬 \ 𝒟, cosProd (exactSlice A q) k h ≤ ((N : ℝ)⁻¹) ^ (4 * L) := by
        intro q hq
        have hq𝒬 := (Finset.mem_sdiff.mp hq).1
        have hqnot𝒟 := (Finset.mem_sdiff.mp hq).2
        have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (mem_ppowersInSet_pos h0_nmem hq𝒬)
        have hmiss_ge : η * M / (q : ℝ) ≤
            (((exactSlice A q).filter (fun n => ¬ dividesInInterval ((k : ℤ) * h) K n)).card : ℝ) := by
          by_contra hlt
          push Not at hlt
          exact hqnot𝒟 (Finset.mem_filter.mpr ⟨hq𝒬, hlt⟩)
        have hslice_bd : ∀ n ∈ exactSlice A q, 1 ≤ n ∧ n ≤ N := fun n hn =>
          hA_bounds n (Finset.mem_filter.mp hn).1
        refine (cosProd_le_exp_of_miss hK_pos.le hslice_bd h).trans ?_
        have hrhs : ((N : ℝ)⁻¹) ^ (4 * L) = Real.exp (-(4 * (L : ℝ) * Real.log (N : ℝ))) := by
          rw [inv_pow, ← Real.rpow_natCast, Real.rpow_def_of_pos hN_pos, ← Real.exp_neg]
          congr 1; push_cast; ring
        rw [hrhs]
        apply Real.exp_le_exp.mpr
        have hq_le : (q : ℝ) ≤ c * (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2)) :=
          (hq_bd q hq𝒬).trans hX_le2
        have hstep1 : 4 * (L : ℝ) * Real.log (N : ℝ) ≤ 8 * (Real.log (N : ℝ)) ^ 2 := by nlinarith
        have hstep2 : 8 * (Real.log (N : ℝ)) ^ 2 ≤ η * M * K ^ 2 / (4 * (N : ℝ) ^ 2 * (q : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]
          have h1 : 4 * (N : ℝ) ^ 2 * (q : ℝ) * (8 * (Real.log (N : ℝ)) ^ 2) =
              32 * (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2 * (q : ℝ) := by ring
          have h2 : (q : ℝ) * ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2) ≤ c * (η * M * K ^ 2) := by
            have := mul_le_mul_of_nonneg_right hq_le (by positivity : 0 ≤ (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2)
            have heq : c * (η * M * K ^ 2 / ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2)) *
                ((N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2) = c * (η * M * K ^ 2) := by
              field_simp [hN_pos.ne', hlogN_pos.ne']
            linarith
          have h3 : 32 * c ≤ 1 := by linarith
          nlinarith [show 0 ≤ η * M * K ^ 2 by positivity]
        have hstep3 : η * M * K ^ 2 / (4 * (N : ℝ) ^ 2 * (q : ℝ)) =
            (η * M / (q : ℝ)) * (K ^ 2 / (4 * (N : ℝ) ^ 2)) := by ring
        have hstep4 : (η * M / (q : ℝ)) * (K ^ 2 / (4 * (N : ℝ) ^ 2)) ≤
            (((exactSlice A q).filter (fun n => ¬ dividesInInterval ((k : ℤ) * h) K n)).card : ℝ) *
              (K ^ 2 / (4 * (N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hmiss_ge (by positivity)
        linarith
      calc ∏ q ∈ 𝒬 \ 𝒟, cosProd (exactSlice A q) k h
          ≤ ∏ _q ∈ 𝒬 \ 𝒟, ((N : ℝ)⁻¹) ^ (4 * L) :=
            Finset.prod_le_prod (fun _ _ => cosProd_nonneg _ _ _) hterm_q
        _ = (((N : ℝ)⁻¹) ^ (4 * L)) ^ (𝒬 \ 𝒟).card := Finset.prod_const _
        _ = (((N : ℝ)⁻¹) ^ (4 * (𝒬 \ 𝒟).card)) ^ L := by
            rw [← pow_mul, ← pow_mul]; congr 1; ring
    -- Every `h ∈ m2` has `𝒟_h ∈ 𝒬.powerset.erase 𝒬`!
    have hD_proper : ∀ h ∈ m2, goodPrimePowers A M η K ((k : ℤ) * h) ∈ 𝒬.powerset.erase 𝒬 := by
      intro h hh
      have hm_mem := (Finset.mem_filter.mp hh).1
      have hnot_m1 := (Finset.mem_filter.mp hh).2
      have hnot_maj := (Finset.mem_filter.mp hm_mem).2
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
      intro heq
      -- By hypothesis (4), since `h ∉ m1`, there exists `x` with `|x - k h| ≤ K / 2` divisible by all `q ∈ 𝒟 = 𝒬`!
      rcases h4 ((k : ℤ) * h) with h4a | ⟨x, hx_dist, hx_dvd⟩
      · exact hnot_m1 h4a
      · rw [heq] at hx_dvd
        -- Then `Q ∣ x`, contradicting `h ∈ minorArc`!
        have hQ_dvd : (Q : ℤ) ∣ x := by
          have hnat : Q ∣ x.natAbs := lcmSet_dvd fun q hq => Int.natCast_dvd.mp (hx_dvd q hq)
          exact Int.natCast_dvd.mpr hnat
        obtain ⟨t, ht⟩ := hQ_dvd
        apply hnot_maj
        refine ⟨t, ?_⟩
        have hsub : (k : ℝ) * (h : ℝ) - (t : ℝ) * (Q : ℝ) = -((x : ℝ) - (((k : ℤ) * h : ℤ) : ℝ)) := by
          have hxR : (x : ℝ) = (Q : ℝ) * (t : ℝ) := by exact_mod_cast ht
          push_cast; linarith
        rw [hsub, abs_neg]
        exact hx_dist
    -- Count `#{h ∈ m2 : 𝒟_h = 𝒟} ≤ 3 * k * N ^ ((𝒬 \ 𝒟).card + 1)` for each `𝒟 ⊆ 𝒬`!
    have hfiber_card : ∀ 𝒟 ∈ 𝒬.powerset.erase 𝒬,
        ((m2.filter (fun h => goodPrimePowers A M η K ((k : ℤ) * h) = 𝒟)).card : ℝ) ≤
          3 * (k : ℝ) * (N : ℝ) ^ ((𝒬 \ 𝒟).card + 1) := by
      intro 𝒟 h𝒟
      have h𝒟Q : 𝒟 ⊆ 𝒬 := Finset.mem_powerset.mp (Finset.mem_erase.mp h𝒟).2
      set D := lcmSet 𝒟
      have hD_pos : 0 < D := lcmSet_pos fun q hq => mem_ppowersInSet_pos h0_nmem (h𝒟Q hq)
      have hD_dvd_Q : D ∣ Q := lcmSet_dvd_lcmSet_of_subset h𝒟Q
      set Fm := m2.filter (fun h => goodPrimePowers A M η K ((k : ℤ) * h) = 𝒟)
      -- Every `h ∈ Fm` has some `m : ℤ` with `|m| ≤ k * (Q / D)` and `|k * h - m * D| ≤ K / 2`!
      set Mlim : ℤ := (k : ℤ) * ((Q / D : ℕ) : ℤ)
      set mRange : Finset ℤ := Finset.Icc (-Mlim) Mlim
      have hex_m : ∀ h ∈ Fm, ∃ m ∈ mRange, |(k : ℝ) * (h : ℝ) - (m : ℝ) * (D : ℝ)| ≤ K / 2 := by
        intro h hh
        have hh2 := (Finset.mem_filter.mp hh).1
        have hDeq := (Finset.mem_filter.mp hh).2
        have hh_m := (Finset.mem_filter.mp hh2).1
        have hh_J := (Finset.mem_filter.mp hh_m).1
        have hh_not4a := (Finset.mem_filter.mp hh2).2
        rcases h4 ((k : ℤ) * h) with h4a | ⟨x, hx_dist, hx_dvd⟩
        · exact (hh_not4a h4a).elim
        · rw [hDeq] at hx_dvd
          have hD_dvd_x : (D : ℤ) ∣ x :=
            Int.natCast_dvd.mpr (lcmSet_dvd fun q hq => Int.natCast_dvd.mp (hx_dvd q hq))
          obtain ⟨m, hm⟩ := hD_dvd_x
          refine ⟨m, ?_, ?_⟩
          · -- Bound `|m| ≤ k * (Q / D)`: since `2 * |h| < Q`, `|k h| < k Q / 2`, and `|x| ≤ |k h| + K/2 < k Q`!
            have h2h : 2 * |h| < (Q : ℤ) := (Finset.mem_filter.mp hh_J).2.2
            have hkh_lt : |(k : ℝ) * (h : ℝ)| < (k : ℝ) * (Q : ℝ) / 2 := by
              have h1 : (2 : ℝ) * |(h : ℝ)| < (Q : ℝ) := by exact_mod_cast h2h
              rw [abs_mul, abs_of_pos hk_pos]
              nlinarith
            have hx_dist' : |(x : ℝ) - (k : ℝ) * (h : ℝ)| ≤ K / 2 := by
              simpa [Int.cast_mul, Int.cast_natCast] using hx_dist
            have hx_lt : |(x : ℝ)| < (k : ℝ) * (Q : ℝ) := by
              have htri := abs_sub_abs_le_abs_sub (x : ℝ) ((k : ℝ) * (h : ℝ))
              have hKQ : K / 2 ≤ (k : ℝ) * (Q : ℝ) / 2 := by
                have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
                nlinarith
              linarith
            have hmD : |(m : ℝ)| * (D : ℝ) < (k : ℝ) * ((Q / D : ℕ) : ℝ) * (D : ℝ) := by
              have hxR : (x : ℝ) = (D : ℝ) * (m : ℝ) := by exact_mod_cast hm
              have hQD : ((Q / D : ℕ) : ℝ) * (D : ℝ) = (Q : ℝ) := by
                exact_mod_cast Nat.div_mul_cancel hD_dvd_Q
              rw [hxR, abs_mul, abs_of_pos (Nat.cast_pos.mpr hD_pos)] at hx_lt
              linarith [show (k : ℝ) * ((Q / D : ℕ) : ℝ) * (D : ℝ) = (k : ℝ) * (Q : ℝ) by
                rw [mul_assoc, hQD]]
            have hm_lt : |(m : ℝ)| < (Mlim : ℝ) := by
              have h1 := lt_of_mul_lt_mul_right hmD (Nat.cast_nonneg D)
              have hMlimR : (Mlim : ℝ) = (k : ℝ) * ((Q / D : ℕ) : ℝ) := by
                dsimp only [Mlim]; rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
              linarith
            have hm_le : |m| ≤ Mlim := le_of_lt (by exact_mod_cast hm_lt)
            exact Finset.mem_Icc.mpr (abs_le.mp hm_le)
          · have hsub : (k : ℝ) * (h : ℝ) - (m : ℝ) * (D : ℝ) = -((x : ℝ) - (((k : ℤ) * h : ℤ) : ℝ)) := by
              have hxR : (x : ℝ) = (D : ℝ) * (m : ℝ) := by exact_mod_cast hm
              push_cast; linarith
            rw [hsub, abs_neg]; exact hx_dist
      -- Cover `Fm` by `mRange.biUnion (fun m => Fm.filter (fun h : ℤ => |k h - m D| ≤ K/2))`
      have hFm_sub : Fm ⊆ mRange.biUnion (fun m =>
          Fm.filter (fun h : ℤ => |(k : ℝ) * (h : ℝ) - (m : ℝ) * (D : ℝ)| ≤ K / 2)) := by
        intro h hh
        obtain ⟨m, hmR, hdist⟩ := hex_m h hh
        exact Finset.mem_biUnion.mpr ⟨m, hmR, Finset.mem_filter.mpr ⟨hh, hdist⟩⟩
      -- For each fixed `m`, at most `⌊K⌋₊ + 1 ≤ N` integers `h` satisfy `|k h - m D| ≤ K / 2`!
      have hslice_card : ∀ m ∈ mRange,
          (Fm.filter (fun h : ℤ => |(k : ℝ) * (h : ℝ) - (m : ℝ) * (D : ℝ)| ≤ K / 2)).card ≤ N := by
        intro m _
        set S_m : Finset ℤ := Fm.filter (fun h : ℤ => |(k : ℝ) * (h : ℝ) - (m : ℝ) * (D : ℝ)| ≤ K / 2)
        by_cases hSne : S_m.Nonempty
        · have hmin_ex := Finset.min'_mem S_m hSne
          set h₀ : ℤ := S_m.min' hSne
          have hsub_Icc : S_m ⊆ Finset.Icc h₀ (h₀ + (⌊K⌋₊ : ℤ)) := by
            intro h hh
            refine Finset.mem_Icc.mpr ⟨Finset.min'_le S_m h hh, ?_⟩
            have hd1 := (Finset.mem_filter.mp hh).2
            have hd0 := (Finset.mem_filter.mp hmin_ex).2
            have hdiff : (k : ℝ) * ((h - h₀ : ℤ) : ℝ) ≤ K := by
              have htri := abs_sub_le ((k : ℝ) * (h : ℝ)) ((m : ℝ) * (D : ℝ)) ((k : ℝ) * (h₀ : ℝ))
              rw [abs_sub_comm ((m : ℝ) * (D : ℝ))] at htri
              have heq : (k : ℝ) * (h : ℝ) - (k : ℝ) * (h₀ : ℝ) = (k : ℝ) * ((h - h₀ : ℤ) : ℝ) := by
                push_cast; ring
              linarith [le_abs_self ((k : ℝ) * (h : ℝ) - (k : ℝ) * (h₀ : ℝ))]
            have hle_K : ((h - h₀ : ℤ) : ℝ) ≤ K := by
              have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
              have hnn : (0 : ℝ) ≤ ((h - h₀ : ℤ) : ℝ) := by
                have := Finset.min'_le S_m h hh
                exact_mod_cast (by omega : 0 ≤ h - h₀)
              nlinarith
            have hle_fl : h - h₀ ≤ (⌊K⌋₊ : ℤ) := by
              have hlt : ((h - h₀ : ℤ) : ℝ) < ((⌊K⌋₊ + 1 : ℕ) : ℝ) := by
                rw [Nat.cast_add, Nat.cast_one]
                linarith [Nat.lt_floor_add_one K]
              have hltZ : h - h₀ < (⌊K⌋₊ : ℤ) + 1 := by exact_mod_cast hlt
              omega
            omega
          calc S_m.card ≤ (Finset.Icc h₀ (h₀ + (⌊K⌋₊ : ℤ))).card := Finset.card_le_card hsub_Icc
            _ = ⌊K⌋₊ + 1 := by rw [Int.card_Icc]; omega
            _ ≤ N := by
                have hK_lt : K < (N : ℝ) := by linarith
                have hfl_lt : ⌊K⌋₊ < N := (Nat.floor_lt hK_pos.le).mpr hK_lt
                omega
        · rw [Finset.not_nonempty_iff_eq_empty.mp hSne]; simp
      have hcard_le : Fm.card ≤ mRange.card * N := by
        calc Fm.card
            ≤ (mRange.biUnion (fun m =>
                Fm.filter (fun h : ℤ => |(k : ℝ) * (h : ℝ) - (m : ℝ) * (D : ℝ)| ≤ K / 2))).card :=
              Finset.card_le_card hFm_sub
          _ ≤ ∑ m ∈ mRange, (Fm.filter (fun h : ℤ => |(k : ℝ) * (h : ℝ) - (m : ℝ) * (D : ℝ)| ≤ K / 2)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _m ∈ mRange, N := Finset.sum_le_sum hslice_card
          _ = mRange.card * N := by simp
      have hMlim_pos : 1 ≤ Mlim := by
        have hQD_pos : 1 ≤ Q / D := Nat.div_pos (Nat.le_of_dvd hQ_pos hD_dvd_Q) hD_pos
        dsimp only [Mlim]
        have : 1 ≤ k * (Q / D) := Nat.mul_pos hk1 hQD_pos
        exact_mod_cast this
      have hmRange_card : (mRange.card : ℝ) ≤ 3 * (k : ℝ) * ((Q / D : ℕ) : ℝ) := by
        have hc_eq : mRange.card = (2 * Mlim + 1).toNat := by
          unfold mRange; rw [Int.card_Icc]; omega
        have h1 : (mRange.card : ℝ) = 2 * (Mlim : ℝ) + 1 := by
          rw [hc_eq]
          have : (0 : ℤ) ≤ 2 * Mlim + 1 := by omega
          have := Int.toNat_of_nonneg this
          exact_mod_cast this
        have hMlimR : (Mlim : ℝ) = (k : ℝ) * ((Q / D : ℕ) : ℝ) := by
          dsimp only [Mlim]; rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
        have hMlim1 : (1 : ℝ) ≤ (Mlim : ℝ) := by exact_mod_cast hMlim_pos
        linarith
      have hQD_le : ((Q / D : ℕ) : ℝ) ≤ (N : ℝ) ^ (𝒬 \ 𝒟).card := by
        have h1 : Q / D ≤ ∏ q ∈ 𝒬 \ 𝒟, q :=
          lcmSet_div_le_prod_sdiff h𝒟Q fun q hq => mem_ppowersInSet_pos h0_nmem hq
        have h2 : ∏ q ∈ 𝒬 \ 𝒟, q ≤ ∏ _q ∈ 𝒬 \ 𝒟, N := by
          refine Finset.prod_le_prod' fun q hq => ?_
          have hq𝒬 := (Finset.mem_sdiff.mp hq).1
          exact (Finset.mem_Icc.mp (ppowersInSet_subset_Icc hA_bounds hq𝒬)).2
        rw [Finset.prod_const] at h2
        exact_mod_cast le_trans h1 h2
      calc (Fm.card : ℝ)
          ≤ (mRange.card : ℝ) * (N : ℝ) := by exact_mod_cast hcard_le
        _ ≤ (3 * (k : ℝ) * ((Q / D : ℕ) : ℝ)) * (N : ℝ) := by gcongr
        _ ≤ (3 * (k : ℝ) * (N : ℝ) ^ (𝒬 \ 𝒟).card) * (N : ℝ) := by gcongr
        _ = 3 * (k : ℝ) * (N : ℝ) ^ ((𝒬 \ 𝒟).card + 1) := by rw [pow_succ]; ring
    -- Sum over `𝒟 ∈ 𝒬.powerset.erase 𝒬`!
    rw [← Finset.sum_fiberwise_of_maps_to hD_proper]
    calc ∑ 𝒟 ∈ 𝒬.powerset.erase 𝒬,
          ∑ h ∈ m2.filter (fun h => goodPrimePowers A M η K ((k : ℤ) * h) = 𝒟), cosProd A k h
        ≤ ∑ 𝒟 ∈ 𝒬.powerset.erase 𝒬,
            (3 * (k : ℝ) * (N : ℝ) ^ ((𝒬 \ 𝒟).card + 1)) * ((N : ℝ)⁻¹) ^ (4 * (𝒬 \ 𝒟).card) := by
          refine Finset.sum_le_sum fun 𝒟 h𝒟 => ?_
          calc ∑ h ∈ m2.filter (fun h => goodPrimePowers A M η K ((k : ℤ) * h) = 𝒟), cosProd A k h
              ≤ ∑ _h ∈ m2.filter (fun h => goodPrimePowers A M η K ((k : ℤ) * h) = 𝒟),
                  ((N : ℝ)⁻¹) ^ (4 * (𝒬 \ 𝒟).card) := by
                refine Finset.sum_le_sum fun h hh => ?_
                have hh2 := (Finset.mem_filter.mp hh).1
                have hDeq := (Finset.mem_filter.mp hh).2
                rw [← hDeq]
                exact hcos_m2 h hh2
            _ = ((m2.filter (fun h => goodPrimePowers A M η K ((k : ℤ) * h) = 𝒟)).card : ℝ) *
                  ((N : ℝ)⁻¹) ^ (4 * (𝒬 \ 𝒟).card) := by simp
            _ ≤ (3 * (k : ℝ) * (N : ℝ) ^ ((𝒬 \ 𝒟).card + 1)) * ((N : ℝ)⁻¹) ^ (4 * (𝒬 \ 𝒟).card) := by
                gcongr; exact hfiber_card 𝒟 h𝒟
      _ = 3 * (k : ℝ) * (N : ℝ) * ∑ 𝒟 ∈ 𝒬.powerset.erase 𝒬, ((N : ℝ) ^ 3)⁻¹ ^ (𝒬 \ 𝒟).card := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun 𝒟 _ => ?_
          set r := (𝒬 \ 𝒟).card
          have h1 : (N : ℝ) ^ (r + 1) * ((N : ℝ)⁻¹) ^ (4 * r) = (N : ℝ) * (((N : ℝ) ^ 3)⁻¹) ^ r := by
            rw [pow_succ, inv_pow, inv_pow, ← pow_mul]
            have hN0 : (N : ℝ) ≠ 0 := hN_pos.ne'
            have h4r : (N : ℝ) ^ (4 * r) = (N : ℝ) ^ r * (N : ℝ) ^ (3 * r) := by
              rw [← pow_add]; congr 1; omega
            rw [h4r]
            field_simp [hN0]
          rw [show (3 * (k : ℝ) * (N : ℝ) ^ (r + 1)) * ((N : ℝ)⁻¹) ^ (4 * r) =
            3 * (k : ℝ) * ((N : ℝ) ^ (r + 1) * ((N : ℝ)⁻¹) ^ (4 * r)) by ring, h1]
          ring
      _ = 3 * (k : ℝ) * (N : ℝ) * ((1 + ((N : ℝ) ^ 3)⁻¹) ^ 𝒬.card - 1) := by
          congr 1
          -- `∑_{𝒟 ⊆ 𝒬} x^{|𝒬 \ 𝒟|} = (1 + x)^{|𝒬|}` via `Finset.prod_add`!
          set x : ℝ := ((N : ℝ) ^ 3)⁻¹
          have hfull : ∑ 𝒟 ∈ 𝒬.powerset, x ^ (𝒬 \ 𝒟).card = (1 + x) ^ 𝒬.card := by
            have h1 := Finset.prod_add (fun _ : ℕ => (1 : ℝ)) (fun _ : ℕ => x) 𝒬
            rw [Finset.prod_const] at h1
            rw [h1]
            refine Finset.sum_congr rfl fun 𝒟 _ => ?_
            simp [Finset.prod_const_one, Finset.prod_const]
          have hQmem : 𝒬 ∈ 𝒬.powerset := Finset.mem_powerset.mpr Subset.rfl
          have hsum_er := Finset.add_sum_erase 𝒬.powerset (fun 𝒟 => x ^ (𝒬 \ 𝒟).card) hQmem
          simp only [Finset.sdiff_self, Finset.card_empty, pow_zero] at hsum_er
          linarith
      _ ≤ 3 * (k : ℝ) * (N : ℝ) * (2 * (𝒬.card : ℝ) * ((N : ℝ) ^ 3)⁻¹) := by
          gcongr
          have h𝒬_le_N : (𝒬.card : ℝ) ≤ (N : ℝ) := by
            have h1 := Finset.card_le_card (ppowersInSet_subset_Icc hA_bounds)
            simp at h1
            exact_mod_cast h1
          have hsmall : (𝒬.card : ℝ) * ((N : ℝ) ^ 3)⁻¹ ≤ 1 / 2 := by
            calc (𝒬.card : ℝ) * ((N : ℝ) ^ 3)⁻¹
                ≤ (N : ℝ) * ((N : ℝ) ^ 3)⁻¹ := by gcongr
              _ = 1 / (N : ℝ) ^ 2 := by field_simp [hN_pos.ne']
              _ ≤ 1 / 2 := by
                  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                  have : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
                  nlinarith
          exact one_add_pow_sub_one_le (by positivity) 𝒬.card hsmall
      _ ≤ 6 * (k : ℝ) / (N : ℝ) := by
          have h𝒬_le_N : (𝒬.card : ℝ) ≤ (N : ℝ) := by
            have h1 := Finset.card_le_card (ppowersInSet_subset_Icc hA_bounds)
            simp at h1
            exact_mod_cast h1
          calc 3 * (k : ℝ) * (N : ℝ) * (2 * (𝒬.card : ℝ) * ((N : ℝ) ^ 3)⁻¹)
              ≤ 3 * (k : ℝ) * (N : ℝ) * (2 * (N : ℝ) * ((N : ℝ) ^ 3)⁻¹) := by gcongr
            _ = 6 * (k : ℝ) / (N : ℝ) := by field_simp [hN_pos.ne']; ring
      _ ≤ 1 / 8 := by
          have hkN : (k : ℝ) ≤ c * (N : ℝ) := hkM.trans (mul_le_mul_of_nonneg_left hMN hc_pos.le)
          rw [div_le_iff₀ hN_pos]
          nlinarith
  -- Step 5: Combine `hm1_bound` and `hm2_bound` to get `(countIntMultiple A k : ℝ) > 1`!
  have hminor_le : ∑ h ∈ minorArc, cosProd A k h ≤ 1 / 4 := by linarith
  have hhalf_F : (2 : ℝ) ^ A.card / (2 * (Q : ℝ)) ≤ (countIntMultiple A k : ℝ) := by
    calc (2 : ℝ) ^ A.card / (2 * (Q : ℝ))
        = ((2 : ℝ) ^ A.card / (Q : ℝ)) * (1 / 2) := by ring
      _ ≤ ((2 : ℝ) ^ A.card / (Q : ℝ)) * (1 - ∑ h ∈ minorArc, cosProd A k h) := by
          gcongr; linarith
      _ ≤ (countIntMultiple A k : ℝ) := hF_lower
  -- Show `2 * Q < 2^{|A|}` using `Q ≤ exp(C_lcm * X) ≤ 2^{|A| / 2}` and `|A| ≥ 64`!
  have hQ_small : (Q : ℝ) ≤ (2 : ℝ) ^ ((A.card : ℝ) / 2) := by
    refine hQ_le_exp.trans ?_
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have h1 : C_lcm * X ≤ (C_lcm * c) * (M / (k : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hX_le1 hClcm_pos.le
      linarith [show C_lcm * (c * (M / (k : ℝ))) = (C_lcm * c) * (M / (k : ℝ)) by ring]
    have h2 : C_lcm * c ≤ Real.log 2 / 16 := by
      have := mul_le_mul_of_nonneg_left hc_le_lcm hClcm_pos.le
      have heq : C_lcm * (Real.log 2 / (16 * C_lcm)) = Real.log 2 / 16 := by
        field_simp [hClcm_pos.ne']
      linarith
    have h3 : (C_lcm * c) * (M / (k : ℝ)) ≤ (Real.log 2 / 2) * (A.card : ℝ) := by
      calc (C_lcm * c) * (M / (k : ℝ))
          ≤ (Real.log 2 / 16) * (A.card : ℝ) :=
            mul_le_mul h2 hcardA_ge (by positivity) (by positivity)
        _ ≤ (Real.log 2 / 2) * (A.card : ℝ) := by nlinarith
    linarith [show Real.log 2 * ((A.card : ℝ) / 2) = (Real.log 2 / 2) * (A.card : ℝ) by ring]
  have h2Q_lt : 2 * (Q : ℝ) < (2 : ℝ) ^ A.card := by
    have hpow_split : (2 : ℝ) ^ A.card = (2 : ℝ) ^ ((A.card : ℝ) / 2) * (2 : ℝ) ^ ((A.card : ℝ) / 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_halves, Real.rpow_natCast]
    have hgt2 : (2 : ℝ) < (2 : ℝ) ^ ((A.card : ℝ) / 2) := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ < (2 : ℝ) ^ ((A.card : ℝ) / 2) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [hpow_split]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((A.card : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  have h1_lt : (1 : ℝ) < (2 : ℝ) ^ A.card / (2 * (Q : ℝ)) := by
    rw [one_lt_div (by positivity)]
    exact h2Q_lt
  linarith

end Prize.PPL024
