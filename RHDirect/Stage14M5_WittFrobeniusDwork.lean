import RHDirect.Stage12MultivarDwork
import RHDirect.Stage12FontainePeriods
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# RHDirect.Stage14M5_WittFrobeniusDwork

Field-2 Package M5 Wave 1: **Witt Vectors `WW p`, Frobenius Lift `sigK p`, Multivariable Dwork
Integrality Lemma (`dwork_multivariable_witt`), `FormalGroupSystem` Positivity Condition
(`sx_dwork_holds`), and Multivariable Formal-Series Inversion Integrality (`WipDworkInvG` /
`intS_invG_mv_inversion`)** in pure Mathlib `v4.33.1`
(`0 sorry`, `0 custom axioms`, `0 opaque`, `0 native_decide`).

## Architecture (Diamond-Free)

All Witt-vector embeddings, Frobenius lifts, and `MvPowerSeries` coefficient maps use **explicit
`RingHom`s** — NEVER nested global `Algebra` instances over `MvPowerSeries`/`WittVector` and NEVER
a global `NormedField (FractionRing (WittVector p k))` instance — preventing typeclass diamonds and
keeping elaboration fast.

## Contents

1. **`WittRingLift p`, `FrobSigK p`, and Concrete Witt Vectors `WW p` / `K0 p`**:
   - Diamond-free structures `WittRingLift p` (integral ring `W` embedded via explicit injective
     `toField : W →+* K` into an ultrametric normed field `K` with `‖p‖ = p⁻¹` and exact
     `p^n`-divisibility characterization) and `FrobSigK p L` (Frobenius endomorphism
     `sigW : W →+* W`, automorphism `sigK : K ≃+* K` commuting with `toField`, and congruence
     `sigW w ≡ w^p (mod p)`).
   - Concrete realization over `WittVector p k` for any perfect field `k` of characteristic `p`,
     specialized to `kb p := AlgebraicClosure (ZMod p)`, `WW p := WittVector p (kb p)`,
     `K0 p := FractionRing (WW p)`, `sigW p := WittVector.frobenius`, and
     `sigK p := IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (kb p))`.
   - Complete ultrametric absolute value `wittAbv p` (`wittAbv_p`, `wittAbv_nonarch`,
     `wittAbv_le_one_iff`, `wittAbv_le_pow_iff`, `wittAbv_unit`, `wittAbv_value`, `wittAbv_sig`,
     `witt_complete`), concrete witnesses `concreteWittRingLift p`, `concreteFrobSigK p`,
     `padicWittRingLift p`, `padicFrobSigK p`, Teichmüller Frobenius identities, and Fontaine
     `A_inf` Frobenius congruence bridge `ainf_frob_congr_p`.

2. **Multivariable Dwork Integrality Lemma over `WittRingLift p` (`dwork_multivariable_witt`)**:
   - Ring-level integrality `IntSMv L f`, `CongOneModPWitt L f`, and explicit Frobenius map
     `wittFrobMap Φ` with equivalences `intSMv_iff_isIntegralMv` and
     `congOneModPWitt_iff_congOneModPMv`.
   - **`dwork_multivariable_witt`**: for any `L : WittRingLift p`, `Φ : FrobSigK p L`, and
     `f : MvPowerSeries σ L.K` with `constantCoeff f = 1`,
     `IntSMv L f ↔ CongOneModPWitt L (f ^ p * invOneMv (wittFrobMap Φ f))`
     (plus dual orientation `dwork_multivariable_witt_dual`, division-free form, and concrete
     `WW p` specialization `dwork_multivariable_WW`).
   - Exponential calculus `expSMv` and unconditional prime-`p` congruence criterion
     `congOneModPMv_expSMv_iff` (valid for ALL primes `p ≥ 2` and arbitrary index types `σ`),
     yielding **`dwork_exp_multivariable_witt`** and twisted Witt Artin–Hasse integrality
     `wittArtinHasseExp_isIntegral`.

3. **`FormalGroupSystem` over `WW p` / `K0 p`, `sx_dwork_holds`, & `PositivityConditionHolds`**:
   - Concrete `FormalGroupSystem` objects over `WW p` / `K0 p`: `IntS`, `IntR`, `expS`, `logF`,
     `inParam`, `inParamHom`, `Simeq` (proved equivalence relation), `sub2`, `BeProp`, `OmBasis`
     (with non-vacuous witness `omBasisTwo`), `DworkLemma`, and `PositivityConditionHolds`.
   - **`sx_dwork_witt`**, **`sx_dwork_holds`**, and unconditional **`positivity_condition_holds`**.
   - Height-2 formal group logarithm functional equation `logF_functional_eq`.

4. **`WipDworkInvG` & Multivariable Formal-Series Inversion Integrality (`intS_invG_mv_inversion`)**:
   - Unified master subring inversion theorem **`intS_invG_subring`** & coordinate-change invariance
     **`image_eq_int_subring`**, specializing cleanly to:
     - Additive-valuation `AltInv` / `WipDworkInvG`: `IntC`, `IntSVal`, `intS_invG_val`,
       `intS_inv_val`, `image_eq_int_val`, `image_eq_image_val`.
     - Ultrametric & `WittRingLift p`: **`intS_invG_norm`**, **`intS_invG_mv_inversion`**,
       **`intS_invG_WW`**, **`image_eq_int_witt`**, **`image_eq_image_witt`**.
   - Explicit degree-recursive formal inverse construction **`exists_unique_mv_formal_inversion`**
     and **`exists_integral_mv_formal_inversion`**.

5. **`FormalGroupSystemWitt` & Wave 2 Handoff (`Stage14M5_DataDIVDefsNuLat`, `Stage14M5_LinkGAndAskIsF`)**:
   - Bundled `FormalGroupSystemWitt p` and `WittDworkFormalGroupPack p` with unconditional concrete
     witnesses `formalGroupSystemWW p` and `concreteWittDworkFormalGroupPack p` for every prime `p`.
-/

open Real Finset IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators NNReal
open RHDirect.PAdicChainValuation
open RHDirect.Stage2DworkExp
open RHDirect.Stage12MultivarDwork
open RHDirect.Stage12FontainePeriods

namespace RHDirect.Stage14M5_WittFrobeniusDwork

noncomputable section

/-! ## Section 0: Ring-Generic Multi-Index & Vanishing-Order Helpers (`LowDeg`) -/

section LowDegHelpers

variable {σ R : Type*}

lemma finsupp_degree_eq_zero_iff (d : σ →₀ ℕ) : d.degree = 0 ↔ d = 0 := by
  constructor
  · intro h
    ext i
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hi
    have hmem : i ∈ d.support := Finsupp.mem_support_iff.mpr hi
    have hle : d i ≤ d.degree := by
      rw [Finsupp.degree_apply]
      exact Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) hmem
    omega
  · rintro rfl; simp

lemma finsupp_degree_pos_of_ne_zero {d : σ →₀ ℕ} (hd : d ≠ 0) : 0 < d.degree := by
  have hne : d.degree ≠ 0 := mt (finsupp_degree_eq_zero_iff d).mp hd
  omega

/-- Ring-generic vanishing order `LowDeg N f`: all coefficients of total degree `< N` vanish.
Works over ANY `[CommSemiring R]` with zero `NormedField` dependency. -/
def LowDeg [CommSemiring R] (N : ℕ) (f : MvPowerSeries σ R) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < N → MvPowerSeries.coeff d f = 0

lemma lowDeg_mono [CommSemiring R] {M N : ℕ} (hMN : M ≤ N) {f : MvPowerSeries σ R}
    (hf : LowDeg N f) : LowDeg M f :=
  fun d hd => hf d (lt_of_lt_of_le hd hMN)

lemma lowDeg_zero [CommSemiring R] (N : ℕ) : LowDeg N (0 : MvPowerSeries σ R) :=
  fun _ _ => by simp

lemma lowDeg_add [CommSemiring R] {N : ℕ} {f g : MvPowerSeries σ R}
    (hf : LowDeg N f) (hg : LowDeg N g) : LowDeg N (f + g) := fun d hd => by
  rw [map_add, hf d hd, hg d hd, add_zero]

lemma lowDeg_mul [CommSemiring R] {M N : ℕ} {f g : MvPowerSeries σ R}
    (hf : LowDeg M f) (hg : LowDeg N g) : LowDeg (M + N) (f * g) := fun d hd => by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have hdeg : x.1.degree + x.2.degree = d.degree := by rw [← map_add, hx]
  by_cases h1 : x.1.degree < M
  · rw [hf x.1 h1, zero_mul]
  · rw [hg x.2 (by omega), mul_zero]

lemma lowDeg_pow [CommSemiring R] {D : ℕ} {f : MvPowerSeries σ R}
    (hf : LowDeg D f) (n : ℕ) : LowDeg (n * D) (f ^ n) := by
  induction n with
  | zero => intro d hd; simp at hd
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact lowDeg_mul ih hf

lemma lowDeg_one_of_constantCoeff_zero [CommSemiring R] {f : MvPowerSeries σ R}
    (hf : MvPowerSeries.constantCoeff f = 0) : LowDeg 1 f := fun d hd => by
  have hd0 : d = 0 := (finsupp_degree_eq_zero_iff d).mp (by omega)
  subst hd0
  simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hf

lemma lowDeg_pow_sub_of_lowDeg [CommRing R] {h₁ h₂ : MvPowerSeries σ R} {N : ℕ}
    (h1 : LowDeg 1 h₁) (h2 : LowDeg 1 h₂) (hdiff : LowDeg N (h₁ - h₂)) {k : ℕ} (hk : 2 ≤ k) :
    LowDeg (N + 1) (h₁ ^ k - h₂ ^ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero =>
    have heq : h₁ ^ 2 - h₂ ^ 2 = (h₁ - h₂) * (h₁ + h₂) := by ring
    rw [add_zero, heq]
    exact lowDeg_mul hdiff (lowDeg_add h1 h2)
  | succ m ih =>
    have heq : h₁ ^ (2 + (m + 1)) - h₂ ^ (2 + (m + 1)) =
        (h₁ ^ (2 + m) - h₂ ^ (2 + m)) * h₁ + h₂ ^ (2 + m) * (h₁ - h₂) := by ring
    rw [heq]
    refine lowDeg_add ?_ ?_
    · exact lowDeg_mono (by omega) (lowDeg_mul (ih (by omega)) h1)
    · have hp2 : LowDeg ((2 + m) * 1) (h₂ ^ (2 + m)) := lowDeg_pow h2 (2 + m)
      exact lowDeg_mono (by omega) (lowDeg_mul hp2 hdiff)

lemma hasSubst_of_constantCoeff_zero_mv [CommRing R] [Finite σ] {τ : Type*}
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.HasSubst a :=
  ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩

lemma deg_one_single (d : σ →₀ ℕ) (h : d.degree = 1) : ∃ y, d = Finsupp.single y 1 := by
  classical
  have hdeg : ∑ i ∈ d.support, d i = 1 := h
  have h1 : ∀ x ∈ d.support, d x = 1 := by
    intro x hx
    have hle := Finset.single_le_sum (f := fun i => d i) (fun _ _ => Nat.zero_le _) hx
    have h0 : d x ≠ 0 := Finsupp.mem_support_iff.1 hx
    omega
  have hcard : d.support.card = 1 := by
    rw [← hdeg, Finset.sum_congr rfl h1]
    simp
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hcard
  refine ⟨y, Finsupp.ext fun x => ?_⟩
  by_cases hx : x = y
  · subst hx
    rw [Finsupp.single_eq_same]
    exact h1 x (by rw [hy]; exact Finset.mem_singleton_self x)
  · have hxs : x ∉ d.support := by rw [hy]; simpa using hx
    have hdx : d x = 0 := by
      by_contra h'
      exact hxs (Finsupp.mem_support_iff.2 h')
    rw [hdx, Finsupp.single_apply, if_neg (Ne.symm hx)]

end LowDegHelpers

/-! ## Section 1: `WittRingLift p`, `FrobSigK p`, and Concrete Witt Vectors `WW p` / `K0 p` -/

section WittRingLiftCore

/-- Construct a `NormedField K` directly from a real-valued `AbsoluteValue K ℝ`,
extending the EXISTING `[Field K]` with `‖x‖ = abv x` definitionally.
Marked `@[instance_reducible]` (and NOT a global `instance`) so that `(normedFieldOfAbv abv).toField`
is definitionally equal to the ambient `Field K` with zero typeclass diamonds. -/
@[instance_reducible]
def normedFieldOfAbv {K : Type*} [Field K] (abv : AbsoluteValue K ℝ) : NormedField K where
  norm x := abv x
  dist x y := abv (x - y)
  dist_self x := by simp
  dist_comm x y := (abv.map_sub y x).symm
  dist_triangle x y z := by
    have h : x - z = (x - y) + (y - z) := by ring
    rw [h]
    exact abv.add_le _ _
  edist_dist x y := by simp [ENNReal.ofReal_eq_coe_nnreal (abv.nonneg _)]
  eq_of_dist_eq_zero {x y} h := sub_eq_zero.mp (abv.eq_zero.mp h)
  dist_eq x y := by
    change abv (x - y) = abv (-x + y)
    rw [show -x + y = -(x - y) by ring, abv.map_neg]
  norm_mul x y := abv.map_mul x y

/-- **Diamond-Free Witt-Vector Ring Lift (`WittRingLift p`)**:
bundles an integral domain `W` of characteristic `0`, an ambient ultrametric normed field `K` of
characteristic `0`, and an explicit injective `RingHom` `toField : W →+* K` (no nested global
`Algebra` instances!) characterizing `W` as the closed unit ball `‖x‖ ≤ 1` and `p^n · W` as
`‖x‖ ≤ p^{-n}`. -/
structure WittRingLift.{u} (p : ℕ) [Fact p.Prime] where
  /-- Integral ring of Witt vectors (e.g. `WW p = WittVector p (AlgebraicClosure (ZMod p))` or `ℤ_[p]`). -/
  W : Type u
  /-- Ambient ultrametric fraction field (e.g. `K0 p = FractionRing (WW p)` or `ℚ_[p]`). -/
  K : Type u
  [ringW : CommRing W]
  [domW : IsDomain W]
  [charZeroW : CharZero W]
  [normedFieldK : NormedField K]
  [ultraK : IsUltrametricDist K]
  [charZeroK : CharZero K]
  /-- Explicit embedding `W →+* K` (avoids global `Algebra` diamonds). -/
  toField : W →+* K
  /-- Injectivity of `toField`. -/
  toField_injective : Function.Injective toField
  /-- Normalized `p`-adic norm of `p` in `K`: `‖(p : K)‖ = p⁻¹`. -/
  norm_p : ‖(p : K)‖ = (p : ℝ)⁻¹
  /-- Exact unit-ball characterization of the integral subring `W ⊆ K`. -/
  norm_le_one_iff : ∀ x : K, ‖x‖ ≤ 1 ↔ ∃ w : W, toField w = x
  /-- Exact `p^n`-divisibility characterization in `K`. -/
  norm_le_p_pow_iff : ∀ (n : ℕ) (x : K),
    ‖x‖ ≤ ((p : ℝ)⁻¹) ^ n ↔ ∃ w : W, x = (p : K) ^ n * toField w

attribute [instance] WittRingLift.ringW WittRingLift.domW WittRingLift.charZeroW
  WittRingLift.normedFieldK WittRingLift.ultraK WittRingLift.charZeroK

namespace WittRingLift

variable {p : ℕ} [Fact p.Prime]

theorem hp (_L : WittRingLift p) : p.Prime := Fact.out

variable (L : WittRingLift p)

theorem toField_norm_le_one (w : L.W) : ‖L.toField w‖ ≤ 1 :=
  (L.norm_le_one_iff (L.toField w)).mpr ⟨w, rfl⟩

theorem norm_le_inv_iff (x : L.K) :
    ‖x‖ ≤ (p : ℝ)⁻¹ ↔ ∃ w : L.W, x = (p : L.K) * L.toField w := by
  simpa [pow_one] using L.norm_le_p_pow_iff 1 x

theorem norm_le_norm_p_iff (x : L.K) :
    ‖x‖ ≤ ‖(p : L.K)‖ ↔ ∃ w : L.W, x = (p : L.K) * L.toField w := by
  rw [L.norm_p]
  exact L.norm_le_inv_iff x

theorem norm_p_pos : 0 < ‖(p : L.K)‖ := by
  rw [L.norm_p]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast L.hp.pos
  positivity

theorem norm_p_lt_one : ‖(p : L.K)‖ < 1 := by
  rw [L.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast L.hp.one_lt)

theorem p_ne_zero : (p : L.K) ≠ 0 :=
  norm_pos_iff.mp L.norm_p_pos

theorem norm_natCast_eq_p_pow_neg_padicVal (n : ℕ) (hn : n ≠ 0) :
    ‖(n : L.K)‖ = ((p : ℝ)⁻¹) ^ (padicValNat p n) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk, hnd⟩ : ∃ k, n = p ^ padicValNat p n * k ∧ ¬ p ∣ k := by
    obtain ⟨k, hk⟩ := pow_padicValNat_dvd (p := p) (n := n)
    refine ⟨k, hk, fun hpk => ?_⟩
    obtain ⟨m, rfl⟩ := hpk
    have hd' : p ^ (padicValNat p n + 1) ∣ n :=
      ⟨m, by calc n = p ^ padicValNat p n * (p * m) := hk
        _ = p ^ (padicValNat p n + 1) * m := by rw [pow_succ]; ring⟩
    have hle := (padicValNat_dvd_iff_le hn).mp hd'
    omega
  have hnorm_k_le : ‖(k : L.K)‖ ≤ 1 := by
    have : (k : L.K) = L.toField (k : L.W) := by simp
    rw [this]
    exact L.toField_norm_le_one (k : L.W)
  have hnorm_k_eq : ‖(k : L.K)‖ = 1 := by
    by_contra hne
    have hlt : ‖(k : L.K)‖ < 1 := lt_of_le_of_ne hnorm_k_le hne
    have hcop : Nat.Coprime p k := hp.coprime_iff_not_dvd.mpr hnd
    have hab : (1 : ℤ) = (p : ℤ) * Nat.gcdA p k + (k : ℤ) * Nat.gcdB p k := by
      have h := Nat.gcd_eq_gcd_ab p k
      rw [hcop.gcd_eq_one] at h
      simpa using h
    have h1 : (1 : L.K) = (p : L.K) * (Nat.gcdA p k : L.K) + (k : L.K) * (Nat.gcdB p k : L.K) := by
      have hcast := congrArg (Int.cast (R := L.K)) hab
      simpa using hcast
    have ha_le : ‖(Nat.gcdA p k : L.K)‖ ≤ 1 := by
      have : (Nat.gcdA p k : L.K) = L.toField (Nat.gcdA p k : L.W) := by simp
      rw [this]
      exact L.toField_norm_le_one _
    have hb_le : ‖(Nat.gcdB p k : L.K)‖ ≤ 1 := by
      have : (Nat.gcdB p k : L.K) = L.toField (Nat.gcdB p k : L.W) := by simp
      rw [this]
      exact L.toField_norm_le_one _
    have hpa : ‖(p : L.K) * (Nat.gcdA p k : L.K)‖ < 1 := by
      rw [norm_mul]
      calc ‖(p : L.K)‖ * ‖(Nat.gcdA p k : L.K)‖ ≤ ‖(p : L.K)‖ * 1 :=
            mul_le_mul_of_nonneg_left ha_le (norm_nonneg _)
        _ = ‖(p : L.K)‖ := mul_one _
        _ < 1 := L.norm_p_lt_one
    have hkb : ‖(k : L.K) * (Nat.gcdB p k : L.K)‖ < 1 := by
      rw [norm_mul]
      calc ‖(k : L.K)‖ * ‖(Nat.gcdB p k : L.K)‖ ≤ ‖(k : L.K)‖ * 1 :=
            mul_le_mul_of_nonneg_left hb_le (norm_nonneg _)
        _ = ‖(k : L.K)‖ := mul_one _
        _ < 1 := hlt
    have h1lt : (1 : ℝ) < 1 := by
      calc (1 : ℝ) = ‖(1 : L.K)‖ := norm_one.symm
        _ = ‖(p : L.K) * (Nat.gcdA p k : L.K) + (k : L.K) * (Nat.gcdB p k : L.K)‖ := by rw [h1]
        _ ≤ max ‖(p : L.K) * (Nat.gcdA p k : L.K)‖ ‖(k : L.K) * (Nat.gcdB p k : L.K)‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt hpa hkb
    exact lt_irrefl 1 h1lt
  conv_lhs => rw [hk]
  rw [Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, L.norm_p, hnorm_k_eq, mul_one]

/-- Exact norm bound for `((k! : L.K))⁻¹ * (p : L.K)^k`: since `v_p(k!) < k` for every `k ≥ 1`
and EVERY prime `p ≥ 2` (via `Stage12FontainePeriods.padicValNat_factorial_lt`),
`‖(k! : L.K)⁻¹‖ * ‖(p : L.K)‖^k ≤ ‖(p : L.K)‖`. -/
theorem norm_inv_factorial_mul_norm_p_pow_le {k : ℕ} (hk : 1 ≤ k) :
    ‖((k.factorial : L.K))⁻¹‖ * ‖(p : L.K)‖ ^ k ≤ ‖(p : L.K)‖ := by
  have hlt : padicValNat p k.factorial < k := padicValNat_factorial_lt (p := p) hk
  have hnorm_fac : ‖(k.factorial : L.K)‖ = ((p : ℝ)⁻¹) ^ (padicValNat p k.factorial) :=
    L.norm_natCast_eq_p_pow_neg_padicVal k.factorial (Nat.factorial_ne_zero k)
  rw [norm_inv, hnorm_fac, L.norm_p]
  have hp_pos : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast L.hp.pos
    positivity
  have hp_le1 : (p : ℝ)⁻¹ ≤ 1 := by
    have := L.norm_p_lt_one
    rw [L.norm_p] at this
    exact this.le
  have hpow_split : ((p : ℝ)⁻¹) ^ k =
      ((p : ℝ)⁻¹) ^ (padicValNat p k.factorial) * ((p : ℝ)⁻¹) ^ (k - padicValNat p k.factorial) := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le]
  rw [hpow_split, inv_mul_cancel_left₀ (pow_pos hp_pos _).ne']
  have hexp : 1 ≤ k - padicValNat p k.factorial := by omega
  calc ((p : ℝ)⁻¹) ^ (k - padicValNat p k.factorial)
      ≤ ((p : ℝ)⁻¹) ^ 1 := pow_le_pow_of_le_one hp_pos.le hp_le1 hexp
    _ = (p : ℝ)⁻¹ := pow_one _

end WittRingLift

/-- **Frobenius Lift (`FrobSigK p L`)** over a `WittRingLift p`:
bundles a ring endomorphism `sigW : L.W →+* L.W`, a field automorphism `sigK : L.K ≃+* L.K`
commuting with `L.toField`, and the Witt Frobenius congruence `sigW w ≡ w^p (mod p)` in `L.W`. -/
structure FrobSigK (p : ℕ) [Fact p.Prime] (L : WittRingLift p) where
  /-- Frobenius lift on the integral ring `W`. -/
  sigW : L.W →+* L.W
  /-- Frobenius automorphism on the ambient field `K`. -/
  sigK : L.K ≃+* L.K
  /-- Compatibility `sigK ∘ toField = toField ∘ sigW`. -/
  commutes : ∀ w : L.W, sigK (L.toField w) = L.toField (sigW w)
  /-- Integral Frobenius congruence: `sigW w - w^p ∈ p · W`. -/
  frob_congr_W : ∀ w : L.W, ∃ y : L.W, sigW w - w ^ p = (p : L.W) * y

namespace FrobSigK

variable {p : ℕ} [Fact p.Prime] {L : WittRingLift p} (Φ : FrobSigK p L)

/-- Norm-level Frobenius lift congruence on the unit ball of `L.K`:
`‖a‖ ≤ 1 → ‖sigK a - a^p‖ ≤ ‖(p : L.K)‖`. -/
theorem sigK_sub_pow_le {a : L.K} (ha : ‖a‖ ≤ 1) :
    ‖Φ.sigK a - a ^ p‖ ≤ ‖(p : L.K)‖ := by
  obtain ⟨w, rfl⟩ := (L.norm_le_one_iff a).mp ha
  obtain ⟨y, hy⟩ := Φ.frob_congr_W w
  rw [L.norm_le_norm_p_iff]
  refine ⟨y, ?_⟩
  rw [Φ.commutes w, ← map_pow, ← map_sub, hy, map_mul, map_natCast]

/-- Reversed-sign Frobenius lift congruence `‖a^p - sigK a‖ ≤ ‖(p : L.K)‖`. -/
theorem pow_sub_sigK_le {a : L.K} (ha : ‖a‖ ≤ 1) :
    ‖a ^ p - Φ.sigK a‖ ≤ ‖(p : L.K)‖ := by
  rw [show a ^ p - Φ.sigK a = -(Φ.sigK a - a ^ p) by ring, norm_neg]
  exact Φ.sigK_sub_pow_le ha

/-- `sigK` preserves the closed unit ball `‖a‖ ≤ 1`. -/
theorem sigK_norm_le_one {a : L.K} (ha : ‖a‖ ≤ 1) : ‖Φ.sigK a‖ ≤ 1 := by
  obtain ⟨w, rfl⟩ := (L.norm_le_one_iff a).mp ha
  rw [Φ.commutes w]
  exact L.toField_norm_le_one _

@[simp] theorem sigK_p : Φ.sigK (p : L.K) = (p : L.K) := map_natCast Φ.sigK p

theorem sigK_iterate_commutes (m : ℕ) (w : L.W) :
    (Φ.sigK)^[m] (L.toField w) = L.toField ((Φ.sigW)^[m] w) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Φ.commutes]

theorem sigK_norm_le_p_pow {n : ℕ} {a : L.K} (ha : ‖a‖ ≤ ((p : ℝ)⁻¹) ^ n) :
    ‖Φ.sigK a‖ ≤ ((p : ℝ)⁻¹) ^ n := by
  obtain ⟨w, rfl⟩ := (L.norm_le_p_pow_iff n a).mp ha
  rw [L.norm_le_p_pow_iff]
  refine ⟨Φ.sigW w, ?_⟩
  rw [map_mul, map_pow, map_natCast, Φ.commutes]

end FrobSigK

/-! ### Concrete Realization 1: `ℤ_[p] ↪ ℚ_[p]` (Trivial Frobenius `σ = id`) -/

/-- Concrete `WittRingLift p` for `ℤ_[p] ↪ ℚ_[p]`. -/
@[reducible]
def padicWittRingLift (p : ℕ) [Fact p.Prime] : WittRingLift p where
  W := ℤ_[p]
  K := ℚ_[p]
  toField := algebraMap ℤ_[p] ℚ_[p]
  toField_injective := Subtype.val_injective
  norm_p := Padic.norm_p
  norm_le_one_iff x := by
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact w.2
  norm_le_p_pow_iff n x := by
    have hp : p.Prime := Fact.out
    have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    constructor
    · intro hx
      have hy : ‖x / (p : ℚ_[p]) ^ n‖ ≤ 1 := by
        rw [norm_div, norm_pow, Padic.norm_p]
        exact div_le_one_of_le₀ hx (by positivity)
      refine ⟨⟨x / (p : ℚ_[p]) ^ n, hy⟩, ?_⟩
      change x = (p : ℚ_[p]) ^ n * (x / (p : ℚ_[p]) ^ n)
      exact (mul_div_cancel₀ x (pow_ne_zero n hp_ne)).symm
    · rintro ⟨w, rfl⟩
      rw [norm_mul, norm_pow, Padic.norm_p]
      exact mul_le_of_le_one_right (by positivity) w.2

/-- Concrete `FrobSigK p` on `ℤ_[p] ↪ ℚ_[p]` with identity Frobenius `σ = id`. -/
def padicFrobSigK (p : ℕ) [Fact p.Prime] : FrobSigK p (padicWittRingLift p) where
  sigW := RingHom.id ℤ_[p]
  sigK := RingEquiv.refl ℚ_[p]
  commutes _ := rfl
  frob_congr_W := by
    intro (w : ℤ_[p])
    have hnorm : ‖(w : ℚ_[p]) - (w : ℚ_[p]) ^ p‖ ≤ ‖(p : ℚ_[p])‖ := by
      rw [show (w : ℚ_[p]) - (w : ℚ_[p]) ^ p = -((w : ℚ_[p]) ^ p - (w : ℚ_[p])) by ring, norm_neg]
      exact padic_pow_prime_sub_le p w.2
    rw [Padic.norm_p] at hnorm
    obtain ⟨y, hy⟩ := ((padicWittRingLift p).norm_le_inv_iff _).mp hnorm
    refine ⟨y, Subtype.ext ?_⟩
    change (w : ℚ_[p]) - (w : ℚ_[p]) ^ p = (p : ℚ_[p]) * (y : ℚ_[p])
    exact hy

/-! ### Concrete Realization 2: Witt Vectors `WittVector p k ↪ FractionRing (WittVector p k)` & `WW p ↪ K0 p` -/

section ConcreteWittVectors

variable (p : ℕ) [hp : Fact p.Prime]

/-- Algebraic closure `k̄ = AlgebraicClosure (ZMod p)` of `𝔽_p`. -/
abbrev kb : Type := AlgebraicClosure (ZMod p)

/-- Concrete ring of Witt vectors `WW p := W(k̄) = WittVector p (AlgebraicClosure (ZMod p))`. -/
abbrev WW : Type := WittVector p (kb p)

/-- Concrete fraction field `K0 p := FractionRing (WW p) = W(k̄)[1/p]`. -/
abbrev K0 : Type := FractionRing (WW p)

/-- Witt-vector Frobenius endomorphism `sigW p : WW p →+* WW p`. -/
@[reducible]
def sigW : WW p →+* WW p := WittVector.frobenius

/-- Witt-vector Frobenius automorphism `sigK p : K0 p ≃+* K0 p` on `K0 p = FractionRing (WW p)`. -/
@[reducible]
def sigK : K0 p ≃+* K0 p :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (kb p))

section GeneralPerfectFieldWitt

variable (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

omit [PerfectRing k p] in
/-- Characteristic zero for `WittVector p k` over any perfect field `k` of characteristic `p`. -/
theorem wittVector_charZero : CharZero (WittVector p k) := by
  refine ⟨fun a b hab => ?_⟩
  by_contra hne
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm (Ne.symm hne) (lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hne))
  set n : ℕ := b - a
  have hn_ne : n ≠ 0 := by omega
  have hcast_zero : (n : WittVector p k) = 0 := by
    have hba : (b : WittVector p k) = (a : WittVector p k) + (n : WittVector p k) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hlt.le]
    rw [hab] at hba
    exact add_left_cancel (hba.symm.trans (add_zero _).symm)
  obtain ⟨m, hm, hnd⟩ : ∃ m, n = p ^ padicValNat p n * m ∧ ¬ p ∣ m := by
    obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := p) (n := n)
    refine ⟨m, hm, fun hpm => ?_⟩
    obtain ⟨r, rfl⟩ := hpm
    have hd' : p ^ (padicValNat p n + 1) ∣ n :=
      ⟨r, by calc n = p ^ padicValNat p n * (p * r) := hm
        _ = p ^ (padicValNat p n + 1) * r := by rw [pow_succ]; ring⟩
    have hle := (padicValNat_dvd_iff_le hn_ne).mp hd'
    omega
  rw [hm, Nat.cast_mul, Nat.cast_pow, mul_eq_zero] at hcast_zero
  rcases hcast_zero with hpow | hm0
  · exact pow_ne_zero _ (WittVector.p_nonzero p k) hpow
  · have hcc := congrArg (WittVector.constantCoeff (p := p) (R := k)) hm0
    simp only [map_natCast, map_zero] at hcc
    exact hnd ((CharP.cast_eq_zero_iff k p m).mp hcc)

/-- `WittVector p k` has `1 < p` in `ℝ≥0` for constructing its `p`-adic absolute value. -/
theorem one_lt_p_nnreal : (1 : ℝ≥0) < (p : ℝ≥0) := by
  exact_mod_cast hp.out.one_lt

/-- Explicit unique height-one prime spectrum `(p) ⊆ WittVector p k`. -/
def wittMaxSpectrum : HeightOneSpectrum (WittVector p k) where
  asIdeal := Ideal.span {(p : WittVector p k)}
  isPrime :=
    (Ideal.span_singleton_prime (WittVector.p_nonzero p k)).mpr (WittVector.irreducible p).prime
  ne_bot := mt Ideal.span_singleton_eq_bot.mp (WittVector.p_nonzero p k)

/-- Normalized `p`-adic absolute value on `FractionRing (WittVector p k)` induced by `(p)`,
normalized so `wittAbvOn p k p = p⁻¹`. -/
def wittAbvOn : AbsoluteValue (FractionRing (WittVector p k)) ℝ :=
  (wittMaxSpectrum p k).adicAbv (one_lt_p_nnreal p)

theorem wittAbvOn_nonarch : IsNonarchimedean (wittAbvOn p k) :=
  isNonarchimedean_adicAbv (wittMaxSpectrum p k) (one_lt_p_nnreal p)

theorem wittAbvOn_coe_le_one (w : WittVector p k) :
    wittAbvOn p k (algebraMap (WittVector p k) (FractionRing (WittVector p k)) w) ≤ 1 :=
  adicAbv_coe_le_one (wittMaxSpectrum p k) (one_lt_p_nnreal p) w

private theorem toNNReal_exp_eq {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  have h : WithZero.exp n = ((Multiplicative.ofAdd n : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) := rfl
  rw [h, WithZeroMulInt.toNNReal_neg_apply he WithZero.coe_ne_zero, WithZero.unzero_coe]
  rfl

theorem wittAbvOn_p :
    wittAbvOn p k (p : FractionRing (WittVector p k)) = (p : ℝ)⁻¹ := by
  have h : (p : FractionRing (WittVector p k)) =
      algebraMap (WittVector p k) (FractionRing (WittVector p k)) (p : WittVector p k) := by simp
  rw [h, wittAbvOn, adicAbv_of_algebraMap]
  have h2 := intValuation_singleton (wittMaxSpectrum p k) (WittVector.p_nonzero p k) rfl
  simp only [intAdicAbv, intAdicAbvDef, AbsoluteValue.coe_mk, MulHom.coe_mk, h2]
  rw [toNNReal_exp_eq]
  simp

theorem wittAbvOn_unit (u : (WittVector p k)ˣ) :
    wittAbvOn p k (algebraMap (WittVector p k) (FractionRing (WittVector p k)) (u : WittVector p k)) = 1 := by
  refine (adicAbv_coe_eq_one_iff (wittMaxSpectrum p k) (one_lt_p_nnreal p) (u : WittVector p k)).2 ?_
  intro hmem
  exact (wittMaxSpectrum p k).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)

theorem wittFrac_p_ne_zero : (p : FractionRing (WittVector p k)) ≠ 0 := by
  intro h
  have h1 := wittAbvOn_p p k
  rw [h, map_zero] at h1
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
    positivity
  exact hpos.ne h1

theorem wittFrac_exists_pow_unit (x : FractionRing (WittVector p k)) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : (WittVector p k)ˣ),
      x = (p : FractionRing (WittVector p k)) ^ n *
        algebraMap (WittVector p k) (FractionRing (WittVector p k)) (u : WittVector p k) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := WittVector p k) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, a', rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
  obtain ⟨n, b', rfl⟩ := WittVector.exists_eq_pow_p_mul' b hb0
  refine ⟨(m : ℤ) - n, a' * b'⁻¹, ?_⟩
  have hp0 := wittFrac_p_ne_zero p k
  have h1 : algebraMap (WittVector p k) (FractionRing (WittVector p k)) (b' : WittVector p k) *
      algebraMap (WittVector p k) (FractionRing (WittVector p k))
        ((b'⁻¹ : (WittVector p k)ˣ) : WittVector p k) = 1 := by
    rw [← map_mul]; simp
  have h2 : algebraMap (WittVector p k) (FractionRing (WittVector p k))
      ((b'⁻¹ : (WittVector p k)ˣ) : WittVector p k) =
      (algebraMap (WittVector p k) (FractionRing (WittVector p k)) (b' : WittVector p k))⁻¹ :=
    eq_inv_of_mul_eq_one_right h1
  rw [zpow_sub₀ hp0, Units.val_mul, map_mul, map_mul, map_mul, h2, map_pow, map_pow, map_natCast,
    zpow_natCast, zpow_natCast]
  field_simp

theorem wittAbvOn_value (x : FractionRing (WittVector p k)) (hx : x ≠ 0) :
    ∃ m : ℤ, wittAbvOn p k x = (p : ℝ) ^ m := by
  obtain ⟨n, u, rfl⟩ := wittFrac_exists_pow_unit p k x hx
  refine ⟨-n, ?_⟩
  rw [map_mul, map_zpow₀, wittAbvOn_p, wittAbvOn_unit, mul_one, inv_zpow, zpow_neg]

theorem wittAbvOn_le_one_iff (x : FractionRing (WittVector p k)) :
    wittAbvOn p k x ≤ 1 ↔
      ∃ w : WittVector p k, algebraMap (WittVector p k) (FractionRing (WittVector p k)) w = x := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact ⟨0, by rw [hx0, map_zero]⟩
    · obtain ⟨n, u, rfl⟩ := wittFrac_exists_pow_unit p k x hx0
      have hval : wittAbvOn p k ((p : FractionRing (WittVector p k)) ^ n *
          algebraMap (WittVector p k) (FractionRing (WittVector p k)) (u : WittVector p k)) =
          (p : ℝ) ^ (-n) := by
        rw [map_mul, map_zpow₀, wittAbvOn_p, wittAbvOn_unit, mul_one, inv_zpow, zpow_neg]
      rw [hval] at hx
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
      have hn_nonneg : 0 ≤ n := by
        by_contra hlt
        push Not at hlt
        have hpos : 0 < -n := by omega
        have hgt : (1 : ℝ) < (p : ℝ) ^ (-n) := one_lt_zpow₀ hp1 hpos
        exact not_lt_of_ge hx hgt
      lift n to ℕ using hn_nonneg
      refine ⟨(p : WittVector p k) ^ n * (u : WittVector p k), ?_⟩
      rw [map_mul, map_pow, map_natCast, zpow_natCast]
  · rintro ⟨w, rfl⟩
    exact wittAbvOn_coe_le_one p k w

theorem wittAbvOn_le_pow_iff (n : ℕ) (x : FractionRing (WittVector p k)) :
    wittAbvOn p k x ≤ ((p : ℝ)⁻¹) ^ n ↔
      ∃ w : WittVector p k,
        x = (p : FractionRing (WittVector p k)) ^ n *
          algebraMap (WittVector p k) (FractionRing (WittVector p k)) w := by
  have hp0 := wittFrac_p_ne_zero p k
  have hpos : (0 : ℝ) < ((p : ℝ)⁻¹) ^ n := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
    positivity
  constructor
  · intro hx
    have hdiv : wittAbvOn p k (x / (p : FractionRing (WittVector p k)) ^ n) ≤ 1 := by
      rw [map_div₀, map_pow, wittAbvOn_p]
      exact div_le_one_of_le₀ hx hpos.le
    obtain ⟨w, hw⟩ := (wittAbvOn_le_one_iff p k _).mp hdiv
    refine ⟨w, ?_⟩
    rw [hw, mul_div_cancel₀ x (pow_ne_zero n hp0)]
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_pow, wittAbvOn_p]
    exact mul_le_of_le_one_right hpos.le (wittAbvOn_coe_le_one p k w)

/-- Integral Frobenius congruence on `WittVector p k`:
for every `w : WittVector p k`, `WittVector.frobenius w - w ^ p = p * y` for some `y`. -/
theorem wittVector_frob_sub_pow (w : WittVector p k) :
    ∃ y : WittVector p k, WittVector.frobenius w - w ^ p = (p : WittVector p k) * y := by
  have h : WittVector.frobenius w - w ^ p ∈ Ideal.span {(p : WittVector p k)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    show WittVector.constantCoeff (WittVector.frobenius w - w ^ p) = 0
    rw [map_sub, map_pow]
    show (WittVector.frobenius w).coeff 0 - (w.coeff 0) ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  exact Ideal.mem_span_singleton.1 h

/-- Local `NormedField` on `FractionRing (WittVector p k)` induced by `wittAbvOn p k`.
Marked `@[instance_reducible]` (never a global `instance`) so its `Field`/`CommRing` projections
are definitionally equal to `OreLocalization.instField` / `OreLocalization.instCommRing`! -/
@[instance_reducible]
def wittNormedFieldOn : NormedField (FractionRing (WittVector p k)) :=
  normedFieldOfAbv (wittAbvOn p k)

theorem wittUltraOn :
    letI := wittNormedFieldOn p k
    IsUltrametricDist (FractionRing (WittVector p k)) := by
  let _ : NormedField (FractionRing (WittVector p k)) := wittNormedFieldOn p k
  exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
    wittAbvOn_nonarch p k x y

/-- Completeness of `FractionRing (WittVector p k)` under `wittNormedFieldOn p k`,
proved directly from `WittVector.isAdicCompleteIdealSpanP`. -/
theorem wittCompleteOn :
    letI := wittNormedFieldOn p k
    CompleteSpace (FractionRing (WittVector p k)) := by
  let _ : NormedField (FractionRing (WittVector p k)) := wittNormedFieldOn p k
  have _ : IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) :=
    WittVector.isAdicCompleteIdealSpanP
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have := hp.out.pos
    positivity
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => ((p : ℝ)⁻¹) ^ n)
    (fun n => pow_pos hpos n) ?_
  intro u hu
  have h0 : ∀ n, ∃ w : WittVector p k,
      algebraMap (WittVector p k) (FractionRing (WittVector p k)) w = u n - u 0 := fun n =>
    (wittAbvOn_le_one_iff p k _).1 (by
      have h : dist (u n) (u 0) < ((p : ℝ)⁻¹) ^ 0 := hu 0 n 0 (Nat.zero_le _) le_rfl
      rw [pow_zero] at h
      exact h.le)
  choose w hw using h0
  have hc : ∀ {m n}, m ≤ n →
      w m ≡ w n [SMOD (Ideal.span {(p : WittVector p k)} ^ m • ⊤ :
        Submodule (WittVector p k) (WittVector p k))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    have h := (hu m m n le_rfl hmn).le
    obtain ⟨y, hy⟩ := (wittAbvOn_le_pow_iff p k m _).1 h
    refine ⟨y, ?_⟩
    apply IsFractionRing.injective (WittVector p k) (FractionRing (WittVector p k))
    rw [map_sub, hw, hw, map_mul, map_pow, map_natCast, ← hy]
    ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : WittVector p k)}) w hc
  refine ⟨u 0 + algebraMap (WittVector p k) (FractionRing (WittVector p k)) L, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)
  change wittAbvOn p k _ ≤ _
  rw [wittAbvOn_le_pow_iff]
  have hn := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hn
  obtain ⟨y, hy⟩ := hn
  refine ⟨y, ?_⟩
  rw [← map_natCast (algebraMap (WittVector p k) (FractionRing (WittVector p k))), ← map_pow,
    ← map_mul, ← hy, map_sub, hw]
  ring

/-- Concrete `WittRingLift p` for `WittVector p k ↪ FractionRing (WittVector p k)` over ANY
perfect field `k` of characteristic `p`. -/
@[reducible]
def wittVectorRingLift : WittRingLift p where
  W := WittVector p k
  K := FractionRing (WittVector p k)
  charZeroW := wittVector_charZero p k
  normedFieldK := wittNormedFieldOn p k
  ultraK := wittUltraOn p k
  charZeroK := by
    have _ := wittVector_charZero p k
    exact charZero_of_injective_algebraMap (IsFractionRing.injective (WittVector p k) _)
  toField := algebraMap (WittVector p k) (FractionRing (WittVector p k))
  toField_injective := IsFractionRing.injective (WittVector p k) _
  norm_p := wittAbvOn_p p k
  norm_le_one_iff := wittAbvOn_le_one_iff p k
  norm_le_p_pow_iff := wittAbvOn_le_pow_iff p k

/-- Concrete `FrobSigK p` on `WittVector p k ↪ FractionRing (WittVector p k)` using Mathlib's
`WittVector.frobenius` and `IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p k)`. -/
@[reducible]
def wittVectorFrobSigK : FrobSigK p (wittVectorRingLift p k) where
  sigW := WittVector.frobenius
  sigK := IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p k)
  commutes w := by
    exact IsLocalization.ringEquivOfRingEquiv_eq _ w
  frob_congr_W := wittVector_frob_sub_pow p k

end GeneralPerfectFieldWitt

/-- Concrete `WittRingLift p` specialized to `WW p = WittVector p (AlgebraicClosure (ZMod p))`
and `K0 p = FractionRing (WW p)`. -/
@[reducible]
def concreteWittRingLift : WittRingLift p :=
  wittVectorRingLift p (kb p)

/-- Concrete `FrobSigK p` specialized to `WW p`, `K0 p`, `sigW p`, and `sigK p`. -/
@[reducible]
def concreteFrobSigK : FrobSigK p (concreteWittRingLift p) :=
  wittVectorFrobSigK p (kb p)

/-- Normalized `p`-adic absolute value on `K0 p`. -/
@[reducible]
def wittAbv : AbsoluteValue (K0 p) ℝ :=
  wittAbvOn p (kb p)

/-- Local `NormedField (K0 p)` (`@[instance_reducible]`, never a global instance). -/
@[instance_reducible]
def wittNormedField : NormedField (K0 p) :=
  wittNormedFieldOn p (kb p)

theorem wittAbv_p : wittAbv p (p : K0 p) = (p : ℝ)⁻¹ :=
  wittAbvOn_p p (kb p)

theorem wittAbv_nonarch : IsNonarchimedean (wittAbv p) :=
  wittAbvOn_nonarch p (kb p)

theorem wittAbv_le_one_iff (x : K0 p) :
    wittAbv p x ≤ 1 ↔ ∃ w : WW p, algebraMap (WW p) (K0 p) w = x :=
  wittAbvOn_le_one_iff p (kb p) x

theorem wittAbv_le_pow_iff (n : ℕ) (x : K0 p) :
    wittAbv p x ≤ ((p : ℝ)⁻¹) ^ n ↔ ∃ w : WW p, x = (p : K0 p) ^ n * algebraMap (WW p) (K0 p) w :=
  wittAbvOn_le_pow_iff p (kb p) n x

theorem sigK_coe (w : WW p) :
    sigK p (algebraMap (WW p) (K0 p) w) = algebraMap (WW p) (K0 p) (sigW p w) :=
  (concreteFrobSigK p).commutes w

theorem wittAbv_sig (a : K0 p) (ha : wittAbv p a ≤ 1) :
    wittAbv p (sigK p a - a ^ p) ≤ (p : ℝ)⁻¹ := by
  have h := (concreteFrobSigK p).sigK_sub_pow_le (a := a) ha
  rw [← wittAbv_p p]
  exact h

theorem witt_complete :
    letI := wittNormedField p
    CompleteSpace (K0 p) :=
  wittCompleteOn p (kb p)

/-- Teichmüller lift intertwines `sigW` with the `p`-th power:
`sigW p (teichmuller p x) = (teichmuller p x) ^ p`. -/
theorem sigW_teichmuller (x : kb p) :
    sigW p (WittVector.teichmuller p x) = (WittVector.teichmuller p x) ^ p := by
  have hpow : (WittVector.teichmuller p x) ^ p = WittVector.teichmuller p (x ^ p) :=
    (map_pow (WittVector.teichmuller p) x p).symm
  rw [hpow]
  ext n
  rw [sigW, WittVector.coeff_frobenius_charP]
  cases n with
  | zero => simp only [WittVector.teichmuller_coeff_zero]
  | succ n =>
    simp only [WittVector.teichmuller_coeff_pos _ _ _ (Nat.succ_pos n), zero_pow hp.out.ne_zero]

/-- Iterated `sigW` on a Teichmüller lift: `(sigW p)^[m] (teichmuller p x) = teichmuller p (x^(p^m))`. -/
theorem sigW_iterate_teichmuller (m : ℕ) (x : kb p) :
    (sigW p)^[m] (WittVector.teichmuller p x) = WittVector.teichmuller p (x ^ (p ^ m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, sigW_teichmuller, ← map_pow (WittVector.teichmuller p),
      ← pow_mul, ← pow_succ]

/-- **Fontaine `A_inf` Frobenius Lift Bridge** (connecting to `RHDirect.Stage12FontainePeriods`):
for any `p`-adically complete base `O` with `¬ IsUnit (p : O)`, the Witt-vector Frobenius on
Fontaine's `A_inf p O = WittVector p (Tilt p O)` satisfies `σ(x) ≡ x^p (mod p)`! -/
theorem ainf_frob_congr_p {O : Type*} [CommRing O] [Fact ¬IsUnit ((p : ℕ) : O)]
    (x : A_inf p O) :
    ∃ y : A_inf p O, WittVector.frobenius x - x ^ p = (p : A_inf p O) * y := by
  have h : WittVector.frobenius x - x ^ p ∈ Ideal.span {(p : A_inf p O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow]
    show (WittVector.frobenius x).coeff 0 - (x.coeff 0) ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  exact Ideal.mem_span_singleton.mp h

end ConcreteWittVectors

end WittRingLiftCore

/-! ## Section 2: `dwork_multivariable_witt` — Multivariable Dwork Integrality Lemma over `WittRingLift p` -/

section MultivarDworkWitt

variable {σ : Type*} {p : ℕ} [hp : Fact p.Prime]

/-- Ring-level integrality over `L : WittRingLift p`:
`f : MvPowerSeries σ L.K` lies in the image of `MvPowerSeries σ L.W` under `MvPowerSeries.map L.toField`. -/
def IntSMv (L : WittRingLift p) (f : MvPowerSeries σ L.K) : Prop :=
  ∃ g : MvPowerSeries σ L.W, f = MvPowerSeries.map L.toField g

/-- Ring-level congruence `f ∈ 1 + p · W[[X]]` over `L : WittRingLift p`:
`constantCoeff f = 1` and `f - 1 = p · map L.toField q` for some `q ∈ W[[X]]`. -/
def CongOneModPWitt (L : WittRingLift p) (f : MvPowerSeries σ L.K) : Prop :=
  MvPowerSeries.constantCoeff f = 1 ∧
    ∃ q : MvPowerSeries σ L.W,
      f - 1 = MvPowerSeries.C (p : L.K) * MvPowerSeries.map L.toField q

/-- Explicit `RingHom` Frobenius action `f ↦ f^σ(X^p)` on `MvPowerSeries σ L.K`. -/
def wittFrobMap {L : WittRingLift p} (Φ : FrobSigK p L) :
    MvPowerSeries σ L.K →+* MvPowerSeries σ L.K :=
  frobMapMv Φ.sigK.toRingHom p hp.out.pos

/-- Explicit `RingHom` Frobenius action `g ↦ g^{sigW}(X^p)` on `MvPowerSeries σ L.W`. -/
def wittFrobMapW {L : WittRingLift p} (Φ : FrobSigK p L) :
    MvPowerSeries σ L.W →+* MvPowerSeries σ L.W :=
  frobMapMv Φ.sigW p hp.out.pos

@[simp] theorem coeff_wittFrobMap_nsmul {L : WittRingLift p} (Φ : FrobSigK p L)
    (f : MvPowerSeries σ L.K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff (p • d) (wittFrobMap Φ f) = Φ.sigK (MvPowerSeries.coeff d f) :=
  coeff_frobMapMv_nsmul Φ.sigK.toRingHom hp.out.pos f d

@[simp] theorem constantCoeff_wittFrobMap {L : WittRingLift p} (Φ : FrobSigK p L)
    (f : MvPowerSeries σ L.K) :
    MvPowerSeries.constantCoeff (wittFrobMap Φ f) = Φ.sigK (MvPowerSeries.constantCoeff f) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : σ →₀ ℕ) = p • (0 : σ →₀ ℕ) by simp,
    coeff_wittFrobMap_nsmul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem wittFrobMap_map_toField {L : WittRingLift p} (Φ : FrobSigK p L)
    (g : MvPowerSeries σ L.W) :
    wittFrobMap Φ (MvPowerSeries.map L.toField g) =
      MvPowerSeries.map L.toField (wittFrobMapW Φ g) := by
  classical
  ext d
  simp only [wittFrobMap, wittFrobMapW, MvPowerSeries.coeff_map, coeff_frobMapMv_eq_ite]
  split_ifs
  · exact Φ.commutes _
  · simp

/-- Equivalence between ring-level integrality `IntSMv L f` and ultrametric `IsIntegralMv f`. -/
theorem intSMv_iff_isIntegralMv (L : WittRingLift p) (f : MvPowerSeries σ L.K) :
    IntSMv L f ↔ IsIntegralMv f := by
  constructor
  · rintro ⟨g, rfl⟩ d
    rw [MvPowerSeries.coeff_map]
    exact L.toField_norm_le_one _
  · intro hf
    choose g hg using fun d => (L.norm_le_one_iff (MvPowerSeries.coeff d f)).mp (hf d)
    let G : MvPowerSeries σ L.W := fun d => g d
    refine ⟨G, ?_⟩
    exact MvPowerSeries.ext fun d => (hg d).symm

/-- Equivalence between coefficient norm bound `≤ ‖p‖` and ring-level `p`-divisibility
`f = C p * map L.toField q`. -/
theorem div_p_mv_iff (L : WittRingLift p) (f : MvPowerSeries σ L.K) :
    CoeffNormLeMv ‖(p : L.K)‖ f ↔
      ∃ q : MvPowerSeries σ L.W,
        f = MvPowerSeries.C (p : L.K) * MvPowerSeries.map L.toField q := by
  constructor
  · intro hf
    choose q hq using fun d => (L.norm_le_norm_p_iff (MvPowerSeries.coeff d f)).mp (hf d)
    let Q : MvPowerSeries σ L.W := fun d => q d
    refine ⟨Q, ?_⟩
    exact MvPowerSeries.ext fun d => by
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map]
      exact hq d
  · rintro ⟨q, rfl⟩ d
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map]
    exact (L.norm_le_norm_p_iff _).mpr ⟨MvPowerSeries.coeff d q, rfl⟩

/-- Equivalence between ring-level `CongOneModPWitt L f` and ultrametric `CongOneModPMv p f`. -/
theorem congOneModPWitt_iff_congOneModPMv (L : WittRingLift p) (f : MvPowerSeries σ L.K) :
    CongOneModPWitt L f ↔ CongOneModPMv p f := by
  classical
  constructor
  · rintro ⟨hf0, q, hq⟩
    refine ⟨hf0, fun d hd => ?_⟩
    have hcoeff := (div_p_mv_iff L (f - 1)).mpr ⟨q, hq⟩ d
    rwa [map_sub, MvPowerSeries.coeff_one, if_neg hd, sub_zero] at hcoeff
  · rintro ⟨hf0, hf⟩
    refine ⟨hf0, (div_p_mv_iff L (f - 1)).mp fun d => ?_⟩
    rw [map_sub, MvPowerSeries.coeff_one]
    by_cases hd0 : d = 0
    · subst hd0
      rw [if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [if_neg hd0, sub_zero]
      exact hf d hd0

omit hp in
/-- `CongOneModPMv p` is closed under multiplicative inversion `invOneMv`. -/
theorem congOneModPMv_invOneMv {K : Type*} [NormedField K] [IsUltrametricDist K]
    {G : MvPowerSeries σ K} (hG : CongOneModPMv p G) :
    CongOneModPMv p (invOneMv G) := by
  classical
  have hp0 : 0 ≤ ‖(p : K)‖ := norm_nonneg _
  have hG_int : IsIntegralMv G := fun d => by
    by_cases hd0 : d = 0
    · subst hd0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG.1, norm_one]
    · exact (hG.2 d hd0).trans (norm_natCast_le_one p)
  have hinv_int : IsIntegralMv (invOneMv G) := isIntegralMv_invOneMv hG.1 hG_int
  have hG1 : CoeffNormLeMv ‖(p : K)‖ (G - 1) := fun d => by
    rw [map_sub, MvPowerSeries.coeff_one]
    by_cases hd0 : d = 0
    · subst hd0
      rw [if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG.1, sub_self, norm_zero]
      exact hp0
    · rw [if_neg hd0, sub_zero]
      exact hG.2 d hd0
  refine ⟨constantCoeff_invOneMv hG.1, fun d hd => ?_⟩
  have hdiff : invOneMv G - 1 = -(G - 1) * invOneMv G := by
    rw [neg_mul, sub_mul, one_mul, mul_invOneMv hG.1]
    ring
  have hprod := coeffNormLeMv_mul hp0 zero_le_one (coeffNormLeMv_neg hG1) hinv_int d
  rw [mul_one, ← hdiff, map_sub, MvPowerSeries.coeff_one, if_neg hd, sub_zero] at hprod
  exact hprod

/-- **Dual Orientation of Multivariable Dwork Lemma over `WittRingLift p`**:
`f ∈ W[[X]] ↔ f^σ(X^p) / f(X)^p ∈ 1 + p · W[[X]]`. -/
theorem dwork_multivariable_witt_dual {L : WittRingLift p} (Φ : FrobSigK p L)
    {f : MvPowerSeries σ L.K} (hf0 : MvPowerSeries.constantCoeff f = 1) :
    IntSMv L f ↔ CongOneModPWitt L (wittFrobMap Φ f * (invOneMv f) ^ p) := by
  rw [intSMv_iff_isIntegralMv, congOneModPWitt_iff_congOneModPMv]
  exact dieudonne_dwork_mv_iff hp.out Φ.sigK.toRingHom (fun _ hc => Φ.pow_sub_sigK_le hc) hf0

/-- **Multivariable Dwork Integrality Lemma over `WittRingLift p` (`dwork_multivariable_witt`)**:
for any `L : WittRingLift p`, Frobenius lift `Φ : FrobSigK p L`, arbitrary index type `σ`, and
`f : MvPowerSeries σ L.K` with `constantCoeff f = 1`:
`f ∈ W[[X]]  ↔  f(X)^p / f^σ(X^p) ∈ 1 + p · W[[X]]`! -/
theorem dwork_multivariable_witt {L : WittRingLift p} (Φ : FrobSigK p L)
    {f : MvPowerSeries σ L.K} (hf0 : MvPowerSeries.constantCoeff f = 1) :
    IntSMv L f ↔ CongOneModPWitt L (f ^ p * invOneMv (wittFrobMap Φ f)) := by
  rw [dwork_multivariable_witt_dual Φ hf0, congOneModPWitt_iff_congOneModPMv,
    congOneModPWitt_iff_congOneModPMv]
  set G := wittFrobMap Φ f * (invOneMv f) ^ p
  set H := f ^ p * invOneMv (wittFrobMap Φ f)
  have hwf0 : MvPowerSeries.constantCoeff (wittFrobMap Φ f) = 1 := by
    rw [constantCoeff_wittFrobMap, hf0, map_one]
  have hG0 : MvPowerSeries.constantCoeff G = 1 := by
    simp [G, hwf0, constantCoeff_invOneMv hf0]
  have hH0 : MvPowerSeries.constantCoeff H = 1 := by
    simp [H, hf0, constantCoeff_invOneMv hwf0]
  have hGH : G * H = 1 := by
    dsimp only [G, H]
    calc wittFrobMap Φ f * (invOneMv f) ^ p * (f ^ p * invOneMv (wittFrobMap Φ f))
        = (wittFrobMap Φ f * invOneMv (wittFrobMap Φ f)) * ((invOneMv f * f) ^ p) := by
            rw [mul_pow]; ring
      _ = 1 * 1 ^ p := by rw [mul_invOneMv hwf0, invOneMv_mul hf0]
      _ = 1 := by simp
  have hH_eq : H = invOneMv G := by
    calc H = 1 * H := (one_mul H).symm
      _ = (invOneMv G * G) * H := by rw [invOneMv_mul hG0]
      _ = invOneMv G * (G * H) := mul_assoc _ _ _
      _ = invOneMv G := by rw [hGH, mul_one]
  have hG_eq : G = invOneMv H := by
    calc G = G * 1 := (mul_one G).symm
      _ = G * (H * invOneMv H) := by rw [mul_invOneMv hH0]
      _ = (G * H) * invOneMv H := (mul_assoc _ _ _).symm
      _ = invOneMv H := by rw [hGH, one_mul]
  constructor
  · intro hG
    rw [hH_eq]
    exact congOneModPMv_invOneMv hG
  · intro hH
    rw [hG_eq]
    exact congOneModPMv_invOneMv hH

/-- Division-free form of `dwork_multivariable_witt`:
`f ∈ W[[X]] ↔ ∃ G ∈ 1 + p · W[[X]], f(X)^p = G · f^σ(X^p)`. -/
theorem dwork_multivariable_witt_exists {L : WittRingLift p} (Φ : FrobSigK p L)
    {f : MvPowerSeries σ L.K} (hf0 : MvPowerSeries.constantCoeff f = 1) :
    IntSMv L f ↔
      ∃ G : MvPowerSeries σ L.K, CongOneModPWitt L G ∧ f ^ p = G * wittFrobMap Φ f := by
  have hwf0 : MvPowerSeries.constantCoeff (wittFrobMap Φ f) = 1 := by
    rw [constantCoeff_wittFrobMap, hf0, map_one]
  rw [dwork_multivariable_witt Φ hf0]
  constructor
  · intro h
    refine ⟨f ^ p * invOneMv (wittFrobMap Φ f), h, ?_⟩
    rw [mul_assoc, invOneMv_mul hwf0, mul_one]
  · rintro ⟨G, hG, heq⟩
    have hEq : f ^ p * invOneMv (wittFrobMap Φ f) = G := by
      rw [heq, mul_assoc, mul_invOneMv hwf0, mul_one]
    rwa [hEq]

/-- Concrete `WW p` / `K0 p` / `sigK p` specialization of `dwork_multivariable_witt`. -/
theorem dwork_multivariable_WW (p : ℕ) [Fact p.Prime] {f : MvPowerSeries σ (K0 p)}
    (hf0 : MvPowerSeries.constantCoeff f = 1) :
    IntSMv (concreteWittRingLift p) f ↔
      CongOneModPWitt (concreteWittRingLift p)
        (f ^ p * invOneMv (wittFrobMap (concreteFrobSigK p) f)) :=
  dwork_multivariable_witt (concreteFrobSigK p) hf0

/-! ### Formal Exponential `expSMv` & Exponential Multivariable Dwork Lemma -/

section ExpMultivarDwork

/-- Explicit formal exponential on `MvPowerSeries σ K`:
`coeff d (expSMv f) = ∑_{k=0}^{d.degree} (k!)⁻¹ * coeff d (f^k)`. -/
def expSMv {K : Type*} [Field K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun d => ∑ k ∈ Finset.range (d.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff d (f ^ k)

theorem coeff_expSMv {K : Type*} [Field K] (f : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (expSMv f) =
      ∑ k ∈ Finset.range (d.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff d (f ^ k) :=
  rfl

@[simp] theorem constantCoeff_expSMv {K : Type*} [Field K] (f : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (expSMv f) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expSMv]
  simp

theorem expSMv_zero {K : Type*} [Field K] :
    expSMv (0 : MvPowerSeries σ K) = 1 := by
  classical
  exact MvPowerSeries.ext fun d => by
    rw [coeff_expSMv, MvPowerSeries.coeff_one]
    by_cases hd0 : d = 0
    · subst hd0; simp
    · rw [if_neg hd0]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases k with _ | k
      · rw [pow_zero, MvPowerSeries.coeff_one, if_neg hd0, mul_zero]
      · rw [zero_pow (Nat.succ_ne_zero k), map_zero, mul_zero]

theorem coeff_expSMv_eq_sum_of_ge {K : Type*} [Field K] {f : MvPowerSeries σ K}
    (hf0 : MvPowerSeries.constantCoeff f = 0) {d : σ →₀ ℕ} {M : ℕ} (hM : d.degree ≤ M) :
    MvPowerSeries.coeff d (expSMv f) =
      ∑ k ∈ Finset.range (M + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff d (f ^ k) := by
  have hlow1 : LowDeg 1 f := lowDeg_one_of_constantCoeff_zero hf0
  rw [coeff_expSMv]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hM)) fun k _ hk => ?_
  rw [Finset.mem_range] at hk
  have hpow : LowDeg (k * 1) (f ^ k) := lowDeg_pow hlow1 k
  rw [mul_one] at hpow
  rw [hpow d (by omega), mul_zero]

/-- Multiplicative homomorphism property of `expSMv` on zero-constant-term series:
`expSMv (f + g) = expSMv f * expSMv g`. -/
theorem expSMv_add {K : Type*} [Field K] [CharZero K] {f g : MvPowerSeries σ K}
    (hf0 : MvPowerSeries.constantCoeff f = 0) (hg0 : MvPowerSeries.constantCoeff g = 0) :
    expSMv (f + g) = expSMv f * expSMv g := by
  classical
  have hlowf : LowDeg 1 f := lowDeg_one_of_constantCoeff_zero hf0
  have hlowg : LowDeg 1 g := lowDeg_one_of_constantCoeff_zero hg0
  exact MvPowerSeries.ext fun d => by
    rw [coeff_expSMv, MvPowerSeries.coeff_mul]
    have hmul_sum :
        ∑ x ∈ Finset.antidiagonal d, MvPowerSeries.coeff x.1 (expSMv f) *
            MvPowerSeries.coeff x.2 (expSMv g) =
        ∑ x ∈ Finset.antidiagonal d,
          ∑ i ∈ Finset.range (d.degree + 1), ∑ j ∈ Finset.range (d.degree + 1),
            (((i.factorial : K))⁻¹ * ((j.factorial : K))⁻¹) *
              (MvPowerSeries.coeff x.1 (f ^ i) * MvPowerSeries.coeff x.2 (g ^ j)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      have hdeg : x.1.degree + x.2.degree = d.degree := by rw [← map_add, hx]
      rw [coeff_expSMv_eq_sum_of_ge hf0 (M := d.degree) (by omega),
        coeff_expSMv_eq_sum_of_ge hg0 (M := d.degree) (by omega),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hmul_sum, Finset.sum_comm]
    have hswap :
        ∑ i ∈ Finset.range (d.degree + 1),
          ∑ x ∈ Finset.antidiagonal d, ∑ j ∈ Finset.range (d.degree + 1),
            (((i.factorial : K))⁻¹ * ((j.factorial : K))⁻¹) *
              (MvPowerSeries.coeff x.1 (f ^ i) * MvPowerSeries.coeff x.2 (g ^ j)) =
        ∑ i ∈ Finset.range (d.degree + 1), ∑ j ∈ Finset.range (d.degree + 1),
          (((i.factorial : K))⁻¹ * ((j.factorial : K))⁻¹) *
            MvPowerSeries.coeff d (f ^ i * g ^ j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
    rw [hswap]
    have hlhs :
        ∑ k ∈ Finset.range (d.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff d ((f + g) ^ k) =
        ∑ k ∈ Finset.range (d.degree + 1),
          ∑ i ∈ Finset.range (k + 1),
            (((i.factorial : K))⁻¹ * (((k - i).factorial : K))⁻¹) *
              MvPowerSeries.coeff d (f ^ i * g ^ (k - i)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [add_pow, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hik : i ≤ k := Nat.le_of_lt_succ hi
      have hch : (k.choose i : K) * (i.factorial : K) * ((k - i).factorial : K) = (k.factorial : K) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
      have hkf : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hif : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      have hkjf : ((k - i).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - i))
      have hcoeff_eq : MvPowerSeries.coeff d (f ^ i * g ^ (k - i) * (k.choose i : MvPowerSeries σ K)) =
          (k.choose i : K) * MvPowerSeries.coeff d (f ^ i * g ^ (k - i)) := by
        rw [show (k.choose i : MvPowerSeries σ K) = MvPowerSeries.C (k.choose i : K) by simp,
          mul_comm, MvPowerSeries.coeff_C_mul]
      rw [hcoeff_eq]
      have hfrac : ((k.factorial : K))⁻¹ * (k.choose i : K) =
          ((i.factorial : K))⁻¹ * (((k - i).factorial : K))⁻¹ := by
        field_simp [hkf, hif, hkjf]
        linear_combination hch
      calc ((k.factorial : K))⁻¹ * ((k.choose i : K) * MvPowerSeries.coeff d (f ^ i * g ^ (k - i)))
          = (((k.factorial : K))⁻¹ * (k.choose i : K)) * MvPowerSeries.coeff d (f ^ i * g ^ (k - i)) := by
              ring
        _ = (((i.factorial : K))⁻¹ * (((k - i).factorial : K))⁻¹) *
              MvPowerSeries.coeff d (f ^ i * g ^ (k - i)) := by rw [hfrac]
    rw [hlhs]
    have hterm_zero : ∀ i j : ℕ, d.degree < i + j →
        (((i.factorial : K))⁻¹ * ((j.factorial : K))⁻¹) * MvPowerSeries.coeff d (f ^ i * g ^ j) = 0 := by
      intro i j hij
      have hlow_ij : LowDeg (i * 1 + j * 1) (f ^ i * g ^ j) :=
        lowDeg_mul (lowDeg_pow hlowf i) (lowDeg_pow hlowg j)
      rw [mul_one, mul_one] at hlow_ij
      rw [hlow_ij d hij, mul_zero]
    let S : Finset (ℕ × ℕ) :=
      (Finset.range (d.degree + 1) ×ˢ Finset.range (d.degree + 1)).filter (fun q => q.1 + q.2 ≤ d.degree)
    have hrhs_eq :
        ∑ i ∈ Finset.range (d.degree + 1), ∑ j ∈ Finset.range (d.degree + 1),
          (((i.factorial : K))⁻¹ * ((j.factorial : K))⁻¹) * MvPowerSeries.coeff d (f ^ i * g ^ j) =
        ∑ q ∈ S, (((q.1.factorial : K))⁻¹ * ((q.2.factorial : K))⁻¹) *
          MvPowerSeries.coeff d (f ^ q.1 * g ^ q.2) := by
      rw [← Finset.sum_product']
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun x hx hnot => ?_
      have hnot' : ¬ (x.1 + x.2 ≤ d.degree) := fun hle => hnot (Finset.mem_filter.mpr ⟨hx, hle⟩)
      exact hterm_zero x.1 x.2 (by omega)
    rw [hrhs_eq, Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ => (x.2, x.1 - x.2)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_sigma, Finset.mem_range] at hx₁ hx₂
      have h1 : x₁.2 = x₂.2 := congrArg Prod.fst heq
      have h2 : x₁.1 - x₁.2 = x₂.1 - x₂.2 := congrArg Prod.snd heq
      cases x₁; cases x₂
      dsimp only at h1 h2 hx₁ hx₂
      subst h1
      congr 1
      omega
    · intro q hq
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
      refine ⟨⟨q.1 + q.2, q.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range]; omega
      · simp
    · intro _ _; rfl

theorem expSMv_nsmul {K : Type*} [Field K] [CharZero K] {f : MvPowerSeries σ K}
    (hf0 : MvPowerSeries.constantCoeff f = 0) (n : ℕ) :
    expSMv (n • f) = (expSMv f) ^ n := by
  induction n with
  | zero => simp [expSMv_zero]
  | succ n ih =>
    rw [succ_nsmul, pow_succ, ← ih]
    exact expSMv_add (by simp [hf0]) hf0

theorem invOneMv_expSMv {K : Type*} [Field K] [CharZero K] {f : MvPowerSeries σ K}
    (hf0 : MvPowerSeries.constantCoeff f = 0) :
    invOneMv (expSMv f) = expSMv (-f) := by
  have h1 : expSMv f * expSMv (-f) = 1 := by
    rw [← expSMv_add hf0 (by simp [hf0]), add_neg_cancel, expSMv_zero]
  have hmul : invOneMv (expSMv f) * expSMv f = 1 := by
    rw [mul_comm]
    exact MvPowerSeries.mul_invOfUnit (expSMv f) 1 (by simp)
  calc invOneMv (expSMv f)
      = invOneMv (expSMv f) * 1 := (mul_one _).symm
    _ = invOneMv (expSMv f) * (expSMv f * expSMv (-f)) := by rw [h1]
    _ = (invOneMv (expSMv f) * expSMv f) * expSMv (-f) := (mul_assoc _ _ _).symm
    _ = expSMv (-f) := by rw [hmul, one_mul]

/-- Commutation of `wittFrobMap Φ` with `expSMv`:
`wittFrobMap Φ (expSMv f) = expSMv (wittFrobMap Φ f)` when `constantCoeff f = 0`. -/
theorem wittFrobMap_expSMv {L : WittRingLift p} (Φ : FrobSigK p L)
    {f : MvPowerSeries σ L.K} (hf0 : MvPowerSeries.constantCoeff f = 0) :
    wittFrobMap Φ (expSMv f) = expSMv (wittFrobMap Φ f) := by
  classical
  exact MvPowerSeries.ext fun d => by
    rw [coeff_expSMv (wittFrobMap Φ f) d, wittFrobMap, coeff_frobMapMv_eq_ite]
    split_ifs with hdiv
    · set e := d.mapRange (· / p) (Nat.zero_div p)
      have hde : p • e = d := nsmul_mapRange_div_eq hdiv
      have he_le : e.degree ≤ d.degree := by
        rw [← hde, map_nsmul, smul_eq_mul]
        exact Nat.le_mul_of_pos_left e.degree hp.out.pos
      rw [coeff_expSMv_eq_sum_of_ge hf0 he_le, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_inv₀, map_natCast, ← map_pow (frobMapMv Φ.sigK.toRingHom p hp.out.pos) f k,
        coeff_frobMapMv_eq_ite, if_pos hdiv]
    · symm
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← map_pow (frobMapMv Φ.sigK.toRingHom p hp.out.pos) f k,
        coeff_frobMapMv_eq_ite, if_neg hdiv, mul_zero]

/-- **Unconditional `p`-adic Exponential Congruence Criterion (`congOneModPMv_expSMv_iff`)**:
for ANY `L : WittRingLift p` (including `p = 2`!), arbitrary index type `σ`, and
`H : MvPowerSeries σ L.K` with `constantCoeff H = 0`:
`CongOneModPMv p (expSMv H)  ↔  CoeffNormLeMv ‖(p : L.K)‖ H`! -/
theorem congOneModPMv_expSMv_iff (L : WittRingLift p) {H : MvPowerSeries σ L.K}
    (hH0 : MvPowerSeries.constantCoeff H = 0) :
    CongOneModPMv p (expSMv H) ↔ CoeffNormLeMv ‖(p : L.K)‖ H := by
  classical
  have hp0 : 0 ≤ ‖(p : L.K)‖ := norm_nonneg _
  constructor
  · intro hexp
    suffices Hall : ∀ N : ℕ, ∀ d : σ →₀ ℕ, d.degree = N →
        ‖MvPowerSeries.coeff d H‖ ≤ ‖(p : L.K)‖ from fun d => Hall _ d rfl
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro d hd
      rcases N with _ | n
      · have hd0 : d = 0 := (finsupp_degree_eq_zero_iff d).mp hd
        subst hd0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hH0, norm_zero]
        exact hp0
      · set M := n + 1
        have hd_ne : d ≠ 0 := by
          intro h0
          rw [h0, map_zero] at hd
          omega
        set H₀ := truncBelow M H
        have hH₀0 : MvPowerSeries.constantCoeff H₀ = 0 := by
          rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_truncBelow,
            if_pos (by simp; omega), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hH0]
        have hH₀_le : CoeffNormLeMv ‖(p : L.K)‖ H₀ := fun m => by
          rw [coeff_truncBelow]
          split_ifs with hm
          · exact ih _ hm m rfl
          · simp [hp0]
        have hlow_H : LowDeg 1 H := lowDeg_one_of_constantCoeff_zero hH0
        have hlow_H₀ : LowDeg 1 H₀ := lowDeg_one_of_constantCoeff_zero hH₀0
        have hdiff : LowDeg M (H - H₀) := fun m hm => by
          rw [map_sub, coeff_truncBelow, if_pos hm, sub_self]
        have hsplit : MvPowerSeries.coeff d (expSMv H) = MvPowerSeries.coeff d H +
            ∑ k ∈ Finset.Icc 2 M,
              ((k.factorial : L.K))⁻¹ * MvPowerSeries.coeff d (H₀ ^ k) := by
          rw [coeff_expSMv, hd]
          have hrange : Finset.range (M + 1) = {0, 1} ∪ Finset.Icc 2 M := by
            ext k
            simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton, Finset.mem_Icc]
            omega
          have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 M) := by
            rw [Finset.disjoint_left]
            intro k hk1 hk2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk1
            simp only [Finset.mem_Icc] at hk2
            omega
          rw [hrange, Finset.sum_union hdisj, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
          simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, MvPowerSeries.coeff_one,
            if_neg hd_ne, mul_zero, zero_add, Nat.factorial_one, one_mul, pow_one]
          congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          have hpow_eq : MvPowerSeries.coeff d (H ^ k) = MvPowerSeries.coeff d (H₀ ^ k) := by
            have h0 := lowDeg_pow_sub_of_lowDeg hlow_H hlow_H₀ hdiff hk.1 d (by omega)
            rw [map_sub, sub_eq_zero] at h0
            exact h0
          rw [hpow_eq]
        have hH_eq : MvPowerSeries.coeff d H = MvPowerSeries.coeff d (expSMv H) -
            ∑ k ∈ Finset.Icc 2 M,
              ((k.factorial : L.K))⁻¹ * MvPowerSeries.coeff d (H₀ ^ k) := by
          linear_combination -hsplit
        rw [hH_eq, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hexp.2 d hd_ne) ?_)
        rw [norm_neg]
        refine ultrametric_norm_sum_le _ _ hp0 fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        have hpow_le : CoeffNormLeMv (‖(p : L.K)‖ ^ k) (H₀ ^ k) := by
          clear hk hsplit hH_eq
          induction k with
          | zero =>
            simpa [IsIntegralMv, CoeffNormLeMv] using isIntegralMv_one (σ := σ) (K := L.K)
          | succ k ihk =>
            rw [pow_succ, pow_succ]
            exact coeffNormLeMv_mul (pow_nonneg hp0 k) hp0 ihk hH₀_le
        rw [norm_mul]
        calc ‖((k.factorial : L.K))⁻¹‖ * ‖MvPowerSeries.coeff d (H₀ ^ k)‖
            ≤ ‖((k.factorial : L.K))⁻¹‖ * ‖(p : L.K)‖ ^ k :=
              mul_le_mul_of_nonneg_left (hpow_le d) (norm_nonneg _)
          _ ≤ ‖(p : L.K)‖ := L.norm_inv_factorial_mul_norm_p_pow_le (by omega)
  · intro hH
    refine ⟨constantCoeff_expSMv H, fun d hd => ?_⟩
    rw [coeff_expSMv]
    refine ultrametric_norm_sum_le _ _ hp0 fun k _ => ?_
    rcases k with _ | k
    · rw [pow_zero, MvPowerSeries.coeff_one, if_neg hd, mul_zero, norm_zero]
      exact hp0
    · have hpow_le : CoeffNormLeMv (‖(p : L.K)‖ ^ (k + 1)) (H ^ (k + 1)) := by
        clear hd
        induction (k + 1) with
        | zero =>
          simpa [IsIntegralMv, CoeffNormLeMv] using isIntegralMv_one (σ := σ) (K := L.K)
        | succ m ihm =>
          rw [pow_succ, pow_succ]
          exact coeffNormLeMv_mul (pow_nonneg hp0 m) hp0 ihm hH
      rw [norm_mul]
      calc ‖(((k + 1).factorial : L.K))⁻¹‖ * ‖MvPowerSeries.coeff d (H ^ (k + 1))‖
          ≤ ‖(((k + 1).factorial : L.K))⁻¹‖ * ‖(p : L.K)‖ ^ (k + 1) :=
            mul_le_mul_of_nonneg_left (hpow_le d) (norm_nonneg _)
        _ ≤ ‖(p : L.K)‖ := L.norm_inv_factorial_mul_norm_p_pow_le (Nat.succ_pos k)

/-- **Exponential Multivariable Dwork Lemma over `WittRingLift p` (`dwork_exp_multivariable_witt`)**:
for any `L : WittRingLift p`, `Φ : FrobSigK p L`, arbitrary index type `σ`, and
`Ps : MvPowerSeries σ L.K` with `constantCoeff Ps = 0`:
`IntSMv L (expSMv Ps)  ↔  ∃ Q : MvPowerSeries σ L.W, wittFrobMap Φ Ps - (p : L.K) • Ps = MvPowerSeries.C (p : L.K) * MvPowerSeries.map L.toField Q`! -/
theorem dwork_exp_multivariable_witt {L : WittRingLift p} (Φ : FrobSigK p L)
    {Ps : MvPowerSeries σ L.K} (hPs0 : MvPowerSeries.constantCoeff Ps = 0) :
    IntSMv L (expSMv Ps) ↔
      ∃ Q : MvPowerSeries σ L.W,
        wittFrobMap Φ Ps - (p : L.K) • Ps =
          MvPowerSeries.C (p : L.K) * MvPowerSeries.map L.toField Q := by
  have hwf0 : MvPowerSeries.constantCoeff (wittFrobMap Φ Ps) = 0 := by
    rw [constantCoeff_wittFrobMap, hPs0, map_zero]
  have hratio : wittFrobMap Φ (expSMv Ps) * (invOneMv (expSMv Ps)) ^ p =
      expSMv (wittFrobMap Φ Ps - (p : L.K) • Ps) := by
    rw [wittFrobMap_expSMv Φ hPs0, invOneMv_expSMv hPs0, ← expSMv_nsmul (by simp [hPs0]) p,
      ← expSMv_add hwf0 (by simp [hPs0])]
    congr 1
    exact MvPowerSeries.ext fun d => by
      simp only [map_add, map_sub, MvPowerSeries.coeff_smul, nsmul_eq_mul]
      rw [show (p : MvPowerSeries σ L.K) = MvPowerSeries.C (p : L.K) by simp,
        MvPowerSeries.coeff_C_mul, map_neg]
      ring
  have hdiff0 : MvPowerSeries.constantCoeff (wittFrobMap Φ Ps - (p : L.K) • Ps) = 0 := by
    rw [map_sub, hwf0, MvPowerSeries.constantCoeff_smul, hPs0, smul_zero, sub_self]
  rw [dwork_multivariable_witt_dual Φ (constantCoeff_expSMv Ps), hratio,
    congOneModPWitt_iff_congOneModPMv, congOneModPMv_expSMv_iff L hdiff0, div_p_mv_iff L]

/-! ### Twisted Witt Artin–Hasse Exponential (Exercising Non-Trivial `sigK`) -/

/-- **Twisted Witt Artin–Hasse Logarithm** for ANY integral parameter `c : L.W`:
`wittAHLog Φ c = ∑_{m ≥ 0} (sigK^[m] (toField c)) · X^{p^m} / p^m ∈ L.K[[X]]`. -/
def wittAHLog {L : WittRingLift p} (Φ : FrobSigK p L) (c : L.W) : MvPowerSeries Unit L.K :=
  open Classical in
  fun d =>
    if h : ∃ m : ℕ, d () = p ^ m then
      ((p : L.K) ^ h.choose)⁻¹ * (Φ.sigK)^[h.choose] (L.toField c)
    else 0

theorem coeff_wittAHLog_pow {L : WittRingLift p} (Φ : FrobSigK p L) (c : L.W) (m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single () (p ^ m)) (wittAHLog Φ c) =
      ((p : L.K) ^ m)⁻¹ * (Φ.sigK)^[m] (L.toField c) := by
  classical
  have hex : ∃ k : ℕ, (Finsupp.single () (p ^ m) : Unit →₀ ℕ) () = p ^ k := ⟨m, by simp⟩
  change (if h : ∃ k : ℕ, (Finsupp.single () (p ^ m) : Unit →₀ ℕ) () = p ^ k then _ else 0) = _
  rw [dif_pos hex]
  have hch : hex.choose = m := by
    have h1 : p ^ m = p ^ hex.choose := by simpa [Finsupp.single_eq_same] using hex.choose_spec
    exact Nat.pow_right_injective hp.out.two_le h1.symm
  rw [hch]

theorem constantCoeff_wittAHLog {L : WittRingLift p} (Φ : FrobSigK p L) (c : L.W) :
    MvPowerSeries.constantCoeff (wittAHLog Φ c) = 0 := by
  classical
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change (if h : ∃ k : ℕ, (0 : Unit →₀ ℕ) () = p ^ k then _ else 0) = 0
  rw [dif_neg]
  rintro ⟨k, hk⟩
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hk
  exact (pow_pos hp.out.pos k).ne hk

/-- Exact Frobenius functional equation for `wittAHLog Φ c`:
`wittFrobMap Φ (wittAHLog Φ c) - p • wittAHLog Φ c = C p * map L.toField (-c · X)`. -/
theorem wittFrobMap_wittAHLog_sub {L : WittRingLift p} (Φ : FrobSigK p L) (c : L.W) :
    wittFrobMap Φ (wittAHLog Φ c) - (p : L.K) • wittAHLog Φ c =
      MvPowerSeries.C (p : L.K) *
        MvPowerSeries.map L.toField (MvPowerSeries.monomial (Finsupp.single () 1) (-c)) := by
  classical
  have hp0 : (p : L.K) ≠ 0 := L.p_ne_zero
  exact MvPowerSeries.ext fun d => by
    rw [map_sub, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_map, MvPowerSeries.coeff_monomial, wittFrobMap, coeff_frobMapMv_eq_ite]
    by_cases hd1 : d = Finsupp.single () 1
    · subst hd1
      have hndiv : ¬ ∀ i : Unit, p ∣ (Finsupp.single () 1 : Unit →₀ ℕ) i := by
        intro h
        have h1 := h ()
        simp only [Finsupp.single_eq_same] at h1
        exact hp.out.not_dvd_one h1
      rw [if_neg hndiv, if_pos rfl,
        show (Finsupp.single () 1 : Unit →₀ ℕ) = Finsupp.single () (p ^ 0) by simp,
        coeff_wittAHLog_pow Φ c 0]
      simp
    · rw [if_neg hd1, map_zero, mul_zero]
      by_cases hex : ∃ m : ℕ, d () = p ^ m
      · rcases hex with ⟨m, hm⟩
        cases m with
        | zero =>
          exfalso
          apply hd1
          ext
          simpa using hm
        | succ m =>
          have hdiv : ∀ i : Unit, p ∣ d i := by
            intro i
            cases i
            rw [hm, pow_succ]
            exact dvd_mul_left p (p ^ m)
          rw [if_pos hdiv]
          have hmap : d.mapRange (· / p) (Nat.zero_div p) = Finsupp.single () (p ^ m) := by
            ext
            simp [Finsupp.mapRange_apply, hm, pow_succ', Nat.mul_div_cancel_left _ hp.out.pos]
          have hd_eq : d = Finsupp.single () (p ^ (m + 1)) := by
            ext
            simpa using hm
          rw [hmap, coeff_wittAHLog_pow, hd_eq, coeff_wittAHLog_pow]
          rw [map_mul, map_inv₀, map_pow, map_natCast, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
            ← Function.iterate_succ_apply' Φ.sigK m, pow_succ']
          field_simp [hp0]
          ring
      · have hndiv_or : ¬ ∀ i : Unit, p ∣ d i ∧ ∃ m, d () / p = p ^ m := by
          rintro h
          obtain ⟨h1, m, hm⟩ := h ()
          apply hex
          refine ⟨m + 1, ?_⟩
          rw [pow_succ', ← hm, Nat.mul_div_cancel' h1]
        have hright0 : MvPowerSeries.coeff d (wittAHLog Φ c) = 0 := by
          change (if h : ∃ m : ℕ, d () = p ^ m then _ else 0) = 0
          exact dif_neg hex
        rw [hright0, mul_zero, sub_zero]
        split_ifs with hdiv
        · have hleft0 : MvPowerSeries.coeff (d.mapRange (· / p) (Nat.zero_div p)) (wittAHLog Φ c) = 0 := by
            change (if h : ∃ m : ℕ, (d.mapRange (· / p) (Nat.zero_div p)) () = p ^ m then _ else 0) = 0
            rw [dif_neg]
            rintro ⟨m, hm⟩
            apply hndiv_or
            intro ⟨⟩
            exact ⟨hdiv (), m, by simpa [Finsupp.mapRange_apply] using hm⟩
          rw [hleft0, map_zero]
        · rfl

/-- **Twisted Witt Artin–Hasse Integrality (`wittArtinHasseExp_isIntegral`)**:
for EVERY `L : WittRingLift p`, EVERY Frobenius lift `Φ : FrobSigK p L`, and EVERY `c : L.W`,
the twisted Artin–Hasse exponential `expSMv (wittAHLog Φ c)` is integral over `L.W`! -/
theorem wittArtinHasseExp_isIntegral {L : WittRingLift p} (Φ : FrobSigK p L) (c : L.W) :
    IntSMv L (expSMv (wittAHLog Φ c)) :=
  (dwork_exp_multivariable_witt Φ (constantCoeff_wittAHLog Φ c)).mpr
    ⟨MvPowerSeries.monomial (Finsupp.single () 1) (-c), wittFrobMap_wittAHLog_sub Φ c⟩

end ExpMultivarDwork

end MultivarDworkWitt

/-! ## Section 3: `FormalGroupSystem` over `WW p` / `K0 p`, `sx_dwork_holds`, & `PositivityConditionHolds` -/

section FormalGroupSystemSection

variable (p : ℕ) [hp : Fact p.Prime]

/-- Integral multivariate power series over `WW p` inside `K0 p[[X_i]]`
(matching Alpöge's `FormalGroupSystem.IntS`). -/
def IntS {ι : Type*} (f : MvPowerSeries ι (K0 p)) : Prop :=
  ∃ g : MvPowerSeries ι (WW p), f = MvPowerSeries.map (algebraMap (WW p) (K0 p)) g

/-- Coefficientwise membership in a subring `R1 ≤ K1` (matching `FormalGroupSystem.IntR`). -/
def IntR {ι K1 : Type*} [Field K1] (R1 : Subring K1) (f : MvPowerSeries ι K1) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ∈ R1

/-- Explicit formal exponential `expS p f` on `MvPowerSeries ι (K0 p)`. -/
def expS {ι : Type*} (f : MvPowerSeries ι (K0 p)) : MvPowerSeries ι (K0 p) :=
  expSMv f

/-- Height-2 Honda / Lubin–Tate formal-group logarithm over `K0 p`:
`logF p = ∑_{j ≥ 0} X^{p^{2j}} / p^j`. -/
def logF : PowerSeries (K0 p) :=
  PowerSeries.mk fun n =>
    ∑ j ∈ Finset.range (n + 1), if n = p ^ (2 * j) then ((p : K0 p) ^ j)⁻¹ else 0

/-- Formal parameter change `inParam p f = f(logF(X_i))` over `K0 p`. -/
def inParam {ι : Type*} (f : MvPowerSeries ι (K0 p)) : MvPowerSeries ι (K0 p) :=
  MvPowerSeries.subst (fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) f

/-- Diamond-free ring-homomorphism version of `inParamK` over any field `K1` via an explicit
`RingHom` `φ : K0 p →+* K1` (zero nested `Algebra` instances!). -/
def inParamHom {ι K1 : Type*} [Field K1] (φ : K0 p →+* K1) (f : MvPowerSeries ι K1) :
    MvPowerSeries ι K1 :=
  MvPowerSeries.subst
    (fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (PowerSeries.map φ (logF p))) f

/-- Exponential integrality equivalence `Simeq p f g`:
`constantCoeff (f - g) = 0` and `expS p (inParam p (f - g)) ∈ 1 + X · WW p[[X]]`. -/
def Simeq {ι : Type*} (f g : MvPowerSeries ι (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧
    ∃ h : MvPowerSeries ι (WW p), MvPowerSeries.constantCoeff h = 0 ∧
      expS p (inParam p (f - g)) = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) h

/-- Two-variable substitution helper `sub2 p f x y = f(x, y)`. -/
def sub2 {τ : Type*} (f : MvPowerSeries (Fin 2) (K0 p)) (x y : MvPowerSeries τ (K0 p)) :
    MvPowerSeries τ (K0 p) :=
  MvPowerSeries.subst ![x, y] f

/-- Formal bilinear pairing conditions `BeProp p be` (matching `FormalGroupSystem.BeProp`). -/
structure BeProp (be : MvPowerSeries (Fin 2) (K0 p)) : Prop where
  ab : ∀ n : Fin 2 →₀ ℕ, MvPowerSeries.coeff n be ≠ 0 → 1 ≤ n 0 ∧ 1 ≤ n 1
  add1 : Simeq p
    (sub2 p be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) -
      sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 2) -
      sub2 p be (MvPowerSeries.X 1) (MvPowerSeries.X 2))
    (0 : MvPowerSeries (Fin 3) (K0 p))
  add2 : Simeq p
    (sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 1 + MvPowerSeries.X 2) -
      sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 1) -
      sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 2))
    (0 : MvPowerSeries (Fin 3) (K0 p))
  conj : ∀ α : WW p, (sigW p)^[2] α = α →
    Simeq p
      (sub2 p be (MvPowerSeries.C (algebraMap (WW p) (K0 p) α) * MvPowerSeries.X 0)
        (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) (K0 p))
      (sub2 p be (MvPowerSeries.X 0)
        (MvPowerSeries.C (algebraMap (WW p) (K0 p) (sigW p α)) * MvPowerSeries.X 1))

/-- Frobenius-fixed dual basis `OmBasis p n'` over `WW p` (matching `FormalGroupSystem.OmBasis`). -/
structure OmBasis (n' : ℕ) where
  om : Fin (n' / 2) → WW p
  omS : Fin (n' / 2) → WW p
  fix : ∀ r, (sigW p)^[n'] (om r) = om r
  fixS : ∀ r, (sigW p)^[n'] (omS r) = omS r
  dual : ∀ r r',
    ∑ i : Fin (n' / 2), (sigW p)^[2 * i.val] (om r * omS r') = if r = r' then 1 else 0

/-- Trivial `n' = 2` non-vacuous witness for `OmBasis p 2` (using `1 ∈ WW p`). -/
def omBasisTwo : OmBasis p 2 where
  om _ := 1
  omS _ := 1
  fix _ := by simp [sigW]
  fixS _ := by simp [sigW]
  dual r r' := by
    fin_cases r; fin_cases r'
    simp [sigW]

theorem intS_eq_intSMv {ι : Type*} (f : MvPowerSeries ι (K0 p)) :
    IntS p f ↔ IntSMv (concreteWittRingLift p) f := Iff.rfl

theorem coeff_logF_zero : PowerSeries.coeff 0 (logF p) = 0 := by
  simp [logF]

theorem constantCoeff_logF : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  exact coeff_logF_zero p

theorem coeff_logF_pow_two (j : ℕ) :
    PowerSeries.coeff (p ^ (2 * j)) (logF p) = ((p : K0 p) ^ j)⁻¹ := by
  simp only [logF, PowerSeries.coeff_mk]
  have hj_mem : j ∈ Finset.range (p ^ (2 * j) + 1) := by
    rw [Finset.mem_range]
    have hlt : 2 * j < p ^ (2 * j) :=
      lt_of_lt_of_le (Nat.lt_two_pow_self (n := 2 * j)) (Nat.pow_le_pow_left hp.out.two_le _)
    omega
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    rw [if_neg]
    intro heq
    have h2 : 2 * j = 2 * k := Nat.pow_right_injective hp.out.two_le heq
    exact hkj (by omega)
  · intro h; exact absurd hj_mem h

theorem coeff_logF_eq_zero_of_not_pow_two {n : ℕ} (hn : ∀ j : ℕ, n ≠ p ^ (2 * j)) :
    PowerSeries.coeff n (logF p) = 0 := by
  simp only [logF, PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg (hn j)]

theorem coeff_logF_one : PowerSeries.coeff 1 (logF p) = 1 := by
  simpa using coeff_logF_pow_two p 0

/-- **Height-2 Honda Functional Equation for `logF p`**:
`logF(X) - p⁻¹ · logF(X^{p^2}) = X` in `K0 p[[X]]`! -/
theorem logF_functional_eq :
    (logF p : MvPowerSeries Unit (K0 p)) -
      ((p : K0 p))⁻¹ • frobSub (p ^ 2) (logF p : MvPowerSeries Unit (K0 p)) =
      MvPowerSeries.X () := by
  classical
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.out.pos 2
  exact MvPowerSeries.ext fun d => by
    rw [map_sub, MvPowerSeries.coeff_smul, coeff_frobSub_eq_ite hp2_pos]
    set n := d ()
    have hd_eq : d = Finsupp.single () n := by ext; simp [n]
    rw [hd_eq, MvPowerSeries.coeff_X]
    have hmap_single : (Finsupp.single () n).mapRange (· / p ^ 2) (Nat.zero_div _) =
        Finsupp.single () (n / p ^ 2) := by ext; simp
    have hcoeff : ∀ m, MvPowerSeries.coeff (Finsupp.single () m) (logF p) =
        PowerSeries.coeff m (logF p) := fun _ => rfl
    rw [hmap_single, hcoeff, hcoeff]
    by_cases hn1 : n = 1
    · rw [hn1]
      have hndiv : ¬ ∀ i : Unit, p ^ 2 ∣ (Finsupp.single () 1 : Unit →₀ ℕ) i := by
        intro h
        have h1 := h ()
        simp only [Finsupp.single_eq_same] at h1
        have : 1 < p ^ 2 := by nlinarith [hp.out.two_le]
        exact Nat.not_dvd_of_pos_of_lt zero_lt_one this h1
      rw [if_neg hndiv, if_pos rfl, coeff_logF_one, mul_zero, sub_zero]
    · have hne : (Finsupp.single () n : Unit →₀ ℕ) ≠ Finsupp.single () 1 := fun h =>
        hn1 (by simpa using congrArg (fun f : Unit →₀ ℕ => f ()) h)
      rw [if_neg hne]
      by_cases hex : ∃ j : ℕ, n = p ^ (2 * j)
      · rcases hex with ⟨j, hj⟩
        rw [hj] at hn1 ⊢
        cases j with
        | zero => exact absurd rfl hn1
        | succ j =>
          have hdiv : ∀ i : Unit, p ^ 2 ∣ (Finsupp.single () (p ^ (2 * (j + 1))) : Unit →₀ ℕ) i := by
            intro ⟨⟩
            simp only [Finsupp.single_eq_same, show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
            exact dvd_mul_left (p ^ 2) (p ^ (2 * j))
          rw [if_pos hdiv]
          have hquot : p ^ (2 * (j + 1)) / p ^ 2 = p ^ (2 * j) := by
            rw [show 2 * (j + 1) = 2 + 2 * j by omega, pow_add]
            exact Nat.mul_div_cancel_left _ hp2_pos
          rw [hquot, coeff_logF_pow_two, coeff_logF_pow_two, pow_succ', mul_inv, sub_self]
      · rw [coeff_logF_eq_zero_of_not_pow_two p (fun j h => hex ⟨j, h⟩), zero_sub, neg_eq_zero]
        split_ifs with hdiv
        · have hnot : ∀ j : ℕ, n / p ^ 2 ≠ p ^ (2 * j) := by
            intro j hq
            apply hex
            refine ⟨j + 1, ?_⟩
            have h1 : p ^ 2 ∣ n := by simpa using hdiv ()
            rw [show 2 * (j + 1) = 2 + 2 * j by omega, pow_add, ← hq, Nat.mul_div_cancel' h1]
          rw [coeff_logF_eq_zero_of_not_pow_two p hnot, mul_zero]
        · rw [mul_zero]

private lemma constantCoeff_subst_X_logF {ι : Type*} (i : ι) :
    MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) = 0 := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst hs]
  rw [finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_logF]
  · intro d hd
    have hlow : LowDeg (d * 1) ((MvPowerSeries.X i : MvPowerSeries ι (K0 p)) ^ d) :=
      lowDeg_pow (lowDeg_one_of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)) d
    rw [mul_one] at hlow
    rw [hlow 0 (by simp; omega), smul_zero]

theorem hasSubst_inParam {ι : Type*} [Finite ι] :
    MvPowerSeries.HasSubst (fun i : ι =>
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) :=
  hasSubst_of_constantCoeff_zero_mv (constantCoeff_subst_X_logF p)

theorem constantCoeff_inParam {ι : Type*} [Finite ι] (f : MvPowerSeries ι (K0 p)) :
    MvPowerSeries.constantCoeff (inParam p f) = MvPowerSeries.constantCoeff f := by
  classical
  have hs := hasSubst_inParam p (ι := ι)
  rw [inParam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hs]
  rw [finsum_eq_single _ (0 : ι →₀ ℕ)]
  · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro d hd
    have hlow : ∀ i : ι,
        LowDeg 1 (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) :=
      fun i => lowDeg_one_of_constantCoeff_zero (constantCoeff_subst_X_logF p i)
    have hprod_low : LowDeg d.degree (d.prod fun i n =>
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) ^ n) := by
      show LowDeg (∑ i ∈ d.support, d i) (∏ i ∈ d.support,
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) ^ d i)
      refine Finset.induction_on d.support ?_ ?_
      · intro _ h; simp at h
      · intro a s ha ih
        rw [Finset.sum_insert ha, Finset.prod_insert ha]
        have hp1 := lowDeg_pow (hlow a) (d a)
        rw [mul_one] at hp1
        exact lowDeg_mul hp1 ih
    have hpos : 0 < d.degree := finsupp_degree_pos_of_ne_zero hd
    rw [hprod_low 0 (by simpa using hpos), smul_zero]

theorem inParam_add {ι : Type*} [Finite ι] (f g : MvPowerSeries ι (K0 p)) :
    inParam p (f + g) = inParam p f + inParam p g := by
  unfold inParam
  have hs := hasSubst_inParam p (ι := ι)
  rw [← MvPowerSeries.coe_substAlgHom hs]
  exact map_add (MvPowerSeries.substAlgHom hs) f g

theorem inParam_sub {ι : Type*} [Finite ι] (f g : MvPowerSeries ι (K0 p)) :
    inParam p (f - g) = inParam p f - inParam p g := by
  unfold inParam
  have hs := hasSubst_inParam p (ι := ι)
  rw [← MvPowerSeries.coe_substAlgHom hs]
  exact map_sub (MvPowerSeries.substAlgHom hs) f g

theorem inParam_neg {ι : Type*} [Finite ι] (f : MvPowerSeries ι (K0 p)) :
    inParam p (-f) = -inParam p f := by
  unfold inParam
  have hs := hasSubst_inParam p (ι := ι)
  rw [← MvPowerSeries.coe_substAlgHom hs]
  exact map_neg (MvPowerSeries.substAlgHom hs) f

theorem inParam_zero {ι : Type*} [Finite ι] :
    inParam p (0 : MvPowerSeries ι (K0 p)) = 0 := by
  unfold inParam
  have hs := hasSubst_inParam p (ι := ι)
  rw [← MvPowerSeries.coe_substAlgHom hs]
  exact map_zero (MvPowerSeries.substAlgHom hs)

/-- `Simeq p` is reflexive. -/
theorem simeq_refl {ι : Type*} [Finite ι] (f : MvPowerSeries ι (K0 p)) : Simeq p f f := by
  refine ⟨by simp, 0, by simp, ?_⟩
  rw [sub_self, inParam_zero, expS, expSMv_zero, map_zero, add_zero]

/-- `Simeq p` is symmetric. -/
theorem simeq_symm {ι : Type*} [Finite ι] {f g : MvPowerSeries ι (K0 p)}
    (h : Simeq p f g) : Simeq p g f := by
  have _ : CharZero (K0 p) := (concreteWittRingLift p).charZeroK
  rcases h with ⟨h0, u, hu0, hu⟩
  have hgf0 : MvPowerSeries.constantCoeff (g - f) = 0 := by
    rw [show g - f = -(f - g) by ring, map_neg, h0, neg_zero]
  have hin0 : MvPowerSeries.constantCoeff (inParam p (f - g)) = 0 := by
    rw [constantCoeff_inParam, h0]
  have h1u0 : MvPowerSeries.constantCoeff (1 + u) = 1 := by simp [hu0]
  have hinv_u : MvPowerSeries.constantCoeff (invOneMv (1 + u)) = 1 := by
    have hmul := congrArg MvPowerSeries.constantCoeff
      (MvPowerSeries.mul_invOfUnit (1 + u) 1 (by simpa using h1u0))
    simp only [map_mul, h1u0, one_mul, map_one] at hmul
    exact hmul
  let v : MvPowerSeries ι (WW p) := invOneMv (1 + u) - 1
  have hv0 : MvPowerSeries.constantCoeff v = 0 := by
    simp only [v, map_sub, hinv_u, map_one, sub_self]
  refine ⟨hgf0, v, hv0, ?_⟩
  rw [show g - f = -(f - g) by ring, inParam_neg, expS, ← invOneMv_expSMv hin0]
  have hmap_inv : MvPowerSeries.map (algebraMap (WW p) (K0 p)) (invOneMv (1 + u)) =
      invOneMv (expS p (inParam p (f - g))) := by
    have hmul : expS p (inParam p (f - g)) *
        MvPowerSeries.map (algebraMap (WW p) (K0 p)) (invOneMv (1 + u)) = 1 := by
      rw [hu, ← map_one (MvPowerSeries.map (algebraMap (WW p) (K0 p))), ← map_add, ← map_mul]
      simp only [invOneMv]
      rw [MvPowerSeries.mul_invOfUnit (1 + u) 1 (by simpa using h1u0), map_one]
    have hinv_exp : invOneMv (expS p (inParam p (f - g))) * expS p (inParam p (f - g)) = 1 := by
      rw [mul_comm]
      exact MvPowerSeries.mul_invOfUnit (expS p (inParam p (f - g))) 1 (by simp [expS])
    calc MvPowerSeries.map (algebraMap (WW p) (K0 p)) (invOneMv (1 + u))
        = 1 * MvPowerSeries.map (algebraMap (WW p) (K0 p)) (invOneMv (1 + u)) := (one_mul _).symm
      _ = (invOneMv (expS p (inParam p (f - g))) * expS p (inParam p (f - g))) *
            MvPowerSeries.map (algebraMap (WW p) (K0 p)) (invOneMv (1 + u)) := by rw [hinv_exp]
      _ = invOneMv (expS p (inParam p (f - g))) *
            (expS p (inParam p (f - g)) *
              MvPowerSeries.map (algebraMap (WW p) (K0 p)) (invOneMv (1 + u))) := mul_assoc _ _ _
      _ = invOneMv (expS p (inParam p (f - g))) := by rw [hmul, mul_one]
  change invOneMv (expS p (inParam p (f - g))) = _
  rw [← hmap_inv, show v = invOneMv (1 + u) - 1 from rfl, map_sub, map_one, add_sub_cancel]

/-- `Simeq p` is transitive. -/
theorem simeq_trans {ι : Type*} [Finite ι] {f g h : MvPowerSeries ι (K0 p)}
    (h1 : Simeq p f g) (h2 : Simeq p g h) : Simeq p f h := by
  have _ : CharZero (K0 p) := (concreteWittRingLift p).charZeroK
  rcases h1 with ⟨hfg0, u, hu0, hu⟩
  rcases h2 with ⟨hgh0, v, hv0, hv⟩
  have hfh0 : MvPowerSeries.constantCoeff (f - h) = 0 := by
    rw [show f - h = (f - g) + (g - h) by ring, map_add, hfg0, hgh0, add_zero]
  refine ⟨hfh0, u + v + u * v, by simp [hu0, hv0], ?_⟩
  have h10 : MvPowerSeries.constantCoeff (inParam p (f - g)) = 0 := by
    rw [constantCoeff_inParam, hfg0]
  have h20 : MvPowerSeries.constantCoeff (inParam p (g - h)) = 0 := by
    rw [constantCoeff_inParam, hgh0]
  rw [show f - h = (f - g) + (g - h) by ring, inParam_add, expS, expSMv_add h10 h20]
  change expS p (inParam p (f - g)) * expS p (inParam p (g - h)) = _
  rw [hu, hv, map_add, map_add, map_mul]
  ring

/-- **FormalGroupSystem Multivariable Dwork Lemma Statement (`DworkLemma p`)**
(matching Alpöge's `FormalGroupSystem.DworkLemma` / `PositivityConditionHolds.sx_dwork`). -/
def DworkLemma : Prop :=
  ∀ {ι : Type} (Ps : MvPowerSeries ι (K0 p)),
    MvPowerSeries.constantCoeff Ps = 0 →
      (IntS p (expS p Ps) ↔
        ∃ Q : MvPowerSeries ι (WW p),
          frobMapMv (sigK p).toRingHom p hp.out.pos Ps - (p : K0 p) • Ps =
            (p : K0 p) • MvPowerSeries.map (algebraMap (WW p) (K0 p)) Q)

/-- General `WittRingLift p` + `FrobSigK p` version of `sx_dwork_holds` (universe-polymorphic). -/
theorem sx_dwork_witt {L : WittRingLift p} (Φ : FrobSigK p L)
    {ι : Type*} (Ps : MvPowerSeries ι L.K) (h0 : MvPowerSeries.constantCoeff Ps = 0) :
    IntSMv L (expSMv Ps) ↔
      ∃ Q : MvPowerSeries ι L.W,
        wittFrobMap Φ Ps - (p : L.K) • Ps =
          (p : L.K) • MvPowerSeries.map L.toField Q := by
  have h := dwork_exp_multivariable_witt Φ h0
  simpa [MvPowerSeries.smul_eq_C_mul] using h

/-- **Unconditional Proof of `sx_dwork_holds` over `WW p` / `K0 p` / `sigK p`**:
for EVERY prime `p`, EVERY index type `ι` (in particular `Fin n`), and EVERY
`Ps : MvPowerSeries ι (K0 p)` with `constantCoeff Ps = 0`:
`IntS p (expS p Ps) ↔ ∃ Q : MvPowerSeries ι (WW p), Ps^{sigK}(X^p) - p • Ps = p • map Q`! -/
theorem sx_dwork_holds : DworkLemma p := by
  intro ι Ps h0
  exact sx_dwork_witt p (concreteFrobSigK p) Ps h0

/-- Concrete `Fin n` specialization of `sx_dwork_holds`. -/
theorem sx_dwork_holds_fin (n : ℕ) (Ps : MvPowerSeries (Fin n) (K0 p))
    (h0 : MvPowerSeries.constantCoeff Ps = 0) :
    IntS p (expS p Ps) ↔
      ∃ Q : MvPowerSeries (Fin n) (WW p),
        frobMapMv (sigK p).toRingHom p hp.out.pos Ps - (p : K0 p) • Ps =
          (p : K0 p) • MvPowerSeries.map (algebraMap (WW p) (K0 p)) Q :=
  sx_dwork_holds p Ps h0

/-- **Positivity Condition (`PositivityConditionHolds`)** for `FormalGroupSystem`
(matching `FormalGroupSystem.adm1` / `PositivityConditionHolds.positivity_condition_holds`):
the multivariable Witt-vector Dwork lemma holds for EVERY prime `p`. -/
def PositivityConditionHolds : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], DworkLemma q

/-- **Unconditional Proof of `PositivityConditionHolds`**: holds across all primes `q`! -/
theorem positivity_condition_holds : PositivityConditionHolds :=
  fun q _ => sx_dwork_holds q

end FormalGroupSystemSection

/-! ## Section 4: `WipDworkInvG` & `intS_invG_mv_inversion` — Multivariable Formal-Series Inversion -/

section WipDworkInvGMaster

/-! ### Part 4A: Master Subring Inversion Integrality (`intS_invG_subring`) -/

variable {C : Type*} [Field C]

/-- **Jacobian Matrix at `0`** of a tuple `Φ : σ → MvPowerSeries σ R`:
`(jacobianMat Φ) x y = coeff (single y 1) (Φ x)`. -/
def jacobianMat {σ R : Type*} [CommSemiring R] (Φ : σ → MvPowerSeries σ R) : Matrix σ σ R :=
  Matrix.of fun x y : σ => MvPowerSeries.coeff (Finsupp.single y 1) (Φ x)

/-- Subring-level integrality: all coefficients of `f` lie in `R : Subring C`. -/
def IntSub {σ : Type*} (R : Subring C) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ, MvPowerSeries.coeff μ f ∈ R

/-- Low-degree subring integrality: all coefficients of total degree `< K` lie in `R`. -/
def LowLtSub {σ : Type*} (R : Subring C) (K : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < K → MvPowerSeries.coeff μ f ∈ R

section SubringHelpers

variable {R : Subring C} {σ τ : Type*}

lemma finsum_mem_subring {ι : Type*} {f : ι → C} (h : ∀ i, f i ∈ R) : (∑ᶠ i, f i) ∈ R := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]; exact R.sum_mem fun i _ => h i
  · rw [finsum_of_infinite_support hs]; exact R.zero_mem

lemma det_mem_subring {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n C)
    (hA : ∀ i j, A i j ∈ R) : A.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun s _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => hA _ _)

lemma intSub_one : IntSub R (1 : MvPowerSeries σ C) := fun μ => by
  classical
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

lemma intSub_mul {f g : MvPowerSeries σ C} (hf : IntSub R f) (hg : IntSub R g) :
    IntSub R (f * g) := fun μ => by
  classical
  rw [MvPowerSeries.coeff_mul]
  exact R.sum_mem fun x _ => R.mul_mem (hf _) (hg _)

lemma intSub_pow {f : MvPowerSeries σ C} (hf : IntSub R f) (n : ℕ) : IntSub R (f ^ n) := by
  induction n with
  | zero => simpa using intSub_one (R := R)
  | succ n ih => rw [pow_succ]; exact intSub_mul ih hf

lemma intSub_prod {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ s, IntSub R (f i)) : IntSub R (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntSub R) (fun _ _ => intSub_mul) intSub_one h

theorem intSub_subst [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntSub R (a s))
    {γ : MvPowerSeries σ C} (hγ : IntSub R γ) : IntSub R (MvPowerSeries.subst a γ) := by
  have hsub := hasSubst_of_constantCoeff_zero_mv ha0
  intro μ
  rw [MvPowerSeries.coeff_subst hsub]
  refine finsum_mem_subring fun d => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hγ d) (intSub_prod _ (fun s _ => intSub_pow (ha s) _) μ)

lemma low_mul_sub {E D D' : ℕ} {f g : MvPowerSeries σ C}
    (hf : LowDeg D f) (hf' : LowLtSub R (E + D) f)
    (hg : LowDeg D' g) (hg' : LowLtSub R (E + D') g) :
    LowDeg (D + D') (f * g) ∧ LowLtSub R (E + (D + D')) (f * g) := by
  classical
  refine ⟨lowDeg_mul hf hg, fun μ hμ => ?_⟩
  rw [MvPowerSeries.coeff_mul]
  refine R.sum_mem fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have hdeg : x.1.degree + x.2.degree = μ.degree := by rw [← map_add, hx]
  by_cases h1 : x.1.degree < D
  · rw [hf x.1 h1, zero_mul]; exact R.zero_mem
  · by_cases h2 : x.2.degree < D'
    · rw [hg x.2 h2, mul_zero]; exact R.zero_mem
    · exact R.mul_mem (hf' x.1 (by omega)) (hg' x.2 (by omega))

lemma low_one_sub (E : ℕ) :
    LowDeg 0 (1 : MvPowerSeries σ C) ∧ LowLtSub R E (1 : MvPowerSeries σ C) :=
  ⟨fun _ hμ => absurd hμ (Nat.not_lt_zero _), fun μ _ => intSub_one μ⟩

lemma low_pow_sub {E D : ℕ} {f : MvPowerSeries σ C}
    (hf : LowDeg D f) (hf' : LowLtSub R (E + D) f) (n : ℕ) :
    LowDeg (n * D) (f ^ n) ∧ LowLtSub R (E + n * D) (f ^ n) := by
  induction n with
  | zero => rw [pow_zero, Nat.zero_mul, Nat.add_zero]; exact low_one_sub E
  | succ n ih => rw [pow_succ, Nat.add_mul, Nat.one_mul]; exact low_mul_sub ih.1 ih.2 hf hf'

lemma low_prod_sub {E : ℕ} {t : σ → MvPowerSeries σ C}
    (ht : ∀ s, LowDeg 1 (t s)) (ht' : ∀ s, LowLtSub R (E + 1) (t s))
    (S : Finset σ) (d : σ → ℕ) :
    LowDeg (∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) ∧
      LowLtSub R (E + ∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty, Nat.add_zero]; exact low_one_sub E
  · intro a S ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hp := low_pow_sub (ht a) (ht' a) (d a)
    rw [Nat.mul_one] at hp
    exact low_mul_sub hp.1 hp.2 ih.1 ih.2

/-- **Master Multivariable Formal-Series Inversion Integrality over ANY Subring `R : Subring C`
(`intS_invG_subring`)**:
if `Φ, G : σ → MvPowerSeries σ C` have coefficients in `R`, `constantCoeff (Φ x) = 0`,
`(jacobianMat Φ).det ≠ 0` with `((jacobianMat Φ).det)⁻¹ ∈ R`, `constantCoeff (t y) = 0`,
and `∀ x, subst t (Φ x) = G x`, then `∀ y, IntSub R (t y)`! -/
theorem intS_invG_subring [Fintype σ] [DecidableEq σ] (Φ t G : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSub R (Φ x))
    (hdet0 : (jacobianMat Φ).det ≠ 0)
    (hdetInv : ((jacobianMat Φ).det)⁻¹ ∈ R)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (hG : ∀ x, IntSub R (G x))
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = G x) :
    ∀ y, IntSub R (t y) := by
  set L : Matrix σ σ C := jacobianMat Φ
  have hord : ∀ s, LowDeg 1 (t s) := fun s => lowDeg_one_of_constantCoeff_zero (ht0 s)
  have hs : MvPowerSeries.HasSubst t := hasSubst_of_constantCoeff_zero_mv ht0
  suffices key : ∀ E : ℕ, ∀ y, LowLtSub R E (t y) by
    intro y μ
    exact key (μ.degree + 1) y μ (Nat.lt_succ_self _)
  intro E
  induction E with
  | zero => intro y μ h; exact absurd h (Nat.not_lt_zero _)
  | succ E ih =>
    intro y μ hμ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hμ with hlt | heqd
    · exact ih y μ hlt
    cases E with
    | zero =>
      rw [hord y μ (by omega)]
      exact R.zero_mem
    | succ E' =>
      have hlow : ∀ s, LowLtSub R (E' + 1) (t s) := ih
      have hbig : ∀ d : σ →₀ ℕ, 2 ≤ d.degree →
          MvPowerSeries.coeff μ (d.prod fun s n => t s ^ n) ∈ R := by
        intro d hd
        have hp := low_prod_sub hord hlow d.support d
        have hprod_eq : (d.prod fun s n => t s ^ n) = ∏ s ∈ d.support, t s ^ d s := rfl
        rw [hprod_eq]
        have hdeg : d.degree = ∑ s ∈ d.support, d s := rfl
        exact hp.2 μ (by omega)
      have heqx : ∀ x, ∑ y', L x y' * MvPowerSeries.coeff μ (t y') =
          MvPowerSeries.coeff μ (G x) -
            ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
              MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => t s ^ n)) := by
        intro x
        have h1 := congrArg (MvPowerSeries.coeff μ) (heq x)
        rw [MvPowerSeries.coeff_subst hs] at h1
        have hfin := MvPowerSeries.coeff_subst_finite hs (Φ x) μ
        set T : (σ →₀ ℕ) → C := fun d =>
          MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => t s ^ n)
        have hsplit : ∀ d, T d = (if d.degree = 1 then T d else 0) +
            (if d.degree = 1 then 0 else T d) := fun d => by split_ifs <;> simp
        have hfg : (Function.support fun d => if d.degree = 1 then T d else 0).Finite :=
          hfin.subset fun d hd => by
            simp only [Function.mem_support] at hd ⊢
            split_ifs at hd
            · exact hd
            · exact absurd rfl hd
        have hfh : (Function.support fun d => if d.degree = 1 then 0 else T d).Finite :=
          hfin.subset fun d hd => by
            simp only [Function.mem_support] at hd ⊢
            split_ifs at hd
            · exact absurd rfl hd
            · exact hd
        have h2 : ∑ᶠ d, T d = (∑ᶠ d, if d.degree = 1 then T d else 0) +
            ∑ᶠ d, (if d.degree = 1 then 0 else T d) := by
          rw [← finsum_add_distrib hfg hfh]
          exact finsum_congr hsplit
        have h3 : (∑ᶠ d, if d.degree = 1 then T d else 0) =
            ∑ y', L x y' * MvPowerSeries.coeff μ (t y') := by
          rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun y' => Finsupp.single y' 1)
            (fun d hd => by
              simp only [Function.mem_support] at hd
              split_ifs at hd with hd1
              · obtain ⟨y', rfl⟩ := deg_one_single d hd1; simp
              · exact absurd rfl hd)]
          rw [Finset.sum_image (fun a _ b _ hab => (Finsupp.single_left_inj one_ne_zero).mp hab)]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [if_pos (by simp)]
          simp only [T, smul_eq_mul]
          have hps : ((Finsupp.single y' 1 : σ →₀ ℕ).prod fun s n => t s ^ n) = t y' := by
            rw [Finsupp.prod_single_index (h := fun s n => t s ^ n) (pow_zero _), pow_one]
          rw [hps]
          rfl
        rw [h2, h3] at h1
        exact eq_sub_of_add_eq h1
      have hc : ∀ x, MvPowerSeries.coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => t s ^ n)) ∈ R := by
        intro x
        refine R.sub_mem (hG x μ) (finsum_mem_subring fun d => ?_)
        split_ifs with hd1
        · exact R.zero_mem
        · by_cases hd0 : d = 0
          · subst hd0
            rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0, zero_smul]
            exact R.zero_mem
          · have h2 : 2 ≤ d.degree := by
              have hpos := finsupp_degree_pos_of_ne_zero hd0
              omega
            rw [smul_eq_mul]
            exact R.mul_mem (hΦ x d) (hbig d h2)
      set w : σ → C := fun y' => MvPowerSeries.coeff μ (t y')
      set c : σ → C := fun x => MvPowerSeries.coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => t s ^ n))
      have hLw : L.mulVec w = c := by
        funext x; simp only [Matrix.mulVec, dotProduct]; exact heqx x
      have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet0
      have hwsol : w = L⁻¹.mulVec c := by
        rw [← hLw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hunit, Matrix.one_mulVec]
      have hinv : ∀ i j, L⁻¹ i j ∈ R := by
        intro i j
        rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
        refine R.mul_mem hdetInv ?_
        rw [Matrix.adjugate_apply]
        refine det_mem_subring _ fun a b => ?_
        rw [Matrix.updateRow_apply]
        split_ifs
        · rw [Pi.single_apply]; split_ifs
          · exact R.one_mem
          · exact R.zero_mem
        · exact hΦ a _
      have hwy : w y = (L⁻¹.mulVec c) y := by rw [← hwsol]
      show w y ∈ R
      rw [hwy]
      simp only [Matrix.mulVec, dotProduct]
      exact R.sum_mem fun x _ => R.mul_mem (hinv y x) (hc x)

/-- Master coordinate-change integrality invariance over any subring `R : Subring C`. -/
theorem image_eq_int_subring [Fintype σ] [DecidableEq σ] (Φ t : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSub R (Φ x))
    (hdet0 : (jacobianMat Φ).det ≠ 0)
    (hdetInv : ((jacobianMat Φ).det)⁻¹ ∈ R)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = MvPowerSeries.X x) :
    {F : MvPowerSeries σ C | ∃ γ, IntSub R γ ∧ F = MvPowerSeries.subst t γ} =
      {F | IntSub R F} := by
  have htI : ∀ y, IntSub R (t y) := intS_invG_subring Φ t MvPowerSeries.X hΦ0 hΦ hdet0 hdetInv ht0
    (fun x μ => by
      rw [MvPowerSeries.coeff_X]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem)
    heq
  ext F
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact intSub_subst ht0 htI hγ
  · intro hF
    have hΦs := hasSubst_of_constantCoeff_zero_mv hΦ0
    have hts := hasSubst_of_constantCoeff_zero_mv ht0
    refine ⟨MvPowerSeries.subst Φ F, intSub_subst hΦ0 hΦ hF, ?_⟩
    rw [MvPowerSeries.subst_comp_subst_apply hΦs hts]
    have hX : (fun x => MvPowerSeries.subst t (Φ x)) = (MvPowerSeries.X : σ → MvPowerSeries σ C) :=
      funext heq
    rw [hX, MvPowerSeries.subst_self]
    rfl

end SubringHelpers

/-! ### Part 4B: Additive-Valuation Specialization (`AltInv` / `WipDworkInvG`) -/

section AddValSpecialization

/-- Integral scalar predicate for an additive valuation `v : AddValuation C (WithTop ℝ)`. -/
def IntC (v : AddValuation C (WithTop ℝ)) (x : C) : Prop :=
  0 ≤ v x

/-- Integral multivariate power series predicate for `v : AddValuation C (WithTop ℝ)`. -/
def IntSVal {σ : Type*} (v : AddValuation C (WithTop ℝ)) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ, IntC v (MvPowerSeries.coeff μ f)

/-- Integral subring `{x : C | 0 ≤ v x}` of an additive valuation `v : AddValuation C (WithTop ℝ)`. -/
def addValSubring (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x : C | 0 ≤ v x}
  mul_mem' {x y} hx hy := by change 0 ≤ v (x * y); rw [AddValuation.map_mul]; exact add_nonneg hx hy
  one_mem' := by change 0 ≤ v 1; simp
  add_mem' {x y} hx hy := le_trans (le_min hx hy) (v.map_add x y)
  zero_mem' := by change 0 ≤ v 0; simp
  neg_mem' {x} hx := by change 0 ≤ v (-x); rwa [AddValuation.map_neg]

/-- **Multivariable Formal-Series Inversion Integrality over `AddValuation` (`intS_invG_val`)**
(matching Alpöge's `WipDworkInvG.intS_invG`). -/
theorem intS_invG_val {σ : Type*} [Fintype σ] [DecidableEq σ] {v : AddValuation C (WithTop ℝ)}
    (Φ t G : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSVal v (Φ x))
    (hL : v (jacobianMat Φ).det = 0)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (hG : ∀ x, IntSVal v (G x))
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = G x) :
    ∀ y, IntSVal v (t y) := by
  have hdet0 : (jacobianMat Φ).det ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hL; exact WithTop.top_ne_coe hL
  have hdetInv : ((jacobianMat Φ).det)⁻¹ ∈ addValSubring v := by
    change 0 ≤ v ((jacobianMat Φ).det)⁻¹
    rw [AddValuation.map_inv, hL]; simp
  exact intS_invG_subring (R := addValSubring v) Φ t G hΦ0 hΦ hdet0 hdetInv ht0 hG heq

/-- Formal inverse integrality (`G x = X x`), matching `AltInv.intS_inv`. -/
theorem intS_inv_val {σ : Type*} [Fintype σ] [DecidableEq σ] {v : AddValuation C (WithTop ℝ)}
    (Φ t : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSVal v (Φ x))
    (hL : v (jacobianMat Φ).det = 0)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = MvPowerSeries.X x) :
    ∀ y, IntSVal v (t y) :=
  intS_invG_val Φ t MvPowerSeries.X hΦ0 hΦ hL ht0
    (fun x μ => by
      rw [MvPowerSeries.coeff_X]
      split_ifs <;> simp [IntC])
    heq

theorem image_eq_int_val {σ : Type*} [Fintype σ] [DecidableEq σ] {v : AddValuation C (WithTop ℝ)}
    (Φ t : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSVal v (Φ x))
    (hL : v (jacobianMat Φ).det = 0)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = MvPowerSeries.X x) :
    {F : MvPowerSeries σ C | ∃ γ, IntSVal v γ ∧ F = MvPowerSeries.subst t γ} =
      {F | IntSVal v F} := by
  have hdet0 : (jacobianMat Φ).det ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hL; exact WithTop.top_ne_coe hL
  have hdetInv : ((jacobianMat Φ).det)⁻¹ ∈ addValSubring v := by
    change 0 ≤ v ((jacobianMat Φ).det)⁻¹
    rw [AddValuation.map_inv, hL]; simp
  exact image_eq_int_subring (R := addValSubring v) Φ t hΦ0 hΦ hdet0 hdetInv ht0 heq

theorem image_eq_image_val {σ : Type*} [Fintype σ] [DecidableEq σ] {v : AddValuation C (WithTop ℝ)}
    (Φ t Φ₂ t₂ : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSVal v (Φ x))
    (hL : v (jacobianMat Φ).det = 0)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = MvPowerSeries.X x)
    (hΦ0₂ : ∀ x, MvPowerSeries.constantCoeff (Φ₂ x) = 0)
    (hΦ₂ : ∀ x, IntSVal v (Φ₂ x))
    (hL₂ : v (jacobianMat Φ₂).det = 0)
    (ht0₂ : ∀ y, MvPowerSeries.constantCoeff (t₂ y) = 0)
    (heq₂ : ∀ x, MvPowerSeries.subst t₂ (Φ₂ x) = MvPowerSeries.X x) :
    {F : MvPowerSeries σ C | ∃ γ, IntSVal v γ ∧ F = MvPowerSeries.subst t γ} =
      {F : MvPowerSeries σ C | ∃ γ, IntSVal v γ ∧ F = MvPowerSeries.subst t₂ γ} := by
  rw [image_eq_int_val Φ t hΦ0 hΦ hL ht0 heq, image_eq_int_val Φ₂ t₂ hΦ0₂ hΦ₂ hL₂ ht0₂ heq₂]

end AddValSpecialization

/-! ### Part 4C: Explicit Degree-Recursive Existence & Uniqueness of Multivariable Formal Inversion -/

section MvFormalInversionExists

variable {σ : Type*}

private lemma lowDeg_prod_sub_of_lowDeg {t₁ t₂ : σ → MvPowerSeries σ C} {N : ℕ}
    (h1 : ∀ s, LowDeg 1 (t₁ s)) (h2 : ∀ s, LowDeg 1 (t₂ s))
    (hdiff : ∀ s, LowDeg N (t₁ s - t₂ s)) (S : Finset σ) (d : σ → ℕ)
    (hdeg : 2 ≤ ∑ s ∈ S, d s) :
    LowDeg (N + 1) ((∏ s ∈ S, t₁ s ^ d s) - (∏ s ∈ S, t₂ s ^ d s)) := by
  classical
  suffices H : ∀ T : Finset σ,
      LowDeg (∑ s ∈ T, d s) (∏ s ∈ T, t₁ s ^ d s) ∧
      LowDeg (∑ s ∈ T, d s) (∏ s ∈ T, t₂ s ^ d s) ∧
      (1 ≤ ∑ s ∈ T, d s →
        LowDeg (N + (∑ s ∈ T, d s) - 1) ((∏ s ∈ T, t₁ s ^ d s) - (∏ s ∈ T, t₂ s ^ d s))) by
    exact lowDeg_mono (by omega) ((H S).2.2 (by omega))
  intro T
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun h => by simp at h⟩
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have ha1 : LowDeg (d a) (t₁ a ^ d a) := by simpa [mul_one] using lowDeg_pow (h1 a) (d a)
    have ha2 : LowDeg (d a) (t₂ a ^ d a) := by simpa [mul_one] using lowDeg_pow (h2 a) (d a)
    refine ⟨lowDeg_mul ha1 ih.1, lowDeg_mul ha2 ih.2.1, fun hsum => ?_⟩
    have hdiff_pow : ∀ k : ℕ, 1 ≤ k → LowDeg (N + k - 1) (t₁ a ^ k - t₂ a ^ k) := by
      intro k hk
      cases k with
      | zero => omega
      | succ k =>
        cases k with
        | zero => simpa using hdiff a
        | succ k =>
          clear hk
          induction k with
          | zero =>
            have heq : t₁ a ^ 2 - t₂ a ^ 2 = (t₁ a - t₂ a) * (t₁ a + t₂ a) := by ring
            rw [show N + 2 - 1 = N + 1 by omega, heq]
            exact lowDeg_mul (hdiff a) (lowDeg_add (h1 a) (h2 a))
          | succ k ihk =>
            have heq : t₁ a ^ (k + 3) - t₂ a ^ (k + 3) =
                (t₁ a ^ (k + 2) - t₂ a ^ (k + 2)) * t₁ a +
                  t₂ a ^ (k + 2) * (t₁ a - t₂ a) := by ring
            rw [heq]
            refine lowDeg_add ?_ ?_
            · exact lowDeg_mono (by omega) (lowDeg_mul ihk (h1 a))
            · have hp2 : LowDeg (k + 2) (t₂ a ^ (k + 2)) := by
                simpa [mul_one] using lowDeg_pow (h2 a) (k + 2)
              exact lowDeg_mono (by omega) (lowDeg_mul hp2 (hdiff a))
    have hsplit : t₁ a ^ d a * (∏ s ∈ T, t₁ s ^ d s) - t₂ a ^ d a * (∏ s ∈ T, t₂ s ^ d s) =
        (t₁ a ^ d a - t₂ a ^ d a) * (∏ s ∈ T, t₁ s ^ d s) +
          t₂ a ^ d a * ((∏ s ∈ T, t₁ s ^ d s) - (∏ s ∈ T, t₂ s ^ d s)) := by ring
    rw [hsplit]
    refine lowDeg_add ?_ ?_
    · by_cases hda : d a = 0
      · rw [hda, pow_zero, pow_zero, sub_self, zero_mul]
        exact lowDeg_zero _
      · exact lowDeg_mono (by omega) (lowDeg_mul (hdiff_pow (d a) (by omega)) ih.1)
    · by_cases hT : ∑ s ∈ T, d s = 0
      · have hall0 : ∀ s ∈ T, d s = 0 := fun s hs => (Finset.sum_eq_zero_iff.mp hT) s hs
        have hp1 : (∏ s ∈ T, t₁ s ^ d s) = 1 :=
          Finset.prod_eq_one fun s hs => by rw [hall0 s hs, pow_zero]
        have hp2 : (∏ s ∈ T, t₂ s ^ d s) = 1 :=
          Finset.prod_eq_one fun s hs => by rw [hall0 s hs, pow_zero]
        rw [hp1, hp2, sub_self, mul_zero]
        exact lowDeg_zero _
      · exact lowDeg_mono (by omega) (lowDeg_mul ha2 (ih.2.2 (by omega)))

/-- Degree-`N` linearization of multivariate substitution `subst t (Φ x)` when `t - t₀` has `LowDeg N`. -/
theorem coeff_mvSubst_split [Fintype σ] {Φ t t₀ : σ → MvPowerSeries σ C} {N : ℕ} (_hN : 1 ≤ N)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (ht₀0 : ∀ y, MvPowerSeries.constantCoeff (t₀ y) = 0)
    (hdiff : ∀ y, LowDeg N (t y - t₀ y)) (x : σ) :
    (∀ μ : σ →₀ ℕ, μ.degree < N →
      MvPowerSeries.coeff μ (MvPowerSeries.subst t (Φ x)) =
        MvPowerSeries.coeff μ (MvPowerSeries.subst t₀ (Φ x))) ∧
    (∀ μ : σ →₀ ℕ, μ.degree = N →
      MvPowerSeries.coeff μ (MvPowerSeries.subst t (Φ x)) =
        MvPowerSeries.coeff μ (MvPowerSeries.subst t₀ (Φ x)) +
          ∑ y, jacobianMat Φ x y * MvPowerSeries.coeff μ (t y - t₀ y)) := by
  classical
  have hst := hasSubst_of_constantCoeff_zero_mv ht0
  have hst₀ := hasSubst_of_constantCoeff_zero_mv ht₀0
  have h1 : ∀ s, LowDeg 1 (t s) := fun s => lowDeg_one_of_constantCoeff_zero (ht0 s)
  have h2 : ∀ s, LowDeg 1 (t₀ s) := fun s => lowDeg_one_of_constantCoeff_zero (ht₀0 s)
  have hterm_eq : ∀ (μ : σ →₀ ℕ) (hμ : μ.degree ≤ N) (d : σ →₀ ℕ), d.degree ≠ 1 →
      MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => t s ^ n) =
        MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => t₀ s ^ n) := by
    intro μ hμ d hd1
    by_cases hd0 : d = 0
    · subst hd0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0, zero_smul, zero_smul]
    · have hd2 : 2 ≤ d.degree := by
        have hpos := finsupp_degree_pos_of_ne_zero hd0
        omega
      have h0 := lowDeg_prod_sub_of_lowDeg h1 h2 hdiff d.support d hd2 μ (by omega)
      rw [map_sub, sub_eq_zero] at h0
      show MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (∏ s ∈ d.support, t s ^ d s) =
        MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (∏ s ∈ d.support, t₀ s ^ d s)
      rw [h0]
  have hdeg1_sum : ∀ (μ : σ →₀ ℕ) (u : σ → MvPowerSeries σ C),
      (∑ᶠ d : σ →₀ ℕ, if d.degree = 1 then
          MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => u s ^ n) else 0) =
        ∑ y, jacobianMat Φ x y * MvPowerSeries.coeff μ (u y) := by
    intro μ u
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun y => Finsupp.single y 1)
      (fun d hd => by
        simp only [Function.mem_support] at hd
        split_ifs at hd with hd1
        · obtain ⟨y, rfl⟩ := deg_one_single d hd1; simp
        · exact absurd rfl hd)]
    rw [Finset.sum_image (fun a _ b _ hab => (Finsupp.single_left_inj one_ne_zero).mp hab)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [if_pos (by simp)]
    simp only [smul_eq_mul]
    have hps : ((Finsupp.single y 1 : σ →₀ ℕ).prod fun s n => u s ^ n) = u y := by
      rw [Finsupp.prod_single_index (h := fun s n => u s ^ n) (pow_zero _), pow_one]
    rw [hps]
    rfl
  have hsplit_subst : ∀ (μ : σ →₀ ℕ) (u : σ → MvPowerSeries σ C) (hsu : MvPowerSeries.HasSubst u),
      MvPowerSeries.coeff μ (MvPowerSeries.subst u (Φ x)) =
        (∑ y, jacobianMat Φ x y * MvPowerSeries.coeff μ (u y)) +
        (∑ᶠ d : σ →₀ ℕ, if d.degree = 1 then 0 else
          MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => u s ^ n)) := by
    intro μ u hsu
    rw [MvPowerSeries.coeff_subst hsu]
    have hfin := MvPowerSeries.coeff_subst_finite hsu (Φ x) μ
    set T : (σ →₀ ℕ) → C := fun d =>
      MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => u s ^ n)
    have hfg : (Function.support fun d => if d.degree = 1 then T d else 0).Finite :=
      hfin.subset fun d hd => by
        simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact hd; exact absurd rfl hd
    have hfh : (Function.support fun d => if d.degree = 1 then 0 else T d).Finite :=
      hfin.subset fun d hd => by
        simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact absurd rfl hd; exact hd
    have h2 : ∑ᶠ d, T d = (∑ᶠ d, if d.degree = 1 then T d else 0) +
        ∑ᶠ d, (if d.degree = 1 then 0 else T d) := by
      rw [← finsum_add_distrib hfg hfh]
      exact finsum_congr fun d => by split_ifs <;> simp
    rw [h2, hdeg1_sum μ u]
  constructor
  · intro μ hμ
    rw [hsplit_subst μ t hst, hsplit_subst μ t₀ hst₀]
    congr 1
    · refine Finset.sum_congr rfl fun y _ => ?_
      have hy := hdiff y μ hμ
      rw [map_sub, sub_eq_zero] at hy
      rw [hy]
    · refine finsum_congr fun d => ?_
      split_ifs with hd1
      · rfl
      · exact hterm_eq μ hμ.le d hd1
  · intro μ hμ
    rw [hsplit_subst μ t hst, hsplit_subst μ t₀ hst₀]
    have htail : (∑ᶠ d : σ →₀ ℕ, if d.degree = 1 then 0 else
        MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => t s ^ n)) =
      (∑ᶠ d : σ →₀ ℕ, if d.degree = 1 then 0 else
        MvPowerSeries.coeff d (Φ x) • MvPowerSeries.coeff μ (d.prod fun s n => t₀ s ^ n)) := by
      refine finsum_congr fun d => ?_
      split_ifs with hd1
      · rfl
      · exact hterm_eq μ hμ.le d hd1
    rw [htail]
    have hlin : ∑ y, jacobianMat Φ x y * MvPowerSeries.coeff μ (t y) =
        ∑ y, jacobianMat Φ x y * MvPowerSeries.coeff μ (t₀ y) +
          ∑ y, jacobianMat Φ x y * MvPowerSeries.coeff μ (t y - t₀ y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_sub]
      ring
    rw [hlin]
    ring

/-- Degree-by-degree recursive construction of the multivariable formal inverse `t` solving
`subst t (Φ x) = G x` when `(jacobianMat Φ).det ≠ 0`. -/
def mvSolveSubstLayer [Fintype σ] [DecidableEq σ] (Φ G : σ → MvPowerSeries σ C) :
    ℕ → σ → MvPowerSeries σ C
  | 0, _ => 0
  | N + 1, y => fun μ =>
      if μ.degree ≤ N then MvPowerSeries.coeff μ (mvSolveSubstLayer Φ G N y)
      else if μ.degree = N + 1 then
        ((jacobianMat Φ)⁻¹.mulVec fun x =>
          MvPowerSeries.coeff μ (G x) -
            MvPowerSeries.coeff μ (MvPowerSeries.subst (mvSolveSubstLayer Φ G N) (Φ x))) y
      else 0

lemma mvSolveSubstLayer_constantCoeff [Fintype σ] [DecidableEq σ]
    (Φ G : σ → MvPowerSeries σ C) (N : ℕ) (y : σ) :
    MvPowerSeries.constantCoeff (mvSolveSubstLayer Φ G N y) = 0 := by
  induction N with
  | zero => simp [mvSolveSubstLayer]
  | succ N ih =>
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show (if (0 : σ →₀ ℕ).degree ≤ N then MvPowerSeries.coeff 0 (mvSolveSubstLayer Φ G N y)
      else if (0 : σ →₀ ℕ).degree = N + 1 then
        ((jacobianMat Φ)⁻¹.mulVec fun x =>
          MvPowerSeries.coeff 0 (G x) -
            MvPowerSeries.coeff 0 (MvPowerSeries.subst (mvSolveSubstLayer Φ G N) (Φ x))) y
      else 0) = 0
    rw [if_pos (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ih]

lemma mvSolveSubstLayer_stable [Fintype σ] [DecidableEq σ]
    (Φ G : σ → MvPowerSeries σ C) {N M : ℕ} (hNM : N ≤ M) (y : σ)
    {μ : σ →₀ ℕ} (hμ : μ.degree ≤ N) :
    MvPowerSeries.coeff μ (mvSolveSubstLayer Φ G M y) =
      MvPowerSeries.coeff μ (mvSolveSubstLayer Φ G N y) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    change (if μ.degree ≤ M then MvPowerSeries.coeff μ (mvSolveSubstLayer Φ G M y) else _) = _
    rw [if_pos (hμ.trans hNM), ih]

/-- The formal limit `mvSolveSubst Φ G y` whose `μ`-th coefficient is read off at layer `μ.degree`. -/
def mvSolveSubst [Fintype σ] [DecidableEq σ] (Φ G : σ → MvPowerSeries σ C) (y : σ) :
    MvPowerSeries σ C :=
  fun μ => MvPowerSeries.coeff μ (mvSolveSubstLayer Φ G μ.degree y)

lemma mvSolveSubst_constantCoeff [Fintype σ] [DecidableEq σ]
    (Φ G : σ → MvPowerSeries σ C) (y : σ) :
    MvPowerSeries.constantCoeff (mvSolveSubst Φ G y) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change MvPowerSeries.coeff 0 (mvSolveSubstLayer Φ G (0 : σ →₀ ℕ).degree y) = 0
  simp [mvSolveSubstLayer]

lemma coeff_mvSolveSubst_eq_layer [Fintype σ] [DecidableEq σ]
    (Φ G : σ → MvPowerSeries σ C) (y : σ) {N : ℕ} {μ : σ →₀ ℕ} (hμ : μ.degree ≤ N) :
    MvPowerSeries.coeff μ (mvSolveSubst Φ G y) =
      MvPowerSeries.coeff μ (mvSolveSubstLayer Φ G N y) :=
  (mvSolveSubstLayer_stable Φ G hμ y le_rfl).symm

/-- **Unconditional Existence & Uniqueness of Multivariable Formal Inversion
(`exists_unique_mv_formal_inversion`)**:
for ANY `Φ, G : σ → MvPowerSeries σ C` (`[Fintype σ]`) with `constantCoeff (Φ x) = 0`,
`constantCoeff (G x) = 0`, and `(jacobianMat Φ).det ≠ 0`, there exists a UNIQUE tuple
`t : σ → MvPowerSeries σ C` with `constantCoeff (t y) = 0` and `∀ x, subst t (Φ x) = G x`! -/
theorem exists_unique_mv_formal_inversion [Fintype σ] [DecidableEq σ]
    (Φ G : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hG0 : ∀ x, MvPowerSeries.constantCoeff (G x) = 0)
    (hdet : (jacobianMat Φ).det ≠ 0) :
    ∃! t : σ → MvPowerSeries σ C,
      (∀ y, MvPowerSeries.constantCoeff (t y) = 0) ∧
        ∀ x, MvPowerSeries.subst t (Φ x) = G x := by
  set t := mvSolveSubst Φ G
  have ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0 := mvSolveSubst_constantCoeff Φ G
  have hunit : IsUnit (jacobianMat Φ).det := isUnit_iff_ne_zero.mpr hdet
  have hlayer_sol : ∀ N : ℕ, ∀ x : σ, ∀ μ : σ →₀ ℕ, μ.degree ≤ N →
      MvPowerSeries.coeff μ (MvPowerSeries.subst (mvSolveSubstLayer Φ G N) (Φ x)) =
        MvPowerSeries.coeff μ (G x) := by
    intro N
    induction N with
    | zero =>
      intro x μ hμ
      have hμ0 : μ = 0 := (finsupp_degree_eq_zero_iff μ).mp (by omega)
      subst hμ0
      have hs0 := hasSubst_of_constantCoeff_zero_mv (mvSolveSubstLayer_constantCoeff Φ G 0)
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG0 x]
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hs0]
      have hzero_all : ∀ d : σ →₀ ℕ,
          MvPowerSeries.coeff d (Φ x) •
            MvPowerSeries.coeff 0 (d.prod fun s n => mvSolveSubstLayer Φ G 0 s ^ n) = 0 := by
        intro d
        by_cases hd0 : d = 0
        · subst hd0
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0 x, zero_smul]
        · have hzero : d.prod (fun s n => (mvSolveSubstLayer Φ G 0 s) ^ n) = 0 := by
            obtain ⟨i, hi⟩ : ∃ i, i ∈ d.support := Finsupp.support_nonempty_iff.mpr hd0
            have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
            exact Finset.prod_eq_zero hi (by simp [mvSolveSubstLayer, zero_pow hdi])
          rw [hzero, map_zero, smul_zero]
      rw [finsum_congr hzero_all, finsum_zero]
    | succ N ih =>
      intro x μ hμ
      have hdiff : ∀ y, LowDeg (N + 1) (mvSolveSubstLayer Φ G (N + 1) y - mvSolveSubstLayer Φ G N y) := by
        intro y ν hν
        rw [map_sub, mvSolveSubstLayer_stable Φ G (Nat.le_succ N) y (by omega), sub_self]
      have hsp := coeff_mvSubst_split (Nat.succ_pos N) hΦ0
        (mvSolveSubstLayer_constantCoeff Φ G (N + 1))
        (mvSolveSubstLayer_constantCoeff Φ G N) hdiff x
      rcases Nat.lt_or_eq_of_le hμ with hlt | heq
      · rw [hsp.1 μ hlt]
        exact ih x μ (Nat.le_of_lt_succ hlt)
      · rw [hsp.2 μ heq]
        set c : σ → C := fun z =>
          MvPowerSeries.coeff μ (G z) -
            MvPowerSeries.coeff μ (MvPowerSeries.subst (mvSolveSubstLayer Φ G N) (Φ z))
        have hdiff_eq : ∀ y, MvPowerSeries.coeff μ
            (mvSolveSubstLayer Φ G (N + 1) y - mvSolveSubstLayer Φ G N y) =
            ((jacobianMat Φ)⁻¹.mulVec c) y := by
          intro y
          have hN0 : MvPowerSeries.coeff μ (mvSolveSubstLayer Φ G N y) = 0 := by
            cases N with
            | zero => simp [mvSolveSubstLayer]
            | succ N' =>
              change (if μ.degree ≤ N' then _ else if μ.degree = N' + 1 then _ else 0) = 0
              rw [if_neg (by omega), if_neg (by omega)]
          rw [map_sub, hN0, sub_zero]
          change (if μ.degree ≤ N then _ else if μ.degree = N + 1 then _ else 0) = _
          rw [if_neg (by omega), if_pos heq]
        have hsum_eq : ∑ y, jacobianMat Φ x y *
            MvPowerSeries.coeff μ (mvSolveSubstLayer Φ G (N + 1) y - mvSolveSubstLayer Φ G N y) =
            c x := by
          simp_rw [hdiff_eq]
          change ((jacobianMat Φ).mulVec ((jacobianMat Φ)⁻¹.mulVec c)) x = c x
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (jacobianMat Φ) hunit, Matrix.one_mulVec]
        rw [hsum_eq]
        dsimp only [c]
        ring
  refine ⟨t, ⟨ht0, fun x => ?_⟩, ?_⟩
  · exact MvPowerSeries.ext fun μ => by
      have hdiff : ∀ y, LowDeg (μ.degree + 1) (t y - mvSolveSubstLayer Φ G μ.degree y) := by
        intro y ν hν
        rw [map_sub, coeff_mvSolveSubst_eq_layer Φ G y (Nat.le_of_lt_succ hν), sub_self]
      have hsp := coeff_mvSubst_split (Nat.succ_pos μ.degree) hΦ0 ht0
        (mvSolveSubstLayer_constantCoeff Φ G μ.degree) hdiff x
      rw [hsp.1 μ (Nat.lt_succ_self μ.degree)]
      exact hlayer_sol μ.degree x μ le_rfl
  · rintro t' ⟨ht'0, ht'eq⟩
    funext y
    exact MvPowerSeries.ext fun μ => by
      suffices H : ∀ N : ℕ, ∀ y : σ, ∀ ν : σ →₀ ℕ, ν.degree < N →
          MvPowerSeries.coeff ν (t' y) = MvPowerSeries.coeff ν (t y) from
        H (μ.degree + 1) y μ (Nat.lt_succ_self _)
      intro N
      induction N with
      | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
      | succ N ih =>
        intro y ν hν
        rcases Nat.lt_succ_iff_lt_or_eq.mp hν with hlt | heq
        · exact ih y ν hlt
        rcases N with _ | n
        · have hν0 : ν = 0 := (finsupp_degree_eq_zero_iff ν).mp heq
          subst hν0
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
            MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ht'0, ht0]
        · have hdiff : ∀ z, LowDeg (n + 1) (t' z - t z) := fun z ω hω => by
            rw [map_sub, ih z ω hω, sub_self]
          have hLvec : (jacobianMat Φ).mulVec (fun z => MvPowerSeries.coeff ν (t' z - t z)) = 0 := by
            funext x
            have hsp := (coeff_mvSubst_split (Nat.succ_pos n) hΦ0 ht'0 ht0 hdiff x).2 ν heq
            have h1 : MvPowerSeries.coeff ν (MvPowerSeries.subst t' (Φ x)) =
                MvPowerSeries.coeff ν (G x) := congrArg (MvPowerSeries.coeff ν) (ht'eq x)
            have h2 : MvPowerSeries.coeff ν (MvPowerSeries.subst t (Φ x)) =
                MvPowerSeries.coeff ν (G x) := by
              have hdiff2 : ∀ z, LowDeg (ν.degree + 1) (t z - mvSolveSubstLayer Φ G ν.degree z) := by
                intro z ω hω
                rw [map_sub, coeff_mvSolveSubst_eq_layer Φ G z (Nat.le_of_lt_succ hω), sub_self]
              have hsp2 := (coeff_mvSubst_split (Nat.succ_pos ν.degree) hΦ0 ht0
                (mvSolveSubstLayer_constantCoeff Φ G ν.degree) hdiff2 x).1 ν (Nat.lt_succ_self _)
              rw [hsp2]
              exact hlayer_sol ν.degree x ν le_rfl
            rw [h1, h2] at hsp
            change ∑ z, jacobianMat Φ x z * MvPowerSeries.coeff ν (t' z - t z) = 0
            linear_combination -hsp
          have hzero : (fun z => MvPowerSeries.coeff ν (t' z - t z)) = 0 := by
            calc (fun z => MvPowerSeries.coeff ν (t' z - t z))
                = (jacobianMat Φ)⁻¹.mulVec ((jacobianMat Φ).mulVec
                    (fun z => MvPowerSeries.coeff ν (t' z - t z))) := by
                      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
              _ = (jacobianMat Φ)⁻¹.mulVec 0 := by rw [hLvec]
              _ = 0 := Matrix.mulVec_zero _
          have hy0 := congrFun hzero y
          rw [Pi.zero_apply, map_sub, sub_eq_zero] at hy0
          exact hy0

end MvFormalInversionExists

end WipDworkInvGMaster

/-! ### Part 4D: Ultrametric & `WittRingLift p` Specializations (`intS_invG_mv_inversion`) -/

section WittMvInversion

/-- Closed unit ball `{x : K | ‖x‖ ≤ 1}` as a `Subring K` for any ultrametric normed field `K`. -/
def ultrametricUnitBallSubring (K : Type*) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x : K | ‖x‖ ≤ 1}
  mul_mem' {x y} hx hy := by
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    calc ‖x‖ * ‖y‖ ≤ 1 * 1 := mul_le_mul hx hy (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  one_mem' := by change ‖(1 : K)‖ ≤ 1; simp
  add_mem' {x y} hx hy :=
    (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by change ‖(0 : K)‖ ≤ 1; simp
  neg_mem' {x} hx := by change ‖-x‖ ≤ 1; rwa [norm_neg]

/-- **Ultrametric Multivariable Formal-Series Inversion Integrality (`intS_invG_norm`)**:
if `Φ, G : σ → MvPowerSeries σ K` are integral (`‖coeff‖ ≤ 1`) with `constantCoeff (Φ x) = 0`,
`‖(jacobianMat Φ).det‖ = 1`, `constantCoeff (t y) = 0`, and `∀ x, subst t (Φ x) = G x`, then
`∀ y, IsIntegralMv (t y)`! -/
theorem intS_invG_norm {σ K : Type*} [NormedField K] [IsUltrametricDist K]
    [Fintype σ] [DecidableEq σ]
    (Φ t G : σ → MvPowerSeries σ K)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IsIntegralMv (Φ x))
    (hL : ‖(jacobianMat Φ).det‖ = 1)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (hG : ∀ x, IsIntegralMv (G x))
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = G x) :
    ∀ y, IsIntegralMv (t y) := by
  have hdet0 : (jacobianMat Φ).det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hL; exact zero_ne_one hL
  have hdetInv : ((jacobianMat Φ).det)⁻¹ ∈ ultrametricUnitBallSubring K := by
    change ‖((jacobianMat Φ).det)⁻¹‖ ≤ 1
    rw [norm_inv, hL, inv_one]
  exact intS_invG_subring (R := ultrametricUnitBallSubring K) Φ t G hΦ0 hΦ hdet0 hdetInv ht0 hG heq

variable {σ : Type*} {p : ℕ} [Fact p.Prime]

/-- **Multivariable Formal-Series Inversion Integrality over `WittRingLift p`
(`intS_invG_mv_inversion`)**:
for any `L : WittRingLift p`, finite index type `σ`, integral `Φ, G : σ → MvPowerSeries σ L.K`
with `constantCoeff (Φ x) = 0` and unimodular Jacobian `‖(jacobianMat Φ).det‖ = 1`, any
zero-constant-term formal solution `t` to `∀ x, subst t (Φ x) = G x` is integral over `L.W`
(`∀ y, IntSMv L (t y)`)! -/
theorem intS_invG_mv_inversion [Fintype σ] [DecidableEq σ] (L : WittRingLift p)
    (Φ t G : σ → MvPowerSeries σ L.K)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSMv L (Φ x))
    (hL : ‖(jacobianMat Φ).det‖ = 1)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (hG : ∀ x, IntSMv L (G x))
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = G x) :
    ∀ y, IntSMv L (t y) := by
  intro y
  rw [intSMv_iff_isIntegralMv]
  exact intS_invG_norm Φ t G hΦ0
    (fun x => (intSMv_iff_isIntegralMv L _).mp (hΦ x))
    hL ht0
    (fun x => (intSMv_iff_isIntegralMv L _).mp (hG x))
    heq y

/-- Unconditional existence + uniqueness + integrality of multivariable formal inversion over
any `WittRingLift p`. -/
theorem exists_integral_mv_formal_inversion [Fintype σ] [DecidableEq σ] (L : WittRingLift p)
    (Φ G : σ → MvPowerSeries σ L.K)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSMv L (Φ x))
    (hL : ‖(jacobianMat Φ).det‖ = 1)
    (hG0 : ∀ x, MvPowerSeries.constantCoeff (G x) = 0)
    (hG : ∀ x, IntSMv L (G x)) :
    ∃! t : σ → MvPowerSeries σ L.K,
      (∀ y, MvPowerSeries.constantCoeff (t y) = 0) ∧
        (∀ y, IntSMv L (t y)) ∧
        ∀ x, MvPowerSeries.subst t (Φ x) = G x := by
  have hdet : (jacobianMat Φ).det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hL; exact zero_ne_one hL
  obtain ⟨t, ⟨ht0, hteq⟩, huniq⟩ := exists_unique_mv_formal_inversion Φ G hΦ0 hG0 hdet
  refine ⟨t, ⟨ht0, intS_invG_mv_inversion L Φ t G hΦ0 hΦ hL ht0 hG hteq, hteq⟩, ?_⟩
  rintro t' ⟨ht'0, _, ht'eq⟩
  exact huniq t' ⟨ht'0, ht'eq⟩

/-- Concrete `WW p` / `K0 p` specialization of `intS_invG_mv_inversion`. -/
theorem intS_invG_WW [Fintype σ] [DecidableEq σ] (p : ℕ) [Fact p.Prime]
    (Φ t G : σ → MvPowerSeries σ (K0 p))
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS p (Φ x))
    (hL : wittAbv p (jacobianMat Φ).det = 1)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (hG : ∀ x, IntS p (G x))
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = G x) :
    ∀ y, IntS p (t y) :=
  intS_invG_mv_inversion (concreteWittRingLift p) Φ t G hΦ0 hΦ hL ht0 hG heq

/-- Integral power-series ring invariance under unimodular formal coordinate changes over
`WittRingLift p` (`image_eq_int_witt`). -/
theorem image_eq_int_witt [Fintype σ] [DecidableEq σ] (L : WittRingLift p)
    (Φ t : σ → MvPowerSeries σ L.K)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSMv L (Φ x))
    (hL : ‖(jacobianMat Φ).det‖ = 1)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = MvPowerSeries.X x) :
    {F : MvPowerSeries σ L.K | ∃ γ, IntSMv L γ ∧ F = MvPowerSeries.subst t γ} =
      {F | IntSMv L F} := by
  have hdet0 : (jacobianMat Φ).det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hL; exact zero_ne_one hL
  have hdetInv : ((jacobianMat Φ).det)⁻¹ ∈ ultrametricUnitBallSubring L.K := by
    change ‖((jacobianMat Φ).det)⁻¹‖ ≤ 1
    rw [norm_inv, hL, inv_one]
  have hsub := image_eq_int_subring (R := ultrametricUnitBallSubring L.K) Φ t hΦ0
    (fun x => (intSMv_iff_isIntegralMv L _).mp (hΦ x)) hdet0 hdetInv ht0 heq
  ext F
  have hiff : ∀ G : MvPowerSeries σ L.K, IntSMv L G ↔ IntSub (ultrametricUnitBallSubring L.K) G :=
    fun G => intSMv_iff_isIntegralMv L G
  simp only [Set.mem_ofPred_eq, hiff]
  exact Set.ext_iff.mp hsub F

theorem image_eq_image_witt [Fintype σ] [DecidableEq σ] (L : WittRingLift p)
    (Φ t Φ₂ t₂ : σ → MvPowerSeries σ L.K)
    (hΦ0 : ∀ x, MvPowerSeries.constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntSMv L (Φ x))
    (hL : ‖(jacobianMat Φ).det‖ = 1)
    (ht0 : ∀ y, MvPowerSeries.constantCoeff (t y) = 0)
    (heq : ∀ x, MvPowerSeries.subst t (Φ x) = MvPowerSeries.X x)
    (hΦ0₂ : ∀ x, MvPowerSeries.constantCoeff (Φ₂ x) = 0)
    (hΦ₂ : ∀ x, IntSMv L (Φ₂ x))
    (hL₂ : ‖(jacobianMat Φ₂).det‖ = 1)
    (ht0₂ : ∀ y, MvPowerSeries.constantCoeff (t₂ y) = 0)
    (heq₂ : ∀ x, MvPowerSeries.subst t₂ (Φ₂ x) = MvPowerSeries.X x) :
    {F : MvPowerSeries σ L.K | ∃ γ, IntSMv L γ ∧ F = MvPowerSeries.subst t γ} =
      {F : MvPowerSeries σ L.K | ∃ γ, IntSMv L γ ∧ F = MvPowerSeries.subst t₂ γ} := by
  rw [image_eq_int_witt L Φ t hΦ0 hΦ hL ht0 heq, image_eq_int_witt L Φ₂ t₂ hΦ0₂ hΦ₂ hL₂ ht0₂ heq₂]

end WittMvInversion

/-! ## Section 5: `FormalGroupSystem` Assembly & M5 Wave 2 Handoff -/

section Wave2Handoff

/-- **Bundled `FormalGroupSystem` over a `WittRingLift p` (`FormalGroupSystemWitt p`)**:
packages a Witt-vector ring lift `L`, its Frobenius lift `Φ`, and the proved multivariable Dwork
integrality, exponential Dwork positivity, and unimodular formal-series inversion theorems, ready
for M5 Wave 2 (`Stage14M5_DataDIVDefsNuLat`, `Stage14M5_LinkGAndAskIsF`). -/
structure FormalGroupSystemWitt (p : ℕ) [Fact p.Prime] where
  /-- Underlying diamond-free Witt ring lift `W →+* K`. -/
  lift : WittRingLift p
  /-- Compatible Frobenius lift `(sigW, sigK)`. -/
  frob : FrobSigK p lift
  /-- Multivariable Dwork integrality lemma `f ∈ W[[X]] ↔ f^p / f^σ(X^p) ∈ 1 + p·W[[X]]`. -/
  dwork_multivar : ∀ {ι : Type} (f : MvPowerSeries ι lift.K),
    MvPowerSeries.constantCoeff f = 1 →
      (IntSMv lift f ↔ CongOneModPWitt lift (f ^ p * invOneMv (wittFrobMap frob f)))
  /-- Exponential multivariable Dwork positivity condition (`sx_dwork`). -/
  dwork_exp : ∀ {ι : Type} (Ps : MvPowerSeries ι lift.K),
    MvPowerSeries.constantCoeff Ps = 0 →
      (IntSMv lift (expSMv Ps) ↔
        ∃ Q : MvPowerSeries ι lift.W,
          wittFrobMap frob Ps - (p : lift.K) • Ps =
            (p : lift.K) • MvPowerSeries.map lift.toField Q)
  /-- Multivariable formal-series inversion integrality (`WipDworkInvG`). -/
  mv_inversion_integral : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ t G : ι → MvPowerSeries ι lift.K),
    (∀ x, MvPowerSeries.constantCoeff (Φ x) = 0) →
    (∀ x, IntSMv lift (Φ x)) →
    ‖(jacobianMat Φ).det‖ = 1 →
    (∀ y, MvPowerSeries.constantCoeff (t y) = 0) →
    (∀ x, IntSMv lift (G x)) →
    (∀ x, MvPowerSeries.subst t (Φ x) = G x) →
    ∀ y, IntSMv lift (t y)
  /-- Coordinate-change integrality invariance (`AltInv.image_eq_int`). -/
  coord_change_int : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ t : ι → MvPowerSeries ι lift.K),
    (∀ x, MvPowerSeries.constantCoeff (Φ x) = 0) →
    (∀ x, IntSMv lift (Φ x)) →
    ‖(jacobianMat Φ).det‖ = 1 →
    (∀ y, MvPowerSeries.constantCoeff (t y) = 0) →
    (∀ x, MvPowerSeries.subst t (Φ x) = MvPowerSeries.X x) →
    {F : MvPowerSeries ι lift.K | ∃ γ, IntSMv lift γ ∧ F = MvPowerSeries.subst t γ} =
      {F | IntSMv lift F}

/-- Build a `FormalGroupSystemWitt p` unconditionally from ANY `(L, Φ)`. -/
def formalGroupSystemOfWitt (p : ℕ) [Fact p.Prime] (L : WittRingLift p) (Φ : FrobSigK p L) :
    FormalGroupSystemWitt p where
  lift := L
  frob := Φ
  dwork_multivar _ hf0 := dwork_multivariable_witt Φ hf0
  dwork_exp Ps h0 := sx_dwork_witt p Φ Ps h0
  mv_inversion_integral Φ' t G hΦ0 hΦ hL ht0 hG heq :=
    intS_invG_mv_inversion L Φ' t G hΦ0 hΦ hL ht0 hG heq
  coord_change_int Φ' t hΦ0 hΦ hL ht0 heq :=
    image_eq_int_witt L Φ' t hΦ0 hΦ hL ht0 heq

/-- Concrete `FormalGroupSystemWitt p` realized on `WW p = WittVector p (AlgebraicClosure (ZMod p))`,
`K0 p = FractionRing (WW p)`, and `sigK p`. -/
def formalGroupSystemWW (p : ℕ) [Fact p.Prime] : FormalGroupSystemWitt p :=
  formalGroupSystemOfWitt p (concreteWittRingLift p) (concreteFrobSigK p)

/-- Concrete `FormalGroupSystemWitt p` realized on `ℤ_[p] ↪ ℚ_[p]` (connecting directly to
`RHDirect.Stage12MultivarDwork`). -/
def formalGroupSystemPadic (p : ℕ) [Fact p.Prime] : FormalGroupSystemWitt p :=
  formalGroupSystemOfWitt p (padicWittRingLift p) (padicFrobSigK p)

theorem nonempty_formalGroupSystemWW (p : ℕ) [Fact p.Prime] :
    Nonempty (FormalGroupSystemWitt p) :=
  ⟨formalGroupSystemWW p⟩

/-- **Complete M5 Wave 2 Handoff Package (`WittDworkFormalGroupPack p`)**:
exports the concrete `WW p / K0 p / sigK p` system, global `PositivityConditionHolds`,
height-2 `logF` functional equation, twisted Witt Artin–Hasse integrality, and Fontaine `A_inf`
Frobenius lift compatibility. -/
structure WittDworkFormalGroupPack (p : ℕ) [Fact p.Prime] where
  system : FormalGroupSystemWitt p
  positivity : PositivityConditionHolds
  dwork_WW : DworkLemma p
  om_base : OmBasis p 2
  logF_eq :
    (logF p : MvPowerSeries Unit (K0 p)) -
      ((p : K0 p))⁻¹ • frobSub (p ^ 2) (logF p : MvPowerSeries Unit (K0 p)) =
      MvPowerSeries.X ()
  ah_integral : ∀ c : system.lift.W, IntSMv system.lift (expSMv (wittAHLog system.frob c))

/-- Unconditional concrete witness `concreteWittDworkFormalGroupPack p` for every prime `p`. -/
def concreteWittDworkFormalGroupPack (p : ℕ) [Fact p.Prime] : WittDworkFormalGroupPack p where
  system := formalGroupSystemWW p
  positivity := positivity_condition_holds
  dwork_WW := sx_dwork_holds p
  om_base := omBasisTwo p
  logF_eq := logF_functional_eq p
  ah_integral c := wittArtinHasseExp_isIntegral (concreteFrobSigK p) c

end Wave2Handoff

end
end RHDirect.Stage14M5_WittFrobeniusDwork
