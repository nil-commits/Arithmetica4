import RHDirect.ChenDefs
import RHDirect.Stage11BombieriVinogradov
import RHDirect.Stage10SiegelWalfiszFull
import RHDirect.Stage8MertensTheorems
import RHDirect.Stage8BarbanDavenport
import RHDirect.Stage2DirichletAP
import Mathlib.Topology.UniformSpace.Compact

/-!
# RHDirect.ChenBVPrimes

Bridge from our verified baseline analytic number theory modules
(`Stage11BombieriVinogradov`, `Stage10SiegelWalfiszFull`, `Stage8MertensTheorems`,
`Stage8BarbanDavenport`, `Stage2DirichletAP`) to the prime-counting, remainder, and
Mertens–Riemann sum inputs needed for **Chen's Theorem** (`RHDirect.ChenDefs`).

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

open Finset MeasureTheory Set Filter Topology RHDirect
open scoped BigOperators

namespace RHDirect.Chen

/-! ## Section 1: Elementary Helpers, PNT Asymptotics, and Prime-Counting Bombieri–Vinogradov -/

/-- Native prime-counting function `π(x) = #{p ≤ ⌊x⌋₊ : p prime}`. -/
def primeCount (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card

theorem primeCount_eq_primeCountAP_one (x : ℝ) :
    primeCount x = Stage2DirichletAP.primeCountAP 1 0 x := by
  unfold primeCount Stage2DirichletAP.primeCountAP
  congr 1; ext p
  simp [Nat.modEq_one]

/-- Harmonic sum bound: for `Q ≥ 1`, `∑_{q=1}^Q 1/q ≤ log Q + 1`. -/
private lemma harmonic_sum_le_log_add_one {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ)⁻¹) ≤ Real.log (Q : ℝ) + 1 := by
  induction Q, hQ using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hstep : (((m + 1 : ℕ) : ℝ)⁻¹) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      have hlog := Real.log_le_sub_one_of_pos (div_pos hm_pos hm1_pos)
      rw [Real.log_div hm_pos.ne' hm1_pos.ne'] at hlog
      have hsub : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(((m + 1 : ℕ) : ℝ)⁻¹) := by
        push_cast
        field_simp [hm1_pos.ne']
        ring
      linarith
    linarith

/-- Sum of `1 / φ(q)` over `1 ≤ q ≤ Q`: bounded by `6 * log (2 * Q)` for `Q ≥ 1`. -/
private lemma sum_inv_totient_Icc_le {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ ≤ 6 * Real.log (2 * (Q : ℝ)) := by
  have h := Stage8BarbanDavenport.sum_inv_totient_dvd_le (d := 1) le_rfl hQ
  have hfilt : (Finset.Icc 1 Q).filter (fun q => 1 ∣ q) = Finset.Icc 1 Q := by
    ext q; simp
  rw [hfilt] at h
  simpa using h

/-- Trivial upper bound on `θ(t; q, a)`: for `q ≥ 1` and `t ≥ 1`,
`chebyshevThetaAP q a t ≤ (t / q + 1) * log t`. -/
private lemma chebyshevThetaAP_le_triv {q : ℕ} (hq : 1 ≤ q) (a : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    Stage2DirichletAP.chebyshevThetaAP q a t ≤ (t / (q : ℝ) + 1) * Real.log t := by
  unfold Stage2DirichletAP.chebyshevThetaAP
  rw [← Finset.sum_filter]
  have ht0 : 0 < t := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterm :
      ∑ n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n.Prime ∧ n ≡ a [MOD q]), Real.log (n : ℝ) ≤
        ∑ _n ∈ (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n.Prime ∧ n ≡ a [MOD q]), Real.log t := by
    refine Finset.sum_le_sum fun n hn => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn.2.1.pos
    have hn_le : (n : ℝ) ≤ t := by
      have h1 : n ≤ ⌊t⌋₊ := Nat.lt_succ_iff.mp hn.1
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le ht0.le)
    exact Real.log_le_log hn_pos hn_le
  rw [Finset.sum_const, nsmul_eq_mul] at hterm
  have hcard :
      ((Finset.range (⌊t⌋₊ + 1)).filter (fun n => n.Prime ∧ n ≡ a [MOD q])).card ≤
        ⌊t⌋₊ / q + 1 := by
    have hsub :
        (Finset.range (⌊t⌋₊ + 1)).filter (fun n => n.Prime ∧ n ≡ a [MOD q]) ⊆
          (Finset.range (⌊t⌋₊ / q + 1)).image (fun k => q * k + a % q) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hn ⊢
      refine ⟨n / q, ?_, ?_⟩
      · exact Nat.lt_succ_iff.mpr (Nat.div_le_div_right (Nat.lt_succ_iff.mp hn.1))
      · have hmod : n % q = a % q := hn.2.2
        rw [← hmod, Nat.div_add_mod]
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have hcardR :
      (((Finset.range (⌊t⌋₊ + 1)).filter (fun n => n.Prime ∧ n ≡ a [MOD q])).card : ℝ) ≤
        t / (q : ℝ) + 1 := by
    have h1 : (((Finset.range (⌊t⌋₊ + 1)).filter (fun n => n.Prime ∧ n ≡ a [MOD q])).card : ℝ) ≤
        ((⌊t⌋₊ / q : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
    have h2 : ((⌊t⌋₊ / q : ℕ) : ℝ) ≤ (⌊t⌋₊ : ℝ) / (q : ℝ) := by
      rw [le_div_iff₀ hq0]
      exact_mod_cast Nat.div_mul_le_self ⌊t⌋₊ q
    have h3 : (⌊t⌋₊ : ℝ) / (q : ℝ) ≤ t / (q : ℝ) :=
      div_le_div_of_nonneg_right (Nat.floor_le ht0.le) hq0.le
    linarith
  exact hterm.trans (mul_le_mul_of_nonneg_right hcardR (Real.log_nonneg ht))

/-- `chebyshevThetaAP q a` is measurable (factors through `Nat.floor`). -/
private lemma measurable_chebyshevThetaAP' (q a : ℕ) :
    Measurable (Stage2DirichletAP.chebyshevThetaAP q a) := by
  have h : Stage2DirichletAP.chebyshevThetaAP q a =
      (fun k : ℕ => ∑ n ∈ Finset.range (k + 1),
        if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

/-- `chebyshevPsiAP q a` is measurable (factors through `Nat.floor`). -/
private lemma measurable_chebyshevPsiAP' (q a : ℕ) :
    Measurable (Stage2DirichletAP.chebyshevPsiAP q a) := by
  have h : Stage2DirichletAP.chebyshevPsiAP q a =
      (fun k : ℕ => ∑ n ∈ Finset.range (k + 1),
        if n ≡ a [MOD q] then ArithmeticFunction.vonMangoldt n else 0) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

/-- `psiAPMaxError q` is measurable in `t`. -/
private lemma measurable_psiAPMaxError (q : ℕ) :
    Measurable (fun t : ℝ => Stage11BombieriVinogradov.psiAPMaxError q t) := by
  unfold Stage11BombieriVinogradov.psiAPMaxError
  split_ifs with h
  · have hmeas_sup : ∀ (s : Finset ℕ) (hs : s.Nonempty),
        Measurable (fun t : ℝ => s.sup' hs (fun a =>
          |Stage2DirichletAP.chebyshevPsiAP q a t - t / (q.totient : ℝ)|)) := by
      intro s hs
      induction hs using Finset.Nonempty.cons_induction with
      | singleton a =>
        simp only [Finset.sup'_singleton]
        exact continuous_abs.measurable.comp
          ((measurable_chebyshevPsiAP' q a).sub (measurable_id.div_const _))
      | cons a s ha hs ih =>
        have heq : (fun t : ℝ => (s.cons a ha).sup' (Finset.cons_nonempty ha) (fun b =>
              |Stage2DirichletAP.chebyshevPsiAP q b t - t / (q.totient : ℝ)|)) =
            fun t : ℝ => max |Stage2DirichletAP.chebyshevPsiAP q a t - t / (q.totient : ℝ)|
              (s.sup' hs (fun b =>
                |Stage2DirichletAP.chebyshevPsiAP q b t - t / (q.totient : ℝ)|)) := by
          funext t; exact Finset.sup'_cons hs _
        rw [heq]
        exact (continuous_abs.measurable.comp
          ((measurable_chebyshevPsiAP' q a).sub (measurable_id.div_const _))).max ih
    exact hmeas_sup _ h
  · exact measurable_const

/-- Trivial bound `psiAPMaxError q t ≤ 7 * t` for `q ≥ 1` and `t ≥ 2`. -/
private lemma psiAPMaxError_le_seven_mul {q : ℕ} (hq : 1 ≤ q) {t : ℝ} (ht : 2 ≤ t) :
    Stage11BombieriVinogradov.psiAPMaxError q t ≤ 7 * t := by
  refine Stage11BombieriVinogradov.psiAPMaxError_le_of_forall (by linarith) fun a _ => ?_
  have h1 : Stage2DirichletAP.chebyshevPsiAP q a t ≤ 6 * t := by
    have ha : Stage2DirichletAP.chebyshevPsiAP q a t ≤ RHDirect.chebyshevPsi t := by
      unfold Stage2DirichletAP.chebyshevPsiAP RHDirect.chebyshevPsi
      refine Finset.sum_le_sum fun n _ => ?_
      split_ifs
      · exact le_rfl
      · exact ArithmeticFunction.vonMangoldt_nonneg
    exact ha.trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith))
  have h2 : 0 ≤ Stage2DirichletAP.chebyshevPsiAP q a t :=
    Stage2DirichletAP.chebyshevPsiAP_nonneg q a t
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h3 : t / (q.totient : ℝ) ≤ t := by
    calc t / (q.totient : ℝ) ≤ t / 1 := div_le_div_of_nonneg_left (by linarith) zero_lt_one hphi_ge1
      _ = t := div_one t
  have h4 : 0 ≤ t / (q.totient : ℝ) := div_nonneg (by linarith) (by linarith)
  rw [abs_le]; constructor <;> linarith

/-- Elementary helper: for any `c > 0` and `P : ℝ`, there exists `K > 0` such that
for all `x ≥ 4`, `(Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x)) ≤ K`. -/
private lemma log_rpow_mul_exp_neg_sqrt_le {c : ℝ} (hc : 0 < c) (P : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 4 ≤ x →
      (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x)) ≤ K := by
  set P' : ℝ := max P 1
  have hP' : 0 < P' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hratio : Tendsto (fun u : ℝ => Real.log u / Real.sqrt u) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    exact h.congr fun u => by rw [Real.sqrt_eq_rpow]
  have hcomp : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.sqrt (Real.log x)) atTop (𝓝 0) :=
    hratio.comp Real.tendsto_log_atTop
  have hev := hcomp.eventually (Iio_mem_nhds (div_pos hc hP'))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  set X₀ : ℝ := max 4 X₁
  have hX₀4 : 4 ≤ X₀ := le_max_left _ _
  have hLX₀_gt1 : 1 < Real.log X₀ := by
    have : Real.exp 1 < X₀ := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  set K : ℝ := max 1 ((Real.log X₀) ^ P')
  refine ⟨K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x hx4 => ?_⟩
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hpow_le : (Real.log x) ^ P ≤ (Real.log x) ^ P' :=
    Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (le_max_left _ _)
  by_cases hge : X₀ ≤ x
  · have hlt : Real.log (Real.log x) / Real.sqrt (Real.log x) < c / P' :=
      hX₁ x ((le_max_right _ _).trans hge)
    have hsq_pos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLx_pos
    have hmul : P' * Real.log (Real.log x) < c * Real.sqrt (Real.log x) := by
      have h1 := (div_lt_iff₀ hsq_pos).mp hlt
      have h2 := mul_lt_mul_of_pos_left h1 hP'
      have h3 : P' * (c / P' * Real.sqrt (Real.log x)) = c * Real.sqrt (Real.log x) := by
        field_simp [hP'.ne']
      linarith
    have h1 : (Real.log x) ^ P' * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := by
      rw [Real.rpow_def_of_pos hLx_pos, ← Real.exp_add]
      exact Real.exp_le_one_iff.mpr (by linarith)
    calc (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x))
        ≤ (Real.log x) ^ P' * Real.exp (-c * Real.sqrt (Real.log x)) :=
          mul_le_mul_of_nonneg_right hpow_le (Real.exp_pos _).le
      _ ≤ 1 := h1
      _ ≤ K := le_max_left _ _
  · push Not at hge
    have hexp_le1 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg (Real.log x)])
    have hlog_le : Real.log x ≤ Real.log X₀ := Real.log_le_log (by linarith) hge.le
    calc (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x))
        ≤ (Real.log x) ^ P' * 1 :=
          mul_le_mul hpow_le hexp_le1 (Real.exp_pos _).le (Real.rpow_nonneg hLx_pos.le _)
      _ = (Real.log x) ^ P' := mul_one _
      _ ≤ (Real.log X₀) ^ P' := Real.rpow_le_rpow hLx_pos.le hlog_le hP'.le
      _ ≤ K := le_max_right _ _

/-- Elementary helper: for any `M > 0`, `(Real.log x) ^ M / Real.sqrt x → 0` as `x → ∞`, so
there exists `K > 0` such that `(Real.log x) ^ M ≤ K * Real.sqrt x` for all `x ≥ 4`. -/
private lemma log_rpow_le_const_mul_sqrt (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 4 ≤ x → (Real.log x) ^ M ≤ K * Real.sqrt x := by
  set M' : ℝ := max M 1
  have hM' : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hα : (0 : ℝ) < 1 / (2 * M') := by positivity
  have hev := ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  set X₀ : ℝ := max 4 X₁
  have hX₀4 : 4 ≤ X₀ := le_max_left _ _
  set K : ℝ := max 1 ((Real.log X₀) ^ M')
  refine ⟨K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x hx4 => ?_⟩
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hx0 : 0 < x := by linarith
  have hpow_le : (Real.log x) ^ M ≤ (Real.log x) ^ M' :=
    Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (le_max_left _ _)
  by_cases hge : X₀ ≤ x
  · have hlt : Real.log x / x ^ (1 / (2 * M')) < 1 := hX₁ x ((le_max_right _ _).trans hge)
    have hle1 : Real.log x ≤ x ^ (1 / (2 * M')) :=
      ((div_lt_one (Real.rpow_pos_of_pos hx0 _)).mp hlt).le
    have hpow := Real.rpow_le_rpow hLx_pos.le hle1 hM'.le
    rw [← Real.rpow_mul hx0.le] at hpow
    have hexp : 1 / (2 * M') * M' = 1 / 2 := by field_simp [hM'.ne']
    rw [hexp, ← Real.sqrt_eq_rpow] at hpow
    calc (Real.log x) ^ M ≤ (Real.log x) ^ M' := hpow_le
      _ ≤ 1 * Real.sqrt x := by linarith
      _ ≤ K * Real.sqrt x := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg x)
  · push Not at hge
    have hsq_ge1 : (1 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    have hlog_le : Real.log x ≤ Real.log X₀ := Real.log_le_log hx0 hge.le
    calc (Real.log x) ^ M ≤ (Real.log x) ^ M' := hpow_le
      _ ≤ (Real.log X₀) ^ M' := Real.rpow_le_rpow hLx_pos.le hlog_le hM'.le
      _ ≤ K := le_max_right _ _
      _ ≤ K * Real.sqrt x := by nlinarith [lt_of_lt_of_le zero_lt_one (le_max_left 1 ((Real.log X₀) ^ M'))]

/-- **Prime-Counting Bombieri–Vinogradov Theorem (`ϑ = 1/2`, `0` assumptions)**:
for every `A : ℝ`, there exist `B > 0` and `C > 0` such that for all `x ≥ 4`:
`∑_{q ≤ √x / (log x)^B} max_{(a,q)=1} |π(x; q, a) - π(x) / φ(q)| ≤ C * x / (log x)^A`. -/
theorem bombieri_vinogradov_primes (A : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ x : ℝ, 4 ≤ x →
        ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊,
          (if h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
            ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' h
              (fun a => |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
                (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|)
          else 0) ≤ C * x / (Real.log x) ^ A := by
  set A' : ℝ := max A 1 with hA'_def
  have hA'1 : 1 ≤ A' := le_max_right A 1
  have hA_le_A' : A ≤ A' := le_max_left A 1
  -- Obtain Bombieri–Vinogradov for `ψ(x; q, a)` at exponent `A'`
  obtain ⟨B_ψ, C_ψ, hBψ, hCψ, hbv_ψ⟩ := Stage11BombieriVinogradov.bombieri_vinogradov A'
  -- Obtain Siegel–Walfisz for `π(x)` at `q = 1`
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := Stage10SiegelWalfiszFull.siegel_walfisz_pi_real
  obtain ⟨C_sw, hCsw, hsw1⟩ := hsw_all 1 zero_lt_one
  -- Choose `B` large enough that `√x / (log x)^B ≤ √y / (log y)^{B_ψ}` and `B - (A'+4)/2 ≥ A'`
  set K_y : ℝ := A' + 4 with hKy_def
  set B : ℝ := max (B_ψ + K_y / 2) (A' + K_y / 2 + 1) with hB_def
  have hB_pos : 0 < B := lt_of_lt_of_le (by dsimp only [K_y]; positivity) (le_max_left _ _)
  -- Asymptotic helpers for `x` large enough that `y = x / (log x)^{K_y} ≥ 4` and `log y ≥ log x / 2`
  obtain ⟨K_sqrt1, hKsq1, hlog_sq1⟩ := log_rpow_le_const_mul_sqrt (2 * K_y)
  obtain ⟨K_sqrt2, hKsq2, hlog_sq2⟩ := log_rpow_le_const_mul_sqrt (A' + 2)
  obtain ⟨K_sw_exp, hKsw_exp, hsw_exp⟩ := log_rpow_mul_exp_neg_sqrt_le hc_sw (A' + 1)
  have hlog_y_ratio : Tendsto (fun x : ℝ => K_y * Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
    have h1 := (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
    have h2 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
      h1.congr fun u => by rw [Real.rpow_one]
    have h3 := (h2.comp Real.tendsto_log_atTop).const_mul K_y
    simpa [mul_div_assoc] using h3
  have hev_y := hlog_y_ratio.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  rw [Filter.eventually_atTop] at hev_y
  obtain ⟨X₁, hX₁⟩ := hev_y
  -- Also ensure `x / (log x)^{K_y} ≥ 4` for `x ≥ X₀`:
  -- since `(log x)^{2 K_y} ≤ K_sqrt1 * √x`, `(log x)^{K_y} ≤ √K_sqrt1 * x^{1/4}`,
  -- actually even simpler: `x / (log x)^{K_y} → ∞` via `log_rpow_le_const_mul_sqrt K_y`!
  obtain ⟨K_sqrt3, hKsq3, hlog_sq3⟩ := log_rpow_le_const_mul_sqrt K_y
  set X₀ : ℝ := max (max 16 X₁) ((4 * K_sqrt3) ^ 2 + 1) with hX0_def
  have hX0_16 : 16 ≤ X₀ := (le_max_left 16 X₁).trans (le_max_left _ _)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Large-`x` constant
  set C_large : ℝ :=
    6 * C_sw * K_sw_exp * 2 +
    C_ψ + 1 +
    (12 / Real.log 2) * K_sqrt2 +
    (2 / Real.log 2) + (1 / Real.log 2) * K_sqrt2 + (12 / (Real.log 2) ^ 2) +
    C_ψ * (2 : ℝ) ^ (A' + 2) + 1 / Real.log 2
  have hC_large_pos : 0 < C_large := by positivity
  -- Small-`x` constant for `4 ≤ x < X₀`
  set C_small : ℝ := (Real.sqrt X₀ * (2 * X₀ + 2)) * (Real.log X₀) ^ A' / 4 + 1
  have hC_small_pos : 0 < C_small := by
    have hLX0 : 0 < Real.log X₀ := Real.log_pos (by linarith)
    positivity
  set C_fin : ℝ := max C_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hC_large_pos (le_max_left _ _)
  refine ⟨B, C_fin, hB_pos, hC_fin_pos, fun x hx4 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx2 : 2 ≤ x := by linarith
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  set Q : ℕ := ⌊Real.sqrt x / (Real.log x) ^ B⌋₊ with hQ_def
  have hQ_le_real : (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B := Nat.floor_le (by positivity)
  have hQ_le_sqrt : (Q : ℝ) ≤ Real.sqrt x := by
    have h1 : (1 : ℝ) ≤ (Real.log x) ^ B := Real.one_le_rpow hLx_gt1.le hB_pos.le
    exact hQ_le_real.trans (div_le_self (Real.sqrt_nonneg x) h1)
  have hA_pow_le : (Real.log x) ^ A ≤ (Real.log x) ^ A' :=
    Real.rpow_le_rpow_of_exponent_le hLx_gt1.le hA_le_A'
  -- Handle `Q = 0` immediately
  by_cases hQ0 : Q = 0
  · simp [hQ0]; positivity
  have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ0
  -- Handle `x < X₀` by trivial bound
  by_cases hge : X₀ ≤ x
  swap
  · push Not at hge
    have hsum_triv :
        ∑ q ∈ Finset.Icc 1 Q,
          (if h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
            ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' h
              (fun a => |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
                (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|)
          else 0) ≤ (Q : ℝ) * (2 * x + 2) := by
      have hterm : ∀ q ∈ Finset.Icc 1 Q,
          (if h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
            ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' h
              (fun a => |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
                (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|)
          else 0) ≤ 2 * x + 2 := by
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hphi1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
        split_ifs with hne
        · refine Finset.sup'_le hne _ fun a _ => ?_
          have h1 : (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤ x + 1 := by
            unfold Stage2DirichletAP.primeCountAP
            have hc : ((Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card ≤
                ⌊x⌋₊ + 1 := (Finset.card_filter_le _ _).trans (by simp)
            have hcR : (((Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) ≤
                (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hc
            linarith [Nat.floor_le hx0.le]
          have h2 : (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ) ≤ x + 1 := by
            have hc : ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card ≤ ⌊x⌋₊ + 1 :=
              (Finset.card_filter_le _ _).trans (by simp)
            have hcR : (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by
              exact_mod_cast hc
            calc _ ≤ (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / 1 :=
                  div_le_div_of_nonneg_left (Nat.cast_nonneg _) zero_lt_one hphi1
              _ = (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) := div_one _
              _ ≤ x + 1 := by linarith [Nat.floor_le hx0.le]
          have h1_nn : (0 : ℝ) ≤ (Stage2DirichletAP.primeCountAP q a x : ℝ) := Nat.cast_nonneg _
          have h2_nn : (0 : ℝ) ≤ (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ) := by
            positivity
          rw [abs_le]; constructor <;> linarith
        · linarith
      calc _ ≤ ∑ _q ∈ Finset.Icc 1 Q, (2 * x + 2) := Finset.sum_le_sum hterm
        _ = (Q : ℝ) * (2 * x + 2) := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hlog_le : (Real.log x) ^ A ≤ (Real.log X₀) ^ A' :=
      hA_pow_le.trans (Real.rpow_le_rpow hLx_pos.le (Real.log_le_log hx0 hge.le) (by linarith))
    have hQ_le_X0 : (Q : ℝ) ≤ Real.sqrt X₀ := hQ_le_sqrt.trans (Real.sqrt_le_sqrt hge.le)
    calc _ ≤ (Q : ℝ) * (2 * x + 2) := hsum_triv
      _ ≤ Real.sqrt X₀ * (2 * X₀ + 2) := by
          have : 0 ≤ 2 * x + 2 := by linarith
          nlinarith
      _ ≤ (Real.sqrt X₀ * (2 * X₀ + 2)) * ((Real.log X₀) ^ A' / (Real.log x) ^ A) * (x / 4) := by
          have h1 : (1 : ℝ) ≤ (Real.log X₀) ^ A' / (Real.log x) ^ A :=
            (one_le_div (Real.rpow_pos_of_pos hLx_pos A)).mpr hlog_le
          have h2 : (1 : ℝ) ≤ x / 4 := by linarith
          have h12 : (1 : ℝ) ≤ ((Real.log X₀) ^ A' / (Real.log x) ^ A) * (x / 4) := by nlinarith
          have hnn : 0 ≤ Real.sqrt X₀ * (2 * X₀ + 2) := by positivity
          calc Real.sqrt X₀ * (2 * X₀ + 2)
              ≤ (Real.sqrt X₀ * (2 * X₀ + 2)) * (((Real.log X₀) ^ A' / (Real.log x) ^ A) * (x / 4)) := by
                nlinarith
            _ = _ := by ring
      _ = ((Real.sqrt X₀ * (2 * X₀ + 2)) * (Real.log X₀) ^ A' / 4) * x / (Real.log x) ^ A := by ring
      _ ≤ C_small * x / (Real.log x) ^ A := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hx0.le)
            (Real.rpow_nonneg hLx_pos.le A)
          dsimp only [C_small]; linarith
      _ ≤ C_fin * x / (Real.log x) ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hx0.le)
            (Real.rpow_nonneg hLx_pos.le A)
  -- Large `x ≥ X₀`: main proof!
  have hx16 : 16 ≤ x := hX0_16.trans hge
  set y : ℝ := x / (Real.log x) ^ K_y with hy_def
  have hy_ge4 : 4 ≤ y := by
    have hsq_ge : 4 * K_sqrt3 ≤ Real.sqrt x := by
      have h1 : (4 * K_sqrt3) ^ 2 ≤ x := by
        have := (le_max_right (max 16 X₁) ((4 * K_sqrt3) ^ 2 + 1)).trans hge
        linarith
      exact Real.le_sqrt_of_sq_le h1
    have hlogK := hlog_sq3 x hx4
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos K_y)]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith [Real.sqrt_nonneg x]
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hy_le_x : y ≤ x := div_le_self hx0.le (Real.one_le_rpow hLx_gt1.le (by dsimp only [K_y]; linarith))
  have hLy_ge_half : Real.log x / 2 ≤ Real.log y := by
    have hlt : K_y * Real.log (Real.log x) / Real.log x < 1 / 2 :=
      hX₁ x (((le_max_right 16 X₁).trans (le_max_left _ _)).trans hge)
    have hmul : K_y * Real.log (Real.log x) < Real.log x / 2 := by
      have := (div_lt_iff₀ hLx_pos).mp hlt
      linarith
    have hlogy : Real.log y = Real.log x - K_y * Real.log (Real.log x) := by
      rw [hy_def, Real.log_div hx0.ne' (Real.rpow_pos_of_pos hLx_pos K_y).ne',
        Real.log_rpow hLx_pos]
    linarith
  have hLy_pos : 0 < Real.log y := by linarith
  -- Bound `log (2 * Q) ≤ 2 * log x` and `log Q + 1 ≤ 2 * log x`
  have h2Q_le_x2 : 2 * (Q : ℝ) ≤ x ^ 2 := by
    have hsq_le : Real.sqrt x ≤ x := by
      have : x ≤ x ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
    nlinarith
  have hlog2Q_le : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log x := by
    have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ1
    calc Real.log (2 * (Q : ℝ)) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) h2Q_le_x2
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlogQ_add1_le : Real.log (Q : ℝ) + 1 ≤ 2 * Real.log x := by
    have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ1
    have h1 : Real.log (Q : ℝ) ≤ Real.log x := by
      have hsq_le : Real.sqrt x ≤ x := by
        have : x ≤ x ^ 2 := by nlinarith
        exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
      exact Real.log_le_log hQpos (hQ_le_sqrt.trans hsq_le)
    linarith
  -- Step A: Compare `π(x)` to `li(x)` using Siegel–Walfisz at `q = 1`
  set liX : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t
  have hpi_sub_li : |((primeCount x : ℝ) - liX)| ≤ C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)) := by
    rw [primeCount_eq_primeCountAP_one]
    have h1 := hsw1 x hx4 1 (by simp [hLx_gt1.le]) 0 (Nat.coprime_one_right 0)
    simpa [liX] using h1
  -- Step B: For each `q ∈ Icc 1 Q` and coprime `a`, bound `|π(x; q, a) - π(x) / φ(q)|`
  have hper_qa : ∀ q ∈ Finset.Icc 1 Q, ∀ a : ℕ, Nat.Coprime a q →
      |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
        (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)| ≤
      |((primeCount x : ℝ) - liX)| / (q.totient : ℝ) +
      (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x) / Real.log x +
      (2 / Real.log 2) / (q.totient : ℝ) +
      ((q : ℝ)⁻¹ * (y / Real.log 2) + Real.log y / Real.log 2 + (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2)) +
      (∫ t in y..x, Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)) +
      (∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2)) := by
    intro q hq a hcop
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq0 : 0 < q := by omega
    have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq0)
    -- Triangle inequality via `liX / φ(q)`
    have htri0 :
        |(Stage2DirichletAP.primeCountAP q a x : ℝ) - (primeCount x : ℝ) / (q.totient : ℝ)| ≤
        |(Stage2DirichletAP.primeCountAP q a x : ℝ) - liX / (q.totient : ℝ)| +
          |((primeCount x : ℝ) - liX)| / (q.totient : ℝ) := by
      have heq : (Stage2DirichletAP.primeCountAP q a x : ℝ) - (primeCount x : ℝ) / (q.totient : ℝ) =
          ((Stage2DirichletAP.primeCountAP q a x : ℝ) - liX / (q.totient : ℝ)) -
          ((primeCount x : ℝ) - liX) / (q.totient : ℝ) := by ring
      rw [heq]
      calc _ ≤ |(Stage2DirichletAP.primeCountAP q a x : ℝ) - liX / (q.totient : ℝ)| +
              |((primeCount x : ℝ) - liX) / (q.totient : ℝ)| := abs_sub _ _
        _ = _ := by rw [abs_div, abs_of_pos hphi_pos]
    -- Integrability helpers on `[u, v] ⊆ [2, x]`
    have hint_inv2 : ∀ u v : ℝ, 2 ≤ u → u ≤ v →
        IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ 2) volume u v := by
      intro u v hu huv
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le huv]
      refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
      · intro t ht; exact ne_of_gt (by linarith [hu, ht.1])
      · intro t ht; exact pow_ne_zero 2 (Real.log_pos (by linarith [hu, ht.1])).ne'
    have hth_triv : ∀ t : ℝ, 2 ≤ t →
        |Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)| ≤ 7 * t := by
      intro t ht2
      have h1 : Stage2DirichletAP.chebyshevThetaAP q a t ≤ 6 * t := by
        have ha1 := Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a t
        have ha2 : Stage2DirichletAP.chebyshevPsiAP q a t ≤ RHDirect.chebyshevPsi t := by
          unfold Stage2DirichletAP.chebyshevPsiAP RHDirect.chebyshevPsi
          refine Finset.sum_le_sum fun n _ => ?_
          split_ifs
          · exact le_rfl
          · exact ArithmeticFunction.vonMangoldt_nonneg
        exact (ha1.trans ha2).trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith))
      have h2 := Stage2DirichletAP.chebyshevThetaAP_nonneg q a t
      have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq0
      have h3 : t / (q.totient : ℝ) ≤ t := by
        calc t / (q.totient : ℝ) ≤ t / 1 := div_le_div_of_nonneg_left (by linarith) zero_lt_one hphi_ge1
          _ = t := div_one t
      have h4 : 0 ≤ t / (q.totient : ℝ) := div_nonneg (by linarith) hphi_pos.le
      rw [abs_le]; constructor <;> linarith
    have hint_err : ∀ u v : ℝ, 2 ≤ u → u ≤ v →
        IntervalIntegrable
          (fun t : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2)) volume u v := by
      intro u v hu huv
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr ?_
      refine Integrable.mono'
        (integrableOn_const (C := 7 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
      · exact (((measurable_chebyshevThetaAP' q a).sub (measurable_id.div_const _)).div
          (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
        have ht2 : 2 ≤ t := hu.trans ht.1.le
        have ht0 : 0 < t := by linarith
        have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
        have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
        calc |Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)| / (t * (Real.log t) ^ 2)
            ≤ (7 * t) / (t * (Real.log 2) ^ 2) := by
              refine div_le_div₀ (by positivity) (hth_triv t ht2) (by positivity) ?_
              gcongr
          _ = 7 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']
    -- Exact Abel decomposition
    have hsplit_int :
        ∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a t / (t * (Real.log t) ^ 2) =
          (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) / (q.totient : ℝ) +
          ∫ t in (2 : ℝ)..x,
            (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
              (t * (Real.log t) ^ 2) := by
      have hconst : (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) / (q.totient : ℝ) =
          ∫ t in (2 : ℝ)..x, (1 / (q.totient : ℝ)) * (1 / (Real.log t) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]; ring
      rw [hconst, ← intervalIntegral.integral_add ((hint_inv2 2 x le_rfl hx2).const_mul _)
        (hint_err 2 x le_rfl hx2)]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx2] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hlt0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      field_simp [ht0.ne', hlt0.ne', hphi_pos.ne']
      ring
    have hdecomp :
        (Stage2DirichletAP.primeCountAP q a x : ℝ) - liX / (q.totient : ℝ) =
          (Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x +
            (2 / Real.log 2) / (q.totient : ℝ) +
            (∫ t in (2 : ℝ)..y,
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2)) +
            (∫ t in y..x,
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2)) := by
      dsimp only [liX]
      rw [Stage10SiegelWalfiszFull.primeCountAP_eq_abel_thetaAP q a hx2,
        Stage10SiegelWalfiszFull.integral_inv_log_eq hx2, hsplit_int,
        ← intervalIntegral.integral_add_adjacent_intervals
          (hint_err 2 y le_rfl hy2) (hint_err y x hy2 hy_le_x)]
      ring
    -- Bound each of the 4 terms in `hdecomp`
    -- Term 1: boundary term at `x`
    have hbd1 : |(Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x| ≤
        (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x) / Real.log x := by
      rw [abs_div, abs_of_pos hLx_pos]
      refine div_le_div_of_nonneg_right ?_ hLx_pos.le
      have h1 : |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
          Stage11BombieriVinogradov.psiAPMaxError q x :=
        Stage11BombieriVinogradov.abs_chebyshevPsiAP_sub_le_psiAPMaxError hq0 hcop x
      have h2 : 0 ≤ Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x :=
        sub_nonneg.mpr (Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a x)
      have h3 : Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x ≤
          Real.sqrt x * Real.log x :=
        Stage2DirichletAP.chebyshevPsiAP_sub_chebyshevThetaAP_le q a (by linarith)
      have heq : Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ) =
          (Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)) -
          (Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x) := by ring
      rw [heq]
      calc _ ≤ |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| +
              |Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x| :=
            abs_sub _ _
        _ = |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| +
              (Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevThetaAP q a x) := by
            rw [abs_of_nonneg h2]
        _ ≤ _ := by linarith
    -- Term 2: constant `(2 / log 2) / φ(q)`
    have hbd2 : |(2 / Real.log 2) / (q.totient : ℝ)| = (2 / Real.log 2) / (q.totient : ℝ) :=
      abs_of_pos (by positivity)
    -- Term 3: low integral `[2, y]`
    have hbd3 : |∫ t in (2 : ℝ)..y,
          (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2)| ≤
        (q : ℝ)⁻¹ * (y / Real.log 2) + Real.log y / Real.log 2 +
          (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2) := by
      have hint_rhs : IntervalIntegrable
          (fun t : ℝ => (q : ℝ)⁻¹ / Real.log 2 + (t * Real.log 2)⁻¹ +
            (q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2) volume 2 y := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hy2]
        refine (continuousOn_const.add ?_).add continuousOn_const
        refine (continuousOn_id.mul continuousOn_const).inv₀ ?_
        intro t ht; exact (mul_pos (show 0 < id t by dsimp; linarith [ht.1]) hlog2_pos).ne'
      have hle_abs : |∫ t in (2 : ℝ)..y,
            (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
              (t * (Real.log t) ^ 2)| ≤
          ∫ t in (2 : ℝ)..y,
            |(Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
              (t * (Real.log t) ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs hy2
      have hmono : ∫ t in (2 : ℝ)..y,
            |(Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
              (t * (Real.log t) ^ 2)| ≤
          ∫ t in (2 : ℝ)..y,
            ((q : ℝ)⁻¹ / Real.log 2 + (t * Real.log 2)⁻¹ +
              (q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2) := by
        refine intervalIntegral.integral_mono_on hy2 (hint_err 2 y le_rfl hy2).abs hint_rhs fun t ht => ?_
        have ht2 : 2 ≤ t := ht.1
        have ht0 : 0 < t := by linarith
        have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
        have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
        have htriv := chebyshevThetaAP_le_triv hq1 a (by linarith : 1 ≤ t)
        have hnn_th := Stage2DirichletAP.chebyshevThetaAP_nonneg q a t
        have hnn_m : 0 ≤ t / (q.totient : ℝ) := div_nonneg ht0.le hphi_pos.le
        have habs_num : |Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)| ≤
            (t / (q : ℝ) + 1) * Real.log t + t / (q.totient : ℝ) := by
          rw [abs_le]; constructor <;> linarith
        rw [abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
        have hqR_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq0
        calc |Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)| / (t * (Real.log t) ^ 2)
            ≤ ((t / (q : ℝ) + 1) * Real.log t + t / (q.totient : ℝ)) / (t * (Real.log t) ^ 2) :=
              div_le_div_of_nonneg_right habs_num (by positivity)
          _ = (q : ℝ)⁻¹ / Real.log t + (t * Real.log t)⁻¹ + (q.totient : ℝ)⁻¹ / (Real.log t) ^ 2 := by
              field_simp [ht0.ne', hlt_pos.ne', hqR_pos.ne', hphi_pos.ne']
          _ ≤ (q : ℝ)⁻¹ / Real.log 2 + (t * Real.log 2)⁻¹ + (q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2 := by
              have h1 : (q : ℝ)⁻¹ / Real.log t ≤ (q : ℝ)⁻¹ / Real.log 2 :=
                div_le_div_of_nonneg_left (by positivity) hlog2_pos hlt_ge
              have h2 : (t * Real.log t)⁻¹ ≤ (t * Real.log 2)⁻¹ :=
                inv_anti₀ (mul_pos ht0 hlog2_pos) (mul_le_mul_of_nonneg_left hlt_ge ht0.le)
              have h3 : (q.totient : ℝ)⁻¹ / (Real.log t) ^ 2 ≤ (q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2 :=
                div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlog2_pos) (by nlinarith)
              linarith
      -- Evaluate the RHS integral explicitly
      have hint_invt : IntervalIntegrable (fun t : ℝ => (t * Real.log 2)⁻¹) volume 2 y := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hy2]
        refine (continuousOn_id.mul continuousOn_const).inv₀ ?_
        intro t ht; exact (mul_pos (show 0 < id t by dsimp; linarith [ht.1]) hlog2_pos).ne'
      have hval_invt : ∫ t in (2 : ℝ)..y, (t * Real.log 2)⁻¹ = (Real.log y - Real.log 2) / Real.log 2 := by
        have hfun : (fun t : ℝ => (t * Real.log 2)⁻¹) = fun t => (Real.log 2)⁻¹ * t⁻¹ := by
          funext t; rw [mul_inv, mul_comm]
        rw [hfun, intervalIntegral.integral_const_mul,
          integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) hy0, Real.log_div hy0.ne' (by norm_num)]
        ring
      have hval_rhs :
          ∫ t in (2 : ℝ)..y,
            ((q : ℝ)⁻¹ / Real.log 2 + (t * Real.log 2)⁻¹ + (q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2) =
          (y - 2) * ((q : ℝ)⁻¹ / Real.log 2) + (Real.log y - Real.log 2) / Real.log 2 +
            (y - 2) * ((q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2) := by
        rw [intervalIntegral.integral_add
            (intervalIntegrable_const.add hint_invt) intervalIntegrable_const,
          intervalIntegral.integral_add intervalIntegrable_const hint_invt,
          intervalIntegral.integral_const, intervalIntegral.integral_const,
          smul_eq_mul, smul_eq_mul, hval_invt]
      calc |∫ t in (2 : ℝ)..y,
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2)|
          ≤ _ := hle_abs.trans hmono
        _ = (y - 2) * ((q : ℝ)⁻¹ / Real.log 2) + (Real.log y - Real.log 2) / Real.log 2 +
              (y - 2) * ((q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2) := hval_rhs
        _ ≤ (q : ℝ)⁻¹ * (y / Real.log 2) + Real.log y / Real.log 2 +
              (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2) := by
            have h1 : (y - 2) * ((q : ℝ)⁻¹ / Real.log 2) ≤ (q : ℝ)⁻¹ * (y / Real.log 2) := by
              have : 0 ≤ (q : ℝ)⁻¹ / Real.log 2 := by positivity
              have heq : y * ((q : ℝ)⁻¹ / Real.log 2) = (q : ℝ)⁻¹ * (y / Real.log 2) := by ring
              nlinarith
            have h2 : (Real.log y - Real.log 2) / Real.log 2 ≤ Real.log y / Real.log 2 :=
              div_le_div_of_nonneg_right (by linarith) hlog2_pos.le
            have h3 : (y - 2) * ((q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2) ≤
                (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2) := by
              have : 0 ≤ (q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2 := by positivity
              have heq : y * ((q.totient : ℝ)⁻¹ / (Real.log 2) ^ 2) =
                  (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2) := by ring
              nlinarith
            linarith
    -- Term 4: high integral `[y, x]`
    have hint_psi : IntervalIntegrable
        (fun t : ℝ => Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)) volume y x := by
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hy_le_x).mpr ?_
      refine Integrable.mono'
        (integrableOn_const (C := 7 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
      · exact ((measurable_psiAPMaxError q).div
          (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
        have ht2 : 2 ≤ t := hy2.trans ht.1.le
        have ht0 : 0 < t := by linarith
        have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
        have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
        rw [Real.norm_of_nonneg (div_nonneg (Stage11BombieriVinogradov.psiAPMaxError_nonneg q t) (by positivity))]
        calc Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)
            ≤ (7 * t) / (t * (Real.log 2) ^ 2) := by
              refine div_le_div₀ (by positivity) (psiAPMaxError_le_seven_mul hq1 ht2) (by positivity) ?_
              gcongr
          _ = 7 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']
    have hint_sqrt : IntervalIntegrable
        (fun t : ℝ => (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2)) volume y x := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hy_le_x]
      refine (Real.continuous_sqrt.continuousOn.mul (Real.continuousOn_log.mono ?_)).div
        (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_
      · intro t ht; exact ne_of_gt (by linarith [hy2, ht.1])
      · intro t ht; exact ne_of_gt (by linarith [hy2, ht.1])
      · intro t ht
        exact (mul_pos (by linarith [hy2, ht.1]) (sq_pos_of_pos (Real.log_pos (by linarith [hy2, ht.1])))).ne'
    have hbd4 : |∫ t in y..x,
          (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2)| ≤
        (∫ t in y..x, Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)) +
        (∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2)) := by
      rw [← intervalIntegral.integral_add hint_psi hint_sqrt]
      refine (intervalIntegral.abs_integral_le_integral_abs hy_le_x).trans ?_
      refine intervalIntegral.integral_mono_on hy_le_x (hint_err y x hy2 hy_le_x).abs
        (hint_psi.add hint_sqrt) fun t ht => ?_
      have ht2 : 2 ≤ t := hy2.trans ht.1
      have ht0 : 0 < t := by linarith
      have hlt_pos : 0 < Real.log t := Real.log_pos (by linarith)
      rw [abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlt_pos)), ← add_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h1 := Stage11BombieriVinogradov.abs_chebyshevPsiAP_sub_le_psiAPMaxError hq0 hcop t
      have h2 : 0 ≤ Stage2DirichletAP.chebyshevPsiAP q a t - Stage2DirichletAP.chebyshevThetaAP q a t :=
        sub_nonneg.mpr (Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a t)
      have h3 := Stage2DirichletAP.chebyshevPsiAP_sub_chebyshevThetaAP_le q a (by linarith : 1 ≤ t)
      have heq : Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ) =
          (Stage2DirichletAP.chebyshevPsiAP q a t - t / (q.totient : ℝ)) -
          (Stage2DirichletAP.chebyshevPsiAP q a t - Stage2DirichletAP.chebyshevThetaAP q a t) := by ring
      rw [heq]
      calc _ ≤ |Stage2DirichletAP.chebyshevPsiAP q a t - t / (q.totient : ℝ)| +
              |Stage2DirichletAP.chebyshevPsiAP q a t - Stage2DirichletAP.chebyshevThetaAP q a t| :=
            abs_sub _ _
        _ = |Stage2DirichletAP.chebyshevPsiAP q a t - t / (q.totient : ℝ)| +
              (Stage2DirichletAP.chebyshevPsiAP q a t - Stage2DirichletAP.chebyshevThetaAP q a t) := by
            rw [abs_of_nonneg h2]
        _ ≤ _ := by linarith
    -- Combine `htri0` + `hdecomp` + `hbd1..4`
    have hdecomp_abs : |(Stage2DirichletAP.primeCountAP q a x : ℝ) - liX / (q.totient : ℝ)| ≤
        (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x) / Real.log x +
        (2 / Real.log 2) / (q.totient : ℝ) +
        ((q : ℝ)⁻¹ * (y / Real.log 2) + Real.log y / Real.log 2 +
          (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2)) +
        (∫ t in y..x, Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)) +
        (∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2)) := by
      rw [hdecomp]
      have htri1 := abs_add_le
        ((Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x +
          (2 / Real.log 2) / (q.totient : ℝ) +
          ∫ t in (2 : ℝ)..y, (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2))
        (∫ t in y..x, (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2))
      have htri2 := abs_add_le
        ((Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x +
          (2 / Real.log 2) / (q.totient : ℝ))
        (∫ t in (2 : ℝ)..y, (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2))
      have htri3 := abs_add_le
        ((Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x)
        ((2 / Real.log 2) / (q.totient : ℝ))
      linarith
    have hprime_eq : (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) = (primeCount x : ℝ) := rfl
    rw [hprime_eq]
    linarith
  -- Step C: Take `sup'` over `a` and sum over `q ∈ Icc 1 Q`!
  have hsum_sup :
      ∑ q ∈ Finset.Icc 1 Q,
        (if h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
          ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' h
            (fun a => |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
              (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|)
        else 0) ≤
      ∑ q ∈ Finset.Icc 1 Q, (
        |((primeCount x : ℝ) - liX)| / (q.totient : ℝ) +
        (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x) / Real.log x +
        (2 / Real.log 2) / (q.totient : ℝ) +
        ((q : ℝ)⁻¹ * (y / Real.log 2) + Real.log y / Real.log 2 +
          (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2)) +
        (∫ t in y..x, Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)) +
        (∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2))) := by
    refine Finset.sum_le_sum fun q hq => ?_
    split_ifs with hne
    · refine Finset.sup'_le hne _ fun a ha => hper_qa q hq a (Finset.mem_filter.mp ha).2
    · have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have h1 : 0 ≤ |((primeCount x : ℝ) - liX)| / (q.totient : ℝ) := by positivity
      have h2 : 0 ≤ (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x) / Real.log x :=
        div_nonneg (add_nonneg (Stage11BombieriVinogradov.psiAPMaxError_nonneg q x) (by positivity)) hLx_pos.le
      have h3 : 0 ≤ (2 / Real.log 2) / (q.totient : ℝ) := by positivity
      have h4 : 0 ≤ (q : ℝ)⁻¹ * (y / Real.log 2) + Real.log y / Real.log 2 +
          (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2) := by positivity
      have h5 : 0 ≤ ∫ t in y..x, Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2) :=
        intervalIntegral.integral_nonneg hy_le_x fun t ht =>
          div_nonneg (Stage11BombieriVinogradov.psiAPMaxError_nonneg q t)
            (mul_nonneg (by linarith [hy0, ht.1]) (sq_nonneg _))
      have h6 : 0 ≤ ∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2) :=
        intervalIntegral.integral_nonneg hy_le_x fun t ht =>
          div_nonneg (mul_nonneg (Real.sqrt_nonneg t) (Real.log_nonneg (by linarith [hy2, ht.1])))
            (mul_nonneg (by linarith [hy0, ht.1]) (sq_nonneg _))
      linarith
  -- Split the sum into 6 pieces and bound each by `c_i * x / (log x)^{A'}`
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_sup
  -- Piece 1: `∑ |π(x) - li(x)| / φ(q)`
  have hP1 : ∑ q ∈ Finset.Icc 1 Q, |((primeCount x : ℝ) - liX)| / (q.totient : ℝ) ≤
      (6 * C_sw * K_sw_exp * 2) * x / (Real.log x) ^ A' := by
    have hpull : ∑ q ∈ Finset.Icc 1 Q, |((primeCount x : ℝ) - liX)| / (q.totient : ℝ) =
        |((primeCount x : ℝ) - liX)| * ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => div_eq_mul_inv _ _
    rw [hpull]
    have hsum_phi := (sum_inv_totient_Icc_le hQ1).trans (mul_le_mul_of_nonneg_left hlog2Q_le (by norm_num))
    have hexp := hsw_exp x hx4
    have hpow_split : (Real.log x) ^ (A' + 1) = (Real.log x) ^ A' * Real.log x := by
      rw [Real.rpow_add hLx_pos, Real.rpow_one]
    rw [hpow_split] at hexp
    have hexp_div : Real.log x * Real.exp (-c_sw * Real.sqrt (Real.log x)) ≤
        K_sw_exp / (Real.log x) ^ A' := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
      linarith
    calc |((primeCount x : ℝ) - liX)| * ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹
        ≤ (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) * (6 * (2 * Real.log x)) :=
          mul_le_mul hpi_sub_li hsum_phi (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = (6 * C_sw * 2) * x * (Real.log x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by ring
      _ ≤ (6 * C_sw * 2) * x * (K_sw_exp / (Real.log x) ^ A') :=
          mul_le_mul_of_nonneg_left hexp_div (by positivity)
      _ = (6 * C_sw * K_sw_exp * 2) * x / (Real.log x) ^ A' := by ring
  -- Piece 2: `∑ (psiAPMaxError q x + √x log x) / log x`
  have hQ_le_Qpsi_x : Q ≤ ⌊Real.sqrt x / (Real.log x) ^ B_ψ⌋₊ := by
    refine Nat.floor_mono ?_
    refine div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (Real.rpow_pos_of_pos hLx_pos B_ψ) ?_
    refine Real.rpow_le_rpow_of_exponent_le hLx_gt1.le ?_
    have h1 : B_ψ ≤ B_ψ + K_y / 2 := by dsimp only [K_y]; linarith
    exact h1.trans (le_max_left _ _)
  have hP2 : ∑ q ∈ Finset.Icc 1 Q,
        (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x) / Real.log x ≤
      (C_ψ + 1) * x / (Real.log x) ^ A' := by
    have hsplit : ∑ q ∈ Finset.Icc 1 Q,
          (Stage11BombieriVinogradov.psiAPMaxError q x + Real.sqrt x * Real.log x) / Real.log x =
        (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q x) / Real.log x +
          (Q : ℝ) * Real.sqrt x := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul, add_div]
      congr 1
      field_simp [hLx_pos.ne']
    rw [hsplit]
    have hbv_x : ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q x ≤
        C_ψ * x / (Real.log x) ^ A' := by
      calc _ ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B_ψ⌋₊,
              Stage11BombieriVinogradov.psiAPMaxError q x :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQ_le_Qpsi_x)
              fun _ _ _ => Stage11BombieriVinogradov.psiAPMaxError_nonneg _ _
        _ ≤ C_ψ * x / (Real.log x) ^ A' := hbv_ψ x (by linarith)
    have h1 : (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q x) / Real.log x ≤
        C_ψ * x / (Real.log x) ^ A' :=
      (div_le_self (Finset.sum_nonneg fun _ _ => Stage11BombieriVinogradov.psiAPMaxError_nonneg _ _)
        hLx_gt1.le).trans hbv_x
    have h2 : (Q : ℝ) * Real.sqrt x ≤ x / (Real.log x) ^ A' := by
      have hB_ge_A' : A' ≤ B := by
        have : A' ≤ A' + K_y / 2 + 1 := by dsimp only [K_y]; linarith
        exact this.trans (le_max_right _ _)
      calc (Q : ℝ) * Real.sqrt x ≤ (Real.sqrt x / (Real.log x) ^ B) * Real.sqrt x :=
            mul_le_mul_of_nonneg_right hQ_le_real (Real.sqrt_nonneg x)
        _ = (Real.sqrt x * Real.sqrt x) / (Real.log x) ^ B := by ring
        _ = x / (Real.log x) ^ B := by rw [Real.mul_self_sqrt hx0.le]
        _ ≤ x / (Real.log x) ^ A' :=
            div_le_div_of_nonneg_left hx0.le (Real.rpow_pos_of_pos hLx_pos A')
              (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le hB_ge_A')
    linarith [show (C_ψ + 1) * x / (Real.log x) ^ A' = C_ψ * x / (Real.log x) ^ A' + x / (Real.log x) ^ A' by ring]
  -- Piece 3: `∑ (2 / log 2) / φ(q)`
  have h2Q_le_x : 2 * (Q : ℝ) ≤ x := by
    have h4sq : 4 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    nlinarith [Real.mul_self_sqrt hx0.le]
  have hlog2Q_le_x : Real.log (2 * (Q : ℝ)) ≤ Real.log x :=
    Real.log_le_log (by positivity) h2Q_le_x
  have hP3 : ∑ q ∈ Finset.Icc 1 Q, (2 / Real.log 2) / (q.totient : ℝ) ≤
      ((12 / Real.log 2) * K_sqrt2) * x / (Real.log x) ^ A' := by
    have hpull : ∑ q ∈ Finset.Icc 1 Q, (2 / Real.log 2) / (q.totient : ℝ) =
        (2 / Real.log 2) * ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => div_eq_mul_inv _ _
    rw [hpull]
    have hsum_phi := (sum_inv_totient_Icc_le hQ1).trans (mul_le_mul_of_nonneg_left hlog2Q_le_x (by norm_num))
    have hsq_le_x : Real.sqrt x ≤ x := by
      have : x ≤ x ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
    have hlog_le : Real.log x ≤ K_sqrt2 * x / (Real.log x) ^ A' := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
      have h1 : Real.log x * (Real.log x) ^ A' = (Real.log x) ^ (A' + 1) := by
        rw [Real.rpow_add hLx_pos, Real.rpow_one, mul_comm]
      rw [h1]
      have h2 : (Real.log x) ^ (A' + 1) ≤ (Real.log x) ^ (A' + 2) :=
        Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by linarith)
      exact h2.trans ((hlog_sq2 x hx4).trans (mul_le_mul_of_nonneg_left hsq_le_x hKsq2.le))
    calc (2 / Real.log 2) * ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹
        ≤ (2 / Real.log 2) * (6 * Real.log x) :=
          mul_le_mul_of_nonneg_left hsum_phi (by positivity)
      _ = (12 / Real.log 2) * Real.log x := by ring
      _ ≤ (12 / Real.log 2) * (K_sqrt2 * x / (Real.log x) ^ A') :=
          mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = ((12 / Real.log 2) * K_sqrt2) * x / (Real.log x) ^ A' := by ring
  -- Piece 4: low-integral bound sum over `q`
  have hP4 : ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ)⁻¹ * (y / Real.log 2) + Real.log y / Real.log 2 +
          (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2)) ≤
      (2 / Real.log 2 + (1 / Real.log 2) * K_sqrt2 + 12 / (Real.log 2) ^ 2) * x / (Real.log x) ^ A' := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hLy_le_Lx : Real.log y ≤ Real.log x := Real.log_le_log hy0 hy_le_x
    have hlogx_mul_y : Real.log x * y ≤ x / (Real.log x) ^ A' := by
      have hpow_ge : (Real.log x) ^ (A' + 1) ≤ (Real.log x) ^ K_y :=
        Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [K_y]; linarith)
      have hpow_split : (Real.log x) ^ (A' + 1) = (Real.log x) ^ A' * Real.log x := by
        rw [Real.rpow_add hLx_pos, Real.rpow_one]
      rw [hy_def, le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
      have hmul : Real.log x * (x / (Real.log x) ^ K_y) * (Real.log x) ^ A' =
          x * ((Real.log x) ^ (A' + 1) / (Real.log x) ^ K_y) := by
        rw [hpow_split]; ring
      rw [hmul]
      have hdiv_le1 : (Real.log x) ^ (A' + 1) / (Real.log x) ^ K_y ≤ 1 :=
        (div_le_one (Real.rpow_pos_of_pos hLx_pos K_y)).mpr hpow_ge
      nlinarith
    have h4a : ∑ q ∈ Finset.Icc 1 Q, (q : ℝ)⁻¹ * (y / Real.log 2) ≤
        (2 / Real.log 2) * x / (Real.log x) ^ A' := by
      rw [← Finset.sum_mul]
      calc (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)⁻¹) * (y / Real.log 2)
          ≤ (2 * Real.log x) * (y / Real.log 2) :=
            mul_le_mul_of_nonneg_right ((harmonic_sum_le_log_add_one hQ1).trans hlogQ_add1_le) (by positivity)
        _ = (2 / Real.log 2) * (Real.log x * y) := by ring
        _ ≤ (2 / Real.log 2) * (x / (Real.log x) ^ A') :=
            mul_le_mul_of_nonneg_left hlogx_mul_y (by positivity)
        _ = (2 / Real.log 2) * x / (Real.log x) ^ A' := by ring
    have h4b : ∑ _q ∈ Finset.Icc 1 Q, (Real.log y / Real.log 2) ≤
        ((1 / Real.log 2) * K_sqrt2) * x / (Real.log x) ^ A' := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      have hsq_log : Real.sqrt x * Real.log x ≤ K_sqrt2 * x / (Real.log x) ^ A' := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
        have h1 : Real.log x * (Real.log x) ^ A' = (Real.log x) ^ (A' + 1) := by
          rw [Real.rpow_add hLx_pos, Real.rpow_one, mul_comm]
        have h2 : (Real.log x) ^ (A' + 1) ≤ (Real.log x) ^ (A' + 2) :=
          Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by linarith)
        have h3 := hlog_sq2 x hx4
        calc Real.sqrt x * Real.log x * (Real.log x) ^ A'
            = Real.sqrt x * (Real.log x) ^ (A' + 1) := by rw [← h1]; ring
          _ ≤ Real.sqrt x * (K_sqrt2 * Real.sqrt x) :=
              mul_le_mul_of_nonneg_left (h2.trans h3) (Real.sqrt_nonneg x)
          _ = K_sqrt2 * (Real.sqrt x * Real.sqrt x) := by ring
          _ = K_sqrt2 * x := by rw [Real.mul_self_sqrt hx0.le]
      calc (Q : ℝ) * (Real.log y / Real.log 2)
          ≤ Real.sqrt x * (Real.log x / Real.log 2) :=
            mul_le_mul hQ_le_sqrt (div_le_div_of_nonneg_right hLy_le_Lx hlog2_pos.le)
              (by positivity) (Real.sqrt_nonneg x)
        _ = (1 / Real.log 2) * (Real.sqrt x * Real.log x) := by ring
        _ ≤ (1 / Real.log 2) * (K_sqrt2 * x / (Real.log x) ^ A') :=
            mul_le_mul_of_nonneg_left hsq_log (by positivity)
        _ = ((1 / Real.log 2) * K_sqrt2) * x / (Real.log x) ^ A' := by ring
    have h4c : ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ * (y / (Real.log 2) ^ 2) ≤
        (12 / (Real.log 2) ^ 2) * x / (Real.log x) ^ A' := by
      rw [← Finset.sum_mul]
      have hsum_phi := (sum_inv_totient_Icc_le hQ1).trans (mul_le_mul_of_nonneg_left hlog2Q_le (by norm_num))
      calc (∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹) * (y / (Real.log 2) ^ 2)
          ≤ (6 * (2 * Real.log x)) * (y / (Real.log 2) ^ 2) :=
            mul_le_mul_of_nonneg_right hsum_phi (by positivity)
        _ = (12 / (Real.log 2) ^ 2) * (Real.log x * y) := by ring
        _ ≤ (12 / (Real.log 2) ^ 2) * (x / (Real.log x) ^ A') :=
            mul_le_mul_of_nonneg_left hlogx_mul_y (by positivity)
        _ = (12 / (Real.log 2) ^ 2) * x / (Real.log x) ^ A' := by ring
    linarith [show (2 / Real.log 2 + (1 / Real.log 2) * K_sqrt2 + 12 / (Real.log 2) ^ 2) * x / (Real.log x) ^ A' =
        (2 / Real.log 2) * x / (Real.log x) ^ A' + ((1 / Real.log 2) * K_sqrt2) * x / (Real.log x) ^ A' +
        (12 / (Real.log 2) ^ 2) * x / (Real.log x) ^ A' by ring]
  -- Helper: `√y = √x / (log x)^{K_y / 2}`
  have hsqrt_y : Real.sqrt y = Real.sqrt x / (Real.log x) ^ (K_y / 2) := by
    rw [hy_def, Real.sqrt_div hx0.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLx_pos.le]
    congr 1; ring
  -- Piece 5: high integral of `psiAPMaxError`
  have hP5 : ∑ q ∈ Finset.Icc 1 Q,
        (∫ t in y..x, Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)) ≤
      (C_ψ * (2 : ℝ) ^ (A' + 2)) * x / (Real.log x) ^ A' := by
    have hint_each : ∀ q ∈ Finset.Icc 1 Q,
        IntervalIntegrable
          (fun t : ℝ => Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)) volume y x := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hy_le_x).mpr ?_
      refine Integrable.mono'
        (integrableOn_const (C := 7 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
      · exact ((measurable_psiAPMaxError q).div
          (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
        have ht2 : 2 ≤ t := hy2.trans ht.1.le
        have ht0 : 0 < t := by linarith
        have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
        have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
        rw [Real.norm_of_nonneg (div_nonneg (Stage11BombieriVinogradov.psiAPMaxError_nonneg q t) (by positivity))]
        calc Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)
            ≤ (7 * t) / (t * (Real.log 2) ^ 2) := by
              refine div_le_div₀ (by positivity) (psiAPMaxError_le_seven_mul hq1 ht2) (by positivity) ?_
              gcongr
          _ = 7 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']
    rw [← intervalIntegral.integral_finsetSum hint_each]
    have hint_sum : IntervalIntegrable
        (fun t : ℝ => ∑ q ∈ Finset.Icc 1 Q,
          Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2)) volume y x := by
      have h := IntervalIntegrable.sum (Finset.Icc 1 Q) hint_each
      exact h.congr fun t _ => Finset.sum_apply t (Finset.Icc 1 Q) _
    have hconst_bound :
        ∫ t in y..x, ∑ q ∈ Finset.Icc 1 Q,
          Stage11BombieriVinogradov.psiAPMaxError q t / (t * (Real.log t) ^ 2) ≤
        ∫ _t in y..x, (C_ψ * (2 : ℝ) ^ (A' + 2)) / (Real.log x) ^ A' := by
      refine intervalIntegral.integral_mono_on hy_le_x hint_sum intervalIntegrable_const fun t ht => ?_
      have ht4 : 4 ≤ t := hy_ge4.trans ht.1
      have ht0 : 0 < t := by linarith
      have hlt_ge : Real.log y ≤ Real.log t := Real.log_le_log hy0 ht.1
      have hlt_le : Real.log t ≤ Real.log x := Real.log_le_log ht0 ht.2
      have hlt_pos : 0 < Real.log t := hLy_pos.trans_le hlt_ge
      have hQ_le_Qpsi_t : Q ≤ ⌊Real.sqrt t / (Real.log t) ^ B_ψ⌋₊ := by
        refine Nat.floor_mono ?_
        have hB_ge : B_ψ + K_y / 2 ≤ B := le_max_left _ _
        have h1 : (Real.log x) ^ (B_ψ + K_y / 2) ≤ (Real.log x) ^ B :=
          Real.rpow_le_rpow_of_exponent_le hLx_gt1.le hB_ge
        calc Real.sqrt x / (Real.log x) ^ B
            ≤ Real.sqrt x / (Real.log x) ^ (B_ψ + K_y / 2) :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (Real.rpow_pos_of_pos hLx_pos _) h1
          _ = (Real.sqrt x / (Real.log x) ^ (K_y / 2)) / (Real.log x) ^ B_ψ := by
              rw [Real.rpow_add hLx_pos, div_div, mul_comm]
          _ = Real.sqrt y / (Real.log x) ^ B_ψ := by rw [← hsqrt_y]
          _ ≤ Real.sqrt t / (Real.log t) ^ B_ψ :=
              div_le_div₀ (Real.sqrt_nonneg t) (Real.sqrt_le_sqrt ht.1)
                (Real.rpow_pos_of_pos hlt_pos B_ψ) (Real.rpow_le_rpow hlt_pos.le hlt_le hBψ.le)
      have hbv_t : ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t ≤
          C_ψ * t / (Real.log t) ^ A' := by
        calc _ ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt t / (Real.log t) ^ B_ψ⌋₊,
                Stage11BombieriVinogradov.psiAPMaxError q t :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQ_le_Qpsi_t)
                fun _ _ _ => Stage11BombieriVinogradov.psiAPMaxError_nonneg _ _
          _ ≤ C_ψ * t / (Real.log t) ^ A' := hbv_ψ t (by linarith)
      rw [← Finset.sum_div]
      have hlogt_pow : (Real.log t) ^ A' * (Real.log t) ^ 2 = (Real.log t) ^ (A' + 2) := by
        rw [Real.rpow_add hlt_pos, Real.rpow_two]
      have hlog_half : (Real.log x / 2) ^ (A' + 2) ≤ (Real.log t) ^ (A' + 2) :=
        Real.rpow_le_rpow (by positivity) (hLy_ge_half.trans hlt_ge) (by linarith)
      have hpow_ge : (Real.log x) ^ A' ≤ (Real.log x) ^ (A' + 2) :=
        Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by linarith)
      calc (∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q t) / (t * (Real.log t) ^ 2)
          ≤ (C_ψ * t / (Real.log t) ^ A') / (t * (Real.log t) ^ 2) :=
            div_le_div_of_nonneg_right hbv_t (by positivity)
        _ = C_ψ / ((Real.log t) ^ A' * (Real.log t) ^ 2) := by
            field_simp [ht0.ne', (Real.rpow_pos_of_pos hlt_pos A').ne', hlt_pos.ne']
        _ = C_ψ / (Real.log t) ^ (A' + 2) := by rw [hlogt_pow]
        _ ≤ C_ψ / (Real.log x / 2) ^ (A' + 2) :=
            div_le_div_of_nonneg_left hCψ.le (Real.rpow_pos_of_pos (by positivity) _) hlog_half
        _ = (C_ψ * (2 : ℝ) ^ (A' + 2)) / (Real.log x) ^ (A' + 2) := by
            rw [Real.div_rpow hLx_pos.le (by norm_num : (0 : ℝ) ≤ 2), div_div_eq_mul_div]
        _ ≤ (C_ψ * (2 : ℝ) ^ (A' + 2)) / (Real.log x) ^ A' :=
            div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hLx_pos A') hpow_ge
    rw [intervalIntegral.integral_const, smul_eq_mul] at hconst_bound
    calc _ ≤ (x - y) * ((C_ψ * (2 : ℝ) ^ (A' + 2)) / (Real.log x) ^ A') := hconst_bound
      _ ≤ x * ((C_ψ * (2 : ℝ) ^ (A' + 2)) / (Real.log x) ^ A') :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (C_ψ * (2 : ℝ) ^ (A' + 2)) * x / (Real.log x) ^ A' := by ring
  -- Piece 6: high integral of `√t * log t / (t * (log t)^2)`
  have hP6 : ∑ _q ∈ Finset.Icc 1 Q,
        (∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2)) ≤
      (1 / Real.log 2) * x / (Real.log x) ^ A' := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hint_sqrt : IntervalIntegrable
        (fun t : ℝ => (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2)) volume y x := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hy_le_x]
      refine (Real.continuous_sqrt.continuousOn.mul (Real.continuousOn_log.mono ?_)).div
        (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_
      · intro t ht; exact ne_of_gt (by linarith [hy2, ht.1])
      · intro t ht; exact ne_of_gt (by linarith [hy2, ht.1])
      · intro t ht
        exact (mul_pos (by linarith [hy2, ht.1]) (sq_pos_of_pos (Real.log_pos (by linarith [hy2, ht.1])))).ne'
    have hint_le : ∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2) ≤
        x / (Real.sqrt y * Real.log 2) := by
      have h1 : ∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2) ≤
          ∫ _t in y..x, 1 / (Real.sqrt y * Real.log 2) := by
        refine intervalIntegral.integral_mono_on hy_le_x hint_sqrt intervalIntegrable_const fun t ht => ?_
        have ht2 : 2 ≤ t := hy2.trans ht.1
        have ht0 : 0 < t := by linarith
        have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
        have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
        have hsq_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
        have heq : (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2) = 1 / (Real.sqrt t * Real.log t) := by
          have hsq2 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
          have hstep : (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2) =
              (Real.sqrt t * Real.log t) / ((Real.sqrt t * Real.sqrt t) * (Real.log t) ^ 2) := by
            rw [hsq2]
          rw [hstep]
          field_simp [hsq_pos.ne', hlt_pos.ne']
        rw [heq]
        exact one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.mpr hy0) hlog2_pos)
          (mul_le_mul (Real.sqrt_le_sqrt ht.1) hlt_ge hlog2_pos.le (Real.sqrt_nonneg t))
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      calc _ ≤ (x - y) * (1 / (Real.sqrt y * Real.log 2)) := h1
        _ ≤ x * (1 / (Real.sqrt y * Real.log 2)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = x / (Real.sqrt y * Real.log 2) := by ring
    have hQ_div_sqy : (Q : ℝ) / Real.sqrt y ≤ 1 / (Real.log x) ^ A' := by
      have hB_ge : A' + K_y / 2 ≤ B := by
        have : A' + K_y / 2 ≤ A' + K_y / 2 + 1 := by linarith
        exact this.trans (le_max_right _ _)
      have h1 : (Real.log x) ^ (A' + K_y / 2) ≤ (Real.log x) ^ B :=
        Real.rpow_le_rpow_of_exponent_le hLx_gt1.le hB_ge
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hy0) (Real.rpow_pos_of_pos hLx_pos A'), one_mul]
      calc (Q : ℝ) * (Real.log x) ^ A'
          ≤ (Real.sqrt x / (Real.log x) ^ B) * (Real.log x) ^ A' :=
            mul_le_mul_of_nonneg_right hQ_le_real (Real.rpow_nonneg hLx_pos.le A')
        _ ≤ (Real.sqrt x / (Real.log x) ^ (A' + K_y / 2)) * (Real.log x) ^ A' :=
            mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (Real.rpow_pos_of_pos hLx_pos _) h1)
              (Real.rpow_nonneg hLx_pos.le A')
        _ = Real.sqrt x / (Real.log x) ^ (K_y / 2) := by
            rw [Real.rpow_add hLx_pos]
            field_simp [(Real.rpow_pos_of_pos hLx_pos A').ne', (Real.rpow_pos_of_pos hLx_pos (K_y / 2)).ne']
        _ = Real.sqrt y := hsqrt_y.symm
    calc (Q : ℝ) * ∫ t in y..x, (Real.sqrt t * Real.log t) / (t * (Real.log t) ^ 2)
        ≤ (Q : ℝ) * (x / (Real.sqrt y * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hint_le (Nat.cast_nonneg Q)
      _ = ((Q : ℝ) / Real.sqrt y) * (x / Real.log 2) := by ring
      _ ≤ (1 / (Real.log x) ^ A') * (x / Real.log 2) :=
          mul_le_mul_of_nonneg_right hQ_div_sqy (by positivity)
      _ = (1 / Real.log 2) * x / (Real.log x) ^ A' := by ring
  -- Combine all 6 pieces and pass from `(log x)^{A'}` to `(log x)^A`
  have hcomb :
      ∑ q ∈ Finset.Icc 1 Q,
        (if h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
          ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' h
            (fun a => |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
              (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|)
        else 0) ≤ C_large * x / (Real.log x) ^ A' := by
    dsimp only [C_large]
    have heq :
        (6 * C_sw * K_sw_exp * 2 + C_ψ + 1 + (12 / Real.log 2) * K_sqrt2 +
          (2 / Real.log 2) + (1 / Real.log 2) * K_sqrt2 + (12 / (Real.log 2) ^ 2) +
          C_ψ * (2 : ℝ) ^ (A' + 2) + 1 / Real.log 2) * x / (Real.log x) ^ A' =
        (6 * C_sw * K_sw_exp * 2) * x / (Real.log x) ^ A' +
        (C_ψ + 1) * x / (Real.log x) ^ A' +
        ((12 / Real.log 2) * K_sqrt2) * x / (Real.log x) ^ A' +
        (2 / Real.log 2 + (1 / Real.log 2) * K_sqrt2 + 12 / (Real.log 2) ^ 2) * x / (Real.log x) ^ A' +
        (C_ψ * (2 : ℝ) ^ (A' + 2)) * x / (Real.log x) ^ A' +
        (1 / Real.log 2) * x / (Real.log x) ^ A' := by ring
    linarith
  calc _ ≤ C_large * x / (Real.log x) ^ A' := hcomb
    _ ≤ C_large * x / (Real.log x) ^ A :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hLx_pos A) hA_pow_le
    _ ≤ C_fin * x / (Real.log x) ^ A :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le)
          (Real.rpow_nonneg hLx_pos.le A)

/-! ### Prime Number Theorem Asymptotics for `primeCount` and `chenGoldbachSet` -/

/-- Prime number counting bound `|π(x) / (x / log x) - 1| ≤ ε` for all sufficiently large `x`. -/
theorem primeCount_asymp :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, 4 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      |(primeCount x : ℝ) / (x / Real.log x) - 1| ≤ ε := by
  intro ε hε
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := Stage10SiegelWalfiszFull.siegel_walfisz_pi_real
  obtain ⟨C_sw, hCsw, hsw1⟩ := hsw_all 1 zero_lt_one
  obtain ⟨K_sw, hKsw, hsw_exp⟩ := log_rpow_mul_exp_neg_sqrt_le hc_sw 2
  obtain ⟨K_sq, hKsq, hlog_sq⟩ := log_rpow_le_const_mul_sqrt 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set M_err : ℝ := C_sw * K_sw + 2 / Real.log 2 + K_sq / (Real.log 2) ^ 2 + 4
  have hM_pos : 0 < M_err := by positivity
  set X₀ : ℝ := max 16 (Real.exp (M_err / ε))
  refine ⟨X₀, le_trans (by norm_num) (le_max_left _ _), fun x hx => ?_⟩
  have hx16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hx4 : 4 ≤ x := by linarith
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hLx_ge : M_err / ε ≤ Real.log x := by
    have hexp : Real.exp (M_err / ε) ≤ x := (le_max_right _ _).trans hx
    exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
  -- `|π(x) - li(x)| ≤ C_sw * x * exp(-c_sw √(log x))`
  have hpi_li : |(primeCount x : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
      C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)) := by
    rw [primeCount_eq_primeCountAP_one]
    simpa [hLx_gt1.le] using hsw1 x hx4 1 (by simp [hLx_gt1.le]) 0 (Nat.coprime_one_right 0)
  -- Bound `∫_2^x 1 / (log t)^2 dt` by splitting at `√x`
  have hsq_ge2 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hsq_le : Real.sqrt x ≤ x := by
    have : x ≤ x ^ 2 := by nlinarith
    exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
  have hint_inv2 : ∀ u v : ℝ, 2 ≤ u → u ≤ v →
      IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ 2) volume u v := by
    intro u v hu huv
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le huv]
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; exact ne_of_gt (by linarith [hu, ht.1])
    · intro t ht; exact pow_ne_zero 2 (Real.log_pos (by linarith [hu, ht.1])).ne'
  have hint_split : ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 =
      (∫ t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log t) ^ 2) +
      (∫ t in (Real.sqrt x)..x, 1 / (Real.log t) ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint_inv2 2 (Real.sqrt x) le_rfl hsq_ge2)
      (hint_inv2 (Real.sqrt x) x hsq_ge2 hsq_le)).symm
  have hint_lo : ∫ t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log t) ^ 2 ≤ Real.sqrt x / (Real.log 2) ^ 2 := by
    have h1 : ∫ t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log t) ^ 2 ≤
        ∫ _t in (2 : ℝ)..(Real.sqrt x), 1 / (Real.log 2) ^ 2 := by
      refine intervalIntegral.integral_mono_on hsq_ge2 (hint_inv2 2 (Real.sqrt x) le_rfl hsq_ge2)
        intervalIntegrable_const fun t ht => ?_
      have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
      exact one_div_le_one_div_of_le (sq_pos_of_pos hlog2_pos) (by nlinarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have : (Real.sqrt x - 2) * (1 / (Real.log 2) ^ 2) ≤ Real.sqrt x * (1 / (Real.log 2) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [show Real.sqrt x * (1 / (Real.log 2) ^ 2) = Real.sqrt x / (Real.log 2) ^ 2 by ring]
  have hint_hi : ∫ t in (Real.sqrt x)..x, 1 / (Real.log t) ^ 2 ≤ 4 * x / (Real.log x) ^ 2 := by
    have h1 : ∫ t in (Real.sqrt x)..x, 1 / (Real.log t) ^ 2 ≤
        ∫ _t in (Real.sqrt x)..x, 4 / (Real.log x) ^ 2 := by
      refine intervalIntegral.integral_mono_on hsq_le (hint_inv2 (Real.sqrt x) x hsq_ge2 hsq_le)
        intervalIntegrable_const fun t ht => ?_
      have hlt_ge : Real.log x / 2 ≤ Real.log t := by
        have h := Real.log_le_log (by linarith) ht.1
        rwa [Real.log_sqrt hx0.le] at h
      calc 1 / (Real.log t) ^ 2 ≤ 1 / (Real.log x / 2) ^ 2 :=
            one_div_le_one_div_of_le (by positivity) (by nlinarith)
        _ = 4 / (Real.log x) ^ 2 := by field_simp [hLx_pos.ne']; ring
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have : (x - Real.sqrt x) * (4 / (Real.log x) ^ 2) ≤ x * (4 / (Real.log x) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg x]) (by positivity)
    linarith [show x * (4 / (Real.log x) ^ 2) = 4 * x / (Real.log x) ^ 2 by ring]
  have hint_nn : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 :=
    intervalIntegral.integral_nonneg hx2 fun t _ => by positivity
  -- `|li(x) - x / log x| ≤ 2 / log 2 + √x / (log 2)^2 + 4 x / (log x)^2`
  have hli_sub : |(∫ t in (2 : ℝ)..x, 1 / Real.log t) - x / Real.log x| ≤
      2 / Real.log 2 + Real.sqrt x / (Real.log 2) ^ 2 + 4 * x / (Real.log x) ^ 2 := by
    rw [Stage10SiegelWalfiszFull.integral_inv_log_eq hx2]
    have heq : x / Real.log x - 2 / Real.log 2 + (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) - x / Real.log x =
        (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) - 2 / Real.log 2 := by ring
    rw [heq, abs_le]
    have h2log2_nn : 0 ≤ 2 / Real.log 2 := div_nonneg (by norm_num) hlog2_pos.le
    constructor <;> linarith [hint_split, hint_lo, hint_hi, hint_nn, h2log2_nn,
      div_nonneg (Real.sqrt_nonneg x) (sq_nonneg (Real.log 2)),
      div_nonneg (show (0 : ℝ) ≤ 4 * x by linarith) (sq_nonneg (Real.log x))]
  -- Bound each term by `c_i * x / (log x)^2`
  have ht1 : C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)) ≤ (C_sw * K_sw) * x / (Real.log x) ^ 2 := by
    have h1 := hsw_exp x hx4
    rw [Real.rpow_two] at h1
    rw [le_div_iff₀ (sq_pos_of_pos hLx_pos)]
    have heq : C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)) * (Real.log x) ^ 2 =
        C_sw * x * ((Real.log x) ^ 2 * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by ring
    rw [heq]
    nlinarith [mul_nonneg hCsw.le hx0.le]
  have ht2 : 2 / Real.log 2 ≤ (2 / Real.log 2) * x / (Real.log x) ^ 2 := by
    have hlog2_le_x : (Real.log x) ^ 2 ≤ x := by
      -- Since `log x ≤ √x`? Check: `Real.log (√x) ≤ √x - 1`, wait: `log x = 2 * log (√x) ≤ 2 * √x`?
      -- Better: `Real.log t ≤ t / Real.exp 1`? Or `log (x^{1/2}) ≤ x^{1/2} - 1` → `log x ≤ 2 * √x` → wait `4 x`!
      -- Even simpler: `log (x^{1/4}) ≤ x^{1/4} - 1` → `log x ≤ 4 * x^{1/4}` → no, just use `Real.log_le_sub_one_of_pos` on `√x / 2`:
      -- Wait: for `x ≥ 16`, `Real.log x = 2 * Real.log (√x) ≤ 2 * (√x / 2) = √x`? Let's check `√x = 4`: `log 16 = 2.77 ≤ 4`!
      -- Proof: `log(√x / 2) ≤ √x / 2 - 1`, so `log(√x) ≤ √x / 2 + log 2 - 1 ≤ √x / 2` (since `log 2 < 1`), so `log x = 2 log(√x) ≤ √x`!
      have hsq_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have hlog2_lt1 : Real.log 2 < 1 := by
        have : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
        exact (Real.log_lt_log (by norm_num) this).trans_eq (Real.log_exp 1)
      have hhalf : Real.log (Real.sqrt x / 2) ≤ Real.sqrt x / 2 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hsq_pos.ne' (by norm_num)] at hhalf
      have hlog_sq_le : Real.log (Real.sqrt x) ≤ Real.sqrt x / 2 := by linarith
      have hLx_le_sq : Real.log x ≤ Real.sqrt x := by
        rw [Real.log_sqrt hx0.le] at hlog_sq_le
        linarith
      calc (Real.log x) ^ 2 ≤ (Real.sqrt x) ^ 2 := by nlinarith
        _ = x := Real.sq_sqrt hx0.le
    rw [le_div_iff₀ (sq_pos_of_pos hLx_pos)]
    have : 0 < 2 / Real.log 2 := by positivity
    nlinarith
  have ht3 : Real.sqrt x / (Real.log 2) ^ 2 ≤ (K_sq / (Real.log 2) ^ 2) * x / (Real.log x) ^ 2 := by
    have h1 := hlog_sq x hx4
    rw [Real.rpow_two] at h1
    rw [le_div_iff₀ (sq_pos_of_pos hLx_pos)]
    have h2 : Real.sqrt x * (Real.log x) ^ 2 ≤ K_sq * x := by
      calc Real.sqrt x * (Real.log x) ^ 2 ≤ Real.sqrt x * (K_sq * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
        _ = K_sq * (Real.sqrt x * Real.sqrt x) := by ring
        _ = K_sq * x := by rw [Real.mul_self_sqrt hx0.le]
    have heq1 : Real.sqrt x / (Real.log 2) ^ 2 * (Real.log x) ^ 2 =
        (Real.sqrt x * (Real.log x) ^ 2) / (Real.log 2) ^ 2 := by ring
    have heq2 : K_sq / (Real.log 2) ^ 2 * x = (K_sq * x) / (Real.log 2) ^ 2 := by ring
    rw [heq1, heq2]
    exact div_le_div_of_nonneg_right h2 (sq_nonneg _)
  have hpi_sub : |(primeCount x : ℝ) - x / Real.log x| ≤ M_err * x / (Real.log x) ^ 2 := by
    have htri : |(primeCount x : ℝ) - x / Real.log x| ≤
        |(primeCount x : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| +
        |(∫ t in (2 : ℝ)..x, 1 / Real.log t) - x / Real.log x| := by
      have heq : (primeCount x : ℝ) - x / Real.log x =
          ((primeCount x : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t) +
          ((∫ t in (2 : ℝ)..x, 1 / Real.log t) - x / Real.log x) := by ring
      rw [heq]; exact abs_add_le _ _
    dsimp only [M_err]
    have heq : (C_sw * K_sw + 2 / Real.log 2 + K_sq / (Real.log 2) ^ 2 + 4) * x / (Real.log x) ^ 2 =
        (C_sw * K_sw) * x / (Real.log x) ^ 2 + (2 / Real.log 2) * x / (Real.log x) ^ 2 +
        (K_sq / (Real.log 2) ^ 2) * x / (Real.log x) ^ 2 + 4 * x / (Real.log x) ^ 2 := by ring
    linarith
  -- Divide by `x / log x`
  have hdiv_pos : 0 < x / Real.log x := div_pos hx0 hLx_pos
  have hquot : |(primeCount x : ℝ) / (x / Real.log x) - 1| =
      |(primeCount x : ℝ) - x / Real.log x| / (x / Real.log x) := by
    rw [show (primeCount x : ℝ) / (x / Real.log x) - 1 =
        ((primeCount x : ℝ) - x / Real.log x) / (x / Real.log x) by field_simp [hdiv_pos.ne'],
      abs_div, abs_of_pos hdiv_pos]
  rw [hquot]
  calc |(primeCount x : ℝ) - x / Real.log x| / (x / Real.log x)
      ≤ (M_err * x / (Real.log x) ^ 2) / (x / Real.log x) :=
        div_le_div_of_nonneg_right hpi_sub hdiv_pos.le
    _ = M_err / Real.log x := by field_simp [hx0.ne', hLx_pos.ne']
    _ ≤ ε := by
        rw [div_le_iff₀ hLx_pos]
        have := (div_le_iff₀ hε).mp hLx_ge
        linarith

/-- Number of distinct prime factors `ω(N) = N.primeFactors.card ≤ log N / log 2` for `N ≥ 1`. -/
private lemma primeFactors_card_le_log {N : ℕ} (hN : 1 ≤ N) :
    (N.primeFactors.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow_le : 2 ^ N.primeFactors.card ≤ N := by
    calc 2 ^ N.primeFactors.card
        = ∏ _p ∈ N.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ N.primeFactors, p :=
          Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ N := Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)
  have hpowR : (2 : ℝ) ^ N.primeFactors.card ≤ (N : ℝ) := by exact_mod_cast hpow_le
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ hlog2_pos).mpr hlog

/-- For even `N ≥ 2`, `primeCount N` and `(chenGoldbachSet N).card` differ by at most `N.primeFactors.card`. -/
theorem primeCount_sub_chenGoldbachSet_card {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) :
    (chenGoldbachSet N).card ≤ primeCount (N : ℝ) ∧
    primeCount (N : ℝ) - (chenGoldbachSet N).card ≤ N.primeFactors.card := by
  have hcard_eq : (chenGoldbachSet N).card =
      ((Finset.range N).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)).card := by
    unfold chenGoldbachSet
    refine Finset.card_image_of_injOn fun p hp q hq heq => ?_
    have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have hqN : q < N := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
    omega
  rw [hcard_eq]
  unfold primeCount
  rw [Nat.floor_natCast]
  set S₁ := (Finset.range N).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)
  set S₂ := (Finset.range (N + 1)).filter Nat.Prime
  have hsub : S₁ ⊆ S₂ := by
    intro p hp
    simp only [S₁, S₂, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2.1⟩
  refine ⟨Finset.card_le_card hsub, ?_⟩
  rw [← Finset.card_sdiff_of_subset hsub]
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_sdiff, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hp
  rw [Nat.mem_primeFactors]
  refine ⟨hp.1.2, ?_, by omega⟩
  by_contra hndvd
  apply hp.2
  have h2dvd : 2 ∣ N := even_iff_two_dvd.mp hEven
  have hp_ne2 : p ≠ 2 := fun h => hndvd (h ▸ h2dvd)
  have hp_gt2 : 2 < p := lt_of_le_of_ne hp.1.2.two_le (Ne.symm hp_ne2)
  have hp_neN : p ≠ N := fun h => hndvd (h ▸ dvd_rfl)
  exact ⟨by omega, hp.1.2, hp_gt2, hndvd⟩

/-- Prime Number Theorem asymptotic for `chenGoldbachSet N` on even integers `N`:
`|((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) - 1| ≤ ε` for all sufficiently large even `N`. -/
theorem chenGoldbachSet_card_asymp :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      |((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) - 1| ≤ ε := by
  intro ε hε
  obtain ⟨X₁, hX₁4, hpi⟩ := primeCount_asymp (ε / 2) (by linarith)
  obtain ⟨K_sq, hKsq, hlog_sq⟩ := log_rpow_le_const_mul_sqrt 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C_rem : ℝ := 2 * K_sq / (Real.log 2 * ε)
  set N₀ : ℕ := max 4 (max ⌈X₁⌉₊ (⌈C_rem ^ 2⌉₊ + 1))
  refine ⟨N₀, le_max_left _ _, fun N hN hEven => ?_⟩
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN_X1 : X₁ ≤ (N : ℝ) := (Nat.le_ceil X₁).trans (by
    exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hN)
  have hN_C : C_rem ^ 2 < (N : ℝ) := by
    have h1 : ⌈C_rem ^ 2⌉₊ + 1 ≤ N :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hN
    have h2 : C_rem ^ 2 ≤ (⌈C_rem ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈C_rem ^ 2⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h1
    linarith
  have hNR4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hLN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hdiv_pos : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos hN0 hLN_pos
  have h1 := hpi (N : ℝ) hN_X1
  obtain ⟨hle, hdiff⟩ := primeCount_sub_chenGoldbachSet_card (by omega) hEven
  have hdiffR : (primeCount (N : ℝ) : ℝ) - ((chenGoldbachSet N).card : ℝ) ≤
      Real.log (N : ℝ) / Real.log 2 := by
    have hsub : ((primeCount (N : ℝ) - (chenGoldbachSet N).card : ℕ) : ℝ) ≤
        (N.primeFactors.card : ℝ) := Nat.cast_le.mpr hdiff
    rw [Nat.cast_sub hle] at hsub
    exact hsub.trans (primeFactors_card_le_log (by omega))
  have hdiff_nn : 0 ≤ (primeCount (N : ℝ) : ℝ) - ((chenGoldbachSet N).card : ℝ) :=
    sub_nonneg.mpr (Nat.cast_le.mpr hle)
  have hdiff_div : |((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
      (primeCount (N : ℝ) : ℝ) / ((N : ℝ) / Real.log (N : ℝ))| ≤ ε / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hdiv_pos, abs_sub_comm, abs_of_nonneg hdiff_nn]
    have hlog2_le : (Real.log (N : ℝ)) ^ 2 ≤ K_sq * Real.sqrt (N : ℝ) := by
      simpa [Real.rpow_two] using hlog_sq (N : ℝ) hNR4
    have hsq_gt : C_rem < Real.sqrt (N : ℝ) := by
      have hC_nn : 0 ≤ C_rem := by dsimp only [C_rem]; positivity
      exact (Real.sqrt_sq hC_nn).symm.trans_lt (Real.sqrt_lt_sqrt (sq_nonneg _) hN_C)
    calc ((primeCount (N : ℝ) : ℝ) - ((chenGoldbachSet N).card : ℝ)) / ((N : ℝ) / Real.log (N : ℝ))
        ≤ (Real.log (N : ℝ) / Real.log 2) / ((N : ℝ) / Real.log (N : ℝ)) :=
          div_le_div_of_nonneg_right hdiffR hdiv_pos.le
      _ = (Real.log (N : ℝ)) ^ 2 / (Real.log 2 * (N : ℝ)) := by field_simp [hN0.ne', hLN_pos.ne', hlog2_pos.ne']
      _ ≤ (K_sq * Real.sqrt (N : ℝ)) / (Real.log 2 * (N : ℝ)) :=
          div_le_div_of_nonneg_right hlog2_le (by positivity)
      _ = K_sq / (Real.log 2 * Real.sqrt (N : ℝ)) := by
          have hsq2 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN0.le
          have hsq_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
          have hstep : (K_sq * Real.sqrt (N : ℝ)) / (Real.log 2 * (N : ℝ)) =
              (K_sq * Real.sqrt (N : ℝ)) / (Real.log 2 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ))) := by
            rw [hsq2]
          rw [hstep]
          field_simp [hsq_pos.ne', hlog2_pos.ne']
      _ ≤ ε / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have hC_mul : (2 * K_sq) / (Real.log 2 * ε) * (Real.log 2 * ε) = 2 * K_sq := by
            field_simp [hlog2_pos.ne', hε.ne']
          have h1' : 2 * K_sq < Real.log 2 * ε * Real.sqrt (N : ℝ) := by
            have := mul_lt_mul_of_pos_right hsq_gt (mul_pos hlog2_pos hε)
            dsimp only [C_rem] at this
            rw [hC_mul] at this
            linarith
          linarith
  have htri : |((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) - 1| ≤
      |((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
        (primeCount (N : ℝ) : ℝ) / ((N : ℝ) / Real.log (N : ℝ))| +
      |(primeCount (N : ℝ) : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) - 1| := by
    have heq : ((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) - 1 =
        (((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) -
          (primeCount (N : ℝ) : ℝ) / ((N : ℝ) / Real.log (N : ℝ))) +
        ((primeCount (N : ℝ) : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) - 1) := by ring
    rw [heq]; exact abs_add_le _ _
  linarith

/-- Convenient PNT two-sided bounds on `(chenGoldbachSet N).card`:
for all sufficiently large even `N`, `(1/2) * N / log N ≤ |A(N)| ≤ 2 * N / log N`. -/
theorem chenGoldbachSet_card_bounds :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (1 / 2 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤ ((chenGoldbachSet N).card : ℝ) ∧
      ((chenGoldbachSet N).card : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨N₀, hN0, hasymp⟩ := chenGoldbachSet_card_asymp (1 / 2) (by norm_num)
  refine ⟨N₀, hN0, fun N hN hEven => ?_⟩
  have hN4 : 4 ≤ N := hN0.trans hN
  have hN0R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hLN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdiv_pos : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos hN0R hLN_pos
  have h := abs_le.mp (hasymp N hN hEven)
  constructor
  · have h1 : (1 / 2 : ℝ) ≤ ((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) := by linarith
    exact (le_div_iff₀ hdiv_pos).mp h1
  · have h2 : ((chenGoldbachSet N).card : ℝ) / ((N : ℝ) / Real.log (N : ℝ)) ≤ 2 := by linarith
    exact (div_le_iff₀ hdiv_pos).mp h2

/-! ## Section 2: Goldbach Shifted-Prime Remainder Bounds (`chen_A_remainder_bound` & `chen_Aq_remainder_bound`) -/

/-- Exact Euler totient formula for squarefree `d`: `d.totient = ∏ p ∈ d.primeFactors, (p - 1)`. -/
private lemma totient_eq_prod_primeFactors_of_squarefree {d : ℕ} (hd : Squarefree d) :
    d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd0 : d = 0
    · exact absurd (hd0 ▸ hd) not_squarefree_zero
    by_cases hd1 : d = 1
    · subst hd1; simp
    have hd2 : 2 ≤ d := by omega
    set p : ℕ := d.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpd : p ∣ d := Nat.minFac_dvd d
    set m : ℕ := d / p
    have hdm : d = p * m := (Nat.mul_div_cancel' hpd).symm
    have hndvd : ¬ p ∣ m := by
      intro hpm
      obtain ⟨k, hk⟩ := hpm
      have hpp : p * p ∣ d := ⟨k, by rw [hdm, hk]; ring⟩
      exact hp.not_isUnit (hd p hpp)
    have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hndvd
    have hm_sq : Squarefree m := hd.squarefree_of_dvd ⟨p, by rw [hdm]; ring⟩
    have hm_ne0 : m ≠ 0 := fun h => hd0 (by rw [hdm, h, mul_zero])
    have hm_lt : m < d := by
      have hp2 : 2 ≤ p := hp.two_le
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm_ne0
      rw [hdm]; nlinarith
    have hpf : d.primeFactors = insert p m.primeFactors := by
      rw [hdm, Nat.primeFactors_mul hp.ne_zero hm_ne0, hp.primeFactors]
      ext q; simp
    have hp_not_mem : p ∉ m.primeFactors := by
      rw [Nat.mem_primeFactors]; intro h; exact hndvd h.2.1
    rw [hpf, Finset.prod_insert hp_not_mem, ← ih m hm_lt hm_sq, hdm, Nat.totient_mul hcop,
      Nat.totient_prime hp]

/-- For even `N` and squarefree `d`:
- if `Nat.Coprime d N`, then `multDensity (chenPrimeDensity N) d = 1 / (d.totient : ℝ)`;
- if `¬ Nat.Coprime d N`, then `multDensity (chenPrimeDensity N) d = 0` AND
  `((chenGoldbachSet N).filter (d ∣ ·)).card = 0`. -/
theorem multDensity_chenPrimeDensity_eq {N d : ℕ} (hEven : Even N) (hd : Squarefree d) :
    (Nat.Coprime d N → multDensity (chenPrimeDensity N) d = 1 / (d.totient : ℝ)) ∧
    (¬ Nat.Coprime d N → multDensity (chenPrimeDensity N) d = 0 ∧
      ((chenGoldbachSet N).filter (d ∣ ·)).card = 0) := by
  have h2dvd : 2 ∣ N := even_iff_two_dvd.mp hEven
  constructor
  · intro hcop
    unfold multDensity
    rw [if_pos hd]
    have hprod : ∏ p ∈ d.primeFactors, chenPrimeDensity N p =
        ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 1)) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd_d : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hp_ndvd_N : ¬ p ∣ N := fun hpN => hp_prime.not_isUnit (isUnit_iff_eq_one.mpr
        (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hp_dvd_d hpN)))
      have hp_ne2 : p ≠ 2 := fun h => hp_ndvd_N (h ▸ h2dvd)
      unfold chenPrimeDensity
      rw [if_pos ⟨hp_prime, hp_ne2, hp_ndvd_N⟩]
    rw [hprod, Finset.prod_div_distrib, Finset.prod_const_one]
    congr 1
    rw [totient_eq_prod_primeFactors_of_squarefree hd, Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub hp1, Nat.cast_one]
  · intro hncop
    have hgcd : 1 < Nat.gcd d N := by
      have hne1 : Nat.gcd d N ≠ 1 := hncop
      have hne0 : Nat.gcd d N ≠ 0 := by
        intro h0
        have hd0 : d = 0 := (Nat.gcd_eq_zero_iff.mp h0).1
        exact not_squarefree_zero (hd0 ▸ hd)
      omega
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd d N ≠ 1)
    have hp_d : p ∣ d := hp_dvd.trans (Nat.gcd_dvd_left d N)
    have hp_N : p ∣ N := hp_dvd.trans (Nat.gcd_dvd_right d N)
    have hd_ne0 : d ≠ 0 := fun h => not_squarefree_zero (h ▸ hd)
    have hp_mem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_d, hd_ne0⟩
    constructor
    · unfold multDensity
      rw [if_pos hd]
      refine Finset.prod_eq_zero hp_mem ?_
      unfold chenPrimeDensity
      rw [if_neg (by tauto)]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha hda
      unfold chenGoldbachSet at ha
      rw [Finset.mem_image] at ha
      obtain ⟨r, hr, rfl⟩ := ha
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      have hpa : p ∣ N - r := hp_d.trans hda
      have hpr : p ∣ r := by
        have hadd : (N - r) + r = N := Nat.sub_add_cancel (by omega)
        exact (Nat.dvd_add_right hpa).mp (hadd.symm ▸ hp_N)
      have hreq : p = r := (Nat.prime_dvd_prime_iff_eq hp_prime hr.2.1).mp hpr
      exact hr.2.2.2 (hreq ▸ hp_N)

/-- Exact comparison between `((chenGoldbachSet N).filter (d ∣ ·)).card` and `primeCountAP d N N`
for even `N ≥ 2` and `d ≥ 1`: they differ by at most `N.primeFactors.card`. -/
private lemma chenGoldbachSet_filter_dvd_sub_primeCountAP {N d : ℕ} (hN : 2 ≤ N) (hEven : Even N) :
    ((chenGoldbachSet N).filter (d ∣ ·)).card ≤ Stage2DirichletAP.primeCountAP d N (N : ℝ) ∧
    Stage2DirichletAP.primeCountAP d N (N : ℝ) - ((chenGoldbachSet N).filter (d ∣ ·)).card ≤
      N.primeFactors.card := by
  have hcard_eq : ((chenGoldbachSet N).filter (d ∣ ·)).card =
      ((Finset.range N).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N ∧ p ≡ N [MOD d])).card := by
    unfold chenGoldbachSet
    rw [Finset.filter_image]
    have hinj : Set.InjOn (fun p => N - p)
        (((Finset.range N).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)).filter (fun p => d ∣ N - p) : Set ℕ) := by
      intro p hp q hq heq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_range] at hp hq
      dsimp only at heq
      omega
    rw [Finset.card_image_of_injOn hinj]
    congr 1; ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hpN, hpp, hp2, hpndvd⟩, hdv⟩
      exact ⟨hpN, hpp, hp2, hpndvd, (Nat.modEq_iff_dvd' (by omega)).mpr hdv⟩
    · rintro ⟨hpN, hpp, hp2, hpndvd, hmod⟩
      exact ⟨⟨hpN, hpp, hp2, hpndvd⟩, (Nat.modEq_iff_dvd' (by omega)).mp hmod⟩
  rw [hcard_eq]
  unfold Stage2DirichletAP.primeCountAP
  rw [Nat.floor_natCast]
  set S₁ := (Finset.range N).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N ∧ p ≡ N [MOD d])
  set S₂ := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ p ≡ N [MOD d])
  have hsub : S₁ ⊆ S₂ := by
    intro p hp
    simp only [S₁, S₂, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2.1, hp.2.2.2.2⟩
  refine ⟨Finset.card_le_card hsub, ?_⟩
  rw [← Finset.card_sdiff_of_subset hsub]
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_sdiff, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hp
  rw [Nat.mem_primeFactors]
  refine ⟨hp.1.2.1, ?_, by omega⟩
  by_contra hndvd
  apply hp.2
  have h2dvd : 2 ∣ N := even_iff_two_dvd.mp hEven
  have hp_ne2 : p ≠ 2 := fun h => hndvd (h ▸ h2dvd)
  have hp_gt2 : 2 < p := lt_of_le_of_ne hp.1.2.1.two_le (Ne.symm hp_ne2)
  have hp_neN : p ≠ N := fun h => hndvd (h ▸ dvd_rfl)
  exact ⟨by omega, hp.1.2.1, hp_gt2, hndvd, hp.1.2.2⟩

/-- Master squarefree remainder bound for `A = chenGoldbachSet N`, valid for EVERY `B ≥ B₀`:
for every `A_exp : ℝ`, there exist `B₀ C > 0` such that for all `B ≥ B₀` and all even `N ≥ 4`:
`∑_{1 ≤ d ≤ √N / (log N)^B, Squarefree d} |#(A_d) - |A| * g(d)| ≤ C * N / (log N)^{A_exp}`. -/
theorem chen_A_remainder_bound_ge (A_exp : ℝ) :
    ∃ B₀ C : ℝ, 0 < B₀ ∧ 0 < C ∧
      ∀ B : ℝ, B₀ ≤ B →
        ∀ N : ℕ, 4 ≤ N → Even N →
          ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B⌋₊).filter Squarefree,
            |(((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
              ((chenGoldbachSet N).card : ℝ) * multDensity (chenPrimeDensity N) d| ≤
            C * (N : ℝ) / (Real.log (N : ℝ)) ^ A_exp := by
  set A' : ℝ := max A_exp 1
  obtain ⟨B_bv, C_bv, hBbv, hCbv, hbv⟩ := bombieri_vinogradov_primes A'
  obtain ⟨K_sq, hKsq, hlog_sq⟩ := log_rpow_le_const_mul_sqrt (A' + 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B₀ : ℝ := max B_bv (A' + 1)
  have hB0_pos : 0 < B₀ := lt_of_lt_of_le hBbv (le_max_left _ _)
  set C_fin : ℝ := C_bv + K_sq / Real.log 2 + 12 * K_sq / Real.log 2
  have hC_pos : 0 < C_fin := by positivity
  refine ⟨B₀, C_fin, hB0_pos, hC_pos, fun B hB N hN4 hEven => ?_⟩
  have hNR4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hLN_gt1 : 1 < Real.log (N : ℝ) := by
    have : Real.exp 1 < (N : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLN_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hLN_gt1
  set Q : ℕ := ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B⌋₊
  have hQ_le_Qb : Q ≤ ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B_bv⌋₊ := by
    refine Nat.floor_mono ?_
    refine div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hLN_pos B_bv) ?_
    exact Real.rpow_le_rpow_of_exponent_le hLN_gt1.le ((le_max_left _ _).trans hB)
  by_cases hQ0 : Q = 0
  · have hIcc : Finset.Icc 1 Q = ∅ := by simp [hQ0]
    rw [hIcc, Finset.filter_empty, Finset.sum_empty]
    positivity
  have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ0
  have hQ_le_real : (Q : ℝ) ≤ Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B := Nat.floor_le (by positivity)
  have hQ_le_sqrt : (Q : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hB_pos : 0 < B := hB0_pos.trans_le hB
    exact hQ_le_real.trans (div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLN_gt1.le hB_pos.le))
  -- Pointwise bound for every `d ∈ (Icc 1 Q).filter Squarefree`
  have hpt : ∀ d ∈ (Finset.Icc 1 Q).filter Squarefree,
      |(((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
        ((chenGoldbachSet N).card : ℝ) * multDensity (chenPrimeDensity N) d| ≤
      (if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
        ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
          (fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
            (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
      else 0) +
      (N.primeFactors.card : ℝ) + (N.primeFactors.card : ℝ) * (d.totient : ℝ)⁻¹ := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, _⟩, hd_sq⟩ := hd
    by_cases hcop : Nat.Coprime d N
    · have hmd := (multDensity_chenPrimeDensity_eq hEven hd_sq).1 hcop
      rw [hmd, mul_one_div]
      obtain ⟨hA_le, hA_diff⟩ := chenGoldbachSet_filter_dvd_sub_primeCountAP (by omega) hEven (d := d)
      obtain ⟨hX_le, hX_diff⟩ := primeCount_sub_chenGoldbachSet_card (by omega) hEven
      have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
      have hd_pos : 0 < d := by omega
      -- `primeCountAP d N N = primeCountAP d (N % d) N` and `N % d` is coprime to `d`
      have hmod_eq : Stage2DirichletAP.primeCountAP d N (N : ℝ) =
          Stage2DirichletAP.primeCountAP d (N % d) (N : ℝ) := by
        unfold Stage2DirichletAP.primeCountAP
        congr 1; ext p; simp [Nat.ModEq]
      have hmem_res : N % d ∈ (Finset.range d).filter (fun a => Nat.Coprime a d) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt N hd_pos), ?_⟩
        rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
        exact hcop.symm.gcd_eq_one
      have hbv_term : |(Stage2DirichletAP.primeCountAP d N (N : ℝ) : ℝ) -
            (primeCount (N : ℝ) : ℝ) / (d.totient : ℝ)| ≤
          (if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
            ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
              (fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
                (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
          else 0) := by
        rw [dif_pos ⟨N % d, hmem_res⟩, hmod_eq]
        exact Finset.le_sup' (f := fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
          (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|) hmem_res
      have hdiff1 : |(((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
            (Stage2DirichletAP.primeCountAP d N (N : ℝ) : ℝ)| ≤ (N.primeFactors.card : ℝ) := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hA_le)), ← Nat.cast_sub hA_le]
        exact_mod_cast hA_diff
      have hdiff2 : |(primeCount (N : ℝ) : ℝ) / (d.totient : ℝ) -
            ((chenGoldbachSet N).card : ℝ) / (d.totient : ℝ)| ≤
          (N.primeFactors.card : ℝ) * (d.totient : ℝ)⁻¹ := by
        rw [← sub_div, abs_div, abs_of_pos hphi_pos,
          abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hX_le)), ← Nat.cast_sub hX_le, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hX_diff) (inv_nonneg.mpr hphi_pos.le)
      have heq : (((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
            ((chenGoldbachSet N).card : ℝ) / (d.totient : ℝ) =
          ((((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
            (Stage2DirichletAP.primeCountAP d N (N : ℝ) : ℝ)) +
          ((Stage2DirichletAP.primeCountAP d N (N : ℝ) : ℝ) -
            (primeCount (N : ℝ) : ℝ) / (d.totient : ℝ)) +
          ((primeCount (N : ℝ) : ℝ) / (d.totient : ℝ) -
            ((chenGoldbachSet N).card : ℝ) / (d.totient : ℝ)) := by ring
      rw [heq]
      have htri1 := abs_add_le
        ((((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
          (Stage2DirichletAP.primeCountAP d N (N : ℝ) : ℝ) +
        ((Stage2DirichletAP.primeCountAP d N (N : ℝ) : ℝ) -
          (primeCount (N : ℝ) : ℝ) / (d.totient : ℝ)))
        ((primeCount (N : ℝ) : ℝ) / (d.totient : ℝ) -
          ((chenGoldbachSet N).card : ℝ) / (d.totient : ℝ))
      have htri2 := abs_add_le
        ((((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
          (Stage2DirichletAP.primeCountAP d N (N : ℝ) : ℝ))
        ((Stage2DirichletAP.primeCountAP d N (N : ℝ) : ℝ) -
          (primeCount (N : ℝ) : ℝ) / (d.totient : ℝ))
      linarith
    · obtain ⟨hmd0, hcard0⟩ := (multDensity_chenPrimeDensity_eq hEven hd_sq).2 hcop
      rw [hmd0, hcard0]
      simp only [Nat.cast_zero, mul_zero, sub_zero, abs_zero]
      have hsup_nn : 0 ≤ (if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
          ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
            (fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
              (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
        else 0) := by
        split_ifs with hne
        · obtain ⟨a, ha⟩ := hne
          exact (abs_nonneg _).trans (Finset.le_sup'
            (f := fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
              (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|) ha)
        · exact le_rfl
      positivity
  -- Sum over `d ∈ (Icc 1 Q).filter Squarefree ⊆ Icc 1 Q`
  have hsum_le :
      ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
        |(((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
          ((chenGoldbachSet N).card : ℝ) * multDensity (chenPrimeDensity N) d| ≤
      (∑ d ∈ Finset.Icc 1 Q,
        (if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
          ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
            (fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
              (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
        else 0)) +
      (Q : ℝ) * (N.primeFactors.card : ℝ) +
      (N.primeFactors.card : ℝ) * ∑ d ∈ Finset.Icc 1 Q, (d.totient : ℝ)⁻¹ := by
    have h1 := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
    have hsub := Finset.filter_subset Squarefree (Finset.Icc 1 Q)
    have hs1 : ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
        (if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
          ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
            (fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
              (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
        else 0) ≤
        ∑ d ∈ Finset.Icc 1 Q,
          (if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
            ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
              (fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
                (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
          else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => ?_
      split_ifs with hne
      · obtain ⟨a, ha⟩ := hne
        exact (abs_nonneg _).trans (Finset.le_sup'
          (f := fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
            (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|) ha)
      · exact le_rfl
    have hs2 : ∑ _d ∈ (Finset.Icc 1 Q).filter Squarefree, (N.primeFactors.card : ℝ) ≤
        (Q : ℝ) * (N.primeFactors.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have : ((Finset.Icc 1 Q).filter Squarefree).card ≤ (Finset.Icc 1 Q).card :=
        Finset.card_filter_le _ _
      rw [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hs3 : ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree, (N.primeFactors.card : ℝ) * (d.totient : ℝ)⁻¹ ≤
        (N.primeFactors.card : ℝ) * ∑ d ∈ Finset.Icc 1 Q, (d.totient : ℝ)⁻¹ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) (Nat.cast_nonneg _)
    linarith
  -- Bound the 3 parts by `C_bv`, `K_sq / log 2`, `12 * K_sq / log 2` times `N / (log N)^{A'}`
  have hpart1 : ∑ d ∈ Finset.Icc 1 Q,
      (if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
        ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
          (fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
            (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
      else 0) ≤ C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
    have hsub := Finset.Icc_subset_Icc_right (a := 1) hQ_le_Qb
    calc _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B_bv⌋₊,
            (if h : ((Finset.range d).filter (fun a => Nat.Coprime a d)).Nonempty then
              ((Finset.range d).filter (fun a => Nat.Coprime a d)).sup' h
                (fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
                  (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|)
            else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => ?_
          split_ifs with hne
          · obtain ⟨a, ha⟩ := hne
            exact (abs_nonneg _).trans (Finset.le_sup'
              (f := fun a => |(Stage2DirichletAP.primeCountAP d a (N : ℝ) : ℝ) -
                (((Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)|) ha)
          · exact le_rfl
      _ ≤ C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := hbv (N : ℝ) hNR4
  have hlogA2 : (Real.log (N : ℝ)) ^ (A' + 2) ≤ K_sq * Real.sqrt (N : ℝ) := hlog_sq (N : ℝ) hNR4
  have hsq_log : Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ K_sq * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLN_pos A')]
    have h1 : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A' = (Real.log (N : ℝ)) ^ (A' + 1) := by
      rw [Real.rpow_add hLN_pos, Real.rpow_one, mul_comm]
    have h2 : (Real.log (N : ℝ)) ^ (A' + 1) ≤ (Real.log (N : ℝ)) ^ (A' + 2) :=
      Real.rpow_le_rpow_of_exponent_le hLN_gt1.le (by linarith)
    calc Real.sqrt (N : ℝ) * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A'
        = Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ (A' + 1) := by rw [← h1]; ring
      _ ≤ Real.sqrt (N : ℝ) * (K_sq * Real.sqrt (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (h2.trans hlogA2) (Real.sqrt_nonneg _)
      _ = K_sq * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
      _ = K_sq * (N : ℝ) := by rw [Real.mul_self_sqrt hN0.le]
  have hpart2 : (Q : ℝ) * (N.primeFactors.card : ℝ) ≤
      (K_sq / Real.log 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
    calc (Q : ℝ) * (N.primeFactors.card : ℝ)
        ≤ Real.sqrt (N : ℝ) * (Real.log (N : ℝ) / Real.log 2) :=
          mul_le_mul hQ_le_sqrt (primeFactors_card_le_log (by omega)) (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      _ = (Real.sqrt (N : ℝ) * Real.log (N : ℝ)) / Real.log 2 := by ring
      _ ≤ (K_sq * (N : ℝ) / (Real.log (N : ℝ)) ^ A') / Real.log 2 :=
          div_le_div_of_nonneg_right hsq_log hlog2_pos.le
      _ = (K_sq / Real.log 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by ring
  have hpart3 : (N.primeFactors.card : ℝ) * ∑ d ∈ Finset.Icc 1 Q, (d.totient : ℝ)⁻¹ ≤
      (12 * K_sq / Real.log 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
    have h2Q_le_N2 : 2 * (Q : ℝ) ≤ (N : ℝ) ^ 2 := by
      have hsq_le : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
        have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
        exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hN0.le)
      nlinarith
    have hlog2Q : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
      have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ1
      calc Real.log (2 * (Q : ℝ)) ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) h2Q_le_N2
        _ = 2 * Real.log (N : ℝ) := by rw [Real.log_pow]; norm_num
    have hsum_phi := (sum_inv_totient_Icc_le hQ1).trans (mul_le_mul_of_nonneg_left hlog2Q (by norm_num))
    have hlog2_le : (Real.log (N : ℝ)) ^ 2 ≤ K_sq * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hLN_pos A')]
      have h1 : (Real.log (N : ℝ)) ^ 2 * (Real.log (N : ℝ)) ^ A' = (Real.log (N : ℝ)) ^ (A' + 2) := by
        rw [Real.rpow_add hLN_pos, Real.rpow_two, mul_comm]
      rw [h1]
      have hsq_le : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
        have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
        exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hN0.le)
      exact hlogA2.trans (mul_le_mul_of_nonneg_left hsq_le hKsq.le)
    calc (N.primeFactors.card : ℝ) * ∑ d ∈ Finset.Icc 1 Q, (d.totient : ℝ)⁻¹
        ≤ (Real.log (N : ℝ) / Real.log 2) * (6 * (2 * Real.log (N : ℝ))) :=
          mul_le_mul (primeFactors_card_le_log (by omega)) hsum_phi
            (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = (12 / Real.log 2) * (Real.log (N : ℝ)) ^ 2 := by ring
      _ ≤ (12 / Real.log 2) * (K_sq * (N : ℝ) / (Real.log (N : ℝ)) ^ A') :=
          mul_le_mul_of_nonneg_left hlog2_le (by positivity)
      _ = (12 * K_sq / Real.log 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by ring
  have hA_pow_le : (Real.log (N : ℝ)) ^ A_exp ≤ (Real.log (N : ℝ)) ^ A' :=
    Real.rpow_le_rpow_of_exponent_le hLN_gt1.le (le_max_left _ _)
  have htot :
      ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
        |(((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
          ((chenGoldbachSet N).card : ℝ) * multDensity (chenPrimeDensity N) d| ≤
      C_fin * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by
    dsimp only [C_fin]
    have heq : (C_bv + K_sq / Real.log 2 + 12 * K_sq / Real.log 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' =
        C_bv * (N : ℝ) / (Real.log (N : ℝ)) ^ A' +
        (K_sq / Real.log 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' +
        (12 * K_sq / Real.log 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A' := by ring
    linarith
  exact htot.trans (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hLN_pos A_exp) hA_pow_le)

/-- **Goldbach Shifted-Prime Remainder Bound (`chen_A_remainder_bound`)**:
for every `A_exp : ℝ`, there exist `B > 0`, `C > 0` such that for all even `N ≥ 4` and
`D = √N / (log N)^B`:
`∑_{d < D, Squarefree d, p|d → p < N^{1/8}} |#(A_d) - |A| * g(d)| ≤ C * N / (log N)^{A_exp}`. -/
theorem chen_A_remainder_bound (A_exp : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ N : ℕ, 4 ≤ N → Even N →
        let D : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B
        ∑ d ∈ (Finset.range (⌊D⌋₊ + 1)).filter
            (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D ∧
              ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8)),
          |(((chenGoldbachSet N).filter (d ∣ ·)).card : ℝ) -
            ((chenGoldbachSet N).card : ℝ) * multDensity (chenPrimeDensity N) d| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ A_exp := by
  obtain ⟨B₀, C, hB0, hC, hbd⟩ := chen_A_remainder_bound_ge A_exp
  refine ⟨B₀, C, hB0, hC, fun N hN4 hEven => ?_⟩
  dsimp only
  set D : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B₀
  have hsub :
      (Finset.range (⌊D⌋₊ + 1)).filter
          (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D ∧
            ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8)) ⊆
        (Finset.Icc 1 ⌊D⌋₊).filter Squarefree := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hd ⊢
    have hd_ne0 : d ≠ 0 := fun h => not_squarefree_zero (h ▸ hd.2.1)
    exact ⟨⟨by omega, by omega⟩, hd.2.1⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _).trans
    (hbd B₀ le_rfl N hN4 hEven)

/-- **Summed `A_q` Remainder Bound (`chen_Aq_remainder_bound_ge`)**, valid for every `B ≥ B₀`:
for every `A_exp : ℝ`, there exist `B₀ C > 0` such that for all `B ≥ B₀`, all even `N ≥ 4`,
and `D = √N / (log N)^B`:
`∑_{q prime, ¬ q ∣ N, N^{1/8} ≤ q < N^{1/3}} ∑_{d ≤ ⌊D/q⌋₊, Squarefree d, p|d → p < N^{1/8}}`
`|#((A_q)_d) - (|A| / (q - 1)) * g(d)| ≤ C * N / (log N)^{A_exp}`. -/
theorem chen_Aq_remainder_bound_ge (A_exp : ℝ) :
    ∃ B₀ C : ℝ, 0 < B₀ ∧ 0 < C ∧
      ∀ B : ℝ, B₀ ≤ B →
        ∀ N : ℕ, 4 ≤ N → Even N →
          let D : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B
          ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ ¬ q ∣ N ∧
              (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
            ∑ d ∈ (Finset.range (⌊D / (q : ℝ)⌋₊ + 1)).filter
                (fun d : ℕ => Squarefree d ∧
                  ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8)),
              |((((chenGoldbachSet N).filter (q ∣ ·)).filter (d ∣ ·)).card : ℝ) -
                (((chenGoldbachSet N).card : ℝ) / ((q : ℝ) - 1)) *
                  multDensity (chenPrimeDensity N) d| ≤
            C * (N : ℝ) / (Real.log (N : ℝ)) ^ A_exp := by
  obtain ⟨B₀, C₀, hB0, hC0, hbd⟩ := chen_A_remainder_bound_ge A_exp
  refine ⟨B₀, 4 * C₀, hB0, by positivity, fun B hB N hN4 hEven => ?_⟩
  dsimp only
  set D : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B
  have hB_pos : 0 < B := hB0.trans_le hB
  have hNR4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hLN_gt1 : 1 < Real.log (N : ℝ) := by
    have : Real.exp 1 < (N : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hD_lt_sqrt : D < Real.sqrt (N : ℝ) := by
    have hpow_gt1 : 1 < (Real.log (N : ℝ)) ^ B := Real.one_lt_rpow hLN_gt1 hB_pos
    exact div_lt_self (Real.sqrt_pos.mpr hN0) hpow_gt1
  set Qset := (Finset.range N).filter (fun q => q.Prime ∧ ¬ q ∣ N ∧
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3))
  set Dset : ℕ → Finset ℕ := fun q => (Finset.range (⌊D / (q : ℝ)⌋₊ + 1)).filter
    (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8))
  set Mset := (Finset.Icc 1 ⌊D⌋₊).filter Squarefree
  set errFn : ℕ → ℝ := fun m =>
    |(((chenGoldbachSet N).filter (m ∣ ·)).card : ℝ) -
      ((chenGoldbachSet N).card : ℝ) * multDensity (chenPrimeDensity N) m|
  -- Rewrite each term `(q, d)` as `errFn (d * q)` with `d * q ∈ Mset`
  have hterm_eq : ∀ q ∈ Qset, ∀ d ∈ Dset q,
      d * q ∈ Mset ∧
      |((((chenGoldbachSet N).filter (q ∣ ·)).filter (d ∣ ·)).card : ℝ) -
        (((chenGoldbachSet N).card : ℝ) / ((q : ℝ) - 1)) *
          multDensity (chenPrimeDensity N) d| = errFn (d * q) := by
    intro q hq d hd
    simp only [Qset, Dset, Finset.mem_filter, Finset.mem_range] at hq hd
    obtain ⟨hqN, hq_prime, hq_ndvd, hq_lo, _⟩ := hq
    obtain ⟨hd_le, hd_sq, hd_pf⟩ := hd
    have hd_ne0 : d ≠ 0 := fun h => not_squarefree_zero (h ▸ hd_sq)
    have hq_pos : 0 < q := hq_prime.pos
    have hq_not_dvd_d : ¬ q ∣ d := by
      intro hqd
      have hmem : q ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hq_prime, hqd, hd_ne0⟩
      linarith [hd_pf q hmem]
    have hcop_qd : Nat.Coprime q d := hq_prime.coprime_iff_not_dvd.mpr hq_not_dvd_d
    have hdq_sq : Squarefree (d * q) :=
      (Nat.squarefree_mul hcop_qd.symm).mpr ⟨hd_sq, hq_prime.squarefree⟩
    have hdq_le_D : (d * q : ℕ) ≤ ⌊D⌋₊ := by
      have hd_le' : (d : ℝ) ≤ D / (q : ℝ) :=
        (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hd_le)).trans (Nat.floor_le (by positivity))
      have hmul : ((d * q : ℕ) : ℝ) ≤ D := by
        push_cast
        have hqR_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
        exact (le_div_iff₀ hqR_pos).mp hd_le'
      exact Nat.le_floor hmul
    have hmem_M : d * q ∈ Mset := by
      simp only [Mset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.mul_pos (Nat.pos_of_ne_zero hd_ne0) hq_pos, hdq_le_D⟩, hdq_sq⟩
    -- Card equality: `(A.filter (q ∣ ·)).filter (d ∣ ·) = A.filter (d * q ∣ ·)`
    have hfilt_eq : ((chenGoldbachSet N).filter (q ∣ ·)).filter (d ∣ ·) =
        (chenGoldbachSet N).filter (d * q ∣ ·) := by
      ext a
      simp only [Finset.mem_filter, and_assoc]
      constructor
      · rintro ⟨ha, hqa, hda⟩
        exact ⟨ha, hcop_qd.symm.mul_dvd_of_dvd_of_dvd hda hqa⟩
      · rintro ⟨ha, hdqa⟩
        exact ⟨ha, (dvd_mul_left q d).trans hdqa, (dvd_mul_right d q).trans hdqa⟩
    -- Density equality: `multDensity (chenPrimeDensity N) (d * q) = multDensity ... d / (q - 1)`
    have hmd_eq : multDensity (chenPrimeDensity N) (d * q) =
        multDensity (chenPrimeDensity N) d / ((q : ℝ) - 1) := by
      unfold multDensity
      rw [if_pos hdq_sq, if_pos hd_sq, Nat.primeFactors_mul hd_ne0 hq_prime.ne_zero,
        hq_prime.primeFactors]
      have hq_not_mem : q ∉ d.primeFactors := by
        rw [Nat.mem_primeFactors]; intro h; exact hq_not_dvd_d h.2.1
      rw [Finset.union_singleton, Finset.prod_insert hq_not_mem]
      have h2dvd : 2 ∣ N := even_iff_two_dvd.mp hEven
      have hq_ne2 : q ≠ 2 := fun h => hq_ndvd (h ▸ h2dvd)
      unfold chenPrimeDensity
      rw [if_pos ⟨hq_prime, hq_ne2, hq_ndvd⟩]
      ring
    refine ⟨hmem_M, ?_⟩
    dsimp only [errFn]
    rw [hfilt_eq, hmd_eq]
    ring_nf
  -- Rewrite double sum as sum over `S_pairs = Qset.sigma Dset`, then fiber over `m = d * q ∈ Mset`
  have hdouble :
      ∑ q ∈ Qset, ∑ d ∈ Dset q,
        |((((chenGoldbachSet N).filter (q ∣ ·)).filter (d ∣ ·)).card : ℝ) -
          (((chenGoldbachSet N).card : ℝ) / ((q : ℝ) - 1)) *
            multDensity (chenPrimeDensity N) d| =
      ∑ x ∈ Qset.sigma Dset, errFn (x.2 * x.1) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun d hd => ?_
    exact (hterm_eq q hq d hd).2
  change ∑ q ∈ Qset, ∑ d ∈ Dset q,
        |((((chenGoldbachSet N).filter (q ∣ ·)).filter (d ∣ ·)).card : ℝ) -
          (((chenGoldbachSet N).card : ℝ) / ((q : ℝ) - 1)) *
            multDensity (chenPrimeDensity N) d| ≤ _
  rw [hdouble]
  -- Group by fiber `x.2 * x.1 = m` for `m ∈ Mset`, each fiber has card `≤ 4`!
  have hfiber :
      ∑ x ∈ Qset.sigma Dset, errFn (x.2 * x.1) =
        ∑ m ∈ Mset, ∑ x ∈ (Qset.sigma Dset).filter (fun x => x.2 * x.1 = m), errFn m := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => x.2 * x.1) (t := Mset)]
    · refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.mp hx).2]
    · intro x hx
      rw [Finset.mem_sigma] at hx
      exact (hterm_eq x.1 hx.1 x.2 hx.2).1
  rw [hfiber]
  have hcard_le4 : ∀ m ∈ Mset,
      ((Qset.sigma Dset).filter (fun x => x.2 * x.1 = m)).card ≤ 4 := by
    intro m hm
    simp only [Mset, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmD⟩, _⟩ := hm
    set P_big := m.primeFactors.filter (fun q : ℕ => (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ))
    have hinj : ((Qset.sigma Dset).filter (fun x => x.2 * x.1 = m)).card ≤ P_big.card := by
      refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_sigma, Qset,
          Finset.mem_filter, Finset.mem_range] at hx
        simp only [P_big, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_primeFactors]
        exact ⟨⟨hx.1.1.2.1, ⟨x.2, by rw [← hx.2, mul_comm]⟩, by omega⟩, hx.1.1.2.2.2.1⟩
      · intro x hx y hy hxy
        dsimp only at hxy
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_sigma, Qset,
          Finset.mem_filter, Finset.mem_range] at hx hy
        have hq_pos : 0 < x.1 := hx.1.1.2.1.pos
        have h2 : x.2 = y.2 := by
          have : x.2 * x.1 = y.2 * x.1 := by rw [hx.2, hxy, hy.2]
          exact Nat.eq_of_mul_eq_mul_right hq_pos this
        exact Sigma.ext hxy (heq_of_eq h2)
    -- `P_big.card ≤ 3 ≤ 4` because `∏_{q ∈ P_big} q ≤ m < √N = (N^{1/8})^4`
    have hP_lt4 : P_big.card < 4 := by
      by_contra hge4
      push Not at hge4
      have hprod_le_m : (∏ q ∈ P_big, (q : ℝ)) ≤ (m : ℝ) := by
        have hnat : ∏ q ∈ P_big, q ≤ m := by
          have hdvd : ∏ q ∈ P_big, q ∣ m :=
            (Finset.prod_dvd_prod_of_subset P_big m.primeFactors id
              (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd m)
          exact Nat.le_of_dvd (by omega) hdvd
        rw [← Nat.cast_prod]
        exact_mod_cast hnat
      have hm_lt_sqrt : (m : ℝ) < Real.sqrt (N : ℝ) :=
        ((Nat.cast_le.mpr hmD).trans (Nat.floor_le (by positivity))).trans_lt hD_lt_sqrt
      have hN18_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) :=
        Real.one_le_rpow (by linarith) (by norm_num)
      have hprod_ge : Real.sqrt (N : ℝ) ≤ ∏ q ∈ P_big, (q : ℝ) := by
        calc Real.sqrt (N : ℝ)
            = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
          _ = ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ (4 : ℕ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
              congr 1; norm_num
          _ ≤ ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ P_big.card :=
              pow_le_pow_right₀ hN18_ge1 hge4
          _ = ∏ _q ∈ P_big, (N : ℝ) ^ ((1 : ℝ) / 8) := by simp
          _ ≤ ∏ q ∈ P_big, (q : ℝ) :=
              Finset.prod_le_prod (fun _ _ => by positivity) fun q hq =>
                (Finset.mem_filter.mp hq).2
      linarith
    omega
  calc ∑ m ∈ Mset, ∑ _x ∈ (Qset.sigma Dset).filter (fun x => x.2 * x.1 = m), errFn m
      ≤ ∑ m ∈ Mset, 4 * errFn m := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le4 m hm) (abs_nonneg _)
    _ = 4 * ∑ m ∈ Mset, errFn m := by rw [← Finset.mul_sum]
    _ ≤ 4 * (C₀ * (N : ℝ) / (Real.log (N : ℝ)) ^ A_exp) :=
        mul_le_mul_of_nonneg_left (hbd B hB N hN4 hEven) (by norm_num)
    _ = (4 * C₀) * (N : ℝ) / (Real.log (N : ℝ)) ^ A_exp := by ring

/-- **Summed `A_q` Remainder Bound (`chen_Aq_remainder_bound`)** (existential `(B, C)` form). -/
theorem chen_Aq_remainder_bound (A_exp : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ N : ℕ, 4 ≤ N → Even N →
        let D : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B
        ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ ¬ q ∣ N ∧
            (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
          ∑ d ∈ (Finset.range (⌊D / (q : ℝ)⌋₊ + 1)).filter
              (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D / (q : ℝ) ∧
                ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8)),
            |((((chenGoldbachSet N).filter (q ∣ ·)).filter (d ∣ ·)).card : ℝ) -
              (((chenGoldbachSet N).card : ℝ) / ((q : ℝ) - 1)) *
                multDensity (chenPrimeDensity N) d| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ A_exp := by
  obtain ⟨B₀, C, hB0, hC, hbd⟩ := chen_Aq_remainder_bound_ge A_exp
  refine ⟨B₀, C, hB0, hC, fun N hN4 hEven => ?_⟩
  dsimp only
  set D : ℝ := Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B₀
  refine (Finset.sum_le_sum fun q _ => ?_).trans (hbd B₀ le_rfl N hN4 hEven)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => abs_nonneg _
  intro d hd
  simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢
  exact ⟨hd.1, hd.2.1, hd.2.2.2⟩

/-! ## Section 3: Mertens–Riemann Prime Sum Lemma & `T₂` Integral Bound -/

/-- Helper: `∑_{b ∈ s.biUnion t} f b ≤ ∑_{a ∈ s} ∑_{b ∈ t a} f b` for nonnegative `f`. -/
private lemma sum_biUnion_le_nonneg {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion :
        ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := t a ∩ s.biUnion t) (f := f) fun b _ => hf b]
    linarith

/-- Mertens II prime-reciprocal bound on a power interval `[N^α, N^β)`:
there exists `C_M > 0` such that for all `N ≥ 2` and `0 < α ≤ β` with `2 ≤ N^α`:
`∑_{N^α ≤ p < N^β, p prime} 1/p ≤ log(β / α) + (2 * C_M / α) / log N + (N^α)⁻¹`. -/
private lemma sum_primes_rpow_inv_le :
    ∃ C_M : ℝ, 0 < C_M ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (α β : ℝ), 0 < α → α ≤ β → 2 ≤ (N : ℝ) ^ α →
        ∑ p ∈ (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ α ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ β),
          (p : ℝ)⁻¹ ≤
          Real.log (β / α) + (2 * C_M / α) / Real.log (N : ℝ) + ((N : ℝ) ^ α)⁻¹ := by
  obtain ⟨C_M, hCM, hM2⟩ := Stage8MertensTheorems.mertens_second_theorem_ge_two
  refine ⟨C_M, hCM, fun N hN2 α β hα hαβ hNa2 => ?_⟩
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hLN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hNa_le_Nb : (N : ℝ) ^ α ≤ (N : ℝ) ^ β := Real.rpow_le_rpow_of_exponent_le hN1.le hαβ
  have hNb2 : 2 ≤ (N : ℝ) ^ β := hNa2.trans hNa_le_Nb
  set S := (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ α ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ β)
  set k₀ : ℕ := ⌊(N : ℝ) ^ α⌋₊
  set A := (Finset.Icc 1 ⌊(N : ℝ) ^ β⌋₊).filter Nat.Prime
  set B := (Finset.Icc 1 k₀).filter Nat.Prime
  have hBA : B ⊆ A := by
    intro p hp
    simp only [A, B, k₀, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hNa_le_Nb)⟩, hp.2⟩
  -- Split `S` into `p = k₀` and `p ≠ k₀`
  rw [← Finset.sum_filter_add_sum_filter_not S (· = k₀)]
  have hbd_eq : ∑ p ∈ S.filter (· = k₀), (p : ℝ)⁻¹ ≤ ((N : ℝ) ^ α)⁻¹ := by
    by_cases hk : k₀ ∈ S
    · have hfilt : S.filter (· = k₀) = {k₀} := by
        ext p; simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hk, h⟩⟩
      rw [hfilt, Finset.sum_singleton]
      have hk_ge : (N : ℝ) ^ α ≤ (k₀ : ℝ) := (Finset.mem_filter.mp hk).2.2.1
      exact inv_anti₀ (by linarith) hk_ge
    · have hfilt : S.filter (· = k₀) = ∅ := by
        ext p; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨hpS, rfl⟩; exact hk hpS
      rw [hfilt, Finset.sum_empty]
      positivity
  have hsub_ne : S.filter (· ≠ k₀) ⊆ A \ B := by
    intro p hp
    simp only [S, A, B, k₀, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨_, hp_prime, hp_lo, hp_hi⟩, hp_ne⟩ := hp
    have hp_le_b : p ≤ ⌊(N : ℝ) ^ β⌋₊ := Nat.le_floor hp_hi.le
    have hp_not_le_a : ¬ p ≤ ⌊(N : ℝ) ^ α⌋₊ := by
      intro hle
      have hp_leR : (p : ℝ) ≤ (N : ℝ) ^ α :=
        (Nat.cast_le.mpr hle).trans (Nat.floor_le (by linarith))
      have hp_eqR : (p : ℝ) = (N : ℝ) ^ α := le_antisymm hp_leR hp_lo
      apply hp_ne
      have hfl : ⌊(N : ℝ) ^ α⌋₊ = p := by rw [← hp_eqR, Nat.floor_natCast]
      exact hfl.symm
    exact ⟨⟨⟨hp_prime.one_le, hp_le_b⟩, hp_prime⟩, fun h => hp_not_le_a h.1.2⟩
  have hbd_ne : ∑ p ∈ S.filter (· ≠ k₀), (p : ℝ)⁻¹ ≤
      Stage8MertensTheorems.mertensSum2 ((N : ℝ) ^ β) - Stage8MertensTheorems.mertensSum2 ((N : ℝ) ^ α) := by
    have hsum_sdiff : ∑ p ∈ A \ B, (p : ℝ)⁻¹ =
        Stage8MertensTheorems.mertensSum2 ((N : ℝ) ^ β) - Stage8MertensTheorems.mertensSum2 ((N : ℝ) ^ α) := by
      unfold Stage8MertensTheorems.mertensSum2
      have := Finset.sum_sdiff hBA (f := fun p : ℕ => (p : ℝ)⁻¹)
      linarith
    rw [← hsum_sdiff]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub_ne fun _ _ _ => by positivity
  -- Apply Mertens II at `N^β` and `N^α`
  have hm_b := abs_le.mp (hM2 ((N : ℝ) ^ β) hNb2)
  have hm_a := abs_le.mp (hM2 ((N : ℝ) ^ α) hNa2)
  have hlog_b : Real.log ((N : ℝ) ^ β) = β * Real.log (N : ℝ) := Real.log_rpow hN0 β
  have hlog_a : Real.log ((N : ℝ) ^ α) = α * Real.log (N : ℝ) := Real.log_rpow hN0 α
  have hlog_diff : Real.log (Real.log ((N : ℝ) ^ β)) - Real.log (Real.log ((N : ℝ) ^ α)) =
      Real.log (β / α) := by
    rw [hlog_b, hlog_a, Real.log_mul (by linarith) hLN_pos.ne',
      Real.log_mul hα.ne' hLN_pos.ne', Real.log_div (by linarith) hα.ne']
    ring
  have herr : C_M / Real.log ((N : ℝ) ^ β) + C_M / Real.log ((N : ℝ) ^ α) ≤
      (2 * C_M / α) / Real.log (N : ℝ) := by
    rw [hlog_b, hlog_a]
    have h1 : C_M / (β * Real.log (N : ℝ)) ≤ C_M / (α * Real.log (N : ℝ)) :=
      div_le_div_of_nonneg_left hCM.le (mul_pos hα hLN_pos) (mul_le_mul_of_nonneg_right hαβ hLN_pos.le)
    have h2 : C_M / (α * Real.log (N : ℝ)) + C_M / (α * Real.log (N : ℝ)) =
        (2 * C_M / α) / Real.log (N : ℝ) := by field_simp [hα.ne', hLN_pos.ne']; ring
    linarith
  linarith

/-- General Mertens–Riemann prime-sum upper bound on `[N^a, N^b)`:
for any `0 < a < b ≤ 1` and any continuous nonnegative `g` on `[a, b]`:
for every `ε > 0`, there exists `N₀ ≥ 2` such that for all `N ≥ N₀`:
`∑_{N^a ≤ p < N^b, p prime} g(log p / log N) / p ≤ (∫ u in a..b, g u / u) + ε`. -/
private lemma sum_primes_Ico_rpow_le_integral {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Set.Icc a b)) (hg_nn : ∀ u ∈ Set.Icc a b, 0 ≤ g u) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∑ p ∈ (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b),
        g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) ≤
        (∫ u in a..b, g u / u) + ε := by
  intro ε hε
  obtain ⟨C_M, hCM, hmertens⟩ := sum_primes_rpow_inv_le
  have hlogba_pos : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div ha).mpr hab)
  set η : ℝ := ε / (4 * Real.log (b / a) + 4) with hη_def
  have hη_pos : 0 < η := by positivity
  have hη_log : 2 * η * Real.log (b / a) ≤ ε / 2 := by
    dsimp only [η]
    rw [show 2 * (ε / (4 * Real.log (b / a) + 4)) * Real.log (b / a) =
        ε * ((2 * Real.log (b / a)) / (4 * Real.log (b / a) + 4)) by ring]
    have hfrac : (2 * Real.log (b / a)) / (4 * Real.log (b / a) + 4) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    nlinarith
  -- Uniform continuity of `g` on compact `[a, b]`
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨ρ, hρ_pos, hρ⟩ := huc η hη_pos
  set M : ℕ := ⌈(b - a) / ρ⌉₊ + 1
  have hM_pos : 0 < M := Nat.succ_pos _
  have hMR_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  set h : ℝ := (b - a) / (M : ℝ)
  have hh_pos : 0 < h := div_pos (sub_pos.mpr hab) hMR_pos
  have hh_lt_ρ : h < ρ := by
    dsimp only [h]
    rw [div_lt_iff₀ hMR_pos]
    have h1 : (b - a) / ρ < (M : ℝ) := by
      have : (b - a) / ρ ≤ (⌈(b - a) / ρ⌉₊ : ℝ) := Nat.le_ceil _
      dsimp only [M]; push_cast; linarith
    have := (div_lt_iff₀ hρ_pos).mp h1
    linarith
  set u : ℕ → ℝ := fun k => a + (k : ℝ) * h
  have hu0 : u 0 = a := by simp [u]
  have huM : u M = b := by
    dsimp only [u, h]; field_simp [hMR_pos.ne']; ring
  have hu_step : ∀ k : ℕ, u (k + 1) - u k = h := fun k => by
    dsimp only [u]; push_cast; ring
  have hu_le : ∀ k : ℕ, k ≤ M → u k ∈ Set.Icc a b := fun k hk => by
    have hkR : (k : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hk
    constructor
    · dsimp only [u]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    · have : (k : ℝ) * h ≤ (M : ℝ) * h := mul_le_mul_of_nonneg_right hkR hh_pos.le
      have hMh : (M : ℝ) * h = b - a := mul_div_cancel₀ (b - a) hMR_pos.ne'
      dsimp only [u]; linarith
  -- Define `G_sum = ∑_{k < M} (g (u k) + η) > 0`
  set G_sum : ℝ := ∑ k ∈ Finset.range M, (g (u k) + η)
  have hG_pos : 0 < G_sum := by
    refine Finset.sum_pos (fun k hk => ?_) ⟨0, Finset.mem_range.mpr hM_pos⟩
    have hmem := hu_le k (Nat.lt_succ_iff.mp (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))
    linarith [hg_nn (u k) hmem]
  -- Choose `N₀` large enough that `(N^a) ≥ max 2 (4 * G_sum / ε)` and `(2 * C_M / a) / log N ≤ ε / (4 * G_sum)`
  set R_pow : ℝ := (max 2 (4 * G_sum / ε)) ^ (1 / a)
  set R_log : ℝ := Real.exp (8 * C_M * G_sum / (a * ε))
  set N₀ : ℕ := max 2 (max ⌈R_pow⌉₊ ⌈R_log⌉₊)
  refine ⟨N₀, le_max_left _ _, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hLN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hN_ge_pow : R_pow ≤ (N : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hN)
  have hN_ge_log : R_log ≤ (N : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hN)
  have hNa_ge : max 2 (4 * G_sum / ε) ≤ (N : ℝ) ^ a := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hN_ge_pow ha.le
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel ha.ne', Real.rpow_one] at h1
    exact h1
  have hNa2 : 2 ≤ (N : ℝ) ^ a := (le_max_left _ _).trans hNa_ge
  have hNa_err : ((N : ℝ) ^ a)⁻¹ ≤ ε / (4 * G_sum) := by
    have h1 : 4 * G_sum / ε ≤ (N : ℝ) ^ a := (le_max_right _ _).trans hNa_ge
    calc ((N : ℝ) ^ a)⁻¹ ≤ (4 * G_sum / ε)⁻¹ := inv_anti₀ (by positivity) h1
      _ = ε / (4 * G_sum) := by rw [inv_div]
  have hlog_err : (2 * C_M / a) / Real.log (N : ℝ) ≤ ε / (4 * G_sum) := by
    have hLN_ge : 8 * C_M * G_sum / (a * ε) ≤ Real.log (N : ℝ) := by
      exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hN_ge_log)
    rw [div_le_div_iff₀ hLN_pos (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hLN_ge hε.le
    have h2 : ε * (8 * C_M * G_sum / (a * ε)) = (2 * C_M / a) * (4 * G_sum) := by
      field_simp [ha.ne', hε.ne']; ring
    linarith
  -- Bin decomposition of `S` into `S_bin k` for `k ∈ range M`
  set S := (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)
  set S_bin : ℕ → Finset ℕ := fun k =>
    (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ (u k) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (u (k + 1)))
  have hcover : S ⊆ (Finset.range M).biUnion S_bin := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpN, hp_prime, hp_lo, hp_hi⟩ := hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
    have hlogp_lo : a ≤ Real.log (p : ℝ) / Real.log (N : ℝ) := by
      rw [le_div_iff₀ hLN_pos]
      have := Real.log_le_log (Real.rpow_pos_of_pos hN0 a) hp_lo
      rwa [Real.log_rpow hN0] at this
    have hlogp_hi : Real.log (p : ℝ) / Real.log (N : ℝ) < b := by
      rw [div_lt_iff₀ hLN_pos]
      have := Real.log_lt_log hp_pos hp_hi
      rwa [Real.log_rpow hN0] at this
    set t : ℝ := (Real.log (p : ℝ) / Real.log (N : ℝ) - a) / h
    have ht_nn : 0 ≤ t := div_nonneg (by linarith) hh_pos.le
    have ht_lt_M : t < (M : ℝ) := by
      dsimp only [t, h]
      rw [div_lt_iff₀ (div_pos (sub_pos.mpr hab) hMR_pos)]
      have hMh : (M : ℝ) * ((b - a) / (M : ℝ)) = b - a := mul_div_cancel₀ _ hMR_pos.ne'
      linarith
    set k : ℕ := ⌊t⌋₊
    have hkM : k < M := by
      have hk_le : (k : ℝ) ≤ t := Nat.floor_le ht_nn
      exact_mod_cast (hk_le.trans_lt ht_lt_M)
    have hku_lo : u k ≤ Real.log (p : ℝ) / Real.log (N : ℝ) := by
      have hk_le : (k : ℝ) ≤ t := Nat.floor_le ht_nn
      have := (le_div_iff₀ hh_pos).mp hk_le
      dsimp only [u]; linarith
    have hku_hi : Real.log (p : ℝ) / Real.log (N : ℝ) < u (k + 1) := by
      have hlt : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
      have := (div_lt_iff₀ hh_pos).mp hlt
      dsimp only [u]; push_cast; linarith
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkM, ?_⟩
    simp only [S_bin, Finset.mem_filter, Finset.mem_range]
    refine ⟨hpN, hp_prime, ?_, ?_⟩
    · rw [Real.rpow_def_of_pos hN0]
      have h1 : Real.log (N : ℝ) * u k ≤ Real.log (p : ℝ) := by
        have := (le_div_iff₀ hLN_pos).mp hku_lo; linarith
      exact (Real.exp_le_exp.mpr h1).trans_eq (Real.exp_log hp_pos)
    · rw [Real.rpow_def_of_pos hN0]
      have h1 : Real.log (p : ℝ) < Real.log (N : ℝ) * u (k + 1) := by
        have := (div_lt_iff₀ hLN_pos).mp hku_hi; linarith
      exact (Real.exp_log hp_pos).symm.trans_lt (Real.exp_lt_exp.mpr h1)
  -- Nonnegativity of summand on `(range M).biUnion S_bin`
  have hterm_nn : ∀ p ∈ (Finset.range M).biUnion S_bin,
      0 ≤ g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.mp hp
    simp only [S_bin, Finset.mem_filter] at hpk
    have hkM : k < M := Finset.mem_range.mp hk
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpk.2.1.pos
    have hlo : a ≤ Real.log (p : ℝ) / Real.log (N : ℝ) := by
      have h1 : a ≤ u k := (hu_le k (by omega)).1
      have h2 := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hpk.2.2.1
      rw [Real.log_rpow hN0] at h2
      exact h1.trans ((le_div_iff₀ hLN_pos).mpr (by linarith))
    have hhi : Real.log (p : ℝ) / Real.log (N : ℝ) ≤ b := by
      have h1 : u (k + 1) ≤ b := (hu_le (k + 1) (by omega)).2
      have h2 := Real.log_le_log hp_pos hpk.2.2.2.le
      rw [Real.log_rpow hN0] at h2
      exact ((div_le_iff₀ hLN_pos).mpr (by linarith)).trans h1
    exact div_nonneg (hg_nn _ ⟨hlo, hhi⟩) hp_pos.le
  -- Bound sum over `S` by sum over bins `k < M`
  have hsum_bins :
      ∑ p ∈ S, g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) ≤
        ∑ k ∈ Finset.range M,
          ∑ p ∈ S_bin k, g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hcover (fun p hp _ => hterm_nn p hp)
    -- Apply `sum_biUnion_le_nonneg` using `max 0` so nonnegativity holds globally
    have h2 : ∑ p ∈ (Finset.range M).biUnion S_bin,
          max 0 (g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) ≤
        ∑ k ∈ Finset.range M, ∑ p ∈ S_bin k,
          max 0 (g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) :=
      sum_biUnion_le_nonneg _ _ _ fun _ => le_max_left _ _
    have hlhs : ∑ p ∈ (Finset.range M).biUnion S_bin,
          max 0 (g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) =
        ∑ p ∈ (Finset.range M).biUnion S_bin, g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) :=
      Finset.sum_congr rfl fun p hp => max_eq_right (hterm_nn p hp)
    have hrhs : ∑ k ∈ Finset.range M, ∑ p ∈ S_bin k,
          max 0 (g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) =
        ∑ k ∈ Finset.range M, ∑ p ∈ S_bin k, g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) :=
      Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun p hp =>
        max_eq_right (hterm_nn p (Finset.mem_biUnion.mpr ⟨k, hk, hp⟩))
    rw [hlhs, hrhs] at h2
    exact h1.trans h2
  -- Bound each bin `k < M`
  have hbin_bd : ∀ k ∈ Finset.range M,
      ∑ p ∈ S_bin k, g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) ≤
        (∫ t in (u k)..(u (k + 1)), g t / t) +
        2 * η * Real.log (u (k + 1) / u k) +
        (g (u k) + η) * ((2 * C_M / a) / Real.log (N : ℝ) + ((N : ℝ) ^ a)⁻¹) := by
    intro k hk
    have hkM : k < M := Finset.mem_range.mp hk
    have huk_mem : u k ∈ Set.Icc a b := hu_le k (by omega)
    have huk1_mem : u (k + 1) ∈ Set.Icc a b := hu_le (k + 1) (by omega)
    have huk_pos : 0 < u k := ha.trans_le huk_mem.1
    have huk_le1 : u k ≤ u (k + 1) := by linarith [hu_step k]
    have huk1_pos : 0 < u (k + 1) := huk_pos.trans_le huk_le1
    have hg_uk_nn : 0 ≤ g (u k) + η := by linarith [hg_nn (u k) huk_mem]
    -- Pointwise `g (log p / log N) ≤ g (u k) + η` on `S_bin k`
    have hpt_k : ∑ p ∈ S_bin k, g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) ≤
        (g (u k) + η) * ∑ p ∈ S_bin k, (p : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      simp only [S_bin, Finset.mem_filter] at hp
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.2.1.pos
      have hlo : u k ≤ Real.log (p : ℝ) / Real.log (N : ℝ) := by
        have h2 := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hp.2.2.1
        rw [Real.log_rpow hN0] at h2
        exact (le_div_iff₀ hLN_pos).mpr (by linarith)
      have hhi : Real.log (p : ℝ) / Real.log (N : ℝ) ≤ u (k + 1) := by
        have h2 := Real.log_le_log hp_pos hp.2.2.2.le
        rw [Real.log_rpow hN0] at h2
        exact (div_le_iff₀ hLN_pos).mpr (by linarith)
      have hdist : dist (Real.log (p : ℝ) / Real.log (N : ℝ)) (u k) < ρ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith [hu_step k]
      have hclose := hρ _ ⟨huk_mem.1.trans hlo, hhi.trans huk1_mem.2⟩ _ huk_mem hdist
      rw [Real.dist_eq] at hclose
      have hgle : g (Real.log (p : ℝ) / Real.log (N : ℝ)) ≤ g (u k) + η := by
        linarith [(abs_le.mp hclose.le).2]
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hgle (inv_nonneg.mpr hp_pos.le)
    -- Apply Mertens II on `[N^{u k}, N^{u (k+1)})`
    have hNuk2 : 2 ≤ (N : ℝ) ^ (u k) := hNa2.trans (Real.rpow_le_rpow_of_exponent_le hN1.le huk_mem.1)
    have hm_k := hmertens N hN2 (u k) (u (k + 1)) huk_pos huk_le1 hNuk2
    have hm_k' : ∑ p ∈ S_bin k, (p : ℝ)⁻¹ ≤
        Real.log (u (k + 1) / u k) + (2 * C_M / a) / Real.log (N : ℝ) + ((N : ℝ) ^ a)⁻¹ := by
      have h1 : 2 * C_M / u k ≤ 2 * C_M / a :=
        div_le_div_of_nonneg_left (by positivity) ha huk_mem.1
      have h2 : (2 * C_M / u k) / Real.log (N : ℝ) ≤ (2 * C_M / a) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right h1 hLN_pos.le
      have h3 : ((N : ℝ) ^ (u k))⁻¹ ≤ ((N : ℝ) ^ a)⁻¹ :=
        inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hN1.le huk_mem.1)
      linarith
    -- Compare `(g (u k) + η) * log (u (k+1) / u k)` to `∫_{u k}^{u (k+1)} (g t + 2 * η) / t dt`
    have hint_inv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (u k) (u (k + 1)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le huk_le1]
      exact continuousOn_id.inv₀ fun t ht => (huk_pos.trans_le ht.1).ne'
    have hint_g : IntervalIntegrable (fun t : ℝ => g t / t) volume (u k) (u (k + 1)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le huk_le1]
      refine (hg_cont.mono fun t ht => ⟨huk_mem.1.trans ht.1, ht.2.trans huk1_mem.2⟩).div
        continuousOn_id fun t ht => (huk_pos.trans_le ht.1).ne'
    have hlog_eq_int : Real.log (u (k + 1) / u k) = ∫ t in (u k)..(u (k + 1)), t⁻¹ :=
      (integral_inv_of_pos huk_pos huk1_pos).symm
    have hint_cmp :
        (g (u k) + η) * Real.log (u (k + 1) / u k) ≤
          (∫ t in (u k)..(u (k + 1)), g t / t) + 2 * η * Real.log (u (k + 1) / u k) := by
      rw [hlog_eq_int, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add hint_g (hint_inv.const_mul (2 * η))]
      refine intervalIntegral.integral_mono_on huk_le1 (hint_inv.const_mul _)
        (hint_g.add (hint_inv.const_mul _)) fun t ht => ?_
      have ht_pos : 0 < t := huk_pos.trans_le ht.1
      have hdist : dist (u k) t < ρ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2, hu_step k]
      have hclose := hρ _ huk_mem _ ⟨huk_mem.1.trans ht.1, ht.2.trans huk1_mem.2⟩ hdist
      rw [Real.dist_eq] at hclose
      have hgle : g (u k) ≤ g t + η := by linarith [(abs_le.mp hclose.le).2]
      have heq : g t / t + 2 * η * t⁻¹ = (g t + 2 * η) * t⁻¹ := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr ht_pos.le)
    calc ∑ p ∈ S_bin k, g (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)
        ≤ (g (u k) + η) * ∑ p ∈ S_bin k, (p : ℝ)⁻¹ := hpt_k
      _ ≤ (g (u k) + η) * (Real.log (u (k + 1) / u k) + (2 * C_M / a) / Real.log (N : ℝ) + ((N : ℝ) ^ a)⁻¹) :=
          mul_le_mul_of_nonneg_left hm_k' hg_uk_nn
      _ = (g (u k) + η) * Real.log (u (k + 1) / u k) +
            (g (u k) + η) * ((2 * C_M / a) / Real.log (N : ℝ) + ((N : ℝ) ^ a)⁻¹) := by ring
      _ ≤ _ := by linarith
  -- Sum over `k ∈ Finset.range M`
  have hsum_int : ∀ m : ℕ, m ≤ M →
      ∑ k ∈ Finset.range m, ∫ t in (u k)..(u (k + 1)), g t / t = ∫ t in a..(u m), g t / t := by
    intro m hm
    induction m with
    | zero => simp [hu0]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      have hint1 : IntervalIntegrable (fun t : ℝ => g t / t) volume a (u m) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (hu_le m (by omega)).1]
        refine (hg_cont.mono fun t ht => ⟨ht.1, ht.2.trans (hu_le m (by omega)).2⟩).div
          continuousOn_id fun t ht => (ha.trans_le ht.1).ne'
      have hint2 : IntervalIntegrable (fun t : ℝ => g t / t) volume (u m) (u (m + 1)) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (by linarith [hu_step m] : u m ≤ u (m + 1))]
        refine (hg_cont.mono fun t ht => ⟨(hu_le m (by omega)).1.trans ht.1,
          ht.2.trans (hu_le (m + 1) hm).2⟩).div
          continuousOn_id fun t ht => (ha.trans_le ((hu_le m (by omega)).1.trans ht.1)).ne'
      exact intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hsum_log : ∑ k ∈ Finset.range M, Real.log (u (k + 1) / u k) = Real.log (b / a) := by
    have hcongr : ∑ k ∈ Finset.range M, Real.log (u (k + 1) / u k) =
        ∑ k ∈ Finset.range M, (Real.log (u (k + 1)) - Real.log (u k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkM : k < M := Finset.mem_range.mp hk
      have huk_pos : 0 < u k := ha.trans_le (hu_le k (by omega)).1
      have huk1_pos : 0 < u (k + 1) := ha.trans_le (hu_le (k + 1) (by omega)).1
      exact Real.log_div huk1_pos.ne' huk_pos.ne'
    rw [hcongr, Finset.sum_range_sub (fun k => Real.log (u k)) M, huM, hu0,
      Real.log_div (ha.trans hab).ne' ha.ne']
  have htot := hsum_bins.trans (Finset.sum_le_sum hbin_bd)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_int M le_rfl, huM,
    ← Finset.mul_sum, hsum_log, ← Finset.sum_mul] at htot
  have herr_tot : G_sum * ((2 * C_M / a) / Real.log (N : ℝ) + ((N : ℝ) ^ a)⁻¹) ≤ ε / 2 := by
    have hhalf : ε / (4 * G_sum) + ε / (4 * G_sum) = ε / (2 * G_sum) := by ring
    have h1 : (2 * C_M / a) / Real.log (N : ℝ) + ((N : ℝ) ^ a)⁻¹ ≤ ε / (2 * G_sum) := by linarith
    calc G_sum * ((2 * C_M / a) / Real.log (N : ℝ) + ((N : ℝ) ^ a)⁻¹)
        ≤ G_sum * (ε / (2 * G_sum)) := mul_le_mul_of_nonneg_left h1 hG_pos.le
      _ = ε / 2 := by field_simp [hG_pos.ne']
  linarith

/-- **`T₂` Prime-Sum to Integral Bound (`chen_T2_sum_le_integral`)**:
for any `F : ℝ → ℝ` continuous, antitone, and nonnegative on `(0, ∞)` and any `B_any > 0`:
for every `ε > 0`, there exists `N₀` such that for all `N ≥ N₀`:
`∑_{q prime, ¬ q ∣ N, N^{1/8} ≤ q < N^{1/3}} F(log((√N / (log N)^{B_any}) / q) / log(N^{1/8})) / (q - 1)`
`≤ (∫ u in (1/8)..(1/3), F (4 - 8 * u) / u) + ε`. -/
theorem chen_T2_sum_le_integral {F : ℝ → ℝ}
    (hF_cont : ContinuousOn F (Set.Ioi 0)) (_hF_anti : AntitoneOn F (Set.Ioi 0))
    (hF_nn : ∀ s > 0, 0 ≤ F s) {B_any : ℝ} (hB : 0 < B_any) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ q ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧ ¬ q ∣ N ∧
          (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3)),
        F ((Real.log ((Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B_any) / (q : ℝ))) /
           Real.log ((N : ℝ) ^ ((1 : ℝ) / 8))) / ((q : ℝ) - 1) ≤
        (∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), F (4 - 8 * u) / u) + ε := by
  intro ε hε
  -- Continuity of `g u = F (4 - 8 * u)` on `[1/8, 1/3]`
  have hg_cont : ContinuousOn (fun u : ℝ => F (4 - 8 * u)) (Set.Icc (1 / 8 : ℝ) (1 / 3 : ℝ)) := by
    refine hF_cont.comp (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
    intro u hu
    simp only [Set.mem_Ioi]
    linarith [hu.2]
  have hg_nn : ∀ u ∈ Set.Icc (1 / 8 : ℝ) (1 / 3 : ℝ), 0 ≤ F (4 - 8 * u) := fun u hu =>
    hF_nn _ (by linarith [hu.2])
  set I_val : ℝ := ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), F (4 - 8 * u) / u
  have hI_nn : 0 ≤ I_val := intervalIntegral.integral_nonneg (by norm_num) fun u hu =>
    div_nonneg (hg_nn u hu) (by linarith [hu.1])
  -- Tolerance split: `(1 + η₁) * (I_val + η₂ * log(8/3) + η₃) ≤ I_val + ε`
  set η₁ : ℝ := min 1 (ε / (4 * (I_val + 1)))
  have hη₁_pos : 0 < η₁ := lt_min zero_lt_one (by positivity)
  have hη₁_le1 : η₁ ≤ 1 := min_le_left _ _
  set η₂ : ℝ := ε / 20
  have hη₂_pos : 0 < η₂ := by positivity
  set η₃ : ℝ := ε / 20
  have hη₃_pos : 0 < η₃ := by positivity
  -- Uniform continuity of `F` on compact `[1, 4] ⊆ (0, ∞)`
  have hF_uc := isCompact_Icc.uniformContinuousOn_of_continuous
    (hF_cont.mono (fun s (hs : s ∈ Set.Icc (1 : ℝ) 4) => (by linarith [hs.1] : (0 : ℝ) < s)))
  rw [Metric.uniformContinuousOn_iff] at hF_uc
  obtain ⟨ρ, hρ_pos, hρ⟩ := hF_uc η₂ hη₂_pos
  -- Apply `sum_primes_Ico_rpow_le_integral` to `u ↦ F (4 - 8 * u) + η₂` on `[1/8, 1/3]`
  obtain ⟨N₁, hN₁2, hriem⟩ := sum_primes_Ico_rpow_le_integral
    (a := (1 / 8 : ℝ)) (b := (1 / 3 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (g := fun u => F (4 - 8 * u) + η₂) (hg_cont.add continuousOn_const)
    (fun u hu => by linarith [hg_nn u hu]) η₃ hη₃_pos
  -- Asymptotic control on `δ_N = 8 * B_any * log(log N) / log N → 0`
  have hdelta_tendsto : Tendsto (fun x : ℝ => 8 * B_any * (Real.log (Real.log x) / Real.log x)) atTop (𝓝 0) := by
    have h1 := (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero
    have h2 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
      h1.congr fun u => by rw [Real.rpow_one]
    simpa using (h2.comp Real.tendsto_log_atTop).const_mul (8 * B_any)
  have hev_delta := hdelta_tendsto.eventually (Iio_mem_nhds (lt_min (show (0 : ℝ) < 1 / 3 by norm_num) hρ_pos))
  rw [Filter.eventually_atTop] at hev_delta
  obtain ⟨X_d, hXd⟩ := hev_delta
  -- Also require `N^{1/8} ≥ max 2 (2 / η₁)` (so `1 / (q - 1) ≤ (1 + η₁) / q`) and `N ≥ 16`
  set N_q : ℕ := ⌈(max 2 (2 / η₁)) ^ (8 : ℝ)⌉₊
  set N₀ : ℕ := max (max N₁ 16) (max ⌈X_d⌉₊ N_q)
  refine ⟨N₀, fun N hN => ?_⟩
  have hN_N1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN16 : 16 ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN_Xd : X_d ≤ (N : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hN)
  have hN_Nq : ((max 2 (2 / η₁)) ^ (8 : ℝ)) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by
    have h1 : N_q ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
    dsimp only [N_q] at h1
    exact_mod_cast h1)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hLN_gt1 : 1 < Real.log (N : ℝ) := by
    have : Real.exp 1 < (N : ℝ) := by
      have h16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
      linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLN_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hLN_gt1
  have hLLN_pos : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos hLN_gt1
  have hN18_ge : max 2 (2 / η₁) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hN_Nq (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [← Real.rpow_mul (by positivity)] at h1
    norm_num at h1
    exact max_le h1.1 h1.2
  set δ_N : ℝ := 8 * B_any * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
  have hδ_pos : 0 < δ_N := by positivity
  have hδ_lt : δ_N < min (1 / 3) ρ := hXd (N : ℝ) hN_Xd
  have hδ_lt_third : δ_N < 1 / 3 := lt_of_lt_of_le hδ_lt (min_le_left _ _)
  have hδ_lt_ρ : δ_N < ρ := lt_of_lt_of_le hδ_lt (min_le_right _ _)
  -- Compare each term of the `T₂` sum to `(1 + η₁) * (F (4 - 8 * u) + η₂) / q`
  set S_full := (Finset.range N).filter (fun q : ℕ => q.Prime ∧
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3))
  set S_cop := (Finset.range N).filter (fun q : ℕ => q.Prime ∧ ¬ q ∣ N ∧
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3))
  have hsub_cop : S_cop ⊆ S_full := by
    intro q hq
    simp only [S_cop, S_full, Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.1, hq.2.2.2⟩
  have hpt : ∀ q ∈ S_full,
      0 ≤ F ((Real.log ((Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B_any) / (q : ℝ))) /
          Real.log ((N : ℝ) ^ ((1 : ℝ) / 8))) / ((q : ℝ) - 1) ∧
      F ((Real.log ((Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B_any) / (q : ℝ))) /
          Real.log ((N : ℝ) ^ ((1 : ℝ) / 8))) / ((q : ℝ) - 1) ≤
        (1 + η₁) * ((F (4 - 8 * (Real.log (q : ℝ) / Real.log (N : ℝ))) + η₂) / (q : ℝ)) := by
    intro q hq
    simp only [S_full, Finset.mem_filter] at hq
    obtain ⟨_, hq_prime, hq_lo, hq_hi⟩ := hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_prime.pos
    have hq_ge2 : (2 : ℝ) ≤ (q : ℝ) := ((le_max_left _ _).trans hN18_ge).trans hq_lo
    have hq_ge_inv : 2 / η₁ ≤ (q : ℝ) := ((le_max_right _ _).trans hN18_ge).trans hq_lo
    set u_q : ℝ := Real.log (q : ℝ) / Real.log (N : ℝ)
    have hu_lo : (1 / 8 : ℝ) ≤ u_q := by
      rw [le_div_iff₀ hLN_pos]
      have := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hq_lo
      rwa [Real.log_rpow hN0] at this
    have hu_hi : u_q ≤ (1 / 3 : ℝ) := by
      rw [div_le_iff₀ hLN_pos]
      have := Real.log_le_log hq_pos hq_hi.le
      rwa [Real.log_rpow hN0] at this
    -- Exact identity for the argument of `F`
    have harg_eq :
        (Real.log ((Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B_any) / (q : ℝ))) /
          Real.log ((N : ℝ) ^ ((1 : ℝ) / 8)) = 4 - 8 * u_q - δ_N := by
      rw [Real.log_div (div_pos (Real.sqrt_pos.mpr hN0) (Real.rpow_pos_of_pos hLN_pos B_any)).ne' hq_pos.ne',
        Real.log_div (Real.sqrt_pos.mpr hN0).ne' (Real.rpow_pos_of_pos hLN_pos B_any).ne',
        Real.log_sqrt hN0.le, Real.log_rpow hLN_pos, Real.log_rpow hN0]
      dsimp only [u_q, δ_N]
      field_simp [hLN_pos.ne']
      ring
    rw [harg_eq]
    have harg_mem : 4 - 8 * u_q - δ_N ∈ Set.Icc (1 : ℝ) 4 := by
      constructor <;> linarith
    have hu_mem : 4 - 8 * u_q ∈ Set.Icc (1 : ℝ) 4 := by
      constructor <;> linarith
    have hF_nn_arg : 0 ≤ F (4 - 8 * u_q - δ_N) := hF_nn _ (by linarith [harg_mem.1])
    have hclose := hρ _ harg_mem _ hu_mem (by
      rw [Real.dist_eq, show 4 - 8 * u_q - δ_N - (4 - 8 * u_q) = -δ_N by ring, abs_neg, abs_of_pos hδ_pos]
      exact hδ_lt_ρ)
    rw [Real.dist_eq] at hclose
    have hF_le : F (4 - 8 * u_q - δ_N) ≤ F (4 - 8 * u_q) + η₂ := by
      linarith [(abs_le.mp hclose.le).2]
    have hinv_le : ((q : ℝ) - 1)⁻¹ ≤ (1 + η₁) * (q : ℝ)⁻¹ := by
      have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
      rw [inv_eq_one_div, show (1 + η₁) * (q : ℝ)⁻¹ = (1 + η₁) / (q : ℝ) by ring,
        div_le_div_iff₀ hq1_pos hq_pos, one_mul]
      have hq_eta : 2 ≤ η₁ * (q : ℝ) := (div_le_iff₀ hη₁_pos).mp hq_ge_inv |>.trans_eq (mul_comm _ _)
      nlinarith
    refine ⟨div_nonneg hF_nn_arg (by linarith), ?_⟩
    rw [div_eq_mul_inv, show (1 + η₁) * ((F (4 - 8 * u_q) + η₂) / (q : ℝ)) =
        (F (4 - 8 * u_q) + η₂) * ((1 + η₁) * (q : ℝ)⁻¹) by ring]
    exact mul_le_mul hF_le hinv_le (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)) (by linarith [hF_nn_arg])
  have hsum_le :
      ∑ q ∈ S_cop,
        F ((Real.log ((Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B_any) / (q : ℝ))) /
           Real.log ((N : ℝ) ^ ((1 : ℝ) / 8))) / ((q : ℝ) - 1) ≤
      (1 + η₁) * ∑ q ∈ S_full,
        (F (4 - 8 * (Real.log (q : ℝ) / Real.log (N : ℝ))) + η₂) / (q : ℝ) := by
    calc _ ≤ ∑ q ∈ S_full,
            F ((Real.log ((Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B_any) / (q : ℝ))) /
               Real.log ((N : ℝ) ^ ((1 : ℝ) / 8))) / ((q : ℝ) - 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_cop fun q hq _ => (hpt q hq).1
      _ ≤ ∑ q ∈ S_full,
            (1 + η₁) * ((F (4 - 8 * (Real.log (q : ℝ) / Real.log (N : ℝ))) + η₂) / (q : ℝ)) :=
          Finset.sum_le_sum fun q hq => (hpt q hq).2
      _ = _ := by rw [← Finset.mul_sum]
  -- Apply `hriem`
  have hr := hriem N hN_N1
  have hint_g : IntervalIntegrable (fun u : ℝ => F (4 - 8 * u) / u) volume (1 / 8 : ℝ) (1 / 3 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 1 / 3)]
    exact hg_cont.div continuousOn_id fun u hu => (by linarith [hu.1] : u ≠ 0)
  have hint_c : IntervalIntegrable (fun u : ℝ => η₂ / u) volume (1 / 8 : ℝ) (1 / 3 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 1 / 3)]
    exact continuousOn_const.div continuousOn_id fun u hu => (by linarith [hu.1] : u ≠ 0)
  have hint_split :
      ∫ u in (1 / 8 : ℝ)..(1 / 3 : ℝ), (F (4 - 8 * u) + η₂) / u =
        I_val + η₂ * Real.log ((1 / 3 : ℝ) / (1 / 8 : ℝ)) := by
    have hfun : (fun u : ℝ => (F (4 - 8 * u) + η₂) / u) =
        fun u => F (4 - 8 * u) / u + η₂ / u := by funext u; ring
    rw [hfun, intervalIntegral.integral_add hint_g hint_c]
    congr 1
    have hfun2 : (fun u : ℝ => η₂ / u) = fun u => η₂ * u⁻¹ := by funext u; ring
    rw [hfun2, intervalIntegral.integral_const_mul,
      integral_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (0 : ℝ) < 1 / 3)]
  rw [hint_split] at hr
  have hlog83_le2 : Real.log ((1 / 3 : ℝ) / (1 / 8 : ℝ)) ≤ 2 := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (1 / 3 : ℝ) / (1 / 8 : ℝ))
    linarith
  have hη₁_I : η₁ * I_val ≤ ε / 4 := by
    have h1 : η₁ ≤ ε / (4 * (I_val + 1)) := min_le_right _ _
    calc η₁ * I_val ≤ (ε / (4 * (I_val + 1))) * (I_val + 1) :=
          mul_le_mul h1 (by linarith) hI_nn (by positivity)
      _ = ε / 4 := by field_simp [(by linarith : I_val + 1 ≠ 0)]
  calc _ ≤ (1 + η₁) * ∑ q ∈ S_full,
            (F (4 - 8 * (Real.log (q : ℝ) / Real.log (N : ℝ))) + η₂) / (q : ℝ) := hsum_le
    _ ≤ (1 + η₁) * (I_val + η₂ * Real.log ((1 / 3 : ℝ) / (1 / 8 : ℝ)) + η₃) :=
        mul_le_mul_of_nonneg_left hr (by linarith)
    _ ≤ (1 + η₁) * (I_val + η₂ * 2 + η₃) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        nlinarith
    _ = I_val + η₁ * I_val + (1 + η₁) * (2 * η₂ + η₃) := by ring
    _ ≤ I_val + ε / 4 + 2 * (3 * (ε / 20)) := by
        dsimp only [η₂, η₃]
        have : (1 + η₁) * (2 * (ε / 20) + ε / 20) ≤ 2 * (3 * (ε / 20)) := by nlinarith
        linarith
    _ ≤ I_val + ε := by linarith

/-! ## Section 4: Triple-Prime Set Cardinality Upper Bound (`chenM_card_upper`) -/

/-- Exact inner FTC integral for Chen's triple-prime set:
for all `u ∈ [1/8, 1/3]`, `∫_{1/3}^{(1-u)/2} 1 / (v * (1 - u - v)) dv = log(2 - 3u) / (1 - u)`. -/
private lemma integral_chen_inner {u : ℝ} (hu_lo : (1 / 8 : ℝ) ≤ u) (hu_hi : u ≤ 1 / 3) :
    ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (v * (1 - u - v)) =
      Real.log (2 - 3 * u) / (1 - u) := by
  have hle : (1 / 3 : ℝ) ≤ (1 - u) / 2 := by linarith
  have h1u_pos : 0 < 1 - u := by linarith
  have hcont : ContinuousOn (fun v : ℝ => 1 / (v * (1 - u - v))) (Set.uIcc (1 / 3 : ℝ) ((1 - u) / 2)) := by
    rw [Set.uIcc_of_le hle]
    refine continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_
    intro v hv
    have hv1 : 0 < v := by linarith [hv.1]
    have hv2 : 0 < 1 - u - v := by linarith [hv.2]
    exact (mul_pos hv1 hv2).ne'
  have hderiv : ∀ v ∈ Set.uIcc (1 / 3 : ℝ) ((1 - u) / 2),
      HasDerivAt (fun x : ℝ => (Real.log x - Real.log (1 - u - x)) / (1 - u))
        (1 / (v * (1 - u - v))) v := by
    intro v hv
    rw [Set.uIcc_of_le hle] at hv
    have hv1 : 0 < v := by linarith [hv.1]
    have hv2 : 0 < 1 - u - v := by linarith [hv.2]
    have hd1 : HasDerivAt Real.log v⁻¹ v := Real.hasDerivAt_log hv1.ne'
    have hd_sub : HasDerivAt (fun x : ℝ => 1 - u - x) (-1) v := by
      simpa using (hasDerivAt_const v (1 - u)).fun_sub (hasDerivAt_id v)
    have hd2 : HasDerivAt (fun x : ℝ => Real.log (1 - u - x)) ((-1) / (1 - u - v)) v := by
      have hcomp := (Real.hasDerivAt_log hv2.ne').comp v hd_sub
      refine hcomp.congr_deriv ?_
      ring
    have hd3 := (hd1.sub hd2).div_const (1 - u)
    refine hd3.congr_deriv ?_
    field_simp [hv1.ne', hv2.ne', h1u_pos.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have htop : (Real.log ((1 - u) / 2) - Real.log (1 - u - (1 - u) / 2)) / (1 - u) = 0 := by
    have : 1 - u - (1 - u) / 2 = (1 - u) / 2 := by ring
    rw [this, sub_self, zero_div]
  have hbot : (Real.log (1 / 3 : ℝ) - Real.log (1 - u - 1 / 3)) / (1 - u) =
      -Real.log (2 - 3 * u) / (1 - u) := by
    have hpos : 0 < 2 - 3 * u := by linarith
    have heq : 1 - u - 1 / 3 = (2 - 3 * u) * (1 / 3 : ℝ) := by ring
    rw [heq, Real.log_mul hpos.ne' (by norm_num)]
    ring
  rw [htop, hbot]
  ring

/-- **Triple-Prime Set Cardinality Upper Bound (`chenM_card_upper`)**:
for every `ε > 0`, there exists `N₀ : ℕ` such that for all `N ≥ N₀`:
`((chenM N).card : ℝ) ≤ (chenIB + ε) * ((N : ℝ) / Real.log (N : ℝ))`. -/
theorem chenM_card_upper :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((chenM N).card : ℝ) ≤ (chenIB + ε) * ((N : ℝ) / Real.log (N : ℝ)) := by
  intro ε hε
  obtain ⟨C_M, hCM, hmertens⟩ := sum_primes_rpow_inv_le
  -- Outer integrand `h_outer u = log(2 - 3 u) / (1 - u)` on `[1/8, 1/3]`
  set h_outer : ℝ → ℝ := fun u => Real.log (2 - 3 * u) / (1 - u)
  have hh_cont : ContinuousOn h_outer (Set.Icc (1 / 8 : ℝ) (1 / 3 : ℝ)) := by
    refine (Real.continuousOn_log.comp (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      fun u hu => (by linarith [hu.2] : 2 - 3 * u ≠ 0)).div
      (continuousOn_const.sub continuousOn_id) fun u hu => (by linarith [hu.2] : 1 - u ≠ 0)
  have hh_nn : ∀ u ∈ Set.Icc (1 / 8 : ℝ) (1 / 3 : ℝ), 0 ≤ h_outer u := fun u hu =>
    div_nonneg (Real.log_nonneg (by linarith [hu.2])) (by linarith [hu.2])
  have hIB_nn : 0 ≤ chenIB := by
    unfold chenIB
    refine intervalIntegral.integral_nonneg (by norm_num) fun u hu => ?_
    exact div_nonneg (Real.log_nonneg (by linarith [hu.2])) (mul_nonneg (by linarith [hu.1]) (by linarith [hu.2]))
  -- Choose `δ` for PNT upper bound on `π(N / (q₁ * q₂))` and `η` for Riemann discretization
  set δ : ℝ := min 1 (ε / (4 * (chenIB + 1)))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ_le1 : δ ≤ 1 := min_le_left _ _
  obtain ⟨X_δ, hXδ4, hpi_asymp⟩ := primeCount_asymp δ hδ_pos
  set η : ℝ := ε / (16 * (1 + δ))
  have hη_pos : 0 < η := by positivity
  -- Uniform continuity of `h_outer` on compact `[1/8, 1/3]`
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hh_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨ρ, hρ_pos, hρ⟩ := huc (η / 2) (by positivity)
  -- Uniform partition of `[1/8, 1/3]` into `M₁` bins of width `h₁ < min (1/12) (min ρ (η / 32))`
  set step_cap : ℝ := min (1 / 12 : ℝ) (min ρ (η / 32))
  have hcap_pos : 0 < step_cap := lt_min (by norm_num) (lt_min hρ_pos (by positivity))
  set M₁ : ℕ := ⌈((1 / 3 : ℝ) - 1 / 8) / step_cap⌉₊ + 1
  have hM1_pos : 0 < M₁ := Nat.succ_pos _
  have hM1R_pos : (0 : ℝ) < (M₁ : ℝ) := Nat.cast_pos.mpr hM1_pos
  set h₁ : ℝ := ((1 / 3 : ℝ) - 1 / 8) / (M₁ : ℝ)
  have hh1_pos : 0 < h₁ := div_pos (by norm_num) hM1R_pos
  have hh1_lt_cap : h₁ < step_cap := by
    dsimp only [h₁]
    rw [div_lt_iff₀ hM1R_pos]
    have h1 : ((1 / 3 : ℝ) - 1 / 8) / step_cap < (M₁ : ℝ) := by
      have : ((1 / 3 : ℝ) - 1 / 8) / step_cap ≤ (⌈((1 / 3 : ℝ) - 1 / 8) / step_cap⌉₊ : ℝ) := Nat.le_ceil _
      dsimp only [M₁]; push_cast; linarith
    have := (div_lt_iff₀ hcap_pos).mp h1
    linarith
  have hh1_lt_tw : h₁ < 1 / 12 := lt_of_lt_of_le hh1_lt_cap (min_le_left _ _)
  have hh1_lt_ρ : h₁ < ρ := lt_of_lt_of_le hh1_lt_cap ((min_le_right _ _).trans (min_le_left _ _))
  have hh1_lt_η : h₁ < η / 32 := lt_of_lt_of_le hh1_lt_cap ((min_le_right _ _).trans (min_le_right _ _))
  set u : ℕ → ℝ := fun i => (1 / 8 : ℝ) + (i : ℝ) * h₁
  have hu0 : u 0 = 1 / 8 := by simp [u]
  have huM1 : u M₁ = 1 / 3 := by
    dsimp only [u, h₁]; field_simp [hM1R_pos.ne']; ring
  have hu_step : ∀ i : ℕ, u (i + 1) - u i = h₁ := fun i => by
    dsimp only [u]; push_cast; ring
  have hu_mem : ∀ i : ℕ, i ≤ M₁ → u i ∈ Set.Icc (1 / 8 : ℝ) (1 / 3 : ℝ) := fun i hi => by
    have hiR : (i : ℝ) ≤ (M₁ : ℝ) := Nat.cast_le.mpr hi
    constructor
    · dsimp only [u]; nlinarith [Nat.cast_nonneg (α := ℝ) i]
    · have : (i : ℝ) * h₁ ≤ (M₁ : ℝ) * h₁ := mul_le_mul_of_nonneg_right hiR hh1_pos.le
      have hMh : (M₁ : ℝ) * h₁ = 1 / 3 - 1 / 8 := mul_div_cancel₀ _ hM1R_pos.ne'
      dsimp only [u]; linarith
  -- For each `i < M₁`, apply `sum_primes_Ico_rpow_le_integral` on `[1/3, (1 - u i) / 2]`
  have hinner_all : ∀ i : ℕ, i < M₁ →
      ∃ N_i : ℕ, 2 ≤ N_i ∧ ∀ N : ℕ, N_i ≤ N →
        ∑ q₂ ∈ (Finset.range N).filter (fun q : ℕ => q.Prime ∧
            (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 - u i) / 2)),
          (1 / (1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ))) / (q₂ : ℝ) ≤
          h_outer (u i) + 3 * η / 4 := by
    intro i hi
    have hui_mem := hu_mem i (by omega)
    have hui1_mem := hu_mem (i + 1) (by omega)
    have hui_lt : u i < 1 / 3 := by
      have : u i < u (i + 1) := by linarith [hu_step i]
      linarith [hui1_mem.2]
    have hhi_gt : (1 / 3 : ℝ) < (1 - u i) / 2 := by linarith
    have hhi_le1 : (1 - u i) / 2 ≤ 1 := by linarith [hui_mem.1]
    have hdenom_pos : ∀ v ∈ Set.Icc (1 / 3 : ℝ) ((1 - u i) / 2), 1 / 4 ≤ 1 - u (i + 1) - v := by
      intro v hv
      linarith [hv.2, hu_step i, hui_mem.2, hh1_lt_tw]
    have hg_cont : ContinuousOn (fun v : ℝ => 1 / (1 - u (i + 1) - v))
        (Set.Icc (1 / 3 : ℝ) ((1 - u i) / 2)) :=
      continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun v hv =>
        (by linarith [hdenom_pos v hv] : 1 - u (i + 1) - v ≠ 0)
    have hg_nn : ∀ v ∈ Set.Icc (1 / 3 : ℝ) ((1 - u i) / 2), 0 ≤ 1 / (1 - u (i + 1) - v) :=
      fun v hv => div_nonneg zero_le_one (by linarith [hdenom_pos v hv])
    obtain ⟨N_i, hNi2, hriem_i⟩ := sum_primes_Ico_rpow_le_integral
      (by norm_num) hhi_gt hhi_le1 hg_cont hg_nn (η / 4) (by positivity)
    refine ⟨N_i, hNi2, fun N hN => (hriem_i N hN).trans ?_⟩
    -- Compare `∫_{1/3}^{(1 - u i)/2} 1 / (v * (1 - u (i+1) - v))` to `h_outer (u i)`
    have hint1 : IntervalIntegrable (fun v : ℝ => (1 / (1 - u (i + 1) - v)) / v)
        volume (1 / 3 : ℝ) ((1 - u i) / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hhi_gt.le]
      exact hg_cont.div continuousOn_id fun v hv => (by linarith [hv.1] : v ≠ 0)
    have hint2 : IntervalIntegrable (fun v : ℝ => 1 / (v * (1 - u i - v)))
        volume (1 / 3 : ℝ) ((1 - u i) / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hhi_gt.le]
      refine continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_
      intro v hv
      exact (mul_pos (by linarith [hv.1]) (by linarith [hv.2, hui_mem.2])).ne'
    have hint3 : IntervalIntegrable (fun v : ℝ => 16 * h₁ * v⁻¹)
        volume (1 / 3 : ℝ) ((1 - u i) / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hhi_gt.le]
      exact continuousOn_const.mul (continuousOn_id.inv₀ fun v hv => (by linarith [hv.1] : v ≠ 0))
    have hcmp :
        ∫ v in (1 / 3 : ℝ)..((1 - u i) / 2), (1 / (1 - u (i + 1) - v)) / v ≤
          (∫ v in (1 / 3 : ℝ)..((1 - u i) / 2), 1 / (v * (1 - u i - v))) +
          (∫ v in (1 / 3 : ℝ)..((1 - u i) / 2), 16 * h₁ * v⁻¹) := by
      rw [← intervalIntegral.integral_add hint2 hint3]
      refine intervalIntegral.integral_mono_on hhi_gt.le hint1 (hint2.add hint3) fun v hv => ?_
      have hv_pos : 0 < v := by linarith [hv.1]
      have hd1 : 1 / 4 ≤ 1 - u (i + 1) - v := hdenom_pos v hv
      have hd2 : 1 / 4 ≤ 1 - u i - v := by linarith [hu_step i]
      have hdiff : 1 / (1 - u (i + 1) - v) - 1 / (1 - u i - v) ≤ 16 * h₁ := by
        have heq : 1 / (1 - u (i + 1) - v) - 1 / (1 - u i - v) =
            h₁ / ((1 - u (i + 1) - v) * (1 - u i - v)) := by
          have hs := hu_step i
          field_simp [(by linarith : 1 - u (i + 1) - v ≠ 0), (by linarith : 1 - u i - v ≠ 0)]
          linarith
        rw [heq]
        have hprod_ge : (1 / 16 : ℝ) ≤ (1 - u (i + 1) - v) * (1 - u i - v) := by nlinarith
        calc h₁ / ((1 - u (i + 1) - v) * (1 - u i - v))
            ≤ h₁ / (1 / 16) := div_le_div_of_nonneg_left hh1_pos.le (by norm_num) hprod_ge
          _ = 16 * h₁ := by ring
      have heq1 : (1 / (1 - u (i + 1) - v)) / v = (1 / (1 - u (i + 1) - v)) * v⁻¹ := div_eq_mul_inv _ _
      have heq2 : 1 / (v * (1 - u i - v)) + 16 * h₁ * v⁻¹ = (1 / (1 - u i - v) + 16 * h₁) * v⁻¹ := by
        field_simp [hv_pos.ne', (by linarith : 1 - u i - v ≠ 0)]
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hv_pos.le)
    have hval3 : ∫ v in (1 / 3 : ℝ)..((1 - u i) / 2), 16 * h₁ * v⁻¹ ≤ 16 * h₁ := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 3) (by linarith)]
      have hlog_le1 : Real.log (((1 - u i) / 2) / (1 / 3 : ℝ)) ≤ 1 := by
        have h1 := Real.log_le_sub_one_of_pos
          (div_pos (show 0 < (1 - u i) / 2 by linarith) (by norm_num : (0 : ℝ) < 1 / 3))
        have h2 : ((1 - u i) / 2) / (1 / 3 : ℝ) ≤ 2 := by linarith [hui_mem.1]
        linarith
      nlinarith
    have hinner_eq := integral_chen_inner hui_mem.1 hui_mem.2
    have h16h : 16 * h₁ ≤ η / 2 := by linarith
    dsimp only [h_outer]
    linarith
  -- Choose uniform `N_inner` across all `i < M₁`
  choose N_bin hN_bin using hinner_all
  set N_inner : ℕ := (Finset.range M₁).sup (fun i => if h : i < M₁ then N_bin i h else 0)
  -- Outer error constant `G_out = ∑_{i < M₁} (h_outer (u i) + 3 * η / 4)`
  set G_out : ℝ := ∑ i ∈ Finset.range M₁, (h_outer (u i) + 3 * η / 4)
  have hG_pos : 0 < G_out := by
    refine Finset.sum_pos (fun i hi => ?_) ⟨0, Finset.mem_range.mpr hM1_pos⟩
    linarith [hh_nn (u i) (hu_mem i (by have := Finset.mem_range.mp hi; omega))]
  -- Choose `N₀` large enough for all requirements simultaneously
  set R_pow1 : ℝ := (max 2 (2 * G_out / η)) ^ (8 : ℝ)
  set R_pow2 : ℝ := X_δ ^ (3 : ℝ)
  set R_log : ℝ := Real.exp (32 * C_M * G_out / η)
  set N₀ : ℕ := max (max N_inner 16) (max (max ⌈R_pow1⌉₊ ⌈R_pow2⌉₊) ⌈R_log⌉₊)
  refine ⟨N₀, fun N hN => ?_⟩
  have hN_inner : N_inner ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN16 : 16 ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN_pow1 : R_pow1 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hN)
  have hN_pow2 : R_pow2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hN)
  have hN_log : R_log ≤ (N : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hN)
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hLN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hN18_ge : max 2 (2 * G_out / η) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hN_pow1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [← Real.rpow_mul (by positivity)] at h1
    norm_num at h1
    exact max_le h1.1 h1.2
  have hN18_ge2 : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := (le_max_left _ _).trans hN18_ge
  have hN13_ge_Xd : X_δ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hN_pow2 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_mul (by linarith)] at h1
    norm_num at h1
    exact h1
  -- Define bins `Q1_bin i` and `Q2_set i`
  set Q1_bin : ℕ → Finset ℕ := fun i =>
    (Finset.range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ (u i) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ (u (i + 1)))
  set Q2_set : ℕ → Finset ℕ := fun i =>
    (Finset.range N).filter (fun q : ℕ => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 - u i) / 2))
  -- Step 1: Bound `(chenM N).card` by summing over `i < M₁`, `q₁ ∈ Q1_bin i`, `q₂ ∈ Q2_set i`
  have hcard_le_bins :
      ((chenM N).card : ℝ) ≤
        ∑ i ∈ Finset.range M₁,
          ∑ q₁ ∈ Q1_bin i,
            ∑ q₂ ∈ Q2_set i,
              (((chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card : ℝ) := by
    have hsub : chenM N ⊆
        (Finset.range M₁).biUnion fun i =>
          (Q1_bin i).biUnion fun q₁ =>
            (Q2_set i).biUnion fun q₂ =>
              (chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂) := by
      intro t ht
      have ht' := ht
      unfold chenM at ht
      simp only [Finset.mem_filter] at ht
      obtain ⟨_, hq1p, hq2p, hq3p, _, _, _, hq1_lo, hq1_hi, hq2_lo, hq23, hprod⟩ := ht
      have hq1N : t.1 < N := by
        have h1 : t.1 ≤ t.1 * t.2.1 * t.2.2 :=
          (Nat.le_mul_of_pos_right _ hq2p.pos).trans (Nat.le_mul_of_pos_right _ hq3p.pos)
        omega
      have hq2N : t.2.1 < N := by
        have h1 : t.2.1 ≤ t.1 * t.2.1 * t.2.2 :=
          (Nat.le_mul_of_pos_left _ hq1p.pos).trans (Nat.le_mul_of_pos_right _ hq3p.pos)
        omega
      have hq1_pos : (0 : ℝ) < (t.1 : ℝ) := Nat.cast_pos.mpr hq1p.pos
      have hq2_pos : (0 : ℝ) < (t.2.1 : ℝ) := Nat.cast_pos.mpr hq2p.pos
      -- Locate bin `i < M₁` for `q₁`
      have hlogq1_lo : (1 / 8 : ℝ) ≤ Real.log (t.1 : ℝ) / Real.log (N : ℝ) := by
        rw [le_div_iff₀ hLN_pos]
        have := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hq1_lo
        rwa [Real.log_rpow hN0] at this
      have hlogq1_hi : Real.log (t.1 : ℝ) / Real.log (N : ℝ) < 1 / 3 := by
        rw [div_lt_iff₀ hLN_pos]
        have := Real.log_lt_log hq1_pos hq1_hi
        rwa [Real.log_rpow hN0] at this
      set s : ℝ := (Real.log (t.1 : ℝ) / Real.log (N : ℝ) - 1 / 8) / h₁
      have hs_nn : 0 ≤ s := div_nonneg (by linarith) hh1_pos.le
      have hs_lt : s < (M₁ : ℝ) := by
        dsimp only [s, h₁]
        rw [div_lt_iff₀ (div_pos (by norm_num) hM1R_pos)]
        have hMh : (M₁ : ℝ) * (((1 / 3 : ℝ) - 1 / 8) / (M₁ : ℝ)) = 1 / 3 - 1 / 8 :=
          mul_div_cancel₀ _ hM1R_pos.ne'
        linarith
      set i : ℕ := ⌊s⌋₊
      have hiM1 : i < M₁ := by exact_mod_cast ((Nat.floor_le hs_nn).trans_lt hs_lt)
      have hui_lo : u i ≤ Real.log (t.1 : ℝ) / Real.log (N : ℝ) := by
        have := (le_div_iff₀ hh1_pos).mp (Nat.floor_le hs_nn)
        dsimp only [u]; linarith
      have hui_hi : Real.log (t.1 : ℝ) / Real.log (N : ℝ) < u (i + 1) := by
        have := (div_lt_iff₀ hh1_pos).mp (Nat.lt_floor_add_one s)
        dsimp only [u]; push_cast; linarith
      have hq1_bin : t.1 ∈ Q1_bin i := by
        simp only [Q1_bin, Finset.mem_filter, Finset.mem_range]
        refine ⟨hq1N, hq1p, ?_, ?_⟩
        · rw [Real.rpow_def_of_pos hN0]
          exact (Real.exp_le_exp.mpr (by linarith [(le_div_iff₀ hLN_pos).mp hui_lo])).trans_eq (Real.exp_log hq1_pos)
        · rw [Real.rpow_def_of_pos hN0]
          exact (Real.exp_log hq1_pos).symm.trans_lt (Real.exp_lt_exp.mpr (by linarith [(div_lt_iff₀ hLN_pos).mp hui_hi]))
      have hq2_bin : t.2.1 ∈ Q2_set i := by
        simp only [Q2_set, Finset.mem_filter, Finset.mem_range]
        refine ⟨hq2N, hq2p, hq2_lo, ?_⟩
        -- Since `q₁ * q₂² ≤ q₁ * q₂ * q₃ < N` and `q₁ ≥ N^{u i}`, we have `q₂ < N^{(1 - u i)/2}`!
        have hq1q2sq : (t.1 : ℝ) * (t.2.1 : ℝ) ^ 2 < (N : ℝ) := by
          have hnat : t.1 * (t.2.1 * t.2.1) < N := by
            have : t.1 * (t.2.1 * t.2.1) ≤ t.1 * t.2.1 * t.2.2 := by
              rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hq23)
            omega
          have hR : ((t.1 * (t.2.1 * t.2.1) : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hnat
          push_cast at hR; linarith
        have hq1_ge_ui : (N : ℝ) ^ (u i) ≤ (t.1 : ℝ) := (Finset.mem_filter.mp hq1_bin).2.2.1
        have hq2sq_lt : (t.2.1 : ℝ) ^ 2 < (N : ℝ) ^ (1 - u i) := by
          have h1 : (N : ℝ) ^ (u i) * (t.2.1 : ℝ) ^ 2 < (N : ℝ) :=
            (mul_le_mul_of_nonneg_right hq1_ge_ui (sq_nonneg _)).trans_lt hq1q2sq
          rw [Real.rpow_sub hN0, Real.rpow_one, lt_div_iff₀ (Real.rpow_pos_of_pos hN0 _)]
          linarith
        have hsq := Real.sqrt_lt_sqrt (sq_nonneg _) hq2sq_lt
        rw [Real.sqrt_sq hq2_pos.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le] at hsq
        simpa [div_eq_mul_inv] using hsq
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hiM1,
        Finset.mem_biUnion.mpr ⟨t.1, hq1_bin,
          Finset.mem_biUnion.mpr ⟨t.2.1, hq2_bin,
            Finset.mem_filter.mpr ⟨ht', rfl, rfl⟩⟩⟩⟩
    have hcard_nat : (chenM N).card ≤
        ∑ i ∈ Finset.range M₁,
          ∑ q₁ ∈ Q1_bin i,
            ∑ q₂ ∈ Q2_set i,
              ((chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card := by
      calc (chenM N).card
          ≤ ((Finset.range M₁).biUnion fun i =>
              (Q1_bin i).biUnion fun q₁ =>
                (Q2_set i).biUnion fun q₂ =>
                  (chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card := Finset.card_le_card hsub
        _ ≤ ∑ i ∈ Finset.range M₁,
              ((Q1_bin i).biUnion fun q₁ =>
                (Q2_set i).biUnion fun q₂ =>
                  (chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card := Finset.card_biUnion_le
        _ ≤ ∑ i ∈ Finset.range M₁, ∑ q₁ ∈ Q1_bin i,
              ((Q2_set i).biUnion fun q₂ =>
                (chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
        _ ≤ _ := Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
    exact_mod_cast hcard_nat
  -- Step 2: For each `i < M₁`, `q₁ ∈ Q1_bin i`, `q₂ ∈ Q2_set i`, bound the fiber card over `q₃`!
  have hfiber_bd : ∀ i ∈ Finset.range M₁, ∀ q₁ ∈ Q1_bin i, ∀ q₂ ∈ Q2_set i,
      (((chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card : ℝ) ≤
        (1 + δ) * ((N : ℝ) / Real.log (N : ℝ)) * (q₁ : ℝ)⁻¹ *
          ((1 / (1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ))) / (q₂ : ℝ)) := by
    intro i hi q₁ hq₁ q₂ hq₂
    have hiM1 : i < M₁ := Finset.mem_range.mp hi
    have hui_mem := hu_mem i (by omega)
    have hui1_mem := hu_mem (i + 1) (by omega)
    simp only [Q1_bin, Q2_set, Finset.mem_filter] at hq₁ hq₂
    have hq1_pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr hq₁.2.1.pos
    have hq2_pos : (0 : ℝ) < (q₂ : ℝ) := Nat.cast_pos.mpr hq₂.2.1.pos
    have hlogq1_hi : Real.log (q₁ : ℝ) / Real.log (N : ℝ) ≤ u (i + 1) := by
      rw [div_le_iff₀ hLN_pos]
      have := Real.log_le_log hq1_pos hq₁.2.2.2.le
      rwa [Real.log_rpow hN0] at this
    have hlogq2_hi : Real.log (q₂ : ℝ) / Real.log (N : ℝ) ≤ (1 - u i) / 2 := by
      rw [div_le_iff₀ hLN_pos]
      have := Real.log_le_log hq2_pos hq₂.2.2.2.le
      rwa [Real.log_rpow hN0] at this
    have hdenom_pos : 0 < 1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ) := by
      linarith [hu_step i, hui_mem.2, hh1_lt_tw]
    by_cases hemp : ((chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card = 0
    · rw [hemp, Nat.cast_zero]; positivity
    -- Nonempty fiber: there exists `t = (q₁, q₂, q₃) ∈ chenM N`, so `N / (q₁ * q₂) > q₃ ≥ q₂ ≥ N^{1/3} ≥ X_δ`!
    obtain ⟨t₀, ht₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hemp)
    simp only [Finset.mem_filter] at ht₀
    have ht0_mem := ht₀.1
    unfold chenM at ht0_mem
    simp only [Finset.mem_filter] at ht0_mem
    obtain ⟨_, _, _, _, _, _, _, _, _, _, ht0_23, ht0_prod⟩ := ht0_mem
    have hquot_ge_Xd : X_δ ≤ (N : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
      have hprod_lt : (q₁ : ℝ) * (q₂ : ℝ) * (t₀.2.2 : ℝ) < (N : ℝ) := by
        have hnat : q₁ * q₂ * t₀.2.2 < N := by rw [← ht₀.2.1, ← ht₀.2.2]; exact ht0_prod
        exact_mod_cast hnat
      have hq2_le_q3 : (q₂ : ℝ) ≤ (t₀.2.2 : ℝ) := by
        rw [← ht₀.2.2]; exact_mod_cast ht0_23
      have hq2_lt_quot : (q₂ : ℝ) < (N : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
        rw [lt_div_iff₀ (mul_pos hq1_pos hq2_pos)]
        nlinarith [mul_pos hq1_pos hq2_pos]
      exact (hN13_ge_Xd.trans hq₂.2.2.1).trans hq2_lt_quot.le
    -- Inject fiber into `primeCount (N / (q₁ * q₂))` via `t ↦ t.2.2`
    have hcard_le_pi : ((chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card ≤
        primeCount ((N : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ))) := by
      unfold primeCount
      refine Finset.card_le_card_of_injOn (fun t => t.2.2) ?_ ?_
      · intro t ht
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht
        have htm := ht.1
        unfold chenM at htm
        simp only [Finset.mem_filter] at htm
        obtain ⟨_, _, _, hq3p, _, _, _, _, _, _, _, ht_prod⟩ := htm
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range]
        refine ⟨Nat.lt_succ_iff.mpr (Nat.le_floor ?_), hq3p⟩
        rw [le_div_iff₀ (mul_pos hq1_pos hq2_pos)]
        have hnat : q₁ * q₂ * t.2.2 < N := by rw [← ht.2.1, ← ht.2.2]; exact ht_prod
        have hR : ((q₁ * q₂ * t.2.2 : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hnat
        push_cast at hR; linarith
      · intro t₁ ht₁ t₂ ht₂ heq
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht₁ ht₂
        exact Prod.ext (ht₁.2.1.trans ht₂.2.1.symm) (Prod.ext (ht₁.2.2.trans ht₂.2.2.symm) heq)
    -- Apply PNT upper bound at `x = N / (q₁ * q₂) ≥ X_δ`
    set x : ℝ := (N : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ))
    have hx4 : 4 ≤ x := hXδ4.trans hquot_ge_Xd
    have hx0 : 0 < x := by linarith
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hpi_le : (primeCount x : ℝ) ≤ (1 + δ) * (x / Real.log x) := by
      have h1 := (abs_le.mp (hpi_asymp x hquot_ge_Xd)).2
      have h2 : (primeCount x : ℝ) / (x / Real.log x) ≤ 1 + δ := by linarith
      exact (div_le_iff₀ (div_pos hx0 hLx_pos)).mp h2
    -- Lower bound `Real.log x ≥ (1 - u (i + 1) - log q₂ / log N) * log N`
    have hLx_ge : (1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) ≤ Real.log x := by
      dsimp only [x]
      rw [Real.log_div hN0.ne' (mul_pos hq1_pos hq2_pos).ne', Real.log_mul hq1_pos.ne' hq2_pos.ne']
      have h1 : Real.log (q₁ : ℝ) ≤ u (i + 1) * Real.log (N : ℝ) := (div_le_iff₀ hLN_pos).mp hlogq1_hi
      have h2 : (1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) =
          Real.log (N : ℝ) - u (i + 1) * Real.log (N : ℝ) - Real.log (q₂ : ℝ) := by
        field_simp [hLN_pos.ne']
      linarith
    calc (((chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card : ℝ)
        ≤ (primeCount x : ℝ) := Nat.cast_le.mpr hcard_le_pi
      _ ≤ (1 + δ) * (x / Real.log x) := hpi_le
      _ ≤ (1 + δ) * (x / ((1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hx0.le (mul_pos hdenom_pos hLN_pos) hLx_ge) (by linarith)
      _ = (1 + δ) * ((N : ℝ) / Real.log (N : ℝ)) * (q₁ : ℝ)⁻¹ *
            ((1 / (1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ))) / (q₂ : ℝ)) := by
          dsimp only [x]; field_simp [hN0.ne', hLN_pos.ne', hq1_pos.ne', hq2_pos.ne', hdenom_pos.ne']
  -- Step 3: Sum over `q₂`, `q₁`, and `i < M₁`!
  have hsum_step :
      ((chenM N).card : ℝ) ≤
        (1 + δ) * ((N : ℝ) / Real.log (N : ℝ)) *
          ∑ i ∈ Finset.range M₁,
            (∑ q₁ ∈ Q1_bin i, (q₁ : ℝ)⁻¹) * (h_outer (u i) + 3 * η / 4) := by
    refine hcard_le_bins.trans ?_
    calc ∑ i ∈ Finset.range M₁, ∑ q₁ ∈ Q1_bin i, ∑ q₂ ∈ Q2_set i,
            (((chenM N).filter (fun t => t.1 = q₁ ∧ t.2.1 = q₂)).card : ℝ)
        ≤ ∑ i ∈ Finset.range M₁, ∑ q₁ ∈ Q1_bin i, ∑ q₂ ∈ Q2_set i,
            (1 + δ) * ((N : ℝ) / Real.log (N : ℝ)) * (q₁ : ℝ)⁻¹ *
              ((1 / (1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ))) / (q₂ : ℝ)) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun q₁ hq₁ =>
            Finset.sum_le_sum fun q₂ hq₂ => hfiber_bd i hi q₁ hq₁ q₂ hq₂
      _ = (1 + δ) * ((N : ℝ) / Real.log (N : ℝ)) *
            ∑ i ∈ Finset.range M₁, (∑ q₁ ∈ Q1_bin i, (q₁ : ℝ)⁻¹) *
              ∑ q₂ ∈ Q2_set i,
                (1 / (1 - u (i + 1) - Real.log (q₂ : ℝ) / Real.log (N : ℝ))) / (q₂ : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q₁ _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q₂ _ => by ring
      _ ≤ (1 + δ) * ((N : ℝ) / Real.log (N : ℝ)) *
            ∑ i ∈ Finset.range M₁, (∑ q₁ ∈ Q1_bin i, (q₁ : ℝ)⁻¹) * (h_outer (u i) + 3 * η / 4) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
          have hiM1 : i < M₁ := Finset.mem_range.mp hi
          have hNi_le : N_bin i hiM1 ≤ N := by
            have hle_sup : (if h : i < M₁ then N_bin i h else 0) ≤ N_inner :=
              Finset.le_sup (f := fun j => if h : j < M₁ then N_bin j h else 0) hi
            rw [dif_pos hiM1] at hle_sup
            exact hle_sup.trans hN_inner
          exact mul_le_mul_of_nonneg_left ((hN_bin i hiM1).2 N hNi_le)
            (Finset.sum_nonneg fun _ _ => by positivity)
  -- Step 4: Bound the outer sum over `i < M₁` by `chenIB + 4 * η`!
  have houter_bin : ∀ i ∈ Finset.range M₁,
      (∑ q₁ ∈ Q1_bin i, (q₁ : ℝ)⁻¹) * (h_outer (u i) + 3 * η / 4) ≤
        (∫ t in (u i)..(u (i + 1)), h_outer t / t) +
        (5 * η / 4) * Real.log (u (i + 1) / u i) +
        (h_outer (u i) + 3 * η / 4) * ((16 * C_M) / Real.log (N : ℝ) + ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹) := by
    intro i hi
    have hiM1 : i < M₁ := Finset.mem_range.mp hi
    have hui_mem := hu_mem i (by omega)
    have hui1_mem := hu_mem (i + 1) (by omega)
    have hui_pos : 0 < u i := by linarith [hui_mem.1]
    have hui_le1 : u i ≤ u (i + 1) := by linarith [hu_step i]
    have hui1_pos : 0 < u (i + 1) := hui_pos.trans_le hui_le1
    have hcoeff_nn : 0 ≤ h_outer (u i) + 3 * η / 4 := by linarith [hh_nn (u i) hui_mem]
    have hNui2 : 2 ≤ (N : ℝ) ^ (u i) := hN18_ge2.trans (Real.rpow_le_rpow_of_exponent_le hN1.le hui_mem.1)
    have hm_i := hmertens N hN2 (u i) (u (i + 1)) hui_pos hui_le1 hNui2
    have hm_i' : ∑ q₁ ∈ Q1_bin i, (q₁ : ℝ)⁻¹ ≤
        Real.log (u (i + 1) / u i) + (16 * C_M) / Real.log (N : ℝ) + ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹ := by
      have h1 : 2 * C_M / u i ≤ 16 * C_M := by
        calc 2 * C_M / u i ≤ 2 * C_M / (1 / 8) :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) hui_mem.1
          _ = 16 * C_M := by ring
      have h2 : (2 * C_M / u i) / Real.log (N : ℝ) ≤ (16 * C_M) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right h1 hLN_pos.le
      have h3 : ((N : ℝ) ^ (u i))⁻¹ ≤ ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹ :=
        inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hN1.le hui_mem.1)
      linarith
    have hint_inv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (u i) (u (i + 1)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hui_le1]
      exact continuousOn_id.inv₀ fun t ht => (hui_pos.trans_le ht.1).ne'
    have hint_h : IntervalIntegrable (fun t : ℝ => h_outer t / t) volume (u i) (u (i + 1)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hui_le1]
      refine (hh_cont.mono fun t ht => ⟨hui_mem.1.trans ht.1, ht.2.trans hui1_mem.2⟩).div
        continuousOn_id fun t ht => (hui_pos.trans_le ht.1).ne'
    have hlog_eq : Real.log (u (i + 1) / u i) = ∫ t in (u i)..(u (i + 1)), t⁻¹ :=
      (integral_inv_of_pos hui_pos hui1_pos).symm
    have hint_cmp :
        (h_outer (u i) + 3 * η / 4) * Real.log (u (i + 1) / u i) ≤
          (∫ t in (u i)..(u (i + 1)), h_outer t / t) + (5 * η / 4) * Real.log (u (i + 1) / u i) := by
      rw [hlog_eq, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add hint_h (hint_inv.const_mul (5 * η / 4))]
      refine intervalIntegral.integral_mono_on hui_le1 (hint_inv.const_mul _)
        (hint_h.add (hint_inv.const_mul _)) fun t ht => ?_
      have ht_pos : 0 < t := hui_pos.trans_le ht.1
      have hdist : dist (u i) t < ρ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2, hu_step i]
      have hclose := hρ _ hui_mem _ ⟨hui_mem.1.trans ht.1, ht.2.trans hui1_mem.2⟩ hdist
      rw [Real.dist_eq] at hclose
      have hgle : h_outer (u i) ≤ h_outer t + η / 2 := by linarith [(abs_le.mp hclose.le).2]
      have heq : h_outer t / t + (5 * η / 4) * t⁻¹ = (h_outer t + 5 * η / 4) * t⁻¹ := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr ht_pos.le)
    calc (∑ q₁ ∈ Q1_bin i, (q₁ : ℝ)⁻¹) * (h_outer (u i) + 3 * η / 4)
        ≤ (Real.log (u (i + 1) / u i) + (16 * C_M) / Real.log (N : ℝ) + ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹) *
            (h_outer (u i) + 3 * η / 4) :=
          mul_le_mul_of_nonneg_right hm_i' hcoeff_nn
      _ = (h_outer (u i) + 3 * η / 4) * Real.log (u (i + 1) / u i) +
            (h_outer (u i) + 3 * η / 4) * ((16 * C_M) / Real.log (N : ℝ) + ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹) := by ring
      _ ≤ _ := by linarith
  -- Telescope integrals & logs over `i < M₁`
  have hsum_int : ∀ m : ℕ, m ≤ M₁ →
      ∑ i ∈ Finset.range m, ∫ t in (u i)..(u (i + 1)), h_outer t / t =
        ∫ t in (1 / 8 : ℝ)..(u m), h_outer t / t := by
    intro m hm
    induction m with
    | zero => simp [hu0]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      have hint1 : IntervalIntegrable (fun t : ℝ => h_outer t / t) volume (1 / 8 : ℝ) (u m) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (hu_mem m (by omega)).1]
        refine (hh_cont.mono fun t ht => ⟨ht.1, ht.2.trans (hu_mem m (by omega)).2⟩).div
          continuousOn_id fun t ht => (by linarith [ht.1] : t ≠ 0)
      have hint2 : IntervalIntegrable (fun t : ℝ => h_outer t / t) volume (u m) (u (m + 1)) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (by linarith [hu_step m] : u m ≤ u (m + 1))]
        refine (hh_cont.mono fun t ht => ⟨(hu_mem m (by omega)).1.trans ht.1,
          ht.2.trans (hu_mem (m + 1) hm).2⟩).div
          continuousOn_id fun t ht => (by linarith [(hu_mem m (by omega)).1, ht.1] : t ≠ 0)
      exact intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hsum_log : ∑ i ∈ Finset.range M₁, Real.log (u (i + 1) / u i) = Real.log ((1 / 3 : ℝ) / (1 / 8 : ℝ)) := by
    have hcongr : ∑ i ∈ Finset.range M₁, Real.log (u (i + 1) / u i) =
        ∑ i ∈ Finset.range M₁, (Real.log (u (i + 1)) - Real.log (u i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiM1 : i < M₁ := Finset.mem_range.mp hi
      exact Real.log_div (by linarith [(hu_mem (i + 1) (by omega)).1] : u (i + 1) ≠ 0)
        (by linarith [(hu_mem i (by omega)).1] : u i ≠ 0)
    rw [hcongr, Finset.sum_range_sub (fun i => Real.log (u i)) M₁, huM1, hu0,
      ← Real.log_div (by norm_num : (1 / 3 : ℝ) ≠ 0) (by norm_num : (1 / 8 : ℝ) ≠ 0)]
  have hIB_eq : ∫ t in (1 / 8 : ℝ)..(1 / 3 : ℝ), h_outer t / t = chenIB := by
    unfold chenIB; dsimp only [h_outer]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [div_div, mul_comm (1 - t) t]
  have houter_tot :
      ∑ i ∈ Finset.range M₁, (∑ q₁ ∈ Q1_bin i, (q₁ : ℝ)⁻¹) * (h_outer (u i) + 3 * η / 4) ≤
        chenIB + 4 * η := by
    have h1 := Finset.sum_le_sum houter_bin
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_int M₁ le_rfl, huM1, hIB_eq,
      ← Finset.mul_sum, hsum_log, ← Finset.sum_mul] at h1
    have hlog83 : Real.log ((1 / 3 : ℝ) / (1 / 8 : ℝ)) ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (1 / 3 : ℝ) / (1 / 8 : ℝ))
      linarith
    have hlog_err : (16 * C_M) / Real.log (N : ℝ) ≤ η / (2 * G_out) := by
      have hLN_ge : 32 * C_M * G_out / η ≤ Real.log (N : ℝ) :=
        (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hN_log)
      rw [div_le_div_iff₀ hLN_pos (by positivity)]
      have h1' := mul_le_mul_of_nonneg_left hLN_ge hη_pos.le
      have h2' : η * (32 * C_M * G_out / η) = (16 * C_M) * (2 * G_out) := by
        field_simp [hη_pos.ne']; ring
      linarith
    have hpow_err : ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹ ≤ η / (2 * G_out) := by
      have h1' : 2 * G_out / η ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := (le_max_right _ _).trans hN18_ge
      calc ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹ ≤ (2 * G_out / η)⁻¹ := inv_anti₀ (by positivity) h1'
        _ = η / (2 * G_out) := by rw [inv_div]
    have hG_err : G_out * ((16 * C_M) / Real.log (N : ℝ) + ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹) ≤ η := by
      calc G_out * ((16 * C_M) / Real.log (N : ℝ) + ((N : ℝ) ^ ((1 : ℝ) / 8))⁻¹)
          ≤ G_out * (η / (2 * G_out) + η / (2 * G_out)) :=
            mul_le_mul_of_nonneg_left (by linarith) hG_pos.le
        _ = η := by field_simp [hG_pos.ne']; ring
    have h54 : (5 * η / 4) * Real.log ((1 / 3 : ℝ) / (1 / 8 : ℝ)) ≤ 3 * η := by nlinarith
    linarith
  -- Final assembly
  have hδ_IB : δ * chenIB ≤ ε / 4 := by
    have h1 : δ ≤ ε / (4 * (chenIB + 1)) := min_le_right _ _
    calc δ * chenIB ≤ (ε / (4 * (chenIB + 1))) * (chenIB + 1) :=
          mul_le_mul h1 (by linarith) hIB_nn (by positivity)
      _ = ε / 4 := by field_simp [(by linarith : chenIB + 1 ≠ 0)]
  have hfinal_const : (1 + δ) * (chenIB + 4 * η) ≤ chenIB + ε := by
    have h4η : (1 + δ) * (4 * η) = ε / 4 := by
      dsimp only [η]; field_simp [(by linarith : 1 + δ ≠ 0)]; ring
    nlinarith
  calc ((chenM N).card : ℝ)
      ≤ (1 + δ) * ((N : ℝ) / Real.log (N : ℝ)) * (chenIB + 4 * η) :=
        hsum_step.trans (mul_le_mul_of_nonneg_left houter_tot (by positivity))
    _ = ((1 + δ) * (chenIB + 4 * η)) * ((N : ℝ) / Real.log (N : ℝ)) := by ring
    _ ≤ (chenIB + ε) * ((N : ℝ) / Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hfinal_const (by positivity)

end RHDirect.Chen


