import RHDirect.MaynardTaoTuples
import RHDirect.MaynardTaoWTrick
import RHDirect.MaynardTaoReduction
import RHDirect.Stage11BombieriVinogradov
import RHDirect.Stage10SiegelWalfiszFull
import RHDirect.Stage8MertensTheorems
import RHDirect.Stage8BarbanDavenport
import RHDirect.ChenBVPrimes
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic

/-!
# RHDirect.MaynardTaoSieve

**UNCONDITIONAL MULTIDIMENSIONAL SELBERG SIEVE FOR MAYNARD–TAO** (`0` assumptions, `0` `sorry`,
`0` custom `axiom`s, `0` `opaque`, `0` `native_decide`).

This file builds the full analytic engine of Maynard (2015), *Small gaps between primes*
(Annals of Mathematics 181, 383–413), directly on top of our verified unconditional
Bombieri–Vinogradov (`RHDirect.Chen.bombieri_vinogradov_primes` / `Stage11BombieriVinogradov`),
Siegel–Walfisz (`Stage10SiegelWalfiszFull`), and elementary multiplicative sum estimates,
and proves the master bridge `maynard_tao_sieve_core`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false

noncomputable section

open Finset MeasureTheory Set Filter Topology RHDirect
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHDirect.MaynardTao

/-! ## Section 1: Recursive Simplex Integral and Lipschitz Test Functions -/

/-- A symmetric, bounded, `ℓ¹`-Lipschitz test function on the standard `k`-simplex
`Δ_k = {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}`. -/
structure SimplexTestFn (k : ℕ) where
  F : (Fin k → ℝ) → ℝ
  bound : ℝ
  lip : ℝ
  bound_nonneg : 0 ≤ bound
  lip_nonneg : 0 ≤ lip
  abs_le : ∀ v : Fin k → ℝ, (∀ i, 0 ≤ v i) → ∑ i, v i ≤ 1 → |F v| ≤ bound
  lipschitz : ∀ u v : Fin k → ℝ,
    (∀ i, 0 ≤ u i) → ∑ i, u i ≤ 1 →
    (∀ i, 0 ≤ v i) → ∑ i, v i ≤ 1 →
    |F u - F v| ≤ lip * ∑ i, |u i - v i|
  symm : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → ℝ), F (v ∘ σ) = F v

/-- Recursive iterated 1D integral over the scaled `k`-simplex
`Δ_k(s) = {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ s}`. -/
def simplexIntegral : (k : ℕ) → ℝ → ((Fin k → ℝ) → ℝ) → ℝ
  | 0, _, G => G Fin.elim0
  | k + 1, s, G =>
      ∫ t in (0 : ℝ)..s, simplexIntegral k (s - t) (fun v => G (Fin.cons t v))

/-- The plain Maynard–Tao simplex integral `I_k(F) = ∫_{Δ_k} F(t)² dt`. -/
def maynardI (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  simplexIntegral k 1 (fun v => (F v) ^ 2)

/-- The prime-weighted Maynard–Tao simplex integral for coordinate `0`:
`J_k^{(0)}(F) = ∫_{Δ_k} (∫_0^{1 - ∑ v_i} F(t, v) dt)² dv`. -/
def maynardJ0 (k : ℕ) (F : (Fin (k + 1) → ℝ) → ℝ) : ℝ :=
  simplexIntegral k 1 (fun v => (∫ t in (0 : ℝ)..(1 - ∑ i, v i), F (Fin.cons t v)) ^ 2)

/-- Membership predicate for the scaled `k`-simplex `Δ_k(s)`. -/
def InSimplex {k : ℕ} (s : ℝ) (v : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ s

lemma inSimplex_elim0 {s : ℝ} (hs : 0 ≤ s) : InSimplex s (Fin.elim0 : Fin 0 → ℝ) :=
  ⟨fun i => i.elim0, by simpa using hs⟩

lemma inSimplex_cons {k : ℕ} {s t : ℝ} {v : Fin k → ℝ}
    (ht : 0 ≤ t) (hv : InSimplex (s - t) v) :
    InSimplex s (Fin.cons t v) := by
  refine ⟨?_, ?_⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa using ht
    · intro j; simpa using hv.1 j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    linarith [hv.2]

lemma inSimplex_mono {k : ℕ} {s₁ s₂ : ℝ} {v : Fin k → ℝ}
    (hs : s₁ ≤ s₂) (hv : InSimplex s₁ v) : InSimplex s₂ v :=
  ⟨hv.1, hv.2.trans hs⟩

/-- A function `G` is `(M, L)`-regular on `Δ_k(s)` if it is bounded by `M` and `L`-Lipschitz
in the `ℓ¹` metric on `Δ_k(s)`. -/
def IsSimplexLipOn {k : ℕ} (s M L : ℝ) (G : (Fin k → ℝ) → ℝ) : Prop :=
  0 ≤ M ∧ 0 ≤ L ∧
  (∀ v, InSimplex s v → |G v| ≤ M) ∧
  (∀ u v, InSimplex s u → InSimplex s v → |G u - G v| ≤ L * ∑ i, |u i - v i|)

lemma IsSimplexLipOn.mono {k : ℕ} {s₁ s₂ M L : ℝ} {G : (Fin k → ℝ) → ℝ}
    (hs : s₁ ≤ s₂) (hG : IsSimplexLipOn s₂ M L G) : IsSimplexLipOn s₁ M L G :=
  ⟨hG.1, hG.2.1, fun v hv => hG.2.2.1 v (inSimplex_mono hs hv),
    fun u v hu hv => hG.2.2.2 u v (inSimplex_mono hs hu) (inSimplex_mono hs hv)⟩

lemma IsSimplexLipOn.cons {k : ℕ} {s t M L : ℝ} {G : (Fin (k + 1) → ℝ) → ℝ}
    (ht0 : 0 ≤ t) (hG : IsSimplexLipOn s M L G) :
    IsSimplexLipOn (s - t) M L (fun v => G (Fin.cons t v)) := by
  refine ⟨hG.1, hG.2.1, ?_, ?_⟩
  · intro v hv
    exact hG.2.2.1 _ (inSimplex_cons ht0 hv)
  · intro u v hu hv
    have h := hG.2.2.2 _ _ (inSimplex_cons ht0 hu) (inSimplex_cons ht0 hv)
    rw [Fin.sum_univ_succ] at h
    simpa [Fin.cons_zero, Fin.cons_succ] using h

lemma SimplexTestFn.isSimplexLipOn {k : ℕ} (T : SimplexTestFn k) :
    IsSimplexLipOn 1 T.bound T.lip T.F :=
  ⟨T.bound_nonneg, T.lip_nonneg, fun v hv => T.abs_le v hv.1 hv.2,
    fun u v hu hv => T.lipschitz u v hu.1 hu.2 hv.1 hv.2⟩

lemma IsSimplexLipOn.sq {k : ℕ} {s M L : ℝ} {G : (Fin k → ℝ) → ℝ}
    (hG : IsSimplexLipOn s M L G) :
    IsSimplexLipOn s (M ^ 2) (2 * M * L) (fun v => (G v) ^ 2) := by
  obtain ⟨hM, hL, hbd, hlip⟩ := hG
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · intro v hv
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbd v hv) 2
  · intro u v hu hv
    have h1 : (G u) ^ 2 - (G v) ^ 2 = (G u + G v) * (G u - G v) := by ring
    rw [h1, abs_mul]
    have hsum : |G u + G v| ≤ 2 * M := by
      calc |G u + G v| ≤ |G u| + |G v| := abs_add_le _ _
        _ ≤ M + M := add_le_add (hbd u hu) (hbd v hv)
        _ = 2 * M := by ring
    calc |G u + G v| * |G u - G v|
        ≤ (2 * M) * (L * ∑ i, |u i - v i|) :=
          mul_le_mul hsum (hlip u v hu hv) (abs_nonneg _) (by positivity)
      _ = (2 * M * L) * ∑ i, |u i - v i| := by ring

lemma IsSimplexLipOn.innerIntegral {k : ℕ} {M L : ℝ} {G : (Fin (k + 1) → ℝ) → ℝ}
    (hG : IsSimplexLipOn 1 M L G) :
    IsSimplexLipOn 1 M (L + M)
      (fun v => ∫ t in (0 : ℝ)..(1 - ∑ i, v i), G (Fin.cons t v)) := by
  obtain ⟨hM, hL, hbd, hlip⟩ := hG
  have hcont : ∀ v : Fin k → ℝ, InSimplex 1 v →
      ContinuousOn (fun t : ℝ => G (Fin.cons t v)) (Set.Icc 0 (1 - ∑ i, v i)) := by
    intro v hv
    refine Metric.continuousOn_iff.mpr fun t ht ε hε => ?_
    refine ⟨ε / (L + 1), by positivity, fun t' ht' htt' => ?_⟩
    rw [Real.dist_eq] at htt' ⊢
    have hv_t : InSimplex 1 (Fin.cons t v) := by
      refine inSimplex_cons ht.1 ⟨hv.1, by linarith [ht.2]⟩
    have hv_t' : InSimplex 1 (Fin.cons t' v) := by
      refine inSimplex_cons ht'.1 ⟨hv.1, by linarith [ht'.2]⟩
    have hd := hlip _ _ hv_t' hv_t
    rw [Fin.sum_univ_succ] at hd
    simp only [Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero, Finset.sum_const_zero,
      add_zero] at hd
    calc |G (Fin.cons t' v) - G (Fin.cons t v)|
        ≤ L * |t' - t| := hd
      _ ≤ (L + 1) * |t' - t| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left htt' (by linarith)
      _ = ε := by field_simp [show L + 1 ≠ 0 by linarith]
  refine ⟨hM, by linarith, ?_, ?_⟩
  · intro v hv
    have hs0 : 0 ≤ 1 - ∑ i, v i := by linarith [hv.2]
    have hs1 : 1 - ∑ i, v i ≤ 1 := by
      have : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ => hv.1 i
      linarith
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 1 - ∑ i, v i) (f := fun t => G (Fin.cons t v)) (C := M) fun t ht => by
        rw [Set.uIoc_of_le hs0] at ht
        simpa [Real.norm_eq_abs] using hbd _ (inSimplex_cons ht.1.le ⟨hv.1, by linarith [ht.2]⟩)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs0] at hnorm
    calc |∫ t in (0 : ℝ)..(1 - ∑ i, v i), G (Fin.cons t v)|
        ≤ M * (1 - ∑ i, v i) := hnorm
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hs1 hM
      _ = M := mul_one M
  · intro u v hu hv
    -- WLOG `1 - ∑ u ≤ 1 - ∑ v` by symmetry
    suffices hsym : ∀ u v : Fin k → ℝ, InSimplex 1 u → InSimplex 1 v →
        1 - ∑ i, u i ≤ 1 - ∑ i, v i →
        |(∫ t in (0 : ℝ)..(1 - ∑ i, u i), G (Fin.cons t u)) -
          (∫ t in (0 : ℝ)..(1 - ∑ i, v i), G (Fin.cons t v))| ≤
          (L + M) * ∑ i, |u i - v i| by
      rcases le_total (1 - ∑ i, u i) (1 - ∑ i, v i) with hle | hle
      · exact hsym u v hu hv hle
      · rw [abs_sub_comm]
        have := hsym v u hv hu hle
        simpa only [abs_sub_comm] using this
    intro u v hu hv hle
    set su := 1 - ∑ i, u i
    set sv := 1 - ∑ i, v i
    have hsu0 : 0 ≤ su := by linarith [hu.2]
    have hsu1 : su ≤ 1 := by
      have : 0 ≤ ∑ i : Fin k, u i := Finset.sum_nonneg fun i _ => hu.1 i
      linarith
    have hint_u : IntervalIntegrable (fun t => G (Fin.cons t u)) volume 0 su :=
      (hcont u hu).intervalIntegrable_of_Icc hsu0
    have hint_v1 : IntervalIntegrable (fun t => G (Fin.cons t v)) volume 0 su :=
      ((hcont v hv).mono (Set.Icc_subset_Icc_right hle)).intervalIntegrable_of_Icc hsu0
    have hint_v2 : IntervalIntegrable (fun t => G (Fin.cons t v)) volume su sv :=
      ((hcont v hv).mono (Set.Icc_subset_Icc_left hsu0)).intervalIntegrable_of_Icc hle
    have hsplit : ∫ t in (0 : ℝ)..sv, G (Fin.cons t v) =
        (∫ t in (0 : ℝ)..su, G (Fin.cons t v)) + (∫ t in su..sv, G (Fin.cons t v)) :=
      (intervalIntegral.integral_add_adjacent_intervals hint_v1 hint_v2).symm
    rw [hsplit]
    have hrew : (∫ t in (0 : ℝ)..su, G (Fin.cons t u)) -
        ((∫ t in (0 : ℝ)..su, G (Fin.cons t v)) + ∫ t in su..sv, G (Fin.cons t v)) =
        (∫ t in (0 : ℝ)..su, (G (Fin.cons t u) - G (Fin.cons t v))) -
          ∫ t in su..sv, G (Fin.cons t v) := by
      rw [intervalIntegral.integral_sub hint_u hint_v1]; ring
    rw [hrew]
    have hterm1 : |∫ t in (0 : ℝ)..su, (G (Fin.cons t u) - G (Fin.cons t v))| ≤
        (L * ∑ i, |u i - v i|) * su := by
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := su)
        (f := fun t => G (Fin.cons t u) - G (Fin.cons t v))
        (C := L * ∑ i, |u i - v i|) fun t ht => by
          rw [Set.uIoc_of_le hsu0] at ht
          have h1 := hlip _ _ (inSimplex_cons ht.1.le ⟨hu.1, by linarith [ht.2]⟩)
            (inSimplex_cons ht.1.le ⟨hv.1, by linarith [ht.2, hle]⟩)
          rw [Fin.sum_univ_succ] at h1
          simpa [Real.norm_eq_abs, Fin.cons_zero, Fin.cons_succ] using h1
      simpa [Real.norm_eq_abs, abs_of_nonneg hsu0] using hnorm
    have hterm2 : |∫ t in su..sv, G (Fin.cons t v)| ≤ M * (sv - su) := by
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := su) (b := sv)
        (f := fun t => G (Fin.cons t v))
        (C := M) fun t ht => by
          rw [Set.uIoc_of_le hle] at ht
          simpa [Real.norm_eq_abs] using
            hbd _ (inSimplex_cons (hsu0.trans ht.1.le) ⟨hv.1, by linarith [ht.2]⟩)
      simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] using hnorm
    have hdiff : sv - su ≤ ∑ i, |u i - v i| := by
      have heq : sv - su = ∑ i, (u i - v i) := by
        dsimp only [su, sv]; rw [Finset.sum_sub_distrib]; ring
      rw [heq]
      exact Finset.sum_le_sum fun i _ => le_abs_self _
    calc |(∫ t in (0 : ℝ)..su, (G (Fin.cons t u) - G (Fin.cons t v))) -
            ∫ t in su..sv, G (Fin.cons t v)|
        ≤ |∫ t in (0 : ℝ)..su, (G (Fin.cons t u) - G (Fin.cons t v))| +
            |∫ t in su..sv, G (Fin.cons t v)| := abs_sub _ _
      _ ≤ (L * ∑ i, |u i - v i|) * su + M * (sv - su) := add_le_add hterm1 hterm2
      _ ≤ (L * ∑ i, |u i - v i|) * 1 + M * ∑ i, |u i - v i| := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left hdiff hM)
          exact mul_le_mul_of_nonneg_left hsu1 (mul_nonneg hL (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      _ = (L + M) * ∑ i, |u i - v i| := by ring

/-- Joint induction establishing boundedness, Lipschitz dependence on `s`, stability under
uniform perturbations, and continuity of the inner slice of `simplexIntegral`. -/
theorem simplexIntegral_props (k : ℕ) :
    (∀ (s M L : ℝ) (G : (Fin k → ℝ) → ℝ), 0 ≤ s → s ≤ 1 → IsSimplexLipOn s M L G →
      |simplexIntegral k s G| ≤ M) ∧
    (∀ (s₁ s₂ M L : ℝ) (G : (Fin k → ℝ) → ℝ), 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      IsSimplexLipOn s₂ M L G →
      |simplexIntegral k s₂ G - simplexIntegral k s₁ G| ≤ (k : ℝ) * M * (s₂ - s₁)) ∧
    (∀ (s M₁ L₁ M₂ L₂ ε : ℝ) (G₁ G₂ : (Fin k → ℝ) → ℝ), 0 ≤ s → s ≤ 1 → 0 ≤ ε →
      IsSimplexLipOn s M₁ L₁ G₁ → IsSimplexLipOn s M₂ L₂ G₂ →
      (∀ v, InSimplex s v → |G₁ v - G₂ v| ≤ ε) →
      |simplexIntegral k s G₁ - simplexIntegral k s G₂| ≤ ε) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro s M L G hs _ hG
      exact hG.2.2.1 Fin.elim0 (inSimplex_elim0 hs)
    · intro s₁ s₂ M L G _ _ _ _
      simp [simplexIntegral]
    · intro s M₁ L₁ M₂ L₂ ε G₁ G₂ hs _ _ _ _ hdiff
      exact hdiff Fin.elim0 (inSimplex_elim0 hs)
  | succ k ih =>
    obtain ⟨ih_bd, ih_s, ih_f⟩ := ih
    -- First prove Lipschitz continuity of `t ↦ simplexIntegral k (s - t) (G (cons t ·))` on `[0, s]`
    have hslice_lip : ∀ (s M L : ℝ) (G : (Fin (k + 1) → ℝ) → ℝ), 0 ≤ s → s ≤ 1 →
        IsSimplexLipOn s M L G →
        ∀ t₁ t₂, t₁ ∈ Set.Icc (0 : ℝ) s → t₂ ∈ Set.Icc (0 : ℝ) s →
          |simplexIntegral k (s - t₁) (fun v => G (Fin.cons t₁ v)) -
            simplexIntegral k (s - t₂) (fun v => G (Fin.cons t₂ v))| ≤
            (L + (k : ℝ) * M) * |t₁ - t₂| := by
      intro s M L G hs0 hs1 hG t₁ t₂ ht₁ ht₂
      suffices hle : ∀ a b, a ∈ Set.Icc (0 : ℝ) s → b ∈ Set.Icc (0 : ℝ) s → a ≤ b →
          |simplexIntegral k (s - a) (fun v => G (Fin.cons a v)) -
            simplexIntegral k (s - b) (fun v => G (Fin.cons b v))| ≤
            (L + (k : ℝ) * M) * (b - a) by
        rcases le_total t₁ t₂ with h | h
        · rw [abs_sub_comm t₁ t₂, abs_of_nonneg (sub_nonneg.mpr h)]
          exact hle t₁ t₂ ht₁ ht₂ h
        · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_sub_comm]
          exact hle t₂ t₁ ht₂ ht₁ h
      intro a b ha hb hab
      have hGa : IsSimplexLipOn (s - a) M L (fun v => G (Fin.cons a v)) := hG.cons ha.1
      have hGb : IsSimplexLipOn (s - b) M L (fun v => G (Fin.cons b v)) := hG.cons hb.1
      have hGa_sub : IsSimplexLipOn (s - b) M L (fun v => G (Fin.cons a v)) :=
        hGa.mono (by linarith)
      have h1 : |simplexIntegral k (s - a) (fun v => G (Fin.cons a v)) -
            simplexIntegral k (s - b) (fun v => G (Fin.cons a v))| ≤
          (k : ℝ) * M * (b - a) := by
        have h := ih_s (s - b) (s - a) M L (fun v => G (Fin.cons a v))
          (by linarith [hb.2]) (by linarith) (by linarith [ha.1]) hGa
        simpa [sub_sub_sub_cancel_left] using h
      have h2 : |simplexIntegral k (s - b) (fun v => G (Fin.cons a v)) -
            simplexIntegral k (s - b) (fun v => G (Fin.cons b v))| ≤
          L * (b - a) := by
        refine ih_f (s - b) M L M L (L * (b - a)) _ _
          (by linarith [hb.2]) (by linarith [hb.1]) (mul_nonneg hG.2.1 (by linarith))
          hGa_sub hGb fun v hv => ?_
        have hlip := hG.2.2.2 (Fin.cons a v) (Fin.cons b v)
          (inSimplex_cons ha.1 (inSimplex_mono (by linarith) hv)) (inSimplex_cons hb.1 hv)
        rw [Fin.sum_univ_succ] at hlip
        simp only [Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero, Finset.sum_const_zero,
          add_zero] at hlip
        rwa [abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)] at hlip
      calc |simplexIntegral k (s - a) (fun v => G (Fin.cons a v)) -
              simplexIntegral k (s - b) (fun v => G (Fin.cons b v))|
          ≤ |simplexIntegral k (s - a) (fun v => G (Fin.cons a v)) -
              simplexIntegral k (s - b) (fun v => G (Fin.cons a v))| +
            |simplexIntegral k (s - b) (fun v => G (Fin.cons a v)) -
              simplexIntegral k (s - b) (fun v => G (Fin.cons b v))| := abs_sub_le _ _ _
        _ ≤ (k : ℝ) * M * (b - a) + L * (b - a) := add_le_add h1 h2
        _ = (L + (k : ℝ) * M) * (b - a) := by ring
    have hslice_cont : ∀ (s M L : ℝ) (G : (Fin (k + 1) → ℝ) → ℝ), 0 ≤ s → s ≤ 1 →
        IsSimplexLipOn s M L G →
        ContinuousOn (fun t => simplexIntegral k (s - t) (fun v => G (Fin.cons t v)))
          (Set.Icc 0 s) := by
      intro s M L G hs0 hs1 hG
      refine Metric.continuousOn_iff.mpr fun t ht ε hε => ?_
      set K := L + (k : ℝ) * M + 1
      have hK : 0 < K := by
        have : 0 ≤ (k : ℝ) * M := mul_nonneg (Nat.cast_nonneg k) hG.1
        linarith [hG.2.1]
      refine ⟨ε / K, div_pos hε hK, fun t' ht' htt' => ?_⟩
      rw [Real.dist_eq] at htt' ⊢
      calc |simplexIntegral k (s - t') (fun v => G (Fin.cons t' v)) -
              simplexIntegral k (s - t) (fun v => G (Fin.cons t v))|
          ≤ (L + (k : ℝ) * M) * |t' - t| := hslice_lip s M L G hs0 hs1 hG t' t ht' ht
        _ ≤ K * |t' - t| := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (abs_nonneg _)
        _ < K * (ε / K) := mul_lt_mul_of_pos_left htt' hK
        _ = ε := mul_div_cancel₀ ε hK.ne'
    refine ⟨?_, ?_, ?_⟩
    · -- Boundedness
      intro s M L G hs0 hs1 hG
      dsimp only [simplexIntegral]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
        (f := fun t => simplexIntegral k (s - t) (fun v => G (Fin.cons t v)))
        (C := M) fun t ht => by
          rw [Set.uIoc_of_le hs0] at ht
          simpa [Real.norm_eq_abs] using
            ih_bd (s - t) M L (fun v => G (Fin.cons t v))
              (by linarith [ht.2]) (by linarith [ht.1]) (hG.cons ht.1.le)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs0] at hnorm
      calc |∫ t in (0 : ℝ)..s, simplexIntegral k (s - t) (fun v => G (Fin.cons t v))|
          ≤ M * s := hnorm
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left hs1 hG.1
        _ = M := mul_one M
    · -- Lipschitz in `s`
      intro s₁ s₂ M L G hs₁ hs12 hs₂ hG
      dsimp only [simplexIntegral]
      have hcont2 := hslice_cont s₂ M L G (hs₁.trans hs12) hs₂ hG
      have hint2a : IntervalIntegrable
          (fun t => simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))) volume 0 s₁ :=
        (hcont2.mono (Set.Icc_subset_Icc_right hs12)).intervalIntegrable_of_Icc hs₁
      have hint2b : IntervalIntegrable
          (fun t => simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))) volume s₁ s₂ :=
        (hcont2.mono (Set.Icc_subset_Icc_left hs₁)).intervalIntegrable_of_Icc hs12
      have hint1 : IntervalIntegrable
          (fun t => simplexIntegral k (s₁ - t) (fun v => G (Fin.cons t v))) volume 0 s₁ :=
        (hslice_cont s₁ M L G hs₁ (hs12.trans hs₂) (hG.mono hs12)).intervalIntegrable_of_Icc hs₁
      have hsplit : ∫ t in (0 : ℝ)..s₂, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v)) =
          (∫ t in (0 : ℝ)..s₁, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))) +
          (∫ t in s₁..s₂, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))) :=
        (intervalIntegral.integral_add_adjacent_intervals hint2a hint2b).symm
      rw [hsplit]
      have hrew : ((∫ t in (0 : ℝ)..s₁, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))) +
            ∫ t in s₁..s₂, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))) -
            ∫ t in (0 : ℝ)..s₁, simplexIntegral k (s₁ - t) (fun v => G (Fin.cons t v)) =
          (∫ t in (0 : ℝ)..s₁, (simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v)) -
              simplexIntegral k (s₁ - t) (fun v => G (Fin.cons t v)))) +
          ∫ t in s₁..s₂, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v)) := by
        rw [intervalIntegral.integral_sub hint2a hint1]; ring
      rw [hrew]
      have h1 : |∫ t in (0 : ℝ)..s₁, (simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v)) -
            simplexIntegral k (s₁ - t) (fun v => G (Fin.cons t v)))| ≤
          (k : ℝ) * M * (s₂ - s₁) * s₁ := by
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s₁)
          (f := fun t => simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v)) -
            simplexIntegral k (s₁ - t) (fun v => G (Fin.cons t v)))
          (C := (k : ℝ) * M * (s₂ - s₁)) fun t ht => by
            rw [Set.uIoc_of_le hs₁] at ht
            have h := ih_s (s₁ - t) (s₂ - t) M L (fun v => G (Fin.cons t v))
              (by linarith [ht.2]) (by linarith) (by linarith [ht.1]) (hG.cons ht.1.le)
            simpa [Real.norm_eq_abs, sub_sub_sub_cancel_right] using h
        simpa [Real.norm_eq_abs, abs_of_nonneg hs₁] using hnorm
      have h2 : |∫ t in s₁..s₂, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))| ≤
          M * (s₂ - s₁) := by
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := s₁) (b := s₂)
          (f := fun t => simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v)))
          (C := M) fun t ht => by
            rw [Set.uIoc_of_le hs12] at ht
            simpa [Real.norm_eq_abs] using
              ih_bd (s₂ - t) M L (fun v => G (Fin.cons t v))
                (by linarith [ht.2]) (by linarith [ht.1, hs₁]) (hG.cons (hs₁.trans ht.1.le))
        simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs12)] using hnorm
      have hs₁1 : s₁ ≤ 1 := hs12.trans hs₂
      calc |(∫ t in (0 : ℝ)..s₁, (simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v)) -
                simplexIntegral k (s₁ - t) (fun v => G (Fin.cons t v)))) +
              ∫ t in s₁..s₂, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))|
          ≤ |∫ t in (0 : ℝ)..s₁, (simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v)) -
                simplexIntegral k (s₁ - t) (fun v => G (Fin.cons t v)))| +
              |∫ t in s₁..s₂, simplexIntegral k (s₂ - t) (fun v => G (Fin.cons t v))| :=
            abs_add_le _ _
        _ ≤ (k : ℝ) * M * (s₂ - s₁) * s₁ + M * (s₂ - s₁) := add_le_add h1 h2
        _ ≤ (k : ℝ) * M * (s₂ - s₁) * 1 + M * (s₂ - s₁) := by
            have hnn : 0 ≤ (k : ℝ) * M * (s₂ - s₁) :=
              mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hG.1) (sub_nonneg.mpr hs12)
            linarith [mul_le_mul_of_nonneg_left hs₁1 hnn]
        _ = ((k + 1 : ℕ) : ℝ) * M * (s₂ - s₁) := by push_cast; ring
    · -- Stability under uniform perturbation
      intro s M₁ L₁ M₂ L₂ ε G₁ G₂ hs0 hs1 hε hG₁ hG₂ hdiff
      dsimp only [simplexIntegral]
      have hint1 : IntervalIntegrable (fun t => simplexIntegral k (s - t) (fun v => G₁ (Fin.cons t v))) volume 0 s :=
        (hslice_cont s M₁ L₁ G₁ hs0 hs1 hG₁).intervalIntegrable_of_Icc hs0
      have hint2 : IntervalIntegrable (fun t => simplexIntegral k (s - t) (fun v => G₂ (Fin.cons t v))) volume 0 s :=
        (hslice_cont s M₂ L₂ G₂ hs0 hs1 hG₂).intervalIntegrable_of_Icc hs0
      rw [← intervalIntegral.integral_sub hint1 hint2]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
        (f := fun t => simplexIntegral k (s - t) (fun v => G₁ (Fin.cons t v)) -
          simplexIntegral k (s - t) (fun v => G₂ (Fin.cons t v)))
        (C := ε) fun t ht => by
          rw [Set.uIoc_of_le hs0] at ht
          simpa [Real.norm_eq_abs] using
            ih_f (s - t) M₁ L₁ M₂ L₂ ε (fun v => G₁ (Fin.cons t v)) (fun v => G₂ (Fin.cons t v))
              (by linarith [ht.2]) (by linarith [ht.1]) hε (hG₁.cons ht.1.le) (hG₂.cons ht.1.le)
              fun v hv => hdiff (Fin.cons t v) (inSimplex_cons ht.1.le hv)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs0] at hnorm
      calc |∫ t in (0 : ℝ)..s, (simplexIntegral k (s - t) (fun v => G₁ (Fin.cons t v)) -
              simplexIntegral k (s - t) (fun v => G₂ (Fin.cons t v)))|
          ≤ ε * s := hnorm
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hs1 hε
        _ = ε := mul_one ε

lemma simplexIntegral_slice_lipschitz {k : ℕ} {s M L : ℝ} {G : (Fin (k + 1) → ℝ) → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hG : IsSimplexLipOn s M L G)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) s) (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) s) :
    |simplexIntegral k (s - t₁) (fun v => G (Fin.cons t₁ v)) -
      simplexIntegral k (s - t₂) (fun v => G (Fin.cons t₂ v))| ≤
      (L + (k : ℝ) * M) * |t₁ - t₂| := by
  have ⟨_, ih_s, ih_f⟩ := simplexIntegral_props k
  suffices hle : ∀ a b, a ∈ Set.Icc (0 : ℝ) s → b ∈ Set.Icc (0 : ℝ) s → a ≤ b →
      |simplexIntegral k (s - a) (fun v => G (Fin.cons a v)) -
        simplexIntegral k (s - b) (fun v => G (Fin.cons b v))| ≤
        (L + (k : ℝ) * M) * (b - a) by
    rcases le_total t₁ t₂ with h | h
    · rw [abs_sub_comm t₁ t₂, abs_of_nonneg (sub_nonneg.mpr h)]
      exact hle t₁ t₂ ht₁ ht₂ h
    · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_sub_comm]
      exact hle t₂ t₁ ht₂ ht₁ h
  intro a b ha hb hab
  have hGa : IsSimplexLipOn (s - a) M L (fun v => G (Fin.cons a v)) := hG.cons ha.1
  have hGb : IsSimplexLipOn (s - b) M L (fun v => G (Fin.cons b v)) := hG.cons hb.1
  have h1 : |simplexIntegral k (s - a) (fun v => G (Fin.cons a v)) -
        simplexIntegral k (s - b) (fun v => G (Fin.cons a v))| ≤
      (k : ℝ) * M * (b - a) := by
    have h := ih_s (s - b) (s - a) M L (fun v => G (Fin.cons a v))
      (by linarith [hb.2]) (by linarith) (by linarith [ha.1]) hGa
    simpa [sub_sub_sub_cancel_left] using h
  have h2 : |simplexIntegral k (s - b) (fun v => G (Fin.cons a v)) -
        simplexIntegral k (s - b) (fun v => G (Fin.cons b v))| ≤
      L * (b - a) := by
    refine ih_f (s - b) M L M L (L * (b - a)) _ _
      (by linarith [hb.2]) (by linarith [hb.1]) (mul_nonneg hG.2.1 (by linarith))
      (hGa.mono (by linarith)) hGb fun v hv => ?_
    have hlip := hG.2.2.2 (Fin.cons a v) (Fin.cons b v)
      (inSimplex_cons ha.1 (inSimplex_mono (by linarith) hv)) (inSimplex_cons hb.1 hv)
    rw [Fin.sum_univ_succ] at hlip
    simp only [Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero, Finset.sum_const_zero,
      add_zero] at hlip
    rwa [abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)] at hlip
  calc |simplexIntegral k (s - a) (fun v => G (Fin.cons a v)) -
          simplexIntegral k (s - b) (fun v => G (Fin.cons b v))|
      ≤ |simplexIntegral k (s - a) (fun v => G (Fin.cons a v)) -
          simplexIntegral k (s - b) (fun v => G (Fin.cons a v))| +
        |simplexIntegral k (s - b) (fun v => G (Fin.cons a v)) -
          simplexIntegral k (s - b) (fun v => G (Fin.cons b v))| := abs_sub_le _ _ _
    _ ≤ (k : ℝ) * M * (b - a) + L * (b - a) := add_le_add h1 h2
    _ = (L + (k : ℝ) * M) * (b - a) := by ring

lemma simplexIntegral_nonneg {k : ℕ} {s : ℝ} {G : (Fin k → ℝ) → ℝ}
    (hs : 0 ≤ s) (hnn : ∀ v, InSimplex s v → 0 ≤ G v) :
    0 ≤ simplexIntegral k s G := by
  induction k generalizing s with
  | zero => exact hnn Fin.elim0 (inSimplex_elim0 hs)
  | succ k ih =>
    dsimp only [simplexIntegral]
    exact intervalIntegral.integral_nonneg hs fun t ht =>
      ih (by linarith [ht.2]) fun v hv => hnn (Fin.cons t v) (inSimplex_cons ht.1 hv)

/-! ## Section 2: Elementary 1D Multiplicative Sums and `k`-D Sum-to-Integral Theorem -/

/-- Multiplicative weight `1 / φ(n)` supported on squarefree `n` coprime to `W`. -/
def aPhi (W n : ℕ) : ℝ :=
  if Squarefree n ∧ Nat.Coprime n W then ((n.totient : ℝ))⁻¹ else 0

/-- Second Selberg multiplicative density `g₂(n) = ∏_{p ∣ n} (p - 2)`. -/
def g₂ (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, (p - 2)

/-- Multiplicative weight `1 / g₂(n)` supported on squarefree `n` coprime to `W`. -/
def aG2 (W n : ℕ) : ℝ :=
  if Squarefree n ∧ Nat.Coprime n W then ((g₂ n : ℝ))⁻¹ else 0

lemma aPhi_zero (W : ℕ) : aPhi W 0 = 0 := by
  simp [aPhi, not_squarefree_zero]

lemma aPhi_nonneg (W n : ℕ) : 0 ≤ aPhi W n := by
  unfold aPhi; split_ifs <;> positivity

lemma aG2_zero (W : ℕ) : aG2 W 0 = 0 := by
  simp [aG2, not_squarefree_zero]

lemma aG2_nonneg (W n : ℕ) : 0 ≤ aG2 W n := by
  unfold aG2; split_ifs <;> positivity

lemma g₂_one : g₂ 1 = 1 := by simp [g₂]

lemma g₂_prime {p : ℕ} (hp : p.Prime) : g₂ p = p - 2 := by
  simp [g₂, hp.primeFactors]

lemma g₂_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : Nat.Coprime a b) :
    g₂ (a * b) = g₂ a * g₂ b := by
  unfold g₂
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hcop.disjoint_primeFactors]

lemma g₂_pos_of_coprime_two {n : ℕ} (hn : n ≠ 0) (hodd : Nat.Coprime n 2) : 0 < g₂ n := by
  unfold g₂
  refine Finset.prod_pos fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpdvd
    have := Nat.Coprime.coprime_dvd_left hpdvd hodd
    simp at this
  have : 3 ≤ p := by have := hpp.two_le; omega
  omega

lemma g₂_le_totient_of_squarefree {n : ℕ} (hn : Squarefree n) : g₂ n ≤ n.totient := by
  have hn0 : n ≠ 0 := hn.ne_zero
  unfold g₂
  have hphi : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_prod_factorization hn0]
    simp only [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hfac1 : n.factorization p = 1 := by
      have hge1 : 1 ≤ n.factorization p :=
        Nat.Prime.dvd_iff_one_le_factorization hpp hn0 |>.mp hpdvd
      have hle1 : n.factorization p ≤ 1 := by
        by_contra hgt
        push Not at hgt
        have hp2 : p ^ 2 ∣ n := (hpp.pow_dvd_iff_le_factorization hn0).mpr (by omega)
        have hsq : p * p ∣ n := by simpa [sq] using hp2
        exact hpp.ne_one (Nat.isUnit_iff.mp (hn p hsq))
      omega
    rw [hfac1, pow_zero, one_mul]
  rw [hphi]
  exact Finset.prod_le_prod' fun p _ => by omega

lemma aPhi_le_aG2 {W n : ℕ} (h2W : 2 ∣ W) : aPhi W n ≤ aG2 W n := by
  unfold aPhi aG2
  split_ifs with h
  · have hn0 : n ≠ 0 := h.1.ne_zero
    have hodd : Nat.Coprime n 2 := Nat.Coprime.coprime_dvd_right h2W h.2
    have hgpos : (0 : ℝ) < (g₂ n : ℝ) := Nat.cast_pos.mpr (g₂_pos_of_coprime_two hn0 hodd)
    have hle : (g₂ n : ℝ) ≤ (n.totient : ℝ) := by exact_mod_cast g₂_le_totient_of_squarefree h.1
    exact inv_anti₀ hgpos hle
  · exact le_rfl

/-- Radical of a positive integer: `rad(n) = ∏_{p ∣ n} p`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma rad_dvd {n : ℕ} (hn : n ≠ 0) : rad n ∣ n :=
  Nat.prod_primeFactors_dvd n

lemma rad_le {n : ℕ} (hn : 0 < n) : rad n ≤ n :=
  Nat.le_of_dvd hn (rad_dvd hn.ne')

lemma squarefree_rad (n : ℕ) : Squarefree (rad n) := by
  unfold rad
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have h1 : p ∣ ∏ q ∈ n.primeFactors, q := dvd_trans (dvd_mul_left p p) hpp
  -- If `p^2 ∣ ∏_{q ∈ s} q` for a finset of distinct primes, contradiction
  have hprod_sf : ∀ s : Finset ℕ, (∀ q ∈ s, q.Prime) → Squarefree (∏ q ∈ s, q) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simpa using squarefree_one
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have haP : a.Prime := hs a (mem_insert_self a s)
      have hsP : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
      have hcop : Nat.Coprime a (∏ q ∈ s, q) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        have hneq : a ≠ q := fun h => ha (h ▸ hq)
        exact (Nat.coprime_primes haP (hsP q hq)).mpr hneq
      exact (Nat.squarefree_mul hcop).mpr ⟨haP.squarefree, ih hsP⟩
  exact (Nat.squarefree_iff_prime_squarefree.mp
    (hprod_sf n.primeFactors fun q hq => Nat.prime_of_mem_primeFactors hq)) p hp hpp

lemma primeFactors_rad (n : ℕ) : (rad n).primeFactors = n.primeFactors := by
  unfold rad
  have hprod_pf : ∀ s : Finset ℕ, (∀ q ∈ s, q.Prime) → (∏ q ∈ s, q).primeFactors = s := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have haP : a.Prime := hs a (mem_insert_self a s)
      have hsP : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
      have hsne : ∏ q ∈ s, q ≠ 0 := (Finset.prod_pos fun q hq => (hsP q hq).pos).ne'
      rw [Finset.prod_insert ha, Nat.primeFactors_mul haP.ne_zero hsne, haP.primeFactors, ih hsP]
      ext x; simp
  exact hprod_pf n.primeFactors fun q hq => Nat.prime_of_mem_primeFactors hq

lemma rad_eq_self_of_squarefree {n : ℕ} (hn : Squarefree n) : rad n = n := by
  unfold rad
  exact Nat.prod_primeFactors_of_squarefree hn

lemma coprime_rad_iff {n W : ℕ} (hn : n ≠ 0) : Nat.Coprime (rad n) W ↔ Nat.Coprime n W := by
  constructor
  · intro h
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpn : p ∣ n := dvd_trans hpdvd (Nat.gcd_dvd_left n W)
    have hpW : p ∣ W := dvd_trans hpdvd (Nat.gcd_dvd_right n W)
    have hprad : p ∣ rad n := Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩)
    exact hp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp h) ▸ Nat.dvd_gcd hprad hpW)
  · exact Nat.Coprime.coprime_dvd_left (rad_dvd hn)

/-- Elementary helper: `∑_{x ∈ s.biUnion t} f x ≤ ∑_{a ∈ s} ∑_{x ∈ t a} f x` for `f ≥ 0`. -/
private lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : α → Finset β} {f : β → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h1 : ∑ x ∈ t a ∪ s.biUnion t, f x ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := t a ∩ s.biUnion t) fun x _ => hf x]
    linarith

/-- Elementary helper: `∏_{x ∈ s} f x ≤ ∏_{x ∈ t} f x` for `s ⊆ t` and `1 ≤ f x` on `t`. -/
private lemma prod_le_prod_of_subset_one_le {α : Type*} [DecidableEq α]
    {s t : Finset α} {f : α → ℝ} (hsub : s ⊆ t) (h1 : ∀ x ∈ t, 1 ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x := by
  rw [← Finset.prod_sdiff hsub]
  have hs_nn : 0 ≤ ∏ x ∈ s, f x := Finset.prod_nonneg fun x hx => by linarith [h1 x (hsub hx)]
  have hdiff_ge1 : 1 ≤ ∏ x ∈ t \ s, f x :=
    Finset.one_le_prod fun x hx => h1 x (Finset.mem_sdiff.mp hx).1
  nlinarith

/-- Elementary helper: `Nat.Coprime (a % b) b ↔ Nat.Coprime a b`. -/
private lemma coprime_mod_left_iff' (a b : ℕ) : Nat.Coprime (a % b) b ↔ Nat.Coprime a b := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec b a, Nat.gcd_comm]

/-- Elementary harmonic bound: `|∑_{1 ≤ n ≤ ⌊x⌋₊} 1/n - log x| ≤ 1` for `x ≥ 1`. -/
lemma abs_harmonic_sub_log_le_one {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((n : ℝ))⁻¹) - Real.log x| ≤ 1 := by
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hx)
  have hx0 : 0 < x := by linarith
  have hN_le : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hx_lt : x < ((N + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one x
  have hupper_gen : ∀ K : ℕ, 1 ≤ K → ∑ n ∈ Finset.Icc 1 K, ((n : ℝ))⁻¹ ≤ Real.log (K : ℝ) + 1 := by
    intro K hK1
    induction K, hK1 using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hstep : (((m + 1 : ℕ) : ℝ))⁻¹ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have hlog := Real.log_le_sub_one_of_pos (div_pos hm_pos hm1_pos)
        rw [Real.log_div hm_pos.ne' hm1_pos.ne'] at hlog
        have hsub : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(((m + 1 : ℕ) : ℝ)⁻¹) := by
          push_cast; field_simp [hm1_pos.ne']; ring
        linarith
      linarith
  have hlower_gen : ∀ K : ℕ, 1 ≤ K → Real.log ((K + 1 : ℕ) : ℝ) ≤ ∑ n ∈ Finset.Icc 1 K, ((n : ℝ))⁻¹ := by
    intro K hK1
    induction K, hK1 using Nat.le_induction with
    | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, inv_one, Nat.cast_add]
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num; linarith
    | succ m hm ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm2_pos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hstep : Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤
          (((m + 1 : ℕ) : ℝ))⁻¹ := by
        have hlog := Real.log_le_sub_one_of_pos (div_pos hm2_pos hm1_pos)
        rw [Real.log_div hm2_pos.ne' hm1_pos.ne'] at hlog
        have hsub : ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = (((m + 1 : ℕ) : ℝ)⁻¹) := by
          push_cast; field_simp [hm1_pos.ne']; ring
        linarith
      have heq : ((m + 1 + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by norm_cast
      rw [heq]
      linarith
  have hupper := hupper_gen N hN1
  have hlower := hlower_gen N hN1
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log x :=
    Real.log_le_log (Nat.cast_pos.mpr hN1) hN_le
  have hlogx_le : Real.log x ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_le_log hx0 hx_lt.le
  rw [abs_le]; constructor <;> linarith

/-- Elementary coprime harmonic sum asymptotic:
`∑_{1 ≤ m ≤ x, (m, W)=1} 1/m = (φ(W)/W) * log x + O_W(1)`. -/
theorem sum_inv_coprime_asymp (W : ℕ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m W), ((m : ℝ))⁻¹) -
        ((W.totient : ℝ) / (W : ℝ)) * Real.log x| ≤ C := by
  have hW_pos : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.mpr hW
  set C : ℝ := (W.totient : ℝ) * (4 + Real.log (W : ℝ)) + 1 with hC_def
  have hC_pos : 0 < C := by
    have : 0 ≤ Real.log (W : ℝ) := Real.log_nonneg (by exact_mod_cast hW)
    positivity
  refine ⟨C, hC_pos, fun x hx => ?_⟩
  set Rset := (Finset.Icc 1 W).filter (fun r => Nat.Coprime r W)
  have hRcard : Rset.card = W.totient := by
    have hbij : Rset = ((Finset.range W).filter (fun r => Nat.Coprime r W)).image
        (fun r => if r = 0 then W else r) := by
      ext m
      simp only [Rset, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨⟨hm1, hmW⟩, hcop⟩
        by_cases hEq : m = W
        · subst hEq
          refine ⟨0, ⟨hW, by simpa using hcop⟩, by simp⟩
        · refine ⟨m, ⟨by omega, hcop⟩, by simp [show m ≠ 0 by omega]⟩
      · rintro ⟨r, ⟨hrW, hcop⟩, rfl⟩
        split_ifs with hr0
        · subst hr0; exact ⟨⟨hW, le_rfl⟩, by simpa using hcop⟩
        · exact ⟨⟨by omega, by omega⟩, hcop⟩
    rw [hbij, Finset.card_image_of_injOn]
    · rw [Nat.totient_eq_card_coprime]
      congr 1; ext r; simp [Nat.coprime_comm]
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
      by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> simp_all <;> omega
  -- Partition `(Icc 1 ⌊x⌋₊).filter (Coprime · W)` by residue `r ∈ Rset`
  have hpart : ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m W), ((m : ℝ))⁻¹ =
      ∑ r ∈ Rset, ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => m ≡ r [MOD W]), ((m : ℝ))⁻¹ := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, Rset]
      constructor
      · rintro ⟨hm, hcop⟩
        let r := if m % W = 0 then W else m % W
        refine ⟨r, ⟨⟨?_, ?_⟩, ?_⟩, ⟨hm, ?_⟩⟩
        · dsimp only [r]; split_ifs with h0
          · exact hW
          · omega
        · dsimp only [r]; split_ifs with h0
          · exact le_rfl
          · exact (Nat.mod_lt m hW).le
        · dsimp only [r]; split_ifs with h0
          · have hWdvd : W ∣ m := Nat.dvd_of_mod_eq_zero h0
            have hW1 : W = 1 := by
              have := Nat.Coprime.coprime_dvd_left hWdvd hcop
              simpa using this
            rw [hW1]; simp
          · exact (coprime_mod_left_iff' m W).mpr hcop
        · dsimp only [r, Nat.ModEq]; split_ifs with h0
          · rw [h0, Nat.mod_self]
          · rw [Nat.mod_mod]
      · rintro ⟨r, ⟨_, hcop⟩, ⟨hm, hmod⟩⟩
        refine ⟨hm, ?_⟩
        rw [Nat.ModEq] at hmod
        exact (coprime_mod_left_iff' m W).mp (hmod ▸ (coprime_mod_left_iff' r W).mpr hcop)
    · intro r₁ hr₁ r₂ hr₂ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro m hm₁ hm₂
      simp only [Finset.mem_filter] at hm₁ hm₂
      simp only [Finset.mem_coe, Rset, Finset.mem_filter, Finset.mem_Icc] at hr₁ hr₂
      have hmod : r₁ ≡ r₂ [MOD W] := hm₁.2.symm.trans hm₂.2
      rw [Nat.ModEq] at hmod
      by_cases h1 : r₁ = W <;> by_cases h2 : r₂ = W
      · exact hne (h1.trans h2.symm)
      · rw [h1, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod; omega
      · rw [h2, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod; omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; exact hne hmod
  rw [hpart]
  -- Each residue class `r ∈ Rset` contributes `(1/W) * log x` up to `4 + log W`
  have hres : ∀ r ∈ Rset,
      |(∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => m ≡ r [MOD W]), ((m : ℝ))⁻¹) -
        (1 / (W : ℝ)) * Real.log x| ≤ 4 + Real.log (W : ℝ) := by
    intro r hr
    simp only [Rset, Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hr1, hrW⟩, _⟩ := hr
    have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr1
    by_cases hxW : x < (W : ℝ)
    · -- For `1 ≤ x < W`, at most 1 element `m = r` in the residue class!
      have hsub : (Finset.Icc 1 ⌊x⌋₊).filter (fun m => m ≡ r [MOD W]) ⊆ {r} := by
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hm ⊢
        have hmW : m < W := by
          have : (m : ℝ) ≤ x := (Nat.cast_le.mpr hm.1.2).trans (Nat.floor_le (by linarith))
          exact_mod_cast this.trans_lt hxW
        have hmod : m % W = r % W := hm.2
        rw [Nat.mod_eq_of_lt hmW] at hmod
        by_cases hrEq : r = W
        · rw [hrEq, Nat.mod_self] at hmod; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hmod; exact hmod
      have hsum_nn : 0 ≤ ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => m ≡ r [MOD W]), ((m : ℝ))⁻¹ :=
        Finset.sum_nonneg fun _ _ => by positivity
      have hsum_le : ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => m ≡ r [MOD W]), ((m : ℝ))⁻¹ ≤ 1 := by
        calc _ ≤ ∑ m ∈ ({r} : Finset ℕ), ((m : ℝ))⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
          _ = ((r : ℝ))⁻¹ := by simp
          _ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hr1)
      have hlog_nn : 0 ≤ (1 / (W : ℝ)) * Real.log x :=
        mul_nonneg (by positivity) (Real.log_nonneg hx)
      have hlog_le : (1 / (W : ℝ)) * Real.log x ≤ Real.log (W : ℝ) := by
        calc (1 / (W : ℝ)) * Real.log x
            ≤ 1 * Real.log x := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg hx)
              rw [div_le_one hW_pos]; exact_mod_cast hW
          _ = Real.log x := one_mul _
          _ ≤ Real.log (W : ℝ) := Real.log_le_log (by linarith) hxW.le
      rw [abs_le]; constructor <;> linarith
    · push Not at hxW
      -- Reindex `{m ∈ Icc 1 ⌊x⌋₊ : m ≡ r [MOD W]}` as `q ↦ W * q + r` for `0 ≤ q ≤ Q`
      have hfl_ge : r ≤ ⌊x⌋₊ := le_trans hrW (Nat.le_floor hxW)
      set Q := (⌊x⌋₊ - r) / W
      have hbij : (Finset.Icc 1 ⌊x⌋₊).filter (fun m => m ≡ r [MOD W]) =
          (Finset.Icc 0 Q).image (fun q => W * q + r) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hm1, hmfl⟩, hmod⟩
          have hrm : r ≤ m := by
            by_contra hlt
            push Not at hlt
            have hmW : m < W := lt_of_lt_of_le hlt hrW
            have h1 : m % W = r % W := hmod
            rw [Nat.mod_eq_of_lt hmW] at h1
            by_cases hrEq : r = W
            · rw [hrEq, Nat.mod_self] at h1; omega
            · rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
          have hdiv : W ∣ m - r := by
            have := Nat.ModEq.symm hmod
            exact (Nat.modEq_iff_dvd' hrm).mp this
          obtain ⟨q, hq⟩ := hdiv
          refine ⟨q, ⟨Nat.zero_le q, ?_⟩, by omega⟩
          have : W * q ≤ ⌊x⌋₊ - r := by omega
          exact (Nat.le_div_iff_mul_le hW).mpr (by rw [mul_comm]; exact this)
        · rintro ⟨q, ⟨_, hqQ⟩, rfl⟩
          have hqW : W * q ≤ ⌊x⌋₊ - r := by
            have := (Nat.le_div_iff_mul_le hW).mp hqQ
            linarith
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [Nat.ModEq, Nat.mul_add_mod]
      rw [hbij, Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hW (by omega))]
      -- Split `q = 0` from `q ∈ Icc 1 Q`
      have hIcc_split : Finset.Icc 0 Q = insert 0 (Finset.Icc 1 Q) := by
        ext q; simp only [Finset.mem_Icc, Finset.mem_insert, Nat.zero_le, true_and]
        by_cases hq : q = 0 <;> simp [hq] <;> omega
      rw [hIcc_split, Finset.sum_insert (by simp)]
      -- Compare `∑_{q=1}^Q 1/(W*q + r)` with `(1/W) * ∑_{q=1}^Q 1/q`:
      -- `1/(W*(q+1)) ≤ 1/(W*q + r) ≤ 1/(W*q)`
      have hup_q : ∑ q ∈ Finset.Icc 1 Q, (((W * q + r : ℕ) : ℝ))⁻¹ ≤
          (1 / (W : ℝ)) * ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun q hq => ?_
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq1
        rw [one_div, ← mul_inv]
        refine inv_anti₀ (mul_pos hW_pos hqpos) ?_
        push_cast; linarith
      have hlo_q : (1 / (W : ℝ)) * (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹ - 1) ≤
          ∑ q ∈ Finset.Icc 1 Q, (((W * q + r : ℕ) : ℝ))⁻¹ := by
        have h1 : (1 / (W : ℝ)) * ∑ q ∈ Finset.Icc 1 Q, (((q + 1 : ℕ) : ℝ))⁻¹ ≤
            ∑ q ∈ Finset.Icc 1 Q, (((W * q + r : ℕ) : ℝ))⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun q hq => ?_
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hqpos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
          rw [one_div, ← mul_inv]
          refine inv_anti₀ (by positivity) ?_
          push_cast
          have hrW' : (r : ℝ) ≤ (W : ℝ) := by exact_mod_cast hrW
          nlinarith
        have h2 : ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹ - 1 ≤
            ∑ q ∈ Finset.Icc 1 Q, (((q + 1 : ℕ) : ℝ))⁻¹ := by
          by_cases hQ0 : Q = 0
          · rw [hQ0]; simp
          · have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ0
            have hshift : ∑ q ∈ Finset.Icc 1 Q, (((q + 1 : ℕ) : ℝ))⁻¹ =
                ∑ k ∈ Finset.Icc 2 (Q + 1), ((k : ℝ))⁻¹ := by
              refine Finset.sum_bij (fun q _ => q + 1) ?_ ?_ ?_ ?_
              · intro q hq; simp only [Finset.mem_Icc] at hq ⊢; omega
              · intro _ _ _ _ h; omega
              · intro k hk; simp only [Finset.mem_Icc] at hk
                exact ⟨k - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro q _; rfl
            rw [hshift]
            have hI1 : Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
              ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            have hI2 : Finset.Icc 2 (Q + 1) = insert (Q + 1) (Finset.Icc 2 Q) := by
              ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hI1, Finset.sum_insert (by simp), hI2, Finset.sum_insert (by simp)]
            simp only [Nat.cast_one, inv_one]
            have : (0 : ℝ) ≤ (((Q + 1 : ℕ) : ℝ))⁻¹ := by positivity
            linarith
        exact le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
      -- Compare `∑_{q=1}^Q 1/q` with `log(x / W)`!
      have hQ_ub : (Q : ℝ) ≤ x / (W : ℝ) := by
        rw [le_div_iff₀ hW_pos]
        have h1 : Q * W ≤ ⌊x⌋₊ := by
          calc Q * W ≤ ⌊x⌋₊ - r := Nat.div_mul_le_self _ _
            _ ≤ ⌊x⌋₊ := Nat.sub_le _ _
        have h1R : (Q : ℝ) * (W : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
        exact h1R.trans (Nat.floor_le (by linarith))
      have hQ_lb : x / (W : ℝ) - 3 ≤ (Q : ℝ) := by
        have h1 : ⌊x⌋₊ - r < (Q + 1) * W := by
          have := Nat.lt_div_mul_add (a := ⌊x⌋₊ - r) hW
          have hmul : (Q + 1) * W = Q * W + W := by ring
          dsimp only [Q] at hmul ⊢
          omega
        have h2 : x - 1 - (W : ℝ) < ((Q + 1 : ℕ) : ℝ) * (W : ℝ) := by
          have hfl : x - 1 < (⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
          have h1R : ((⌊x⌋₊ - r : ℕ) : ℝ) < ((Q + 1 : ℕ) : ℝ) * (W : ℝ) := by exact_mod_cast h1
          rw [Nat.cast_sub hfl_ge] at h1R
          have hrW' : (r : ℝ) ≤ (W : ℝ) := by exact_mod_cast hrW
          linarith
        have h3 : (x - 1 - (W : ℝ)) / (W : ℝ) < (Q : ℝ) + 1 := by
          rw [div_lt_iff₀ hW_pos]; push_cast at h2; linarith
        have h4 : (1 : ℝ) / (W : ℝ) ≤ 1 := by rw [div_le_one hW_pos]; exact_mod_cast hW
        have h5 : (x - 1 - (W : ℝ)) / (W : ℝ) = x / (W : ℝ) - 1 / (W : ℝ) - 1 := by
          field_simp [hW_pos.ne']
        linarith
      have hlog_xW : Real.log (x / (W : ℝ)) = Real.log x - Real.log (W : ℝ) :=
        Real.log_div (by linarith) hW_pos.ne'
      have hxW1 : 1 ≤ x / (W : ℝ) := (one_le_div hW_pos).mpr hxW
      have hr_inv_le : (((W * 0 + r : ℕ) : ℝ))⁻¹ ≤ 1 := by
        simp only [mul_zero, zero_add]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast hr1)
      have hr_inv_nn : (0 : ℝ) ≤ (((W * 0 + r : ℕ) : ℝ))⁻¹ := by positivity
      have hW_inv_le : (1 : ℝ) / (W : ℝ) ≤ 1 := by rw [div_le_one hW_pos]; exact_mod_cast hW
      have hlogW_nn : 0 ≤ Real.log (W : ℝ) := Real.log_nonneg (by exact_mod_cast hW)
      by_cases hQ0 : Q = 0
      · -- `Q = 0`, so `x / W ≤ 3`, `log(x / W) ≤ 2`, and sum is just `1/r ∈ [0, 1]`
        have hxW3 : x / (W : ℝ) ≤ 3 := by rw [hQ0, Nat.cast_zero] at hQ_lb; linarith
        have hlog3 : Real.log (x / (W : ℝ)) ≤ 2 := by
          calc Real.log (x / (W : ℝ)) ≤ x / (W : ℝ) - 1 :=
                Real.log_le_sub_one_of_pos (by linarith)
            _ ≤ 2 := by linarith
        have hIcc0 : Finset.Icc 1 Q = ∅ := by rw [hQ0]; rfl
        rw [hIcc0, Finset.sum_empty, add_zero]
        have hlogx_le : Real.log x ≤ 2 + Real.log (W : ℝ) := by linarith
        have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
        have h1 : (1 / (W : ℝ)) * Real.log x ≤ 2 + Real.log (W : ℝ) := by
          calc (1 / (W : ℝ)) * Real.log x ≤ 1 * Real.log x :=
                mul_le_mul_of_nonneg_right hW_inv_le hlogx_nn
            _ = Real.log x := one_mul _
            _ ≤ 2 + Real.log (W : ℝ) := hlogx_le
        have h2 : 0 ≤ (1 / (W : ℝ)) * Real.log x := mul_nonneg (by positivity) hlogx_nn
        rw [abs_le]; constructor <;> linarith
      · have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ0
        have hharm := abs_harmonic_sub_log_le_one (x := (Q : ℝ)) (by exact_mod_cast hQ1)
        rw [Nat.floor_natCast] at hharm
        have hharm_lo : Real.log (Q : ℝ) - 1 ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹ :=
          (abs_le.mp hharm).1 |> fun h => by linarith
        have hharm_hi : ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹ ≤ Real.log (Q : ℝ) + 1 :=
          (abs_le.mp hharm).2 |> fun h => by linarith
        have hlogQ_hi : Real.log (Q : ℝ) ≤ Real.log (x / (W : ℝ)) :=
          Real.log_le_log (Nat.cast_pos.mpr hQ1) hQ_ub
        -- Lower bound `log(Q) ≥ log(x/W) - 2`: since `Q + 3 ≥ x/W` and `Q ≥ 1`, `x/W ≤ 4 Q`,
        -- so `log(x/W) - log Q ≤ log 4 = 2 log 2 ≤ 2`!
        have hlogQ_lo : Real.log (x / (W : ℝ)) - 2 ≤ Real.log (Q : ℝ) := by
          have h4Q : x / (W : ℝ) ≤ 4 * (Q : ℝ) := by
            have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
            linarith
          have hlog4 : Real.log (x / (W : ℝ)) ≤ Real.log (4 * (Q : ℝ)) :=
            Real.log_le_log (by linarith) h4Q
          rw [Real.log_mul (by norm_num) (Nat.cast_pos.mpr hQ1).ne'] at hlog4
          have h4 : Real.log 4 ≤ 2 := by
            have h2 : Real.log 2 ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
              linarith
            have h4eq : Real.log (4 : ℝ) = Real.log (2 * 2) := by norm_num
            rw [h4eq, Real.log_mul (by norm_num) (by norm_num)]; linarith
          linarith
        have hsum_hi : (((W * 0 + r : ℕ) : ℝ))⁻¹ + ∑ q ∈ Finset.Icc 1 Q, (((W * q + r : ℕ) : ℝ))⁻¹ ≤
            (1 / (W : ℝ)) * Real.log x + 2 := by
          have h1 : (1 / (W : ℝ)) * ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹ ≤
              (1 / (W : ℝ)) * (Real.log x + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith
          have h2 : (1 / (W : ℝ)) * (Real.log x + 1) = (1 / (W : ℝ)) * Real.log x + 1 / (W : ℝ) := by
            ring
          linarith
        have hsum_lo : (1 / (W : ℝ)) * Real.log x - (4 + Real.log (W : ℝ)) ≤
            (((W * 0 + r : ℕ) : ℝ))⁻¹ + ∑ q ∈ Finset.Icc 1 Q, (((W * q + r : ℕ) : ℝ))⁻¹ := by
          have h1 : (1 / (W : ℝ)) * (Real.log x - Real.log (W : ℝ) - 4) ≤
              (1 / (W : ℝ)) * (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ))⁻¹ - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h2 : (1 / (W : ℝ)) * (Real.log (W : ℝ) + 4) ≤ Real.log (W : ℝ) + 4 := by
            calc (1 / (W : ℝ)) * (Real.log (W : ℝ) + 4)
                ≤ 1 * (Real.log (W : ℝ) + 4) :=
                  mul_le_mul_of_nonneg_right hW_inv_le (by linarith)
              _ = Real.log (W : ℝ) + 4 := one_mul _
          have h3 : (1 / (W : ℝ)) * (Real.log x - Real.log (W : ℝ) - 4) =
              (1 / (W : ℝ)) * Real.log x - (1 / (W : ℝ)) * (Real.log (W : ℝ) + 4) := by ring
          linarith
        rw [abs_le]; constructor <;> linarith
  have hmain : ((W.totient : ℝ) / (W : ℝ)) * Real.log x =
      ∑ _r ∈ Rset, (1 / (W : ℝ)) * Real.log x := by
    rw [Finset.sum_const, hRcard, nsmul_eq_mul]; ring
  rw [hmain, ← Finset.sum_sub_distrib]
  calc |∑ r ∈ Rset, ((∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => m ≡ r [MOD W]), ((m : ℝ))⁻¹) -
          (1 / (W : ℝ)) * Real.log x)|
      ≤ ∑ r ∈ Rset, |(∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => m ≡ r [MOD W]), ((m : ℝ))⁻¹) -
          (1 / (W : ℝ)) * Real.log x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ Rset, (4 + Real.log (W : ℝ)) := Finset.sum_le_sum hres
    _ = (W.totient : ℝ) * (4 + Real.log (W : ℝ)) := by rw [Finset.sum_const, hRcard, nsmul_eq_mul]
    _ ≤ C := by dsimp only [C]; linarith

/-- Telescoping bound: `∑_{a=1}^N a^{-3/2} ≤ 3`. -/
lemma sum_rpow_neg_three_halves_le (N : ℕ) :
    ∑ a ∈ Finset.Icc 1 N, ((a : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 3 := by
  by_cases hN0 : N = 0
  · subst hN0; simp
  · have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
    have hstep : ∀ m : ℕ, 2 ≤ m →
        ((m : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 2 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 2 / Real.sqrt (m : ℝ) := by
      intro m hm
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hsm_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
      have hsm1_pos : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hm1_pos
      have hsub : (m : ℝ) - ((m - 1 : ℕ) : ℝ) = 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring
      have hdiff : Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ) =
          1 / (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)) := by
        have hpos_sum : 0 < Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ) := by positivity
        rw [eq_div_iff hpos_sum.ne']
        have hsq : (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) *
            (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)) =
            (Real.sqrt (m : ℝ)) ^ 2 - (Real.sqrt ((m - 1 : ℕ) : ℝ)) ^ 2 := by ring
        rw [hsq, Real.sq_sqrt hm_pos.le, Real.sq_sqrt hm1_pos.le, hsub]
      have hrhs : 2 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 2 / Real.sqrt (m : ℝ) =
          2 / (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) *
            (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ))) := by
        have h1 : 2 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 2 / Real.sqrt (m : ℝ) =
            2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) /
              (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)) := by
          field_simp [hsm_pos.ne', hsm1_pos.ne']
        rw [h1, hdiff]
        have hpos_sum : 0 < Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ) := by positivity
        field_simp [hsm_pos.ne', hsm1_pos.ne', hpos_sum.ne']
      rw [hrhs]
      have hle_sqrt : Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le m 1)
      have hden_le : Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) *
          (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)) ≤ 2 * ((m : ℝ) * Real.sqrt (m : ℝ)) := by
        have h1 : Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
          calc Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)
              ≤ Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) :=
                mul_le_mul_of_nonneg_right hle_sqrt hsm_pos.le
            _ = (m : ℝ) := Real.mul_self_sqrt hm_pos.le
        have h2 : Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
          linarith
        calc Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) *
              (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ))
            ≤ (m : ℝ) * (2 * Real.sqrt (m : ℝ)) :=
              mul_le_mul h1 h2 (by positivity) hm_pos.le
          _ = 2 * ((m : ℝ) * Real.sqrt (m : ℝ)) := by ring
      have hlhs : (m : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
        rw [Real.rpow_neg hm_pos.le, one_div]
        congr 1
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm_pos, Real.rpow_one,
          Real.sqrt_eq_rpow]
      rw [hlhs]
      have hden_pos : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) *
          (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)) := by positivity
      calc 1 / ((m : ℝ) * Real.sqrt (m : ℝ))
          = 2 / (2 * ((m : ℝ) * Real.sqrt (m : ℝ))) := by field_simp [hm_pos.ne', hsm_pos.ne']
        _ ≤ 2 / (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) *
              (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ))) :=
            div_le_div_of_nonneg_left (by norm_num) hden_pos hden_le
    -- Prove by induction on `N ≥ 1` that `∑_{a=1}^N a^{-3/2} ≤ 3 - 2 / √N`
    suffices hstrong : ∑ a ∈ Finset.Icc 1 N, ((a : ℝ) ^ (-(3 / 2 : ℝ))) ≤
        3 - 2 / Real.sqrt (N : ℝ) by
      have : 0 ≤ 2 / Real.sqrt (N : ℝ) := by positivity
      linarith
    induction N, hN1 using Nat.le_induction with
    | base => simp; norm_num
    | succ m hm ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hs := hstep (m + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hs
      have ih' := ih (by omega)
      linarith

/-- Squarefull decomposition: if every prime factor of `q ≥ 1` has multiplicity `≥ 2`, then
there exist `a, b ≥ 1` with `q = a^2 * b^3`. -/
lemma exists_sq_mul_cube_of_squarefull {q : ℕ} (hq : 0 < q)
    (hsf : ∀ p ∈ q.primeFactors, 2 ≤ q.factorization p) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ q = a ^ 2 * b ^ 3 := by
  let b := ∏ p ∈ q.primeFactors.filter (fun p => Odd (q.factorization p)), p
  have hb_pos : 1 ≤ b :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  let a := ∏ p ∈ q.primeFactors,
      p ^ ((q.factorization p - if Odd (q.factorization p) then 3 else 0) / 2)
  have ha_pos : 1 ≤ a :=
    Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  refine ⟨a, b, ha_pos, hb_pos, ?_⟩
  have hq_fac : q = ∏ p ∈ q.primeFactors, p ^ (q.factorization p) :=
    (Nat.factorization_prod_pow_eq_self hq.ne').symm
  have hb3 : b ^ 3 = ∏ p ∈ q.primeFactors,
      p ^ (if Odd (q.factorization p) then 3 else 0) := by
    dsimp only [b]
    rw [← Finset.prod_pow, Finset.prod_filter]
    refine Finset.prod_congr rfl fun p _ => by split_ifs <;> simp
  have ha2 : a ^ 2 = ∏ p ∈ q.primeFactors,
      p ^ (2 * ((q.factorization p - if Odd (q.factorization p) then 3 else 0) / 2)) := by
    dsimp only [a]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => by rw [← pow_mul, mul_comm]
  rw [ha2, hb3, ← Finset.prod_mul_distrib]
  conv_lhs => rw [hq_fac]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_add]
  congr 1
  have hge2 : 2 ≤ q.factorization p := hsf p hp
  split_ifs with hodd
  · obtain ⟨t, ht⟩ := hodd
    have ht1 : 1 ≤ t := by omega
    omega
  · have heven : Even (q.factorization p) := Nat.not_odd_iff_even.mp hodd
    obtain ⟨t, ht⟩ := heven
    omega

/-- Bound on `∑_{k=2}^K (log k + 1) / (k * rad k) ≤ 36` uniformly in `K`. -/
lemma sum_log_div_mul_rad_le (K : ℕ) :
    ∑ k ∈ Finset.Icc 2 K, (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ) ≤ 36 := by
  -- For each `k ∈ Icc 2 K`, `q = k * rad k` is squarefull (`v_p(q) ≥ 2`), and `k ↦ q` is injective
  have hrad_eq : ∀ k : ℕ, 1 ≤ k → rad (k * rad k) = rad k := by
    intro k hk
    have hk0 : k ≠ 0 := by omega
    have hr0 : rad k ≠ 0 := (rad_pos k).ne'
    have hpf : (k * rad k).primeFactors = k.primeFactors := by
      rw [Nat.primeFactors_mul hk0 hr0, primeFactors_rad, Finset.union_idempotent]
    change ∏ p ∈ (k * rad k).primeFactors, p = ∏ p ∈ k.primeFactors, p
    rw [hpf]
  have hinj : Set.InjOn (fun k => k * rad k) (Finset.Icc 2 K : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk₁ hk₂
    dsimp only at heq
    have hr1 : rad k₁ = rad k₂ := by
      have h1 := hrad_eq k₁ (by omega)
      have h2 := hrad_eq k₂ (by omega)
      rw [← h1, heq, h2]
    rw [hr1] at heq
    exact Nat.eq_of_mul_eq_mul_right (rad_pos k₂) heq
  -- Each `q = k * rad k` decomposes as `a^2 * b^3` with `1 ≤ a, b ≤ q ≤ K^2`
  have hdecomp : ∀ k ∈ Finset.Icc 2 K,
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a ≤ K * K ∧ b ≤ K * K ∧ k * rad k = a ^ 2 * b ^ 3 := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hq_pos : 0 < k * rad k := Nat.mul_pos (by omega) (rad_pos k)
    have hsf : ∀ p ∈ (k * rad k).primeFactors, 2 ≤ (k * rad k).factorization p := by
      intro p hp
      rw [Nat.primeFactors_mul (by omega) (rad_pos k).ne', primeFactors_rad,
        Finset.union_idempotent] at hp
      rw [Nat.factorization_mul (by omega) (rad_pos k).ne', Finsupp.add_apply]
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have h1 : 1 ≤ k.factorization p :=
        (hpp.dvd_iff_one_le_factorization (by omega)).mp (Nat.dvd_of_mem_primeFactors hp)
      have h2 : 1 ≤ (rad k).factorization p :=
        (hpp.dvd_iff_one_le_factorization (rad_pos k).ne').mp
          (Finset.dvd_prod_of_mem _ hp)
      omega
    obtain ⟨a, b, ha1, hb1, hab⟩ := exists_sq_mul_cube_of_squarefull hq_pos hsf
    have hq_le : k * rad k ≤ K * K :=
      Nat.mul_le_mul hkK ((rad_le (by omega)).trans hkK)
    have ha_le : a ≤ K * K := by
      have : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) a
      have : a ^ 2 ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_right _ (pow_pos hb1 3)
      omega
    have hb_le : b ≤ K * K := by
      have : b ≤ b ^ 3 := Nat.le_self_pow (by norm_num) b
      have : b ^ 3 ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_left _ (pow_pos ha1 2)
      omega
    exact ⟨a, b, ha1, hb1, ha_le, hb_le, hab⟩
  choose fa fb hfa1 hfb1 hfaK hfbK hfab using fun k (hk : k ∈ Finset.Icc 2 K) => hdecomp k hk
  -- Termwise bound: `(log k + 1) / q ≤ 4 * a^{-3/2} * b^{-3/2}`
  have hterm : ∀ k (hk : k ∈ Finset.Icc 2 K),
      (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ) ≤
        4 * ((fa k hk : ℝ) ^ (-(3 / 2 : ℝ))) * ((fb k hk : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hq_pos : (0 : ℝ) < ((k * rad k : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.mul_pos (by omega) (rad_pos k))
    have hk_le_q : (k : ℝ) ≤ ((k * rad k : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_right k (rad_pos k)
    have hlog_le : Real.log (k : ℝ) + 1 ≤ 4 * (((k * rad k : ℕ) : ℝ) ^ (1 / 4 : ℝ)) := by
      have h1 : Real.log (k : ℝ) ≤ Real.log ((k * rad k : ℕ) : ℝ) :=
        Real.log_le_log (Nat.cast_pos.mpr (by omega)) hk_le_q
      have h2 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hq_pos (1 / 4 : ℝ))
      rw [Real.log_rpow hq_pos] at h2
      linarith
    have hdiv : (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ) ≤
        4 * (((k * rad k : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) := by
      calc (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ)
          ≤ 4 * (((k * rad k : ℕ) : ℝ) ^ (1 / 4 : ℝ)) / ((k * rad k : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hlog_le hq_pos.le
        _ = 4 * ((((k * rad k : ℕ) : ℝ) ^ (1 / 4 : ℝ)) / (((k * rad k : ℕ) : ℝ) ^ (1 : ℝ))) := by
            rw [Real.rpow_one, mul_div_assoc]
        _ = 4 * (((k * rad k : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) := by
            rw [← Real.rpow_sub hq_pos]; norm_num
    have ha_pos : (0 : ℝ) < (fa k hk : ℝ) := Nat.cast_pos.mpr (hfa1 k hk)
    have hb_pos : (0 : ℝ) < (fb k hk : ℝ) := Nat.cast_pos.mpr (hfb1 k hk)
    have hq_eq : ((k * rad k : ℕ) : ℝ) = (fa k hk : ℝ) ^ (2 : ℝ) * (fb k hk : ℝ) ^ (3 : ℝ) := by
      rw [hfab k hk]; push_cast; norm_cast
    have hrpow : ((k * rad k : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) =
        (fa k hk : ℝ) ^ (-(3 / 2 : ℝ)) * (fb k hk : ℝ) ^ (-(9 / 4 : ℝ)) := by
      rw [hq_eq, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul ha_pos.le, ← Real.rpow_mul hb_pos.le]
      norm_num
    have hb_le : (fb k hk : ℝ) ^ (-(9 / 4 : ℝ)) ≤ (fb k hk : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hfb1 k hk) (by norm_num)
    calc (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ)
        ≤ 4 * (((k * rad k : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) := hdiv
      _ = 4 * ((fa k hk : ℝ) ^ (-(3 / 2 : ℝ)) * (fb k hk : ℝ) ^ (-(9 / 4 : ℝ))) := by rw [hrpow]
      _ ≤ 4 * ((fa k hk : ℝ) ^ (-(3 / 2 : ℝ)) * (fb k hk : ℝ) ^ (-(3 / 2 : ℝ))) := by
          gcongr
      _ = 4 * ((fa k hk : ℝ) ^ (-(3 / 2 : ℝ))) * ((fb k hk : ℝ) ^ (-(3 / 2 : ℝ))) := by ring
  -- Inject `Icc 2 K` into `(Icc 1 (K*K)) ×ˢ (Icc 1 (K*K))` via `k ↦ (fa k, fb k)`
  let embed : ℕ → ℕ × ℕ := fun k =>
    if hk : k ∈ Finset.Icc 2 K then (fa k hk, fb k hk) else (0, 0)
  have hembed_inj : Set.InjOn embed (Finset.Icc 2 K : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hk1' : k₁ ∈ Finset.Icc 2 K := hk₁
    have hk2' : k₂ ∈ Finset.Icc 2 K := hk₂
    simp only [embed, dif_pos hk1', dif_pos hk2', Prod.mk.injEq] at heq
    have hq_eq : k₁ * rad k₁ = k₂ * rad k₂ := by
      rw [hfab k₁ hk1', hfab k₂ hk2', heq.1, heq.2]
    exact hinj hk₁ hk₂ hq_eq
  have hsum1 : ∑ k ∈ Finset.Icc 2 K, (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.Icc 2 K,
        4 * (((embed k).1 : ℝ) ^ (-(3 / 2 : ℝ))) * (((embed k).2 : ℝ) ^ (-(3 / 2 : ℝ))) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have h := hterm k hk
    simpa only [embed, dif_pos hk] using h
  have hsum2 : ∑ k ∈ Finset.Icc 2 K,
        4 * (((embed k).1 : ℝ) ^ (-(3 / 2 : ℝ))) * (((embed k).2 : ℝ) ^ (-(3 / 2 : ℝ))) =
      ∑ p ∈ (Finset.Icc 2 K).image embed,
        4 * ((p.1 : ℝ) ^ (-(3 / 2 : ℝ))) * ((p.2 : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Finset.sum_image (f := fun p : ℕ × ℕ =>
      4 * ((p.1 : ℝ) ^ (-(3 / 2 : ℝ))) * ((p.2 : ℝ) ^ (-(3 / 2 : ℝ))))
      (fun a ha b hb hab => hembed_inj ha hb hab)).symm
  have hsub : (Finset.Icc 2 K).image embed ⊆ Finset.Icc 1 (K * K) ×ˢ Finset.Icc 1 (K * K) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
    dsimp only [embed]; rw [dif_pos hk]
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨hfa1 k hk, hfaK k hk⟩, ⟨hfb1 k hk, hfbK k hk⟩⟩
  have hsum3 : ∑ p ∈ (Finset.Icc 2 K).image embed,
        4 * ((p.1 : ℝ) ^ (-(3 / 2 : ℝ))) * ((p.2 : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      ∑ p ∈ Finset.Icc 1 (K * K) ×ˢ Finset.Icc 1 (K * K),
        4 * ((p.1 : ℝ) ^ (-(3 / 2 : ℝ))) * ((p.2 : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hprod : ∑ p ∈ Finset.Icc 1 (K * K) ×ˢ Finset.Icc 1 (K * K),
        4 * ((p.1 : ℝ) ^ (-(3 / 2 : ℝ))) * ((p.2 : ℝ) ^ (-(3 / 2 : ℝ))) =
      4 * (∑ a ∈ Finset.Icc 1 (K * K), ((a : ℝ) ^ (-(3 / 2 : ℝ)))) *
          (∑ b ∈ Finset.Icc 1 (K * K), ((b : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    rw [Finset.sum_product]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hb3 := sum_rpow_neg_three_halves_le (K * K)
  have hnn : 0 ≤ ∑ a ∈ Finset.Icc 1 (K * K), ((a : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ k ∈ Finset.Icc 2 K, (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ)
      ≤ 4 * (∑ a ∈ Finset.Icc 1 (K * K), ((a : ℝ) ^ (-(3 / 2 : ℝ)))) *
          (∑ b ∈ Finset.Icc 1 (K * K), ((b : ℝ) ^ (-(3 / 2 : ℝ)))) := by
        linarith [hsum1, hsum2, hsum3, hprod]
    _ ≤ 4 * 3 * 3 := by nlinarith
    _ = 36 := by norm_num

/-- **1D Multiplicative Asymptotic for `aPhi W`**:
`∑_{1 ≤ n ≤ x, sqfree, (n, W) = 1} 1 / φ(n) = (φ(W)/W) * log x + O_W(1)`. -/
theorem sum_aPhi_asymp (W : ℕ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, aPhi W n) - ((W.totient : ℝ) / (W : ℝ)) * Real.log x| ≤ C := by
  obtain ⟨C₀, hC₀_pos, hcop⟩ := sum_inv_coprime_asymp W hW
  refine ⟨C₀ + 36, by linarith, fun x hx => ?_⟩
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hx)
  set S_cop := (Finset.Icc 1 N).filter (fun m => Nat.Coprime m W)
  set S_sf := (Finset.Icc 1 N).filter (fun n => Squarefree n ∧ Nat.Coprime n W)
  have haPhi_eq : ∑ n ∈ Finset.Icc 1 N, aPhi W n = ∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹ := by
    unfold aPhi
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [haPhi_eq]
  -- Truncated inverse totient for squarefree `n` at exponent cutoff `M`:
  let truncInvPhi : ℕ → ℕ → ℝ := fun M n =>
    ∏ p ∈ n.primeFactors, ∑ e ∈ Finset.Icc 1 M, (((p : ℝ) ^ e))⁻¹
  -- Exact closed form of the inner geometric sum
  have hgeom : ∀ (p M : ℕ), p.Prime →
      ∑ e ∈ Finset.Icc 1 M, (((p : ℝ) ^ e))⁻¹ =
        (1 - (((p : ℝ) ^ M))⁻¹) * (((p : ℝ) - 1))⁻¹ := by
    intro p M hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpne : (p : ℝ) ≠ 0 := by linarith
    induction M with
    | zero => simp
    | succ m ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext e; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), ih]
      field_simp [hpm1, hpne, pow_ne_zero m hpne, pow_ne_zero (m + 1) hpne]
      rw [pow_succ]; ring
  have htrunc_le : ∀ M n, Squarefree n → truncInvPhi M n ≤ ((n.totient : ℝ))⁻¹ := by
    intro M n hn
    have hn0 : n ≠ 0 := hn.ne_zero
    have hphi : (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
      have hnat : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
        rw [Nat.totient_eq_prod_factorization hn0]
        simp only [Finsupp.prod, Nat.support_factorization]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have h1 : 1 ≤ n.factorization p :=
          (hpp.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp)
        have h2 : n.factorization p ≤ 1 := by
          by_contra hgt; push Not at hgt
          have hp2 : p * p ∣ n := by
            simpa [sq] using (hpp.pow_dvd_iff_le_factorization hn0).mpr (by omega : 2 ≤ _)
          exact hpp.ne_one (Nat.isUnit_iff.mp (hn p hp2))
        have heq : n.factorization p = 1 := by omega
        rw [heq, pow_zero, one_mul]
      rw [hnat, Nat.cast_prod]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
      rw [Nat.cast_sub hp1, Nat.cast_one]
    rw [hphi, ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [hgeom p M hpp]
    have h1 : 1 - (((p : ℝ) ^ M))⁻¹ ≤ 1 := by
      have : (0 : ℝ) ≤ (((p : ℝ) ^ M))⁻¹ := by positivity
      linarith
    have h2 : (0 : ℝ) ≤ (((p : ℝ) - 1))⁻¹ := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      exact inv_nonneg.mpr (by linarith)
    calc (1 - (((p : ℝ) ^ M))⁻¹) * (((p : ℝ) - 1))⁻¹
        ≤ 1 * (((p : ℝ) - 1))⁻¹ := mul_le_mul_of_nonneg_right h1 h2
      _ = (((p : ℝ) - 1))⁻¹ := one_mul _
  -- Expand `truncInvPhi M n` as a sum over `m` with `rad m = n` and all `v_p(m) ≤ M`
  let fiberM : ℕ → ℕ → Finset ℕ := fun M n =>
    (Finset.Icc 1 (n ^ M)).filter (fun m => rad m = n ∧ ∀ p ∈ n.primeFactors, m.factorization p ≤ M)
  have htrunc_eq_fiber : ∀ M n, Squarefree n →
      truncInvPhi M n = ∑ m ∈ fiberM M n, ((m : ℝ))⁻¹ := by
    intro M n hn
    have hn0 : n ≠ 0 := hn.ne_zero
    dsimp only [truncInvPhi]
    rw [Finset.prod_sum]
    -- Bijection between `f ∈ pi n.primeFactors (fun _ => Icc 1 M)` and `m ∈ fiberM M n`
    refine Finset.sum_bij (fun f _ => ∏ p ∈ n.primeFactors.attach, p.1 ^ (f p.1 p.2)) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_pi] at hf
      set m := ∏ p ∈ n.primeFactors.attach, p.1 ^ (f p.1 p.2)
      have hm_pos : 0 < m :=
        Finset.prod_pos fun p _ => pow_pos (Nat.prime_of_mem_primeFactors p.2).pos _
      have hm_le : m ≤ n ^ M := by
        calc m ≤ ∏ p ∈ n.primeFactors.attach, p.1 ^ M := by
              refine Finset.prod_le_prod' fun p _ =>
                Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors p.2).pos
                  (Finset.mem_Icc.mp (hf p.1 p.2)).2
          _ = (∏ p ∈ n.primeFactors, p) ^ M := by
              rw [Finset.prod_pow]; congr 1; exact Finset.prod_attach n.primeFactors id
          _ = n ^ M := by rw [← rad, rad_eq_self_of_squarefree hn]
      have hfac_m : ∀ q : ℕ, m.factorization q =
          if hq : q ∈ n.primeFactors then f q hq else 0 := by
        intro q
        dsimp only [m]
        rw [Nat.factorization_prod (fun p _ =>
          pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero), Finsupp.finset_sum_apply]
        by_cases hq : q ∈ n.primeFactors
        · rw [dif_pos hq, Finset.sum_eq_single ⟨q, hq⟩]
          · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
              (Nat.prime_of_mem_primeFactors hq).factorization_self, mul_one]
          · intro p _ hne
            have hpq : q ≠ p.1 := fun h => hne (Subtype.ext h.symm)
            rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
              (Nat.prime_of_mem_primeFactors p.2).factorization, Finsupp.single_eq_of_ne hpq,
              mul_zero]
          · intro hmem; exact absurd (Finset.mem_attach _ _) hmem
        · rw [dif_neg hq]
          refine Finset.sum_eq_zero fun p _ => ?_
          have hpq : q ≠ p.1 := fun h => hq (h ▸ p.2)
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
            (Nat.prime_of_mem_primeFactors p.2).factorization, Finsupp.single_eq_of_ne hpq,
            mul_zero]
      have hpf_m : m.primeFactors = n.primeFactors := by
        ext q
        rw [← Nat.support_factorization, Finsupp.mem_support_iff, hfac_m q]
        by_cases hq : q ∈ n.primeFactors
        · rw [dif_pos hq]
          have hge1 : 1 ≤ f q hq := (Finset.mem_Icc.mp (hf q hq)).1
          exact ⟨fun _ => hq, fun _ => by omega⟩
        · rw [dif_neg hq]; simp [hq]
      simp only [fiberM, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hm_pos, hm_le⟩, ?_, ?_⟩
      · unfold rad; rw [hpf_m]; exact rad_eq_self_of_squarefree hn
      · intro p hp; rw [hfac_m p, dif_pos hp]; exact (Finset.mem_Icc.mp (hf p hp)).2
    · intro f₁ hf₁ f₂ hf₂ heq
      -- Both give the same `m`, hence same factorization on every `p ∈ n.primeFactors`
      have hfac_eq : ∀ (f : ∀ a ∈ n.primeFactors, ℕ), f ∈ n.primeFactors.pi (fun _ => Finset.Icc 1 M) →
          ∀ q (hq : q ∈ n.primeFactors),
            (∏ p ∈ n.primeFactors.attach, p.1 ^ (f p.1 p.2)).factorization q = f q hq := by
        intro f hf q hq
        rw [Nat.factorization_prod (fun p _ =>
          pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero), Finsupp.finset_sum_apply,
          Finset.sum_eq_single ⟨q, hq⟩]
        · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
            (Nat.prime_of_mem_primeFactors hq).factorization_self, mul_one]
        · intro p _ hne
          have hpq : q ≠ p.1 := fun h => hne (Subtype.ext h.symm)
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
            (Nat.prime_of_mem_primeFactors p.2).factorization, Finsupp.single_eq_of_ne hpq,
            mul_zero]
        · intro hmem; exact absurd (Finset.mem_attach _ _) hmem
      funext p hp
      have h1 := hfac_eq f₁ hf₁ p hp
      have h2 := hfac_eq f₂ hf₂ p hp
      rw [heq] at h1
      linarith
    · intro m hm
      simp only [fiberM, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, _⟩, hrad, hleM⟩ := hm
      have hpf_eq : m.primeFactors = n.primeFactors := by
        rw [← primeFactors_rad m, hrad]
      refine ⟨fun p _ => m.factorization p, ?_, ?_⟩
      · simp only [Finset.mem_pi, Finset.mem_Icc]
        intro p hp
        refine ⟨?_, hleM p hp⟩
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors (hpf_eq.symm ▸ hp)
        exact (hpp.dvd_iff_one_le_factorization (by omega)).mp hpm
      · have hprod : ∏ p ∈ n.primeFactors.attach, p.1 ^ (m.factorization p.1) =
            ∏ p ∈ m.primeFactors, p ^ (m.factorization p) := by
          rw [hpf_eq]; exact Finset.prod_attach _ (fun p => p ^ (m.factorization p))
        rw [hprod]
        exact Nat.factorization_prod_pow_eq_self (by omega)
    · intro f _
      have hcast : ((∏ x ∈ n.primeFactors.attach, x.1 ^ (f x.1 x.2) : ℕ) : ℝ) =
          ∏ x ∈ n.primeFactors.attach, ((x.1 : ℝ) ^ (f x.1 x.2)) := by
        push_cast; rfl
      rw [hcast, Finset.prod_inv_distrib]
  -- Lower bound: `∑ m ∈ S_cop, 1/m ≤ ∑ n ∈ S_sf, 1/φ(n)`
  have hlower : ∑ m ∈ S_cop, ((m : ℝ))⁻¹ ≤ ∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹ := by
    have hM_mem : ∀ m ∈ S_cop, m ∈ fiberM (N + 1) (rad m) := by
      intro m hm
      simp only [S_cop, Finset.mem_filter, Finset.mem_Icc] at hm
      simp only [fiberM, Finset.mem_filter, Finset.mem_Icc]
      have hm_le_pow : m ≤ (rad m) ^ (N + 1) := by
        by_cases hm1 : m = 1
        · subst hm1; simp [rad]
        · have hrad2 : 2 ≤ rad m := by
            obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
            have hpr : p ∣ rad m := Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩)
            exact le_trans hp.two_le (Nat.le_of_dvd (rad_pos m) hpr)
          calc m ≤ N := hm.1.2
            _ ≤ 2 ^ (N + 1) := by
                have := Nat.lt_two_pow_self (n := N + 1); omega
            _ ≤ (rad m) ^ (N + 1) := Nat.pow_le_pow_left hrad2 _
      refine ⟨⟨hm.1.1, hm_le_pow⟩, trivial, fun p hp => ?_⟩
      rw [primeFactors_rad] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpow_le : p ^ (m.factorization p) ≤ m :=
        Nat.le_of_dvd hm.1.1 (Nat.ordProj_dvd m p)
      have h2_le : 2 ^ (m.factorization p) ≤ m :=
        le_trans (Nat.pow_le_pow_left hpp.two_le _) hpow_le
      have hlt : m.factorization p < 2 ^ (m.factorization p) := Nat.lt_two_pow_self
      omega
    have hsub : S_cop ⊆ S_sf.biUnion (fun n => fiberM (N + 1) n) := by
      intro m hm
      rw [Finset.mem_biUnion]
      simp only [S_cop, Finset.mem_filter, Finset.mem_Icc] at hm
      refine ⟨rad m, ?_, hM_mem m (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hm.1, hm.2⟩)⟩
      simp only [S_sf, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨rad_pos m, (rad_le hm.1.1).trans hm.1.2⟩, squarefree_rad m,
        (coprime_rad_iff (by omega)).mpr hm.2⟩
    have hdisj : Set.PairwiseDisjoint (S_sf : Set ℕ) (fun n => fiberM (N + 1) n) := by
      intro n₁ _ n₂ _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro m hm₁ hm₂
      simp only [fiberM, Finset.mem_filter] at hm₁ hm₂
      exact hne (hm₁.2.1.symm.trans hm₂.2.1)
    calc ∑ m ∈ S_cop, ((m : ℝ))⁻¹
        ≤ ∑ m ∈ S_sf.biUnion (fun n => fiberM (N + 1) n), ((m : ℝ))⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = ∑ n ∈ S_sf, ∑ m ∈ fiberM (N + 1) n, ((m : ℝ))⁻¹ := Finset.sum_biUnion hdisj
      _ = ∑ n ∈ S_sf, truncInvPhi (N + 1) n :=
          Finset.sum_congr rfl fun n hn => (htrunc_eq_fiber (N + 1) n (Finset.mem_filter.mp hn).2.1).symm
      _ ≤ ∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹ :=
          Finset.sum_le_sum fun n hn => htrunc_le (N + 1) n (Finset.mem_filter.mp hn).2.1
  -- Upper bound: for every `M ≥ 1`, `∑ n ∈ S_sf, truncInvPhi M n ≤ ∑ m ∈ S_cop, 1/m + 36`
  have hupper_M : ∀ M : ℕ, 1 ≤ M →
      ∑ n ∈ S_sf, truncInvPhi M n ≤ (∑ m ∈ S_cop, ((m : ℝ))⁻¹) + 36 := by
    intro M hM
    have hdisj : Set.PairwiseDisjoint (S_sf : Set ℕ) (fun n => fiberM M n) := by
      intro n₁ _ n₂ _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro m hm₁ hm₂
      simp only [fiberM, Finset.mem_filter] at hm₁ hm₂
      exact hne (hm₁.2.1.symm.trans hm₂.2.1)
    rw [Finset.sum_congr rfl fun n hn => htrunc_eq_fiber M n (Finset.mem_filter.mp hn).2.1,
      ← Finset.sum_biUnion hdisj]
    set U := S_sf.biUnion (fun n => fiberM M n)
    rw [← Finset.sum_filter_add_sum_filter_not U (fun m => m ≤ N)]
    -- First part (`m ≤ N`): subset of `S_cop`
    have hpart1 : ∑ m ∈ U.filter (fun m => m ≤ N), ((m : ℝ))⁻¹ ≤ ∑ m ∈ S_cop, ((m : ℝ))⁻¹ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun _ _ _ => by positivity
      simp only [U, Finset.mem_filter, Finset.mem_biUnion, fiberM, S_sf, Finset.mem_Icc] at hm
      rcases hm with ⟨⟨n, ⟨_, _, hcop_n⟩, ⟨⟨hm1, _⟩, hrad, _⟩⟩, hmN⟩
      simp only [S_cop, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm1, hmN⟩, (coprime_rad_iff (by omega)).mp (hrad ▸ hcop_n)⟩
    -- Second part (`m > N`): write `n = rad m ≤ N`, `k = m / n ≥ 2`, `rad k ∣ n`, `n * k > N`
    have hpart2 : ∑ m ∈ U.filter (fun m => ¬ m ≤ N), ((m : ℝ))⁻¹ ≤ 36 := by
      set K := N ^ M
      -- Group by `k = m / rad m ∈ Icc 2 K`
      let grp : ℕ → Finset ℕ := fun k =>
        (Finset.Icc 1 (N / rad k)).filter (fun d => N < d * rad k * k) |>.image (fun d => d * rad k * k)
      have hsub2 : U.filter (fun m => ¬ m ≤ N) ⊆ (Finset.Icc 2 K).biUnion grp := by
        intro m hm
        simp only [U, Finset.mem_filter, Finset.mem_biUnion, fiberM, S_sf, Finset.mem_Icc] at hm
        rcases hm with ⟨⟨n, ⟨⟨hn1, hnN⟩, _, _⟩, ⟨⟨hm1, hm_le⟩, hrad, _⟩⟩, hmgt⟩
        have hndvd : n ∣ m := hrad ▸ rad_dvd (by omega)
        obtain ⟨k, hmk⟩ := hndvd
        have hk2 : 2 ≤ k := by
          by_contra hklt; push Not at hklt
          have : k = 0 ∨ k = 1 := by omega
          rcases this with rfl | rfl <;> omega
        have hkK : k ≤ K := by
          have : k ≤ m := by rw [hmk]; exact Nat.le_mul_of_pos_left k hn1
          exact this.trans (hm_le.trans (Nat.pow_le_pow_left hnN M))
        -- `rad k ∣ n` because every prime factor of `k` divides `m` hence divides `rad m = n`
        have hradk_dvd : rad k ∣ n := by
          rw [← hrad]
          unfold rad
          refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
          intro p hp
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hpk : p ∣ k := Nat.dvd_of_mem_primeFactors hp
          exact Nat.mem_primeFactors.mpr ⟨hpp, dvd_trans hpk (hmk ▸ dvd_mul_left k n), by omega⟩
        obtain ⟨d, hnd⟩ := hradk_dvd
        have hd1 : 1 ≤ d := by
          by_contra hd0; push Not at hd0
          have : d = 0 := by omega
          rw [this, mul_zero] at hnd; omega
        have hd_le : d ≤ N / rad k := by
          rw [Nat.le_div_iff_mul_le (rad_pos k), mul_comm]; omega
        rw [Finset.mem_biUnion]
        refine ⟨k, Finset.mem_Icc.mpr ⟨hk2, hkK⟩, ?_⟩
        simp only [grp, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨d, ⟨⟨hd1, hd_le⟩, ?_⟩, ?_⟩
        · have : d * rad k * k = m := by rw [hmk, hnd]; ring
          omega
        · rw [hmk, hnd]; ring
      have hgrp_bound : ∀ k ∈ Finset.Icc 2 K,
          ∑ m ∈ grp k, ((m : ℝ))⁻¹ ≤ (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ) := by
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkr_pos : 0 < rad k * k := Nat.mul_pos (rad_pos k) (by omega)
        have hgrp_inj : ∀ d₁ d₂, d₁ * rad k * k = d₂ * rad k * k → d₁ = d₂ := by
          intro d₁ d₂ h
          have : d₁ * (rad k * k) = d₂ * (rad k * k) := by linarith
          exact Nat.eq_of_mul_eq_mul_right hkr_pos this
        dsimp only [grp]
        rw [Finset.sum_image (fun d₁ _ d₂ _ h => hgrp_inj d₁ d₂ h)]
        have hfactor : ∑ d ∈ (Finset.Icc 1 (N / rad k)).filter (fun d => N < d * rad k * k),
              (((d * rad k * k : ℕ) : ℝ))⁻¹ =
            (∑ d ∈ (Finset.Icc 1 (N / rad k)).filter (fun d => N < d * rad k * k), ((d : ℝ))⁻¹) /
              ((k * rad k : ℕ) : ℝ) := by
          rw [div_eq_mul_inv, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          push_cast; field_simp
        rw [hfactor]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        -- Bound `∑_{d ∈ Icc (a+1) b} 1/d ≤ log k + 1` where `a = N / (k * rad k)`, `b = N / rad k`
        set a := N / (rad k * k)
        set b := N / rad k
        have hsub_d : (Finset.Icc 1 b).filter (fun d => N < d * rad k * k) ⊆ Finset.Icc (a + 1) b := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
          refine ⟨?_, hd.1.2⟩
          have h1 : a * (rad k * k) ≤ N := Nat.div_mul_le_self N (rad k * k)
          have h2 : a * (rad k * k) < d * (rad k * k) := by linarith [hd.2]
          have h3 : a < d := Nat.lt_of_mul_lt_mul_right h2
          omega
        calc ∑ d ∈ (Finset.Icc 1 b).filter (fun d => N < d * rad k * k), ((d : ℝ))⁻¹
            ≤ ∑ d ∈ Finset.Icc (a + 1) b, ((d : ℝ))⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_d fun _ _ _ => by positivity
          _ ≤ Real.log (k : ℝ) + 1 := by
              by_cases hab : b < a + 1
              · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
                have : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
                linarith
              · push Not at hab
                by_cases ha0 : a = 0
                · -- `a = 0` means `N < rad k * k`, so `b = N / rad k ≤ k`
                  have hNlt : N < rad k * k := by
                    by_contra hge; push Not at hge
                    have : 1 ≤ N / (rad k * k) := (Nat.le_div_iff_mul_le hkr_pos).mpr (by linarith)
                    omega
                  have hbk : b ≤ k := by
                    have : b * rad k ≤ N := Nat.div_mul_le_self N (rad k)
                    have : b * rad k < k * rad k := by linarith
                    exact (Nat.lt_of_mul_lt_mul_right this).le
                  have hharm := abs_harmonic_sub_log_le_one (x := (b : ℝ)) (by exact_mod_cast (by omega : 1 ≤ b))
                  rw [Nat.floor_natCast] at hharm
                  have hlogb : Real.log (b : ℝ) ≤ Real.log (k : ℝ) :=
                    Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hbk)
                  rw [ha0, zero_add]
                  linarith [(abs_le.mp hharm).2]
                · -- `a ≥ 1`: telescope `1/d ≤ log d - log(d - 1)` from `a + 1` to `b`
                  have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha0
                  have htelesc : ∑ d ∈ Finset.Icc (a + 1) b, ((d : ℝ))⁻¹ ≤
                      Real.log (b : ℝ) - Real.log (a : ℝ) := by
                    have hstep : ∀ d ∈ Finset.Icc (a + 1) b,
                        ((d : ℝ))⁻¹ ≤ Real.log (d : ℝ) - Real.log ((d - 1 : ℕ) : ℝ) := by
                      intro d hd
                      have hd2 : 2 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
                      have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
                      have hd1_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
                      have hlog := Real.log_le_sub_one_of_pos (div_pos hd1_pos hd_pos)
                      rw [Real.log_div hd1_pos.ne' hd_pos.ne'] at hlog
                      have hsub : ((d - 1 : ℕ) : ℝ) / (d : ℝ) - 1 = -(((d : ℝ))⁻¹) := by
                        rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
                        field_simp [hd_pos.ne']; ring
                      linarith
                    have ht_gen : ∀ m : ℕ, a + 1 ≤ m →
                        ∑ d ∈ Finset.Icc (a + 1) m,
                            (Real.log (d : ℝ) - Real.log ((d - 1 : ℕ) : ℝ)) =
                          Real.log (m : ℝ) - Real.log (a : ℝ) := by
                      intro m hm0
                      induction m, hm0 using Nat.le_induction with
                      | base => simp
                      | succ m hm ih =>
                        have hIcc : Finset.Icc (a + 1) (m + 1) =
                            insert (m + 1) (Finset.Icc (a + 1) m) := by
                          ext d; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                        rw [hIcc, Finset.sum_insert (by simp), ih]
                        simp only [Nat.add_sub_cancel]; ring
                    calc ∑ d ∈ Finset.Icc (a + 1) b, ((d : ℝ))⁻¹
                        ≤ ∑ d ∈ Finset.Icc (a + 1) b,
                            (Real.log (d : ℝ) - Real.log ((d - 1 : ℕ) : ℝ)) :=
                          Finset.sum_le_sum hstep
                      _ = Real.log (b : ℝ) - Real.log (a : ℝ) := ht_gen b hab
                  -- Since `b * rad k ≤ N < (a + 1) * rad k * k ≤ 2 * a * k * rad k`, `b ≤ 2 * a * k`
                  have hb_le : b ≤ 2 * a * k := by
                    have h1 : b * rad k ≤ N := Nat.div_mul_le_self N (rad k)
                    have h2 : N < (a + 1) * (rad k * k) := by
                      have := Nat.lt_div_mul_add (a := N) hkr_pos
                      have hmul : (a + 1) * (rad k * k) = a * (rad k * k) + rad k * k := by ring
                      dsimp only [a] at hmul ⊢; omega
                    have h3 : (a + 1) * (rad k * k) ≤ (2 * a * k) * rad k := by nlinarith
                    have h4 : b * rad k < (2 * a * k) * rad k := lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
                    exact (Nat.lt_of_mul_lt_mul_right h4).le
                  have hlog_ba : Real.log (b : ℝ) - Real.log (a : ℝ) ≤ Real.log (k : ℝ) + 1 := by
                    have h1 : Real.log (b : ℝ) ≤ Real.log (2 * (a : ℝ) * (k : ℝ)) :=
                      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hb_le)
                    rw [Real.log_mul (by positivity) (Nat.cast_pos.mpr (by omega)).ne',
                      Real.log_mul (by norm_num) (Nat.cast_pos.mpr ha1).ne'] at h1
                    have hlog2 : Real.log 2 ≤ 1 := by
                      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
                      linarith
                    linarith
                  linarith
      calc ∑ m ∈ U.filter (fun m => ¬ m ≤ N), ((m : ℝ))⁻¹
          ≤ ∑ m ∈ (Finset.Icc 2 K).biUnion grp, ((m : ℝ))⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => by positivity
        _ ≤ ∑ k ∈ Finset.Icc 2 K, ∑ m ∈ grp k, ((m : ℝ))⁻¹ :=
            sum_biUnion_le_of_nonneg (fun _ => by positivity)
        _ ≤ ∑ k ∈ Finset.Icc 2 K, (Real.log (k : ℝ) + 1) / ((k * rad k : ℕ) : ℝ) :=
            Finset.sum_le_sum hgrp_bound
        _ ≤ 36 := sum_log_div_mul_rad_le K
    linarith
  -- Let `M → ∞`: `truncInvPhi M n → (n.totient : ℝ)⁻¹` for each `n ∈ S_sf`
  have htend : Tendsto (fun M : ℕ => ∑ n ∈ S_sf, truncInvPhi M n) atTop
      (𝓝 (∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹)) := by
    refine tendsto_finset_sum S_sf fun n hn => ?_
    have hsf : Squarefree n := (Finset.mem_filter.mp hn).2.1
    have hn0 : n ≠ 0 := hsf.ne_zero
    have hphi : ((n.totient : ℝ))⁻¹ = ∏ p ∈ n.primeFactors, (((p : ℝ) - 1))⁻¹ := by
      have hnat : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
        rw [Nat.totient_eq_prod_factorization hn0]
        simp only [Finsupp.prod, Nat.support_factorization]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have h1 : 1 ≤ n.factorization p :=
          (hpp.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp)
        have h2 : n.factorization p ≤ 1 := by
          by_contra hgt; push Not at hgt
          have hp2 : p * p ∣ n := by
            simpa [sq] using (hpp.pow_dvd_iff_le_factorization hn0).mpr (by omega : 2 ≤ _)
          exact hpp.ne_one (Nat.isUnit_iff.mp (hsf p hp2))
        have heq : n.factorization p = 1 := by omega
        rw [heq, pow_zero, one_mul]
      rw [hnat, Nat.cast_prod, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
      rw [Nat.cast_sub hp1, Nat.cast_one]
    rw [hphi]
    refine tendsto_finset_prod n.primeFactors fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hrew : (fun M : ℕ => ∑ e ∈ Finset.Icc 1 M, (((p : ℝ) ^ e))⁻¹) =
        fun M : ℕ => (1 - (((p : ℝ))⁻¹) ^ M) * (((p : ℝ) - 1))⁻¹ := by
      funext M; rw [hgeom p M hpp, inv_pow]
    rw [hrew]
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpp.pos
    have hlt1 : |((p : ℝ))⁻¹| < 1 := by
      rw [abs_of_pos (inv_pos.mpr hp_pos)]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hpp.one_lt)
    have hpow0 : Tendsto (fun M : ℕ => (((p : ℝ))⁻¹) ^ M) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one hlt1
    have hsub1 : Tendsto (fun M : ℕ => (1 : ℝ) - (((p : ℝ))⁻¹) ^ M) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hpow0
    simpa only [sub_zero, one_mul] using hsub1.mul_const (((p : ℝ) - 1))⁻¹
  have hupper : ∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹ ≤ (∑ m ∈ S_cop, ((m : ℝ))⁻¹) + 36 :=
    le_of_tendsto htend (eventually_atTop.mpr ⟨1, fun M hM => hupper_M M hM⟩)
  have hcop_x := hcop x hx
  rw [abs_le] at hcop_x ⊢
  constructor <;> linarith

/-- Elementary telescoping bound: for `D₀ ≥ 4` and any `M`,
`∑_{p ∈ (D₀, M] prime} 1 / (p - 2)^2 ≤ 1 / (D₀ - 2)`. -/
lemma sum_inv_sub_two_sq_le {D₀ M : ℕ} (hD : 4 ≤ D₀) :
    ∑ p ∈ (Finset.Icc (D₀ + 1) M).filter Nat.Prime, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹ ≤
      1 / ((D₀ - 2 : ℕ) : ℝ) := by
  calc ∑ p ∈ (Finset.Icc (D₀ + 1) M).filter Nat.Prime, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹
      ≤ ∑ n ∈ Finset.Icc (D₀ + 1) M, ((((n - 2 : ℕ) : ℝ) ^ 2))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    _ ≤ ∑ n ∈ Finset.Icc (D₀ + 1) M,
          ((((n - 3 : ℕ) : ℝ))⁻¹ - (((n - 2 : ℕ) : ℝ))⁻¹) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn5 : 5 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
        have hpos1 : (0 : ℝ) < ((n - 3 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hpos2 : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hsub : ((n - 2 : ℕ) : ℝ) - ((n - 3 : ℕ) : ℝ) = 1 := by
          rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n)]; push_cast; ring
        have hdiff : (((n - 3 : ℕ) : ℝ))⁻¹ - (((n - 2 : ℕ) : ℝ))⁻¹ =
            1 / (((n - 3 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) := by
          field_simp [hpos1.ne', hpos2.ne']; linarith
        rw [hdiff, one_div]
        refine inv_anti₀ (mul_pos hpos1 hpos2) ?_
        rw [sq]
        have hle : ((n - 3 : ℕ) : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : n - 3 ≤ n - 2)
        exact mul_le_mul_of_nonneg_right hle hpos2.le
    _ ≤ 1 / ((D₀ - 2 : ℕ) : ℝ) := by
        by_cases hM : M < D₀ + 1
        · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
        · push Not at hM
          have htelesc : ∑ n ∈ Finset.Icc (D₀ + 1) M,
              ((((n - 3 : ℕ) : ℝ))⁻¹ - (((n - 2 : ℕ) : ℝ))⁻¹) =
              (((D₀ - 2 : ℕ) : ℝ))⁻¹ - (((M - 2 : ℕ) : ℝ))⁻¹ := by
            induction M, hM using Nat.le_induction with
            | base =>
              simp only [Finset.Icc_self, Finset.sum_singleton]
              have h1 : D₀ + 1 - 3 = D₀ - 2 := by omega
              have h2 : D₀ + 1 - 2 = D₀ - 1 := by omega
              rw [h1]
            | succ m hm ih =>
              have hIcc : Finset.Icc (D₀ + 1) (m + 1) = insert (m + 1) (Finset.Icc (D₀ + 1) m) := by
                ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              rw [hIcc, Finset.sum_insert (by simp), ih]
              have h1 : m + 1 - 3 = m - 2 := by omega
              rw [h1]; ring
          rw [htelesc, one_div]
          have : (0 : ℝ) ≤ (((M - 2 : ℕ) : ℝ))⁻¹ := by positivity
          linarith

/-- Product bound over primes `> D₀`: for `D₀ ≥ 6`,
`∑_{1 ≤ s ≤ M, sqfree, (s, W D₀)=1} 1 / g₂(s)² ≤ 1 + 2 / (D₀ - 2)`. -/
lemma sum_inv_g2_sq_le {D₀ M : ℕ} (hD : 6 ≤ D₀) :
    ∑ s ∈ (Finset.Icc 1 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)),
      (((g₂ s : ℝ) ^ 2))⁻¹ ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := by
  set P := (Finset.Icc (D₀ + 1) M).filter Nat.Prime
  -- Expand `∏_{p ∈ P} (1 + 1/(p-2)^2) = ∑_{T ⊆ P} ∏_{p ∈ T} 1/(p-2)^2`
  have hprod_ge : ∑ s ∈ (Finset.Icc 1 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)),
      (((g₂ s : ℝ) ^ 2))⁻¹ ≤ ∏ p ∈ P, (1 + ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹) := by
    rw [Finset.prod_one_add]
    have hmap : ∀ s ∈ (Finset.Icc 1 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)),
        s.primeFactors ∈ P.powerset := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_Icc] at hs
      rw [Finset.mem_powerset]
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
      have hpM : p ≤ M := (Nat.le_of_dvd hs.1.1 hps).trans hs.1.2
      have hpD : D₀ < p := by
        by_contra hle; push Not at hle
        have hpW : p ∣ W D₀ := (prime_dvd_W_iff hpp).mpr hle
        exact hpp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hs.2.2) ▸ Nat.dvd_gcd hps hpW)
      simp only [P, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hpM⟩, hpp⟩
    have hinj : Set.InjOn Nat.primeFactors
        ((Finset.Icc 1 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)) : Set ℕ) := by
      intro s₁ hs₁ s₂ hs₂ heq
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hs₁ hs₂
      rw [← rad_eq_self_of_squarefree hs₁.2.1, ← rad_eq_self_of_squarefree hs₂.2.1]
      unfold rad; rw [heq]
    have hterm : ∀ s ∈ (Finset.Icc 1 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)),
        (((g₂ s : ℝ) ^ 2))⁻¹ = ∏ p ∈ s.primeFactors, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹ := by
      intro s _
      unfold g₂
      rw [Nat.cast_prod, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    calc _ = ∑ s ∈ (Finset.Icc 1 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)),
            ∏ p ∈ s.primeFactors, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹ := Finset.sum_congr rfl hterm
      _ = ∑ T ∈ ((Finset.Icc 1 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀))).image
            Nat.primeFactors, ∏ p ∈ T, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹ :=
          (Finset.sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹)
            (fun a ha b hb hab => hinj ha hb hab)).symm
      _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_) fun _ _ _ =>
            Finset.prod_nonneg fun _ _ => by positivity
          rcases Finset.mem_image.mp hT with ⟨s, hs, rfl⟩
          exact hmap s hs
  have hprod_exp : ∏ p ∈ P, (1 + ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹) ≤
      Real.exp (∑ p ∈ P, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun p _ => ?_
    linarith [Real.add_one_le_exp ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹]
  have hsum_le : ∑ p ∈ P, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹ ≤ 1 / ((D₀ - 2 : ℕ) : ℝ) :=
    sum_inv_sub_two_sq_le (by omega)
  have hu_le : 1 / ((D₀ - 2 : ℕ) : ℝ) ≤ 1 / 2 := by
    have hD2 : (4 : ℝ) ≤ ((D₀ - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ D₀ - 2)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hexp_le : Real.exp (1 / ((D₀ - 2 : ℕ) : ℝ)) ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := by
    set u := 1 / ((D₀ - 2 : ℕ) : ℝ)
    have hu0 : 0 ≤ u := by positivity
    -- For `0 ≤ u ≤ 1/2`: `exp u ≤ 1 / (1 - u) ≤ 1 + 2 u`!
    have h1 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    have hpos : 0 < 1 - u := by linarith
    have h2 : Real.exp u ≤ 1 / (1 - u) := by
      rw [le_div_iff₀ hpos]
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos u).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
      linarith
    have h3 : 1 / (1 - u) ≤ 1 + 2 * u := by
      rw [div_le_iff₀ hpos]
      nlinarith
    calc Real.exp u ≤ 1 + 2 * u := h2.trans h3
      _ = 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := by dsimp only [u]; ring
  calc _ ≤ ∏ p ∈ P, (1 + ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹) := hprod_ge
    _ ≤ Real.exp (∑ p ∈ P, ((((p - 2 : ℕ) : ℝ) ^ 2))⁻¹) := hprod_exp
    _ ≤ Real.exp (1 / ((D₀ - 2 : ℕ) : ℝ)) := Real.exp_le_exp.mpr hsum_le
    _ ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := hexp_le

/-- Tail bound for `s > 1`: `∑_{2 ≤ s ≤ M, sqfree, (s, W D₀)=1} 1 / g₂(s)² ≤ 2 / (D₀ - 2)`. -/
lemma sum_inv_g2_sq_gt_one_le {D₀ M : ℕ} (hD : 6 ≤ D₀) :
    ∑ s ∈ (Finset.Icc 2 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)),
      (((g₂ s : ℝ) ^ 2))⁻¹ ≤ 2 / ((D₀ - 2 : ℕ) : ℝ) := by
  by_cases hM0 : M = 0
  · subst hM0; simp; positivity
  · have hM1 : 1 ≤ M := Nat.pos_of_ne_zero hM0
    have hsplit : (Finset.Icc 1 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)) =
        insert 1 ((Finset.Icc 2 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀))) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
      constructor
      · rintro ⟨⟨hs1, hsM⟩, hsf, hcop⟩
        by_cases h1 : s = 1
        · exact Or.inl h1
        · exact Or.inr ⟨⟨by omega, hsM⟩, hsf, hcop⟩
      · rintro (rfl | ⟨⟨hs2, hsM⟩, hsf, hcop⟩)
        · exact ⟨⟨le_rfl, hM1⟩, squarefree_one, Nat.coprime_one_left _⟩
        · exact ⟨⟨by omega, hsM⟩, hsf, hcop⟩
    have hbd := sum_inv_g2_sq_le (D₀ := D₀) (M := M) hD
    rw [hsplit, Finset.sum_insert (by simp)] at hbd
    simp only [g₂_one, Nat.cast_one, one_pow, inv_one] at hbd
    linarith

/-- Same tail bound with `1 / φ(s)² ≤ 1 / g₂(s)²`. -/
lemma sum_inv_phi_sq_gt_one_le {D₀ M : ℕ} (hD : 6 ≤ D₀) :
    ∑ s ∈ (Finset.Icc 2 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)),
      (((s.totient : ℝ) ^ 2))⁻¹ ≤ 2 / ((D₀ - 2 : ℕ) : ℝ) := by
  have h2W : 2 ∣ W D₀ := (prime_dvd_W_iff Nat.prime_two).mpr (by omega)
  calc _ ≤ ∑ s ∈ (Finset.Icc 2 M).filter (fun s => Squarefree s ∧ Nat.Coprime s (W D₀)),
            (((g₂ s : ℝ) ^ 2))⁻¹ := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hsf : Squarefree s := (Finset.mem_filter.mp hs).2.1
          have hcop : Nat.Coprime s (W D₀) := (Finset.mem_filter.mp hs).2.2
          have hgpos : (0 : ℝ) < (g₂ s : ℝ) :=
            Nat.cast_pos.mpr (g₂_pos_of_coprime_two hsf.ne_zero (hcop.coprime_dvd_right h2W))
          have hle : (g₂ s : ℝ) ≤ (s.totient : ℝ) := by exact_mod_cast g₂_le_totient_of_squarefree hsf
          exact inv_anti₀ (sq_pos_of_pos hgpos) (pow_le_pow_left₀ hgpos.le hle 2)
    _ ≤ 2 / ((D₀ - 2 : ℕ) : ℝ) := sum_inv_g2_sq_gt_one_le hD

/-- Upper bound `∑_{n=1}^M aG2 (W D₀) n ≤ 2 * ∑_{n=1}^M aPhi (W D₀) n` for `D₀ ≥ 6`. -/
lemma sum_aG2_le_two_mul_sum_aPhi {D₀ M : ℕ} (hD : 6 ≤ D₀) :
    ∑ n ∈ Finset.Icc 1 M, aG2 (W D₀) n ≤ 2 * ∑ n ∈ Finset.Icc 1 M, aPhi (W D₀) n := by
  have h2W : 2 ∣ W D₀ := (prime_dvd_W_iff Nat.prime_two).mpr (by omega)
  -- For squarefree `n` coprime to `W D₀`, `1 / g₂(n) = (1 / φ(n)) * ∑_{d ∣ n} 1 / g₂(d)`!
  have hid : ∀ n : ℕ, Squarefree n → Nat.Coprime n (W D₀) →
      ((g₂ n : ℝ))⁻¹ = ((n.totient : ℝ))⁻¹ * ∑ d ∈ n.divisors, ((g₂ d : ℝ))⁻¹ := by
    intro n hsf hcop
    have hn0 : n ≠ 0 := hsf.ne_zero
    have hodd : Nat.Coprime n 2 := hcop.coprime_dvd_right h2W
    have hg_pos : (0 : ℝ) < (g₂ n : ℝ) := Nat.cast_pos.mpr (g₂_pos_of_coprime_two hn0 hodd)
    have hphi_pos : (0 : ℝ) < (n.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0))
    have hsum_eq : ∑ d ∈ n.divisors, ((g₂ d : ℝ))⁻¹ =
        ∏ p ∈ n.primeFactors, (1 + (((p - 2 : ℕ) : ℝ))⁻¹) := by
      rw [Finset.prod_one_add]
      refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
      · intro d hd
        rw [Finset.mem_powerset]
        exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hn0
      · intro d₁ hd₁ d₂ hd₂ heq
        have hsf1 : Squarefree d₁ := hsf.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd₁)
        have hsf2 : Squarefree d₂ := hsf.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd₂)
        rw [← rad_eq_self_of_squarefree hsf1, ← rad_eq_self_of_squarefree hsf2]
        unfold rad; rw [heq]
      · intro T hT
        rw [Finset.mem_powerset] at hT
        refine ⟨∏ p ∈ T, p, ?_, ?_⟩
        · rw [Nat.mem_divisors]
          refine ⟨?_, hn0⟩
          rw [← rad_eq_self_of_squarefree hsf]
          exact Finset.prod_dvd_prod_of_subset _ _ _ hT
        · have hT_prime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
          induction T using Finset.induction_on with
          | empty => simp
          | insert a s ha ih =>
            have haP : a.Prime := hT_prime a (mem_insert_self a s)
            have hsP : ∀ q ∈ s, q.Prime := fun q hq => hT_prime q (mem_insert_of_mem hq)
            have hsne : ∏ q ∈ s, q ≠ 0 := (Finset.prod_pos fun q hq => (hsP q hq).pos).ne'
            rw [Finset.prod_insert ha, Nat.primeFactors_mul haP.ne_zero hsne, haP.primeFactors,
              ih (Finset.Subset.trans (Finset.subset_insert a s) hT) hsP]
            ext x; simp
      · intro d _
        unfold g₂
        rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
    rw [hsum_eq]
    have hphi_prod : (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ) := by
      have hnat : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
        rw [Nat.totient_eq_prod_factorization hn0]
        simp only [Finsupp.prod, Nat.support_factorization]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have h1 : 1 ≤ n.factorization p :=
          (hpp.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp)
        have h2 : n.factorization p ≤ 1 := by
          by_contra hgt; push Not at hgt
          have hp2 : p * p ∣ n := by
            simpa [sq] using (hpp.pow_dvd_iff_le_factorization hn0).mpr (by omega : 2 ≤ _)
          exact hpp.ne_one (Nat.isUnit_iff.mp (hsf p hp2))
        have heq : n.factorization p = 1 := by omega
        rw [heq, pow_zero, one_mul]
      rw [hnat, Nat.cast_prod]
    rw [hphi_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    unfold g₂
    rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpD : D₀ < p := by
      by_contra hle; push Not at hle
      exact hpp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hcop) ▸
        Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) ((prime_dvd_W_iff hpp).mpr hle))
    have hpm1 : ((p - 1 : ℕ) : ℝ) = ((p - 2 : ℕ) : ℝ) + 1 := by
      have : p - 1 = (p - 2) + 1 := by omega
      rw [this]; push_cast; ring
    have hpos : (0 : ℝ) < ((p - 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [hpm1]; field_simp [hpos.ne', (by linarith : ((p - 2 : ℕ) : ℝ) + 1 ≠ 0)]
  -- Swap sums: write `n = d * m` with `d, m ∈ Icc 1 M`, squarefree, coprime to `W D₀`, `Coprime d m`
  set S := (Finset.Icc 1 M).filter (fun n => Squarefree n ∧ Nat.Coprime n (W D₀))
  have hlhs : ∑ n ∈ Finset.Icc 1 M, aG2 (W D₀) n = ∑ n ∈ S, ((g₂ n : ℝ))⁻¹ := by
    unfold aG2; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hrhs : ∑ n ∈ Finset.Icc 1 M, aPhi (W D₀) n = ∑ n ∈ S, ((n.totient : ℝ))⁻¹ := by
    unfold aPhi; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [hlhs, hrhs]
  have h1 : ∑ n ∈ S, ((g₂ n : ℝ))⁻¹ =
      ∑ n ∈ S, ∑ d ∈ n.divisors, ((n.totient : ℝ))⁻¹ * ((g₂ d : ℝ))⁻¹ := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hid n (Finset.mem_filter.mp hn).2.1 (Finset.mem_filter.mp hn).2.2, Finset.mul_sum]
  rw [h1]
  -- Inject `(n, d)` with `n ∈ S, d ∣ n` into `(d, m) ∈ S ×ˢ S` via `m = n / d`
  have h2 : ∑ n ∈ S, ∑ d ∈ n.divisors, ((n.totient : ℝ))⁻¹ * ((g₂ d : ℝ))⁻¹ ≤
      ∑ p ∈ S ×ˢ S, ((((p.1.totient : ℝ))⁻¹ * ((g₂ p.1 : ℝ))⁻¹) * ((p.2.totient : ℝ))⁻¹) := by
    have hsig : ∑ n ∈ S, ∑ d ∈ n.divisors, ((n.totient : ℝ))⁻¹ * ((g₂ d : ℝ))⁻¹ =
        ∑ x ∈ S.sigma (fun n => n.divisors), ((x.1.totient : ℝ))⁻¹ * ((g₂ x.2 : ℝ))⁻¹ :=
      (Finset.sum_sigma S (fun n => n.divisors) (fun x => ((x.1.totient : ℝ))⁻¹ * ((g₂ x.2 : ℝ))⁻¹)).symm
    rw [hsig]
    let emb : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
    have hinj : Set.InjOn emb ((S.sigma (fun n => n.divisors)) : Set (Σ _ : ℕ, ℕ)) := by
      intro x hx y hy heq
      simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Nat.mem_divisors] at hx hy
      simp only [emb, Prod.mk.injEq] at heq
      have h1 : x.1 = x.2 * (x.1 / x.2) := (Nat.mul_div_cancel' hx.2.1).symm
      have h2 : y.1 = y.2 * (y.1 / y.2) := (Nat.mul_div_cancel' hy.2.1).symm
      have hf : x.1 = y.1 := by rw [h1, h2, heq.2, heq.1]
      exact Sigma.ext hf (heq_of_eq heq.1)
    have hterm : ∀ x ∈ S.sigma (fun n => n.divisors),
        ((x.1.totient : ℝ))⁻¹ * ((g₂ x.2 : ℝ))⁻¹ =
          ((((emb x).1.totient : ℝ))⁻¹ * ((g₂ (emb x).1 : ℝ))⁻¹) * (((emb x).2.totient : ℝ))⁻¹ := by
      intro x hx
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hx
      have hsf : Squarefree x.1 := (Finset.mem_filter.mp hx.1).2.1
      have hmul : x.2 * (x.1 / x.2) = x.1 := Nat.mul_div_cancel' hx.2.1
      have hcop : Nat.Coprime x.2 (x.1 / x.2) :=
        Nat.coprime_of_squarefree_mul (hmul.symm ▸ hsf)
      have hphi : x.1.totient = x.2.totient * (x.1 / x.2).totient := by
        conv_lhs => rw [← hmul]
        exact Nat.totient_mul hcop
      simp only [emb, hphi, Nat.cast_mul]; ring
    calc ∑ x ∈ S.sigma (fun n => n.divisors), ((x.1.totient : ℝ))⁻¹ * ((g₂ x.2 : ℝ))⁻¹
        = ∑ x ∈ S.sigma (fun n => n.divisors),
            ((((emb x).1.totient : ℝ))⁻¹ * ((g₂ (emb x).1 : ℝ))⁻¹) * (((emb x).2.totient : ℝ))⁻¹ :=
          Finset.sum_congr rfl hterm
      _ = ∑ p ∈ (S.sigma (fun n => n.divisors)).image emb,
            ((((p.1.totient : ℝ))⁻¹ * ((g₂ p.1 : ℝ))⁻¹) * ((p.2.totient : ℝ))⁻¹) :=
          (Finset.sum_image (f := fun p : ℕ × ℕ =>
            ((((p.1.totient : ℝ))⁻¹ * ((g₂ p.1 : ℝ))⁻¹) * ((p.2.totient : ℝ))⁻¹))
            (fun a ha b hb hab => hinj ha hb hab)).symm
      _ ≤ ∑ p ∈ S ×ˢ S, ((((p.1.totient : ℝ))⁻¹ * ((g₂ p.1 : ℝ))⁻¹) * ((p.2.totient : ℝ))⁻¹) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => by positivity
          rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
          simp only [Finset.mem_sigma, Nat.mem_divisors, S, Finset.mem_filter, Finset.mem_Icc] at hx
          obtain ⟨⟨⟨hn1, hnM⟩, hsf, hcop⟩, hdvd, _⟩ := hx
          have hm_dvd : x.1 / x.2 ∣ x.1 := Nat.div_dvd_of_dvd hdvd
          have hd1 : 1 ≤ x.2 := Nat.pos_of_dvd_of_pos hdvd hn1
          have hm1 : 1 ≤ x.1 / x.2 := Nat.pos_of_dvd_of_pos hm_dvd hn1
          simp only [emb, Finset.mem_product, S, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨⟨hd1, (Nat.le_of_dvd hn1 hdvd).trans hnM⟩, hsf.squarefree_of_dvd hdvd,
            hcop.coprime_dvd_left hdvd⟩,
            ⟨⟨hm1, (Nat.le_of_dvd hn1 hm_dvd).trans hnM⟩, hsf.squarefree_of_dvd hm_dvd,
            hcop.coprime_dvd_left hm_dvd⟩⟩
  have hprod : ∑ p ∈ S ×ˢ S, ((((p.1.totient : ℝ))⁻¹ * ((g₂ p.1 : ℝ))⁻¹) * ((p.2.totient : ℝ))⁻¹) =
      (∑ d ∈ S, ((d.totient : ℝ))⁻¹ * ((g₂ d : ℝ))⁻¹) * (∑ m ∈ S, ((m.totient : ℝ))⁻¹) := by
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hfactor_le : ∑ d ∈ S, ((d.totient : ℝ))⁻¹ * ((g₂ d : ℝ))⁻¹ ≤ 2 := by
    calc ∑ d ∈ S, ((d.totient : ℝ))⁻¹ * ((g₂ d : ℝ))⁻¹
        ≤ ∑ d ∈ S, (((g₂ d : ℝ) ^ 2))⁻¹ := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hsf : Squarefree d := (Finset.mem_filter.mp hd).2.1
          have hcop : Nat.Coprime d (W D₀) := (Finset.mem_filter.mp hd).2.2
          have hgpos : (0 : ℝ) < (g₂ d : ℝ) :=
            Nat.cast_pos.mpr (g₂_pos_of_coprime_two hsf.ne_zero (hcop.coprime_dvd_right h2W))
          have hle : (g₂ d : ℝ) ≤ (d.totient : ℝ) := by exact_mod_cast g₂_le_totient_of_squarefree hsf
          rw [sq, mul_inv]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hgpos hle) (by positivity)
      _ ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := sum_inv_g2_sq_le hD
      _ ≤ 2 := by
          have h4 : (4 : ℝ) ≤ ((D₀ - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ D₀ - 2)
          have : 2 / ((D₀ - 2 : ℕ) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          linarith
  calc ∑ n ∈ S, ∑ d ∈ n.divisors, ((n.totient : ℝ))⁻¹ * ((g₂ d : ℝ))⁻¹
      ≤ (∑ d ∈ S, ((d.totient : ℝ))⁻¹ * ((g₂ d : ℝ))⁻¹) * (∑ m ∈ S, ((m.totient : ℝ))⁻¹) :=
        h2.trans_eq hprod
    _ ≤ 2 * ∑ m ∈ S, ((m.totient : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hfactor_le (Finset.sum_nonneg fun _ _ => by positivity)

/-- Elementary upper bound `d / φ(d) ≤ exp(2) * log R` for all `1 ≤ d ≤ R` (`R ≥ 16`). -/
lemma nat_div_totient_le {d : ℕ} {R : ℝ} (hd1 : 1 ≤ d) (hR : 16 ≤ R) (hdR : (d : ℝ) ≤ R) :
    (d : ℝ) / (d.totient : ℝ) ≤ Real.exp 2 * Real.log R := by
  have hd0 : d ≠ 0 := by omega
  have hlogR_gt2 : 2 < Real.log R := by
    have he2 : Real.exp 2 < 16 := by
      have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ < 3 * 3 := mul_lt_mul'' h1 h1 (Real.exp_pos 1).le (Real.exp_pos 1).le
        _ < 16 := by norm_num
    exact (Real.log_exp 2).symm.trans_lt (Real.log_lt_log (Real.exp_pos 2) (by linarith))
  have hphi_ratio : (d : ℝ) / (d.totient : ℝ) =
      ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    have hnat : d.totient * (∏ p ∈ d.primeFactors, p) = d * ∏ p ∈ d.primeFactors, (p - 1) :=
      Nat.totient_mul_prod_primeFactors d
    have hR_eq : (d.totient : ℝ) * (∏ p ∈ d.primeFactors, (p : ℝ)) =
        (d : ℝ) * ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
      have hcast : ((d.totient * ∏ p ∈ d.primeFactors, p : ℕ) : ℝ) =
          ((d * ∏ p ∈ d.primeFactors, (p - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      rw [hcast]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
    have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
    have hden_pos : (0 : ℝ) < ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) :=
      Finset.prod_pos fun p hp => by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        linarith
    rw [Finset.prod_div_distrib, div_eq_div_iff hphi_pos.ne' hden_pos.ne']
    linarith
  rw [hphi_ratio]
  -- Split `d.primeFactors` at `K = ⌊log R⌋₊`
  set K : ℕ := ⌊Real.log R⌋₊
  have hK2 : 2 ≤ K := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ Real.log R))
  have hK_le : (K : ℝ) ≤ Real.log R := Nat.floor_le (by linarith)
  have hlogR_lt_K1 : Real.log R < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [← Finset.prod_filter_mul_prod_filter_not d.primeFactors (fun p => p ≤ K)]
  -- Part 1 (`p ≤ K`): bounded by telescoping product `∏_{n=2}^K n / (n - 1) = K ≤ log R`
  have hpart1 : ∏ p ∈ d.primeFactors.filter (fun p => p ≤ K), (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log R := by
    have hsub : d.primeFactors.filter (fun p => p ≤ K) ⊆ Finset.Icc 2 K := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨(Nat.prime_of_mem_primeFactors hp.1).two_le, hp.2⟩
    have hle_Icc : ∏ p ∈ d.primeFactors.filter (fun p => p ≤ K), (p : ℝ) / ((p : ℝ) - 1) ≤
        ∏ n ∈ Finset.Icc 2 K, (n : ℝ) / ((n : ℝ) - 1) := by
      refine prod_le_prod_of_subset_one_le hsub fun n hn => ?_
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [one_le_div (by linarith)]; linarith
    have htelesc_gen : ∀ m : ℕ, 2 ≤ m → ∏ n ∈ Finset.Icc 2 m, (n : ℝ) / ((n : ℝ) - 1) = (m : ℝ) := by
      intro m hm2
      induction m, hm2 using Nat.le_induction with
      | base => simp; norm_num
      | succ m hm ih =>
        have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.prod_insert (by simp), ih]
        have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast; field_simp [hm0]; ring
    exact (hle_Icc.trans_eq (htelesc_gen K hK2)).trans hK_le
  -- Part 2 (`p > K`)
  have hpart2 : ∏ p ∈ d.primeFactors.filter (fun p => ¬ p ≤ K), (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp 2 := by
    set S₂ := d.primeFactors.filter (fun p => ¬ p ≤ K)
    have hcard_le : (S₂.card : ℝ) ≤ Real.log R := by
      have h3pow : (3 : ℕ) ^ S₂.card ≤ d := by
        calc (3 : ℕ) ^ S₂.card = ∏ _p ∈ S₂, 3 := by rw [Finset.prod_const]
          _ ≤ ∏ p ∈ S₂, p := Finset.prod_le_prod' fun p hp => by
                have := (Finset.mem_filter.mp hp).2; omega
          _ ≤ ∏ p ∈ d.primeFactors, p :=
              Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) fun p hp _ =>
                (Nat.prime_of_mem_primeFactors hp).one_le
          _ ≤ d := Nat.le_of_dvd hd1 (Nat.prod_primeFactors_dvd d)
      have h3R : (3 : ℝ) ^ S₂.card ≤ R := le_trans (by exact_mod_cast h3pow) hdR
      have hlog := Real.log_le_log (by positivity) h3R
      rw [Real.log_pow] at hlog
      have hlog3 : 1 ≤ Real.log 3 := by
        have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) he1)
      nlinarith [Nat.cast_nonneg (α := ℝ) S₂.card]
    have hfactor : ∀ p ∈ S₂, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (2 / Real.log R) := by
      intro p hp
      have hpK : K + 1 ≤ p := by have := (Finset.mem_filter.mp hp).2; omega
      have hp_gt : Real.log R < (p : ℝ) := lt_of_lt_of_le hlogR_lt_K1 (by exact_mod_cast hpK)
      have hpm1_ge : Real.log R / 2 ≤ (p : ℝ) - 1 := by linarith
      have hfrac : (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
        field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]; ring
      have hinv : 1 / ((p : ℝ) - 1) ≤ 2 / Real.log R := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
      calc (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := hfrac
        _ ≤ 1 + 2 / Real.log R := by linarith
        _ ≤ Real.exp (2 / Real.log R) := by linarith [Real.add_one_le_exp (2 / Real.log R)]
    calc ∏ p ∈ S₂, (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∏ _p ∈ S₂, Real.exp (2 / Real.log R) :=
          Finset.prod_le_prod (fun p hp => by
            have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
            exact div_nonneg (by linarith) (by linarith)) hfactor
      _ = Real.exp ((S₂.card : ℝ) * (2 / Real.log R)) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ Real.exp 2 := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : (S₂.card : ℝ) * (2 / Real.log R) ≤ Real.log R * (2 / Real.log R) :=
            mul_le_mul_of_nonneg_right hcard_le (by positivity)
          have h2 : Real.log R * (2 / Real.log R) = 2 := by field_simp [show Real.log R ≠ 0 by linarith]
          linarith
  calc (∏ p ∈ d.primeFactors.filter (fun p => p ≤ K), (p : ℝ) / ((p : ℝ) - 1)) *
        (∏ p ∈ d.primeFactors.filter (fun p => ¬ p ≤ K), (p : ℝ) / ((p : ℝ) - 1))
      ≤ Real.log R * Real.exp 2 := mul_le_mul hpart1 hpart2 (Finset.prod_nonneg fun p hp => by
          have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
          exact div_nonneg (by linarith) (by linarith)) (by linarith)
    _ = Real.exp 2 * Real.log R := mul_comm _ _

/-! ### 1D and `k`-Dimensional Sum-to-Integral Theorems -/

/-- **1D Weighted Sum-to-Integral Lemma** (pure Lipschitz step-approximation, zero `HasDerivAt`):
if `a n ≥ 0`, `a 0 = 0`, and `|∑_{n ≤ x} a n - c * log x| ≤ C` for all `x ≥ 1`, then for any
`s ∈ [0, 1]`, any `(M, L)`-Lipschitz function `f` on `[0, s]`, and any `R ≥ exp 4`:
`|∑_{1 ≤ n ≤ R^s} a n * f(log n / log R) - c * log R * ∫_0^s f(t) dt| ≤
  ((2 * c + 2 * C + 2) * (L + M) + C * M) * √(log R)`. -/
theorem sum_1d_approx_integral {a : ℕ → ℝ} {c C : ℝ}
    (ha_nn : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (ha_asymp : ∀ x : ℝ, 1 ≤ x → |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) - c * Real.log x| ≤ C)
    {s M L R : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L) (hR : Real.exp 4 ≤ R)
    {f : ℝ → ℝ}
    (hf_bd : ∀ t ∈ Set.Icc (0 : ℝ) s, |f t| ≤ M)
    (hf_lip : ∀ t₁ ∈ Set.Icc (0 : ℝ) s, ∀ t₂ ∈ Set.Icc (0 : ℝ) s, |f t₁ - f t₂| ≤ L * |t₁ - t₂|) :
    |(∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R)) -
      c * Real.log R * (∫ t in (0 : ℝ)..s, f t)| ≤
      (4 * c * L + 6 * C * M + 2 * C * L + 2 * L + 2 * M) * Real.sqrt (Real.log R) := by
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
  have hlogR_ge4 : 4 ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 4) hR
    rwa [Real.log_exp] at this
  have hlogR_pos : 0 < Real.log R := by linarith
  have hsq_ge2 : 2 ≤ Real.sqrt (Real.log R) := Real.le_sqrt_of_sq_le (by linarith)
  have hsq_pos : 0 < Real.sqrt (Real.log R) := by linarith
  set Q : ℕ := ⌊Real.sqrt (Real.log R)⌋₊
  have hQ_ge2 : 2 ≤ Q := Nat.le_floor hsq_ge2
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hQ_le : (Q : ℝ) ≤ Real.sqrt (Real.log R) := Nat.floor_le hsq_pos.le
  have hsq_le_2Q : Real.sqrt (Real.log R) ≤ 2 * (Q : ℝ) := by
    have hlt : Real.sqrt (Real.log R) < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
    linarith
  have hRs_ge1 : 1 ≤ R ^ s := Real.one_le_rpow (by linarith [Real.add_one_le_exp (4 : ℝ)]) hs0
  -- Handle `s = 0` separately
  by_cases hs_zero : s = 0
  · subst hs_zero
    simp only [Real.rpow_zero, Nat.floor_one, Finset.Icc_self, Finset.sum_singleton,
      Nat.cast_one, Real.log_one, zero_div, intervalIntegral.integral_same, mul_zero, sub_zero]
    have ha1 := ha_asymp 1 le_rfl
    simp only [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Real.log_one, mul_zero,
      sub_zero, abs_of_nonneg (ha_nn 1)] at ha1
    have hf0 := hf_bd 0 ⟨le_rfl, le_rfl⟩
    calc |a 1 * f 0| = a 1 * |f 0| := by rw [abs_mul, abs_of_nonneg (ha_nn 1)]
      _ ≤ C * M := mul_le_mul ha1 hf0 (abs_nonneg _) hC
      _ ≤ (4 * c * L + 6 * C * M + 2 * C * L + 2 * L + 2 * M) * Real.sqrt (Real.log R) := by
          have h1 : 0 ≤ 4 * c * L + 2 * C * L + 2 * L + 2 * M := by positivity
          have h2 : 0 ≤ C * M := mul_nonneg hC hM
          nlinarith
  · have hs_pos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs_zero)
    -- Define grid points `t j = s * j / Q` for `j = 0, ..., Q`
    let tg : ℕ → ℝ := fun j => s * (j : ℝ) / (Q : ℝ)
    let xg : ℕ → ℝ := fun j => R ^ (tg j)
    have htg_mem : ∀ j ≤ Q, tg j ∈ Set.Icc (0 : ℝ) s := fun j hj => by
      refine ⟨by dsimp only [tg]; positivity, ?_⟩
      dsimp only [tg]
      rw [div_le_iff₀ hQ_pos]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hs0
    have hxg_ge1 : ∀ j ≤ Q, 1 ≤ xg j := fun j hj =>
      Real.one_le_rpow (by linarith [Real.add_one_le_exp (4 : ℝ)]) (htg_mem j hj).1
    have hxg_mono : ∀ j₁ j₂, j₁ ≤ j₂ → xg j₁ ≤ xg j₂ := fun j₁ j₂ h =>
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (4 : ℝ)])
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast h) hs0) hQ_pos.le)
    have htg_Q : tg Q = s := by dsimp only [tg]; field_simp [hQ_pos.ne']
    have hxg_Q : xg Q = R ^ s := by dsimp only [xg]; rw [htg_Q]
    have htg_0 : tg 0 = 0 := by simp [tg]
    have hxg_0 : xg 0 = 1 := by simp [xg, htg_0]
    -- Partition `Icc 1 ⌊R^s⌋₊` into `{1}` and `Ioc ⌊xg (j-1)⌋₊ ⌊xg j⌋₊` for `j ∈ Icc 1 Q`
    have hpart_sum : ∀ g : ℕ → ℝ,
        ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, g n =
          g 1 + ∑ j ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, g n := by
      intro g
      have htelesc : ∀ m ≤ Q,
          ∑ n ∈ Finset.Icc 1 ⌊xg m⌋₊, g n =
            g 1 + ∑ j ∈ Finset.Icc 1 m, ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, g n := by
        intro m
        induction m with
        | zero => simp [hxg_0]
        | succ m ih =>
          intro hm
          have hIcc_j : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have hle_fl : ⌊xg m⌋₊ ≤ ⌊xg (m + 1)⌋₊ :=
            Nat.floor_mono (hxg_mono m (m + 1) (Nat.le_succ m))
          have h1_le_fl : 1 ≤ ⌊xg m⌋₊ := Nat.le_floor (by simpa using hxg_ge1 m (by omega))
          have hunion : Finset.Icc 1 ⌊xg (m + 1)⌋₊ =
              Finset.Icc 1 ⌊xg m⌋₊ ∪ Finset.Ioc ⌊xg m⌋₊ ⌊xg (m + 1)⌋₊ := by
            ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
          have hdisj : Disjoint (Finset.Icc 1 ⌊xg m⌋₊) (Finset.Ioc ⌊xg m⌋₊ ⌊xg (m + 1)⌋₊) := by
            rw [Finset.disjoint_left]; intro n h1 h2
            simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
          rw [hunion, Finset.sum_union hdisj, ih (by omega), hIcc_j, Finset.sum_insert (by simp),
            Nat.add_sub_cancel]; ring
      simpa [hxg_Q] using htelesc Q le_rfl
    -- Step 1: Replace `f(log n / log R)` by `f(tg j)` on block `j`
    have hstep1 : |(∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R)) -
        (a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q,
          (∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) * f (tg j))| ≤
        (L / (Q : ℝ)) * (c * Real.log R + C) := by
      rw [hpart_sum (fun n => a n * f (Real.log (n : ℝ) / Real.log R))]
      simp only [Nat.cast_one, Real.log_one, zero_div]
      have hrew : (a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q,
            ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n * f (Real.log (n : ℝ) / Real.log R)) -
          (a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q,
            (∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) * f (tg j)) =
          ∑ j ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊,
            a n * (f (Real.log (n : ℝ) / Real.log R) - f (tg j)) := by
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => by ring
      rw [hrew]
      have hblk : ∀ j ∈ Finset.Icc 1 Q, ∀ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊,
          |a n * (f (Real.log (n : ℝ) / Real.log R) - f (tg j))| ≤ (L / (Q : ℝ)) * a n := by
        intro j hj n hn
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hjQ : j ≤ Q := (Finset.mem_Icc.mp hj).2
        have hn_gt : xg (j - 1) < (n : ℝ) := by
          have hfl : ⌊xg (j - 1)⌋₊ < n := (Finset.mem_Ioc.mp hn).1
          have : (⌊xg (j - 1)⌋₊ + 1 : ℕ) ≤ n := hfl
          have hlt := Nat.lt_floor_add_one (xg (j - 1))
          have hcast : ((⌊xg (j - 1)⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast this
          linarith
        have hn_le : (n : ℝ) ≤ xg j :=
          (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le (by positivity))
        have htn_lo : tg (j - 1) ≤ Real.log (n : ℝ) / Real.log R := by
          rw [le_div_iff₀ hlogR_pos]
          have hlog := Real.log_le_log (by positivity) hn_gt.le
          rw [Real.log_rpow hR_pos] at hlog; linarith
        have htn_hi : Real.log (n : ℝ) / Real.log R ≤ tg j := by
          rw [div_le_iff₀ hlogR_pos]
          have hlog := Real.log_le_log (by linarith [hxg_ge1 (j - 1) (by omega)]) hn_le
          rw [Real.log_rpow hR_pos] at hlog; linarith
        have htn_mem : Real.log (n : ℝ) / Real.log R ∈ Set.Icc (0 : ℝ) s :=
          ⟨(htg_mem (j - 1) (by omega)).1.trans htn_lo, htn_hi.trans (htg_mem j hjQ).2⟩
        have hdiff_t : |Real.log (n : ℝ) / Real.log R - tg j| ≤ 1 / (Q : ℝ) := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htn_hi)]
          have hgdiff : tg j - tg (j - 1) = s / (Q : ℝ) := by
            dsimp only [tg]
            rw [Nat.cast_sub hj1, Nat.cast_one]; ring
          calc tg j - Real.log (n : ℝ) / Real.log R
              ≤ tg j - tg (j - 1) := by linarith
            _ = s / (Q : ℝ) := hgdiff
            _ ≤ 1 / (Q : ℝ) := div_le_div_of_nonneg_right hs1 hQ_pos.le
        rw [abs_mul, abs_of_nonneg (ha_nn n)]
        calc a n * |f (Real.log (n : ℝ) / Real.log R) - f (tg j)|
            ≤ a n * (L * |Real.log (n : ℝ) / Real.log R - tg j|) :=
              mul_le_mul_of_nonneg_left (hf_lip _ htn_mem _ (htg_mem j hjQ)) (ha_nn n)
          _ ≤ a n * (L * (1 / (Q : ℝ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiff_t hL) (ha_nn n)
          _ = (L / (Q : ℝ)) * a n := by ring
      have htot_a : ∑ j ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n ≤
          c * Real.log R + C := by
        have h1 := hpart_sum a
        have h2 := ha_asymp (R ^ s) hRs_ge1
        rw [Real.log_rpow hR_pos] at h2
        have h3 : c * (s * Real.log R) ≤ c * Real.log R := by
          have : s * Real.log R ≤ 1 * Real.log R := mul_le_mul_of_nonneg_right hs1 hlogR_pos.le
          nlinarith
        linarith [(abs_le.mp h2).2, ha_nn 1]
      calc |∑ j ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊,
              a n * (f (Real.log (n : ℝ) / Real.log R) - f (tg j))|
          ≤ ∑ j ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊,
              |a n * (f (Real.log (n : ℝ) / Real.log R) - f (tg j))| :=
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ j ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, (L / (Q : ℝ)) * a n :=
            Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun n hn => hblk j hj n hn
        _ = (L / (Q : ℝ)) * ∑ j ∈ Finset.Icc 1 Q, ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n := by
            simp_rw [← Finset.mul_sum]
        _ ≤ (L / (Q : ℝ)) * (c * Real.log R + C) :=
            mul_le_mul_of_nonneg_left htot_a (by positivity)
    -- Step 2: Replace each block sum `∑_{Ioc} a n` by `c * (s / Q) * log R` (error `≤ 2 * C` per block)
    have hstep2 : |(a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q,
          (∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) * f (tg j)) -
        c * Real.log R * ∑ j ∈ Finset.Icc 1 Q, f (tg j) * (s / (Q : ℝ))| ≤
        (2 * (Q : ℝ) + 1) * C * M := by
      have ha1 : |a 1 * f 0| ≤ C * M := by
        have h1 := ha_asymp 1 le_rfl
        simp only [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Real.log_one, mul_zero,
          sub_zero, abs_of_nonneg (ha_nn 1)] at h1
        rw [abs_mul, abs_of_nonneg (ha_nn 1)]
        exact mul_le_mul h1 (hf_bd 0 ⟨le_rfl, hs0⟩) (abs_nonneg _) hC
      have hblk_diff : ∀ j ∈ Finset.Icc 1 Q,
          |(∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) - c * (s / (Q : ℝ)) * Real.log R| ≤ 2 * C := by
        intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hjQ : j ≤ Q := (Finset.mem_Icc.mp hj).2
        have hfl_le : ⌊xg (j - 1)⌋₊ ≤ ⌊xg j⌋₊ := Nat.floor_mono (hxg_mono _ _ (by omega))
        have hfl1 : 1 ≤ ⌊xg (j - 1)⌋₊ := Nat.le_floor (by simpa using hxg_ge1 (j - 1) (by omega))
        have hsum_diff : ∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n =
            (∑ n ∈ Finset.Icc 1 ⌊xg j⌋₊, a n) - (∑ n ∈ Finset.Icc 1 ⌊xg (j - 1)⌋₊, a n) := by
          have hunion : Finset.Icc 1 ⌊xg j⌋₊ =
              Finset.Icc 1 ⌊xg (j - 1)⌋₊ ∪ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊ := by
            ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
          have hdisj : Disjoint (Finset.Icc 1 ⌊xg (j - 1)⌋₊) (Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊) := by
            rw [Finset.disjoint_left]; intro n h1 h2
            simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
          rw [hunion, Finset.sum_union hdisj]; ring
        rw [hsum_diff]
        have ha_j := ha_asymp (xg j) (hxg_ge1 j hjQ)
        have ha_jm := ha_asymp (xg (j - 1)) (hxg_ge1 (j - 1) (by omega))
        dsimp only [xg] at ha_j ha_jm
        rw [Real.log_rpow hR_pos] at ha_j ha_jm
        have hgdiff : tg j - tg (j - 1) = s / (Q : ℝ) := by
          dsimp only [tg]; rw [Nat.cast_sub hj1, Nat.cast_one]; ring
        have hrew : ((∑ n ∈ Finset.Icc 1 ⌊xg j⌋₊, a n) - ∑ n ∈ Finset.Icc 1 ⌊xg (j - 1)⌋₊, a n) -
            c * (s / (Q : ℝ)) * Real.log R =
            ((∑ n ∈ Finset.Icc 1 ⌊xg j⌋₊, a n) - c * (tg j * Real.log R)) -
            ((∑ n ∈ Finset.Icc 1 ⌊xg (j - 1)⌋₊, a n) - c * (tg (j - 1) * Real.log R)) := by
          rw [← hgdiff]; ring
        rw [hrew]
        calc _ ≤ |(∑ n ∈ Finset.Icc 1 ⌊xg j⌋₊, a n) - c * (tg j * Real.log R)| +
                |(∑ n ∈ Finset.Icc 1 ⌊xg (j - 1)⌋₊, a n) - c * (tg (j - 1) * Real.log R)| :=
              abs_sub _ _
          _ ≤ C + C := add_le_add ha_j ha_jm
          _ = 2 * C := by ring
      have hrew2 : (a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q,
            (∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) * f (tg j)) -
          c * Real.log R * ∑ j ∈ Finset.Icc 1 Q, f (tg j) * (s / (Q : ℝ)) =
          a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q,
            ((∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) - c * (s / (Q : ℝ)) * Real.log R) *
              f (tg j) := by
        rw [Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
        congr 1; refine Finset.sum_congr rfl fun j _ => by ring
      rw [hrew2]
      calc |a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q, _|
          ≤ |a 1 * f 0| + ∑ j ∈ Finset.Icc 1 Q,
              |((∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) - c * (s / (Q : ℝ)) * Real.log R) *
                f (tg j)| := by
            linarith [abs_add_le (a 1 * f 0) (∑ j ∈ Finset.Icc 1 Q,
              ((∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) - c * (s / (Q : ℝ)) * Real.log R) *
                f (tg j)),
              Finset.abs_sum_le_sum_abs (fun j =>
                ((∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) - c * (s / (Q : ℝ)) * Real.log R) *
                  f (tg j)) (Finset.Icc 1 Q)]
        _ ≤ C * M + ∑ j ∈ Finset.Icc 1 Q, (2 * C) * M := by
            refine add_le_add ha1 (Finset.sum_le_sum fun j hj => ?_)
            rw [abs_mul]
            exact mul_le_mul (hblk_diff j hj) (hf_bd _ (htg_mem j (Finset.mem_Icc.mp hj).2))
              (abs_nonneg _) (by positivity)
        _ = (2 * (Q : ℝ) + 1) * C * M := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    -- Step 3: Compare Riemann sum `∑ f(tg j) * (s/Q)` to `∫_0^s f(t) dt` (error `≤ L / Q`)
    have hstep3 : |(∑ j ∈ Finset.Icc 1 Q, f (tg j) * (s / (Q : ℝ))) - ∫ t in (0 : ℝ)..s, f t| ≤
        L / (Q : ℝ) := by
      have hf_cont : ContinuousOn f (Set.Icc 0 s) := by
        refine Metric.continuousOn_iff.mpr fun t ht ε hε => ?_
        refine ⟨ε / (L + 1), by positivity, fun t' ht' htt' => ?_⟩
        rw [Real.dist_eq] at htt' ⊢
        calc |f t' - f t| ≤ L * |t' - t| := hf_lip t' ht' t ht
          _ ≤ (L + 1) * |t' - t| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left htt' (by linarith)
          _ = ε := by field_simp [show L + 1 ≠ 0 by linarith]
      have hint_split : ∫ t in (0 : ℝ)..s, f t =
          ∑ j ∈ Finset.Icc 1 Q, ∫ t in tg (j - 1)..tg j, f t := by
        have ht : ∀ m ≤ Q, ∫ t in (0 : ℝ)..tg m, f t =
            ∑ j ∈ Finset.Icc 1 m, ∫ t in tg (j - 1)..tg j, f t := by
          intro m
          induction m with
          | zero => simp [htg_0]
          | succ m ih =>
            intro hm
            have hIcc_j : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
              ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            have h1 : IntervalIntegrable f volume 0 (tg m) :=
              (hf_cont.mono (Set.Icc_subset_Icc_right (htg_mem m (by omega)).2)).intervalIntegrable_of_Icc
                (htg_mem m (by omega)).1
            have hle : tg m ≤ tg (m + 1) := by
              dsimp only [tg]; gcongr; exact_mod_cast Nat.le_succ m
            have h2 : IntervalIntegrable f volume (tg m) (tg (m + 1)) :=
              (hf_cont.mono (Set.Icc_subset_Icc (htg_mem m (by omega)).1
                (htg_mem (m + 1) hm).2)).intervalIntegrable_of_Icc hle
            rw [hIcc_j, Finset.sum_insert (by simp), ← ih (by omega), Nat.add_sub_cancel]
            have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
            linarith
        simpa [htg_Q] using ht Q le_rfl
      rw [hint_split, ← Finset.sum_sub_distrib]
      have hblk_int : ∀ j ∈ Finset.Icc 1 Q,
          |f (tg j) * (s / (Q : ℝ)) - ∫ t in tg (j - 1)..tg j, f t| ≤ L * (s / (Q : ℝ)) ^ 2 := by
        intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hjQ : j ≤ Q := (Finset.mem_Icc.mp hj).2
        have hgdiff : tg j - tg (j - 1) = s / (Q : ℝ) := by
          dsimp only [tg]; rw [Nat.cast_sub hj1, Nat.cast_one]; ring
        have hle : tg (j - 1) ≤ tg j := by linarith [show 0 ≤ s / (Q : ℝ) by positivity]
        have hconst : f (tg j) * (s / (Q : ℝ)) = ∫ _t in tg (j - 1)..tg j, f (tg j) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hgdiff, mul_comm]
        rw [hconst]
        have hint_f : IntervalIntegrable f volume (tg (j - 1)) (tg j) :=
          (hf_cont.mono (Set.Icc_subset_Icc (htg_mem (j - 1) (by omega)).1
            (htg_mem j hjQ).2)).intervalIntegrable_of_Icc hle
        rw [← intervalIntegral.integral_sub intervalIntegrable_const hint_f]
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := tg (j - 1))
          (b := tg j) (f := fun t => f (tg j) - f t) (C := L * (s / (Q : ℝ))) fun t ht => by
            rw [Set.uIoc_of_le hle] at ht
            have ht_mem : t ∈ Set.Icc (0 : ℝ) s :=
              ⟨(htg_mem (j - 1) (by omega)).1.trans ht.1.le, ht.2.trans (htg_mem j hjQ).2⟩
            rw [Real.norm_eq_abs]
            calc |f (tg j) - f t| ≤ L * |tg j - t| := hf_lip _ (htg_mem j hjQ) t ht_mem
              _ ≤ L * (s / (Q : ℝ)) := by
                  refine mul_le_mul_of_nonneg_left ?_ hL
                  rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith [ht.1]
        rw [Real.norm_eq_abs, hgdiff, abs_of_nonneg (div_nonneg hs0 hQ_pos.le)] at hnorm
        calc |∫ t in tg (j - 1)..tg j, (f (tg j) - f t)|
            ≤ L * (s / (Q : ℝ)) * (s / (Q : ℝ)) := hnorm
          _ = L * (s / (Q : ℝ)) ^ 2 := by ring
      calc |∑ j ∈ Finset.Icc 1 Q, (f (tg j) * (s / (Q : ℝ)) - ∫ t in tg (j - 1)..tg j, f t)|
          ≤ ∑ j ∈ Finset.Icc 1 Q, |f (tg j) * (s / (Q : ℝ)) - ∫ t in tg (j - 1)..tg j, f t| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.Icc 1 Q, L * (s / (Q : ℝ)) ^ 2 := Finset.sum_le_sum hblk_int
        _ = L * s ^ 2 / (Q : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
            field_simp [hQ_pos.ne']
        _ ≤ L / (Q : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ hQ_pos.le
            have hs2 : s ^ 2 ≤ 1 := by nlinarith
            nlinarith
    -- Combine Steps 1, 2, 3!
    have hcomb := abs_sub_le
      (∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R))
      (a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q, (∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) * f (tg j))
      (c * Real.log R * (∫ t in (0 : ℝ)..s, f t))
    have hcomb2 := abs_sub_le
      (a 1 * f 0 + ∑ j ∈ Finset.Icc 1 Q, (∑ n ∈ Finset.Ioc ⌊xg (j - 1)⌋₊ ⌊xg j⌋₊, a n) * f (tg j))
      (c * Real.log R * ∑ j ∈ Finset.Icc 1 Q, f (tg j) * (s / (Q : ℝ)))
      (c * Real.log R * (∫ t in (0 : ℝ)..s, f t))
    have hstep3' : |c * Real.log R * ∑ j ∈ Finset.Icc 1 Q, f (tg j) * (s / (Q : ℝ)) -
        c * Real.log R * ∫ t in (0 : ℝ)..s, f t| ≤ c * Real.log R * (L / (Q : ℝ)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg hc hlogR_pos.le)]
      exact mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hc hlogR_pos.le)
    have hlogR_div_Q : Real.log R / (Q : ℝ) ≤ 2 * Real.sqrt (Real.log R) := by
      rw [div_le_iff₀ hQ_pos]
      have hsq2 : Real.sqrt (Real.log R) * Real.sqrt (Real.log R) = Real.log R :=
        Real.mul_self_sqrt hlogR_pos.le
      nlinarith
    have h1_div_Q : 1 / (Q : ℝ) ≤ Real.sqrt (Real.log R) := by
      have : 1 / (Q : ℝ) ≤ 1 := by rw [div_le_one hQ_pos]; exact_mod_cast (by omega : 1 ≤ Q)
      linarith
    have h2Q1 : (2 * (Q : ℝ) + 1) ≤ 3 * Real.sqrt (Real.log R) := by linarith
    have hb1 : (L / (Q : ℝ)) * (c * Real.log R + C) ≤
        (2 * c * L + C * L) * Real.sqrt (Real.log R) := by
      have hA : (L / (Q : ℝ)) * (c * Real.log R) = c * L * (Real.log R / (Q : ℝ)) := by ring
      have hB : (L / (Q : ℝ)) * C = C * L * (1 / (Q : ℝ)) := by ring
      have hA_le : c * L * (Real.log R / (Q : ℝ)) ≤ 2 * c * L * Real.sqrt (Real.log R) := by
        nlinarith [mul_nonneg hc hL]
      have hB_le : C * L * (1 / (Q : ℝ)) ≤ C * L * Real.sqrt (Real.log R) := by
        nlinarith [mul_nonneg hC hL]
      nlinarith
    have hb2 : (2 * (Q : ℝ) + 1) * C * M ≤ 6 * C * M * Real.sqrt (Real.log R) := by
      have : 0 ≤ C * M := mul_nonneg hC hM
      nlinarith
    have hb3 : c * Real.log R * (L / (Q : ℝ)) ≤ 2 * c * L * Real.sqrt (Real.log R) := by
      have : c * Real.log R * (L / (Q : ℝ)) = c * L * (Real.log R / (Q : ℝ)) := by ring
      nlinarith [mul_nonneg hc hL]
    have hnn_extra : 0 ≤ (C * L + 2 * L + 2 * M) * Real.sqrt (Real.log R) := by positivity
    linarith

/-- **`k`-Dimensional Uniform Sum-to-Integral Theorem** (by induction on `k` using
`sum_1d_approx_integral`): for any `k : ℕ`, any weight `a` with `|∑_{n ≤ x} a n - c * log x| ≤ C`,
and any Lipschitz parameters `(M, L)`, there exists `K_err ≥ 0` (independent of `R, s, G`) such that
for all `R ≥ exp 4`, all `s ∈ [0, 1]`, and all `(M, L)`-Lipschitz `G` on `Δ_k(s)`:
`|∑_{∏ r_i ≤ R^s} (∏ i, a (r i)) * G (log r_i / log R) - (c * log R)^k * simplexIntegral k s G| ≤
  K_err * (log R)^(k - 1/2)`. -/
theorem sum_kd_approx_integral_uniform (k : ℕ) {a : ℕ → ℝ} {c C : ℝ}
    (ha_nn : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (ha_asymp : ∀ x : ℝ, 1 ≤ x → |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) - c * Real.log x| ≤ C)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ K_err : ℝ, 0 ≤ K_err ∧ ∀ R : ℝ, Real.exp 4 ≤ R → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ G : (Fin k → ℝ) → ℝ, IsSimplexLipOn s M L G →
        |(∑ r ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R ^ s⌋₊)).filter
              (fun r => ((∏ i, r i : ℕ) : ℝ) ≤ R ^ s),
            (∏ i, a (r i)) * G (fun i => Real.log (r i : ℝ) / Real.log R)) -
          (c * Real.log R) ^ k * simplexIntegral k s G| ≤
          K_err * (Real.log R) ^ ((k : ℝ) - 1 / 2) := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, fun R hR s hs0 _ G _ => ?_⟩
    have hRs1 : 1 ≤ R ^ s := Real.one_le_rpow (by linarith [Real.add_one_le_exp (4 : ℝ)]) hs0
    have hfilt : (Fintype.piFinset (fun _ : Fin 0 => Finset.Icc 1 ⌊R ^ s⌋₊)).filter
        (fun r => ((∏ i, r i : ℕ) : ℝ) ≤ R ^ s) = {Fin.elim0} := by
      ext r
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim r Fin.elim0,
        fun _ => ⟨fun i => Fin.elim0 i, by simpa using hRs1⟩⟩
    rw [hfilt, Finset.sum_singleton]
    have hfun : (fun i : Fin 0 => Real.log ((Fin.elim0 i : ℕ) : ℝ) / Real.log R) = Fin.elim0 :=
      Subsingleton.elim _ _
    simp [simplexIntegral, hfun]
  | succ k ih =>
    obtain ⟨K_prev, hKp_nn, hKp⟩ := ih
    set L' : ℝ := L + (k : ℝ) * M
    have hL'_nn : 0 ≤ L' := by positivity
    set K_1d : ℝ := 4 * c * L' + 6 * C * M + 2 * C * L' + 2 * L' + 2 * M
    have hK1d_nn : 0 ≤ K_1d := by positivity
    set K_new : ℝ := (c + C) * K_prev + c ^ k * K_1d
    have hKnew_nn : 0 ≤ K_new := by positivity
    refine ⟨K_new, hKnew_nn, fun R hR s hs0 hs1 G hG => ?_⟩
    have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
    have hlogR_ge4 : 4 ≤ Real.log R := by
      have := Real.log_le_log (Real.exp_pos 4) hR; rwa [Real.log_exp] at this
    have hlogR_pos : 0 < Real.log R := by linarith
    have hRs1 : 1 ≤ R ^ s := Real.one_le_rpow (by linarith [Real.add_one_le_exp (4 : ℝ)]) hs0
    -- Factor the `(k + 1)`-tuple sum into an outer sum over `n = r 0 ∈ Icc 1 ⌊R^s⌋₊`
    -- and an inner sum over `r' : Fin k → ℕ` with `∏ r' i ≤ R^{s - log n / log R}`
    let S_full := (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 ⌊R ^ s⌋₊)).filter
        (fun r => ((∏ i, r i : ℕ) : ℝ) ≤ R ^ s)
    let innerS : ℕ → Finset (Fin k → ℕ) := fun n =>
      (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R ^ (s - Real.log (n : ℝ) / Real.log R)⌋₊)).filter
        (fun r' => ((∏ i, r' i : ℕ) : ℝ) ≤ R ^ (s - Real.log (n : ℝ) / Real.log R))
    have hR_sub : ∀ n : ℕ, 1 ≤ n → R ^ (s - Real.log (n : ℝ) / Real.log R) = R ^ s / (n : ℝ) := by
      intro n hn
      rw [Real.rpow_sub hR_pos]
      congr 1
      rw [Real.rpow_def_of_pos hR_pos, mul_div_cancel₀ _ hlogR_pos.ne',
        Real.exp_log (Nat.cast_pos.mpr hn)]
    have hsplit_sum :
        ∑ r ∈ S_full, (∏ i, a (r i)) * G (fun i => Real.log (r i : ℝ) / Real.log R) =
        ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n *
          ∑ r' ∈ innerS n, (∏ i, a (r' i)) *
            G (Fin.cons (Real.log (n : ℝ) / Real.log R) (fun i => Real.log (r' i : ℝ) / Real.log R)) := by
      simp_rw [Finset.mul_sum]
      have hsig : (∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, ∑ r' ∈ innerS n,
            a n * ((∏ i, a (r' i)) *
              G (Fin.cons (Real.log (n : ℝ) / Real.log R) (fun i => Real.log (r' i : ℝ) / Real.log R)))) =
          ∑ x ∈ (Finset.Icc 1 ⌊R ^ s⌋₊).sigma innerS,
            a x.1 * ((∏ i, a (x.2 i)) *
              G (Fin.cons (Real.log (x.1 : ℝ) / Real.log R) (fun i => Real.log (x.2 i : ℝ) / Real.log R))) :=
        (Finset.sum_sigma (Finset.Icc 1 ⌊R ^ s⌋₊) innerS
          (fun x : Σ _ : ℕ, (Fin k → ℕ) =>
            a x.1 * ((∏ i, a (x.2 i)) *
              G (Fin.cons (Real.log (x.1 : ℝ) / Real.log R)
                (fun i => Real.log (x.2 i : ℝ) / Real.log R))))).symm
      rw [hsig]
      refine Finset.sum_bij (fun r _ => ⟨r 0, Fin.tail r⟩) ?_ ?_ ?_ ?_
      · intro r hr
        simp only [S_full, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hr
        obtain ⟨hr_mem, hr_prod⟩ := hr
        have hr0_1 : 1 ≤ r 0 := (hr_mem 0).1
        have hr0_pos : (0 : ℝ) < (r 0 : ℝ) := Nat.cast_pos.mpr hr0_1
        have htail_prod : ((∏ i : Fin k, Fin.tail r i : ℕ) : ℝ) ≤ R ^ (s - Real.log (r 0 : ℝ) / Real.log R) := by
          rw [hR_sub (r 0) hr0_1, le_div_iff₀ hr0_pos]
          rw [Fin.prod_univ_succ] at hr_prod
          push_cast at hr_prod
          simpa [Fin.tail, mul_comm] using hr_prod
        simp only [Finset.mem_sigma, Finset.mem_Icc, innerS, Finset.mem_filter,
          Fintype.mem_piFinset]
        refine ⟨hr_mem 0, fun i => ⟨(hr_mem i.succ).1, ?_⟩, htail_prod⟩
        refine Nat.le_floor ?_
        have hi_le : (r i.succ : ℝ) ≤ ((∏ j : Fin k, Fin.tail r j : ℕ) : ℝ) := by
          exact_mod_cast Finset.single_le_prod' (f := Fin.tail r) (fun j _ => (hr_mem j.succ).1) (Finset.mem_univ i)
        exact hi_le.trans htail_prod
      · intro r₁ _ r₂ _ heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        ext i
        refine Fin.cases heq.1 (fun j => ?_) i
        exact congrFun heq.2 j
      · intro x hx
        simp only [Finset.mem_sigma, Finset.mem_Icc, innerS, Finset.mem_filter,
          Fintype.mem_piFinset] at hx
        obtain ⟨⟨hx1, hxfl⟩, hx_mem, hx_prod⟩ := hx
        have hx1_pos : (0 : ℝ) < (x.1 : ℝ) := Nat.cast_pos.mpr hx1
        have hprod_le : ((∏ i : Fin (k + 1), (Fin.cons x.1 x.2 : Fin (k + 1) → ℕ) i : ℕ) : ℝ) ≤ R ^ s := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hR_sub x.1 hx1, le_div_iff₀ hx1_pos] at hx_prod
          rw [Nat.cast_mul]; linarith
        refine ⟨Fin.cons x.1 x.2, ?_, ?_⟩
        · simp only [S_full, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
          refine ⟨fun i => Fin.cases ⟨hx1, hxfl⟩ (fun j => ⟨(hx_mem j).1, ?_⟩) i, hprod_le⟩
          refine Nat.le_floor ?_
          have h1 : (x.2 j : ℝ) ≤ R ^ (s - Real.log (x.1 : ℝ) / Real.log R) :=
            (Nat.cast_le.mpr (hx_mem j).2).trans (Nat.floor_le (by positivity))
          rw [hR_sub x.1 hx1] at h1
          exact h1.trans (div_le_self (by positivity) (by exact_mod_cast hx1))
        · rfl
      · intro r _
        rw [Fin.prod_univ_succ]
        have hfun : (fun i : Fin (k + 1) => Real.log (r i : ℝ) / Real.log R) =
            Fin.cons (Real.log (r 0 : ℝ) / Real.log R)
              (fun i : Fin k => Real.log (Fin.tail r i : ℝ) / Real.log R) := by
          ext i; refine Fin.cases rfl (fun j => rfl) i
        rw [hfun]; simp [Fin.tail]; ring
    rw [hsplit_sum]
    -- Define the 1D slice function `f(t) = simplexIntegral k (s - t) (G (cons t ·))`
    let f : ℝ → ℝ := fun t => simplexIntegral k (s - t) (fun v => G (Fin.cons t v))
    -- Bound the difference between the inner sum and `(c * log R)^k * f(log n / log R)` via IH
    have hinner_diff : ∀ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊,
        |(∑ r' ∈ innerS n, (∏ i, a (r' i)) *
            G (Fin.cons (Real.log (n : ℝ) / Real.log R) (fun i => Real.log (r' i : ℝ) / Real.log R))) -
          (c * Real.log R) ^ k * f (Real.log (n : ℝ) / Real.log R)| ≤
          K_prev * (Real.log R) ^ ((k : ℝ) - 1 / 2) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_le : (n : ℝ) ≤ R ^ s :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (by positivity))
      set t := Real.log (n : ℝ) / Real.log R
      have ht0 : 0 ≤ t := div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) hlogR_pos.le
      have hts : t ≤ s := by
        dsimp only [t]
        rw [div_le_iff₀ hlogR_pos]
        have hlog := Real.log_le_log (Nat.cast_pos.mpr hn1) hn_le
        rwa [Real.log_rpow hR_pos] at hlog
      exact hKp R hR (s - t) (by linarith) (by linarith) (fun v => G (Fin.cons t v)) (hG.cons ht0)
    -- Step A: Replace inner sum by `(c * log R)^k * f(log n / log R)`
    have hA_sum : ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n ≤ (c + C) * Real.log R := by
      have ha_bd := ha_asymp (R ^ s) hRs1
      rw [Real.log_rpow hR_pos] at ha_bd
      have h1 : c * (s * Real.log R) ≤ c * Real.log R := by
        have : s * Real.log R ≤ 1 * Real.log R := mul_le_mul_of_nonneg_right hs1 hlogR_pos.le
        nlinarith
      have h2 : C ≤ C * Real.log R := by nlinarith
      linarith [(abs_le.mp ha_bd).2]
    have hstepA : |(∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n *
          ∑ r' ∈ innerS n, (∏ i, a (r' i)) *
            G (Fin.cons (Real.log (n : ℝ) / Real.log R) (fun i => Real.log (r' i : ℝ) / Real.log R))) -
        (c * Real.log R) ^ k *
          ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R)| ≤
        (c + C) * K_prev * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
      have hrew : (∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n *
            ∑ r' ∈ innerS n, (∏ i, a (r' i)) *
              G (Fin.cons (Real.log (n : ℝ) / Real.log R) (fun i => Real.log (r' i : ℝ) / Real.log R))) -
          (c * Real.log R) ^ k * ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R) =
          ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n *
            ((∑ r' ∈ innerS n, (∏ i, a (r' i)) *
              G (Fin.cons (Real.log (n : ℝ) / Real.log R) (fun i => Real.log (r' i : ℝ) / Real.log R))) -
              (c * Real.log R) ^ k * f (Real.log (n : ℝ) / Real.log R)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => by ring
      rw [hrew]
      have hrpow_eq : Real.log R * (Real.log R) ^ ((k : ℝ) - 1 / 2) =
          (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
        calc Real.log R * (Real.log R) ^ ((k : ℝ) - 1 / 2)
            = (Real.log R) ^ (1 : ℝ) * (Real.log R) ^ ((k : ℝ) - 1 / 2) := by rw [Real.rpow_one]
          _ = (Real.log R) ^ ((1 : ℝ) + ((k : ℝ) - 1 / 2)) := (Real.rpow_add hlogR_pos _ _).symm
          _ = (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by congr 1; push_cast; ring
      calc |∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, _|
          ≤ ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊,
              |a n * ((∑ r' ∈ innerS n, _) - (c * Real.log R) ^ k * f (Real.log (n : ℝ) / Real.log R))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * (K_prev * (Real.log R) ^ ((k : ℝ) - 1 / 2)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            rw [abs_mul, abs_of_nonneg (ha_nn n)]
            exact mul_le_mul_of_nonneg_left (hinner_diff n hn) (ha_nn n)
        _ = (∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n) * (K_prev * (Real.log R) ^ ((k : ℝ) - 1 / 2)) := by
            rw [← Finset.sum_mul]
        _ ≤ ((c + C) * Real.log R) * (K_prev * (Real.log R) ^ ((k : ℝ) - 1 / 2)) :=
            mul_le_mul_of_nonneg_right hA_sum (by positivity)
        _ = (c + C) * K_prev * (Real.log R * (Real.log R) ^ ((k : ℝ) - 1 / 2)) := by ring
        _ = (c + C) * K_prev * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by rw [hrpow_eq]
    -- Step B: Apply `sum_1d_approx_integral` to `f`
    have hf_bd : ∀ t ∈ Set.Icc (0 : ℝ) s, |f t| ≤ M := fun t ht =>
      (simplexIntegral_props k).1 (s - t) M L (fun v => G (Fin.cons t v))
        (by linarith [ht.2]) (by linarith [ht.1]) (hG.cons ht.1)
    have hf_lip : ∀ t₁ ∈ Set.Icc (0 : ℝ) s, ∀ t₂ ∈ Set.Icc (0 : ℝ) s, |f t₁ - f t₂| ≤ L' * |t₁ - t₂| :=
      fun t₁ ht₁ t₂ ht₂ => simplexIntegral_slice_lipschitz hs0 hs1 hG ht₁ ht₂
    have h1d := sum_1d_approx_integral ha_nn hc hC ha_asymp hs0 hs1 hM hL'_nn hR hf_bd hf_lip
    have hstepB : |(c * Real.log R) ^ k *
          (∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R)) -
        (c * Real.log R) ^ (k + 1) * simplexIntegral (k + 1) s G| ≤
        c ^ k * K_1d * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
      have hrew : (c * Real.log R) ^ k *
            (∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R)) -
          (c * Real.log R) ^ (k + 1) * simplexIntegral (k + 1) s G =
          (c * Real.log R) ^ k *
            ((∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R)) -
              c * Real.log R * (∫ t in (0 : ℝ)..s, f t)) := by
        dsimp only [simplexIntegral, f]; rw [pow_succ]; ring
      rw [hrew, abs_mul, abs_of_nonneg (pow_nonneg (mul_nonneg hc hlogR_pos.le) k)]
      have hrpow_eq : (Real.log R) ^ k * Real.sqrt (Real.log R) =
          (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.log R) k, ← Real.rpow_add hlogR_pos]
        congr 1; push_cast; ring
      calc (c * Real.log R) ^ k * |(∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R)) -
              c * Real.log R * ∫ t in (0 : ℝ)..s, f t|
          ≤ (c * Real.log R) ^ k * (K_1d * Real.sqrt (Real.log R)) :=
            mul_le_mul_of_nonneg_left h1d (pow_nonneg (mul_nonneg hc hlogR_pos.le) k)
        _ = c ^ k * K_1d * ((Real.log R) ^ k * Real.sqrt (Real.log R)) := by rw [mul_pow]; ring
        _ = c ^ k * K_1d * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by rw [hrpow_eq]
    have htri := abs_sub_le
      (∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n *
        ∑ r' ∈ innerS n, (∏ i, a (r' i)) *
          G (Fin.cons (Real.log (n : ℝ) / Real.log R) (fun i => Real.log (r' i : ℝ) / Real.log R)))
      ((c * Real.log R) ^ k * ∑ n ∈ Finset.Icc 1 ⌊R ^ s⌋₊, a n * f (Real.log (n : ℝ) / Real.log R))
      ((c * Real.log R) ^ (k + 1) * simplexIntegral (k + 1) s G)
    calc _ ≤ (c + C) * K_prev * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) +
            c ^ k * K_1d * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by linarith
      _ = K_new * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by dsimp only [K_new]; ring

/-- Specialization of `sum_kd_approx_integral_uniform` to `s = 1`. -/
theorem sum_kd_approx_integral (k : ℕ) {a : ℕ → ℝ} {c C : ℝ}
    (ha_nn : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (ha_asymp : ∀ x : ℝ, 1 ≤ x → |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) - c * Real.log x| ≤ C)
    {M L : ℝ} {G : (Fin k → ℝ) → ℝ} (hG : IsSimplexLipOn 1 M L G) :
    ∃ K_err : ℝ, 0 ≤ K_err ∧ ∀ R : ℝ, Real.exp 4 ≤ R →
      |(∑ r ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R⌋₊)).filter
            (fun r => ((∏ i, r i : ℕ) : ℝ) ≤ R),
          (∏ i, a (r i)) * G (fun i => Real.log (r i : ℝ) / Real.log R)) -
        (c * Real.log R) ^ k * simplexIntegral k 1 G| ≤
        K_err * (Real.log R) ^ ((k : ℝ) - 1 / 2) := by
  obtain ⟨K_err, hK_nn, hK⟩ := sum_kd_approx_integral_uniform k ha_nn hc hC ha_asymp M L hG.1 hG.2.1
  refine ⟨K_err, hK_nn, fun R hR => ?_⟩
  simpa only [Real.rpow_one] using hK R hR 1 zero_le_one le_rfl G hG

/-! ## Section 3: Multidimensional Selberg Sieve Algebra, Möbius Inversion, and CRT -/

/-- Master divisor-sum formula for squarefree integers:
`∑_{d ∣ q} ∏_{p ∈ d.primeFactors} f p = ∏_{p ∈ q.primeFactors} (1 + f p)`. -/
lemma sum_divisors_prod_of_squarefree {q : ℕ} (hq : Squarefree q) (f : ℕ → ℝ) :
    ∑ d ∈ q.divisors, (∏ p ∈ d.primeFactors, f p) = ∏ p ∈ q.primeFactors, (1 + f p) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  rw [Finset.prod_one_add]
  refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hq0
  · intro d₁ hd₁ d₂ hd₂ heq
    have hsf1 : Squarefree d₁ := hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd₁)
    have hsf2 : Squarefree d₂ := hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd₂)
    rw [← rad_eq_self_of_squarefree hsf1, ← rad_eq_self_of_squarefree hsf2]
    unfold rad; rw [heq]
  · intro T hT
    rw [Finset.mem_powerset] at hT
    refine ⟨∏ p ∈ T, p, ?_, ?_⟩
    · rw [Nat.mem_divisors]
      refine ⟨?_, hq0⟩
      rw [← rad_eq_self_of_squarefree hq]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hT
    · have hT_prime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
      induction T using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have haP : a.Prime := hT_prime a (mem_insert_self a s)
        have hsP : ∀ r ∈ s, r.Prime := fun r hr => hT_prime r (mem_insert_of_mem hr)
        have hsne : ∏ r ∈ s, r ≠ 0 := (Finset.prod_pos fun r hr => (hsP r hr).pos).ne'
        rw [Finset.prod_insert ha, Nat.primeFactors_mul haP.ne_zero hsne, haP.primeFactors,
          ih (Finset.Subset.trans (Finset.subset_insert a s) hT) hsP]
        ext x; simp
  · intro _ _; rfl

/-- Product of sums over a `Fintype.piFinset`:
`∑ c ∈ Fintype.piFinset s, ∏ i, f i (c i) = ∏ i, ∑ x ∈ s i, f i x`. -/
lemma sum_piFinset_prod {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : ι → Finset α) (f : ι → α → ℝ) :
    ∑ c ∈ Fintype.piFinset s, ∏ i, f i (c i) = ∏ i, ∑ x ∈ s i, f i x := by
  rw [Finset.prod_sum]
  symm
  refine Finset.sum_bij (fun g _ i => g i (Finset.mem_univ i)) ?_ ?_ ?_ ?_
  · intro g hg
    rw [Fintype.mem_piFinset]
    intro i; exact Finset.mem_pi.mp hg i (Finset.mem_univ i)
  · intro g₁ _ g₂ _ heq
    funext i hi
    exact congrFun heq i
  · intro c hc
    refine ⟨fun i _ => c i, ?_, rfl⟩
    rw [Finset.mem_pi]; intro i _; exact Fintype.mem_piFinset.mp hc i
  · intro g _
    exact Finset.prod_attach Finset.univ (fun i => f i (g i (Finset.mem_univ i)))

/-- For squarefree `n`, `(μ n : ℝ) = ∏_{p ∈ n.primeFactors} (-1)`. -/
lemma moebius_eq_prod_neg_one_of_squarefree {n : ℕ} (hn : Squarefree n) :
    (μ n : ℝ) = ∏ _p ∈ n.primeFactors, (-1 : ℝ) := by
  have hprod : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      (μ (∏ p ∈ s, p) : ℝ) = ∏ _p ∈ s, (-1 : ℝ) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have haP : a.Prime := hs a (mem_insert_self a s)
      have hsP : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
      have hcop : Nat.Coprime a (∏ q ∈ s, q) :=
        Nat.Coprime.prod_right fun q hq =>
          (Nat.coprime_primes haP (hsP q hq)).mpr (fun h => ha (h ▸ hq))
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hmul : (μ (a * ∏ q ∈ s, q) : ℝ) = (μ a : ℝ) * (μ (∏ q ∈ s, q) : ℝ) := by
        exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      rw [hmul, ih hsP, ArithmeticFunction.moebius_apply_prime haP]; simp
  conv_lhs => rw [← rad_eq_self_of_squarefree hn]
  exact hprod n.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp

/-- For squarefree `n`, `(n.totient : ℝ) = ∏_{p ∈ n.primeFactors} ((p : ℝ) - 1)`. -/
lemma totient_eq_prod_sub_one_of_squarefree {n : ℕ} (hn : Squarefree n) :
    (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hnat : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_prod_factorization hn0]
    simp only [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h1 : 1 ≤ n.factorization p :=
      (hpp.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp)
    have h2 : n.factorization p ≤ 1 := by
      by_contra hgt; push Not at hgt
      have hp2 : p * p ∣ n := by
        simpa [sq] using (hpp.pow_dvd_iff_le_factorization hn0).mpr (by omega : 2 ≤ _)
      exact hpp.ne_one (Nat.isUnit_iff.mp (hn p hp2))
    have heq : n.factorization p = 1 := by omega
    rw [heq, pow_zero, one_mul]
  rw [hnat, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

/-- Möbius sum over divisors of a squarefree integer `q`: `∑_{d ∣ q} μ d = if q = 1 then 1 else 0`. -/
lemma sum_moebius_divisors_of_squarefree {q : ℕ} (hq : Squarefree q) :
    ∑ d ∈ q.divisors, (μ d : ℝ) = if q = 1 then 1 else 0 := by
  have h1 : ∑ d ∈ q.divisors, (μ d : ℝ) = ∑ d ∈ q.divisors, ∏ _p ∈ d.primeFactors, (-1 : ℝ) :=
    Finset.sum_congr rfl fun d hd =>
      moebius_eq_prod_neg_one_of_squarefree (hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  rw [h1, sum_divisors_prod_of_squarefree hq]
  by_cases hq1 : q = 1
  · subst hq1; simp
  · rw [if_neg hq1]
    obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
    have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne_zero⟩
    exact Finset.prod_eq_zero hpmem (by norm_num)

/-- Second Selberg divisor identity for squarefree `q`:
`∑_{c ∣ q} μ(c) * c / φ(c) = μ(q) / φ(q)`. -/
lemma sum_moebius_mul_div_totient_of_squarefree {q : ℕ} (hq : Squarefree q) :
    ∑ c ∈ q.divisors, (μ c : ℝ) * (c : ℝ) / ((c.totient : ℝ)) =
      (μ q : ℝ) / ((q.totient : ℝ)) := by
  have h1 : ∑ c ∈ q.divisors, (μ c : ℝ) * (c : ℝ) / ((c.totient : ℝ)) =
      ∑ c ∈ q.divisors, ∏ p ∈ c.primeFactors, (-(p : ℝ) / ((p : ℝ) - 1)) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcsf : Squarefree c := hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hc)
    rw [moebius_eq_prod_neg_one_of_squarefree hcsf, totient_eq_prod_sub_one_of_squarefree hcsf]
    have hc_eq : (c : ℝ) = ∏ p ∈ c.primeFactors, (p : ℝ) := by
      conv_lhs => rw [← rad_eq_self_of_squarefree hcsf]
      unfold rad; rw [Nat.cast_prod]
    rw [hc_eq, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p _ => by ring
  rw [h1, sum_divisors_prod_of_squarefree hq, moebius_eq_prod_neg_one_of_squarefree hq,
    totient_eq_prod_sub_one_of_squarefree hq, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]; ring

/-- Divisor sum of `g₂` for odd squarefree `n`: `∑_{u ∣ n} g₂(u) = φ(n)`. -/
lemma sum_g2_divisors_eq_totient {n : ℕ} (hn : Squarefree n) (hodd : Nat.Coprime n 2) :
    ∑ u ∈ n.divisors, (g₂ u : ℝ) = (n.totient : ℝ) := by
  have h1 : ∑ u ∈ n.divisors, (g₂ u : ℝ) =
      ∑ u ∈ n.divisors, ∏ p ∈ u.primeFactors, ((p - 2 : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun u _ => by unfold g₂; rw [Nat.cast_prod]
  rw [h1, sum_divisors_prod_of_squarefree hn, totient_eq_prod_sub_one_of_squarefree hn]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    intro h2; rw [h2] at hpdvd
    exact absurd (hodd.coprime_dvd_left hpdvd) (by decide)
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  rw [Nat.cast_sub (by omega : 2 ≤ p)]; push_cast; ring

/-- Divisor sum of `φ` for squarefree `n`: `∑_{u ∣ n} φ(u) = n`. -/
lemma sum_totient_divisors_eq_self (n : ℕ) :
    ∑ u ∈ n.divisors, (u.totient : ℝ) = (n : ℝ) := by
  exact_mod_cast Nat.sum_totient n

/-- `Squarefree (∏ i, d i)` implies every coordinate is squarefree and distinct coordinates
are pairwise coprime. -/
lemma squarefree_prod_coord {ι : Type*} [DecidableEq ι] {s : Finset ι} {d : ι → ℕ}
    (hsf : Squarefree (∏ i ∈ s, d i)) :
    (∀ i ∈ s, Squarefree (d i)) ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (d i) (d j)) := by
  refine ⟨fun i hi => hsf.squarefree_of_dvd (Finset.dvd_prod_of_mem d hi), ?_⟩
  intro i hi j hj hij
  have hdvd : d i * d j ∣ ∏ r ∈ s, d r := by
    have hsub : ({i, j} : Finset ι) ⊆ s := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h1 := Finset.prod_dvd_prod_of_subset ({i, j} : Finset ι) s d hsub
    rwa [Finset.prod_pair hij] at h1
  exact Nat.coprime_of_squarefree_mul (hsf.squarefree_of_dvd hdvd)

/-- Converse: pairwise coprime squarefree factors have a squarefree product. -/
lemma squarefree_prod_of_pairwise {ι : Type*} [DecidableEq ι] {s : Finset ι} {d : ι → ℕ}
    (hsf : ∀ i ∈ s, Squarefree (d i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (d i) (d j)) :
    Squarefree (∏ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simp [squarefree_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_sf : Squarefree (d a) := hsf a (mem_insert_self a s)
    have hs_sf : Squarefree (∏ i ∈ s, d i) :=
      ih (fun i hi => hsf i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hcop i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
    have hacop : Nat.Coprime (d a) (∏ i ∈ s, d i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (mem_insert_self a s) i (mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    exact (Nat.squarefree_mul hacop).mpr ⟨ha_sf, hs_sf⟩

/-- Valid support tuples for the `(k + 1)`-dimensional Maynard–Tao Selberg sieve at modulus `W₀`
and level `R`: `1 ≤ d_i`, `∏ d_i ≤ R`, `Squarefree (∏ d_i)`, `Coprime (∏ d_i) W₀`. -/
def validTupleSet (k W₀ : ℕ) (R : ℝ) : Finset (Fin (k + 1) → ℕ) :=
  (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 ⌊R⌋₊)).filter
    (fun d => ((∏ i, d i : ℕ) : ℝ) ≤ R ∧ Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W₀)

lemma mem_validTupleSet {k W₀ : ℕ} {R : ℝ} (hR : 0 ≤ R) {d : Fin (k + 1) → ℕ} :
    d ∈ validTupleSet k W₀ R ↔
      (∀ i, 1 ≤ d i) ∧ ((∏ i, d i : ℕ) : ℝ) ≤ R ∧
      Squarefree (∏ i, d i) ∧ Nat.Coprime (∏ i, d i) W₀ := by
  simp only [validTupleSet, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hmem, hprod, hsf, hcop⟩
    exact ⟨fun i => (hmem i).1, hprod, hsf, hcop⟩
  · rintro ⟨h1, hprod, hsf, hcop⟩
    refine ⟨fun i => ⟨h1 i, Nat.le_floor ?_⟩, hprod, hsf, hcop⟩
    have hi_le : (d i : ℝ) ≤ ((∏ j, d j : ℕ) : ℝ) := by
      exact_mod_cast Finset.single_le_prod' (f := d) (fun j _ => h1 j) (Finset.mem_univ i)
    exact hi_le.trans hprod

lemma validTupleSet_of_dvd {k W₀ : ℕ} {R : ℝ} (hR : 0 ≤ R) {d r : Fin (k + 1) → ℕ}
    (hr : r ∈ validTupleSet k W₀ R) (hd1 : ∀ i, 1 ≤ d i) (hdvd : ∀ i, d i ∣ r i) :
    d ∈ validTupleSet k W₀ R := by
  rw [mem_validTupleSet hR] at hr ⊢
  obtain ⟨hr1, hr_prod, hr_sf, hr_cop⟩ := hr
  have hprod_dvd : ∏ i, d i ∣ ∏ i, r i := Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hdvd i
  have hr_pos : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr1 i
  refine ⟨hd1, ?_, hr_sf.squarefree_of_dvd hprod_dvd, hr_cop.coprime_dvd_left hprod_dvd⟩
  exact le_trans (by exact_mod_cast Nat.le_of_dvd hr_pos hprod_dvd) hr_prod

/-- Diagonalized sieve variable `y_r = F(log r_1 / log R, ..., log r_{k+1} / log R)` on
`validTupleSet k W₀ R`, zero elsewhere. -/
def yVar {k : ℕ} (W₀ : ℕ) (R : ℝ) (T : SimplexTestFn (k + 1)) (r : Fin (k + 1) → ℕ) : ℝ :=
  if r ∈ validTupleSet k W₀ R then T.F (fun i => Real.log (r i : ℝ) / Real.log R) else 0

/-- Selberg sieve weight coefficients `λ_d` obtained by Möbius inversion from `yVar`. -/
def lamVar {k : ℕ} (W₀ : ℕ) (R : ℝ) (T : SimplexTestFn (k + 1)) (d : Fin (k + 1) → ℕ) : ℝ :=
  if d ∈ validTupleSet k W₀ R then
    (∏ i, (μ (d i) : ℝ) * (d i : ℝ)) *
      ∑ r ∈ (validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i),
        yVar W₀ R T r / (∏ i, ((r i).totient : ℝ))
  else 0

/-- Multidimensional Selberg sieve weight `w(n) = (∑_{d_i ∣ n + h_i} λ_d)² ≥ 0`. -/
def sieveWeight {k : ℕ} (h : Fin (k + 1) ↪ ℕ) (W₀ : ℕ) (R : ℝ)
    (T : SimplexTestFn (k + 1)) (n : ℕ) : ℝ :=
  (∑ d ∈ (validTupleSet k W₀ R).filter (fun d => ∀ i, d i ∣ n + h i), lamVar W₀ R T d) ^ 2

lemma sieveWeight_nonneg {k : ℕ} (h : Fin (k + 1) ↪ ℕ) (W₀ : ℕ) (R : ℝ)
    (T : SimplexTestFn (k + 1)) (n : ℕ) : 0 ≤ sieveWeight h W₀ R T n :=
  sq_nonneg _

lemma abs_yVar_le {k : ℕ} (W₀ : ℕ) {R : ℝ} (hR : Real.exp 4 ≤ R)
    (T : SimplexTestFn (k + 1)) (r : Fin (k + 1) → ℕ) :
    |yVar W₀ R T r| ≤ T.bound := by
  unfold yVar
  split_ifs with hr
  · have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
    have hlogR_pos : 0 < Real.log R := by
      have := Real.log_le_log (Real.exp_pos 4) hR; rw [Real.log_exp] at this; linarith
    obtain ⟨hr1, hr_prod, _, _⟩ := (mem_validTupleSet hR_pos.le).mp hr
    refine T.abs_le _ (fun i => div_nonneg (Real.log_nonneg (by exact_mod_cast hr1 i)) hlogR_pos.le) ?_
    rw [← Finset.sum_div, div_le_one hlogR_pos]
    have hsum_log : ∑ i : Fin (k + 1), Real.log (r i : ℝ) = Real.log ((∏ i, r i : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod fun i _ => (Nat.cast_pos.mpr (hr1 i)).ne']
    rw [hsum_log]
    exact Real.log_le_log (Nat.cast_pos.mpr (Finset.prod_pos fun i _ => hr1 i)) hr_prod
  · simp [T.bound_nonneg]

/-- **Exact Möbius Inversion Identity for `lamVar`**:
for every tuple `r : Fin (k + 1) → ℕ`,
`∑_{d ∈ validTupleSet, r ∣ d} λ_d / (∏ d_i) = (∏ μ(r_i)) * y_r / (∏ φ(r_i))`. -/
theorem sum_lamVar_div_prod_eq {k : ℕ} (W₀ : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (T : SimplexTestFn (k + 1)) (r : Fin (k + 1) → ℕ) :
    ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => ∀ i, r i ∣ d i),
        lamVar W₀ R T d / (∏ i, (d i : ℝ)) =
      (∏ i, (μ (r i) : ℝ)) * yVar W₀ R T r / (∏ i, ((r i).totient : ℝ)) := by
  have hR0 : 0 ≤ R := by linarith
  by_cases hr : r ∈ validTupleSet k W₀ R
  · -- Substitute `lamVar d`, cancel `∏ d_i`, swap sums over `d` and `t`
    have hstep1 : ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => ∀ i, r i ∣ d i),
          lamVar W₀ R T d / (∏ i, (d i : ℝ)) =
        ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => ∀ i, r i ∣ d i),
          ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i, d i ∣ t i),
            (∏ i, (μ (d i) : ℝ)) * (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ))) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdV : d ∈ validTupleSet k W₀ R := (Finset.mem_filter.mp hd).1
      have hd1 : ∀ i, 1 ≤ d i := ((mem_validTupleSet hR0).mp hdV).1
      have hdprod_ne : (∏ i : Fin (k + 1), (d i : ℝ)) ≠ 0 :=
        (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (hd1 i)).ne'
      unfold lamVar
      rw [if_pos hdV, Finset.prod_mul_distrib, mul_assoc, mul_div_assoc,
        mul_div_cancel_left₀ _ hdprod_ne, Finset.mul_sum]
    rw [hstep1]
    -- Swap sums: outer `t ∈ validTupleSet` with `r ∣ t`, inner `d` with `∀ i, r i ∣ d i ∧ d i ∣ t i`
    have hswap : ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => ∀ i, r i ∣ d i),
          ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i, d i ∣ t i),
            (∏ i, (μ (d i) : ℝ)) * (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ))) =
        ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i, r i ∣ t i),
          (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ))) *
            ∑ d ∈ (Fintype.piFinset (fun i : Fin (k + 1) => (t i / r i).divisors)),
              ∏ i, (μ (r i * d i) : ℝ) := by
      -- First rewrite both sides as sums over pairs `(d, t)` with `r ∣ d ∣ t`
      have h1 : ∀ d ∈ (validTupleSet k W₀ R).filter (fun d => ∀ i, r i ∣ d i),
          ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i, d i ∣ t i),
            (∏ i, (μ (d i) : ℝ)) * (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ))) =
          ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i, r i ∣ t i),
            if (∀ i, d i ∣ t i) then
              (∏ i, (μ (d i) : ℝ)) * (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ)))
            else 0 := by
        intro d hd
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext t; simp only [Finset.mem_filter]
        exact ⟨fun ⟨ht, hdt⟩ => ⟨⟨ht, fun i => dvd_trans ((Finset.mem_filter.mp hd).2 i) (hdt i)⟩, hdt⟩,
          fun ⟨⟨ht, _⟩, hdt⟩ => ⟨ht, hdt⟩⟩
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun t ht => ?_
      have htV : t ∈ validTupleSet k W₀ R := (Finset.mem_filter.mp ht).1
      have hrt : ∀ i, r i ∣ t i := (Finset.mem_filter.mp ht).2
      have ht1 : ∀ i, 1 ≤ t i := ((mem_validTupleSet hR0).mp htV).1
      have hr1 : ∀ i, 1 ≤ r i := ((mem_validTupleSet hR0).mp hr).1
      rw [← Finset.sum_filter, ← Finset.sum_mul, mul_comm]
      congr 1
      -- Bijection `c ↦ (fun i => r i * c i)` from `piFinset (divisors (t i / r i))` to `{d ∈ V : r ∣ d ∣ t}`
      symm
      refine Finset.sum_bij (fun c _ i => r i * c i) ?_ ?_ ?_ ?_
      · intro c hc
        simp only [Fintype.mem_piFinset, Nat.mem_divisors] at hc
        simp only [Finset.mem_filter]
        have hdvd_t : ∀ i, r i * c i ∣ t i := fun i => by
          have hmul : r i * (t i / r i) = t i := Nat.mul_div_cancel' (hrt i)
          rw [← hmul]; exact mul_dvd_mul_left (r i) (hc i).1
        have hd1 : ∀ i, 1 ≤ r i * c i := fun i =>
          Nat.pos_of_dvd_of_pos (hdvd_t i) (ht1 i)
        exact ⟨⟨validTupleSet_of_dvd hR0 htV hd1 hdvd_t, fun i => dvd_mul_right (r i) (c i)⟩, hdvd_t⟩
      · intro c₁ _ c₂ _ heq
        ext i
        have hi := congrFun heq i
        exact Nat.eq_of_mul_eq_mul_left (hr1 i) hi
      · intro d hd
        simp only [Finset.mem_filter] at hd
        obtain ⟨⟨hdV, hrd⟩, hdt⟩ := hd
        refine ⟨fun i => d i / r i, ?_, ?_⟩
        · simp only [Fintype.mem_piFinset, Nat.mem_divisors]
          intro i
          refine ⟨?_, (Nat.div_pos (Nat.le_of_dvd (ht1 i) (hrt i)) (hr1 i)).ne'⟩
          obtain ⟨q, hq⟩ := hdt i
          obtain ⟨m, hm⟩ := hrd i
          have : r i * (m * q) = r i * (t i / r i) := by
            rw [Nat.mul_div_cancel' (hrt i), hq, hm]; ring
          have hdiv : m * q = t i / r i := Nat.eq_of_mul_eq_mul_left (hr1 i) this
          have hdm : d i / r i = m := by rw [hm, Nat.mul_div_cancel_left _ (hr1 i)]
          rw [hdm]; exact ⟨q, hdiv.symm⟩
        · ext i; exact Nat.mul_div_cancel' (hrd i)
      · intro _ _; rfl
    rw [hswap]
    -- Evaluate the inner sum: it vanishes unless `t = r`!
    rw [Finset.sum_eq_single r]
    · -- `t = r`: `t i / r i = 1`, so only `c i = 1`
      have hdiv1 : ∀ i : Fin (k + 1), r i / r i = 1 :=
        fun i => Nat.div_self (((mem_validTupleSet hR0).mp hr).1 i)
      have hpi1 : Fintype.piFinset (fun i : Fin (k + 1) => (r i / r i).divisors) = {fun _ => 1} := by
        ext c
        simp only [Fintype.mem_piFinset, hdiv1, Nat.divisors_one, Finset.mem_singleton]
        exact ⟨fun hc => funext hc, fun hc i => by rw [hc]⟩
      rw [hpi1, Finset.sum_singleton]
      simp only [mul_one]; ring
    · intro t ht hne
      have htV : t ∈ validTupleSet k W₀ R := (Finset.mem_filter.mp ht).1
      have hrt : ∀ i, r i ∣ t i := (Finset.mem_filter.mp ht).2
      have ht_sf : ∀ i, Squarefree (t i) := fun i =>
        (squarefree_prod_coord ((mem_validTupleSet hR0).mp htV).2.2.1).1 i (Finset.mem_univ i)
      -- Factor `∏ i, μ(r i * c i) = (∏ i, μ(r i)) * (∏ i, μ(c i))`
      have hfac : ∀ c ∈ Fintype.piFinset (fun i : Fin (k + 1) => (t i / r i).divisors),
          ∏ i, (μ (r i * c i) : ℝ) = (∏ i, (μ (r i) : ℝ)) * ∏ i, (μ (c i) : ℝ) := by
        intro c hc
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        have hmul : r i * (t i / r i) = t i := Nat.mul_div_cancel' (hrt i)
        have hcop_rt : Nat.Coprime (r i) (t i / r i) :=
          Nat.coprime_of_squarefree_mul (hmul.symm ▸ ht_sf i)
        have hc_dvd : c i ∣ t i / r i := Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hc i)
        have hcop : Nat.Coprime (r i) (c i) := hcop_rt.coprime_dvd_right hc_dvd
        have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
        exact_mod_cast hm
      rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum,
        sum_piFinset_prod (fun i : Fin (k + 1) => (t i / r i).divisors) (fun _ x => (μ x : ℝ))]
      -- Since `t ≠ r`, some coordinate `i₀` has `t i₀ / r i₀ ≠ 1`, so its factor is `0`!
      have hex : ∃ i₀ : Fin (k + 1), t i₀ / r i₀ ≠ 1 := by
        by_contra hall; push Not at hall
        apply hne; ext i
        have := Nat.mul_div_cancel' (hrt i)
        rw [hall i, mul_one] at this; exact this.symm
      obtain ⟨i₀, hi₀⟩ := hex
      have hzero : ∑ c ∈ (t i₀ / r i₀).divisors, (μ c : ℝ) = 0 := by
        have hsf_q : Squarefree (t i₀ / r i₀) :=
          (ht_sf i₀).squarefree_of_dvd (Nat.div_dvd_of_dvd (hrt i₀))
        rw [sum_moebius_divisors_of_squarefree hsf_q, if_neg hi₀]
      have hprod0 : (∏ i : Fin (k + 1), ∑ c ∈ (t i / r i).divisors, (μ c : ℝ)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) hzero
      rw [hprod0, mul_zero, mul_zero]
    · intro hnot; exact absurd (Finset.mem_filter.mpr ⟨hr, fun _ => dvd_refl _⟩) hnot
  · -- `r ∉ validTupleSet`: both sides are `0`!
    have hempty : (validTupleSet k W₀ R).filter (fun d => ∀ i, r i ∣ d i) = ∅ := by
      ext d; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hdV hrd
      have hd1 : ∀ i, 1 ≤ d i := ((mem_validTupleSet hR0).mp hdV).1
      have hr1 : ∀ i, 1 ≤ r i := fun i => Nat.pos_of_dvd_of_pos (hrd i) (hd1 i)
      exact hr (validTupleSet_of_dvd hR0 hdV hr1 hrd)
    rw [hempty, Finset.sum_empty]
    unfold yVar; rw [if_neg hr]; ring

/-- Second diagonalized sieve variable `y^{(m)}_r` for coordinate `m : Fin (k + 1)`. -/
def yMVar {k : ℕ} (W₀ : ℕ) (R : ℝ) (T : SimplexTestFn (k + 1)) (m : Fin (k + 1))
    (r : Fin (k + 1) → ℕ) : ℝ :=
  if r ∈ validTupleSet k W₀ R ∧ r m = 1 then
    (∏ i ∈ Finset.univ.erase m, (μ (r i) : ℝ) * (g₂ (r i) : ℝ)) *
      ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i),
        lamVar W₀ R T d / (∏ i ∈ Finset.univ.erase m, ((d i).totient : ℝ))
  else 0

/-- **Exact Formula Expressing `yMVar` in Terms of `yVar`** (Maynard 2015 Lemma 5.3):
for `r ∈ validTupleSet k W₀ R` with `r m = 1`:
`yMVar m r = (∏_{i ≠ m} g₂(r i) * r i / φ(r i)²) *
  ∑_{t ∈ validTupleSet, ∀ i ≠ m, r i ∣ t i} (y_t / φ(t m)) * ∏_{i ≠ m} μ(t i / r i) / φ(t i / r i)²`. -/
theorem yMVar_eq_sum_yVar {k : ℕ} (W₀ : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (T : SimplexTestFn (k + 1)) (m : Fin (k + 1)) (r : Fin (k + 1) → ℕ)
    (hr : r ∈ validTupleSet k W₀ R) (hrm : r m = 1) :
    yMVar W₀ R T m r =
      (∏ i ∈ Finset.univ.erase m, ((g₂ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ) ^ 2)) *
        ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i ∈ Finset.univ.erase m, r i ∣ t i),
          (yVar W₀ R T t / ((t m).totient : ℝ)) *
            ∏ i ∈ Finset.univ.erase m,
              ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ) ^ 2)) := by
  have hR0 : 0 ≤ R := by linarith
  have hr1 : ∀ i, 1 ≤ r i := ((mem_validTupleSet hR0).mp hr).1
  have hr_sf : ∀ i, Squarefree (r i) := fun i =>
    (squarefree_prod_coord ((mem_validTupleSet hR0).mp hr).2.2.1).1 i (Finset.mem_univ i)
  unfold yMVar
  rw [if_pos ⟨hr, hrm⟩]
  -- Expand `lamVar d` inside the sum over `d`
  have hstep1 : ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i),
        lamVar W₀ R T d / (∏ i ∈ Finset.univ.erase m, ((d i).totient : ℝ)) =
      ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i),
        ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i, d i ∣ t i),
          (∏ i ∈ Finset.univ.erase m, (μ (d i) : ℝ) * (d i : ℝ) / ((d i).totient : ℝ)) *
            (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ))) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdV : d ∈ validTupleSet k W₀ R := (Finset.mem_filter.mp hd).1
    have hdm : d m = 1 := (Finset.mem_filter.mp hd).2.1
    unfold lamVar
    rw [if_pos hdV, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m), hdm]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one, mul_one, one_mul]
    rw [mul_div_right_comm, ← Finset.prod_div_distrib, Finset.mul_sum]
  rw [hstep1]
  -- Swap sums: outer `t ∈ V` with `∀ i ≠ m, r i ∣ t i`, inner `c` with `c i ∣ t i / r i` (`i ≠ m`)
  have hswap : ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i),
        ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i, d i ∣ t i),
          (∏ i ∈ Finset.univ.erase m, (μ (d i) : ℝ) * (d i : ℝ) / ((d i).totient : ℝ)) *
            (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ))) =
      ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i ∈ Finset.univ.erase m, r i ∣ t i),
        (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ))) *
          ∏ i ∈ Finset.univ.erase m,
            (((μ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ)) *
              ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ)))) := by
    have h1 : ∀ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i),
        ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i, d i ∣ t i),
          (∏ i ∈ Finset.univ.erase m, (μ (d i) : ℝ) * (d i : ℝ) / ((d i).totient : ℝ)) *
            (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ))) =
        ∑ t ∈ (validTupleSet k W₀ R).filter (fun t => ∀ i ∈ Finset.univ.erase m, r i ∣ t i),
          if (∀ i, d i ∣ t i) then
            (∏ i ∈ Finset.univ.erase m, (μ (d i) : ℝ) * (d i : ℝ) / ((d i).totient : ℝ)) *
              (yVar W₀ R T t / (∏ i, ((t i).totient : ℝ)))
          else 0 := by
      intro d hd
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext t; simp only [Finset.mem_filter]
      exact ⟨fun ⟨ht, hdt⟩ => ⟨⟨ht, fun i _ => dvd_trans ((Finset.mem_filter.mp hd).2.2 i) (hdt i)⟩, hdt⟩,
        fun ⟨⟨ht, _⟩, hdt⟩ => ⟨ht, hdt⟩⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htV : t ∈ validTupleSet k W₀ R := (Finset.mem_filter.mp ht).1
    have hrt : ∀ i ∈ Finset.univ.erase m, r i ∣ t i := (Finset.mem_filter.mp ht).2
    have hrt_all : ∀ i, r i ∣ t i := fun i => by
      by_cases hi : i = m
      · subst hi; rw [hrm]; exact one_dvd _
      · exact hrt i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    have ht1 : ∀ i, 1 ≤ t i := ((mem_validTupleSet hR0).mp htV).1
    have ht_sf : ∀ i, Squarefree (t i) := fun i =>
      (squarefree_prod_coord ((mem_validTupleSet hR0).mp htV).2.2.1).1 i (Finset.mem_univ i)
    rw [← Finset.sum_filter, ← Finset.sum_mul, mul_comm]
    congr 1
    -- Express the `d`-sum as `∏_{i ≠ m} ∑_{c ∣ t i / r i} μ(r i * c) * (r i * c) / φ(r i * c)`
    have hprod_sum :
        ∏ i ∈ Finset.univ.erase m,
          (((μ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ)) *
            ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ)))) =
        ∏ i ∈ Finset.univ.erase m,
          ∑ c ∈ (t i / r i).divisors,
            (μ (r i * c) : ℝ) * ((r i * c : ℕ) : ℝ) / (((r i * c).totient : ℝ)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hmul : r i * (t i / r i) = t i := Nat.mul_div_cancel' (hrt i hi)
      have hcop_rt : Nat.Coprime (r i) (t i / r i) :=
        Nat.coprime_of_squarefree_mul (hmul.symm ▸ ht_sf i)
      have hsf_q : Squarefree (t i / r i) := (ht_sf i).squarefree_of_dvd (Nat.div_dvd_of_dvd (hrt i hi))
      rw [← sum_moebius_mul_div_totient_of_squarefree hsf_q, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      have hcop : Nat.Coprime (r i) c := hcop_rt.coprime_dvd_right (Nat.dvd_of_mem_divisors hc)
      have hmu : (μ (r i * c) : ℝ) = (μ (r i) : ℝ) * (μ c : ℝ) := by
        exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      have hphi : ((r i * c).totient : ℝ) = ((r i).totient : ℝ) * (c.totient : ℝ) := by
        exact_mod_cast Nat.totient_mul hcop
      rw [hmu, hphi, Nat.cast_mul]; ring
    rw [hprod_sum, Finset.prod_sum]
    symm
    refine Finset.sum_bij (fun f _ i => if hi : i ∈ Finset.univ.erase m then r i * f i hi else 1)
      ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_pi, Nat.mem_divisors] at hf
      simp only [Finset.mem_filter]
      have hdvd_t : ∀ i, (if hi : i ∈ Finset.univ.erase m then r i * f i hi else 1) ∣ t i := fun i => by
        split_ifs with hi
        · have hmul : r i * (t i / r i) = t i := Nat.mul_div_cancel' (hrt i hi)
          rw [← hmul]; exact mul_dvd_mul_left (r i) (hf i hi).1
        · exact one_dvd _
      have hd1 : ∀ i, 1 ≤ (if hi : i ∈ Finset.univ.erase m then r i * f i hi else 1) := fun i =>
        Nat.pos_of_dvd_of_pos (hdvd_t i) (ht1 i)
      refine ⟨⟨validTupleSet_of_dvd hR0 htV hd1 hdvd_t, ?_, ?_⟩, hdvd_t⟩
      · simp
      · intro i; split_ifs with hi
        · exact dvd_mul_right _ _
        · have him : i = m := by
            by_contra hne; exact hi (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)
          rw [him, hrm]
    · intro f₁ _ f₂ _ heq
      funext i hi
      have h := congrFun heq i
      simp only [dif_pos hi] at h
      exact Nat.eq_of_mul_eq_mul_left (hr1 i) h
    · intro d hd
      simp only [Finset.mem_filter] at hd
      obtain ⟨⟨_, hdm, hrd⟩, hdt⟩ := hd
      refine ⟨fun i _ => d i / r i, ?_, ?_⟩
      · simp only [Finset.mem_pi, Nat.mem_divisors]
        intro i hi
        refine ⟨?_, (Nat.div_pos (Nat.le_of_dvd (ht1 i) (hrt i hi)) (hr1 i)).ne'⟩
        obtain ⟨q, hq⟩ := hdt i
        obtain ⟨u, hu⟩ := hrd i
        have : r i * (u * q) = r i * (t i / r i) := by
          rw [Nat.mul_div_cancel' (hrt i hi), hq, hu]; ring
        have hdiv : u * q = t i / r i := Nat.eq_of_mul_eq_mul_left (hr1 i) this
        have hdu : d i / r i = u := by rw [hu, Nat.mul_div_cancel_left _ (hr1 i)]
        rw [hdu]; exact ⟨q, hdiv.symm⟩
      · ext i
        split_ifs with hi
        · exact Nat.mul_div_cancel' (hrd i)
        · have him : i = m := by
            by_contra hne; exact hi (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)
          rw [him, hdm]
    · intro f _
      symm
      rw [← Finset.prod_attach (Finset.univ.erase m)]
      refine Finset.prod_congr rfl fun i _ => by simp only [dif_pos i.2]
  rw [hswap, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htV : t ∈ validTupleSet k W₀ R := (Finset.mem_filter.mp ht).1
  have hrt : ∀ i ∈ Finset.univ.erase m, r i ∣ t i := (Finset.mem_filter.mp ht).2
  have ht_sf : ∀ i, Squarefree (t i) := fun i =>
    (squarefree_prod_coord ((mem_validTupleSet hR0).mp htV).2.2.1).1 i (Finset.mem_univ i)
  -- Simplify `(∏_{i ≠ m} μ(r i) g₂(r i)) * (y t / ∏ φ(t i)) * ∏_{i ≠ m} (μ(r i) r i / φ(r i) * μ(q i) / φ(q i))`
  rw [← Finset.mul_prod_erase _ (fun i => ((t i).totient : ℝ)) (Finset.mem_univ m)]
  have hphi_split : ∏ i ∈ Finset.univ.erase m, ((t i).totient : ℝ) =
      (∏ i ∈ Finset.univ.erase m, ((r i).totient : ℝ)) *
        (∏ i ∈ Finset.univ.erase m, (((t i / r i).totient : ℝ))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hmul : r i * (t i / r i) = t i := Nat.mul_div_cancel' (hrt i hi)
    have hcop : Nat.Coprime (r i) (t i / r i) :=
      Nat.coprime_of_squarefree_mul (hmul.symm ▸ ht_sf i)
    conv_lhs => rw [← hmul]
    exact_mod_cast Nat.totient_mul hcop
  have hmu_sq : ∀ i ∈ Finset.univ.erase m, (μ (r i) : ℝ) * (μ (r i) : ℝ) = 1 := fun i _ => by
    rw [moebius_eq_prod_neg_one_of_squarefree (hr_sf i), ← Finset.prod_mul_distrib]
    simp
  have hprod_comb :
      (∏ i ∈ Finset.univ.erase m, (μ (r i) : ℝ) * (g₂ (r i) : ℝ)) *
        (∏ i ∈ Finset.univ.erase m, (((μ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ)) *
          ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ))))) /
        ((∏ i ∈ Finset.univ.erase m, ((r i).totient : ℝ)) *
          (∏ i ∈ Finset.univ.erase m, (((t i / r i).totient : ℝ)))) =
      (∏ i ∈ Finset.univ.erase m, ((g₂ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ) ^ 2)) *
        (∏ i ∈ Finset.univ.erase m, ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ) ^ 2))) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hms := hmu_sq i hi
    have hphi_r_ne : ((r i).totient : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Nat.totient_pos.mpr (hr1 i))).ne'
    have hq_pos : 0 < t i / r i :=
      Nat.div_pos (Nat.le_of_dvd (((mem_validTupleSet hR0).mp htV).1 i) (hrt i hi)) (hr1 i)
    have hphi_q_ne : (((t i / r i).totient : ℝ)) ≠ 0 :=
      (Nat.cast_pos.mpr (Nat.totient_pos.mpr hq_pos)).ne'
    field_simp [hphi_r_ne, hphi_q_ne]
    rw [sq, hms]; ring
  rw [hphi_split]
  calc (∏ i ∈ Finset.univ.erase m, (μ (r i) : ℝ) * (g₂ (r i) : ℝ)) *
        (yVar W₀ R T t / (((t m).totient : ℝ) *
          ((∏ i ∈ Finset.univ.erase m, ((r i).totient : ℝ)) *
            ∏ i ∈ Finset.univ.erase m, (((t i / r i).totient : ℝ)))) *
          ∏ i ∈ Finset.univ.erase m,
            ((μ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ) *
              ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ)))))
      = ((∏ i ∈ Finset.univ.erase m, (μ (r i) : ℝ) * (g₂ (r i) : ℝ)) *
          (∏ i ∈ Finset.univ.erase m,
            ((μ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ) *
              ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ))))) /
          ((∏ i ∈ Finset.univ.erase m, ((r i).totient : ℝ)) *
            ∏ i ∈ Finset.univ.erase m, (((t i / r i).totient : ℝ)))) *
          (yVar W₀ R T t / ((t m).totient : ℝ)) := by ring
    _ = ((∏ i ∈ Finset.univ.erase m, ((g₂ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ) ^ 2)) *
          (∏ i ∈ Finset.univ.erase m, ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ) ^ 2)))) *
          (yVar W₀ R T t / ((t m).totient : ℝ)) := by rw [hprod_comb]
    _ = _ := by ring

/-- **Pointwise Upper Bound on `|lamVar d|`**: for `16 ≤ R`, `W₀ ≥ 1`:
`|lamVar d| ≤ T.bound * (exp 2 * log R * (6 * log (2 * R)))^(k + 1)`. -/
lemma abs_lamVar_le {k W₀ : ℕ} {R : ℝ} (hR : Real.exp 4 ≤ R)
    (T : SimplexTestFn (k + 1)) (d : Fin (k + 1) → ℕ) :
    |lamVar W₀ R T d| ≤
      T.bound * (Real.exp 2 * Real.log R * (6 * Real.log (2 * R))) ^ (k + 1) := by
  have hR16 : 16 ≤ R := by
    have h4 : (16 : ℝ) ≤ Real.exp 4 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    exact h4.trans hR
  have hlogR_pos : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog2R_pos : 0 < Real.log (2 * R) := Real.log_pos (by linarith)
  unfold lamVar
  split_ifs with hd
  · have hR0 : 0 ≤ R := by linarith
    obtain ⟨hd1, hd_prod, hd_sf_prod, _⟩ := (mem_validTupleSet hR0).mp hd
    have hd_le : ∀ i, (d i : ℝ) ≤ R := fun i =>
      le_trans (by exact_mod_cast Finset.single_le_prod' (f := d) (fun j _ => hd1 j) (Finset.mem_univ i))
        hd_prod
    have hmu_le1 : ∀ n : ℕ, |(μ n : ℝ)| ≤ 1 := fun n => by
      by_cases hsf : Squarefree n
      · rw [moebius_eq_prod_neg_one_of_squarefree hsf, Finset.abs_prod]
        simp
      · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
    -- Reindex `r` divisible by `d` via `c i = r i / d i` so `φ(r i) = φ(d i) * φ(c i)`
    have hsum_le : |∑ r ∈ (validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i),
          yVar W₀ R T r / (∏ i, ((r i).totient : ℝ))| ≤
        (T.bound / (∏ i, ((d i).totient : ℝ))) * (6 * Real.log (2 * R)) ^ (k + 1) := by
      have htri : |∑ r ∈ (validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i),
            yVar W₀ R T r / (∏ i, ((r i).totient : ℝ))| ≤
          ∑ r ∈ (validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i),
            T.bound / (∏ i, ((r i).totient : ℝ)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [abs_div, abs_of_nonneg (a := ∏ i, ((r i).totient : ℝ))
          (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)]
        exact div_le_div_of_nonneg_right (abs_yVar_le W₀ hR T r) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
      -- Inject `r ↦ (fun i => r i / d i)` into `piFinset (Icc 1 ⌊R⌋₊)`
      let emb : (Fin (k + 1) → ℕ) → (Fin (k + 1) → ℕ) := fun r i => r i / d i
      have hinj : Set.InjOn emb (((validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i)) : Set _) := by
        intro r₁ hr₁ r₂ hr₂ heq
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr₁ hr₂
        ext i
        have h := congrFun heq i
        dsimp only [emb] at h
        rw [← Nat.mul_div_cancel' (hr₁.2 i), ← Nat.mul_div_cancel' (hr₂.2 i), h]
      have hphi_split : ∀ r ∈ (validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i),
          T.bound / (∏ i, ((r i).totient : ℝ)) =
            (T.bound / (∏ i, ((d i).totient : ℝ))) * ∏ i, (((emb r i).totient : ℝ))⁻¹ := by
        intro r hr
        have hrV := (Finset.mem_filter.mp hr).1
        have hdr := (Finset.mem_filter.mp hr).2
        have hr_sf : ∀ i, Squarefree (r i) := fun i =>
          (squarefree_prod_coord ((mem_validTupleSet hR0).mp hrV).2.2.1).1 i (Finset.mem_univ i)
        have hpeq : ∏ i, ((r i).totient : ℝ) =
            (∏ i, ((d i).totient : ℝ)) * ∏ i, (((emb r i).totient : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          have hmul : d i * (r i / d i) = r i := Nat.mul_div_cancel' (hdr i)
          have hcop : Nat.Coprime (d i) (r i / d i) :=
            Nat.coprime_of_squarefree_mul (hmul.symm ▸ hr_sf i)
          conv_lhs => rw [← hmul]
          exact_mod_cast Nat.totient_mul hcop
        rw [hpeq, Finset.prod_inv_distrib]; ring
      have hsub : ((validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i)).image emb ⊆
          Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 ⌊R⌋₊) := by
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨r, hr, rfl⟩
        have hrV := (Finset.mem_filter.mp hr).1
        have hdr := (Finset.mem_filter.mp hr).2
        obtain ⟨hr1, hr_prod, _, _⟩ := (mem_validTupleSet hR0).mp hrV
        rw [Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_Icc]
        refine ⟨Nat.div_pos (Nat.le_of_dvd (hr1 i) (hdr i)) (hd1 i), Nat.le_floor ?_⟩
        have hle : ((r i / d i : ℕ) : ℝ) ≤ (r i : ℝ) := by exact_mod_cast Nat.div_le_self (r i) (d i)
        have hri : (r i : ℝ) ≤ R :=
          le_trans (by exact_mod_cast Finset.single_le_prod' (f := r) (fun j _ => hr1 j) (Finset.mem_univ i))
            hr_prod
        exact hle.trans hri
      have h1d_phi : ∑ c ∈ Finset.Icc 1 ⌊R⌋₊, ((c.totient : ℝ))⁻¹ ≤ 6 * Real.log (2 * R) := by
        have hfl1 : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ R))
        have hbd := Stage8BarbanDavenport.sum_inv_totient_dvd_le (d := 1) le_rfl hfl1
        have hfilt : (Finset.Icc 1 ⌊R⌋₊).filter (fun q => 1 ∣ q) = Finset.Icc 1 ⌊R⌋₊ := by
          ext q; simp
        rw [hfilt] at hbd
        have hlog : Real.log (2 * (⌊R⌋₊ : ℝ)) ≤ Real.log (2 * R) :=
          Real.log_le_log (by positivity) (by linarith [Nat.floor_le hR0])
        simp only [Nat.totient_one, Nat.cast_one, div_one] at hbd
        linarith
      calc |∑ r ∈ (validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i),
              yVar W₀ R T r / (∏ i, ((r i).totient : ℝ))|
          ≤ ∑ r ∈ (validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i),
              (T.bound / (∏ i, ((d i).totient : ℝ))) * ∏ i, (((emb r i).totient : ℝ))⁻¹ :=
            htri.trans_eq (Finset.sum_congr rfl hphi_split)
        _ = (T.bound / (∏ i, ((d i).totient : ℝ))) *
              ∑ c ∈ ((validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i)).image emb,
                ∏ i, ((c i).totient : ℝ)⁻¹ := by
            rw [← Finset.mul_sum]
            congr 1
            exact (Finset.sum_image (f := fun c : Fin (k + 1) → ℕ => ∏ i, ((c i).totient : ℝ)⁻¹)
              (fun a ha b hb hab => hinj ha hb hab)).symm
        _ ≤ (T.bound / (∏ i, ((d i).totient : ℝ))) *
              ∑ c ∈ Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 ⌊R⌋₊),
                ∏ i, ((c i).totient : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
              (div_nonneg T.bound_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _))
        _ = (T.bound / (∏ i, ((d i).totient : ℝ))) *
              (∑ c ∈ Finset.Icc 1 ⌊R⌋₊, ((c.totient : ℝ))⁻¹) ^ (k + 1) := by
            rw [sum_piFinset_prod (fun _ : Fin (k + 1) => Finset.Icc 1 ⌊R⌋₊)
              (fun _ x => ((x.totient : ℝ))⁻¹), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ (T.bound / (∏ i, ((d i).totient : ℝ))) * (6 * Real.log (2 * R)) ^ (k + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (div_nonneg T.bound_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _))
            exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) h1d_phi (k + 1)
    rw [abs_mul, Finset.abs_prod]
    have hprod_mu_d : (∏ i : Fin (k + 1), |(μ (d i) : ℝ) * (d i : ℝ)|) / (∏ i, ((d i).totient : ℝ)) ≤
        (Real.exp 2 * Real.log R) ^ (k + 1) := by
      rw [← Finset.prod_div_distrib]
      calc ∏ i : Fin (k + 1), |(μ (d i) : ℝ) * (d i : ℝ)| / ((d i).totient : ℝ)
          ≤ ∏ _i : Fin (k + 1), (Real.exp 2 * Real.log R) := by
            refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
            rw [abs_mul, abs_of_nonneg (a := (d i : ℝ)) (Nat.cast_nonneg _)]
            calc |(μ (d i) : ℝ)| * (d i : ℝ) / ((d i).totient : ℝ)
                ≤ 1 * (d i : ℝ) / ((d i).totient : ℝ) := by
                  gcongr; exact hmu_le1 (d i)
              _ = (d i : ℝ) / ((d i).totient : ℝ) := by ring
              _ ≤ Real.exp 2 * Real.log R := nat_div_totient_le (hd1 i) hR16 (hd_le i)
        _ = (Real.exp 2 * Real.log R) ^ (k + 1) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc (∏ i : Fin (k + 1), |(μ (d i) : ℝ) * (d i : ℝ)|) *
          |∑ r ∈ (validTupleSet k W₀ R).filter (fun r => ∀ i, d i ∣ r i),
            yVar W₀ R T r / (∏ i, ((r i).totient : ℝ))|
        ≤ (∏ i : Fin (k + 1), |(μ (d i) : ℝ) * (d i : ℝ)|) *
            ((T.bound / (∏ i, ((d i).totient : ℝ))) * (6 * Real.log (2 * R)) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hsum_le (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = T.bound * ((∏ i : Fin (k + 1), |(μ (d i) : ℝ) * (d i : ℝ)|) / (∏ i, ((d i).totient : ℝ))) *
            (6 * Real.log (2 * R)) ^ (k + 1) := by ring
      _ ≤ T.bound * (Real.exp 2 * Real.log R) ^ (k + 1) * (6 * Real.log (2 * R)) ^ (k + 1) := by
          gcongr; exact T.bound_nonneg
      _ = T.bound * (Real.exp 2 * Real.log R * (6 * Real.log (2 * R))) ^ (k + 1) := by
          rw [mul_pow]; ring
  · rw [abs_zero]
    exact mul_nonneg T.bound_nonneg (pow_nonneg (by positivity) _)

/-- Upper bound on the number of `(k + 1)`-tuples with `∏ d_i ≤ R`:
`#(validTupleSet k W₀ R) ≤ R * (Real.log R + 1)^k`. -/
lemma card_validTupleSet_le (k W₀ : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    ((validTupleSet k W₀ R).card : ℝ) ≤ R * (Real.log R + 1) ^ k := by
  have hgen : ∀ (m : ℕ) (X : ℝ), 1 ≤ X →
      (((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 ⌊X⌋₊)).filter
          (fun d => ((∏ i, d i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤ X * (Real.log X + 1) ^ m := by
    intro m
    induction m with
    | zero =>
      intro X hX
      have hcard : ((Fintype.piFinset (fun _ : Fin 1 => Finset.Icc 1 ⌊X⌋₊)).filter
          (fun d => ((∏ i, d i : ℕ) : ℝ) ≤ X)).card ≤ ⌊X⌋₊ := by
        calc _ ≤ (Fintype.piFinset (fun _ : Fin 1 => Finset.Icc 1 ⌊X⌋₊)).card :=
              Finset.card_filter_le _ _
          _ = ⌊X⌋₊ := by simp
      calc _ ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hcard
        _ ≤ X := Nat.floor_le (by linarith)
        _ = X * (Real.log X + 1) ^ 0 := by simp
    | succ m ih =>
      intro X hX
      set S := (Fintype.piFinset (fun _ : Fin (m + 2) => Finset.Icc 1 ⌊X⌋₊)).filter
        (fun d => ((∏ i, d i : ℕ) : ℝ) ≤ X)
      let inner : ℕ → Finset (Fin (m + 1) → ℕ) := fun n =>
        (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 ⌊X / (n : ℝ)⌋₊)).filter
          (fun d' => ((∏ i, d' i : ℕ) : ℝ) ≤ X / (n : ℝ))
      have hcard_eq : (S.card : ℝ) = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((inner n).card : ℝ) := by
        have hnat : S.card = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (inner n).card := by
          rw [← Finset.card_sigma]
          refine Finset.card_bij (fun d _ => ⟨d 0, Fin.tail d⟩) ?_ ?_ ?_
          · intro d hd
            simp only [S, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hd
            have hd0 : 1 ≤ d 0 := (hd.1 0).1
            have htail : ((∏ i : Fin (m + 1), Fin.tail d i : ℕ) : ℝ) ≤ X / (d 0 : ℝ) := by
              rw [le_div_iff₀ (Nat.cast_pos.mpr hd0)]
              rw [Fin.prod_univ_succ] at hd; push_cast at hd
              simpa [Fin.tail, mul_comm] using hd.2
            simp only [Finset.mem_sigma, Finset.mem_Icc, inner, Finset.mem_filter,
              Fintype.mem_piFinset]
            refine ⟨hd.1 0, fun i => ⟨(hd.1 i.succ).1, Nat.le_floor ?_⟩, htail⟩
            have hi_le : (Fin.tail d i : ℝ) ≤ ((∏ j : Fin (m + 1), Fin.tail d j : ℕ) : ℝ) := by
              exact_mod_cast Finset.single_le_prod' (f := Fin.tail d)
                (fun j _ => (hd.1 j.succ).1) (Finset.mem_univ i)
            exact hi_le.trans htail
          · intro d₁ _ d₂ _ heq
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
            ext i; refine Fin.cases heq.1 (fun j => congrFun heq.2 j) i
          · intro x hx
            simp only [Finset.mem_sigma, Finset.mem_Icc, inner, Finset.mem_filter,
              Fintype.mem_piFinset] at hx
            have hx1 : (0 : ℝ) < (x.1 : ℝ) := Nat.cast_pos.mpr hx.1.1
            have hprod : ((∏ i : Fin (m + 2), (Fin.cons x.1 x.2 : Fin (m + 2) → ℕ) i : ℕ) : ℝ) ≤ X := by
              rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
              rw [le_div_iff₀ hx1] at hx
              rw [Nat.cast_mul]; linarith [hx.2.2]
            refine ⟨Fin.cons x.1 x.2, ?_, rfl⟩
            simp only [S, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
            refine ⟨fun i => Fin.cases hx.1 (fun j => ⟨(hx.2.1 j).1, Nat.le_floor ?_⟩) i, hprod⟩
            have h1 : (x.2 j : ℝ) ≤ X / (x.1 : ℝ) :=
              (Nat.cast_le.mpr (hx.2.1 j).2).trans (Nat.floor_le (by positivity))
            exact h1.trans (div_le_self (by linarith) (by exact_mod_cast hx.1.1))
        exact_mod_cast hnat
      rw [hcard_eq]
      have hharm := abs_harmonic_sub_log_le_one hX
      have hlog_nn : 0 ≤ Real.log X := Real.log_nonneg hX
      calc ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((inner n).card : ℝ)
          ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (X / (n : ℝ)) * (Real.log X + 1) ^ m := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
            have hn_le : (n : ℝ) ≤ X :=
              (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (by linarith))
            have hXn : 1 ≤ X / (n : ℝ) := (one_le_div (Nat.cast_pos.mpr hn1)).mpr hn_le
            have h1 := ih (X / (n : ℝ)) hXn
            have hlog_le : Real.log (X / (n : ℝ)) ≤ Real.log X :=
              Real.log_le_log (by linarith) (div_le_self (by linarith) (by exact_mod_cast hn1))
            have hpow : (Real.log (X / (n : ℝ)) + 1) ^ m ≤ (Real.log X + 1) ^ m :=
              pow_le_pow_left₀ (by linarith [Real.log_nonneg hXn]) (by linarith) m
            exact h1.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
        _ = X * (Real.log X + 1) ^ m * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((n : ℝ))⁻¹ := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
        _ ≤ X * (Real.log X + 1) ^ m * (Real.log X + 1) := by
            refine mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hharm).2]) (by positivity)
        _ = X * (Real.log X + 1) ^ (m + 1) := by rw [pow_succ]; ring
  have hsub : validTupleSet k W₀ R ⊆
      (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 ⌊R⌋₊)).filter
        (fun d => ((∏ i, d i : ℕ) : ℝ) ≤ R) := by
    intro d hd; simp only [validTupleSet, Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.1⟩
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hgen k R hR)

/-- **CRT for a finite family of pairwise coprime moduli**:
there exists `x₀ : ℕ` such that for all `n : ℕ`,
`(∀ i ∈ s, n ≡ c i [MOD M i]) ↔ n ≡ x₀ [MOD ∏ i ∈ s, M i]`. -/
lemma exists_crt_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (M c : ι → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (M i) (M j)) :
    ∃ x₀ : ℕ, ∀ n : ℕ, (∀ i ∈ s, n ≡ c i [MOD M i]) ↔ n ≡ x₀ [MOD ∏ i ∈ s, M i] := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp [Nat.modEq_one]⟩
  | insert a s ha ih =>
    obtain ⟨x₁, hx₁⟩ := ih (fun i hi j hj hij =>
      hcop i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
    have hacop : Nat.Coprime (M a) (∏ i ∈ s, M i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (mem_insert_self a s) i (mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    obtain ⟨x₀, hx₀a, hx₀s⟩ := Nat.chineseRemainder hacop (c a) x₁
    refine ⟨x₀, fun n => ?_⟩
    rw [Finset.prod_insert ha, ← Nat.modEq_and_modEq_iff_modEq_mul hacop]
    constructor
    · intro h
      refine ⟨(h a (mem_insert_self a s)).trans hx₀a.symm, ?_⟩
      exact ((hx₁ n).mp fun i hi => h i (mem_insert_of_mem hi)).trans hx₀s.symm
    · rintro ⟨hna, hns⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hna.trans hx₀a
      · exact ((hx₁ n).mpr (hns.trans hx₀s)) i hi

/-- Counting integers in `[A, B)` in a single residue class modulo `M ≥ 1`:
`|#{n ∈ [A, B) : n ≡ c [MOD M]} - (B - A) / M| ≤ 1`. -/
lemma card_Ico_modEq_sub_div_le {M : ℕ} (hM : 1 ≤ M) (A B c : ℕ) (hAB : A ≤ B) :
    |((((Finset.Ico A B).filter (fun n => n ≡ c [MOD M])).card : ℝ) -
      ((B - A : ℕ) : ℝ) / (M : ℝ))| ≤ 1 := by
  -- First prove for `[0, N)`: `N / M ≤ #{n < N : n ≡ r0 [MOD M]} ≤ N / M + 1`
  have hcount_range : ∀ N r0 : ℕ,
      N / M ≤ ((Finset.range N).filter (fun n => n ≡ r0 [MOD M])).card ∧
      ((Finset.range N).filter (fun n => n ≡ r0 [MOD M])).card ≤ N / M + 1 := by
    intro N r0
    set r := r0 % M
    have hrM : r < M := Nat.mod_lt r0 hM
    -- `{n < N : n ≡ r0 [MOD M]} = {M * q + r : q < Q}` where `Q = N / M + if r < N % M then 1 else 0`
    set Q := N / M + if r < N % M then 1 else 0
    have hbij : (Finset.range N).filter (fun n => n ≡ r0 [MOD M]) =
        (Finset.range Q).image (fun q => M * q + r) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hnN, hmod⟩
        have hnr : n % M = r := hmod
        refine ⟨n / M, ?_, by rw [← hnr, Nat.div_add_mod]⟩
        have hdiv : M * (n / M) + r < M * (N / M) + N % M := by
          rw [← hnr, Nat.div_add_mod, Nat.div_add_mod]; exact hnN
        dsimp only [Q]
        split_ifs with hlt
        · have : n / M ≤ N / M := Nat.div_le_div_right hnN.le
          omega
        · by_contra hge; push Not at hge
          have : M * (N / M) ≤ M * (n / M) := Nat.mul_le_mul_left M hge
          omega
      · rintro ⟨q, hqQ, rfl⟩
        refine ⟨?_, ?_⟩
        · have hNeq : N = M * (N / M) + N % M := (Nat.div_add_mod N M).symm
          dsimp only [Q] at hqQ
          split_ifs at hqQ with hlt
          · have hqle : q ≤ N / M := by omega
            rcases hqle.eq_or_lt with rfl | hqlt
            · omega
            · have : M * (q + 1) ≤ M * (N / M) := Nat.mul_le_mul_left M hqlt
              have : M * q + M = M * (q + 1) := by ring
              omega
          · have : M * (q + 1) ≤ M * (N / M) := Nat.mul_le_mul_left M hqQ
            have : M * q + M = M * (q + 1) := by ring
            omega
        · rw [Nat.ModEq, Nat.mul_add_mod, Nat.mod_mod]
    rw [hbij, Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left hM (by omega)),
      Finset.card_range]
    dsimp only [Q]; split_ifs <;> omega
  -- Shift `[A, B)` to `[0, B - A)` with shifted residue `c' = (c % M + M - A % M) % M`!
  set c' := (c % M + M - A % M) % M
  have hAc' : A + c' ≡ c [MOD M] := by
    have hAM : A % M < M := Nat.mod_lt A hM
    rw [Nat.ModEq, Nat.add_mod, show c' % M = (c % M + M - A % M) % M by simp [c'],
      Nat.add_mod_mod]
    have heq : A % M + (c % M + M - A % M) = c % M + M := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_mod]
  have hshift : ((Finset.Ico A B).filter (fun n => n ≡ c [MOD M])).card =
      ((Finset.range (B - A)).filter (fun t => t ≡ c' [MOD M])).card := by
    refine Finset.card_bij (fun n _ => n - A) ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hn ⊢
      refine ⟨by omega, ?_⟩
      have h1 : A + (n - A) ≡ A + c' [MOD M] := by
        rw [Nat.add_sub_cancel' hn.1.1]; exact hn.2.trans hAc'.symm
      exact Nat.ModEq.add_left_cancel' A h1
    · intro n₁ hn₁ n₂ hn₂ heq
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
      omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      refine ⟨A + t, ?_, Nat.add_sub_cancel_left A t⟩
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨Nat.le_add_right A t, by omega⟩, ?_⟩
      exact (Nat.ModEq.add_left A ht.2).trans hAc'
  rw [hshift]
  have hBA := hcount_range (B - A) c'
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hdiv1 : (((B - A) / M : ℕ) : ℝ) ≤ ((B - A : ℕ) : ℝ) / (M : ℝ) := by
    rw [le_div_iff₀ hMpos]; exact_mod_cast Nat.div_mul_le_self (B - A) M
  have hdiv2 : ((B - A : ℕ) : ℝ) / (M : ℝ) < (((B - A) / M : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hMpos]
    have h1 : B - A < ((B - A) / M + 1) * M := by
      have := Nat.lt_div_mul_add (a := B - A) hM
      have hmul : ((B - A) / M + 1) * M = (B - A) / M * M + M := by ring
      omega
    have h1R : ((B - A : ℕ) : ℝ) < ((((B - A) / M + 1 : ℕ)) : ℝ) * (M : ℝ) := by exact_mod_cast h1
    push_cast at h1R; linarith
  have hBA1 : (((B - A) / M : ℕ) : ℝ) ≤
      (((Finset.range (B - A)).filter (fun t => t ≡ c' [MOD M])).card : ℝ) := by exact_mod_cast hBA.1
  have hBA2 : (((Finset.range (B - A)).filter (fun t => t ≡ c' [MOD M])).card : ℝ) ≤
      (((B - A) / M : ℕ) : ℝ) + 1 := by exact_mod_cast hBA.2
  rw [abs_le]; constructor <;> linarith

/-! ## Section 4: Diagonalization and Asymptotic Bounds for `S₂` and `S₁` -/

/-- If a finite family is pairwise coprime, its `Finset.lcm` equals its product. -/
lemma finset_lcm_eq_prod_of_pairwise_coprime {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
    s.lcm f = ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.lcm_insert, Finset.prod_insert ha,
      ih (fun i hi j hj hij => hcop i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)]
    have hacop : Nat.Coprime (f a) (∏ i ∈ s, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (mem_insert_self a s) i (mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    have h := Nat.gcd_mul_lcm (f a) (∏ i ∈ s, f i)
    rw [hacop.gcd_eq_one, one_mul] at h
    exact h

/-- Multiplicativity of `φ` over a finite pairwise coprime product. -/
lemma totient_prod_of_pairwise_coprime {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
    (∏ i ∈ s, f i).totient = ∏ i ∈ s, (f i).totient := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hacop : Nat.Coprime (f a) (∏ i ∈ s, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (mem_insert_self a s) i (mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    rw [Nat.totient_mul hacop,
      ih (fun i hi j hj hij => hcop i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)]

/-- Multiplicativity of `g₂` over a finite pairwise coprime product of positive integers. -/
lemma g₂_prod_of_pairwise_coprime {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) (hpos : ∀ i ∈ s, f i ≠ 0)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
    g₂ (∏ i ∈ s, f i) = ∏ i ∈ s, g₂ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [g₂_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hacop : Nat.Coprime (f a) (∏ i ∈ s, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (mem_insert_self a s) i (mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    have hsne : ∏ i ∈ s, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hpos i (mem_insert_of_mem hi)
    rw [g₂_mul_of_coprime (hpos a (mem_insert_self a s)) hsne hacop,
      ih (fun i hi => hpos i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hcop i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)]

/-- Cross-coprimality condition between two `(k + 1)`-tuples: `∀ i ≠ j, Coprime (d i) (e j)`. -/
def PairwiseCoprimeCross {k : ℕ} (d e : Fin (k + 1) → ℕ) : Prop :=
  ∀ i j : Fin (k + 1), i ≠ j → Nat.Coprime (d i) (e j)

instance {k : ℕ} (d e : Fin (k + 1) → ℕ) : Decidable (PairwiseCoprimeCross d e) := by
  unfold PairwiseCoprimeCross; infer_instance

/-- Main quadratic form for the plain sum `S₂`:
`Q₂ = ∑'_{d, e} λ_d λ_e / ∏ lcm(d_i, e_i)`. -/
def Q2Sum {k : ℕ} (W₀ : ℕ) (R : ℝ) (T : SimplexTestFn (k + 1)) : ℝ :=
  ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
    if PairwiseCoprimeCross d e then
      lamVar W₀ R T d * lamVar W₀ R T e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))
    else 0

/-- **Diagonalization Upper Bound for `Q₂`** (Maynard 2015 Lemma 5.1):
for `D₀ ≥ 6`, `W₀ = W D₀`, `R ≥ exp 4`:
`Q2Sum W₀ R T ≤ (∑_{u ∈ V} y_u² / ∏ φ(u_i)) +
  T.bound² * (∑_{n ≤ R} aPhi W₀ n)^(k + 1) * ((1 + 2 / (D₀ - 2))^((k + 1) * k) - 1)`. -/
theorem Q2Sum_le {k D₀ : ℕ} (hD : 6 ≤ D₀) {R : ℝ} (hR : Real.exp 4 ≤ R)
    (T : SimplexTestFn (k + 1)) :
    Q2Sum (W D₀) R T ≤
      (∑ u ∈ validTupleSet k (W D₀) R, (yVar (W D₀) R T u) ^ 2 / (∏ i, ((u i).totient : ℝ))) +
      T.bound ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi (W D₀) n) ^ (k + 1) *
        ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1) := by
  set W₀ := W D₀
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
  have hR1 : 1 ≤ R := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hR
  set S_sf := (Finset.Icc 1 ⌊R⌋₊).filter (fun n => Squarefree n ∧ Nat.Coprime n W₀)
  set offD : Finset (Fin (k + 1) × Fin (k + 1)) := (Finset.univ : Finset (Fin (k + 1))).offDiag
  have hoffD_card : offD.card = (k + 1) * k := by
    simp only [offD, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    have : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    omega
  -- Step 1: Rewrite `Q2Sum` by expanding `1 / lcm(d i, e i)` via `φ(u i)` and `PairwiseCoprimeCross` via `μ(s p)`
  let Uset := Fintype.piFinset (fun _ : Fin (k + 1) => S_sf)
  let Sset := Fintype.piFinset (fun _ : offD => S_sf)
  let mkA : (Fin (k + 1) → ℕ) → (offD → ℕ) → (Fin (k + 1) → ℕ) := fun u s i =>
    Nat.lcm (u i) (Finset.lcm (Finset.univ.erase i)
      (fun j => if h : (i, j) ∈ offD then s ⟨(i, j), h⟩ else 1))
  let mkB : (Fin (k + 1) → ℕ) → (offD → ℕ) → (Fin (k + 1) → ℕ) := fun u s i =>
    Nat.lcm (u i) (Finset.lcm (Finset.univ.erase i)
      (fun j => if h : (j, i) ∈ offD then s ⟨(j, i), h⟩ else 1))
  have hdiag : Q2Sum W₀ R T =
      ∑ u ∈ Uset, ∑ s ∈ Sset,
        (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
          ((∏ i, (μ (mkA u s i) : ℝ)) * yVar W₀ R T (mkA u s) / (∏ i, ((mkA u s i).totient : ℝ))) *
          ((∏ i, (μ (mkB u s i) : ℝ)) * yVar W₀ R T (mkB u s) / (∏ i, ((mkB u s i).totient : ℝ))) := by
    -- Express each `(d, e)` term as a sum over `(u, s) ∈ Uset × Sset` with divisibility indicators
    have hterm_de : ∀ d ∈ validTupleSet k W₀ R, ∀ e ∈ validTupleSet k W₀ R,
        (if PairwiseCoprimeCross d e then
          lamVar W₀ R T d * lamVar W₀ R T e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))
        else 0) =
        ∑ u ∈ Uset, ∑ s ∈ Sset,
          if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
            (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
              (lamVar W₀ R T d / (∏ i, (d i : ℝ))) * (lamVar W₀ R T e / (∏ i, (e i : ℝ)))
          else 0 := by
      intro d hd e he
      obtain ⟨hd1, hd_prod, hd_sf, hd_cop⟩ := (mem_validTupleSet hR_pos.le).mp hd
      obtain ⟨he1, he_prod, he_sf, he_cop⟩ := (mem_validTupleSet hR_pos.le).mp he
      have hd_sf_i : ∀ i, Squarefree (d i) := fun i => (squarefree_prod_coord hd_sf).1 i (Finset.mem_univ i)
      have hd_cop_i : ∀ i, Nat.Coprime (d i) W₀ := fun i =>
        hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
      have hd_le_R : ∀ i, d i ≤ ⌊R⌋₊ := fun i => (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 i |> Finset.mem_Icc.mp).2
      -- (1) Indicator for `PairwiseCoprimeCross d e`
      have hcross : (if PairwiseCoprimeCross d e then (1 : ℝ) else 0) =
          ∑ s ∈ Sset, (if ∀ p : offD, s p ∣ d p.1.1 ∧ s p ∣ e p.1.2 then ∏ p : offD, (μ (s p) : ℝ) else 0) := by
        have h1 : (if PairwiseCoprimeCross d e then (1 : ℝ) else 0) =
            ∏ p : offD, ∑ x ∈ (Nat.gcd (d p.1.1) (e p.1.2)).divisors, (μ x : ℝ) := by
          have hfac : ∀ p : offD,
              ∑ x ∈ (Nat.gcd (d p.1.1) (e p.1.2)).divisors, (μ x : ℝ) =
                if Nat.Coprime (d p.1.1) (e p.1.2) then 1 else 0 := fun p => by
            have hgsf : Squarefree (Nat.gcd (d p.1.1) (e p.1.2)) :=
              (hd_sf_i p.1.1).squarefree_of_dvd (Nat.gcd_dvd_left _ _)
            exact sum_moebius_divisors_of_squarefree hgsf
          rw [Finset.prod_congr rfl fun p _ => hfac p]
          by_cases hpc : PairwiseCoprimeCross d e
          · rw [if_pos hpc]
            exact (Finset.prod_eq_one fun p _ => by
              rw [if_pos (hpc p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2)]).symm
          · rw [if_neg hpc]
            unfold PairwiseCoprimeCross at hpc; push Not at hpc
            obtain ⟨i, j, hij, hnc⟩ := hpc
            have hp : (i, j) ∈ offD := Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩
            exact (Finset.prod_eq_zero (Finset.mem_univ (⟨(i, j), hp⟩ : offD)) (by rw [if_neg hnc])).symm
        rw [h1, ← sum_piFinset_prod]
        -- Both sides are sums of `∏ p, μ(s p)` over the same set of `s`!
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext s
        simp only [Sset, Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors, S_sf, Finset.mem_Icc]
        constructor
        · intro hs
          refine ⟨fun p => ?_, fun p => Nat.dvd_gcd_iff.mp (hs p).1⟩
          have hdvd_d : s p ∣ d p.1.1 := dvd_trans (hs p).1 (Nat.gcd_dvd_left _ _)
          exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd_d (hd1 p.1.1),
            (Nat.le_of_dvd (hd1 p.1.1) hdvd_d).trans (hd_le_R p.1.1)⟩,
            (hd_sf_i p.1.1).squarefree_of_dvd hdvd_d,
            (hd_cop_i p.1.1).coprime_dvd_left hdvd_d⟩
        · rintro ⟨_, hdvd⟩ p
          exact ⟨Nat.dvd_gcd (hdvd p).1 (hdvd p).2, (Nat.gcd_pos_of_pos_left _ (hd1 p.1.1)).ne'⟩
      -- (2) Expansion of `∏ i, gcd(d i, e i)` via `∑_{u ∣ gcd} φ(u)`
      have hgcd_prod : ∏ i, (Nat.gcd (d i) (e i) : ℝ) =
          ∑ u ∈ Uset, if ∀ i, u i ∣ d i ∧ u i ∣ e i then ∏ i, ((u i).totient : ℝ) else 0 := by
        have h1 : ∏ i, (Nat.gcd (d i) (e i) : ℝ) =
            ∏ i, ∑ x ∈ (Nat.gcd (d i) (e i)).divisors, ((x.totient : ℝ)) :=
          Finset.prod_congr rfl fun i _ => (sum_totient_divisors_eq_self _).symm
        rw [h1, ← sum_piFinset_prod, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext u
        simp only [Uset, Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors, S_sf, Finset.mem_Icc]
        constructor
        · intro hu
          refine ⟨fun i => ?_, fun i => Nat.dvd_gcd_iff.mp (hu i).1⟩
          have hdvd_d : u i ∣ d i := dvd_trans (hu i).1 (Nat.gcd_dvd_left _ _)
          exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd_d (hd1 i),
            (Nat.le_of_dvd (hd1 i) hdvd_d).trans (hd_le_R i)⟩,
            (hd_sf_i i).squarefree_of_dvd hdvd_d,
            (hd_cop_i i).coprime_dvd_left hdvd_d⟩
        · rintro ⟨_, hdvd⟩ i
          exact ⟨Nat.dvd_gcd (hdvd i).1 (hdvd i).2, (Nat.gcd_pos_of_pos_left _ (hd1 i)).ne'⟩
      -- (3) `1 / ∏ lcm(d i, e i) = (∏ gcd(d i, e i)) / ((∏ d i) * (∏ e i))`
      have hlcm_eq : (1 : ℝ) / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) =
          (∏ i, (Nat.gcd (d i) (e i) : ℝ)) / ((∏ i, (d i : ℝ)) * (∏ i, (e i : ℝ))) := by
        have hlcm_ne : (∏ i : Fin (k + 1), (Nat.lcm (d i) (e i) : ℝ)) ≠ 0 :=
          (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.lcm_pos (hd1 i) (he1 i))).ne'
        have hde_ne : (∏ i : Fin (k + 1), (d i : ℝ)) * (∏ i : Fin (k + 1), (e i : ℝ)) ≠ 0 :=
          mul_ne_zero (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (hd1 i)).ne'
            (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (he1 i)).ne'
        rw [div_eq_div_iff hlcm_ne hde_ne, one_mul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        have h := Nat.gcd_mul_lcm (d i) (e i)
        have hR : (Nat.gcd (d i) (e i) : ℝ) * (Nat.lcm (d i) (e i) : ℝ) = (d i : ℝ) * (e i : ℝ) := by
          exact_mod_cast h
        linarith
      -- (4) Equivalence of divisibility conditions with `mkA` and `mkB`
      have hdvd_iff : ∀ u ∈ Uset, ∀ s ∈ Sset,
          ((∀ i, u i ∣ d i ∧ u i ∣ e i) ∧ (∀ p : offD, s p ∣ d p.1.1 ∧ s p ∣ e p.1.2)) ↔
          ((∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i)) := by
        intro u _ s _
        constructor
        · rintro ⟨hu, hs⟩
          refine ⟨fun i => Nat.lcm_dvd (hu i).1 (Finset.lcm_dvd fun j hj => ?_),
            fun i => Nat.lcm_dvd (hu i).2 (Finset.lcm_dvd fun j hj => ?_)⟩
          · have hij : (i, j) ∈ offD :=
              Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, (Finset.mem_erase.mp hj).1.symm⟩
            rw [dif_pos hij]; exact (hs ⟨(i, j), hij⟩).1
          · have hji : (j, i) ∈ offD :=
              Finset.mem_offDiag.mpr ⟨Finset.mem_univ j, Finset.mem_univ i, (Finset.mem_erase.mp hj).1⟩
            rw [dif_pos hji]; exact (hs ⟨(j, i), hji⟩).2
        · rintro ⟨hA, hB⟩
          refine ⟨fun i => ⟨dvd_trans (Nat.dvd_lcm_left _ _) (hA i),
            dvd_trans (Nat.dvd_lcm_left _ _) (hB i)⟩, fun p => ?_⟩
          have hne : p.1.1 ≠ p.1.2 := (Finset.mem_offDiag.mp p.2).2.2
          have hj1 : p.1.2 ∈ Finset.univ.erase p.1.1 := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
          have hj2 : p.1.1 ∈ Finset.univ.erase p.1.2 := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
          have h1 : s p ∣ Finset.lcm (Finset.univ.erase p.1.1)
              (fun j => if h : (p.1.1, j) ∈ offD then s ⟨(p.1.1, j), h⟩ else 1) := by
            have := Finset.dvd_lcm (f := fun j => if h : (p.1.1, j) ∈ offD then s ⟨(p.1.1, j), h⟩ else 1) hj1
            simpa only [dif_pos p.2] using this
          have h2 : s p ∣ Finset.lcm (Finset.univ.erase p.1.2)
              (fun j => if h : (j, p.1.2) ∈ offD then s ⟨(j, p.1.2), h⟩ else 1) := by
            have := Finset.dvd_lcm (f := fun j => if h : (j, p.1.2) ∈ offD then s ⟨(j, p.1.2), h⟩ else 1) hj2
            simpa only [dif_pos p.2] using this
          exact ⟨dvd_trans (dvd_trans h1 (Nat.dvd_lcm_right _ _)) (hA p.1.1),
            dvd_trans (dvd_trans h2 (Nat.dvd_lcm_right _ _)) (hB p.1.2)⟩
      -- Combine (1), (2), (3), (4)
      have hcomb : (if PairwiseCoprimeCross d e then
            lamVar W₀ R T d * lamVar W₀ R T e / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) else 0) =
          (if PairwiseCoprimeCross d e then (1 : ℝ) else 0) * (∏ i, (Nat.gcd (d i) (e i) : ℝ)) *
            (lamVar W₀ R T d / (∏ i, (d i : ℝ))) * (lamVar W₀ R T e / (∏ i, (e i : ℝ))) := by
        split_ifs
        · calc lamVar W₀ R T d * lamVar W₀ R T e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))
              = lamVar W₀ R T d * lamVar W₀ R T e * ((1 : ℝ) / (∏ i, (Nat.lcm (d i) (e i) : ℝ))) := by ring
            _ = lamVar W₀ R T d * lamVar W₀ R T e *
                  ((∏ i, (Nat.gcd (d i) (e i) : ℝ)) / ((∏ i, (d i : ℝ)) * (∏ i, (e i : ℝ)))) := by rw [hlcm_eq]
            _ = _ := by ring
        · ring
      rw [hcomb, hcross, hgcd_prod]
      rw [Finset.sum_mul_sum]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u hu => ?_
      refine Finset.sum_congr rfl fun s hs => ?_
      by_cases h1 : ∀ p : offD, s p ∣ d p.1.1 ∧ s p ∣ e p.1.2
      · by_cases h2 : ∀ i, u i ∣ d i ∧ u i ∣ e i
        · rw [if_pos h1, if_pos h2, if_pos ((hdvd_iff u hu s hs).mp ⟨h2, h1⟩)]; ring
        · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 ((hdvd_iff u hu s hs).mpr h).1)]; ring
      · rw [if_neg h1, if_neg (fun h => h1 ((hdvd_iff u hu s hs).mpr h).2)]; ring
    -- Sum `hterm_de` over `d, e ∈ validTupleSet`, swap sums to `(u, s)` outer, apply `sum_lamVar_div_prod_eq`!
    unfold Q2Sum
    have h1 : ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
          (if PairwiseCoprimeCross d e then
            lamVar W₀ R T d * lamVar W₀ R T e / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) else 0) =
        ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
          ∑ u ∈ Uset, ∑ s ∈ Sset,
            if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
              (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
                (lamVar W₀ R T d / (∏ i, (d i : ℝ))) * (lamVar W₀ R T e / (∏ i, (e i : ℝ)))
            else 0 :=
      Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => hterm_de d hd e he
    rw [h1]
    -- Swap sums: `∑_d ∑_e ∑_u ∑_s = ∑_u ∑_s ∑_d ∑_e`
    calc ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R, ∑ u ∈ Uset, ∑ s ∈ Sset,
            (if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
              (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
                (lamVar W₀ R T d / (∏ i, (d i : ℝ))) * (lamVar W₀ R T e / (∏ i, (e i : ℝ)))
            else 0)
        = ∑ d ∈ validTupleSet k W₀ R, ∑ u ∈ Uset, ∑ s ∈ Sset, ∑ e ∈ validTupleSet k W₀ R,
            (if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
              (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
                (lamVar W₀ R T d / (∏ i, (d i : ℝ))) * (lamVar W₀ R T e / (∏ i, (e i : ℝ)))
            else 0) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ u ∈ Uset, ∑ s ∈ Sset, ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
            (if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
              (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
                (lamVar W₀ R T d / (∏ i, (d i : ℝ))) * (lamVar W₀ R T e / (∏ i, (e i : ℝ)))
            else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ u ∈ Uset, ∑ s ∈ Sset,
            (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
              ((∏ i, (μ (mkA u s i) : ℝ)) * yVar W₀ R T (mkA u s) / (∏ i, ((mkA u s i).totient : ℝ))) *
              ((∏ i, (μ (mkB u s i) : ℝ)) * yVar W₀ R T (mkB u s) / (∏ i, ((mkB u s i).totient : ℝ))) := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun s _ => ?_
          have hfact : ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
                (if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
                  (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
                    (lamVar W₀ R T d / (∏ i, (d i : ℝ))) * (lamVar W₀ R T e / (∏ i, (e i : ℝ)))
                else 0) =
              (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
                (∑ d ∈ (validTupleSet k W₀ R).filter (fun d => ∀ i, mkA u s i ∣ d i),
                  lamVar W₀ R T d / (∏ i, (d i : ℝ))) *
                (∑ e ∈ (validTupleSet k W₀ R).filter (fun e => ∀ i, mkB u s i ∣ e i),
                  lamVar W₀ R T e / (∏ i, (e i : ℝ))) := by
            rw [Finset.sum_filter, Finset.sum_filter, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => ?_
            by_cases hd : ∀ i, mkA u s i ∣ d i
            · by_cases he : ∀ i, mkB u s i ∣ e i
              · rw [if_pos ⟨hd, he⟩, if_pos hd, if_pos he]; ring
              · rw [if_neg (fun h => he h.2), if_pos hd, if_neg he]; ring
            · rw [if_neg (fun h => hd h.1), if_neg hd]; ring
          rw [hfact, sum_lamVar_div_prod_eq W₀ hR1 T (mkA u s),
            sum_lamVar_div_prod_eq W₀ hR1 T (mkB u s)]
  rw [hdiag]
  -- Step 2: Split `Sset` into `s1 := fun _ => 1` vs `Sset.erase s1`
  let s1 : offD → ℕ := fun _ => 1
  have hs1_mem : s1 ∈ Sset := by
    rw [Fintype.mem_piFinset]; intro _
    simp only [S_sf, Finset.mem_filter, Finset.mem_Icc, s1]
    exact ⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast hR1)⟩, squarefree_one, Nat.coprime_one_left _⟩
  rw [Finset.sum_comm, ← Finset.add_sum_erase Sset _ hs1_mem]
  -- Evaluate the `s = s1` main term
  have hmain : ∑ u ∈ Uset,
        (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s1 p) : ℝ)) *
          ((∏ i, (μ (mkA u s1 i) : ℝ)) * yVar W₀ R T (mkA u s1) / (∏ i, ((mkA u s1 i).totient : ℝ))) *
          ((∏ i, (μ (mkB u s1 i) : ℝ)) * yVar W₀ R T (mkB u s1) / (∏ i, ((mkB u s1 i).totient : ℝ))) =
      ∑ u ∈ validTupleSet k W₀ R, (yVar W₀ R T u) ^ 2 / (∏ i, ((u i).totient : ℝ)) := by
    have hAB1 : ∀ u, mkA u s1 = u ∧ mkB u s1 = u := fun u => by
      have hlcm1 : ∀ (t : Finset (Fin (k + 1))) (g : Fin (k + 1) → ℕ),
          (∀ j ∈ t, g j = 1) → t.lcm g = 1 := fun t g hg =>
        Nat.dvd_one.mp (Finset.lcm_dvd fun j hj => by rw [hg j hj])
      constructor <;> (ext i; dsimp only [mkA, mkB, s1]; rw [hlcm1 _ _ (fun j _ => by split_ifs <;> rfl)]; simp)
    have hVsub : validTupleSet k W₀ R ⊆ Uset := by
      intro u hu
      obtain ⟨hu1, _, hu_sf, hu_cop⟩ := (mem_validTupleSet hR_pos.le).mp hu
      rw [Fintype.mem_piFinset]; intro i
      simp only [S_sf, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hu1 i, (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hu).1 i |> Finset.mem_Icc.mp).2⟩,
        (squarefree_prod_coord hu_sf).1 i (Finset.mem_univ i),
        hu_cop.coprime_dvd_left (Finset.dvd_prod_of_mem u (Finset.mem_univ i))⟩
    rw [← Finset.sum_subset hVsub]
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [(hAB1 u).1, (hAB1 u).2]
      obtain ⟨hu1, _, hu_sf, _⟩ := (mem_validTupleSet hR_pos.le).mp hu
      have hphi_ne : (∏ i : Fin (k + 1), ((u i).totient : ℝ)) ≠ 0 :=
        (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.totient_pos.mpr (hu1 i))).ne'
      have hmu_sq : (∏ i : Fin (k + 1), (μ (u i) : ℝ)) * (∏ i : Fin (k + 1), (μ (u i) : ℝ)) = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [moebius_eq_prod_neg_one_of_squarefree ((squarefree_prod_coord hu_sf).1 i (Finset.mem_univ i)),
          ← Finset.prod_mul_distrib]
        simp
      have hs1_mu : (∏ p : offD, (μ (s1 p) : ℝ)) = 1 := by simp [s1]
      rw [hs1_mu, mul_one]
      field_simp [hphi_ne]
      rw [sq, hmu_sq, one_mul]
    · intro u _ huV
      rw [(hAB1 u).1]
      unfold yVar; rw [if_neg huV]; ring
  rw [hmain]
  gcongr
  -- Step 3: Bound the `s ∈ Sset.erase s1` error term
  have hterm_s : ∀ s ∈ Sset.erase s1, ∀ u ∈ Uset,
      |(∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
          ((∏ i, (μ (mkA u s i) : ℝ)) * yVar W₀ R T (mkA u s) / (∏ i, ((mkA u s i).totient : ℝ))) *
          ((∏ i, (μ (mkB u s i) : ℝ)) * yVar W₀ R T (mkB u s) / (∏ i, ((mkB u s i).totient : ℝ)))| ≤
      T.bound ^ 2 * (∏ i, ((u i).totient : ℝ)⁻¹) * (∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹) := by
    intro s hs u hu
    by_cases hAB : mkA u s ∈ validTupleSet k W₀ R ∧ mkB u s ∈ validTupleSet k W₀ R
    · obtain ⟨hAV, hBV⟩ := hAB
      have hA_cop := (squarefree_prod_coord ((mem_validTupleSet hR_pos.le).mp hAV).2.2.1).2
      have hB_cop := (squarefree_prod_coord ((mem_validTupleSet hR_pos.le).mp hBV).2.2.1).2
      -- Prove `mkA u s i = u i * ∏_{j ≠ i} s(i, j)` (pairwise coprime!) and `mkB u s i = u i * ∏_{j ≠ i} s(j, i)`
      have hphi_A : ∀ i : Fin (k + 1), ((mkA u s i).totient : ℝ) =
          ((u i).totient : ℝ) * ∏ j ∈ Finset.univ.erase i,
            ((if h : (i, j) ∈ offD then s ⟨(i, j), h⟩ else 1).totient : ℝ) := by
        intro i
        have hcop_pair : ∀ j₁ ∈ Finset.univ.erase i, ∀ j₂ ∈ Finset.univ.erase i, j₁ ≠ j₂ →
            Nat.Coprime (if h : (i, j₁) ∈ offD then s ⟨(i, j₁), h⟩ else 1)
              (if h : (i, j₂) ∈ offD then s ⟨(i, j₂), h⟩ else 1) := by
          intro j₁ hj₁ j₂ hj₂ hne
          have h1 : (i, j₁) ∈ offD :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j₁, (Finset.mem_erase.mp hj₁).1.symm⟩
          have h2 : (i, j₂) ∈ offD :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j₂, (Finset.mem_erase.mp hj₂).1.symm⟩
          rw [dif_pos h1, dif_pos h2]
          -- `s(i, j₁) ∣ mkB u s j₁` and `s(i, j₂) ∣ mkB u s j₂`, which are coprime!
          have hd1 : s ⟨(i, j₁), h1⟩ ∣ mkB u s j₁ := by
            have := Finset.dvd_lcm (f := fun j => if h : (j, j₁) ∈ offD then s ⟨(j, j₁), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj₁).1.symm, Finset.mem_univ i⟩)
            rw [dif_pos h1] at this
            exact dvd_trans this (Nat.dvd_lcm_right _ _)
          have hd2 : s ⟨(i, j₂), h2⟩ ∣ mkB u s j₂ := by
            have := Finset.dvd_lcm (f := fun j => if h : (j, j₂) ∈ offD then s ⟨(j, j₂), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj₂).1.symm, Finset.mem_univ i⟩)
            rw [dif_pos h2] at this
            exact dvd_trans this (Nat.dvd_lcm_right _ _)
          exact (hB_cop j₁ (Finset.mem_univ j₁) j₂ (Finset.mem_univ j₂) hne).coprime_dvd_left hd1
            |>.coprime_dvd_right hd2
        have hlcm_eq := finset_lcm_eq_prod_of_pairwise_coprime (Finset.univ.erase i) _ hcop_pair
        have hucop : Nat.Coprime (u i) (∏ j ∈ Finset.univ.erase i,
            if h : (i, j) ∈ offD then s ⟨(i, j), h⟩ else 1) := by
          refine Nat.Coprime.prod_right fun j hj => ?_
          have h1 : (i, j) ∈ offD :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, (Finset.mem_erase.mp hj).1.symm⟩
          rw [dif_pos h1]
          have hd_u : u i ∣ mkB u s i := Nat.dvd_lcm_left _ _
          have hd_s : s ⟨(i, j), h1⟩ ∣ mkB u s j := by
            have := Finset.dvd_lcm (f := fun r => if h : (r, j) ∈ offD then s ⟨(r, j), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1.symm, Finset.mem_univ i⟩)
            rw [dif_pos h1] at this
            exact dvd_trans this (Nat.dvd_lcm_right _ _)
          exact (hB_cop i (Finset.mem_univ i) j (Finset.mem_univ j) (Finset.mem_erase.mp hj).1.symm).coprime_dvd_left hd_u
            |>.coprime_dvd_right hd_s
        have hAeq : mkA u s i = u i * ∏ j ∈ Finset.univ.erase i,
            if h : (i, j) ∈ offD then s ⟨(i, j), h⟩ else 1 := by
          dsimp only [mkA]; rw [hlcm_eq]
          have h := Nat.gcd_mul_lcm (u i) (∏ j ∈ Finset.univ.erase i,
            if h : (i, j) ∈ offD then s ⟨(i, j), h⟩ else 1)
          rw [hucop.gcd_eq_one, one_mul] at h; exact h
        rw [hAeq, Nat.totient_mul hucop, totient_prod_of_pairwise_coprime _ _ hcop_pair]
        push_cast; rfl
      have hphi_B : ∀ i : Fin (k + 1), ((mkB u s i).totient : ℝ) =
          ((u i).totient : ℝ) * ∏ j ∈ Finset.univ.erase i,
            ((if h : (j, i) ∈ offD then s ⟨(j, i), h⟩ else 1).totient : ℝ) := by
        intro i
        have hcop_pair : ∀ j₁ ∈ Finset.univ.erase i, ∀ j₂ ∈ Finset.univ.erase i, j₁ ≠ j₂ →
            Nat.Coprime (if h : (j₁, i) ∈ offD then s ⟨(j₁, i), h⟩ else 1)
              (if h : (j₂, i) ∈ offD then s ⟨(j₂, i), h⟩ else 1) := by
          intro j₁ hj₁ j₂ hj₂ hne
          have h1 : (j₁, i) ∈ offD :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ j₁, Finset.mem_univ i, (Finset.mem_erase.mp hj₁).1⟩
          have h2 : (j₂, i) ∈ offD :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ j₂, Finset.mem_univ i, (Finset.mem_erase.mp hj₂).1⟩
          rw [dif_pos h1, dif_pos h2]
          have hd1 : s ⟨(j₁, i), h1⟩ ∣ mkA u s j₁ := by
            have := Finset.dvd_lcm (f := fun r => if h : (j₁, r) ∈ offD then s ⟨(j₁, r), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj₁).1.symm, Finset.mem_univ i⟩)
            rw [dif_pos h1] at this
            exact dvd_trans this (Nat.dvd_lcm_right _ _)
          have hd2 : s ⟨(j₂, i), h2⟩ ∣ mkA u s j₂ := by
            have := Finset.dvd_lcm (f := fun r => if h : (j₂, r) ∈ offD then s ⟨(j₂, r), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj₂).1.symm, Finset.mem_univ i⟩)
            rw [dif_pos h2] at this
            exact dvd_trans this (Nat.dvd_lcm_right _ _)
          exact (hA_cop j₁ (Finset.mem_univ j₁) j₂ (Finset.mem_univ j₂) hne).coprime_dvd_left hd1
            |>.coprime_dvd_right hd2
        have hlcm_eq := finset_lcm_eq_prod_of_pairwise_coprime (Finset.univ.erase i) _ hcop_pair
        have hucop : Nat.Coprime (u i) (∏ j ∈ Finset.univ.erase i,
            if h : (j, i) ∈ offD then s ⟨(j, i), h⟩ else 1) := by
          refine Nat.Coprime.prod_right fun j hj => ?_
          have h1 : (j, i) ∈ offD :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ j, Finset.mem_univ i, (Finset.mem_erase.mp hj).1⟩
          rw [dif_pos h1]
          have hd_u : u i ∣ mkA u s i := Nat.dvd_lcm_left _ _
          have hd_s : s ⟨(j, i), h1⟩ ∣ mkA u s j := by
            have := Finset.dvd_lcm (f := fun r => if h : (j, r) ∈ offD then s ⟨(j, r), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1.symm, Finset.mem_univ i⟩)
            rw [dif_pos h1] at this
            exact dvd_trans this (Nat.dvd_lcm_right _ _)
          exact (hA_cop i (Finset.mem_univ i) j (Finset.mem_univ j) (Finset.mem_erase.mp hj).1.symm).coprime_dvd_left hd_u
            |>.coprime_dvd_right hd_s
        have hBeq : mkB u s i = u i * ∏ j ∈ Finset.univ.erase i,
            if h : (j, i) ∈ offD then s ⟨(j, i), h⟩ else 1 := by
          dsimp only [mkB]; rw [hlcm_eq]
          have h := Nat.gcd_mul_lcm (u i) (∏ j ∈ Finset.univ.erase i,
            if h : (j, i) ∈ offD then s ⟨(j, i), h⟩ else 1)
          rw [hucop.gcd_eq_one, one_mul] at h; exact h
        rw [hBeq, Nat.totient_mul hucop, totient_prod_of_pairwise_coprime _ _ hcop_pair]
        push_cast; rfl
      -- Product over `i` of `∏_{j ≠ i} φ(s(i, j))` equals `∏_{p : offD} φ(s p)`!
      have hprod_offA : (∏ i : Fin (k + 1), ∏ j ∈ Finset.univ.erase i,
            ((if h : (i, j) ∈ offD then s ⟨(i, j), h⟩ else 1).totient : ℝ)) =
          ∏ p : offD, ((s p).totient : ℝ) := by
        rw [← Finset.prod_sigma (s := Finset.univ) (t := fun i : Fin (k + 1) => Finset.univ.erase i)
          (f := fun x : Σ _ : Fin (k + 1), Fin (k + 1) =>
            ((if h : (x.1, x.2) ∈ offD then s ⟨(x.1, x.2), h⟩ else 1).totient : ℝ))]
        refine Finset.prod_bij (fun x _ => ⟨(x.1, x.2),
          Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
            (Finset.mem_erase.mp (Finset.mem_sigma.mp ‹_›).2).1.symm⟩⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro x₁ _ x₂ _ heq
          simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
          exact Sigma.ext heq.1 (heq_of_eq heq.2)
        · intro p _
          refine ⟨⟨p.1.1, p.1.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
            Finset.mem_erase.mpr ⟨(Finset.mem_offDiag.mp p.2).2.2.symm, Finset.mem_univ _⟩⟩,
            Subtype.ext rfl⟩
        · intro x hx
          have hmem : (x.1, x.2) ∈ offD :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
              (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).1.symm⟩
          simp only [dif_pos hmem]
      have hprod_offB : (∏ i : Fin (k + 1), ∏ j ∈ Finset.univ.erase i,
            ((if h : (j, i) ∈ offD then s ⟨(j, i), h⟩ else 1).totient : ℝ)) =
          ∏ p : offD, ((s p).totient : ℝ) := by
        rw [← Finset.prod_sigma (s := Finset.univ) (t := fun i : Fin (k + 1) => Finset.univ.erase i)
          (f := fun x : Σ _ : Fin (k + 1), Fin (k + 1) =>
            ((if h : (x.2, x.1) ∈ offD then s ⟨(x.2, x.1), h⟩ else 1).totient : ℝ))]
        refine Finset.prod_bij (fun x _ => ⟨(x.2, x.1),
          Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
            (Finset.mem_erase.mp (Finset.mem_sigma.mp ‹_›).2).1⟩⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro x₁ _ x₂ _ heq
          simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
          exact Sigma.ext heq.2 (heq_of_eq heq.1)
        · intro p _
          refine ⟨⟨p.1.2, p.1.1⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
            Finset.mem_erase.mpr ⟨(Finset.mem_offDiag.mp p.2).2.2, Finset.mem_univ _⟩⟩,
            Subtype.ext rfl⟩
        · intro x hx
          have hmem : (x.2, x.1) ∈ offD :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
              (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).1⟩
          simp only [dif_pos hmem]
      have hphi_A_prod : (∏ i, ((mkA u s i).totient : ℝ)) =
          (∏ i, ((u i).totient : ℝ)) * ∏ p : offD, ((s p).totient : ℝ) := by
        rw [Finset.prod_congr rfl fun i _ => hphi_A i, Finset.prod_mul_distrib, hprod_offA]
      have hphi_B_prod : (∏ i, ((mkB u s i).totient : ℝ)) =
          (∏ i, ((u i).totient : ℝ)) * ∏ p : offD, ((s p).totient : ℝ) := by
        rw [Finset.prod_congr rfl fun i _ => hphi_B i, Finset.prod_mul_distrib, hprod_offB]
      have hmu_le1 : ∀ n : ℕ, |(μ n : ℝ)| ≤ 1 := fun n => by
        by_cases hsf : Squarefree n
        · rw [moebius_eq_prod_neg_one_of_squarefree hsf, Finset.abs_prod]; simp
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
      have hu_pos : 0 < ∏ i, ((u i).totient : ℝ) :=
        Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.totient_pos.mpr
          (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu i)).1).1)
      have hs_pos : 0 < ∏ p : offD, ((s p).totient : ℝ) :=
        Finset.prod_pos fun p _ => Nat.cast_pos.mpr (Nat.totient_pos.mpr
          (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_of_mem_erase hs) p)).1).1)
      rw [hphi_A_prod, hphi_B_prod]
      have hden_eq : (∏ i, ((u i).totient : ℝ)) /
          (((∏ i, ((u i).totient : ℝ)) * ∏ p : offD, ((s p).totient : ℝ)) *
            ((∏ i, ((u i).totient : ℝ)) * ∏ p : offD, ((s p).totient : ℝ))) =
          (∏ i, ((u i).totient : ℝ)⁻¹) * (∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹) := by
        rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_pow]
        field_simp [hu_pos.ne', hs_pos.ne']
      have habs_mu : |(∏ p : offD, (μ (s p) : ℝ)) * (∏ i, (μ (mkA u s i) : ℝ)) *
          (∏ i, (μ (mkB u s i) : ℝ))| ≤ 1 := by
        rw [abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod, Finset.abs_prod]
        have h1 : ∏ p : offD, |(μ (s p) : ℝ)| ≤ 1 := Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p _ => hmu_le1 _)
        have h2 : ∏ i, |(μ (mkA u s i) : ℝ)| ≤ 1 := Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hmu_le1 _)
        have h3 : ∏ i, |(μ (mkB u s i) : ℝ)| ≤ 1 := Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hmu_le1 _)
        calc (∏ p : offD, |(μ (s p) : ℝ)|) * (∏ i, |(μ (mkA u s i) : ℝ)|) * (∏ i, |(μ (mkB u s i) : ℝ)|)
            ≤ 1 * 1 * 1 := by
              refine mul_le_mul (mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) zero_le_one)
                h3 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have hrew : (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
            ((∏ i, (μ (mkA u s i) : ℝ)) * yVar W₀ R T (mkA u s) /
              ((∏ i, ((u i).totient : ℝ)) * ∏ p : offD, ((s p).totient : ℝ))) *
            ((∏ i, (μ (mkB u s i) : ℝ)) * yVar W₀ R T (mkB u s) /
              ((∏ i, ((u i).totient : ℝ)) * ∏ p : offD, ((s p).totient : ℝ))) =
          ((∏ p : offD, (μ (s p) : ℝ)) * (∏ i, (μ (mkA u s i) : ℝ)) * (∏ i, (μ (mkB u s i) : ℝ))) *
            (yVar W₀ R T (mkA u s) * yVar W₀ R T (mkB u s)) *
            ((∏ i, ((u i).totient : ℝ)) /
              (((∏ i, ((u i).totient : ℝ)) * ∏ p : offD, ((s p).totient : ℝ)) *
                ((∏ i, ((u i).totient : ℝ)) * ∏ p : offD, ((s p).totient : ℝ)))) := by ring
      have hden_nn : 0 ≤ (∏ i, ((u i).totient : ℝ)⁻¹) * (∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹) :=
        mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
          (Finset.prod_nonneg fun _ _ => by positivity)
      rw [hrew, hden_eq, abs_mul, abs_mul, abs_of_nonneg hden_nn]
      have hy_bd : |yVar W₀ R T (mkA u s) * yVar W₀ R T (mkB u s)| ≤ T.bound ^ 2 := by
        rw [abs_mul, sq]
        exact mul_le_mul (abs_yVar_le W₀ hR T _) (abs_yVar_le W₀ hR T _) (abs_nonneg _) T.bound_nonneg
      calc |(∏ p : offD, (μ (s p) : ℝ)) * (∏ i, (μ (mkA u s i) : ℝ)) * (∏ i, (μ (mkB u s i) : ℝ))| *
            |yVar W₀ R T (mkA u s) * yVar W₀ R T (mkB u s)| *
            ((∏ i, ((u i).totient : ℝ)⁻¹) * (∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹))
          ≤ 1 * T.bound ^ 2 *
              ((∏ i, ((u i).totient : ℝ)⁻¹) * (∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹)) := by
            gcongr
        _ = T.bound ^ 2 * (∏ i, ((u i).totient : ℝ)⁻¹) *
              (∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹) := by ring
    · -- At least one of `mkA u s`, `mkB u s` is not in `validTupleSet`, so term is `0`!
      have hzero : yVar W₀ R T (mkA u s) = 0 ∨ yVar W₀ R T (mkB u s) = 0 := by
        by_cases hA : mkA u s ∈ validTupleSet k W₀ R
        · right; unfold yVar; rw [if_neg (fun hB => hAB ⟨hA, hB⟩)]
        · left; unfold yVar; rw [if_neg hA]
      rcases hzero with h0 | h0 <;> simp [h0] <;> positivity
  -- Sum `hterm_s` over `s ∈ Sset.erase s1` and `u ∈ Uset`
  have hsum_u : ∑ u ∈ Uset, ∏ i : Fin (k + 1), ((u i).totient : ℝ)⁻¹ =
      (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 1) := by
    rw [sum_piFinset_prod (fun _ : Fin (k + 1) => S_sf) (fun _ x => ((x.totient : ℝ))⁻¹),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    unfold aPhi; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hsum_s : ∑ s ∈ Sset.erase s1, ∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹ ≤
      (1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1 := by
    have hfull : ∑ s ∈ Sset, ∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹ =
        (∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹) ^ ((k + 1) * k) := by
      rw [sum_piFinset_prod (fun _ : offD => S_sf) (fun _ x => (((x.totient : ℝ) ^ 2))⁻¹),
        Finset.prod_const, Finset.card_univ, Fintype.card_coe, hoffD_card]
    have hsplit_s := Finset.add_sum_erase Sset (fun s => ∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹) hs1_mem
    have hs1_val : ∏ p : offD, (((s1 p).totient : ℝ) ^ 2)⁻¹ = 1 := by simp [s1]
    rw [hs1_val] at hsplit_s
    have h1d_phi2 : ∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹ ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := by
      have h2W : 2 ∣ W₀ := (prime_dvd_W_iff Nat.prime_two).mpr (by omega)
      calc ∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹
          ≤ ∑ n ∈ S_sf, (((g₂ n : ℝ) ^ 2))⁻¹ := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hsf := (Finset.mem_filter.mp hn).2.1
            have hcop := (Finset.mem_filter.mp hn).2.2
            have hgpos : (0 : ℝ) < (g₂ n : ℝ) :=
              Nat.cast_pos.mpr (g₂_pos_of_coprime_two hsf.ne_zero (hcop.coprime_dvd_right h2W))
            exact inv_anti₀ (sq_pos_of_pos hgpos)
              (pow_le_pow_left₀ hgpos.le (by exact_mod_cast g₂_le_totient_of_squarefree hsf) 2)
        _ ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := sum_inv_g2_sq_le hD
    have hpow : (∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹) ^ ((k + 1) * k) ≤
        (1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) h1d_phi2 _
    linarith
  calc ∑ s ∈ Sset.erase s1, ∑ u ∈ Uset,
        (∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
          ((∏ i, (μ (mkA u s i) : ℝ)) * yVar W₀ R T (mkA u s) / (∏ i, ((mkA u s i).totient : ℝ))) *
          ((∏ i, (μ (mkB u s i) : ℝ)) * yVar W₀ R T (mkB u s) / (∏ i, ((mkB u s i).totient : ℝ)))
      ≤ ∑ s ∈ Sset.erase s1, ∑ u ∈ Uset,
          |(∏ i, ((u i).totient : ℝ)) * (∏ p : offD, (μ (s p) : ℝ)) *
            ((∏ i, (μ (mkA u s i) : ℝ)) * yVar W₀ R T (mkA u s) / (∏ i, ((mkA u s i).totient : ℝ))) *
            ((∏ i, (μ (mkB u s i) : ℝ)) * yVar W₀ R T (mkB u s) / (∏ i, ((mkB u s i).totient : ℝ)))| :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun u _ => le_abs_self _
    _ ≤ ∑ s ∈ Sset.erase s1, ∑ u ∈ Uset,
          T.bound ^ 2 * (∏ i, ((u i).totient : ℝ)⁻¹) *
            (∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun u hu => hterm_s s hs u hu
    _ = T.bound ^ 2 * (∑ u ∈ Uset, ∏ i, ((u i).totient : ℝ)⁻¹) *
          (∑ s ∈ Sset.erase s1, ∏ p : offD, (((s p).totient : ℝ) ^ 2)⁻¹) := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ T.bound ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 1) *
          ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1) := by
        rw [hsum_u]
        exact mul_le_mul_of_nonneg_left hsum_s
          (mul_nonneg (sq_nonneg _) (pow_nonneg (Finset.sum_nonneg fun _ _ => aPhi_nonneg _ _) _))

/-- **Plain Sieve Sum `S₂` Upper Bound on `[A, B)`**:
if every distinct pair `h i ≠ h j` has `|h i - h j| ≤ D₀`, then
`∑_{n ∈ [A, B), n ≡ b [MOD W D₀]} sieveWeight h (W D₀) R T n ≤
  ((B - A) / W D₀) * Q2Sum (W D₀) R T + (∑_{d ∈ V} |lamVar d|)²`. -/
theorem S2_interval_upper {k D₀ : ℕ} {h : Fin (k + 1) ↪ ℕ}
    (hdiff : ∀ i j : Fin (k + 1), i ≠ j → (h i : ℤ) - (h j : ℤ) ≠ 0 ∧ |(h i : ℤ) - (h j : ℤ)| ≤ (D₀ : ℤ))
    {R : ℝ} (hR : Real.exp 4 ≤ R) (T : SimplexTestFn (k + 1)) (b A B : ℕ) (hAB : A ≤ B) :
    ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W D₀]),
        sieveWeight h (W D₀) R T n ≤
      (((B - A : ℕ) : ℝ) / (W D₀ : ℝ)) * Q2Sum (W D₀) R T +
        (∑ d ∈ validTupleSet k (W D₀) R, |lamVar (W D₀) R T d|) ^ 2 := by
  set W₀ := W D₀
  have hW_pos : 1 ≤ W₀ := W_pos D₀
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
  -- Expand `(∑_{d ∣ n + h} λ_d)² = ∑_{d, e} λ_d λ_e 1_{∀ i, lcm(d i, e i) ∣ n + h i}` and swap sums
  have hexpand : ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]),
        sieveWeight h W₀ R T n =
      ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
        lamVar W₀ R T d * lamVar W₀ R T e *
          ((((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧
              ∀ i, Nat.lcm (d i) (e i) ∣ n + h i)).card : ℝ)) := by
    have h1 : ∀ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]),
        sieveWeight h W₀ R T n =
        ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
          if (∀ i, Nat.lcm (d i) (e i) ∣ n + h i) then
            lamVar W₀ R T d * lamVar W₀ R T e
          else 0 := by
      intro n _
      unfold sieveWeight
      rw [sq, Finset.sum_mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd_div : ∀ i, d i ∣ n + h i
      · rw [if_pos hd_div, Finset.sum_filter]
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases he_div : ∀ i, e i ∣ n + h i
        · have hl : ∀ i, Nat.lcm (d i) (e i) ∣ n + h i := fun i => Nat.lcm_dvd (hd_div i) (he_div i)
          rw [if_pos he_div, if_pos hl]
        · have hl : ¬ ∀ i, Nat.lcm (d i) (e i) ∣ n + h i := fun hl =>
            he_div fun i => dvd_trans (Nat.dvd_lcm_right _ _) (hl i)
          rw [if_neg he_div, if_neg hl]
      · rw [if_neg hd_div]
        symm
        refine Finset.sum_eq_zero fun e _ => ?_
        have hl : ¬ ∀ i, Nat.lcm (d i) (e i) ∣ n + h i := fun hl =>
          hd_div fun i => dvd_trans (Nat.dvd_lcm_left _ _) (hl i)
        rw [if_neg hl]
    rw [Finset.sum_congr rfl h1]
    calc ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]),
            ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
              (if (∀ i, Nat.lcm (d i) (e i) ∣ n + h i) then lamVar W₀ R T d * lamVar W₀ R T e else 0)
        = ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
            ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]),
              (if (∀ i, Nat.lcm (d i) (e i) ∣ n + h i) then lamVar W₀ R T d * lamVar W₀ R T e else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          have hfeq : ((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀])).filter
                (fun n => ∀ i, Nat.lcm (d i) (e i) ∣ n + h i) =
              (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧
                ∀ i, Nat.lcm (d i) (e i) ∣ n + h i) := by
            ext n; simp [and_assoc]
          rw [hfeq]
  rw [hexpand]
  have coprime_lcm_left : ∀ {a b c : ℕ}, Nat.Coprime a c → Nat.Coprime b c → Nat.Coprime (Nat.lcm a b) c :=
    fun ha hb => (ha.mul_left hb).coprime_dvd_left (Nat.lcm_dvd_mul _ _)
  have coprime_lcm_right : ∀ {a b c : ℕ}, Nat.Coprime c a → Nat.Coprime c b → Nat.Coprime c (Nat.lcm a b) :=
    fun ha hb => (coprime_lcm_left ha.symm hb.symm).symm
  -- Evaluate each `(d, e)` term: if `¬ PairwiseCoprimeCross d e`, count = 0; else CRT + `card_Ico_modEq_sub_div_le`!
  have hde_bound : ∀ d ∈ validTupleSet k W₀ R, ∀ e ∈ validTupleSet k W₀ R,
      lamVar W₀ R T d * lamVar W₀ R T e *
        ((((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧
            ∀ i, Nat.lcm (d i) (e i) ∣ n + h i)).card : ℝ)) ≤
      (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) *
        (if PairwiseCoprimeCross d e then
          lamVar W₀ R T d * lamVar W₀ R T e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))
        else 0) +
      |lamVar W₀ R T d| * |lamVar W₀ R T e| := by
    intro d hd e he
    obtain ⟨hd1, _, hd_sf, hd_cop⟩ := (mem_validTupleSet hR_pos.le).mp hd
    obtain ⟨he1, _, he_sf, he_cop⟩ := (mem_validTupleSet hR_pos.le).mp he
    by_cases hpc : PairwiseCoprimeCross d e
    · rw [if_pos hpc]
      -- Moduli `M : Option (Fin (k + 1)) → ℕ` are pairwise coprime!
      let M : Option (Fin (k + 1)) → ℕ
        | none => W₀
        | some i => Nat.lcm (d i) (e i)
      let c : Option (Fin (k + 1)) → ℕ
        | none => b
        | some i => (M (some i) - h i % M (some i)) % M (some i)
      have hM_cop : ∀ x ∈ (Finset.univ : Finset (Option (Fin (k + 1)))),
          ∀ y ∈ (Finset.univ : Finset (Option (Fin (k + 1)))), x ≠ y → Nat.Coprime (M x) (M y) := by
        intro x _ y _ hxy
        have hd_cop_i : ∀ i, Nat.Coprime (d i) W₀ := fun i =>
          hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
        have he_cop_i : ∀ i, Nat.Coprime (e i) W₀ := fun i =>
          he_cop.coprime_dvd_left (Finset.dvd_prod_of_mem e (Finset.mem_univ i))
        have hd_pair := (squarefree_prod_coord hd_sf).2
        have he_pair := (squarefree_prod_coord he_sf).2
        cases x with
        | none =>
          cases y with
          | none => exact absurd rfl hxy
          | some j =>
            dsimp only [M]
            exact (coprime_lcm_left (hd_cop_i j) (he_cop_i j)).symm
        | some i =>
          cases y with
          | none =>
            dsimp only [M]
            exact coprime_lcm_left (hd_cop_i i) (he_cop_i i)
          | some j =>
            have hij : i ≠ j := fun h => hxy (congrArg some h)
            dsimp only [M]
            exact coprime_lcm_left
              (coprime_lcm_right (hd_pair i (Finset.mem_univ i) j (Finset.mem_univ j) hij)
                (hpc i j hij))
              (coprime_lcm_right (hpc j i hij.symm).symm
                (he_pair i (Finset.mem_univ i) j (Finset.mem_univ j) hij))
      obtain ⟨x₀, hx₀⟩ := exists_crt_finset Finset.univ M c hM_cop
      have hMprod : ∏ x : Option (Fin (k + 1)), M x = W₀ * ∏ i, Nat.lcm (d i) (e i) := by
        rw [Fintype.prod_option]
      have hMpos : 1 ≤ W₀ * ∏ i, Nat.lcm (d i) (e i) :=
        Nat.mul_pos hW_pos (Finset.prod_pos fun i _ => Nat.lcm_pos (hd1 i) (he1 i))
      have hfilt_eq : (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧
            ∀ i, Nat.lcm (d i) (e i) ∣ n + h i) =
          (Finset.Ico A B).filter (fun n => n ≡ x₀ [MOD W₀ * ∏ i, Nat.lcm (d i) (e i)]) := by
        ext n; simp only [Finset.mem_filter]; refine and_congr_right fun _ => ?_
        rw [← hMprod, ← hx₀ n]
        have hc_add : ∀ i, c (some i) + h i ≡ 0 [MOD Nat.lcm (d i) (e i)] := fun i => by
          dsimp only [c, M]
          have hmpos : 0 < Nat.lcm (d i) (e i) := Nat.lcm_pos (hd1 i) (he1 i)
          have hlt : h i % Nat.lcm (d i) (e i) < Nat.lcm (d i) (e i) := Nat.mod_lt _ hmpos
          rw [Nat.ModEq, Nat.add_mod, Nat.mod_mod, Nat.mod_add_mod]
          have heq : Nat.lcm (d i) (e i) - h i % Nat.lcm (d i) (e i) + h i % Nat.lcm (d i) (e i) =
              Nat.lcm (d i) (e i) := Nat.sub_add_cancel hlt.le
          rw [heq, Nat.mod_self, Nat.zero_mod]
        constructor
        · rintro ⟨hnb, hdiv⟩ x _
          cases x with
          | none => exact hnb
          | some i =>
            dsimp only [M]
            have h0 : n + h i ≡ 0 [MOD Nat.lcm (d i) (e i)] := Nat.modEq_zero_iff_dvd.mpr (hdiv i)
            exact Nat.ModEq.add_right_cancel' (h i) (h0.trans (hc_add i).symm)
        · intro hall
          refine ⟨hall none (Finset.mem_univ none), fun i => ?_⟩
          have hi := hall (some i) (Finset.mem_univ (some i))
          exact Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_right (h i) hi).trans (hc_add i))
      rw [hfilt_eq]
      have hcnt := card_Ico_modEq_sub_div_le hMpos A B x₀ hAB
      have hdiv_eq : ((B - A : ℕ) : ℝ) / ((W₀ * ∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ) =
          (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) / (∏ i, (Nat.lcm (d i) (e i) : ℝ)) := by
        rw [Nat.cast_mul, Nat.cast_prod, div_div]
      rw [hdiv_eq] at hcnt
      set cnt := (((Finset.Ico A B).filter (fun n => n ≡ x₀ [MOD W₀ * ∏ i, Nat.lcm (d i) (e i)])).card : ℝ)
      set main := (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) / (∏ i, (Nat.lcm (d i) (e i) : ℝ))
      have hle : lamVar W₀ R T d * lamVar W₀ R T e * (cnt - main) ≤
          |lamVar W₀ R T d| * |lamVar W₀ R T e| := by
        calc lamVar W₀ R T d * lamVar W₀ R T e * (cnt - main)
            ≤ |lamVar W₀ R T d * lamVar W₀ R T e * (cnt - main)| := le_abs_self _
          _ = |lamVar W₀ R T d| * |lamVar W₀ R T e| * |cnt - main| := by rw [abs_mul, abs_mul]
          _ ≤ |lamVar W₀ R T d| * |lamVar W₀ R T e| * 1 :=
              mul_le_mul_of_nonneg_left hcnt (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = |lamVar W₀ R T d| * |lamVar W₀ R T e| := mul_one _
      have hmain_eq : lamVar W₀ R T d * lamVar W₀ R T e * main =
          (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) *
            (lamVar W₀ R T d * lamVar W₀ R T e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))) := by
        dsimp only [main]; ring
      linarith
    · -- `¬ PairwiseCoprimeCross d e`: no `n` satisfies all divisibilities!
      rw [if_neg hpc, mul_zero, zero_add]
      have hempty : (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧
          ∀ i, Nat.lcm (d i) (e i) ∣ n + h i) = ∅ := by
        ext n; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ _ hdiv
        unfold PairwiseCoprimeCross at hpc; push Not at hpc
        obtain ⟨i, j, hij, hnc⟩ := hpc
        obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hnc
        have hpd : p ∣ d i := dvd_trans hpgcd (Nat.gcd_dvd_left _ _)
        have hpe : p ∣ e j := dvd_trans hpgcd (Nat.gcd_dvd_right _ _)
        have hpni : p ∣ n + h i := dvd_trans hpd (dvd_trans (Nat.dvd_lcm_left _ _) (hdiv i))
        have hpnj : p ∣ n + h j := dvd_trans hpe (dvd_trans (Nat.dvd_lcm_right _ _) (hdiv j))
        -- Hence `p ∣ |(h i : ℤ) - (h j : ℤ)|`, so `p ≤ D₀`, so `p ∣ W D₀`, contradicting `Coprime (d i) W₀`!
        have hp_int : (p : ℤ) ∣ (h i : ℤ) - (h j : ℤ) := by
          have hiZ : (p : ℤ) ∣ (n : ℤ) + (h i : ℤ) := by exact_mod_cast hpni
          have hjZ : (p : ℤ) ∣ (n : ℤ) + (h j : ℤ) := by exact_mod_cast hpnj
          have hsub := dvd_sub hiZ hjZ
          simpa using hsub
        have hp_le_D0 : p ≤ D₀ := by
          have hne := (hdiff i j hij).1
          have habs_le := (hdiff i j hij).2
          have hdvd_nat : p ∣ ((h i : ℤ) - (h j : ℤ)).natAbs := by
            exact Int.natCast_dvd.mp hp_int
          have hpos_abs : 0 < ((h i : ℤ) - (h j : ℤ)).natAbs := Int.natAbs_pos.mpr hne
          have hle1 : p ≤ ((h i : ℤ) - (h j : ℤ)).natAbs := Nat.le_of_dvd hpos_abs hdvd_nat
          have hle2 : ((h i : ℤ) - (h j : ℤ)).natAbs ≤ D₀ := by
            have : ((((h i : ℤ) - (h j : ℤ)).natAbs : ℕ) : ℤ) = |(h i : ℤ) - (h j : ℤ)| :=
              Int.natCast_natAbs _
            omega
          exact hle1.trans hle2
        have hpW : p ∣ W₀ := (prime_dvd_W_iff hp).mpr hp_le_D0
        have hcop_di : Nat.Coprime (d i) W₀ :=
          hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
        exact hp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hcop_di) ▸ Nat.dvd_gcd hpd hpW)
      rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
        lamVar W₀ R T d * lamVar W₀ R T e *
          ((((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧
              ∀ i, Nat.lcm (d i) (e i) ∣ n + h i)).card : ℝ))
      ≤ ∑ d ∈ validTupleSet k W₀ R, ∑ e ∈ validTupleSet k W₀ R,
          ((((B - A : ℕ) : ℝ) / (W₀ : ℝ)) *
            (if PairwiseCoprimeCross d e then
              lamVar W₀ R T d * lamVar W₀ R T e / (∏ i, (Nat.lcm (d i) (e i) : ℝ))
            else 0) +
          |lamVar W₀ R T d| * |lamVar W₀ R T e|) :=
        Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => hde_bound d hd e he
    _ = (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * Q2Sum W₀ R T +
          (∑ d ∈ validTupleSet k W₀ R, |lamVar W₀ R T d|) ^ 2 := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        · unfold Q2Sum; simp_rw [Finset.mul_sum]
        · rw [sq, Finset.sum_mul_sum]

/-! ### Section 4b: Asymptotic Upper Bound for `Q2Sum` and Lower Bound for `Q1Sum` -/

/-- Helper: for `c ≥ 0`, `C ≥ 0`, `L ≥ 1`, and `n ≥ 1`:
`(c * L + C) ^ n ≤ (c * L) ^ n + (c + C) ^ n * L ^ (n - 1)`. -/
private lemma add_pow_le_main_plus_lower {c C L : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (n : ℕ) :
    (c * L + C) ^ (n + 1) ≤ (c * L) ^ (n + 1) + (c + C) ^ (n + 1) * L ^ n := by
  have hL0 : 0 ≤ L := by linarith
  have hbin : (c * L + C) ^ (n + 1) =
      ∑ j ∈ Finset.range (n + 2), (c * L) ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ) :=
    add_pow (c * L) C (n + 1)
  rw [hbin, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  have hrest : ∑ j ∈ Finset.range (n + 1),
        (c * L) ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ) ≤
      (c + C) ^ (n + 1) * L ^ n := by
    calc ∑ j ∈ Finset.range (n + 1), (c * L) ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ)
        ≤ ∑ j ∈ Finset.range (n + 1), c ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ) * L ^ n := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hLj : L ^ j ≤ L ^ n := pow_le_pow_right₀ hL hj_le
          rw [mul_pow]
          calc c ^ j * L ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ)
              = c ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ) * L ^ j := by ring
            _ ≤ c ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ) * L ^ n := by gcongr
      _ = (∑ j ∈ Finset.range (n + 1), c ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ)) * L ^ n := by
          rw [← Finset.sum_mul]
      _ ≤ (∑ j ∈ Finset.range (n + 2), c ^ j * C ^ (n + 1 - j) * ((n + 1).choose j : ℝ)) * L ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hL0 _)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _))
            fun _ _ _ => by positivity
      _ = (c + C) ^ (n + 1) * L ^ n := by rw [← add_pow c C (n + 1)]
  linarith

/-- **Asymptotic Upper Bound for `Q2Sum`**: for fixed `D₀ ≥ 6`, `T : SimplexTestFn (k + 1)`:
there exists `K₂ ≥ 0` such that for all `R ≥ exp 4`:
`Q2Sum (W D₀) R T ≤ ((φ(W D₀)/W D₀) * log R)^(k + 1) * (maynardI (k + 1) T.F + E₂(D₀)) + K₂ * (log R)^(k + 1/2)`. -/
theorem Q2Sum_asymp_upper {k D₀ : ℕ} (hD : 6 ≤ D₀) (T : SimplexTestFn (k + 1)) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ R : ℝ, Real.exp 4 ≤ R →
      Q2Sum (W D₀) R T ≤
        ((((W D₀).totient : ℝ) / (W D₀ : ℝ)) * Real.log R) ^ (k + 1) *
          (maynardI (k + 1) T.F +
            T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) +
        K₂ * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
  set W₀ := W D₀
  set cW : ℝ := ((W₀.totient : ℝ) / (W₀ : ℝ))
  have hcW_nn : 0 ≤ cW := by positivity
  obtain ⟨C_phi, hC_phi, hphi_asymp⟩ := sum_aPhi_asymp (W D₀) (W_pos D₀)
  obtain ⟨K_int, hK_int_nn, hK_int⟩ :=
    sum_kd_approx_integral (k + 1) (aPhi_nonneg W₀) hcW_nn hC_phi.le hphi_asymp T.isSimplexLipOn.sq
  set E_off : ℝ := T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)
  have hE_off_nn : 0 ≤ E_off := by
    dsimp only [E_off]
    have h1 : (1 : ℝ) ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ 2 / ((D₀ - 2 : ℕ) : ℝ) := by positivity
      linarith
    have h2 : (1 : ℝ) ≤ (1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) := one_le_pow₀ h1
    exact mul_nonneg (sq_nonneg _) (by linarith)
  set K₂ : ℝ := K_int + E_off * (cW + C_phi) ^ (k + 1)
  refine ⟨K₂, add_nonneg hK_int_nn (mul_nonneg hE_off_nn (pow_nonneg (by positivity) _)), fun R hR => ?_⟩
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
  have hR1 : 1 ≤ R := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hR
  have hlogR4 : 4 ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 4) hR; rwa [Real.log_exp] at this
  have hlogR1 : 1 ≤ Real.log R := by linarith
  have hQ2 := Q2Sum_le hD hR T
  -- Upper bound the diagonal sum by the full simplex sum (dropping pairwise coprimality)
  have hdiag_le : ∑ u ∈ validTupleSet k W₀ R, (yVar W₀ R T u) ^ 2 / (∏ i, ((u i).totient : ℝ)) ≤
      ∑ r ∈ (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 ⌊R⌋₊)).filter
          (fun r => ((∏ i, r i : ℕ) : ℝ) ≤ R),
        (∏ i, aPhi W₀ (r i)) * (T.F (fun i => Real.log (r i : ℝ) / Real.log R)) ^ 2 := by
    have hsub : validTupleSet k W₀ R ⊆
        (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 ⌊R⌋₊)).filter
          (fun r => ((∏ i, r i : ℕ) : ℝ) ≤ R) := by
      intro u hu; simp only [validTupleSet, Finset.mem_filter] at hu ⊢; exact ⟨hu.1, hu.2.1⟩
    calc ∑ u ∈ validTupleSet k W₀ R, (yVar W₀ R T u) ^ 2 / (∏ i, ((u i).totient : ℝ))
        = ∑ u ∈ validTupleSet k W₀ R,
            (∏ i, aPhi W₀ (u i)) * (T.F (fun i => Real.log (u i : ℝ) / Real.log R)) ^ 2 := by
          refine Finset.sum_congr rfl fun u hu => ?_
          obtain ⟨_, _, hu_sf, hu_cop⟩ := (mem_validTupleSet hR_pos.le).mp hu
          unfold yVar; rw [if_pos hu]
          have ha_eq : ∏ i : Fin (k + 1), aPhi W₀ (u i) = (∏ i, ((u i).totient : ℝ))⁻¹ := by
            rw [← Finset.prod_inv_distrib]
            refine Finset.prod_congr rfl fun i _ => ?_
            unfold aPhi
            rw [if_pos ⟨(squarefree_prod_coord hu_sf).1 i (Finset.mem_univ i),
              hu_cop.coprime_dvd_left (Finset.dvd_prod_of_mem u (Finset.mem_univ i))⟩]
          rw [ha_eq]; ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ =>
          mul_nonneg (Finset.prod_nonneg fun _ _ => aPhi_nonneg _ _) (sq_nonneg _)
  have hint_bd := (abs_le.mp (hK_int R hR)).2
  have hsum_aPhi : ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n ≤ cW * Real.log R + C_phi := by
    linarith [(abs_le.mp (hphi_asymp R hR1)).2]
  have hpow_aPhi : (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 1) ≤
      (cW * Real.log R) ^ (k + 1) + (cW + C_phi) ^ (k + 1) * (Real.log R) ^ k :=
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => aPhi_nonneg _ _) hsum_aPhi (k + 1)).trans
      (add_pow_le_main_plus_lower hcW_nn hC_phi.le hlogR1 k)
  have hLk_le : (Real.log R) ^ k ≤ (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlogR1 (by push_cast; linarith)
  have hoff_bd : T.bound ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 1) *
        ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1) ≤
      (cW * Real.log R) ^ (k + 1) * E_off +
        E_off * (cW + C_phi) ^ (k + 1) * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
    calc T.bound ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 1) *
            ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)
        = (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 1) * E_off := by dsimp only [E_off]; ring
      _ ≤ ((cW * Real.log R) ^ (k + 1) + (cW + C_phi) ^ (k + 1) * (Real.log R) ^ k) * E_off :=
          mul_le_mul_of_nonneg_right hpow_aPhi hE_off_nn
      _ = (cW * Real.log R) ^ (k + 1) * E_off + E_off * (cW + C_phi) ^ (k + 1) * (Real.log R) ^ k := by ring
      _ ≤ (cW * Real.log R) ^ (k + 1) * E_off +
            E_off * (cW + C_phi) ^ (k + 1) * (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) := by gcongr
  have hI_eq : maynardI (k + 1) T.F = simplexIntegral (k + 1) 1 (fun v => (T.F v) ^ 2) := rfl
  rw [hI_eq]
  dsimp only [K₂]
  linarith

/-- The quadratic form `Q1Sum` appearing in the prime-weighted sieve sum `S₁^{(m)}`. -/
def Q1Sum {k : ℕ} (W₀ : ℕ) (R : ℝ) (T : SimplexTestFn (k + 1)) (m : Fin (k + 1)) : ℝ :=
  ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1),
    ∑ e ∈ (validTupleSet k W₀ R).filter (fun e => e m = 1),
      if PairwiseCoprimeCross d e then
        lamVar W₀ R T d * lamVar W₀ R T e /
          (∏ i ∈ Finset.univ.erase m, ((Nat.lcm (d i) (e i)).totient : ℝ))
      else 0

/-- For squarefree `a` and `b`, `φ(gcd(a, b)) * φ(lcm(a, b)) = φ(a) * φ(b)`. -/
lemma totient_gcd_mul_totient_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    (Nat.gcd a b).totient * (Nat.lcm a b).totient = a.totient * b.totient := by
  set g := Nat.gcd a b
  set a' := a / g
  set b' := b / g
  have hga : g * a' = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * b' = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hcop_ga' : Nat.Coprime g a' := Nat.coprime_of_squarefree_mul (hga.symm ▸ ha)
  have hcop_gb' : Nat.Coprime g b' := Nat.coprime_of_squarefree_mul (hgb.symm ▸ hb)
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha.ne_zero)
  have hcop_a'b' : Nat.Coprime a' b' := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hmul : g * Nat.gcd a' b' = Nat.gcd (g * a') (g * b') := (Nat.gcd_mul_left g a' b').symm
    rw [hga, hgb] at hmul
    exact Nat.eq_of_mul_eq_mul_left hg_pos (by omega)
  have hlcm : Nat.lcm a b = g * a' * b' := by
    have h1 := Nat.gcd_mul_lcm a b
    have h2 : g * (g * a' * b') = a * b := by
      calc g * (g * a' * b') = (g * a') * (g * b') := by ring
        _ = a * b := by rw [hga, hgb]
    exact Nat.eq_of_mul_eq_mul_left hg_pos (h1.trans h2.symm)
  rw [hlcm, Nat.totient_mul (hcop_gb'.mul_left hcop_a'b'), Nat.totient_mul hcop_ga',
    ← hga, ← hgb, Nat.totient_mul hcop_ga', Nat.totient_mul hcop_gb']
  ring

/-- For odd squarefree `n` (`Coprime n 2`), `g₂(n) * n ≤ φ(n)²`. -/
lemma g2_mul_self_le_totient_sq {n : ℕ} (hsf : Squarefree n) (hodd : Nat.Coprime n 2) :
    g₂ n * n ≤ n.totient ^ 2 := by
  have hprod_n : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
  have hphi := totient_eq_prod_sub_one_of_squarefree hsf
  have hg2 : (g₂ n : ℝ) = ∏ p ∈ n.primeFactors, ((p - 2 : ℕ) : ℝ) := by
    unfold g₂; rw [Nat.cast_prod]
  suffices hR : (g₂ n : ℝ) * (n : ℝ) ≤ (n.totient : ℝ) ^ 2 by exact_mod_cast hR
  rw [hg2, hprod_n, hphi, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun p hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    intro h2; subst h2
    exact Nat.prime_two.not_dvd_one
      ((Nat.coprime_iff_gcd_eq_one.mp hodd) ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) dvd_rfl)
  have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
  have hsub2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := Nat.cast_sub (by omega : 2 ≤ p)
  rw [hsub2]; nlinarith

/-- Elementary product inequality: if `0 ≤ a i ≤ 1` for all `i ∈ s`, then
`1 - ∏ i ∈ s, (1 - a i) ≤ ∑ i ∈ s, a i`. -/
private lemma one_sub_prod_one_sub_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∏ i ∈ s, (1 - a i) ≤ ∑ i ∈ s, a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have hx0 : 0 ≤ a x := ha0 x (Finset.mem_insert_self x s)
    have hx1 : a x ≤ 1 := ha1 x (Finset.mem_insert_self x s)
    have hih := ih (fun i hi => ha0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
    have hprod_le1 : ∏ i ∈ s, (1 - a i) ≤ 1 :=
      Finset.prod_le_one (fun i hi => by linarith [ha1 i (Finset.mem_insert_of_mem hi)])
        (fun i hi => by linarith [ha0 i (Finset.mem_insert_of_mem hi)])
    have hprod_nn : 0 ≤ ∏ i ∈ s, (1 - a i) :=
      Finset.prod_nonneg fun i hi => by linarith [ha1 i (Finset.mem_insert_of_mem hi)]
    nlinarith

/-- For squarefree `n` coprime to `W D₀` (`D₀ ≥ 6`), `1 - g₂(n) * n / φ(n)² ≤ ∑_{p ∣ n} 1 / (p - 1)²`. -/
lemma one_sub_g2_mul_div_totient_sq_le {n D₀ : ℕ} (hD : 6 ≤ D₀) (hsf : Squarefree n)
    (hcop : Nat.Coprime n (W D₀)) :
    1 - (g₂ n : ℝ) * (n : ℝ) / ((n.totient : ℝ) ^ 2) ≤
      ∑ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
  have h2W : 2 ∣ W D₀ := (prime_dvd_W_iff Nat.prime_two).mpr (by omega)
  have hodd : Nat.Coprime n 2 := hcop.coprime_dvd_right h2W
  have hprod_n : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
  have hphi : (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ) := by
    rw [totient_eq_prod_sub_one_of_squarefree hsf]
    refine Finset.prod_congr rfl fun p hp => ?_
    simpa using (Nat.cast_sub (R := ℝ) (Nat.prime_of_mem_primeFactors hp).one_le).symm
  have hg2 : (g₂ n : ℝ) = ∏ p ∈ n.primeFactors, ((p - 2 : ℕ) : ℝ) := by
    unfold g₂; push_cast; rfl
  have hratio : (g₂ n : ℝ) * (n : ℝ) / ((n.totient : ℝ) ^ 2) =
      ∏ p ∈ n.primeFactors, (1 - (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    rw [hg2, hprod_n, hphi, ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro h2; subst h2
      exact Nat.prime_two.not_dvd_one
        ((Nat.coprime_iff_gcd_eq_one.mp hodd) ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) dvd_rfl)
    have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
    have hpm1_ne : (((p - 1 : ℕ) : ℝ)) ≠ 0 := by
      have : 1 ≤ p - 1 := by omega
      exact_mod_cast (show p - 1 ≠ 0 by omega)
    have hsub1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ p)
    have hsub2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by exact_mod_cast Nat.cast_sub (by omega : 2 ≤ p)
    field_simp [hpm1_ne]
    rw [hsub1, hsub2]; ring
  rw [hratio]
  refine one_sub_prod_one_sub_le_sum n.primeFactors _ (fun p _ => by positivity) fun p hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 2 ≤ p := hp_prime.two_le
  have h1 : (1 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ p - 1 by omega)
    nlinarith
  exact inv_le_one_of_one_le₀ h1

/-- Pointwise upper bound on `|yMVar W₀ R T m r|` for `W₀ = W D₀` (`D₀ ≥ 6`):
`|yMVar (W D₀) R T m r| ≤ 2^k * T.bound * (∑ n ∈ Icc 1 ⌊R⌋₊, aPhi (W D₀) n)`. -/
lemma abs_yMVar_le {k D₀ : ℕ} (hD : 6 ≤ D₀) {R : ℝ} (hR : Real.exp 4 ≤ R)
    (T : SimplexTestFn (k + 1)) (m : Fin (k + 1)) (r : Fin (k + 1) → ℕ) :
    |yMVar (W D₀) R T m r| ≤
      (2 : ℝ) ^ k * T.bound * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi (W D₀) n) := by
  set W₀ := W D₀
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
  have hR1 : 1 ≤ R := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hR
  have h2W : 2 ∣ W₀ := (prime_dvd_W_iff Nat.prime_two).mpr (by omega)
  by_cases hrm : r ∈ validTupleSet k W₀ R ∧ r m = 1
  · obtain ⟨hrV, hrm1⟩ := hrm
    rw [yMVar_eq_sum_yVar W₀ hR1 T m r hrV hrm1]
    obtain ⟨hr1, _, hr_sf_prod, hr_cop_prod⟩ := (mem_validTupleSet hR_pos.le).mp hrV
    have hP_le1 : |∏ i ∈ Finset.univ.erase m, ((g₂ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ) ^ 2)| ≤ 1 := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun i _ => ?_
      rw [abs_of_nonneg (by positivity)]
      have hsf_i : Squarefree (r i) := (squarefree_prod_coord hr_sf_prod).1 i (Finset.mem_univ i)
      have hcop_i : Nat.Coprime (r i) W₀ :=
        hr_cop_prod.coprime_dvd_left (Finset.dvd_prod_of_mem r (Finset.mem_univ i))
      have hphi_pos : (0 : ℝ) < ((r i).totient : ℝ) ^ 2 :=
        sq_pos_of_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr (hr1 i)))
      rw [div_le_one hphi_pos]
      exact_mod_cast g2_mul_self_le_totient_sq hsf_i (hcop_i.coprime_dvd_right h2W)
    set S_sf : Finset ℕ := (Finset.Icc 1 ⌊R⌋₊).filter (fun n => Squarefree n ∧ Nat.Coprime n W₀)
    -- Map `t` injectively to `(t m, fun i : Finset.univ.erase m => t i / r i)` in `S_sf × piFinset S_sf`
    let emb : (Fin (k + 1) → ℕ) → ℕ × (↥(Finset.univ.erase m) → ℕ) :=
      fun t => (t m, fun i => t i.1 / r i.1)
    set filt := (validTupleSet k W₀ R).filter (fun t => ∀ i ∈ Finset.univ.erase m, r i ∣ t i)
    have hinj : Set.InjOn emb filt := by
      intro t₁ ht₁ t₂ ht₂ heq
      have h1 := (Finset.mem_filter.mp ht₁).2
      have h2 := (Finset.mem_filter.mp ht₂).2
      ext i
      by_cases hi : i = m
      · subst hi; exact congrArg Prod.fst heq
      · have hi' : i ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
        have hq : t₁ i / r i = t₂ i / r i := congrFun (congrArg Prod.snd heq) ⟨i, hi'⟩
        rw [← Nat.mul_div_cancel' (h1 i hi'), ← Nat.mul_div_cancel' (h2 i hi'), hq]
    have hsub : filt.image emb ⊆ S_sf ×ˢ Fintype.piFinset (fun _ : ↥(Finset.univ.erase m) => S_sf) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
      have htV := (Finset.mem_filter.mp ht).1
      have hrt := (Finset.mem_filter.mp ht).2
      obtain ⟨ht1, ht_prod, ht_sf_prod, ht_cop_prod⟩ := (mem_validTupleSet hR_pos.le).mp htV
      have ht_sf : ∀ i, Squarefree (t i) := fun i => (squarefree_prod_coord ht_sf_prod).1 i (Finset.mem_univ i)
      have ht_cop : ∀ i, Nat.Coprime (t i) W₀ := fun i =>
        ht_cop_prod.coprime_dvd_left (Finset.dvd_prod_of_mem t (Finset.mem_univ i))
      have ht_le : ∀ i, t i ≤ ⌊R⌋₊ := fun i => Nat.le_floor <|
        le_trans (by exact_mod_cast Finset.single_le_prod' (f := t) (fun j _ => ht1 j) (Finset.mem_univ i)) ht_prod
      rw [Finset.mem_product, Fintype.mem_piFinset]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht1 m, ht_le m⟩, ht_sf m, ht_cop m⟩, fun i => ?_⟩
      have hdvd : t i.1 / r i.1 ∣ t i.1 := Nat.div_dvd_of_dvd (hrt i.1 i.2)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (ht1 i.1) (hrt i.1 i.2)) (hr1 i.1),
        (Nat.div_le_self _ _).trans (ht_le i.1)⟩,
        (ht_sf i.1).squarefree_of_dvd hdvd, (ht_cop i.1).coprime_dvd_left hdvd⟩
    have hmu_le1 : ∀ n : ℕ, |(μ n : ℝ)| ≤ 1 := fun n => by
      by_cases hsf : Squarefree n
      · rw [moebius_eq_prod_neg_one_of_squarefree hsf, Finset.abs_prod]; simp
      · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
    have hsum_le : |∑ t ∈ filt, (yVar W₀ R T t / ((t m).totient : ℝ)) *
          ∏ i ∈ Finset.univ.erase m, ((μ (t i / r i) : ℝ) / (((t i / r i).totient : ℝ) ^ 2))| ≤
        (2 : ℝ) ^ k * T.bound * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) := by
      have h1d_phi2 : ∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹ ≤ 2 := by
        have hbd : ∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹ ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := by
          calc ∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹
              ≤ ∑ n ∈ S_sf, (((g₂ n : ℝ) ^ 2))⁻¹ := by
                refine Finset.sum_le_sum fun n hn => ?_
                have hsf := (Finset.mem_filter.mp hn).2.1
                have hcop := (Finset.mem_filter.mp hn).2.2
                have hgpos : (0 : ℝ) < (g₂ n : ℝ) :=
                  Nat.cast_pos.mpr (g₂_pos_of_coprime_two hsf.ne_zero (hcop.coprime_dvd_right h2W))
                exact inv_anti₀ (sq_pos_of_pos hgpos)
                  (pow_le_pow_left₀ hgpos.le (by exact_mod_cast g₂_le_totient_of_squarefree hsf) 2)
            _ ≤ 1 + 2 / ((D₀ - 2 : ℕ) : ℝ) := sum_inv_g2_sq_le hD
        have hD4 : (4 : ℝ) ≤ ((D₀ - 2 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ D₀ - 2 by omega)
        have hle1 : 2 / ((D₀ - 2 : ℕ) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      have h1d_phi : ∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹ = ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n := by
        unfold aPhi; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      have hcard_erase : Fintype.card ↥(Finset.univ.erase m) = k := by
        rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ,
          Fintype.card_fin]; omega
      calc |∑ t ∈ filt, _|
          ≤ ∑ t ∈ filt, T.bound * (((emb t).1.totient : ℝ)⁻¹ *
              ∏ i : ↥(Finset.univ.erase m), ((((emb t).2 i).totient : ℝ) ^ 2)⁻¹) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
            rw [abs_mul, abs_div, abs_of_nonneg (a := ((t m).totient : ℝ)) (Nat.cast_nonneg _), Finset.abs_prod,
              ← Finset.prod_attach (Finset.univ.erase m)]
            have hy := abs_yVar_le W₀ hR T t
            have hpr : ∏ i ∈ (Finset.univ.erase m).attach,
                  |(μ (t i.1 / r i.1) : ℝ) / (((t i.1 / r i.1).totient : ℝ) ^ 2)| ≤
                ∏ i : ↥(Finset.univ.erase m), ((((emb t).2 i).totient : ℝ) ^ 2)⁻¹ := by
              refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_
              rw [abs_div, abs_of_nonneg (a := (((t i.1 / r i.1).totient : ℝ) ^ 2)) (sq_nonneg _), div_eq_mul_inv]
              calc |(μ (t i.1 / r i.1) : ℝ)| * (((t i.1 / r i.1).totient : ℝ) ^ 2)⁻¹
                  ≤ 1 * (((t i.1 / r i.1).totient : ℝ) ^ 2)⁻¹ := by gcongr; exact hmu_le1 _
                _ = _ := one_mul _
            calc |yVar W₀ R T t| / ((t m).totient : ℝ) *
                  ∏ i ∈ (Finset.univ.erase m).attach, |(μ (t i.1 / r i.1) : ℝ) / (((t i.1 / r i.1).totient : ℝ) ^ 2)|
                ≤ (T.bound / ((t m).totient : ℝ)) *
                    ∏ i : ↥(Finset.univ.erase m), ((((emb t).2 i).totient : ℝ) ^ 2)⁻¹ := by
                  refine mul_le_mul (div_le_div_of_nonneg_right hy (Nat.cast_nonneg _)) hpr
                    (Finset.prod_nonneg fun _ _ => abs_nonneg _) (div_nonneg T.bound_nonneg (Nat.cast_nonneg _))
              _ = _ := by dsimp only [emb]; ring
        _ = T.bound * ∑ x ∈ filt.image emb,
              ((x.1.totient : ℝ)⁻¹ * ∏ i : ↥(Finset.univ.erase m), (((x.2 i).totient : ℝ) ^ 2)⁻¹) := by
            rw [← Finset.mul_sum, Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
        _ ≤ T.bound * ∑ x ∈ S_sf ×ˢ Fintype.piFinset (fun _ : ↥(Finset.univ.erase m) => S_sf),
              ((x.1.totient : ℝ)⁻¹ * ∏ i : ↥(Finset.univ.erase m), (((x.2 i).totient : ℝ) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
                mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => by positivity))
              T.bound_nonneg
        _ = T.bound * ((∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹) *
              (∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹) ^ k) := by
            rw [Finset.sum_product]
            have hsm : ∑ x ∈ S_sf, ∑ y ∈ Fintype.piFinset (fun _ : ↥(Finset.univ.erase m) => S_sf),
                  (x.totient : ℝ)⁻¹ * ∏ i : ↥(Finset.univ.erase m), (((y i).totient : ℝ) ^ 2)⁻¹ =
                (∑ x ∈ S_sf, (x.totient : ℝ)⁻¹) *
                  ∑ y ∈ Fintype.piFinset (fun _ : ↥(Finset.univ.erase m) => S_sf),
                    ∏ i : ↥(Finset.univ.erase m), (((y i).totient : ℝ) ^ 2)⁻¹ :=
              (Finset.sum_mul_sum _ _ _ _).symm
            rw [hsm,
              sum_piFinset_prod (fun _ : ↥(Finset.univ.erase m) => S_sf)
                (fun _ n => (((n.totient : ℝ) ^ 2))⁻¹),
              Finset.prod_const, Finset.card_univ, hcard_erase]
        _ ≤ T.bound * ((∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) * (2 : ℝ) ^ k) := by
            rw [h1d_phi]
            have hpow : (∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹) ^ k ≤ (2 : ℝ) ^ k :=
              pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) h1d_phi2 k
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpow (Finset.sum_nonneg fun _ _ => aPhi_nonneg _ _))
              T.bound_nonneg
        _ = (2 : ℝ) ^ k * T.bound * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) := by ring
    rw [abs_mul]
    calc |∏ i ∈ Finset.univ.erase m, ((g₂ (r i) : ℝ) * (r i : ℝ) / ((r i).totient : ℝ) ^ 2)| *
          |∑ t ∈ filt, _|
        ≤ 1 * ((2 : ℝ) ^ k * T.bound * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n)) :=
          mul_le_mul hP_le1 hsum_le (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  · unfold yMVar; rw [if_neg hrm, abs_zero]
    exact mul_nonneg (mul_nonneg (by positivity) T.bound_nonneg)
      (Finset.sum_nonneg fun _ _ => aPhi_nonneg _ _)

/-- **Diagonalization Lower Bound for `Q1Sum`** (Maynard 2015 Lemma 5.2):
for `D₀ ≥ 6`, `R ≥ exp 4`, `T : SimplexTestFn (k + 1)`, `m : Fin (k + 1)`:
`Q1Sum (W D₀) R T m ≥ ∑_{u ∈ V, u m = 1} (yMVar m u)² / ∏_{i ≠ m} g₂(u i) -
  8^k * T.bound² * (∑ aPhi)^{k + 2} * ((1 + 2 / (D₀ - 2))^{k * (k - 1)} - 1)`. -/
theorem Q1Sum_diag_lower {k D₀ : ℕ} (hD : 6 ≤ D₀) {R : ℝ} (hR : Real.exp 4 ≤ R)
    (T : SimplexTestFn (k + 1)) (m : Fin (k + 1)) :
    (∑ u ∈ (validTupleSet k (W D₀) R).filter (fun u => u m = 1),
        (yMVar (W D₀) R T m u) ^ 2 / (∏ i ∈ Finset.univ.erase m, (g₂ (u i) : ℝ))) -
      (8 : ℝ) ^ k * T.bound ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi (W D₀) n) ^ (k + 2) *
        ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1) ≤
      Q1Sum (W D₀) R T m := by
  set W₀ := W D₀
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
  have hR1 : 1 ≤ R := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hR
  have h2W : 2 ∣ W₀ := (prime_dvd_W_iff Nat.prime_two).mpr (by omega)
  set Vm := (validTupleSet k W₀ R).filter (fun d => d m = 1)
  set Em : Finset (Fin (k + 1)) := Finset.univ.erase m
  have hEm_card : Em.card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]; omega
  set S_sf : Finset ℕ := (Finset.Icc 1 ⌊R⌋₊).filter (fun n => Squarefree n ∧ Nat.Coprime n W₀)
  set offDm : Finset (Fin (k + 1) × Fin (k + 1)) := Em.offDiag
  have hoffDm_card : offDm.card = k * (k - 1) := by
    rw [Finset.offDiag_card, hEm_card]
    rcases k with _ | k'
    · simp
    · simp only [Nat.add_sub_cancel]
      have h1 : (k' + 1) * (k' + 1) = (k' + 1) * k' + (k' + 1) := by ring
      omega
  set Uset : Finset (↥Em → ℕ) := Fintype.piFinset (fun _ : ↥Em => S_sf)
  set Sset : Finset (↥offDm → ℕ) := Fintype.piFinset (fun _ : ↥offDm => S_sf)
  let mkA : (↥Em → ℕ) → (↥offDm → ℕ) → Fin (k + 1) → ℕ := fun u s i =>
    if hi : i ∈ Em then
      Nat.lcm (u ⟨i, hi⟩) (Finset.lcm (Em.erase i) (fun j => if h : (i, j) ∈ offDm then s ⟨(i, j), h⟩ else 1))
    else 1
  let mkB : (↥Em → ℕ) → (↥offDm → ℕ) → Fin (k + 1) → ℕ := fun u s i =>
    if hi : i ∈ Em then
      Nat.lcm (u ⟨i, hi⟩) (Finset.lcm (Em.erase i) (fun j => if h : (j, i) ∈ offDm then s ⟨(j, i), h⟩ else 1))
    else 1
  -- Helper: expressing `∑_{d ∈ Vm, ∀ i, r i ∣ d i} lamVar d / ∏_{i ∈ Em} φ(d i)` via `yMVar`
  have hsum_lam_m : ∀ r : Fin (k + 1) → ℕ, r m = 1 →
      ∑ d ∈ Vm.filter (fun d => ∀ i, r i ∣ d i),
          lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ)) =
        (∏ i ∈ Em, (μ (r i) : ℝ)) * yMVar W₀ R T m r / (∏ i ∈ Em, (g₂ (r i) : ℝ)) := by
    intro r hrm
    by_cases hrV : r ∈ validTupleSet k W₀ R
    · have hfeq : Vm.filter (fun d => ∀ i, r i ∣ d i) =
          (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i) := by
        ext d; simp [Vm, and_assoc]
      rw [hfeq]
      obtain ⟨hr1, _, hr_sf_prod, hr_cop_prod⟩ := (mem_validTupleSet hR_pos.le).mp hrV
      unfold yMVar; rw [if_pos ⟨hrV, hrm⟩]
      have hg2_pos : ∏ i ∈ Em, (g₂ (r i) : ℝ) ≠ 0 :=
        (Finset.prod_pos fun i _ => Nat.cast_pos.mpr
          (g₂_pos_of_coprime_two ((squarefree_prod_coord hr_sf_prod).1 i (Finset.mem_univ i)).ne_zero
            ((hr_cop_prod.coprime_dvd_left (Finset.dvd_prod_of_mem r (Finset.mem_univ i))).coprime_dvd_right h2W))).ne'
      have hmu_sq : (∏ i ∈ Em, (μ (r i) : ℝ)) * (∏ i ∈ Em, (μ (r i) : ℝ)) = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [moebius_eq_prod_neg_one_of_squarefree ((squarefree_prod_coord hr_sf_prod).1 i (Finset.mem_univ i)),
          ← Finset.prod_mul_distrib]
        simp
      rw [Finset.prod_mul_distrib]
      calc ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i),
              lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))
          = 1 * (∑ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i),
              lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
              ((∏ i ∈ Em, (g₂ (r i) : ℝ)) / (∏ i ∈ Em, (g₂ (r i) : ℝ))) := by
            rw [div_self hg2_pos, one_mul, mul_one]
        _ = (∏ i ∈ Em, (μ (r i) : ℝ)) *
              ((∏ i ∈ Em, (μ (r i) : ℝ)) * (∏ i ∈ Em, (g₂ (r i) : ℝ)) *
                ∑ d ∈ (validTupleSet k W₀ R).filter (fun d => d m = 1 ∧ ∀ i, r i ∣ d i),
                  lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) /
              (∏ i ∈ Em, (g₂ (r i) : ℝ)) := by
            rw [← hmu_sq]; ring
    · unfold yMVar; rw [if_neg (fun h => hrV h.1), mul_zero, zero_div]
      refine Finset.sum_eq_zero fun d hd => ?_
      exfalso
      have hdV : d ∈ validTupleSet k W₀ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1
      have hrd : ∀ i, r i ∣ d i := (Finset.mem_filter.mp hd).2
      have hd1 : ∀ i, 1 ≤ d i := ((mem_validTupleSet hR_pos.le).mp hdV).1
      exact hrV (validTupleSet_of_dvd hR_pos.le hdV (fun i => Nat.pos_of_dvd_of_pos (hrd i) (hd1 i)) hrd)
  -- Step 1: Exact diagonalization of `Q1Sum`
  have hdiag : Q1Sum W₀ R T m =
      ∑ u ∈ Uset, ∑ s ∈ Sset,
        (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
          ((∏ i ∈ Em, (μ (mkA u s i) : ℝ)) * yMVar W₀ R T m (mkA u s) / (∏ i ∈ Em, (g₂ (mkA u s i) : ℝ))) *
          ((∏ i ∈ Em, (μ (mkB u s i) : ℝ)) * yMVar W₀ R T m (mkB u s) / (∏ i ∈ Em, (g₂ (mkB u s i) : ℝ))) := by
    have hterm_de : ∀ d ∈ Vm, ∀ e ∈ Vm,
        (if PairwiseCoprimeCross d e then
          lamVar W₀ R T d * lamVar W₀ R T e / (∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ))
        else 0) =
        ∑ u ∈ Uset, ∑ s ∈ Sset,
          if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
            (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
              (lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
              (lamVar W₀ R T e / (∏ i ∈ Em, ((e i).totient : ℝ)))
          else 0 := by
      intro d hd e he
      have hdV := (Finset.mem_filter.mp hd).1
      have hdm := (Finset.mem_filter.mp hd).2
      have heV := (Finset.mem_filter.mp he).1
      have hem := (Finset.mem_filter.mp he).2
      obtain ⟨hd1, hd_prod, hd_sf, hd_cop⟩ := (mem_validTupleSet hR_pos.le).mp hdV
      obtain ⟨he1, _, he_sf, _⟩ := (mem_validTupleSet hR_pos.le).mp heV
      have hd_sf_i : ∀ i, Squarefree (d i) := fun i => (squarefree_prod_coord hd_sf).1 i (Finset.mem_univ i)
      have he_sf_i : ∀ i, Squarefree (e i) := fun i => (squarefree_prod_coord he_sf).1 i (Finset.mem_univ i)
      have hd_cop_i : ∀ i, Nat.Coprime (d i) W₀ := fun i =>
        hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
      have hd_le_R : ∀ i, d i ≤ ⌊R⌋₊ := fun i => Nat.le_floor <|
        le_trans (by exact_mod_cast Finset.single_le_prod' (f := d) (fun j _ => hd1 j) (Finset.mem_univ i)) hd_prod
      -- (1) Cross-coprimality indicator on `offDm` (since `d m = e m = 1`)
      have hcross : (if PairwiseCoprimeCross d e then (1 : ℝ) else 0) =
          ∑ s ∈ Sset, (if ∀ p : ↥offDm, s p ∣ d p.1.1 ∧ s p ∣ e p.1.2 then ∏ p : ↥offDm, (μ (s p) : ℝ) else 0) := by
        have h1 : (if PairwiseCoprimeCross d e then (1 : ℝ) else 0) =
            ∏ p : ↥offDm, ∑ x ∈ (Nat.gcd (d p.1.1) (e p.1.2)).divisors, (μ x : ℝ) := by
          have hfac : ∀ p : ↥offDm,
              ∑ x ∈ (Nat.gcd (d p.1.1) (e p.1.2)).divisors, (μ x : ℝ) =
                if Nat.Coprime (d p.1.1) (e p.1.2) then 1 else 0 := fun p =>
            sum_moebius_divisors_of_squarefree ((hd_sf_i p.1.1).squarefree_of_dvd (Nat.gcd_dvd_left _ _))
          rw [Finset.prod_congr rfl fun p _ => hfac p]
          by_cases hpc : PairwiseCoprimeCross d e
          · rw [if_pos hpc]
            exact (Finset.prod_eq_one fun p _ => by
              rw [if_pos (hpc p.1.1 p.1.2 (Finset.mem_offDiag.mp p.2).2.2)]).symm
          · rw [if_neg hpc]
            unfold PairwiseCoprimeCross at hpc; push Not at hpc
            obtain ⟨i, j, hij, hnc⟩ := hpc
            have him : i ≠ m := fun h => hnc (by rw [h, hdm]; exact Nat.coprime_one_left _)
            have hjm : j ≠ m := fun h => hnc (by rw [h, hem]; exact Nat.coprime_one_right _)
            have hp : (i, j) ∈ offDm := Finset.mem_offDiag.mpr
              ⟨Finset.mem_erase.mpr ⟨him, Finset.mem_univ i⟩,
               Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩, hij⟩
            exact (Finset.prod_eq_zero (Finset.mem_univ (⟨(i, j), hp⟩ : ↥offDm)) (by rw [if_neg hnc])).symm
        rw [h1, ← sum_piFinset_prod, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext s
        simp only [Sset, Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors, S_sf, Finset.mem_Icc]
        constructor
        · intro hs
          refine ⟨fun p => ?_, fun p => Nat.dvd_gcd_iff.mp (hs p).1⟩
          have hdvd_d : s p ∣ d p.1.1 := dvd_trans (hs p).1 (Nat.gcd_dvd_left _ _)
          exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd_d (hd1 p.1.1),
            (Nat.le_of_dvd (hd1 p.1.1) hdvd_d).trans (hd_le_R p.1.1)⟩,
            (hd_sf_i p.1.1).squarefree_of_dvd hdvd_d,
            (hd_cop_i p.1.1).coprime_dvd_left hdvd_d⟩
        · rintro ⟨_, hdvd⟩ p
          exact ⟨Nat.dvd_gcd (hdvd p).1 (hdvd p).2, (Nat.gcd_pos_of_pos_left _ (hd1 p.1.1)).ne'⟩
      -- (2) Expansion of `∏_{i ∈ Em} φ(gcd(d i, e i))` via `∑_{u ∣ gcd} g₂(u)`
      have hgcd_prod : ∏ i ∈ Em, ((Nat.gcd (d i) (e i)).totient : ℝ) =
          ∑ u ∈ Uset, if ∀ i : ↥Em, u i ∣ d i.1 ∧ u i ∣ e i.1 then ∏ i : ↥Em, (g₂ (u i) : ℝ) else 0 := by
        have h1 : ∏ i ∈ Em, ((Nat.gcd (d i) (e i)).totient : ℝ) =
            ∏ i : ↥Em, ∑ x ∈ (Nat.gcd (d i.1) (e i.1)).divisors, (g₂ x : ℝ) := by
          rw [← Finset.prod_attach Em]
          refine Finset.prod_congr rfl fun i _ => ?_
          exact (sum_g2_divisors_eq_totient
            ((hd_sf_i i.1).squarefree_of_dvd (Nat.gcd_dvd_left _ _))
            (((hd_cop_i i.1).coprime_dvd_left (Nat.gcd_dvd_left _ _)).coprime_dvd_right h2W)).symm
        rw [h1, ← sum_piFinset_prod, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext u
        simp only [Uset, Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors, S_sf, Finset.mem_Icc]
        constructor
        · intro hu
          refine ⟨fun i => ?_, fun i => Nat.dvd_gcd_iff.mp (hu i).1⟩
          have hdvd_d : u i ∣ d i.1 := dvd_trans (hu i).1 (Nat.gcd_dvd_left _ _)
          exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd_d (hd1 i.1),
            (Nat.le_of_dvd (hd1 i.1) hdvd_d).trans (hd_le_R i.1)⟩,
            (hd_sf_i i.1).squarefree_of_dvd hdvd_d,
            (hd_cop_i i.1).coprime_dvd_left hdvd_d⟩
        · rintro ⟨_, hdvd⟩ i
          exact ⟨Nat.dvd_gcd (hdvd i).1 (hdvd i).2, (Nat.gcd_pos_of_pos_left _ (hd1 i.1)).ne'⟩
      -- (3) `1 / ∏_{i ∈ Em} φ(lcm(d i, e i)) = (∏_{i ∈ Em} φ(gcd(d i, e i))) / ((∏ φ(d i)) * (∏ φ(e i)))`
      have hlcm_eq : (1 : ℝ) / (∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ)) =
          (∏ i ∈ Em, ((Nat.gcd (d i) (e i)).totient : ℝ)) /
            ((∏ i ∈ Em, ((d i).totient : ℝ)) * (∏ i ∈ Em, ((e i).totient : ℝ))) := by
        have hlcm_ne : (∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ)) ≠ 0 :=
          (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.lcm_pos (hd1 i) (he1 i)))).ne'
        have hde_ne : (∏ i ∈ Em, ((d i).totient : ℝ)) * (∏ i ∈ Em, ((e i).totient : ℝ)) ≠ 0 :=
          mul_ne_zero (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.totient_pos.mpr (hd1 i))).ne'
            (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.totient_pos.mpr (he1 i))).ne'
        rw [div_eq_div_iff hlcm_ne hde_ne, one_mul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        have h : ((Nat.gcd (d i) (e i)).totient : ℝ) * ((Nat.lcm (d i) (e i)).totient : ℝ) =
            ((d i).totient : ℝ) * ((e i).totient : ℝ) := by
          exact_mod_cast totient_gcd_mul_totient_lcm (hd_sf_i i) (he_sf_i i)
        linarith
      -- (4) Equivalence of divisibility conditions with `mkA` and `mkB`
      have hdvd_iff : ∀ u ∈ Uset, ∀ s ∈ Sset,
          ((∀ i : ↥Em, u i ∣ d i.1 ∧ u i ∣ e i.1) ∧ (∀ p : ↥offDm, s p ∣ d p.1.1 ∧ s p ∣ e p.1.2)) ↔
          ((∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i)) := by
        intro u _ s _
        constructor
        · rintro ⟨hu, hs⟩
          refine ⟨fun i => ?_, fun i => ?_⟩
          · dsimp only [mkA]; split_ifs with hi
            · refine Nat.lcm_dvd (hu ⟨i, hi⟩).1 (Finset.lcm_dvd fun j hj => ?_)
              have hij : (i, j) ∈ offDm :=
                Finset.mem_offDiag.mpr ⟨hi, (Finset.mem_erase.mp hj).2, (Finset.mem_erase.mp hj).1.symm⟩
              rw [dif_pos hij]; exact (hs ⟨(i, j), hij⟩).1
            · exact one_dvd _
          · dsimp only [mkB]; split_ifs with hi
            · refine Nat.lcm_dvd (hu ⟨i, hi⟩).2 (Finset.lcm_dvd fun j hj => ?_)
              have hji : (j, i) ∈ offDm :=
                Finset.mem_offDiag.mpr ⟨(Finset.mem_erase.mp hj).2, hi, (Finset.mem_erase.mp hj).1⟩
              rw [dif_pos hji]; exact (hs ⟨(j, i), hji⟩).2
            · exact one_dvd _
        · rintro ⟨hA, hB⟩
          refine ⟨fun i => ?_, fun p => ?_⟩
          · have hAi := hA i.1; have hBi := hB i.1
            dsimp only [mkA, mkB] at hAi hBi; rw [dif_pos i.2] at hAi hBi
            exact ⟨dvd_trans (Nat.dvd_lcm_left _ _) hAi, dvd_trans (Nat.dvd_lcm_left _ _) hBi⟩
          · obtain ⟨hp1, hp2, hne⟩ := Finset.mem_offDiag.mp p.2
            have hj1 : p.1.2 ∈ Em.erase p.1.1 := Finset.mem_erase.mpr ⟨hne.symm, hp2⟩
            have hj2 : p.1.1 ∈ Em.erase p.1.2 := Finset.mem_erase.mpr ⟨hne, hp1⟩
            have hAi := hA p.1.1; have hBi := hB p.1.2
            dsimp only [mkA] at hAi; rw [dif_pos hp1] at hAi
            dsimp only [mkB] at hBi; rw [dif_pos hp2] at hBi
            have h1 : s p ∣ Finset.lcm (Em.erase p.1.1)
                (fun j => if h : (p.1.1, j) ∈ offDm then s ⟨(p.1.1, j), h⟩ else 1) := by
              have := Finset.dvd_lcm (f := fun j => if h : (p.1.1, j) ∈ offDm then s ⟨(p.1.1, j), h⟩ else 1) hj1
              simpa only [dif_pos p.2] using this
            have h2 : s p ∣ Finset.lcm (Em.erase p.1.2)
                (fun j => if h : (j, p.1.2) ∈ offDm then s ⟨(j, p.1.2), h⟩ else 1) := by
              have := Finset.dvd_lcm (f := fun j => if h : (j, p.1.2) ∈ offDm then s ⟨(j, p.1.2), h⟩ else 1) hj2
              simpa only [dif_pos p.2] using this
            exact ⟨dvd_trans (dvd_trans h1 (Nat.dvd_lcm_right _ _)) hAi,
              dvd_trans (dvd_trans h2 (Nat.dvd_lcm_right _ _)) hBi⟩
      have hcomb : (if PairwiseCoprimeCross d e then
            lamVar W₀ R T d * lamVar W₀ R T e / (∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ)) else 0) =
          (if PairwiseCoprimeCross d e then (1 : ℝ) else 0) * (∏ i ∈ Em, ((Nat.gcd (d i) (e i)).totient : ℝ)) *
            (lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
            (lamVar W₀ R T e / (∏ i ∈ Em, ((e i).totient : ℝ))) := by
        split_ifs
        · calc lamVar W₀ R T d * lamVar W₀ R T e / (∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ))
              = lamVar W₀ R T d * lamVar W₀ R T e * ((1 : ℝ) / (∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ))) := by ring
            _ = lamVar W₀ R T d * lamVar W₀ R T e *
                  ((∏ i ∈ Em, ((Nat.gcd (d i) (e i)).totient : ℝ)) /
                    ((∏ i ∈ Em, ((d i).totient : ℝ)) * (∏ i ∈ Em, ((e i).totient : ℝ)))) := by rw [hlcm_eq]
            _ = _ := by ring
        · ring
      rw [hcomb, hcross, hgcd_prod, Finset.sum_mul_sum]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun s hs => ?_
      by_cases h1 : ∀ p : ↥offDm, s p ∣ d p.1.1 ∧ s p ∣ e p.1.2
      · by_cases h2 : ∀ i : ↥Em, u i ∣ d i.1 ∧ u i ∣ e i.1
        · rw [if_pos h1, if_pos h2, if_pos ((hdvd_iff u hu s hs).mp ⟨h2, h1⟩)]; ring
        · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 ((hdvd_iff u hu s hs).mpr h).1)]; ring
      · rw [if_neg h1, if_neg (fun h => h1 ((hdvd_iff u hu s hs).mpr h).2)]; ring
    unfold Q1Sum
    have h1 : ∑ d ∈ Vm, ∑ e ∈ Vm,
          (if PairwiseCoprimeCross d e then
            lamVar W₀ R T d * lamVar W₀ R T e / (∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ)) else 0) =
        ∑ d ∈ Vm, ∑ e ∈ Vm, ∑ u ∈ Uset, ∑ s ∈ Sset,
          if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
            (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
              (lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
              (lamVar W₀ R T e / (∏ i ∈ Em, ((e i).totient : ℝ)))
          else 0 :=
      Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => hterm_de d hd e he
    rw [h1]
    calc ∑ d ∈ Vm, ∑ e ∈ Vm, ∑ u ∈ Uset, ∑ s ∈ Sset,
            (if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
              (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
                (lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
                (lamVar W₀ R T e / (∏ i ∈ Em, ((e i).totient : ℝ)))
            else 0)
        = ∑ d ∈ Vm, ∑ u ∈ Uset, ∑ s ∈ Sset, ∑ e ∈ Vm,
            (if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
              (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
                (lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
                (lamVar W₀ R T e / (∏ i ∈ Em, ((e i).totient : ℝ)))
            else 0) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ u ∈ Uset, ∑ s ∈ Sset, ∑ d ∈ Vm, ∑ e ∈ Vm,
            (if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
              (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
                (lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
                (lamVar W₀ R T e / (∏ i ∈ Em, ((e i).totient : ℝ)))
            else 0) := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun s _ => ?_
          have hfact : ∑ d ∈ Vm, ∑ e ∈ Vm,
                (if (∀ i, mkA u s i ∣ d i) ∧ (∀ i, mkB u s i ∣ e i) then
                  (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
                    (lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
                    (lamVar W₀ R T e / (∏ i ∈ Em, ((e i).totient : ℝ)))
                else 0) =
              (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
                (∑ d ∈ Vm.filter (fun d => ∀ i, mkA u s i ∣ d i),
                  lamVar W₀ R T d / (∏ i ∈ Em, ((d i).totient : ℝ))) *
                (∑ e ∈ Vm.filter (fun e => ∀ i, mkB u s i ∣ e i),
                  lamVar W₀ R T e / (∏ i ∈ Em, ((e i).totient : ℝ))) := by
            rw [Finset.sum_filter (s := Vm), Finset.sum_filter (s := Vm), mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => ?_
            by_cases hd : ∀ i, mkA u s i ∣ d i
            · by_cases he : ∀ i, mkB u s i ∣ e i
              · rw [if_pos ⟨hd, he⟩, if_pos hd, if_pos he]; ring
              · rw [if_neg (fun h => he h.2), if_pos hd, if_neg he]; ring
            · rw [if_neg (fun h => hd h.1), if_neg hd]; ring
          have hmA : mkA u s m = 1 := by simp [mkA, Em]
          have hmB : mkB u s m = 1 := by simp [mkB, Em]
          rw [hfact, hsum_lam_m (mkA u s) hmA, hsum_lam_m (mkB u s) hmB]
  rw [hdiag]
  -- Step 2: Split `Sset` into `s1 := fun _ => 1` vs `Sset.erase s1`
  let s1 : ↥offDm → ℕ := fun _ => 1
  have hs1_mem : s1 ∈ Sset := by
    rw [Fintype.mem_piFinset]; intro _
    simp only [S_sf, Finset.mem_filter, Finset.mem_Icc, s1]
    exact ⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast hR1)⟩, squarefree_one, Nat.coprime_one_left _⟩
  rw [Finset.sum_comm, ← Finset.add_sum_erase Sset _ hs1_mem]
  -- Evaluate `s = s1` main term
  let extU : (↥Em → ℕ) → (Fin (k + 1) → ℕ) := fun u i => if hi : i ∈ Em then u ⟨i, hi⟩ else 1
  have hmk_s1 : ∀ u : ↥Em → ℕ, mkA u s1 = extU u ∧ mkB u s1 = extU u := fun u => by
    have hl1 : ∀ i, (Em.erase i).lcm (fun _ => 1) = 1 := fun i =>
      Nat.dvd_one.mp (Finset.lcm_dvd fun _ _ => dvd_rfl)
    constructor <;> (ext i; dsimp only [mkA, mkB, extU, s1]; split_ifs with hi <;> simp [hl1])
  have hmain : ∑ u ∈ Uset,
        (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s1 p) : ℝ)) *
          ((∏ i ∈ Em, (μ (mkA u s1 i) : ℝ)) * yMVar W₀ R T m (mkA u s1) / (∏ i ∈ Em, (g₂ (mkA u s1 i) : ℝ))) *
          ((∏ i ∈ Em, (μ (mkB u s1 i) : ℝ)) * yMVar W₀ R T m (mkB u s1) / (∏ i ∈ Em, (g₂ (mkB u s1 i) : ℝ))) =
      ∑ u ∈ Vm, (yMVar W₀ R T m u) ^ 2 / (∏ i ∈ Em, (g₂ (u i) : ℝ)) := by
    have hterm : ∀ u ∈ Uset,
        (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s1 p) : ℝ)) *
          ((∏ i ∈ Em, (μ (mkA u s1 i) : ℝ)) * yMVar W₀ R T m (mkA u s1) / (∏ i ∈ Em, (g₂ (mkA u s1 i) : ℝ))) *
          ((∏ i ∈ Em, (μ (mkB u s1 i) : ℝ)) * yMVar W₀ R T m (mkB u s1) / (∏ i ∈ Em, (g₂ (mkB u s1 i) : ℝ))) =
        (yMVar W₀ R T m (extU u)) ^ 2 / (∏ i ∈ Em, (g₂ (extU u i) : ℝ)) := by
      intro u hu
      rw [(hmk_s1 u).1, (hmk_s1 u).2]
      have hs1_mu : ∏ p : ↥offDm, (μ (s1 p) : ℝ) = 1 := by simp [s1]
      have hmu_sq : (∏ i ∈ Em, (μ (extU u i) : ℝ)) * (∏ i ∈ Em, (μ (extU u i) : ℝ)) = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun i hi => ?_
        have hsf_i : Squarefree (extU u i) := by
          dsimp only [extU]; rw [dif_pos hi]
          exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu ⟨i, hi⟩)).2.1
        rw [moebius_eq_prod_neg_one_of_squarefree hsf_i, ← Finset.prod_mul_distrib]; simp
      have hg2_eq : ∏ i : ↥Em, (g₂ (u i) : ℝ) = ∏ i ∈ Em, (g₂ (extU u i) : ℝ) := by
        rw [← Finset.prod_attach Em]
        refine Finset.prod_congr rfl fun i _ => by simp [extU, i.2]
      have hg2_ne : ∏ i ∈ Em, (g₂ (extU u i) : ℝ) ≠ 0 :=
        (Finset.prod_pos fun i hi => by
          dsimp only [extU]; rw [dif_pos hi]
          have hmem := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu ⟨i, hi⟩)
          exact Nat.cast_pos.mpr (g₂_pos_of_coprime_two hmem.2.1.ne_zero (hmem.2.2.coprime_dvd_right h2W))).ne'
      rw [hs1_mu, hg2_eq, mul_one]
      have h1 : (∏ i ∈ Em, (g₂ (extU u i) : ℝ)) *
            ((∏ i ∈ Em, (μ (extU u i) : ℝ)) * yMVar W₀ R T m (extU u) / (∏ i ∈ Em, (g₂ (extU u i) : ℝ))) *
            ((∏ i ∈ Em, (μ (extU u i) : ℝ)) * yMVar W₀ R T m (extU u) / (∏ i ∈ Em, (g₂ (extU u i) : ℝ))) =
          ((∏ i ∈ Em, (μ (extU u i) : ℝ)) * (∏ i ∈ Em, (μ (extU u i) : ℝ))) *
            (yMVar W₀ R T m (extU u)) ^ 2 / (∏ i ∈ Em, (g₂ (extU u i) : ℝ)) *
            ((∏ i ∈ Em, (g₂ (extU u i) : ℝ)) / (∏ i ∈ Em, (g₂ (extU u i) : ℝ))) := by ring
      rw [h1, hmu_sq, div_self hg2_ne, one_mul, mul_one]
    rw [Finset.sum_congr rfl hterm]
    symm
    refine Finset.sum_bij_ne_zero (fun v _ _ => fun i : ↥Em => v i.1) ?_ ?_ ?_ ?_
    · intro v hv _
      have hvV := (Finset.mem_filter.mp hv).1
      obtain ⟨hv1, hv_prod, hv_sf, hv_cop⟩ := (mem_validTupleSet hR_pos.le).mp hvV
      rw [Fintype.mem_piFinset]; intro i
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hv1 i.1, Nat.le_floor <|
        le_trans (by exact_mod_cast Finset.single_le_prod' (f := v) (fun j _ => hv1 j) (Finset.mem_univ i.1)) hv_prod⟩,
        (squarefree_prod_coord hv_sf).1 i.1 (Finset.mem_univ i.1),
        hv_cop.coprime_dvd_left (Finset.dvd_prod_of_mem v (Finset.mem_univ i.1))⟩
    · intro v₁ hv₁ _ v₂ hv₂ _ heq
      have h1m := (Finset.mem_filter.mp hv₁).2
      have h2m := (Finset.mem_filter.mp hv₂).2
      ext i
      by_cases hi : i = m
      · rw [hi, h1m, h2m]
      · exact congrFun heq ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩
    · intro u hu hne
      have hmemV : extU u ∈ Vm := by
        by_contra hnot
        have : yMVar W₀ R T m (extU u) = 0 := by
          unfold yMVar; rw [if_neg (fun h => hnot (Finset.mem_filter.mpr h))]
        exact hne (by simp [this])
      refine ⟨extU u, hmemV, hne, ?_⟩
      ext i; simp [extU, i.2]
    · intro v hv _
      have hvm := (Finset.mem_filter.mp hv).2
      have heqv : extU (fun i : ↥Em => v i.1) = v := by
        ext i; dsimp only [extU]; split_ifs with hi
        · rfl
        · have : i = m := by by_contra hne; exact hi (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)
          rw [this, hvm]
      rw [heqv]
  rw [hmain]
  -- Step 3: Bound `|∑_{s ∈ Sset.erase s1} ∑_{u ∈ Uset} ...|`
  set yM_max : ℝ := (2 : ℝ) ^ k * T.bound * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n)
  have hyM_max_nn : 0 ≤ yM_max := by
    dsimp only [yM_max]
    exact mul_nonneg (mul_nonneg (by positivity) T.bound_nonneg)
      (Finset.sum_nonneg fun _ _ => aPhi_nonneg _ _)
  have hterm_s : ∀ s ∈ Sset.erase s1, ∀ u ∈ Uset,
      |(∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
        ((∏ i ∈ Em, (μ (mkA u s i) : ℝ)) * yMVar W₀ R T m (mkA u s) / (∏ i ∈ Em, (g₂ (mkA u s i) : ℝ))) *
        ((∏ i ∈ Em, (μ (mkB u s i) : ℝ)) * yMVar W₀ R T m (mkB u s) / (∏ i ∈ Em, (g₂ (mkB u s i) : ℝ)))| ≤
      yM_max ^ 2 * (∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹) * (∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹) := by
    intro s hs u hu
    by_cases hAB : mkA u s ∈ validTupleSet k W₀ R ∧ mkB u s ∈ validTupleSet k W₀ R
    · obtain ⟨hAV, hBV⟩ := hAB
      have hA_cop := (squarefree_prod_coord ((mem_validTupleSet hR_pos.le).mp hAV).2.2.1).2
      have hB_cop := (squarefree_prod_coord ((mem_validTupleSet hR_pos.le).mp hBV).2.2.1).2
      have hg2_A : ∀ (i : Fin (k + 1)) (hi : i ∈ Em), (g₂ (mkA u s i) : ℝ) =
          (g₂ (u ⟨i, hi⟩) : ℝ) * ∏ j ∈ Em.erase i,
            (g₂ (if h : (i, j) ∈ offDm then s ⟨(i, j), h⟩ else 1) : ℝ) := fun i hi => by
        have hcop_pair : ∀ j₁ ∈ Em.erase i, ∀ j₂ ∈ Em.erase i, j₁ ≠ j₂ →
            Nat.Coprime (if h : (i, j₁) ∈ offDm then s ⟨(i, j₁), h⟩ else 1)
              (if h : (i, j₂) ∈ offDm then s ⟨(i, j₂), h⟩ else 1) := by
          intro j₁ hj₁ j₂ hj₂ hne
          have h1 : (i, j₁) ∈ offDm := Finset.mem_offDiag.mpr ⟨hi, (Finset.mem_erase.mp hj₁).2, (Finset.mem_erase.mp hj₁).1.symm⟩
          have h2 : (i, j₂) ∈ offDm := Finset.mem_offDiag.mpr ⟨hi, (Finset.mem_erase.mp hj₂).2, (Finset.mem_erase.mp hj₂).1.symm⟩
          rw [dif_pos h1, dif_pos h2]
          have hd1 : s ⟨(i, j₁), h1⟩ ∣ mkB u s j₁ := by
            dsimp only [mkB]; rw [dif_pos (Finset.mem_erase.mp hj₁).2]
            have := Finset.dvd_lcm (f := fun r => if h : (r, j₁) ∈ offDm then s ⟨(r, j₁), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj₁).1.symm, hi⟩)
            rw [dif_pos h1] at this; exact dvd_trans this (Nat.dvd_lcm_right _ _)
          have hd2 : s ⟨(i, j₂), h2⟩ ∣ mkB u s j₂ := by
            dsimp only [mkB]; rw [dif_pos (Finset.mem_erase.mp hj₂).2]
            have := Finset.dvd_lcm (f := fun r => if h : (r, j₂) ∈ offDm then s ⟨(r, j₂), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj₂).1.symm, hi⟩)
            rw [dif_pos h2] at this; exact dvd_trans this (Nat.dvd_lcm_right _ _)
          exact (hB_cop j₁ (Finset.mem_univ j₁) j₂ (Finset.mem_univ j₂) hne).coprime_dvd_left hd1
            |>.coprime_dvd_right hd2
        have hlcm_eq := finset_lcm_eq_prod_of_pairwise_coprime (Em.erase i) _ hcop_pair
        have hucop : Nat.Coprime (u ⟨i, hi⟩) (∏ j ∈ Em.erase i,
            if h : (i, j) ∈ offDm then s ⟨(i, j), h⟩ else 1) := by
          refine Nat.Coprime.prod_right fun j hj => ?_
          have h1 : (i, j) ∈ offDm := Finset.mem_offDiag.mpr ⟨hi, (Finset.mem_erase.mp hj).2, (Finset.mem_erase.mp hj).1.symm⟩
          rw [dif_pos h1]
          have hd_u : u ⟨i, hi⟩ ∣ mkB u s i := by dsimp only [mkB]; rw [dif_pos hi]; exact Nat.dvd_lcm_left _ _
          have hd_s : s ⟨(i, j), h1⟩ ∣ mkB u s j := by
            dsimp only [mkB]; rw [dif_pos (Finset.mem_erase.mp hj).2]
            have := Finset.dvd_lcm (f := fun r => if h : (r, j) ∈ offDm then s ⟨(r, j), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1.symm, hi⟩)
            rw [dif_pos h1] at this; exact dvd_trans this (Nat.dvd_lcm_right _ _)
          exact (hB_cop i (Finset.mem_univ i) j (Finset.mem_univ j) (Finset.mem_erase.mp hj).1.symm).coprime_dvd_left hd_u
            |>.coprime_dvd_right hd_s
        have hAeq : mkA u s i = u ⟨i, hi⟩ * ∏ j ∈ Em.erase i,
            if h : (i, j) ∈ offDm then s ⟨(i, j), h⟩ else 1 := by
          dsimp only [mkA]; rw [dif_pos hi, hlcm_eq]
          have h := Nat.gcd_mul_lcm (u ⟨i, hi⟩) (∏ j ∈ Em.erase i,
            if h : (i, j) ∈ offDm then s ⟨(i, j), h⟩ else 1)
          rw [hucop.gcd_eq_one, one_mul] at h; exact h
        have hu_ne : u ⟨i, hi⟩ ≠ 0 :=
          Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu ⟨i, hi⟩)).1).1
        have hs_ne : ∀ j ∈ Em.erase i, (if h : (i, j) ∈ offDm then s ⟨(i, j), h⟩ else 1) ≠ 0 := fun j _ => by
          split_ifs with h
          · exact Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_of_mem_erase hs) ⟨(i, j), h⟩)).1).1
          · exact one_ne_zero
        have hprod_ne : (∏ j ∈ Em.erase i, if h : (i, j) ∈ offDm then s ⟨(i, j), h⟩ else 1) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr hs_ne
        rw [hAeq, g₂_mul_of_coprime hu_ne hprod_ne hucop, g₂_prod_of_pairwise_coprime _ _ hs_ne hcop_pair]
        push_cast; rfl
      have hg2_B : ∀ (i : Fin (k + 1)) (hi : i ∈ Em), (g₂ (mkB u s i) : ℝ) =
          (g₂ (u ⟨i, hi⟩) : ℝ) * ∏ j ∈ Em.erase i,
            (g₂ (if h : (j, i) ∈ offDm then s ⟨(j, i), h⟩ else 1) : ℝ) := fun i hi => by
        have hcop_pair : ∀ j₁ ∈ Em.erase i, ∀ j₂ ∈ Em.erase i, j₁ ≠ j₂ →
            Nat.Coprime (if h : (j₁, i) ∈ offDm then s ⟨(j₁, i), h⟩ else 1)
              (if h : (j₂, i) ∈ offDm then s ⟨(j₂, i), h⟩ else 1) := by
          intro j₁ hj₁ j₂ hj₂ hne
          have h1 : (j₁, i) ∈ offDm := Finset.mem_offDiag.mpr ⟨(Finset.mem_erase.mp hj₁).2, hi, (Finset.mem_erase.mp hj₁).1⟩
          have h2 : (j₂, i) ∈ offDm := Finset.mem_offDiag.mpr ⟨(Finset.mem_erase.mp hj₂).2, hi, (Finset.mem_erase.mp hj₂).1⟩
          rw [dif_pos h1, dif_pos h2]
          have hd1 : s ⟨(j₁, i), h1⟩ ∣ mkA u s j₁ := by
            dsimp only [mkA]; rw [dif_pos (Finset.mem_erase.mp hj₁).2]
            have := Finset.dvd_lcm (f := fun r => if h : (j₁, r) ∈ offDm then s ⟨(j₁, r), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj₁).1.symm, hi⟩)
            rw [dif_pos h1] at this; exact dvd_trans this (Nat.dvd_lcm_right _ _)
          have hd2 : s ⟨(j₂, i), h2⟩ ∣ mkA u s j₂ := by
            dsimp only [mkA]; rw [dif_pos (Finset.mem_erase.mp hj₂).2]
            have := Finset.dvd_lcm (f := fun r => if h : (j₂, r) ∈ offDm then s ⟨(j₂, r), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj₂).1.symm, hi⟩)
            rw [dif_pos h2] at this; exact dvd_trans this (Nat.dvd_lcm_right _ _)
          exact (hA_cop j₁ (Finset.mem_univ j₁) j₂ (Finset.mem_univ j₂) hne).coprime_dvd_left hd1
            |>.coprime_dvd_right hd2
        have hlcm_eq := finset_lcm_eq_prod_of_pairwise_coprime (Em.erase i) _ hcop_pair
        have hucop : Nat.Coprime (u ⟨i, hi⟩) (∏ j ∈ Em.erase i,
            if h : (j, i) ∈ offDm then s ⟨(j, i), h⟩ else 1) := by
          refine Nat.Coprime.prod_right fun j hj => ?_
          have h1 : (j, i) ∈ offDm := Finset.mem_offDiag.mpr ⟨(Finset.mem_erase.mp hj).2, hi, (Finset.mem_erase.mp hj).1⟩
          rw [dif_pos h1]
          have hd_u : u ⟨i, hi⟩ ∣ mkA u s i := by dsimp only [mkA]; rw [dif_pos hi]; exact Nat.dvd_lcm_left _ _
          have hd_s : s ⟨(j, i), h1⟩ ∣ mkA u s j := by
            dsimp only [mkA]; rw [dif_pos (Finset.mem_erase.mp hj).2]
            have := Finset.dvd_lcm (f := fun r => if h : (j, r) ∈ offDm then s ⟨(j, r), h⟩ else 1)
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1.symm, hi⟩)
            rw [dif_pos h1] at this; exact dvd_trans this (Nat.dvd_lcm_right _ _)
          exact (hA_cop i (Finset.mem_univ i) j (Finset.mem_univ j) (Finset.mem_erase.mp hj).1.symm).coprime_dvd_left hd_u
            |>.coprime_dvd_right hd_s
        have hBeq : mkB u s i = u ⟨i, hi⟩ * ∏ j ∈ Em.erase i,
            if h : (j, i) ∈ offDm then s ⟨(j, i), h⟩ else 1 := by
          dsimp only [mkB]; rw [dif_pos hi, hlcm_eq]
          have h := Nat.gcd_mul_lcm (u ⟨i, hi⟩) (∏ j ∈ Em.erase i,
            if h : (j, i) ∈ offDm then s ⟨(j, i), h⟩ else 1)
          rw [hucop.gcd_eq_one, one_mul] at h; exact h
        have hu_ne : u ⟨i, hi⟩ ≠ 0 :=
          Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu ⟨i, hi⟩)).1).1
        have hs_ne : ∀ j ∈ Em.erase i, (if h : (j, i) ∈ offDm then s ⟨(j, i), h⟩ else 1) ≠ 0 := fun j _ => by
          split_ifs with h
          · exact Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_of_mem_erase hs) ⟨(j, i), h⟩)).1).1
          · exact one_ne_zero
        have hprod_ne : (∏ j ∈ Em.erase i, if h : (j, i) ∈ offDm then s ⟨(j, i), h⟩ else 1) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr hs_ne
        rw [hBeq, g₂_mul_of_coprime hu_ne hprod_ne hucop, g₂_prod_of_pairwise_coprime _ _ hs_ne hcop_pair]
        push_cast; rfl
      have hprod_offA : (∏ i ∈ Em, ∏ j ∈ Em.erase i,
            (g₂ (if h : (i, j) ∈ offDm then s ⟨(i, j), h⟩ else 1) : ℝ)) =
          ∏ p : ↥offDm, (g₂ (s p) : ℝ) := by
        rw [← Finset.prod_sigma (s := Em) (t := fun i : Fin (k + 1) => Em.erase i)
          (f := fun x : Σ _ : Fin (k + 1), Fin (k + 1) =>
            (g₂ (if h : (x.1, x.2) ∈ offDm then s ⟨(x.1, x.2), h⟩ else 1) : ℝ))]
        refine Finset.prod_bij (fun x hx => ⟨(x.1, x.2),
          Finset.mem_offDiag.mpr ⟨(Finset.mem_sigma.mp hx).1,
            (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).2,
            (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).1.symm⟩⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro x₁ _ x₂ _ heq
          simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
          exact Sigma.ext heq.1 (heq_of_eq heq.2)
        · intro p _
          obtain ⟨hp1, hp2, hne⟩ := Finset.mem_offDiag.mp p.2
          exact ⟨⟨p.1.1, p.1.2⟩, Finset.mem_sigma.mpr ⟨hp1, Finset.mem_erase.mpr ⟨hne.symm, hp2⟩⟩, Subtype.ext rfl⟩
        · intro x hx
          have hmem : (x.1, x.2) ∈ offDm := Finset.mem_offDiag.mpr
            ⟨(Finset.mem_sigma.mp hx).1, (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).2,
             (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).1.symm⟩
          simp only [dif_pos hmem]
      have hprod_offB : (∏ i ∈ Em, ∏ j ∈ Em.erase i,
            (g₂ (if h : (j, i) ∈ offDm then s ⟨(j, i), h⟩ else 1) : ℝ)) =
          ∏ p : ↥offDm, (g₂ (s p) : ℝ) := by
        rw [← Finset.prod_sigma (s := Em) (t := fun i : Fin (k + 1) => Em.erase i)
          (f := fun x : Σ _ : Fin (k + 1), Fin (k + 1) =>
            (g₂ (if h : (x.2, x.1) ∈ offDm then s ⟨(x.2, x.1), h⟩ else 1) : ℝ))]
        refine Finset.prod_bij (fun x hx => ⟨(x.2, x.1),
          Finset.mem_offDiag.mpr ⟨(Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).2,
            (Finset.mem_sigma.mp hx).1, (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).1⟩⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro x₁ _ x₂ _ heq
          simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
          exact Sigma.ext heq.2 (heq_of_eq heq.1)
        · intro p _
          obtain ⟨hp1, hp2, hne⟩ := Finset.mem_offDiag.mp p.2
          exact ⟨⟨p.1.2, p.1.1⟩, Finset.mem_sigma.mpr ⟨hp2, Finset.mem_erase.mpr ⟨hne, hp1⟩⟩, Subtype.ext rfl⟩
        · intro x hx
          have hmem : (x.2, x.1) ∈ offDm := Finset.mem_offDiag.mpr
            ⟨(Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).2, (Finset.mem_sigma.mp hx).1,
             (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).1⟩
          simp only [dif_pos hmem]
      have hg2_A_prod : (∏ i ∈ Em, (g₂ (mkA u s i) : ℝ)) =
          (∏ i : ↥Em, (g₂ (u i) : ℝ)) * ∏ p : ↥offDm, (g₂ (s p) : ℝ) := by
        rw [← Finset.prod_attach Em, Finset.prod_congr rfl fun i _ => hg2_A i.1 i.2,
          Finset.prod_mul_distrib]
        congr 1
        rw [← hprod_offA, ← Finset.prod_attach Em]
      have hg2_B_prod : (∏ i ∈ Em, (g₂ (mkB u s i) : ℝ)) =
          (∏ i : ↥Em, (g₂ (u i) : ℝ)) * ∏ p : ↥offDm, (g₂ (s p) : ℝ) := by
        rw [← Finset.prod_attach Em, Finset.prod_congr rfl fun i _ => hg2_B i.1 i.2,
          Finset.prod_mul_distrib]
        congr 1
        rw [← hprod_offB, ← Finset.prod_attach Em]
      have hmu_le1 : ∀ n : ℕ, |(μ n : ℝ)| ≤ 1 := fun n => by
        by_cases hsf : Squarefree n
        · rw [moebius_eq_prod_neg_one_of_squarefree hsf, Finset.abs_prod]; simp
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
      have hu_pos : 0 < ∏ i : ↥Em, (g₂ (u i) : ℝ) :=
        Finset.prod_pos fun i _ => by
          have hmem := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu i)
          exact Nat.cast_pos.mpr (g₂_pos_of_coprime_two hmem.2.1.ne_zero (hmem.2.2.coprime_dvd_right h2W))
      have hs_pos : 0 < ∏ p : ↥offDm, (g₂ (s p) : ℝ) :=
        Finset.prod_pos fun p _ => by
          have hmem := Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_of_mem_erase hs) p)
          exact Nat.cast_pos.mpr (g₂_pos_of_coprime_two hmem.2.1.ne_zero (hmem.2.2.coprime_dvd_right h2W))
      rw [hg2_A_prod, hg2_B_prod]
      have hden_eq : (∏ i : ↥Em, (g₂ (u i) : ℝ)) /
          (((∏ i : ↥Em, (g₂ (u i) : ℝ)) * ∏ p : ↥offDm, (g₂ (s p) : ℝ)) *
            ((∏ i : ↥Em, (g₂ (u i) : ℝ)) * ∏ p : ↥offDm, (g₂ (s p) : ℝ))) =
          (∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹) * (∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹) := by
        rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_pow]
        field_simp [hu_pos.ne', hs_pos.ne']
      have habs_mu : |(∏ p : ↥offDm, (μ (s p) : ℝ)) * (∏ i ∈ Em, (μ (mkA u s i) : ℝ)) *
          (∏ i ∈ Em, (μ (mkB u s i) : ℝ))| ≤ 1 := by
        rw [abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod, Finset.abs_prod]
        have h1 : ∏ p : ↥offDm, |(μ (s p) : ℝ)| ≤ 1 := Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p _ => hmu_le1 _)
        have h2 : ∏ i ∈ Em, |(μ (mkA u s i) : ℝ)| ≤ 1 := Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hmu_le1 _)
        have h3 : ∏ i ∈ Em, |(μ (mkB u s i) : ℝ)| ≤ 1 := Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hmu_le1 _)
        calc (∏ p : ↥offDm, |(μ (s p) : ℝ)|) * (∏ i ∈ Em, |(μ (mkA u s i) : ℝ)|) * (∏ i ∈ Em, |(μ (mkB u s i) : ℝ)|)
            ≤ 1 * 1 * 1 := by
              refine mul_le_mul (mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) zero_le_one)
                h3 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have hrew : (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
            ((∏ i ∈ Em, (μ (mkA u s i) : ℝ)) * yMVar W₀ R T m (mkA u s) /
              ((∏ i : ↥Em, (g₂ (u i) : ℝ)) * ∏ p : ↥offDm, (g₂ (s p) : ℝ))) *
            ((∏ i ∈ Em, (μ (mkB u s i) : ℝ)) * yMVar W₀ R T m (mkB u s) /
              ((∏ i : ↥Em, (g₂ (u i) : ℝ)) * ∏ p : ↥offDm, (g₂ (s p) : ℝ))) =
          ((∏ p : ↥offDm, (μ (s p) : ℝ)) * (∏ i ∈ Em, (μ (mkA u s i) : ℝ)) * (∏ i ∈ Em, (μ (mkB u s i) : ℝ))) *
            (yMVar W₀ R T m (mkA u s) * yMVar W₀ R T m (mkB u s)) *
            ((∏ i : ↥Em, (g₂ (u i) : ℝ)) /
              (((∏ i : ↥Em, (g₂ (u i) : ℝ)) * ∏ p : ↥offDm, (g₂ (s p) : ℝ)) *
                ((∏ i : ↥Em, (g₂ (u i) : ℝ)) * ∏ p : ↥offDm, (g₂ (s p) : ℝ)))) := by ring
      have hden_nn : 0 ≤ (∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹) * (∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹) :=
        mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (Finset.prod_nonneg fun _ _ => by positivity)
      rw [hrew, hden_eq, abs_mul, abs_mul, abs_of_nonneg hden_nn]
      have hy_bd : |yMVar W₀ R T m (mkA u s) * yMVar W₀ R T m (mkB u s)| ≤ yM_max ^ 2 := by
        rw [abs_mul, sq]
        exact mul_le_mul (abs_yMVar_le hD hR T m _) (abs_yMVar_le hD hR T m _) (abs_nonneg _) hyM_max_nn
      calc |(∏ p : ↥offDm, (μ (s p) : ℝ)) * (∏ i ∈ Em, (μ (mkA u s i) : ℝ)) * (∏ i ∈ Em, (μ (mkB u s i) : ℝ))| *
            |yMVar W₀ R T m (mkA u s) * yMVar W₀ R T m (mkB u s)| *
            ((∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹) * (∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹))
          ≤ 1 * yM_max ^ 2 *
              ((∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹) * (∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹)) := by gcongr
        _ = yM_max ^ 2 * (∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹) * (∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹) := by ring
    · have hzero : yMVar W₀ R T m (mkA u s) = 0 ∨ yMVar W₀ R T m (mkB u s) = 0 := by
        by_cases hA : mkA u s ∈ validTupleSet k W₀ R
        · right; unfold yMVar; rw [if_neg (fun hB => hAB ⟨hA, hB.1⟩)]
        · left; unfold yMVar; rw [if_neg (fun h => hA h.1)]
      rcases hzero with h0 | h0 <;> simp [h0] <;> positivity
  have hsum_u : ∑ u ∈ Uset, ∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹ ≤
      (2 : ℝ) ^ k * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k := by
    rw [sum_piFinset_prod (fun _ : ↥Em => S_sf) (fun _ x => (g₂ x : ℝ)⁻¹),
      Finset.prod_const, Finset.card_univ, Fintype.card_coe, hEm_card]
    have h1d : ∑ x ∈ S_sf, (g₂ x : ℝ)⁻¹ = ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n := by
      unfold aG2; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [h1d, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => aG2_nonneg _ _)
      (sum_aG2_le_two_mul_sum_aPhi hD) k
  have hsum_s : ∑ s ∈ Sset.erase s1, ∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹ ≤
      (1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1 := by
    have hfull : ∑ s ∈ Sset, ∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹ =
        (∑ n ∈ S_sf, ((g₂ n : ℝ) ^ 2)⁻¹) ^ (k * (k - 1)) := by
      rw [sum_piFinset_prod (fun _ : ↥offDm => S_sf) (fun _ x => ((g₂ x : ℝ) ^ 2)⁻¹),
        Finset.prod_const, Finset.card_univ, Fintype.card_coe, hoffDm_card]
    have hsplit_s := Finset.add_sum_erase Sset (fun s => ∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹) hs1_mem
    have hs1_val : ∏ p : ↥offDm, ((g₂ (s1 p) : ℝ) ^ 2)⁻¹ = 1 := by simp [s1, g₂]
    rw [hs1_val] at hsplit_s
    have hpow : (∑ n ∈ S_sf, ((g₂ n : ℝ) ^ 2)⁻¹) ^ (k * (k - 1)) ≤
        (1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (sum_inv_g2_sq_le hD) _
    linarith
  have hoff_abs : |∑ s ∈ Sset.erase s1, ∑ u ∈ Uset,
        (∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
          ((∏ i ∈ Em, (μ (mkA u s i) : ℝ)) * yMVar W₀ R T m (mkA u s) / (∏ i ∈ Em, (g₂ (mkA u s i) : ℝ))) *
          ((∏ i ∈ Em, (μ (mkB u s i) : ℝ)) * yMVar W₀ R T m (mkB u s) / (∏ i ∈ Em, (g₂ (mkB u s i) : ℝ)))| ≤
      (8 : ℝ) ^ k * T.bound ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 2) *
        ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1) := by
    calc |∑ s ∈ Sset.erase s1, ∑ u ∈ Uset, _|
        ≤ ∑ s ∈ Sset.erase s1, ∑ u ∈ Uset,
            |(∏ i : ↥Em, (g₂ (u i) : ℝ)) * (∏ p : ↥offDm, (μ (s p) : ℝ)) *
              ((∏ i ∈ Em, (μ (mkA u s i) : ℝ)) * yMVar W₀ R T m (mkA u s) / (∏ i ∈ Em, (g₂ (mkA u s i) : ℝ))) *
              ((∏ i ∈ Em, (μ (mkB u s i) : ℝ)) * yMVar W₀ R T m (mkB u s) / (∏ i ∈ Em, (g₂ (mkB u s i) : ℝ)))| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ s ∈ Sset.erase s1, ∑ u ∈ Uset,
            yM_max ^ 2 * (∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹) * (∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹) :=
          Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun u hu => hterm_s s hs u hu
      _ = yM_max ^ 2 * (∑ u ∈ Uset, ∏ i : ↥Em, (g₂ (u i) : ℝ)⁻¹) *
            (∑ s ∈ Sset.erase s1, ∏ p : ↥offDm, ((g₂ (s p) : ℝ) ^ 2)⁻¹) := by
          simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ yM_max ^ 2 * ((2 : ℝ) ^ k * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k) *
            ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsum_u (sq_nonneg _)) hsum_s
            (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
            (mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
              (pow_nonneg (Finset.sum_nonneg fun _ _ => aPhi_nonneg _ _) _)))
      _ = (8 : ℝ) ^ k * T.bound ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 2) *
            ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1) := by
          dsimp only [yM_max]
          have h8 : ((2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ k = (8 : ℝ) ^ k := by
            rw [← pow_mul, ← pow_add, show k * 2 + k = 3 * k by ring, pow_mul]; norm_num
          have hp2 : (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k =
              (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ (k + 2) := by
            rw [← pow_add, add_comm]
          calc ((2 : ℝ) ^ k * T.bound * ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ 2 *
                ((2 : ℝ) ^ k * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k) *
                ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1)
              = (((2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ k) * T.bound ^ 2 *
                  ((∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k) *
                  ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1) := by ring
            _ = _ := by rw [h8, hp2]
  linarith [(abs_le.mp hoff_abs).1]

/-- Canonical permutation of `Fin (k + 1)` placing `m` at coordinate `0` and `m.succAbove j` at `j.succ`. -/
private def permM {k : ℕ} (m : Fin (k + 1)) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.ofBijective (Fin.cases m m.succAbove)
    (Finite.injective_iff_bijective.mp fun i₁ i₂ => by
      refine Fin.cases ?_ (fun j₁ => ?_) i₁ <;> refine Fin.cases ?_ (fun j₂ => ?_) i₂ <;> intro h
      · rfl
      · exfalso; exact (Fin.succAbove_ne m j₂) h.symm
      · exfalso; exact (Fin.succAbove_ne m j₁) h
      · exact congrArg Fin.succ (Fin.succAbove_right_injective h))

private lemma permM_zero {k : ℕ} (m : Fin (k + 1)) : permM m 0 = m := rfl
private lemma permM_succ {k : ℕ} (m : Fin (k + 1)) (j : Fin k) : permM m j.succ = m.succAbove j := rfl

/-- Explicit `D₀`-dependent relative error term in `Q1Sum_asymp_lower`, satisfying `E1_D0 → 0` as `D₀ → ∞`. -/
def E1_D0 (k : ℕ) (B : ℝ) (D₀ : ℕ) : ℝ :=
  let δ : ℝ := 2 / ((D₀ - 2 : ℕ) : ℝ)
  B ^ 2 * ((8 : ℝ) ^ k * ((1 + δ) ^ (k * (k - 1)) - 1) +
    (2 : ℝ) ^ (k + 1) * ((1 + δ) ^ k - 1) +
    ((2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) + (k : ℝ) ^ 2) * δ)

lemma E1_D0_nonneg (k : ℕ) (B : ℝ) (D₀ : ℕ) : 0 ≤ E1_D0 k B D₀ := by
  unfold E1_D0
  set δ : ℝ := 2 / ((D₀ - 2 : ℕ) : ℝ)
  have hδ : 0 ≤ δ := by positivity
  have h1 : (1 : ℝ) ≤ (1 + δ) ^ (k * (k - 1)) := one_le_pow₀ (by linarith)
  have h2 : (1 : ℝ) ≤ (1 + δ) ^ k := one_le_pow₀ (by linarith)
  refine mul_nonneg (sq_nonneg _) (add_nonneg (add_nonneg ?_ ?_) ?_)
  · exact mul_nonneg (by positivity) (by linarith)
  · exact mul_nonneg (by positivity) (by linarith)
  · positivity

lemma tendsto_E1_D0 (k : ℕ) (B : ℝ) :
    Filter.Tendsto (fun D₀ : ℕ => E1_D0 k B D₀) Filter.atTop (nhds 0) := by
  have hδ : Filter.Tendsto (fun D₀ : ℕ => (2 : ℝ) / ((D₀ - 2 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
    have hnat : Filter.Tendsto (fun D₀ : ℕ => ((D₀ - 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨Nat.ceil b + 2, fun n hn => ?_⟩
      have h1 : Nat.ceil b ≤ n - 2 := by omega
      exact (Nat.le_ceil b).trans (by exact_mod_cast h1)
    exact tendsto_const_nhds.div_atTop hnat
  have h1 : Filter.Tendsto (fun D₀ : ℕ =>
      (1 + (2 : ℝ) / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1) Filter.atTop (nhds 0) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).add hδ).pow (k * (k - 1))).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using this
  have h2 : Filter.Tendsto (fun D₀ : ℕ =>
      (1 + (2 : ℝ) / ((D₀ - 2 : ℕ) : ℝ)) ^ k - 1) Filter.atTop (nhds 0) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).add hδ).pow k).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using this
  have h3 := (((h1.const_mul ((8 : ℝ) ^ k)).add (h2.const_mul ((2 : ℝ) ^ (k + 1)))).add
    (hδ.const_mul ((2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) + (k : ℝ) ^ 2))).const_mul (B ^ 2)
  simpa [E1_D0] using h3

/-- Helper: `L¹` prime-factor reciprocal bound against `1 / g₂(n)`:
for `D₀ ≥ 6`, `∑_{n ∈ S_sf} (∑_{p ∣ n} 1/(p - 1)) / g₂(n) ≤ (2 / (D₀ - 2)) * ∑_{n=1}^M aG2 (W D₀) n`. -/
private lemma sum_primeFactors_inv_sub_one_div_g2_le {D₀ M : ℕ} (hD : 6 ≤ D₀) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Squarefree n ∧ Nat.Coprime n (W D₀)),
        (∑ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ n : ℝ) ≤
      (2 / ((D₀ - 2 : ℕ) : ℝ)) * ∑ n ∈ Finset.Icc 1 M, aG2 (W D₀) n := by
  set W₀ := W D₀
  set S_sf := (Finset.Icc 1 M).filter (fun n => Squarefree n ∧ Nat.Coprime n W₀)
  set P := (Finset.Icc (D₀ + 1) M).filter Nat.Prime
  have hmem_P : ∀ n ∈ S_sf, ∀ p ∈ n.primeFactors, p ∈ P := by
    intro n hn p hp
    have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hcop := (Finset.mem_filter.mp hn).2.2
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have hpD : D₀ < p := by
      by_contra hle; push Not at hle
      exact hpp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hcop) ▸
        Nat.dvd_gcd hpn ((prime_dvd_W_iff hpp).mpr hle))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, (Nat.le_of_dvd h1.1 hpn).trans h1.2⟩, hpp⟩
  have hswap : ∑ n ∈ S_sf, (∑ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ n : ℝ) =
      ∑ p ∈ P, (((p - 1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ S_sf.filter (fun n => p ∣ n), (g₂ n : ℝ)⁻¹ := by
    have h1 : ∀ n ∈ S_sf, (∑ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ n : ℝ) =
        ∑ p ∈ P, if p ∣ n then (((p - 1 : ℕ) : ℝ))⁻¹ * (g₂ n : ℝ)⁻¹ else 0 := fun n hn => by
      rw [div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p; simp only [Finset.mem_filter, Nat.mem_primeFactors]
      have hn0 : n ≠ 0 := (Finset.mem_filter.mp hn).2.1.ne_zero
      constructor
      · rintro ⟨hpp, hpn, _⟩
        exact ⟨hmem_P n hn p (Nat.mem_primeFactors.mpr ⟨hpp, hpn, hn0⟩), hpn⟩
      · rintro ⟨hpP, hpn⟩
        exact ⟨(Finset.mem_filter.mp hpP).2, hpn, hn0⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter, Finset.mul_sum]
  rw [hswap]
  have hinner : ∀ p ∈ P, ∑ n ∈ S_sf.filter (fun n => p ∣ n), (g₂ n : ℝ)⁻¹ ≤
      (((p - 2 : ℕ) : ℝ))⁻¹ * ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hpD : D₀ + 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hterm : ∀ n ∈ S_sf.filter (fun n => p ∣ n),
        (g₂ n : ℝ)⁻¹ = (((p - 2 : ℕ) : ℝ))⁻¹ * (g₂ (n / p) : ℝ)⁻¹ := by
      intro n hn
      have hnS := (Finset.mem_filter.mp hn).1
      have hpn := (Finset.mem_filter.mp hn).2
      have hsf := (Finset.mem_filter.mp hnS).2.1
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
      have hcop : Nat.Coprime p (n / p) := Nat.coprime_of_squarefree_mul (hmul.symm ▸ hsf)
      have hq_ne : n / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp (Finset.mem_filter.mp hnS).1).1 hpn) hpp.pos)
      have hg2_p : g₂ p = p - 2 := by unfold g₂; rw [hpp.primeFactors]; simp
      conv_lhs => rw [← hmul]
      rw [g₂_mul_of_coprime hpp.ne_zero hq_ne hcop, hg2_p, Nat.cast_mul, mul_inv]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hinj : Set.InjOn (fun n => n / p) (S_sf.filter (fun n => p ∣ n)) := by
      intro n₁ hn₁ n₂ hn₂ heq
      dsimp only at heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2,
        ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2, heq]
    have hsub : (S_sf.filter (fun n => p ∣ n)).image (fun n => n / p) ⊆ S_sf := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨n, hn, rfl⟩
      have hnS := (Finset.mem_filter.mp hn).1
      have hpn := (Finset.mem_filter.mp hn).2
      have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hnS).1
      have hdvd : n / p ∣ n := Nat.div_dvd_of_dvd hpn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd h1.1 hpn) hpp.pos,
        (Nat.div_le_self _ _).trans h1.2⟩,
        (Finset.mem_filter.mp hnS).2.1.squarefree_of_dvd hdvd,
        (Finset.mem_filter.mp hnS).2.2.coprime_dvd_left hdvd⟩
    calc ∑ n ∈ S_sf.filter (fun n => p ∣ n), (g₂ (n / p) : ℝ)⁻¹
        = ∑ c ∈ (S_sf.filter (fun n => p ∣ n)).image (fun n => n / p), (g₂ c : ℝ)⁻¹ :=
          (Finset.sum_image (f := fun c => (g₂ c : ℝ)⁻¹) (fun a ha b hb hab => hinj ha hb hab)).symm
      _ ≤ ∑ c ∈ S_sf, (g₂ c : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n := by
          unfold aG2; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  calc ∑ p ∈ P, (((p - 1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ S_sf.filter (fun n => p ∣ n), (g₂ n : ℝ)⁻¹
      ≤ ∑ p ∈ P, (((p - 2 : ℕ) : ℝ) ^ 2)⁻¹ * ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp5 : 5 ≤ p := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega
        have hinv_le : (((p - 1 : ℕ) : ℝ))⁻¹ ≤ (((p - 2 : ℕ) : ℝ))⁻¹ :=
          inv_anti₀ (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast (show p - 2 ≤ p - 1 by omega))
        calc (((p - 1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ S_sf.filter (fun n => p ∣ n), (g₂ n : ℝ)⁻¹
            ≤ (((p - 1 : ℕ) : ℝ))⁻¹ * ((((p - 2 : ℕ) : ℝ))⁻¹ * ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n) :=
              mul_le_mul_of_nonneg_left (hinner p hp) (by positivity)
          _ = ((((p - 1 : ℕ) : ℝ))⁻¹ * (((p - 2 : ℕ) : ℝ))⁻¹) * ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n := by ring
          _ ≤ ((((p - 2 : ℕ) : ℝ))⁻¹ * (((p - 2 : ℕ) : ℝ))⁻¹) * ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinv_le (by positivity))
                (Finset.sum_nonneg fun _ _ => aG2_nonneg _ _)
          _ = (((p - 2 : ℕ) : ℝ) ^ 2)⁻¹ * ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n := by rw [sq, mul_inv]
    _ = (∑ p ∈ P, (((p - 2 : ℕ) : ℝ) ^ 2)⁻¹) * ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n := by rw [← Finset.sum_mul]
    _ ≤ (2 / ((D₀ - 2 : ℕ) : ℝ)) * ∑ n ∈ Finset.Icc 1 M, aG2 W₀ n := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => aG2_nonneg _ _)
        have h1 := sum_inv_sub_two_sq_le (D₀ := D₀) (M := M) (by omega)
        have hDpos : (0 : ℝ) < ((D₀ - 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have h2 : 1 / ((D₀ - 2 : ℕ) : ℝ) ≤ 2 / ((D₀ - 2 : ℕ) : ℝ) := by
          rw [div_le_div_iff_of_pos_right hDpos]; norm_num
        exact h1.trans h2

/-- Helper: sum of `∏ i, aPhi (W D₀) (v i)` over non-pairwise-coprime `k`-tuples with `∏ v_i ≤ R`
is bounded by `k² * (2 / (D₀ - 2)) * (∑_{n ≤ ⌊R⌋} aPhi (W D₀) n)^k`. -/
private lemma sum_non_coprime_simplex_le {k D₀ : ℕ} (hD : 6 ≤ D₀) {R : ℝ} (hR : 1 ≤ R) :
    ∑ v ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R⌋₊)).filter
        (fun v => ((∏ i, v i : ℕ) : ℝ) ≤ R ∧ ¬ Squarefree (∏ i, v i)),
        ∏ i, aPhi (W D₀) (v i) ≤
      (k : ℝ) ^ 2 * (2 / ((D₀ - 2 : ℕ) : ℝ)) * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi (W D₀) n) ^ k := by
  set W₀ := W D₀
  set S_sf := (Finset.Icc 1 ⌊R⌋₊).filter (fun n => Squarefree n ∧ Nat.Coprime n W₀)
  set P := (Finset.Icc (D₀ + 1) ⌊R⌋₊).filter Nat.Prime
  set offK : Finset (Fin k × Fin k) := (Finset.univ : Finset (Fin k)).offDiag
  set bad := (Fintype.piFinset (fun _ : Fin k => S_sf)).filter (fun v => ¬ Squarefree (∏ i, v i))
  -- First restrict to `S_sf` (outside `S_sf`, `∏ aPhi = 0`)
  have hrestrict : ∑ v ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R⌋₊)).filter
        (fun v => ((∏ i, v i : ℕ) : ℝ) ≤ R ∧ ¬ Squarefree (∏ i, v i)),
        ∏ i, aPhi W₀ (v i) ≤
      ∑ v ∈ bad, ∏ i, aPhi W₀ (v i) := by
    have hzero : ∀ v ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R⌋₊)).filter
        (fun v => ((∏ i, v i : ℕ) : ℝ) ≤ R ∧ ¬ Squarefree (∏ i, v i)),
        v ∉ bad → ∏ i, aPhi W₀ (v i) = 0 := by
      intro v hv hnb
      simp only [Finset.mem_filter, Fintype.mem_piFinset] at hv
      simp only [bad, Finset.mem_filter, Fintype.mem_piFinset, S_sf, not_and] at hnb
      have hall : ¬ ∀ i, v i ∈ Finset.Icc 1 ⌊R⌋₊ ∧ Squarefree (v i) ∧ Nat.Coprime (v i) W₀ := fun h =>
        hnb h hv.2.2
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      unfold aPhi; rw [if_neg (fun hc => hi (hv.1 i) hc.1 hc.2)]
    calc _ = ∑ v ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R⌋₊)).filter
            (fun v => ((∏ i, v i : ℕ) : ℝ) ≤ R ∧ ¬ Squarefree (∏ i, v i))).filter (fun v => v ∈ bad),
            ∏ i, aPhi W₀ (v i) := by
          rw [Finset.sum_filter (p := fun v => v ∈ bad)]
          refine Finset.sum_congr rfl fun v hv => ?_
          split_ifs with hb
          · rfl
          · exact hzero v hv hb
      _ ≤ ∑ v ∈ bad, ∏ i, aPhi W₀ (v i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (Finset.mem_filter.mp hv).2)
            fun _ _ _ => Finset.prod_nonneg fun _ _ => aPhi_nonneg _ _
  -- Cover `bad` by `biUnion` over `(pair, p) ∈ offK ×ˢ P` of `{v ∈ piFinset S_sf : p ∣ v pair.1 ∧ p ∣ v pair.2}`
  let slice : (Fin k × Fin k) × ℕ → Finset (Fin k → ℕ) := fun x =>
    (Fintype.piFinset (fun _ : Fin k => S_sf)).filter (fun v => x.2 ∣ v x.1.1 ∧ x.2 ∣ v x.1.2)
  have hcover : bad ⊆ (offK ×ˢ P).biUnion slice := by
    intro v hv
    have hvS : v ∈ Fintype.piFinset (fun _ : Fin k => S_sf) := (Finset.mem_filter.mp hv).1
    have hnsf : ¬ Squarefree (∏ i, v i) := (Finset.mem_filter.mp hv).2
    have hsf_i : ∀ i, Squarefree (v i) := fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hvS i)).2.1
    have hnot_pair : ¬ ∀ i ∈ (Finset.univ : Finset (Fin k)), ∀ j ∈ (Finset.univ : Finset (Fin k)),
        i ≠ j → Nat.Coprime (v i) (v j) := fun hpair =>
      hnsf (squarefree_prod_of_pairwise (fun i _ => hsf_i i) hpair)
    push Not at hnot_pair
    obtain ⟨i₁, _, i₂, _, hne, hnc⟩ := hnot_pair
    obtain ⟨p, hpp, hpgcd⟩ := Nat.exists_prime_and_dvd hnc
    have hp1 : p ∣ v i₁ := dvd_trans hpgcd (Nat.gcd_dvd_left _ _)
    have hp2 : p ∣ v i₂ := dvd_trans hpgcd (Nat.gcd_dvd_right _ _)
    have hv1 := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hvS i₁)
    have hpD : D₀ < p := by
      by_contra hle; push Not at hle
      exact hpp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hv1.2.2) ▸
        Nat.dvd_gcd hp1 ((prime_dvd_W_iff hpp).mpr hle))
    have hpM : p ≤ ⌊R⌋₊ := (Nat.le_of_dvd (Finset.mem_Icc.mp hv1.1).1 hp1).trans (Finset.mem_Icc.mp hv1.1).2
    exact Finset.mem_biUnion.mpr ⟨((i₁, i₂), p),
      Finset.mem_product.mpr ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hpM⟩, hpp⟩⟩,
      Finset.mem_filter.mpr ⟨hvS, hp1, hp2⟩⟩
  have hslice_bd : ∀ x ∈ offK ×ˢ P,
      ∑ v ∈ slice x, ∏ i, aPhi W₀ (v i) ≤
        (((x.2 - 1 : ℕ) : ℝ) ^ 2)⁻¹ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k := by
    rintro ⟨⟨i₁, i₂⟩, p⟩ hx
    have hne : i₁ ≠ i₂ := (Finset.mem_offDiag.mp (Finset.mem_product.mp hx).1).2.2
    have hpp : p.Prime := (Finset.mem_filter.mp (Finset.mem_product.mp hx).2).2
    let emb : (Fin k → ℕ) → (Fin k → ℕ) := fun v i => if i = i₁ ∨ i = i₂ then v i / p else v i
    have hinj : Set.InjOn emb (slice ((i₁, i₂), p)) := by
      intro v₁ hv₁ v₂ hv₂ heq
      have h1 := (Finset.mem_filter.mp hv₁).2
      have h2 := (Finset.mem_filter.mp hv₂).2
      ext i
      have hi := congrFun heq i
      dsimp only [emb] at hi
      by_cases hor : i = i₁ ∨ i = i₂
      · rw [if_pos hor, if_pos hor] at hi
        rcases hor with rfl | rfl
        · rw [← Nat.mul_div_cancel' h1.1, ← Nat.mul_div_cancel' h2.1, hi]
        · rw [← Nat.mul_div_cancel' h1.2, ← Nat.mul_div_cancel' h2.2, hi]
      · rwa [if_neg hor, if_neg hor] at hi
    have hsub : (slice ((i₁, i₂), p)).image emb ⊆ Fintype.piFinset (fun _ : Fin k => S_sf) := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨v, hv, rfl⟩
      have hvS := (Finset.mem_filter.mp hv).1
      have hdv := (Finset.mem_filter.mp hv).2
      rw [Fintype.mem_piFinset]; intro i
      dsimp only [emb]
      split_ifs with hor
      · have hvi := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hvS i)
        have hpi : p ∣ v i := by rcases hor with rfl | rfl <;> [exact hdv.1; exact hdv.2]
        have hdvd : v i / p ∣ v i := Nat.div_dvd_of_dvd hpi
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hvi.1).1 hpi) hpp.pos,
          (Nat.div_le_self _ _).trans (Finset.mem_Icc.mp hvi.1).2⟩,
          hvi.2.1.squarefree_of_dvd hdvd, hvi.2.2.coprime_dvd_left hdvd⟩
      · exact Fintype.mem_piFinset.mp hvS i
    have hterm : ∀ v ∈ slice ((i₁, i₂), p),
        ∏ i, aPhi W₀ (v i) = (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ * ∏ i, aPhi W₀ (emb v i) := by
      intro v hv
      have hvS := (Finset.mem_filter.mp hv).1
      have hdv := (Finset.mem_filter.mp hv).2
      have hfac : ∀ j : Fin k, p ∣ v j → aPhi W₀ (v j) = (((p - 1 : ℕ) : ℝ))⁻¹ * aPhi W₀ (v j / p) := by
        intro j hpj
        have hvj := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hvS j)
        have hmul : p * (v j / p) = v j := Nat.mul_div_cancel' hpj
        have hcop : Nat.Coprime p (v j / p) := Nat.coprime_of_squarefree_mul (hmul.symm ▸ hvj.2.1)
        have hdvd : v j / p ∣ v j := Nat.div_dvd_of_dvd hpj
        unfold aPhi
        rw [if_pos hvj.2, if_pos ⟨hvj.2.1.squarefree_of_dvd hdvd, hvj.2.2.coprime_dvd_left hdvd⟩]
        conv_lhs => rw [← hmul]
        rw [Nat.totient_mul hcop, Nat.totient_prime hpp, Nat.cast_mul, mul_inv]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₁),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i₂⟩)]
      have hrem : ∏ i ∈ (Finset.univ.erase i₁).erase i₂, aPhi W₀ (v i) =
          ∏ i ∈ (Finset.univ.erase i₁).erase i₂, aPhi W₀ (emb v i) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have h1 : i ≠ i₂ := (Finset.mem_erase.mp hi).1
        have h2 : i ≠ i₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        simp [emb, h1, h2]
      rw [hfac i₁ hdv.1, hfac i₂ hdv.2, hrem]
      have he1 : emb v i₁ = v i₁ / p := by simp [emb]
      have he2 : emb v i₂ = v i₂ / p := by simp [emb]
      rw [← he1, ← he2]
      have hprod_emb : ∏ i, aPhi W₀ (emb v i) =
          aPhi W₀ (emb v i₁) * (aPhi W₀ (emb v i₂) * ∏ i ∈ (Finset.univ.erase i₁).erase i₂, aPhi W₀ (emb v i)) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₁),
          ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i₂⟩)]
      rw [hprod_emb, sq, mul_inv]; ring
    calc ∑ v ∈ slice ((i₁, i₂), p), ∏ i, aPhi W₀ (v i)
        = (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ * ∑ v ∈ slice ((i₁, i₂), p), ∏ i, aPhi W₀ (emb v i) := by
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      _ = (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ * ∑ c ∈ (slice ((i₁, i₂), p)).image emb, ∏ i, aPhi W₀ (c i) := by
          congr 1; exact (Finset.sum_image (f := fun c : Fin k → ℕ => ∏ i, aPhi W₀ (c i))
            (fun a ha b hb hab => hinj ha hb hab)).symm
      _ ≤ (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ * ∑ c ∈ Fintype.piFinset (fun _ : Fin k => S_sf), ∏ i, aPhi W₀ (c i) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Finset.prod_nonneg fun _ _ => aPhi_nonneg _ _)
            (by positivity)
      _ = (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k := by
          rw [sum_piFinset_prod (fun _ : Fin k => S_sf) (fun _ n => aPhi W₀ n),
            Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 2
          have h1 : ∑ n ∈ S_sf, aPhi W₀ n = ∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹ :=
            Finset.sum_congr rfl fun n hn => by unfold aPhi; rw [if_pos (Finset.mem_filter.mp hn).2]
          rw [h1]; unfold aPhi; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  calc ∑ v ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R⌋₊)).filter
          (fun v => ((∏ i, v i : ℕ) : ℝ) ≤ R ∧ ¬ Squarefree (∏ i, v i)), ∏ i, aPhi W₀ (v i)
      ≤ ∑ v ∈ bad, ∏ i, aPhi W₀ (v i) := hrestrict
    _ ≤ ∑ v ∈ (offK ×ˢ P).biUnion slice, ∏ i, aPhi W₀ (v i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => Finset.prod_nonneg fun _ _ => aPhi_nonneg _ _
    _ ≤ ∑ x ∈ offK ×ˢ P, ∑ v ∈ slice x, ∏ i, aPhi W₀ (v i) :=
        sum_biUnion_le_of_nonneg (fun _ => Finset.prod_nonneg fun _ _ => aPhi_nonneg _ _)
    _ ≤ ∑ x ∈ offK ×ˢ P, (((x.2 - 1 : ℕ) : ℝ) ^ 2)⁻¹ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k :=
        Finset.sum_le_sum hslice_bd
    _ = (offK.card : ℝ) * (∑ p ∈ P, (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹) * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k := by
        rw [Finset.sum_product]; dsimp only
        rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]; ring
    _ ≤ (k : ℝ) ^ 2 * (2 / ((D₀ - 2 : ℕ) : ℝ)) * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n) ^ k := by
        have hoff_le : (offK.card : ℝ) ≤ (k : ℝ) ^ 2 := by
          rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
          have : k * k - k ≤ k * k := Nat.sub_le _ _
          calc ((k * k - k : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast this
            _ = (k : ℝ) ^ 2 := by push_cast; ring
        have hP_le : ∑ p ∈ P, (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 / ((D₀ - 2 : ℕ) : ℝ) := by
          have h1 : ∑ p ∈ P, (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ ∑ p ∈ P, (((p - 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp5 : 5 ≤ p := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega
            exact inv_anti₀ (sq_pos_of_pos (Nat.cast_pos.mpr (by omega)))
              (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show p - 2 ≤ p - 1 by omega)) 2)
          have h2 := sum_inv_sub_two_sq_le (D₀ := D₀) (M := ⌊R⌋₊) (by omega)
          have hDpos : (0 : ℝ) < ((D₀ - 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
          have h3 : 1 / ((D₀ - 2 : ℕ) : ℝ) ≤ 2 / ((D₀ - 2 : ℕ) : ℝ) := by
            rw [div_le_div_iff_of_pos_right hDpos]; norm_num
          exact h1.trans (h2.trans h3)
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul hoff_le hP_le (Finset.sum_nonneg fun _ _ => by positivity) (by positivity))
          (pow_nonneg (Finset.sum_nonneg fun _ _ => aPhi_nonneg _ _) _)

/-- **Asymptotic Lower Bound for `Q1Sum`** (Maynard 2015 Proposition 4.1 / Lemma 5.3):
for fixed `D₀ ≥ 6`, `T : SimplexTestFn (k + 1)`, and `m : Fin (k + 1)`:
there exists `K₁ ≥ 0` such that for all `R ≥ exp 4`:
`((φ(W D₀)/W D₀) * log R)^(k + 2) * (maynardJ0 k T.F - E1_D0 k T.bound D₀) - K₁ * (log R)^(k + 3/2) ≤ Q1Sum (W D₀) R T m`. -/
theorem Q1Sum_asymp_lower {k D₀ : ℕ} (hD : 6 ≤ D₀) (T : SimplexTestFn (k + 1)) (m : Fin (k + 1)) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ R : ℝ, Real.exp 4 ≤ R →
      ((((W D₀).totient : ℝ) / (W D₀ : ℝ)) * Real.log R) ^ (k + 2) *
          (maynardJ0 k T.F - E1_D0 k T.bound D₀) -
        K₁ * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) ≤
      Q1Sum (W D₀) R T m := by
  set W₀ := W D₀
  set cW : ℝ := ((W₀.totient : ℝ) / (W₀ : ℝ))
  have hcW_nn : 0 ≤ cW := by positivity
  have h2W : 2 ∣ W₀ := (prime_dvd_W_iff Nat.prime_two).mpr (by omega)
  set δ : ℝ := 2 / ((D₀ - 2 : ℕ) : ℝ)
  have hδ_nn : 0 ≤ δ := by positivity
  obtain ⟨C_phi, hC_phi, hphi_asymp⟩ := sum_aPhi_asymp W₀ (W_pos D₀)
  -- `1D` error constant (uniform in `s ∈ [0, 1]` and `u`)
  set K_1d : ℝ := 4 * cW * (T.lip + T.bound) + 6 * C_phi * T.bound +
    2 * C_phi * (T.lip + T.bound) + 2 * (T.lip + T.bound) + 2 * T.bound
  have hK1d_nn : 0 ≤ K_1d := by
    dsimp only [K_1d]
    have := T.bound_nonneg; have := T.lip_nonneg; positivity
  -- `k`-dimensional integral approximation for `G_J(w)^2`
  let G_J : (Fin k → ℝ) → ℝ := fun w =>
    ∫ t in (0 : ℝ)..(1 - ∑ j, w j), T.F (Fin.cons t w)
  obtain ⟨K_J, hKJ_nn, hKJ⟩ :=
    sum_kd_approx_integral k (aPhi_nonneg W₀) hcW_nn hC_phi.le hphi_asymp
      T.isSimplexLipOn.innerIntegral.sq
  -- Assemble explicit `R`-asymptotic error constant `K₁`
  set C_sum : ℝ := (cW + C_phi) ^ (k + 2)
  have hCsum_nn : 0 ≤ C_sum := by positivity
  set E_off1 : ℝ := (8 : ℝ) ^ k * T.bound ^ 2 * ((1 + δ) ^ (k * (k - 1)) - 1)
  set E_piece : ℝ := T.bound ^ 2 * ((2 : ℝ) ^ (k + 1) * ((1 + δ) ^ k - 1) +
    (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) * δ)
  set E_ncop : ℝ := T.bound ^ 2 * (k : ℝ) ^ 2 * δ
  have hE1_nn : 0 ≤ E_off1 := by
    have : (1 : ℝ) ≤ (1 + δ) ^ (k * (k - 1)) := one_le_pow₀ (by linarith)
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (by linarith)
  have hEp_nn : 0 ≤ E_piece := by
    have : (1 : ℝ) ≤ (1 + δ) ^ k := one_le_pow₀ (by linarith)
    exact mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity))
  have hEn_nn : 0 ≤ E_ncop := by positivity
  set K₁ : ℝ :=
    E_off1 * C_sum +
    E_piece * cW * (cW + C_phi) ^ (k + 1) +
    (2 : ℝ) ^ (k + 1) * T.bound * cW * K_1d * (cW + C_phi) ^ k +
    E_ncop * cW ^ 2 * (cW + C_phi) ^ k +
    cW ^ 2 * K_J
  have hK1_nn : 0 ≤ K₁ := by
    dsimp only [K₁]
    have := T.bound_nonneg; positivity
  refine ⟨K₁, hK1_nn, fun R hR => ?_⟩
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
  have hR1 : 1 ≤ R := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hR
  have hlogR4 : 4 ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 4) hR; rwa [Real.log_exp] at this
  have hlogR_pos : 0 < Real.log R := by linarith
  have hlogR1 : 1 ≤ Real.log R := by linarith
  set Vm := (validTupleSet k W₀ R).filter (fun u => u m = 1)
  set Em : Finset (Fin (k + 1)) := Finset.univ.erase m
  set S_sf := (Finset.Icc 1 ⌊R⌋₊).filter (fun n => Squarefree n ∧ Nat.Coprime n W₀)
  set A_phi := ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n
  have hAphi_nn : 0 ≤ A_phi := Finset.sum_nonneg fun _ _ => aPhi_nonneg _ _
  have hAphi_le : A_phi ≤ cW * Real.log R + C_phi := by
    linarith [(abs_le.mp (hphi_asymp R hR1)).2]
  have hAphi_crude : A_phi ≤ (cW + C_phi) * Real.log R := by
    have : C_phi ≤ C_phi * Real.log R := by nlinarith
    linarith
  -- Idealized `yMain u` for `u : Fin (k + 1) → ℕ`
  let yMain : (Fin (k + 1) → ℕ) → ℝ := fun u =>
    (cW * Real.log R) * G_J (fun j : Fin k => Real.log (u (m.succAbove j) : ℝ) / Real.log R)
  have hyMain_abs : ∀ u ∈ Vm, |yMain u| ≤ (cW * Real.log R) * T.bound := by
    intro u hu
    have huV := (Finset.mem_filter.mp hu).1
    have hum := (Finset.mem_filter.mp hu).2
    obtain ⟨hu1, hu_prod, _, _⟩ := (mem_validTupleSet hR_pos.le).mp huV
    have hin : InSimplex 1 (fun j : Fin k => Real.log (u (m.succAbove j) : ℝ) / Real.log R) := by
      refine ⟨fun j => div_nonneg (Real.log_nonneg (by exact_mod_cast hu1 _)) hlogR_pos.le, ?_⟩
      rw [← Finset.sum_div, div_le_one hlogR_pos]
      have hprod_eq : ∏ j : Fin k, (u (m.succAbove j) : ℝ) = ∏ i : Fin (k + 1), (u i : ℝ) := by
        rw [Fin.prod_univ_succAbove _ m, hum, Nat.cast_one, one_mul]
      rw [← Real.log_prod fun j _ => (Nat.cast_pos.mpr (hu1 _)).ne', hprod_eq]
      exact Real.log_le_log (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (hu1 i)) (by exact_mod_cast hu_prod)
    rw [abs_mul, abs_of_nonneg (mul_nonneg hcW_nn hlogR_pos.le)]
    exact mul_le_mul_of_nonneg_left (T.isSimplexLipOn.innerIntegral.2.2.1 _ hin) (mul_nonneg hcW_nn hlogR_pos.le)
  -- Pointwise approximation of `yMVar W₀ R T m u` by `yMain u` for `u ∈ Vm`
  have happrox_u : ∀ u ∈ Vm,
      |yMVar W₀ R T m u - yMain u| ≤
        T.bound * A_phi * (((1 + δ) ^ k - 1) + δ +
          ∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) +
        K_1d * Real.sqrt (Real.log R) := by
    intro u hu
    have huV := (Finset.mem_filter.mp hu).1
    have hum := (Finset.mem_filter.mp hu).2
    obtain ⟨hu1, hu_prod, hu_sf_prod, hu_cop_prod⟩ := (mem_validTupleSet hR_pos.le).mp huV
    have hu_sf : ∀ i, Squarefree (u i) := fun i => (squarefree_prod_coord hu_sf_prod).1 i (Finset.mem_univ i)
    have hu_cop : ∀ i, Nat.Coprime (u i) W₀ := fun i =>
      hu_cop_prod.coprime_dvd_left (Finset.dvd_prod_of_mem u (Finset.mem_univ i))
    have hu_prod_eq : ∏ i ∈ Em, u i = ∏ i, u i := by
      have h := Finset.mul_prod_erase Finset.univ u (Finset.mem_univ m)
      rw [hum, one_mul] at h; exact h
    -- Express `yMVar` via `yMVar_eq_sum_yVar` and split `t` into `q = 1` vs `q ≠ 1`
    rw [yMVar_eq_sum_yVar W₀ hR1 T m u huV hum]
    set P_u : ℝ := ∏ i ∈ Em, ((g₂ (u i) : ℝ) * (u i : ℝ) / ((u i).totient : ℝ) ^ 2)
    set filt := (validTupleSet k W₀ R).filter (fun t => ∀ i ∈ Em, u i ∣ t i)
    set filt1 := filt.filter (fun t => ∀ i ∈ Em, t i = u i)
    set filtTail := filt.filter (fun t => ¬ ∀ i ∈ Em, t i = u i)
    have hsplit_t : ∑ t ∈ filt, (yVar W₀ R T t / ((t m).totient : ℝ)) *
          ∏ i ∈ Em, ((μ (t i / u i) : ℝ) / (((t i / u i).totient : ℝ) ^ 2)) =
        (∑ t ∈ filt1, yVar W₀ R T t / ((t m).totient : ℝ)) +
        (∑ t ∈ filtTail, (yVar W₀ R T t / ((t m).totient : ℝ)) *
          ∏ i ∈ Em, ((μ (t i / u i) : ℝ) / (((t i / u i).totient : ℝ) ^ 2))) := by
      rw [← Finset.sum_filter_add_sum_filter_not filt (fun t => ∀ i ∈ Em, t i = u i)]
      congr 1
      refine Finset.sum_congr rfl fun t ht => ?_
      have heq := (Finset.mem_filter.mp ht).2
      have hpr : ∏ i ∈ Em, ((μ (t i / u i) : ℝ) / (((t i / u i).totient : ℝ) ^ 2)) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        rw [heq i hi, Nat.div_self (hu1 i)]; simp
      rw [hpr, mul_one]
    set MainT : ℝ := ∑ t ∈ filt1, yVar W₀ R T t / ((t m).totient : ℝ)
    set TailT : ℝ := ∑ t ∈ filtTail, (yVar W₀ R T t / ((t m).totient : ℝ)) *
      ∏ i ∈ Em, ((μ (t i / u i) : ℝ) / (((t i / u i).totient : ℝ) ^ 2))
    -- (a) `0 ≤ P_u ≤ 1` and `1 - P_u ≤ δ`
    have hPu_nn : 0 ≤ P_u := Finset.prod_nonneg fun _ _ => by positivity
    have hPu_le1 : P_u ≤ 1 := by
      refine Finset.prod_le_one (fun _ _ => by positivity) fun i _ => ?_
      have hphi_pos : (0 : ℝ) < ((u i).totient : ℝ) ^ 2 :=
        sq_pos_of_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr (hu1 i)))
      rw [div_le_one hphi_pos]
      exact_mod_cast g2_mul_self_le_totient_sq (hu_sf i) ((hu_cop i).coprime_dvd_right h2W)
    have h1subPu : 1 - P_u ≤ δ := by
      -- Since `∏_{i ∈ Em} u i = ∏ u i` is squarefree and pairwise coprime, `P_u = g₂(∏ u) * (∏ u) / φ(∏ u)²`!
      have hprod_ne : ∀ i ∈ Em, u i ≠ 0 := fun i _ => Nat.ne_of_gt (hu1 i)
      have hpair := (squarefree_prod_coord hu_sf_prod).2
      have hPu_eq : P_u = (g₂ (∏ i, u i) : ℝ) * ((∏ i, u i : ℕ) : ℝ) / (((∏ i, u i).totient : ℝ) ^ 2) := by
        rw [← hu_prod_eq, g₂_prod_of_pairwise_coprime Em u hprod_ne (fun i _ j _ h => hpair i (Finset.mem_univ i) j (Finset.mem_univ j) h),
          totient_prod_of_pairwise_coprime Em u (fun i _ j _ h => hpair i (Finset.mem_univ i) j (Finset.mem_univ j) h)]
        rw [Nat.cast_prod, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_div_distrib]
      rw [hPu_eq]
      calc 1 - (g₂ (∏ i, u i) : ℝ) * ((∏ i, u i : ℕ) : ℝ) / (((∏ i, u i).totient : ℝ) ^ 2)
          ≤ ∑ p ∈ (∏ i, u i).primeFactors, (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
            one_sub_g2_mul_div_totient_sq_le hD hu_sf_prod hu_cop_prod
        _ ≤ ∑ p ∈ (Finset.Icc (D₀ + 1) ⌊R⌋₊).filter Nat.Prime, (((p - 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
            have hsubP : (∏ i, u i).primeFactors ⊆ (Finset.Icc (D₀ + 1) ⌊R⌋₊).filter Nat.Prime := by
              intro p hp
              have hpp := Nat.prime_of_mem_primeFactors hp
              have hpu := Nat.dvd_of_mem_primeFactors hp
              have hpD : D₀ < p := by
                by_contra hle; push Not at hle
                exact hpp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hu_cop_prod) ▸
                  Nat.dvd_gcd hpu ((prime_dvd_W_iff hpp).mpr hle))
              have hpos : 0 < ∏ i, u i := Finset.prod_pos fun i _ => hu1 i
              exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,
                Nat.le_floor ((Nat.cast_le.mpr (Nat.le_of_dvd hpos hpu)).trans hu_prod)⟩, hpp⟩
            calc ∑ p ∈ (∏ i, u i).primeFactors, (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹
                ≤ ∑ p ∈ (∏ i, u i).primeFactors, (((p - 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
                  refine Finset.sum_le_sum fun p hp => ?_
                  have hp5 : 5 ≤ p := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hsubP hp)).1).1; omega
                  exact inv_anti₀ (sq_pos_of_pos (Nat.cast_pos.mpr (by omega)))
                    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show p - 2 ≤ p - 1 by omega)) 2)
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubP fun _ _ _ => by positivity
        _ ≤ δ := by
            have h1 := sum_inv_sub_two_sq_le (D₀ := D₀) (M := ⌊R⌋₊) (by omega)
            have hDpos : (0 : ℝ) < ((D₀ - 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
            have h2 : 1 / ((D₀ - 2 : ℕ) : ℝ) ≤ 2 / ((D₀ - 2 : ℕ) : ℝ) := by
              rw [div_le_div_iff_of_pos_right hDpos]; norm_num
            exact h1.trans h2
    -- (b) Piece A: `|P_u * TailT| ≤ T.bound * A_phi * ((1 + δ)^k - 1)`
    have hTail : |TailT| ≤ T.bound * A_phi * ((1 + δ) ^ k - 1) := by
      let emb : (Fin (k + 1) → ℕ) → ℕ × (↥Em → ℕ) := fun t => (t m, fun i => t i.1 / u i.1)
      let q1 : ↥Em → ℕ := fun _ => 1
      have hq1_mem : q1 ∈ Fintype.piFinset (fun _ : ↥Em => S_sf) := by
        rw [Fintype.mem_piFinset]; intro _
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by dsimp only [q1]; exact_mod_cast hR1)⟩,
          squarefree_one, Nat.coprime_one_left _⟩
      have hinj : Set.InjOn emb filtTail := by
        intro t₁ ht₁ t₂ ht₂ heq
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp ht₁).1).2
        have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp ht₂).1).2
        ext i
        by_cases hi : i = m
        · subst hi; exact congrArg Prod.fst heq
        · have hi' : i ∈ Em := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
          have hq : t₁ i / u i = t₂ i / u i := congrFun (congrArg Prod.snd heq) ⟨i, hi'⟩
          rw [← Nat.mul_div_cancel' (h1 i hi'), ← Nat.mul_div_cancel' (h2 i hi'), hq]
      have hsub : filtTail.image emb ⊆ S_sf ×ˢ (Fintype.piFinset (fun _ : ↥Em => S_sf)).erase q1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
        have htF := (Finset.mem_filter.mp ht).1
        have hnot1 := (Finset.mem_filter.mp ht).2
        have htV := (Finset.mem_filter.mp htF).1
        have hut := (Finset.mem_filter.mp htF).2
        obtain ⟨ht1, ht_prod, ht_sf_prod, ht_cop_prod⟩ := (mem_validTupleSet hR_pos.le).mp htV
        have ht_sf : ∀ i, Squarefree (t i) := fun i => (squarefree_prod_coord ht_sf_prod).1 i (Finset.mem_univ i)
        have ht_cop : ∀ i, Nat.Coprime (t i) W₀ := fun i =>
          ht_cop_prod.coprime_dvd_left (Finset.dvd_prod_of_mem t (Finset.mem_univ i))
        have ht_le : ∀ i, t i ≤ ⌊R⌋₊ := fun i => Nat.le_floor <|
          le_trans (by exact_mod_cast Finset.single_le_prod' (f := t) (fun j _ => ht1 j) (Finset.mem_univ i)) ht_prod
        rw [Finset.mem_product, Finset.mem_erase, Fintype.mem_piFinset]
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht1 m, ht_le m⟩, ht_sf m, ht_cop m⟩, ?_, fun i => ?_⟩
        · intro heq1; apply hnot1; intro i hi
          have hqi : t i / u i = 1 := congrFun heq1 ⟨i, hi⟩
          rw [← Nat.mul_div_cancel' (hut i hi), hqi, mul_one]
        · have hdvd : t i.1 / u i.1 ∣ t i.1 := Nat.div_dvd_of_dvd (hut i.1 i.2)
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (ht1 i.1) (hut i.1 i.2)) (hu1 i.1),
            (Nat.div_le_self _ _).trans (ht_le i.1)⟩,
            (ht_sf i.1).squarefree_of_dvd hdvd, (ht_cop i.1).coprime_dvd_left hdvd⟩
      have hmu_le1 : ∀ n : ℕ, |(μ n : ℝ)| ≤ 1 := fun n => by
        by_cases hsf : Squarefree n
        · rw [moebius_eq_prod_neg_one_of_squarefree hsf, Finset.abs_prod]; simp
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
      have hcard_Em : Fintype.card ↥Em = k := by
        rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]; omega
      have hsum_q : ∑ q ∈ (Fintype.piFinset (fun _ : ↥Em => S_sf)).erase q1,
            ∏ i : ↥Em, (((q i).totient : ℝ) ^ 2)⁻¹ ≤ (1 + δ) ^ k - 1 := by
        have hfull : ∑ q ∈ Fintype.piFinset (fun _ : ↥Em => S_sf),
              ∏ i : ↥Em, (((q i).totient : ℝ) ^ 2)⁻¹ =
            (∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹) ^ k := by
          rw [sum_piFinset_prod (fun _ : ↥Em => S_sf) (fun _ n => (((n.totient : ℝ) ^ 2))⁻¹),
            Finset.prod_const, Finset.card_univ, hcard_Em]
        have hsp := Finset.add_sum_erase (Fintype.piFinset (fun _ : ↥Em => S_sf))
          (fun q => ∏ i : ↥Em, (((q i).totient : ℝ) ^ 2)⁻¹) hq1_mem
        have hq1_val : ∏ i : ↥Em, (((q1 i).totient : ℝ) ^ 2)⁻¹ = 1 := by simp [q1]
        rw [hq1_val] at hsp
        have h1d : ∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹ ≤ 1 + δ := by
          calc ∑ n ∈ S_sf, (((n.totient : ℝ) ^ 2))⁻¹
              ≤ ∑ n ∈ S_sf, (((g₂ n : ℝ) ^ 2))⁻¹ := by
                refine Finset.sum_le_sum fun n hn => ?_
                have hsf := (Finset.mem_filter.mp hn).2.1
                have hcop := (Finset.mem_filter.mp hn).2.2
                have hgpos : (0 : ℝ) < (g₂ n : ℝ) :=
                  Nat.cast_pos.mpr (g₂_pos_of_coprime_two hsf.ne_zero (hcop.coprime_dvd_right h2W))
                exact inv_anti₀ (sq_pos_of_pos hgpos)
                  (pow_le_pow_left₀ hgpos.le (by exact_mod_cast g₂_le_totient_of_squarefree hsf) 2)
            _ ≤ 1 + δ := sum_inv_g2_sq_le hD
        have hpow := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) h1d k
        linarith
      calc |TailT|
          ≤ ∑ t ∈ filtTail, T.bound * (((emb t).1.totient : ℝ)⁻¹ *
              ∏ i : ↥Em, ((((emb t).2 i).totient : ℝ) ^ 2)⁻¹) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
            rw [abs_mul, abs_div, abs_of_nonneg (a := ((t m).totient : ℝ)) (Nat.cast_nonneg _),
              Finset.abs_prod, ← Finset.prod_attach Em]
            have hpr : ∏ i ∈ Em.attach, |(μ (t i.1 / u i.1) : ℝ) / (((t i.1 / u i.1).totient : ℝ) ^ 2)| ≤
                ∏ i : ↥Em, ((((emb t).2 i).totient : ℝ) ^ 2)⁻¹ := by
              refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_
              rw [abs_div, abs_of_nonneg (a := (((t i.1 / u i.1).totient : ℝ) ^ 2)) (sq_nonneg _), div_eq_mul_inv]
              calc |(μ (t i.1 / u i.1) : ℝ)| * (((t i.1 / u i.1).totient : ℝ) ^ 2)⁻¹
                  ≤ 1 * (((t i.1 / u i.1).totient : ℝ) ^ 2)⁻¹ := by gcongr; exact hmu_le1 _
                _ = _ := one_mul _
            calc |yVar W₀ R T t| / ((t m).totient : ℝ) *
                  ∏ i ∈ Em.attach, |(μ (t i.1 / u i.1) : ℝ) / (((t i.1 / u i.1).totient : ℝ) ^ 2)|
                ≤ (T.bound / ((t m).totient : ℝ)) * ∏ i : ↥Em, ((((emb t).2 i).totient : ℝ) ^ 2)⁻¹ :=
                  mul_le_mul (div_le_div_of_nonneg_right (abs_yVar_le W₀ hR T t) (Nat.cast_nonneg _)) hpr
                    (Finset.prod_nonneg fun _ _ => abs_nonneg _) (div_nonneg T.bound_nonneg (Nat.cast_nonneg _))
              _ = _ := by dsimp only [emb]; ring
        _ = T.bound * ∑ x ∈ filtTail.image emb,
              ((x.1.totient : ℝ)⁻¹ * ∏ i : ↥Em, (((x.2 i).totient : ℝ) ^ 2)⁻¹) := by
            rw [← Finset.mul_sum, Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
        _ ≤ T.bound * ∑ x ∈ S_sf ×ˢ (Fintype.piFinset (fun _ : ↥Em => S_sf)).erase q1,
              ((x.1.totient : ℝ)⁻¹ * ∏ i : ↥Em, (((x.2 i).totient : ℝ) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
                mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => by positivity)) T.bound_nonneg
        _ = T.bound * ((∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹) *
              ∑ q ∈ (Fintype.piFinset (fun _ : ↥Em => S_sf)).erase q1,
                ∏ i : ↥Em, (((q i).totient : ℝ) ^ 2)⁻¹) := by
            rw [Finset.sum_product]; dsimp only
            congr 1; exact (Finset.sum_mul_sum _ _ _ _).symm
        _ ≤ T.bound * (A_phi * ((1 + δ) ^ k - 1)) := by
            have h1d : ∑ n ∈ S_sf, ((n.totient : ℝ))⁻¹ = A_phi := by
              unfold A_phi aPhi; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
            rw [h1d]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_q hAphi_nn) T.bound_nonneg
        _ = T.bound * A_phi * ((1 + δ) ^ k - 1) := by ring
    -- (c) Rewrite `MainT` as a 1D sum over `t_m ≤ R^s_u` with `Coprime t_m (∏ u)`
    set s_u : ℝ := 1 - ∑ j : Fin k, Real.log (u (m.succAbove j) : ℝ) / Real.log R
    have hprod_pos : (0 : ℝ) < ((∏ i, u i : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Finset.prod_pos fun i _ => hu1 i)
    have hRsu_eq : R ^ s_u = R / ((∏ i, u i : ℕ) : ℝ) := by
      have hsum_eq : ∑ j : Fin k, Real.log (u (m.succAbove j) : ℝ) / Real.log R =
          Real.log ((∏ i, u i : ℕ) : ℝ) / Real.log R := by
        rw [← Finset.sum_div]
        congr 1
        have hpeq : ∏ j : Fin k, (u (m.succAbove j) : ℝ) = ((∏ i, u i : ℕ) : ℝ) := by
          rw [Fin.prod_univ_succAbove u m, hum, one_mul, Nat.cast_prod]
        rw [← Real.log_prod fun j _ => (Nat.cast_pos.mpr (hu1 _)).ne', hpeq]
      dsimp only [s_u]; rw [hsum_eq, Real.rpow_def_of_pos hR_pos]
      have hexp : Real.log R * (1 - Real.log ((∏ i, u i : ℕ) : ℝ) / Real.log R) =
          Real.log (R / ((∏ i, u i : ℕ) : ℝ)) := by
        rw [Real.log_div hR_pos.ne' hprod_pos.ne']
        field_simp [hlogR_pos.ne']
      rw [hexp, Real.exp_log (div_pos hR_pos hprod_pos)]
    have hsu0 : 0 ≤ s_u := by
      have h1 : 1 ≤ R / ((∏ i, u i : ℕ) : ℝ) := (one_le_div hprod_pos).mpr hu_prod
      have hlog := Real.log_nonneg h1
      rw [← hRsu_eq, Real.log_rpow hR_pos] at hlog
      exact nonneg_of_mul_nonneg_left hlog hlogR_pos
    have hsu1 : s_u ≤ 1 := by
      have : 0 ≤ ∑ j : Fin k, Real.log (u (m.succAbove j) : ℝ) / Real.log R :=
        Finset.sum_nonneg fun j _ => div_nonneg (Real.log_nonneg (by exact_mod_cast hu1 _)) hlogR_pos.le
      dsimp only [s_u]; linarith
    let f_u : ℝ → ℝ := fun t =>
      T.F (Fin.cons t (fun j : Fin k => Real.log (u (m.succAbove j) : ℝ) / Real.log R))
    have hMainT_eq : MainT =
        ∑ n ∈ (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => Nat.Coprime n (∏ i, u i)),
          aPhi W₀ n * f_u (Real.log (n : ℝ) / Real.log R) := by
      symm
      refine Finset.sum_bij_ne_zero (fun n _ _ => Function.update u m n) ?_ ?_ ?_ ?_
      · intro n hn hne
        have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hncop_u := (Finset.mem_filter.mp hn).2
        have hnsfc : Squarefree n ∧ Nat.Coprime n W₀ := by
          by_contra hnot
          have : aPhi W₀ n = 0 := by unfold aPhi; rw [if_neg hnot]
          exact hne (by simp [this])
        have hprod_upd : ∏ i, Function.update u m n i = n * ∏ i, u i := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Function.update_self]
          congr 1
          rw [← hu_prod_eq]
          refine Finset.prod_congr rfl fun i hi => Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _
        have hupd_V : Function.update u m n ∈ validTupleSet k W₀ R := by
          rw [mem_validTupleSet hR_pos.le]
          refine ⟨fun i => by by_cases hi : i = m <;> simp [hi, hnI.1, hu1], ?_, ?_, ?_⟩
          · rw [hprod_upd, Nat.cast_mul]
            have hnR : (n : ℝ) ≤ R / ((∏ i, u i : ℕ) : ℝ) := by
              rw [← hRsu_eq]; exact (Nat.cast_le.mpr hnI.2).trans (Nat.floor_le (by positivity))
            exact (le_div_iff₀ hprod_pos).mp hnR
          · rw [hprod_upd]
            exact (Nat.squarefree_mul hncop_u).mpr ⟨hnsfc.1, hu_sf_prod⟩
          · rw [hprod_upd]; exact hnsfc.2.mul_left hu_cop_prod
        simp only [filt1, filt, Finset.mem_filter]
        refine ⟨⟨hupd_V, fun i hi => by rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]⟩,
          fun i hi => Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _⟩
      · intro n₁ _ _ n₂ _ _ heq
        have := congrFun heq m; simpa using this
      · intro t ht hne
        have htF := (Finset.mem_filter.mp ht).1
        have hteq := (Finset.mem_filter.mp ht).2
        have htV := (Finset.mem_filter.mp htF).1
        obtain ⟨ht1, ht_prod, ht_sf_prod, ht_cop_prod⟩ := (mem_validTupleSet hR_pos.le).mp htV
        have hprod_t : ∏ i, t i = t m * ∏ i, u i := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), ← hu_prod_eq]
          congr 1; exact Finset.prod_congr rfl hteq
        have htm_le : t m ≤ ⌊R ^ s_u⌋₊ := by
          refine Nat.le_floor ?_
          rw [hRsu_eq, le_div_iff₀ hprod_pos]
          rw [hprod_t, Nat.cast_mul] at ht_prod; exact ht_prod
        have htm_cop_u : Nat.Coprime (t m) (∏ i, u i) :=
          Nat.coprime_of_squarefree_mul (hprod_t ▸ ht_sf_prod)
        have htm_mem : t m ∈ (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => Nat.Coprime n (∏ i, u i)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht1 m, htm_le⟩, htm_cop_u⟩
        have hupd_eq : Function.update u m (t m) = t := by
          ext i; by_cases hi : i = m
          · subst hi; simp
          · rw [Function.update_of_ne hi, hteq i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)]
        have hval_eq : aPhi W₀ (t m) * f_u (Real.log (t m : ℝ) / Real.log R) =
            yVar W₀ R T t / ((t m).totient : ℝ) := by
          unfold aPhi yVar
          have hsfm := (squarefree_prod_coord ht_sf_prod).1 m (Finset.mem_univ m)
          have hcopm := ht_cop_prod.coprime_dvd_left (Finset.dvd_prod_of_mem t (Finset.mem_univ m))
          rw [if_pos ⟨hsfm, hcopm⟩, if_pos htV]
          have hFeq : f_u (Real.log (t m : ℝ) / Real.log R) = T.F (fun i => Real.log (t i : ℝ) / Real.log R) := by
            dsimp only [f_u]
            rw [← T.symm (permM m) (fun i => Real.log (t i : ℝ) / Real.log R)]
            congr 1; funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [permM_zero]
            · simp only [Function.comp_apply, Fin.cons_succ, permM_succ]
              rw [hteq (m.succAbove j) (Finset.mem_erase.mpr ⟨Fin.succAbove_ne m j, Finset.mem_univ _⟩)]
          rw [hFeq]; ring
        exact ⟨t m, htm_mem, by rw [hval_eq]; exact hne, hupd_eq⟩
      · intro n hn hne
        have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hncop_u := (Finset.mem_filter.mp hn).2
        have hnsfc : Squarefree n ∧ Nat.Coprime n W₀ := by
          by_contra hnot
          have : aPhi W₀ n = 0 := by unfold aPhi; rw [if_neg hnot]
          exact hne (by simp [this])
        have hprod_upd : ∏ i, Function.update u m n i = n * ∏ i, u i := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Function.update_self, ← hu_prod_eq]
          congr 1; exact Finset.prod_congr rfl fun i hi => Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _
        have hupd_V : Function.update u m n ∈ validTupleSet k W₀ R := by
          rw [mem_validTupleSet hR_pos.le]
          refine ⟨fun i => by by_cases hi : i = m <;> simp [hi, hnI.1, hu1], ?_, ?_, ?_⟩
          · rw [hprod_upd, Nat.cast_mul]
            have hnR : (n : ℝ) ≤ R / ((∏ i, u i : ℕ) : ℝ) := by
              rw [← hRsu_eq]; exact (Nat.cast_le.mpr hnI.2).trans (Nat.floor_le (by positivity))
            exact (le_div_iff₀ hprod_pos).mp hnR
          · rw [hprod_upd]; exact (Nat.squarefree_mul hncop_u).mpr ⟨hnsfc.1, hu_sf_prod⟩
          · rw [hprod_upd]; exact hnsfc.2.mul_left hu_cop_prod
        unfold aPhi yVar
        rw [if_pos hnsfc, if_pos hupd_V, Function.update_self]
        have hFeq : f_u (Real.log (n : ℝ) / Real.log R) =
            T.F (fun i => Real.log (Function.update u m n i : ℝ) / Real.log R) := by
          dsimp only [f_u]
          rw [← T.symm (permM m) (fun i => Real.log (Function.update u m n i : ℝ) / Real.log R)]
          congr 1; funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [permM_zero]
          · simp only [Function.comp_apply, Fin.cons_succ, permM_succ]
            rw [Function.update_of_ne (Fin.succAbove_ne m j)]
        rw [hFeq]; ring
    -- Bound `|MainT| ≤ T.bound * A_phi` (for Piece B)
    have hMainT_abs : |MainT| ≤ T.bound * A_phi := by
      rw [hMainT_eq]
      have hfloor_le : ⌊R ^ s_u⌋₊ ≤ ⌊R⌋₊ := Nat.floor_mono (by
        calc R ^ s_u ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 hsu1
          _ = R := Real.rpow_one R)
      have hsubI : (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => Nat.Coprime n (∏ i, u i)) ⊆ Finset.Icc 1 ⌊R⌋₊ :=
        fun n hn => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1,
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2.trans hfloor_le⟩
      calc |∑ n ∈ (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => Nat.Coprime n (∏ i, u i)),
              aPhi W₀ n * f_u (Real.log (n : ℝ) / Real.log R)|
          ≤ ∑ n ∈ (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => Nat.Coprime n (∏ i, u i)),
              aPhi W₀ n * T.bound := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
            rw [abs_mul, abs_of_nonneg (aPhi_nonneg _ _)]
            refine mul_le_mul_of_nonneg_left ?_ (aPhi_nonneg _ _)
            have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
            have ht0 : 0 ≤ Real.log (n : ℝ) / Real.log R :=
              div_nonneg (Real.log_nonneg (by exact_mod_cast hnI.1)) hlogR_pos.le
            have hts : Real.log (n : ℝ) / Real.log R ≤ s_u := by
              rw [div_le_iff₀ hlogR_pos, ← Real.log_rpow hR_pos]
              exact Real.log_le_log (Nat.cast_pos.mpr hnI.1)
                ((Nat.cast_le.mpr hnI.2).trans (Nat.floor_le (by positivity)))
            have hin : InSimplex 1 (Fin.cons (Real.log (n : ℝ) / Real.log R)
                (fun j : Fin k => Real.log (u (m.succAbove j) : ℝ) / Real.log R)) :=
              inSimplex_cons ht0 ⟨fun j => div_nonneg (Real.log_nonneg (by exact_mod_cast hu1 _)) hlogR_pos.le,
                by dsimp only [s_u] at hts; linarith⟩
            exact T.isSimplexLipOn.2.2.1 _ hin
        _ ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aPhi W₀ n * T.bound :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubI fun _ _ _ => mul_nonneg (aPhi_nonneg _ _) T.bound_nonneg
        _ = T.bound * A_phi := by rw [← Finset.sum_mul, mul_comm]
    -- (d) Piece C: `|MainT - UnfilteredMainT| ≤ T.bound * A_phi * ∑_{i ∈ Em} ∑_{p ∣ u i} (p - 1)⁻¹`
    set UnfT : ℝ := ∑ n ∈ Finset.Icc 1 ⌊R ^ s_u⌋₊, aPhi W₀ n * f_u (Real.log (n : ℝ) / Real.log R)
    have hPieceC : |MainT - UnfT| ≤
        T.bound * A_phi * ∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹ := by
      have hdiff_eq : UnfT - MainT =
          ∑ n ∈ (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => ¬ Nat.Coprime n (∏ i, u i)),
            aPhi W₀ n * f_u (Real.log (n : ℝ) / Real.log R) := by
        dsimp only [UnfT]; rw [hMainT_eq]
        have hsp := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊R ^ s_u⌋₊)
          (fun n => Nat.Coprime n (∏ i, u i)) (fun n => aPhi W₀ n * f_u (Real.log (n : ℝ) / Real.log R))
        linarith
      rw [abs_sub_comm, hdiff_eq]
      have hfloor_le : ⌊R ^ s_u⌋₊ ≤ ⌊R⌋₊ := Nat.floor_mono (by
        calc R ^ s_u ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 hsu1
          _ = R := Real.rpow_one R)
      have hcov : (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => ¬ Nat.Coprime n (∏ i, u i)) ⊆
          (∏ i, u i).primeFactors.biUnion (fun p => (Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n)) := by
        intro n hn
        have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hnc := (Finset.mem_filter.mp hn).2
        obtain ⟨p, hpp, hpgcd⟩ := Nat.exists_prime_and_dvd hnc
        exact Finset.mem_biUnion.mpr ⟨p,
          Nat.mem_primeFactors.mpr ⟨hpp, dvd_trans hpgcd (Nat.gcd_dvd_right _ _), hu_sf_prod.ne_zero⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnI.1, hnI.2.trans hfloor_le⟩,
            dvd_trans hpgcd (Nat.gcd_dvd_left _ _)⟩⟩
      have hdiv_p : ∀ p ∈ (∏ i, u i).primeFactors,
          ∑ n ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n), aPhi W₀ n ≤
            (((p - 1 : ℕ) : ℝ))⁻¹ * A_phi := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hterm : ∀ n ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n),
            aPhi W₀ n ≤ (((p - 1 : ℕ) : ℝ))⁻¹ * aPhi W₀ (n / p) := by
          intro n hn
          have hpn := (Finset.mem_filter.mp hn).2
          unfold aPhi; split_ifs with h1 h2
          · have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
            have hcop : Nat.Coprime p (n / p) := Nat.coprime_of_squarefree_mul (hmul.symm ▸ h1.1)
            conv_lhs => rw [← hmul]
            rw [Nat.totient_mul hcop, Nat.totient_prime hpp, Nat.cast_mul, mul_inv]
          · exfalso
            have hdvd : n / p ∣ n := Nat.div_dvd_of_dvd hpn
            exact h2 ⟨h1.1.squarefree_of_dvd hdvd, h1.2.coprime_dvd_left hdvd⟩
          · positivity
          · positivity
        have hinj : Set.InjOn (fun n => n / p) ((Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n)) := by
          intro n₁ hn₁ n₂ hn₂ heq
          dsimp only at heq
          rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2,
            ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2, heq]
        have hsub : ((Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n)).image (fun n => n / p) ⊆ Finset.Icc 1 ⌊R⌋₊ := by
          intro c hc
          rcases Finset.mem_image.mp hc with ⟨n, hn, rfl⟩
          have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
          exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd h1.1 (Finset.mem_filter.mp hn).2) hpp.pos,
            (Nat.div_le_self _ _).trans h1.2⟩
        calc ∑ n ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n), aPhi W₀ n
            ≤ (((p - 1 : ℕ) : ℝ))⁻¹ * ∑ n ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n), aPhi W₀ (n / p) := by
              rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
          _ = (((p - 1 : ℕ) : ℝ))⁻¹ * ∑ c ∈ ((Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n)).image (fun n => n / p),
                aPhi W₀ c := by
              congr 1; exact (Finset.sum_image (f := aPhi W₀) (fun a ha b hb hab => hinj ha hb hab)).symm
          _ ≤ (((p - 1 : ℕ) : ℝ))⁻¹ * A_phi :=
              mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => aPhi_nonneg _ _) (by positivity)
      have hpf_sum : ∑ p ∈ (∏ i, u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹ ≤
          ∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹ := by
        have hsub_pf : (∏ i, u i).primeFactors ⊆ Em.biUnion (fun i => (u i).primeFactors) := by
          intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hpdvd : p ∣ ∏ i ∈ Em, u i := hu_prod_eq.symm ▸ Nat.dvd_of_mem_primeFactors hp
          obtain ⟨i, hi, hpi⟩ := hpp.prime.exists_mem_finset_dvd hpdvd
          exact Finset.mem_biUnion.mpr ⟨i, hi, Nat.mem_primeFactors.mpr ⟨hpp, hpi, Nat.ne_of_gt (hu1 i)⟩⟩
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub_pf fun _ _ _ => by positivity).trans
          (sum_biUnion_le_of_nonneg fun _ => by positivity)
      calc |∑ n ∈ (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => ¬ Nat.Coprime n (∏ i, u i)),
              aPhi W₀ n * f_u (Real.log (n : ℝ) / Real.log R)|
          ≤ ∑ n ∈ (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => ¬ Nat.Coprime n (∏ i, u i)),
              T.bound * aPhi W₀ n := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
            rw [abs_mul, abs_of_nonneg (aPhi_nonneg _ _), mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (aPhi_nonneg _ _)
            have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
            have ht0 : 0 ≤ Real.log (n : ℝ) / Real.log R :=
              div_nonneg (Real.log_nonneg (by exact_mod_cast hnI.1)) hlogR_pos.le
            have hts : Real.log (n : ℝ) / Real.log R ≤ s_u := by
              rw [div_le_iff₀ hlogR_pos, ← Real.log_rpow hR_pos]
              exact Real.log_le_log (Nat.cast_pos.mpr hnI.1)
                ((Nat.cast_le.mpr hnI.2).trans (Nat.floor_le (by positivity)))
            exact T.isSimplexLipOn.2.2.1 _ (inSimplex_cons ht0
              ⟨fun j => div_nonneg (Real.log_nonneg (by exact_mod_cast hu1 _)) hlogR_pos.le,
                by dsimp only [s_u] at hts; linarith⟩)
        _ = T.bound * ∑ n ∈ (Finset.Icc 1 ⌊R ^ s_u⌋₊).filter (fun n => ¬ Nat.Coprime n (∏ i, u i)),
              aPhi W₀ n := by rw [← Finset.mul_sum]
        _ ≤ T.bound * ∑ n ∈ (∏ i, u i).primeFactors.biUnion (fun p => (Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n)),
              aPhi W₀ n :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => aPhi_nonneg _ _) T.bound_nonneg
        _ ≤ T.bound * ∑ p ∈ (∏ i, u i).primeFactors, ∑ n ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun n => p ∣ n),
              aPhi W₀ n :=
            mul_le_mul_of_nonneg_left (sum_biUnion_le_of_nonneg fun _ => aPhi_nonneg _ _) T.bound_nonneg
        _ ≤ T.bound * ∑ p ∈ (∏ i, u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹ * A_phi :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hdiv_p) T.bound_nonneg
        _ = T.bound * A_phi * ∑ p ∈ (∏ i, u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹ := by
            rw [← Finset.sum_mul]; ring
        _ ≤ T.bound * A_phi * ∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_left hpf_sum (mul_nonneg T.bound_nonneg hAphi_nn)
    -- (e) Piece D: `|UnfT - yMain u| ≤ K_1d * √(log R)` via `sum_1d_approx_integral`!
    have hPieceD : |UnfT - yMain u| ≤ K_1d * Real.sqrt (Real.log R) := by
      have hf_bd : ∀ t ∈ Set.Icc (0 : ℝ) s_u, |f_u t| ≤ T.bound := fun t ht =>
        T.isSimplexLipOn.2.2.1 _ (inSimplex_cons ht.1
          ⟨fun j => div_nonneg (Real.log_nonneg (by exact_mod_cast hu1 _)) hlogR_pos.le,
            by dsimp only [s_u] at ht; linarith [ht.2]⟩)
      have hf_lip : ∀ t₁ ∈ Set.Icc (0 : ℝ) s_u, ∀ t₂ ∈ Set.Icc (0 : ℝ) s_u,
          |f_u t₁ - f_u t₂| ≤ (T.lip + T.bound) * |t₁ - t₂| := fun t₁ ht₁ t₂ ht₂ => by
        let w : Fin k → ℝ := fun j => Real.log (u (m.succAbove j) : ℝ) / Real.log R
        have hin1 : InSimplex 1 (Fin.cons t₁ w) := inSimplex_cons ht₁.1
          ⟨fun j => div_nonneg (Real.log_nonneg (by exact_mod_cast hu1 _)) hlogR_pos.le,
            by dsimp only [s_u, w] at ht₁ ⊢; linarith [ht₁.2]⟩
        have hin2 : InSimplex 1 (Fin.cons t₂ w) := inSimplex_cons ht₂.1
          ⟨fun j => div_nonneg (Real.log_nonneg (by exact_mod_cast hu1 _)) hlogR_pos.le,
            by dsimp only [s_u, w] at ht₂ ⊢; linarith [ht₂.2]⟩
        have hd := T.isSimplexLipOn.2.2.2 _ _ hin1 hin2
        rw [Fin.sum_univ_succ] at hd
        simp only [Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero, Finset.sum_const_zero, add_zero] at hd
        exact hd.trans (mul_le_mul_of_nonneg_right (by linarith [T.bound_nonneg]) (abs_nonneg _))
      have h1d := sum_1d_approx_integral (aPhi_nonneg W₀) hcW_nn hC_phi.le hphi_asymp
        hsu0 hsu1 T.bound_nonneg (add_nonneg T.lip_nonneg T.bound_nonneg) hR hf_bd hf_lip
      have hyM_eq : yMain u = cW * Real.log R * ∫ t in (0 : ℝ)..s_u, f_u t := rfl
      rw [hyM_eq]
      exact h1d
    -- Combine Pieces A, B, C, D via triangle inequality!
    rw [hsplit_t]
    have hrew : P_u * (MainT + TailT) - yMain u =
        P_u * TailT + (P_u - 1) * MainT + (MainT - UnfT) + (UnfT - yMain u) := by ring
    rw [hrew]
    have hAB : |P_u * TailT| ≤ T.bound * A_phi * ((1 + δ) ^ k - 1) := by
      rw [abs_mul, abs_of_nonneg hPu_nn]
      calc P_u * |TailT| ≤ 1 * (T.bound * A_phi * ((1 + δ) ^ k - 1)) :=
            mul_le_mul hPu_le1 hTail (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hB : |(P_u - 1) * MainT| ≤ T.bound * A_phi * δ := by
      rw [abs_mul, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 1 - P_u)]
      calc (1 - P_u) * |MainT| ≤ δ * (T.bound * A_phi) :=
            mul_le_mul h1subPu hMainT_abs (abs_nonneg _) hδ_nn
        _ = T.bound * A_phi * δ := by ring
    have htri1 := abs_add_le (P_u * TailT + (P_u - 1) * MainT + (MainT - UnfT)) (UnfT - yMain u)
    have htri2 := abs_add_le (P_u * TailT + (P_u - 1) * MainT) (MainT - UnfT)
    have htri3 := abs_add_le (P_u * TailT) ((P_u - 1) * MainT)
    linarith
  -- Step 2: Apply `x² ≥ y² - 2 |y| |x - y|` on `Vm` and sum against `1 / ∏_{i ∈ Em} g₂(u i)`
  set Uset : Finset (↥Em → ℕ) := Fintype.piFinset (fun _ : ↥Em => S_sf)
  have hsum_Vm_g2 : ∑ u ∈ Vm, (∏ i ∈ Em, (g₂ (u i) : ℝ))⁻¹ ≤ (2 : ℝ) ^ k * A_phi ^ k := by
    let proj : (Fin (k + 1) → ℕ) → (↥Em → ℕ) := fun u i => u i.1
    have hinj : Set.InjOn proj Vm := by
      intro u₁ hu₁ u₂ hu₂ heq
      ext i; by_cases hi : i = m
      · rw [hi, (Finset.mem_filter.mp hu₁).2, (Finset.mem_filter.mp hu₂).2]
      · exact congrFun heq ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩
    have hsub : Vm.image proj ⊆ Uset := by
      intro x hx; rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
      obtain ⟨hu1, hu_prod, hu_sf, hu_cop⟩ := (mem_validTupleSet hR_pos.le).mp (Finset.mem_filter.mp hu).1
      rw [Fintype.mem_piFinset]; intro i
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hu1 i.1, Nat.le_floor <|
        le_trans (by exact_mod_cast Finset.single_le_prod' (f := u) (fun j _ => hu1 j) (Finset.mem_univ i.1)) hu_prod⟩,
        (squarefree_prod_coord hu_sf).1 i.1 (Finset.mem_univ i.1),
        hu_cop.coprime_dvd_left (Finset.dvd_prod_of_mem u (Finset.mem_univ i.1))⟩
    have hEm_card : Fintype.card ↥Em = k := by
      rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]; omega
    calc ∑ u ∈ Vm, (∏ i ∈ Em, (g₂ (u i) : ℝ))⁻¹
        = ∑ u ∈ Vm, ∏ i : ↥Em, (g₂ (proj u i) : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.prod_inv_distrib, ← Finset.prod_attach Em]; rfl
      _ = ∑ x ∈ Vm.image proj, ∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹ :=
          (Finset.sum_image (f := fun x : ↥Em → ℕ => ∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹)
            (fun a ha b hb hab => hinj ha hb hab)).symm
      _ ≤ ∑ x ∈ Uset, ∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity
      _ = (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ k := by
          rw [sum_piFinset_prod (fun _ : ↥Em => S_sf) (fun _ x => (g₂ x : ℝ)⁻¹),
            Finset.prod_const, Finset.card_univ, hEm_card]
          congr 1; unfold aG2; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      _ ≤ (2 * A_phi) ^ k :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => aG2_nonneg _ _) (sum_aG2_le_two_mul_sum_aPhi hD) k
      _ = (2 : ℝ) ^ k * A_phi ^ k := mul_pow 2 A_phi k
  have hsum_Vm_pf : ∑ u ∈ Vm,
        (∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (∏ i ∈ Em, (g₂ (u i) : ℝ)) ≤
      (k : ℝ) * (2 : ℝ) ^ k * δ * A_phi ^ k := by
    let proj : (Fin (k + 1) → ℕ) → (↥Em → ℕ) := fun u i => u i.1
    have hinj : Set.InjOn proj Vm := by
      intro u₁ hu₁ u₂ hu₂ heq
      ext i; by_cases hi : i = m
      · rw [hi, (Finset.mem_filter.mp hu₁).2, (Finset.mem_filter.mp hu₂).2]
      · exact congrFun heq ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩
    have hsub : Vm.image proj ⊆ Uset := by
      intro x hx; rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
      obtain ⟨hu1, hu_prod, hu_sf, hu_cop⟩ := (mem_validTupleSet hR_pos.le).mp (Finset.mem_filter.mp hu).1
      rw [Fintype.mem_piFinset]; intro i
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hu1 i.1, Nat.le_floor <|
        le_trans (by exact_mod_cast Finset.single_le_prod' (f := u) (fun j _ => hu1 j) (Finset.mem_univ i.1)) hu_prod⟩,
        (squarefree_prod_coord hu_sf).1 i.1 (Finset.mem_univ i.1),
        hu_cop.coprime_dvd_left (Finset.dvd_prod_of_mem u (Finset.mem_univ i.1))⟩
    have hEm_card : Fintype.card ↥Em = k := by
      rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]; omega
    have hsum_U : ∑ x ∈ Uset,
          (∑ j : ↥Em, ∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) * (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹) ≤
        (k : ℝ) * δ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ k := by
      have hdist : ∀ x : ↥Em → ℕ,
          (∑ j : ↥Em, ∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) * (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹) =
          ∑ j : ↥Em, (∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) * (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹) :=
        fun x => Finset.sum_mul _ _ _
      simp_rw [hdist]
      rw [Finset.sum_comm]
      have hcoord : ∀ j : ↥Em,
          ∑ x ∈ Uset, (∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) * (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹) ≤
          δ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ k := by
        intro j
        have hfact : ∑ x ∈ Uset,
              (∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) * (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹) =
            (∑ n ∈ S_sf, (∑ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ n : ℝ)) *
              (∑ n ∈ S_sf, (g₂ n : ℝ)⁻¹) ^ (k - 1) := by
          have hterm_j : ∀ x : ↥Em → ℕ,
              (∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) * (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹) =
              ∏ i : ↥Em, (if i = j then (∑ p ∈ (x i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ (x i) : ℝ)
                else (g₂ (x i) : ℝ)⁻¹) := fun x => by
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
              ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), if_pos rfl]
            have hrest : ∏ i ∈ Finset.univ.erase j,
                  (if i = j then (∑ p ∈ (x i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ (x i) : ℝ)
                    else (g₂ (x i) : ℝ)⁻¹) =
                ∏ i ∈ Finset.univ.erase j, (g₂ (x i) : ℝ)⁻¹ :=
              Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_erase.mp hi).1
            rw [hrest, div_eq_mul_inv]; ring
          simp_rw [hterm_j]
          dsimp only [Uset]
          rw [sum_piFinset_prod (fun _ : ↥Em => S_sf) (fun i n =>
            if i = j then (∑ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ n : ℝ) else (g₂ n : ℝ)⁻¹)]
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
          simp only [if_pos rfl]
          congr 1
          have hrest : ∏ i ∈ Finset.univ.erase j,
                ∑ n ∈ S_sf, (if i = j then (∑ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ n : ℝ)
                  else (g₂ n : ℝ)⁻¹) =
              ∏ _i ∈ Finset.univ.erase j, ∑ n ∈ S_sf, (g₂ n : ℝ)⁻¹ :=
            Finset.prod_congr rfl fun i hi => Finset.sum_congr rfl fun _ _ => if_neg (Finset.mem_erase.mp hi).1
          rw [hrest, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, hEm_card]
        rw [hfact]
        have h1d_g2 : ∑ n ∈ S_sf, (g₂ n : ℝ)⁻¹ = ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n := by
          unfold aG2; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        rw [h1d_g2]
        have hkpos : 1 ≤ k := by
          have : 0 < Fintype.card ↥Em := Fintype.card_pos_iff.mpr ⟨j⟩
          omega
        calc (∑ n ∈ S_sf, (∑ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (g₂ n : ℝ)) *
              (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ (k - 1)
            ≤ (δ * ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ (k - 1) :=
              mul_le_mul_of_nonneg_right (sum_primeFactors_inv_sub_one_div_g2_le hD)
                (pow_nonneg (Finset.sum_nonneg fun _ _ => aG2_nonneg _ _) _)
          _ = δ * ((∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ (k - 1)) := by ring
          _ = δ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ k := by
              rw [← pow_succ', Nat.sub_add_cancel hkpos]
      calc ∑ j : ↥Em, ∑ x ∈ Uset, (∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) * (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹)
          ≤ ∑ _j : ↥Em, δ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ k := Finset.sum_le_sum fun j _ => hcoord j
        _ = (k : ℝ) * δ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ k := by
            rw [Finset.sum_const, Finset.card_univ, hEm_card, nsmul_eq_mul]; ring
    calc ∑ u ∈ Vm, (∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (∏ i ∈ Em, (g₂ (u i) : ℝ))
        = ∑ u ∈ Vm, (∑ j : ↥Em, ∑ p ∈ (proj u j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) *
            (∏ i : ↥Em, (g₂ (proj u i) : ℝ)⁻¹) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [div_eq_mul_inv, ← Finset.sum_attach Em, ← Finset.prod_inv_distrib, ← Finset.prod_attach Em]; rfl
      _ = ∑ x ∈ Vm.image proj, (∑ j : ↥Em, ∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) *
            (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹) :=
          (Finset.sum_image (f := fun x : ↥Em → ℕ =>
            (∑ j : ↥Em, ∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) * (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹))
            (fun a ha b hb hab => hinj ha hb hab)).symm
      _ ≤ ∑ x ∈ Uset, (∑ j : ↥Em, ∑ p ∈ (x j).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) *
            (∏ i : ↥Em, (g₂ (x i) : ℝ)⁻¹) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
            mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
              (Finset.prod_nonneg fun _ _ => by positivity)
      _ ≤ (k : ℝ) * δ * (∑ n ∈ Finset.Icc 1 ⌊R⌋₊, aG2 W₀ n) ^ k := hsum_U
      _ ≤ (k : ℝ) * δ * ((2 * A_phi) ^ k) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => aG2_nonneg _ _) (sum_aG2_le_two_mul_sum_aPhi hD) k)
            (by positivity)
      _ = (k : ℝ) * (2 : ℝ) ^ k * δ * A_phi ^ k := by rw [mul_pow]; ring
  -- Now lower-bound `∑_{u ∈ Vm} (yMVar u)^2 / ∏ g₂` by `∑_{u ∈ Vm} (yMain u)^2 / ∏ g₂ - Error`!
  have hdiag_replace :
      (∑ u ∈ Vm, (yMain u) ^ 2 / (∏ i ∈ Em, (g₂ (u i) : ℝ))) -
        (E_piece * (cW * Real.log R) * A_phi ^ (k + 1) +
          (2 : ℝ) ^ (k + 1) * T.bound * (cW * Real.log R) * K_1d * Real.sqrt (Real.log R) * A_phi ^ k) ≤
      ∑ u ∈ Vm, (yMVar W₀ R T m u) ^ 2 / (∏ i ∈ Em, (g₂ (u i) : ℝ)) := by
    have hpt : ∀ u ∈ Vm,
        (yMain u) ^ 2 / (∏ i ∈ Em, (g₂ (u i) : ℝ)) -
          2 * ((cW * Real.log R) * T.bound) *
            ((T.bound * A_phi * (((1 + δ) ^ k - 1) + δ) + K_1d * Real.sqrt (Real.log R)) *
                (∏ i ∈ Em, (g₂ (u i) : ℝ))⁻¹ +
              T.bound * A_phi *
                ((∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (∏ i ∈ Em, (g₂ (u i) : ℝ)))) ≤
        (yMVar W₀ R T m u) ^ 2 / (∏ i ∈ Em, (g₂ (u i) : ℝ)) := by
      intro u hu
      have hg_pos : 0 < ∏ i ∈ Em, (g₂ (u i) : ℝ) := by
        obtain ⟨_, _, hu_sf, hu_cop⟩ := (mem_validTupleSet hR_pos.le).mp (Finset.mem_filter.mp hu).1
        exact Finset.prod_pos fun i _ => Nat.cast_pos.mpr
          (g₂_pos_of_coprime_two ((squarefree_prod_coord hu_sf).1 i (Finset.mem_univ i)).ne_zero
            ((hu_cop.coprime_dvd_left (Finset.dvd_prod_of_mem u (Finset.mem_univ i))).coprime_dvd_right h2W))
      have hsq : (yMain u) ^ 2 - 2 * |yMain u| * |yMVar W₀ R T m u - yMain u| ≤ (yMVar W₀ R T m u) ^ 2 := by
        nlinarith [sq_nonneg (yMVar W₀ R T m u - yMain u),
          neg_abs_le (yMain u * (yMVar W₀ R T m u - yMain u)),
          abs_mul (yMain u) (yMVar W₀ R T m u - yMain u)]
      have hbd1 : 2 * |yMain u| * |yMVar W₀ R T m u - yMain u| ≤
          2 * ((cW * Real.log R) * T.bound) *
            (T.bound * A_phi * (((1 + δ) ^ k - 1) + δ +
              ∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) +
              K_1d * Real.sqrt (Real.log R)) := by
        have h1 := hyMain_abs u hu
        have h2 := happrox_u u hu
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (abs_nonneg _)
          (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hcW_nn hlogR_pos.le) T.bound_nonneg))
      have hnum : (yMain u) ^ 2 - 2 * ((cW * Real.log R) * T.bound) *
            (T.bound * A_phi * (((1 + δ) ^ k - 1) + δ +
              ∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) +
              K_1d * Real.sqrt (Real.log R)) ≤ (yMVar W₀ R T m u) ^ 2 := by linarith
      have hdiv := div_le_div_of_nonneg_right hnum hg_pos.le
      have hrhs_eq : ((yMain u) ^ 2 - 2 * ((cW * Real.log R) * T.bound) *
            (T.bound * A_phi * (((1 + δ) ^ k - 1) + δ +
              ∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) +
              K_1d * Real.sqrt (Real.log R))) / (∏ i ∈ Em, (g₂ (u i) : ℝ)) =
          (yMain u) ^ 2 / (∏ i ∈ Em, (g₂ (u i) : ℝ)) -
          2 * ((cW * Real.log R) * T.bound) *
            ((T.bound * A_phi * (((1 + δ) ^ k - 1) + δ) + K_1d * Real.sqrt (Real.log R)) *
                (∏ i ∈ Em, (g₂ (u i) : ℝ))⁻¹ +
              T.bound * A_phi *
                ((∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (∏ i ∈ Em, (g₂ (u i) : ℝ)))) := by
        field_simp [hg_pos.ne']; ring
      linarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib] at hsum
    have herr_sum : ∑ u ∈ Vm,
          2 * ((cW * Real.log R) * T.bound) *
            ((T.bound * A_phi * (((1 + δ) ^ k - 1) + δ) + K_1d * Real.sqrt (Real.log R)) *
                (∏ i ∈ Em, (g₂ (u i) : ℝ))⁻¹ +
              T.bound * A_phi *
                ((∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (∏ i ∈ Em, (g₂ (u i) : ℝ)))) ≤
        E_piece * (cW * Real.log R) * A_phi ^ (k + 1) +
          (2 : ℝ) ^ (k + 1) * T.bound * (cW * Real.log R) * K_1d * Real.sqrt (Real.log R) * A_phi ^ k := by
      simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      have h1 : (T.bound * A_phi * (((1 + δ) ^ k - 1) + δ) + K_1d * Real.sqrt (Real.log R)) *
            (∑ u ∈ Vm, (∏ i ∈ Em, (g₂ (u i) : ℝ))⁻¹) ≤
          (T.bound * A_phi * (((1 + δ) ^ k - 1) + δ) + K_1d * Real.sqrt (Real.log R)) *
            ((2 : ℝ) ^ k * A_phi ^ k) :=
        mul_le_mul_of_nonneg_left hsum_Vm_g2 (by
          have : (1 : ℝ) ≤ (1 + δ) ^ k := one_le_pow₀ (by linarith)
          exact add_nonneg (mul_nonneg (mul_nonneg T.bound_nonneg hAphi_nn) (by linarith)) (by positivity))
      have h2 : T.bound * A_phi *
            (∑ u ∈ Vm, (∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (∏ i ∈ Em, (g₂ (u i) : ℝ))) ≤
          T.bound * A_phi * ((k : ℝ) * (2 : ℝ) ^ k * δ * A_phi ^ k) :=
        mul_le_mul_of_nonneg_left hsum_Vm_pf (mul_nonneg T.bound_nonneg hAphi_nn)
      calc 2 * ((cW * Real.log R) * T.bound) *
            ((T.bound * A_phi * (((1 + δ) ^ k - 1) + δ) + K_1d * Real.sqrt (Real.log R)) *
                (∑ u ∈ Vm, (∏ i ∈ Em, (g₂ (u i) : ℝ))⁻¹) +
              T.bound * A_phi *
                (∑ u ∈ Vm, (∑ i ∈ Em, ∑ p ∈ (u i).primeFactors, (((p - 1 : ℕ) : ℝ))⁻¹) / (∏ i ∈ Em, (g₂ (u i) : ℝ))))
          ≤ 2 * ((cW * Real.log R) * T.bound) *
              ((T.bound * A_phi * (((1 + δ) ^ k - 1) + δ) + K_1d * Real.sqrt (Real.log R)) * ((2 : ℝ) ^ k * A_phi ^ k) +
                T.bound * A_phi * ((k : ℝ) * (2 : ℝ) ^ k * δ * A_phi ^ k)) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 h2)
              (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hcW_nn hlogR_pos.le) T.bound_nonneg))
        _ = E_piece * (cW * Real.log R) * A_phi ^ (k + 1) +
              (2 : ℝ) ^ (k + 1) * T.bound * (cW * Real.log R) * K_1d * Real.sqrt (Real.log R) * A_phi ^ k := by
            dsimp only [E_piece]; rw [pow_succ (2 : ℝ) k, pow_succ A_phi k]; ring
    linarith
  -- Step 3: Lower-bound `∑_{u ∈ Vm} (yMain u)^2 / ∏ g₂` via `1/g₂ ≥ 1/φ`, re-inserting non-coprime tuples, and `sum_kd_approx_integral k`!
  have hmain_lower :
      (cW * Real.log R) ^ (k + 2) * maynardJ0 k T.F -
        (cW * Real.log R) ^ 2 * (E_ncop * A_phi ^ k + K_J * (Real.log R) ^ ((k : ℝ) - 1 / 2)) ≤
      ∑ u ∈ Vm, (yMain u) ^ 2 / (∏ i ∈ Em, (g₂ (u i) : ℝ)) := by
    have hge_phi : ∑ u ∈ Vm, (yMain u) ^ 2 / (∏ i ∈ Em, ((u i).totient : ℝ)) ≤
        ∑ u ∈ Vm, (yMain u) ^ 2 / (∏ i ∈ Em, (g₂ (u i) : ℝ)) := by
      refine Finset.sum_le_sum fun u hu => ?_
      obtain ⟨hu1, _, hu_sf, hu_cop⟩ := (mem_validTupleSet hR_pos.le).mp (Finset.mem_filter.mp hu).1
      have hg_pos : 0 < ∏ i ∈ Em, (g₂ (u i) : ℝ) := Finset.prod_pos fun i _ => Nat.cast_pos.mpr
        (g₂_pos_of_coprime_two ((squarefree_prod_coord hu_sf).1 i (Finset.mem_univ i)).ne_zero
          ((hu_cop.coprime_dvd_left (Finset.dvd_prod_of_mem u (Finset.mem_univ i))).coprime_dvd_right h2W))
      have hle : ∏ i ∈ Em, (g₂ (u i) : ℝ) ≤ ∏ i ∈ Em, ((u i).totient : ℝ) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ => by
          exact_mod_cast g₂_le_totient_of_squarefree ((squarefree_prod_coord hu_sf).1 i (Finset.mem_univ i))
      exact div_le_div_of_nonneg_left (sq_nonneg _) hg_pos hle
    -- Reindex `Vm` to `Vk := {v : Fin k → ℕ ∈ Simplex_k : Squarefree (∏ v) ∧ Coprime (∏ v) W₀}`
    set SimplexK := (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R⌋₊)).filter
      (fun v => ((∏ j, v j : ℕ) : ℝ) ≤ R)
    have hbij_k : ∑ u ∈ Vm, (yMain u) ^ 2 / (∏ i ∈ Em, ((u i).totient : ℝ)) =
        (cW * Real.log R) ^ 2 *
          ∑ v ∈ SimplexK.filter (fun v => Squarefree (∏ j, v j)),
            (∏ j, aPhi W₀ (v j)) * (G_J (fun j => Real.log (v j : ℝ) / Real.log R)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij_ne_zero (fun u _ _ j => u (m.succAbove j)) ?_ ?_ ?_ ?_
      · intro u hu _
        obtain ⟨hu1, hu_prod, hu_sf, _⟩ := (mem_validTupleSet hR_pos.le).mp (Finset.mem_filter.mp hu).1
        have hum := (Finset.mem_filter.mp hu).2
        have hpeq : ∏ j : Fin k, u (m.succAbove j) = ∏ i, u i := by
          rw [Fin.prod_univ_succAbove u m, hum, one_mul]
        simp only [SimplexK, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
        refine ⟨⟨fun j => ⟨hu1 _, Nat.le_floor <|
          le_trans (by exact_mod_cast Finset.single_le_prod' (f := u) (fun i _ => hu1 i) (Finset.mem_univ _)) hu_prod⟩,
          hpeq.symm ▸ hu_prod⟩, hpeq.symm ▸ hu_sf⟩
      · intro u₁ hu₁ _ u₂ hu₂ _ heq
        have h1m := (Finset.mem_filter.mp hu₁).2
        have h2m := (Finset.mem_filter.mp hu₂).2
        ext i
        by_cases hi : i = m
        · rw [hi, h1m, h2m]
        · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
          exact congrFun heq j
      · intro v hv hne
        have hvS := (Finset.mem_filter.mp hv).1
        have hv_sf := (Finset.mem_filter.mp hv).2
        have hvI : ∀ j, v j ∈ Finset.Icc 1 ⌊R⌋₊ := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hvS).1
        have hv_prod : ((∏ j, v j : ℕ) : ℝ) ≤ R := (Finset.mem_filter.mp hvS).2
        have hv_cop_j : ∀ j, Nat.Coprime (v j) W₀ := fun j => by
          by_contra hnc
          have h0 : aPhi W₀ (v j) = 0 := by unfold aPhi; rw [if_neg (fun h => hnc h.2)]
          have hpr0 : ∏ i, aPhi W₀ (v i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h0
          exact hne (by simp [hpr0])
        let u : Fin (k + 1) → ℕ := m.insertNth 1 v
        have hpeq : ∏ i, u i = ∏ j, v j := by
          rw [Fin.prod_univ_succAbove u m]; simp [u]
        have huVm : u ∈ Vm := by
          refine Finset.mem_filter.mpr ⟨(mem_validTupleSet hR_pos.le).mpr ⟨?_, hpeq.symm ▸ hv_prod,
            hpeq.symm ▸ hv_sf, hpeq.symm ▸ Nat.Coprime.prod_left (fun j _ => hv_cop_j j)⟩, by simp [u]⟩
          intro i
          by_cases hi : i = m
          · subst hi; simp [u]
          · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
            simp only [u, Fin.insertNth_apply_succAbove]
            exact (Finset.mem_Icc.mp (hvI j)).1
        have hu_succ : (fun j : Fin k => u (m.succAbove j)) = v := by ext j; simp [u]
        have hval_eq : (yMain u) ^ 2 / (∏ i ∈ Em, ((u i).totient : ℝ)) =
            (cW * Real.log R) ^ 2 * ((∏ j, aPhi W₀ (v j)) * (G_J (fun j => Real.log (v j : ℝ) / Real.log R)) ^ 2) := by
          have ha_eq : ∏ j, aPhi W₀ (v j) = (∏ i ∈ Em, ((u i).totient : ℝ))⁻¹ := by
            have hphi_eq : ∏ i ∈ Em, ((u i).totient : ℝ) = ∏ j, ((v j).totient : ℝ) := by
              have h1 := Fin.prod_univ_succAbove (fun i => ((u i).totient : ℝ)) m
              have h2 := Finset.mul_prod_erase Finset.univ (fun i => ((u i).totient : ℝ)) (Finset.mem_univ m)
              have hum1 : u m = 1 := by simp [u]
              rw [hum1, Nat.totient_one, Nat.cast_one, one_mul] at h1 h2
              rw [h2, h1]; refine Finset.prod_congr rfl fun j _ => by simp [u]
            rw [hphi_eq, ← Finset.prod_inv_distrib]
            refine Finset.prod_congr rfl fun j _ => ?_
            unfold aPhi; rw [if_pos ⟨(squarefree_prod_coord hv_sf).1 j (Finset.mem_univ j), hv_cop_j j⟩]
          dsimp only [yMain]; simp only [u, Fin.insertNth_apply_succAbove]; rw [ha_eq]; ring
        exact ⟨u, huVm, by rw [hval_eq]; exact hne, hu_succ⟩
      · intro u hu _
        obtain ⟨_, _, hu_sf, hu_cop⟩ := (mem_validTupleSet hR_pos.le).mp (Finset.mem_filter.mp hu).1
        have hum := (Finset.mem_filter.mp hu).2
        have ha_eq : ∏ j : Fin k, aPhi W₀ (u (m.succAbove j)) = (∏ i ∈ Em, ((u i).totient : ℝ))⁻¹ := by
          have hphi_eq : ∏ i ∈ Em, ((u i).totient : ℝ) = ∏ j : Fin k, ((u (m.succAbove j)).totient : ℝ) := by
            have h1 := Fin.prod_univ_succAbove (fun i => ((u i).totient : ℝ)) m
            have h2 := Finset.mul_prod_erase Finset.univ (fun i => ((u i).totient : ℝ)) (Finset.mem_univ m)
            rw [hum, Nat.totient_one, Nat.cast_one, one_mul] at h1 h2
            rw [h2, ← h1]
          rw [hphi_eq, ← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl fun j _ => ?_
          unfold aPhi
          rw [if_pos ⟨(squarefree_prod_coord hu_sf).1 _ (Finset.mem_univ _),
            hu_cop.coprime_dvd_left (Finset.dvd_prod_of_mem u (Finset.mem_univ _))⟩]
        dsimp only [yMain]; rw [ha_eq]; ring
    have hsplit_K := Finset.sum_filter_add_sum_filter_not SimplexK (fun v => Squarefree (∏ j, v j))
      (fun v => (∏ j, aPhi W₀ (v j)) * (G_J (fun j => Real.log (v j : ℝ) / Real.log R)) ^ 2)
    have hnoncop_bd : ∑ v ∈ SimplexK.filter (fun v => ¬ Squarefree (∏ j, v j)),
          (∏ j, aPhi W₀ (v j)) * (G_J (fun j => Real.log (v j : ℝ) / Real.log R)) ^ 2 ≤
        E_ncop * A_phi ^ k := by
      have hfeq : SimplexK.filter (fun v => ¬ Squarefree (∏ j, v j)) =
          (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊R⌋₊)).filter
            (fun v => ((∏ j, v j : ℕ) : ℝ) ≤ R ∧ ¬ Squarefree (∏ j, v j)) := by
        ext v; simp [SimplexK, and_assoc]
      calc ∑ v ∈ SimplexK.filter (fun v => ¬ Squarefree (∏ j, v j)),
              (∏ j, aPhi W₀ (v j)) * (G_J (fun j => Real.log (v j : ℝ) / Real.log R)) ^ 2
          ≤ ∑ v ∈ SimplexK.filter (fun v => ¬ Squarefree (∏ j, v j)),
              (∏ j, aPhi W₀ (v j)) * T.bound ^ 2 := by
            refine Finset.sum_le_sum fun v hv => ?_
            refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun _ _ => aPhi_nonneg _ _)
            have hvS := (Finset.mem_filter.mp hv).1
            have hvI := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hvS).1
            have hv_prod := (Finset.mem_filter.mp hvS).2
            have hin : InSimplex 1 (fun j => Real.log (v j : ℝ) / Real.log R) := by
              refine ⟨fun j => div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp (hvI j)).1)) hlogR_pos.le, ?_⟩
              rw [← Finset.sum_div, div_le_one hlogR_pos,
                ← Real.log_prod fun j _ => (Nat.cast_pos.mpr (Finset.mem_Icc.mp (hvI j)).1).ne']
              exact Real.log_le_log (Finset.prod_pos fun j _ => Nat.cast_pos.mpr (Finset.mem_Icc.mp (hvI j)).1)
                (by exact_mod_cast hv_prod)
            have hbd := T.isSimplexLipOn.innerIntegral.2.2.1 _ hin
            have hsq : |G_J (fun j => Real.log (v j : ℝ) / Real.log R)| ^ 2 ≤ T.bound ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hbd 2
            simpa [sq_abs] using hsq
        _ = T.bound ^ 2 * ∑ v ∈ SimplexK.filter (fun v => ¬ Squarefree (∏ j, v j)), ∏ j, aPhi W₀ (v j) := by
            rw [← Finset.sum_mul, mul_comm]
        _ ≤ T.bound ^ 2 * ((k : ℝ) ^ 2 * δ * A_phi ^ k) := by
            rw [hfeq]
            exact mul_le_mul_of_nonneg_left (sum_non_coprime_simplex_le hD hR1) (sq_nonneg _)
        _ = E_ncop * A_phi ^ k := by dsimp only [E_ncop]; ring
    have hint_lo := (abs_le.mp (hKJ R hR)).1
    have hJ0_eq : maynardJ0 k T.F = simplexIntegral k 1 (fun w => (G_J w) ^ 2) := rfl
    rw [hJ0_eq]
    have hsum_lo : (cW * Real.log R) ^ k * simplexIntegral k 1 (fun w => (G_J w) ^ 2) -
          (E_ncop * A_phi ^ k + K_J * (Real.log R) ^ ((k : ℝ) - 1 / 2)) ≤
        ∑ v ∈ SimplexK.filter (fun v => Squarefree (∏ j, v j)),
          (∏ j, aPhi W₀ (v j)) * (G_J (fun j => Real.log (v j : ℝ) / Real.log R)) ^ 2 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum_lo (sq_nonneg (cW * Real.log R))
    have hpow2 : (cW * Real.log R) ^ 2 * (cW * Real.log R) ^ k = (cW * Real.log R) ^ (k + 2) := by
      rw [← pow_add, add_comm]
    rw [mul_sub, ← mul_assoc, hpow2] at hmul
    linarith [hge_phi, hbij_k, hmul]
  -- Step 4: Combine `Q1Sum_diag_lower`, `hdiag_replace`, `hmain_lower`, and convert powers of `A_phi` to `cW * log R` + lower-order!
  have hQ1 := Q1Sum_diag_lower hD hR T m
  have hpow_k2 : A_phi ^ (k + 2) ≤ (cW * Real.log R) ^ (k + 2) + C_sum * (Real.log R) ^ (k + 1) :=
    (pow_le_pow_left₀ hAphi_nn hAphi_le (k + 2)).trans
      (add_pow_le_main_plus_lower hcW_nn hC_phi.le hlogR1 (k + 1))
  have hpow_k1 : A_phi ^ (k + 1) ≤ (cW * Real.log R) ^ (k + 1) + (cW + C_phi) ^ (k + 1) * (Real.log R) ^ k :=
    (pow_le_pow_left₀ hAphi_nn hAphi_le (k + 1)).trans
      (add_pow_le_main_plus_lower hcW_nn hC_phi.le hlogR1 k)
  have hpow_k_crude : A_phi ^ k ≤ (cW + C_phi) ^ k * (Real.log R) ^ k := by
    calc A_phi ^ k ≤ ((cW + C_phi) * Real.log R) ^ k := pow_le_pow_left₀ hAphi_nn hAphi_crude k
      _ = (cW + C_phi) ^ k * (Real.log R) ^ k := mul_pow _ _ _
  have hL_k1_le : (Real.log R) ^ (k + 1) ≤ (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlogR1 (by push_cast; linarith)
  have hL_k_half : (Real.log R) ^ (k + 1) * Real.sqrt (Real.log R) =
      (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hlogR_pos]
    congr 1; push_cast; ring
  have hL_2_k : (Real.log R) ^ 2 * (Real.log R) ^ ((k : ℝ) - 1 / 2) =
      (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast (Real.log R) 2, ← Real.rpow_add hlogR_pos]
    congr 1; push_cast; ring
  have hE1_decomp : E_off1 + E_piece + E_ncop = E1_D0 k T.bound D₀ := by
    dsimp only [E_off1, E_piece, E_ncop, E1_D0, δ]; ring
  have hterm1 : E_off1 * A_phi ^ (k + 2) ≤
      (cW * Real.log R) ^ (k + 2) * E_off1 +
        E_off1 * C_sum * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
    calc E_off1 * A_phi ^ (k + 2)
        ≤ E_off1 * ((cW * Real.log R) ^ (k + 2) + C_sum * (Real.log R) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hpow_k2 hE1_nn
      _ = (cW * Real.log R) ^ (k + 2) * E_off1 + E_off1 * C_sum * (Real.log R) ^ (k + 1) := by ring
      _ ≤ (cW * Real.log R) ^ (k + 2) * E_off1 +
            E_off1 * C_sum * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by gcongr
  have hterm2 : E_piece * (cW * Real.log R) * A_phi ^ (k + 1) ≤
      (cW * Real.log R) ^ (k + 2) * E_piece +
        E_piece * cW * (cW + C_phi) ^ (k + 1) * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
    calc E_piece * (cW * Real.log R) * A_phi ^ (k + 1)
        ≤ E_piece * (cW * Real.log R) *
            ((cW * Real.log R) ^ (k + 1) + (cW + C_phi) ^ (k + 1) * (Real.log R) ^ k) :=
          mul_le_mul_of_nonneg_left hpow_k1 (by positivity)
      _ = (cW * Real.log R) ^ (k + 2) * E_piece +
            E_piece * cW * (cW + C_phi) ^ (k + 1) * (Real.log R) ^ (k + 1) := by
          rw [pow_succ' (cW * Real.log R) (k + 1), pow_succ' (Real.log R) k]; ring
      _ ≤ (cW * Real.log R) ^ (k + 2) * E_piece +
            E_piece * cW * (cW + C_phi) ^ (k + 1) * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by gcongr
  have hterm3 : (2 : ℝ) ^ (k + 1) * T.bound * (cW * Real.log R) * K_1d * Real.sqrt (Real.log R) * A_phi ^ k ≤
      (2 : ℝ) ^ (k + 1) * T.bound * cW * K_1d * (cW + C_phi) ^ k *
        (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
    calc (2 : ℝ) ^ (k + 1) * T.bound * (cW * Real.log R) * K_1d * Real.sqrt (Real.log R) * A_phi ^ k
        ≤ (2 : ℝ) ^ (k + 1) * T.bound * (cW * Real.log R) * K_1d * Real.sqrt (Real.log R) *
            ((cW + C_phi) ^ k * (Real.log R) ^ k) :=
          mul_le_mul_of_nonneg_left hpow_k_crude (by have := T.bound_nonneg; positivity)
      _ = (2 : ℝ) ^ (k + 1) * T.bound * cW * K_1d * (cW + C_phi) ^ k *
            ((Real.log R) ^ (k + 1) * Real.sqrt (Real.log R)) := by rw [pow_succ (Real.log R) k]; ring
      _ = _ := by rw [hL_k_half]
  have hterm4 : (cW * Real.log R) ^ 2 * (E_ncop * A_phi ^ k + K_J * (Real.log R) ^ ((k : ℝ) - 1 / 2)) ≤
      (cW * Real.log R) ^ (k + 2) * E_ncop +
        (E_ncop * cW ^ 2 * (cW + C_phi) ^ k + cW ^ 2 * K_J) *
          (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
    have h4a : (cW * Real.log R) ^ 2 * (E_ncop * A_phi ^ k) ≤
        (cW * Real.log R) ^ (k + 2) * E_ncop +
          E_ncop * cW ^ 2 * (cW + C_phi) ^ k * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
      rcases k with _ | k'
      · simp only [pow_zero, mul_one, zero_add]
        have : 0 ≤ E_ncop * cW ^ 2 * 1 * (Real.log R) ^ (((2 : ℕ) : ℝ) - 1 / 2) := by positivity
        linarith
      · have hpk : A_phi ^ (k' + 1) ≤ (cW * Real.log R) ^ (k' + 1) + (cW + C_phi) ^ (k' + 1) * (Real.log R) ^ k' :=
          (pow_le_pow_left₀ hAphi_nn hAphi_le (k' + 1)).trans
            (add_pow_le_main_plus_lower hcW_nn hC_phi.le hlogR1 k')
        have hpow_c : (cW * Real.log R) ^ 2 * (cW * Real.log R) ^ (k' + 1) = (cW * Real.log R) ^ (k' + 1 + 2) := by
          rw [← pow_add]; congr 1; omega
        have hpow_L : (Real.log R) ^ 2 * (Real.log R) ^ k' = (Real.log R) ^ (k' + 2) := by
          rw [← pow_add, add_comm]
        calc (cW * Real.log R) ^ 2 * (E_ncop * A_phi ^ (k' + 1))
            ≤ (cW * Real.log R) ^ 2 * (E_ncop * ((cW * Real.log R) ^ (k' + 1) + (cW + C_phi) ^ (k' + 1) * (Real.log R) ^ k')) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpk hEn_nn) (sq_nonneg _)
          _ = ((cW * Real.log R) ^ 2 * (cW * Real.log R) ^ (k' + 1)) * E_ncop +
                E_ncop * cW ^ 2 * (cW + C_phi) ^ (k' + 1) * ((Real.log R) ^ 2 * (Real.log R) ^ k') := by
              rw [mul_pow cW (Real.log R) 2]; ring
          _ = (cW * Real.log R) ^ (k' + 1 + 2) * E_ncop +
                E_ncop * cW ^ 2 * (cW + C_phi) ^ (k' + 1) * (Real.log R) ^ (k' + 2) := by
              rw [hpow_c, hpow_L]
          _ ≤ (cW * Real.log R) ^ (k' + 1 + 2) * E_ncop +
                E_ncop * cW ^ 2 * (cW + C_phi) ^ (k' + 1) * (Real.log R) ^ (((k' + 1 + 2 : ℕ) : ℝ) - 1 / 2) := by
              gcongr
    have h4b : (cW * Real.log R) ^ 2 * (K_J * (Real.log R) ^ ((k : ℝ) - 1 / 2)) =
        cW ^ 2 * K_J * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by
      rw [mul_pow cW (Real.log R) 2, ← hL_2_k]; ring
    linarith
  have hQ1_rew : (8 : ℝ) ^ k * T.bound ^ 2 * A_phi ^ (k + 2) *
        ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ (k * (k - 1)) - 1) =
      E_off1 * A_phi ^ (k + 2) := by
    dsimp only [E_off1, δ]; ring
  rw [hQ1_rew] at hQ1
  dsimp only [K₁]
  rw [← hE1_decomp]
  linarith

/-! ### Section 4c: Divisor-Function Bound, Bombieri–Vinogradov Error, and `S1_m_interval_lower` -/

/-- **Elementary Rankin / Divisor-Function Bound**: for any `B : ℕ` and `N ≥ 1`:
`∑_{1 ≤ q ≤ N, Squarefree q} B^{ω(q)} / q ≤ (Real.log N + 1)^B`. -/
lemma sum_pow_omega_div_le (B N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ (Finset.Icc 1 N).filter Squarefree, ((B : ℝ) ^ (q.primeFactors.card)) / (q : ℝ) ≤
      (Real.log (N : ℝ) + 1) ^ B := by
  set Box := Fintype.piFinset (fun _ : Fin B => Finset.Icc 1 N)
  -- For each squarefree `q ∈ Icc 1 N`, map `f : ↥q.primeFactors → Fin B` injectively into `{a ∈ Box : ∏ j, a j = q}`
  have hfiber : ∀ q ∈ (Finset.Icc 1 N).filter Squarefree,
      (B : ℝ) ^ (q.primeFactors.card) ≤
        ((Box.filter (fun a => ∏ j, a j = q)).card : ℝ) := by
    intro q hq
    have hqI := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    have hqsf := (Finset.mem_filter.mp hq).2
    let emb : (↥q.primeFactors → Fin B) → (Fin B → ℕ) := fun f j =>
      ∏ p ∈ q.primeFactors.attach.filter (fun p => f p = j), p.1
    have hcard_dom : (Finset.univ : Finset (↥q.primeFactors → Fin B)).card = B ^ q.primeFactors.card := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    have hmaps : ∀ f : ↥q.primeFactors → Fin B, emb f ∈ Box.filter (fun a => ∏ j, a j = q) := by
      intro f
      have hprod : ∏ j : Fin B, emb f j = q := by
        have h1 : ∏ j : Fin B, ∏ p ∈ q.primeFactors.attach.filter (fun p => f p = j), p.1 =
            ∏ p ∈ q.primeFactors.attach, p.1 :=
          Finset.prod_fiberwise_of_maps_to (g := f) (fun _ _ => Finset.mem_univ _) (fun p : ↥q.primeFactors => p.1)
        rw [h1, Finset.prod_attach q.primeFactors (fun x => x), Nat.prod_primeFactors_of_squarefree hqsf]
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => Finset.mem_Icc.mpr ⟨?_, ?_⟩, hprod⟩
      · exact Finset.prod_pos fun p _ => (Nat.prime_of_mem_primeFactors p.2).pos
      · have hdvd : emb f j ∣ q := hprod ▸ Finset.dvd_prod_of_mem (emb f) (Finset.mem_univ j)
        exact (Nat.le_of_dvd hqI.1 hdvd).trans hqI.2
    have hinj : Set.InjOn emb (Finset.univ : Finset (↥q.primeFactors → Fin B)) := by
      intro f₁ _ f₂ _ heq
      funext p
      have hpp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
      have hdiv1 : p.1 ∣ emb f₁ (f₁ p) := by
        exact Finset.dvd_prod_of_mem (fun x : ↥q.primeFactors => x.1)
          (Finset.mem_filter.mpr ⟨Finset.mem_attach _ p, rfl⟩)
      rw [heq] at hdiv1
      obtain ⟨r, hr, hpr⟩ := hpp.prime.exists_mem_finset_dvd hdiv1
      have hrp : p.1 = r.1 := (Nat.prime_dvd_prime_iff_eq hpp (Nat.prime_of_mem_primeFactors r.2)).mp hpr
      have hreq : r = p := Subtype.ext hrp.symm
      have hfr := (Finset.mem_filter.mp hr).2
      rw [hreq] at hfr
      exact hfr.symm
    have hnat : B ^ q.primeFactors.card ≤ (Box.filter (fun a => ∏ j, a j = q)).card := by
      rw [← hcard_dom]
      exact Finset.card_le_card_of_injOn emb (fun f _ => hmaps f) hinj
    exact_mod_cast hnat
  calc ∑ q ∈ (Finset.Icc 1 N).filter Squarefree, ((B : ℝ) ^ (q.primeFactors.card)) / (q : ℝ)
      ≤ ∑ q ∈ (Finset.Icc 1 N).filter Squarefree,
          ((Box.filter (fun a => ∏ j, a j = q)).card : ℝ) / (q : ℝ) :=
        Finset.sum_le_sum fun q hq => div_le_div_of_nonneg_right (hfiber q hq) (Nat.cast_nonneg _)
    _ = ∑ q ∈ (Finset.Icc 1 N).filter Squarefree,
          ∑ a ∈ Box.filter (fun a => ∏ j, a j = q), (∏ j : Fin B, (a j : ℝ)⁻¹) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hterm : ∀ a ∈ Box.filter (fun a => ∏ j, a j = q), (∏ j : Fin B, (a j : ℝ)⁻¹) = ((q : ℝ))⁻¹ := by
          intro a ha
          rw [Finset.prod_inv_distrib, ← Nat.cast_prod, (Finset.mem_filter.mp ha).2]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ = ∑ a ∈ ((Finset.Icc 1 N).filter Squarefree).biUnion (fun q => Box.filter (fun a => ∏ j, a j = q)),
          (∏ j : Fin B, (a j : ℝ)⁻¹) := by
        symm
        refine Finset.sum_biUnion fun q₁ _ q₂ _ hne => ?_
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro a ha₁ ha₂
        exact hne ((Finset.mem_filter.mp ha₁).2.symm.trans (Finset.mem_filter.mp ha₂).2)
    _ ≤ ∑ a ∈ Box, (∏ j : Fin B, (a j : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _)
          fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity
    _ = (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ^ B := by
        dsimp only [Box]
        rw [sum_piFinset_prod (fun _ : Fin B => Finset.Icc 1 N) (fun _ n => (n : ℝ)⁻¹),
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (Real.log (N : ℝ) + 1) ^ B := by
        have hharm := (abs_le.mp (abs_harmonic_sub_log_le_one (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)))).2
        rw [Nat.floor_natCast] at hharm
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (by linarith) B

/-- **Multiplicity Bound for `∏_{i ≠ m} lcm(d i, e i) = r`**:
for squarefree `r`, the number of `(d, e) ∈ Vm ×ˢ Vm` with `PairwiseCoprimeCross d e` and
`∏_{i ∈ Em} lcm(d i, e i) = r` is at most `(3 * (k + 1)) ^ ω(r)`. -/
private lemma mult_lcm_pair_le {k W₀ : ℕ} {R : ℝ} (hR : 0 ≤ R) (m : Fin (k + 1))
    (r : ℕ) (hrsf : Squarefree r) :
    let Vm := (validTupleSet k W₀ R).filter (fun d => d m = 1)
    let Em := (Finset.univ : Finset (Fin (k + 1))).erase m
    (((Vm ×ˢ Vm).filter (fun de => PairwiseCoprimeCross de.1 de.2 ∧
        ∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i) = r)).card : ℝ) ≤
      ((3 * (k + 1) : ℕ) : ℝ) ^ (r.primeFactors.card) := by
  intro Vm Em
  set S := (Vm ×ˢ Vm).filter (fun de => PairwiseCoprimeCross de.1 de.2 ∧
    ∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i) = r)
  let pick : (Fin (k + 1) → ℕ) → (Fin (k + 1) → ℕ) → ℕ → Fin (k + 1) := fun d e p =>
    if h : ∃ i ∈ Em, p ∣ Nat.lcm (d i) (e i) then h.choose else m
  let tag : (Fin (k + 1) → ℕ) → (Fin (k + 1) → ℕ) → ℕ → Fin (k + 1) → Fin 3 := fun d e p i =>
    if p ∣ d i then (if p ∣ e i then 2 else 0) else 1
  let emb : ((Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ)) → (↥r.primeFactors → Fin (k + 1) × Fin 3) :=
    fun de p => (pick de.1 de.2 p.1, tag de.1 de.2 p.1 (pick de.1 de.2 p.1))
  have hinj : Set.InjOn emb S := by
    intro x₁ hx₁ x₂ hx₂ heq
    rcases x₁ with ⟨d₁, e₁⟩; rcases x₂ with ⟨d₂, e₂⟩
    have hx₁m := Finset.mem_filter.mp hx₁
    have hx₂m := Finset.mem_filter.mp hx₂
    have hd₁V := (Finset.mem_filter.mp (Finset.mem_product.mp hx₁m.1).1).1
    have hd₁m := (Finset.mem_filter.mp (Finset.mem_product.mp hx₁m.1).1).2
    have he₁V := (Finset.mem_filter.mp (Finset.mem_product.mp hx₁m.1).2).1
    have he₁m := (Finset.mem_filter.mp (Finset.mem_product.mp hx₁m.1).2).2
    have hd₂V := (Finset.mem_filter.mp (Finset.mem_product.mp hx₂m.1).1).1
    have hd₂m := (Finset.mem_filter.mp (Finset.mem_product.mp hx₂m.1).1).2
    have he₂V := (Finset.mem_filter.mp (Finset.mem_product.mp hx₂m.1).2).1
    have he₂m := (Finset.mem_filter.mp (Finset.mem_product.mp hx₂m.1).2).2
    have hr₁ := hx₁m.2.2
    have hr₂ := hx₂m.2.2
    have hpair₁ := (squarefree_prod_coord (hr₁.symm ▸ hrsf)).2
    have hpair₂ := (squarefree_prod_coord (hr₂.symm ▸ hrsf)).2
    have hd₁_sf : ∀ i, Squarefree (d₁ i) := fun i =>
      (squarefree_prod_coord ((mem_validTupleSet hR).mp hd₁V).2.2.1).1 i (Finset.mem_univ i)
    have he₁_sf : ∀ i, Squarefree (e₁ i) := fun i =>
      (squarefree_prod_coord ((mem_validTupleSet hR).mp he₁V).2.2.1).1 i (Finset.mem_univ i)
    have hd₂_sf : ∀ i, Squarefree (d₂ i) := fun i =>
      (squarefree_prod_coord ((mem_validTupleSet hR).mp hd₂V).2.2.1).1 i (Finset.mem_univ i)
    have he₂_sf : ∀ i, Squarefree (e₂ i) := fun i =>
      (squarefree_prod_coord ((mem_validTupleSet hR).mp he₂V).2.2.1).1 i (Finset.mem_univ i)
    -- Helper: unique index `pick d e p = i` when `p.Prime` and `p ∣ lcm(d i, e i)`
    have hpick_eq : ∀ {d e : Fin (k + 1) → ℕ} {i : Fin (k + 1)} {p : ℕ},
        (∀ a ∈ Em, ∀ b ∈ Em, a ≠ b → Nat.Coprime (Nat.lcm (d a) (e a)) (Nat.lcm (d b) (e b))) →
        i ∈ Em → p.Prime → p ∣ Nat.lcm (d i) (e i) → pick d e p = i := by
      intro d e i p hpair hi hpp hdiv
      have hex : ∃ j ∈ Em, p ∣ Nat.lcm (d j) (e j) := ⟨i, hi, hdiv⟩
      dsimp only [pick]; rw [dif_pos hex]
      by_contra hne
      have hcop := hpair hex.choose hex.choose_spec.1 i hi hne
      exact hpp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hcop) ▸ Nat.dvd_gcd hex.choose_spec.2 hdiv)
    have hpick_mem : ∀ {d e : Fin (k + 1) → ℕ}, ∏ i ∈ Em, Nat.lcm (d i) (e i) = r →
        ∀ p : ↥r.primeFactors, pick d e p.1 ∈ Em ∧ p.1 ∣ Nat.lcm (d (pick d e p.1)) (e (pick d e p.1)) := by
      intro d e hr p
      have hpp := Nat.prime_of_mem_primeFactors p.2
      have hpr : p.1 ∣ ∏ i ∈ Em, Nat.lcm (d i) (e i) := hr.symm ▸ Nat.dvd_of_mem_primeFactors p.2
      obtain ⟨i, hi, hdiv⟩ := hpp.prime.exists_mem_finset_dvd hpr
      have hex : ∃ j ∈ Em, p.1 ∣ Nat.lcm (d j) (e j) := ⟨i, hi, hdiv⟩
      dsimp only [pick]; rw [dif_pos hex]; exact hex.choose_spec
    -- Characterize `p ∣ d i` and `p ∣ e i` from `(pick, tag)`
    have hchar_d : ∀ i ∈ Em, (d₁ i).primeFactors = (d₂ i).primeFactors := by
      intro i hi; ext p; simp only [Nat.mem_primeFactors]
      constructor
      · rintro ⟨hpp, hpd1, _⟩
        have hpl1 : p ∣ Nat.lcm (d₁ i) (e₁ i) := dvd_trans hpd1 (Nat.dvd_lcm_left _ _)
        have hpr : p ∣ r := hr₁ ▸ dvd_trans hpl1 (Finset.dvd_prod_of_mem (fun j => Nat.lcm (d₁ j) (e₁ j)) hi)
        have hp_mem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpr, hrsf.ne_zero⟩
        have hpk1 : pick d₁ e₁ p = i := hpick_eq hpair₁ hi hpp hpl1
        have heqp := congrFun heq ⟨p, hp_mem⟩
        dsimp only [emb] at heqp
        have hpk2 : pick d₂ e₂ p = i := (congrArg Prod.fst heqp).symm.trans hpk1
        have htg : tag d₂ e₂ p i = tag d₁ e₁ p i := by
          have := congrArg Prod.snd heqp; rw [hpk1, hpk2] at this; exact this.symm
        have hpd2 : p ∣ d₂ i := by
          by_contra hnd2
          have h2 : tag d₂ e₂ p i = 1 := by dsimp only [tag]; rw [if_neg hnd2]
          dsimp only [tag] at htg; rw [if_pos hpd1] at htg
          split_ifs at htg <;> omega
        exact ⟨hpp, hpd2, (hd₂_sf i).ne_zero⟩
      · rintro ⟨hpp, hpd2, _⟩
        have hpl2 : p ∣ Nat.lcm (d₂ i) (e₂ i) := dvd_trans hpd2 (Nat.dvd_lcm_left _ _)
        have hpr : p ∣ r := hr₂ ▸ dvd_trans hpl2 (Finset.dvd_prod_of_mem (fun j => Nat.lcm (d₂ j) (e₂ j)) hi)
        have hp_mem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpr, hrsf.ne_zero⟩
        have hpk2 : pick d₂ e₂ p = i := hpick_eq hpair₂ hi hpp hpl2
        have heqp := congrFun heq ⟨p, hp_mem⟩
        dsimp only [emb] at heqp
        have hpk1 : pick d₁ e₁ p = i := (congrArg Prod.fst heqp).trans hpk2
        have htg : tag d₁ e₁ p i = tag d₂ e₂ p i := by
          have := congrArg Prod.snd heqp; rw [hpk1, hpk2] at this; exact this
        have hpd1 : p ∣ d₁ i := by
          by_contra hnd1
          have h1 : tag d₁ e₁ p i = 1 := by dsimp only [tag]; rw [if_neg hnd1]
          dsimp only [tag] at htg; rw [if_pos hpd2] at htg
          split_ifs at htg <;> omega
        exact ⟨hpp, hpd1, (hd₁_sf i).ne_zero⟩
    have hchar_e : ∀ i ∈ Em, (e₁ i).primeFactors = (e₂ i).primeFactors := by
      intro i hi; ext p; simp only [Nat.mem_primeFactors]
      constructor
      · rintro ⟨hpp, hpe1, _⟩
        have hpl1 : p ∣ Nat.lcm (d₁ i) (e₁ i) := dvd_trans hpe1 (Nat.dvd_lcm_right _ _)
        have hpr : p ∣ r := hr₁ ▸ dvd_trans hpl1 (Finset.dvd_prod_of_mem (fun j => Nat.lcm (d₁ j) (e₁ j)) hi)
        have hp_mem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpr, hrsf.ne_zero⟩
        have hpk1 : pick d₁ e₁ p = i := hpick_eq hpair₁ hi hpp hpl1
        have heqp := congrFun heq ⟨p, hp_mem⟩
        dsimp only [emb] at heqp
        have hpk2 : pick d₂ e₂ p = i := (congrArg Prod.fst heqp).symm.trans hpk1
        have hpl2 : p ∣ Nat.lcm (d₂ i) (e₂ i) := hpk2 ▸ (hpick_mem hr₂ ⟨p, hp_mem⟩).2
        have htg : tag d₂ e₂ p i = tag d₁ e₁ p i := by
          have := congrArg Prod.snd heqp; rw [hpk1, hpk2] at this; exact this.symm
        have hpe2 : p ∣ e₂ i := by
          by_contra hne2
          have hpd2 : p ∣ d₂ i := by
            rcases hpp.dvd_mul.mp (dvd_trans hpl2 (Nat.lcm_dvd_mul _ _)) with h | h
            · exact h
            · exact absurd h hne2
          have h2 : tag d₂ e₂ p i = 0 := by dsimp only [tag]; rw [if_pos hpd2, if_neg hne2]
          dsimp only [tag] at htg; rw [if_pos hpe1] at htg
          split_ifs at htg <;> omega
        exact ⟨hpp, hpe2, (he₂_sf i).ne_zero⟩
      · rintro ⟨hpp, hpe2, _⟩
        have hpl2 : p ∣ Nat.lcm (d₂ i) (e₂ i) := dvd_trans hpe2 (Nat.dvd_lcm_right _ _)
        have hpr : p ∣ r := hr₂ ▸ dvd_trans hpl2 (Finset.dvd_prod_of_mem (fun j => Nat.lcm (d₂ j) (e₂ j)) hi)
        have hp_mem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpr, hrsf.ne_zero⟩
        have hpk2 : pick d₂ e₂ p = i := hpick_eq hpair₂ hi hpp hpl2
        have heqp := congrFun heq ⟨p, hp_mem⟩
        dsimp only [emb] at heqp
        have hpk1 : pick d₁ e₁ p = i := (congrArg Prod.fst heqp).trans hpk2
        have hpl1 : p ∣ Nat.lcm (d₁ i) (e₁ i) := hpk1 ▸ (hpick_mem hr₁ ⟨p, hp_mem⟩).2
        have htg : tag d₁ e₁ p i = tag d₂ e₂ p i := by
          have := congrArg Prod.snd heqp; rw [hpk1, hpk2] at this; exact this
        have hpe1 : p ∣ e₁ i := by
          by_contra hne1
          have hpd1 : p ∣ d₁ i := by
            rcases hpp.dvd_mul.mp (dvd_trans hpl1 (Nat.lcm_dvd_mul _ _)) with h | h
            · exact h
            · exact absurd h hne1
          have h1 : tag d₁ e₁ p i = 0 := by dsimp only [tag]; rw [if_pos hpd1, if_neg hne1]
          dsimp only [tag] at htg; rw [if_pos hpe2] at htg
          split_ifs at htg <;> omega
        exact ⟨hpp, hpe1, (he₁_sf i).ne_zero⟩
    dsimp only at hd₁m hd₂m he₁m he₂m
    apply Prod.ext <;> (ext i; dsimp only)
    · by_cases hi : i = m
      · rw [hi, hd₁m, hd₂m]
      · have hi' : i ∈ Em := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
        rw [← Nat.prod_primeFactors_of_squarefree (hd₁_sf i), ← Nat.prod_primeFactors_of_squarefree (hd₂_sf i),
          hchar_d i hi']
    · by_cases hi : i = m
      · rw [hi, he₁m, he₂m]
      · have hi' : i ∈ Em := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
        rw [← Nat.prod_primeFactors_of_squarefree (he₁_sf i), ← Nat.prod_primeFactors_of_squarefree (he₂_sf i),
          hchar_e i hi']
  have hnat : S.card ≤ (3 * (k + 1)) ^ r.primeFactors.card := by
    have h1 := Finset.card_le_card_of_injOn emb (fun _ _ => Finset.mem_univ _) hinj
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_coe, mul_comm (k + 1) 3] at h1
    exact h1
  exact_mod_cast hnat

/-- **Prime-Weighted Sieve Sum `S₁^{(m)}` Lower Bound via Bombieri–Vinogradov (`ϑ = 1/2`)**:
for fixed `D₀ ≥ 6`, tuple `h : Fin (k + 1) ↪ ℕ` with pairwise differences `≤ D₀`, W-trick residue `b`,
test function `T`, and coordinate `m : Fin (k + 1)`:
there exist `B_bv > 0` and `C_err ≥ 0` such that on every subinterval `[A, B) ⊆ [X, 2X]` with
`W D₀ * R² ≤ √(A + h m - 1) / (log (3 X))^B_bv`:
`S₁^{(m)}([A, B)) ≥ ((π(B + h m - 1) - π(A + h m - 1)) / φ(W D₀)) * Q1Sum (W D₀) R T m - C_err * X / (log X)^4`. -/
theorem S1_m_interval_lower {k D₀ : ℕ} (hD : 6 ≤ D₀) {h : Fin (k + 1) ↪ ℕ}
    (hdiff : ∀ i j : Fin (k + 1), i ≠ j → (h i : ℤ) - (h j : ℤ) ≠ 0 ∧ |(h i : ℤ) - (h j : ℤ)| ≤ (D₀ : ℤ))
    {b : ℕ} (hcop_b : ∀ i : Fin (k + 1), Nat.Coprime (b + h i) (W D₀))
    (T : SimplexTestFn (k + 1)) (m : Fin (k + 1)) :
    ∃ B_bv C_err : ℝ, 0 < B_bv ∧ 0 ≤ C_err ∧
      ∀ (X A B : ℕ) (R : ℝ),
        16 ≤ X → X ≤ A → A ≤ B → B ≤ 2 * X → h m ≤ X →
        Real.exp 4 ≤ R → R < (X : ℝ) →
        (W D₀ : ℝ) * R ^ 2 ≤ Real.sqrt ((A + h m - 1 : ℕ) : ℝ) / (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv →
        ((((Finset.range (B + h m)).filter Nat.Prime).card : ℝ) -
          (((Finset.range (A + h m)).filter Nat.Prime).card : ℝ)) / (((W D₀).totient : ℝ)) *
          Q1Sum (W D₀) R T m -
          C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 ≤
        ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W D₀] ∧ Nat.Prime (n + h m)),
          sieveWeight h (W D₀) R T n := by
  set W₀ := W D₀
  have hW_pos : 1 ≤ W₀ := W_pos D₀
  set M_k : ℕ := 3 * (k + 1)
  set A_bv : ℝ := ((M_k ^ 2 : ℕ) : ℝ) + 8 * ((k + 1 : ℕ) : ℝ) + 12
  obtain ⟨B_bv, C_bv, hBbv_pos, hCbv_pos, hBV⟩ := RHDirect.Chen.bombieri_vinogradov_primes A_bv
  -- Constants for `L_max² * √(...)`
  set C_lam : ℝ := T.bound * (12 * Real.exp 2) ^ (k + 1)
  have hClam_nn : 0 ≤ C_lam := mul_nonneg T.bound_nonneg (by positivity)
  set C_cs : ℝ := Real.sqrt ((3 : ℝ) ^ (M_k ^ 2) * (54 * Real.exp 2 * C_bv * (2 : ℝ) ^ A_bv))
  set C_err : ℝ := 2 * C_lam ^ 2 * C_cs
  refine ⟨B_bv, C_err, hBbv_pos, by positivity, fun X A B R hX16 hXA hAB hB2X hhmX hR hRX hQR => ?_⟩
  have hR_pos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hR
  have hR1 : 1 ≤ R := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hR
  have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogX_ge2 : 2 ≤ Real.log (X : ℝ) := by
    have h1 : Real.exp 2 ≤ (16 : ℝ) := by
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le he 2
        _ ≤ 16 := by norm_num
    have h2 : Real.exp 2 ≤ (X : ℝ) := h1.trans (by exact_mod_cast hX16)
    have h3 := Real.log_le_log (Real.exp_pos 2) h2
    rwa [Real.log_exp] at h3
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hlog3X_le : Real.log ((3 * X : ℕ) : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (by norm_num) hX_pos.ne']
    have : Real.log ((3 : ℕ) : ℝ) ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ X by omega))
    linarith
  set Vm := (validTupleSet k W₀ R).filter (fun d => d m = 1)
  set Em : Finset (Fin (k + 1)) := Finset.univ.erase m
  -- Step 1: For every `n ∈ [A, B)` with `Nat.Prime (n + h m)`, `d m ∣ n + h m` forces `d m = 1`!
  have hweight_prime : ∀ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m)),
      sieveWeight h W₀ R T n =
        (∑ d ∈ Vm.filter (fun d => ∀ i ∈ Em, d i ∣ n + h i), lamVar W₀ R T d) ^ 2 := by
    intro n hn
    have hnA : A ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
    have hprime : Nat.Prime (n + h m) := (Finset.mem_filter.mp hn).2.2
    unfold sieveWeight
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d; simp only [Vm, Finset.mem_filter]
    constructor
    · rintro ⟨hdV, hdiv⟩
      obtain ⟨hd1, hd_prod, _, _⟩ := (mem_validTupleSet hR_pos.le).mp hdV
      have hdm_le : (d m : ℝ) ≤ R :=
        le_trans (by exact_mod_cast Finset.single_le_prod' (f := d) (fun j _ => hd1 j) (Finset.mem_univ m)) hd_prod
      have hdm_lt : d m < n + h m := by
        have : (d m : ℝ) < (n + h m : ℝ) := hdm_le.trans_lt (hRX.trans_le (by exact_mod_cast (show X ≤ n + h m by omega)))
        exact_mod_cast this
      have hdm1 : d m = 1 := by
        rcases hprime.eq_one_or_self_of_dvd (d m) (hdiv m) with h1 | hself
        · exact h1
        · omega
      exact ⟨⟨hdV, hdm1⟩, fun i _ => hdiv i⟩
    · rintro ⟨⟨hdV, hdm1⟩, hdiv⟩
      refine ⟨hdV, fun i => ?_⟩
      by_cases hi : i = m
      · subst hi; rw [hdm1]; exact one_dvd _
      · exact hdiv i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  -- Step 2: Expand the square and swap sums
  have hexpand : ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m)),
        sieveWeight h W₀ R T n =
      ∑ d ∈ Vm, ∑ e ∈ Vm,
        lamVar W₀ R T d * lamVar W₀ R T e *
          ((((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m) ∧
              ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i)).card : ℝ)) := by
    rw [Finset.sum_congr rfl hweight_prime]
    have h1 : ∀ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m)),
        (∑ d ∈ Vm.filter (fun d => ∀ i ∈ Em, d i ∣ n + h i), lamVar W₀ R T d) ^ 2 =
        ∑ d ∈ Vm, ∑ e ∈ Vm,
          if (∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i) then lamVar W₀ R T d * lamVar W₀ R T e else 0 := by
      intro n _
      rw [sq, Finset.sum_mul_sum, Finset.sum_filter (s := Vm)]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd_div : ∀ i ∈ Em, d i ∣ n + h i
      · rw [if_pos hd_div, Finset.sum_filter (s := Vm)]
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases he_div : ∀ i ∈ Em, e i ∣ n + h i
        · rw [if_pos he_div, if_pos fun i hi => Nat.lcm_dvd (hd_div i hi) (he_div i hi)]
        · rw [if_neg he_div, if_neg fun hl => he_div fun i hi => dvd_trans (Nat.dvd_lcm_right _ _) (hl i hi)]
      · rw [if_neg hd_div]; symm
        refine Finset.sum_eq_zero fun e _ => ?_
        rw [if_neg fun hl => hd_div fun i hi => dvd_trans (Nat.dvd_lcm_left _ _) (hl i hi)]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hfeq : ((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m))).filter
          (fun n => ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i) =
        (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m) ∧
          ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i) := by ext n; simp [and_assoc]
    rw [hfeq]
  rw [hexpand]
  -- Define `E_sup x q` matching `Chen.bombieri_vinogradov_primes`
  let E_sup : ℝ → ℕ → ℝ := fun x q =>
    if hq : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
      ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' hq
        (fun a => |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
          (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|)
    else 0
  set y₁ : ℝ := ((A + h m - 1 : ℕ) : ℝ)
  set y₂ : ℝ := ((B + h m - 1 : ℕ) : ℝ)
  set Δπ : ℝ := (((Finset.range (B + h m)).filter Nat.Prime).card : ℝ) -
    (((Finset.range (A + h m)).filter Nat.Prime).card : ℝ)
  have coprime_lcm_left : ∀ {a c₁ c₂ : ℕ}, Nat.Coprime a c₂ → Nat.Coprime c₁ c₂ → Nat.Coprime (Nat.lcm a c₁) c₂ :=
    fun ha hb => (ha.mul_left hb).coprime_dvd_left (Nat.lcm_dvd_mul _ _)
  have coprime_lcm_right : ∀ {a c₁ c₂ : ℕ}, Nat.Coprime c₂ a → Nat.Coprime c₂ c₁ → Nat.Coprime c₂ (Nat.lcm a c₁) :=
    fun ha hb => (coprime_lcm_left ha.symm hb.symm).symm
  -- Step 3: For each `(d, e) ∈ Vm × Vm`, evaluate count via CRT + `primeCountAP`
  have hde_err : ∀ d ∈ Vm, ∀ e ∈ Vm,
      (if PairwiseCoprimeCross d e then
        lamVar W₀ R T d * lamVar W₀ R T e *
          (Δπ / (((W₀).totient : ℝ) * ∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ))) -
        |lamVar W₀ R T d| * |lamVar W₀ R T e| *
          (E_sup y₂ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)) + E_sup y₁ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)))
      else 0) ≤
      lamVar W₀ R T d * lamVar W₀ R T e *
        ((((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m) ∧
            ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i)).card : ℝ)) := by
    intro d hd e he
    have hdV := (Finset.mem_filter.mp hd).1; have hdm := (Finset.mem_filter.mp hd).2
    have heV := (Finset.mem_filter.mp he).1; have hem := (Finset.mem_filter.mp he).2
    obtain ⟨hd1, _, hd_sf, hd_cop⟩ := (mem_validTupleSet hR_pos.le).mp hdV
    obtain ⟨he1, _, he_sf, he_cop⟩ := (mem_validTupleSet hR_pos.le).mp heV
    by_cases hpc : PairwiseCoprimeCross d e
    · rw [if_pos hpc]
      let M : Option (↥Em) → ℕ
        | none => W₀
        | some i => Nat.lcm (d i.1) (e i.1)
      let c : Option (↥Em) → ℕ
        | none => b
        | some i => (M (some i) - h i.1 % M (some i)) % M (some i)
      have hM_cop : ∀ x ∈ (Finset.univ : Finset (Option (↥Em))),
          ∀ y ∈ (Finset.univ : Finset (Option (↥Em))), x ≠ y → Nat.Coprime (M x) (M y) := by
        intro x _ y _ hxy
        have hd_cop_i : ∀ i, Nat.Coprime (d i) W₀ := fun i =>
          hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
        have he_cop_i : ∀ i, Nat.Coprime (e i) W₀ := fun i =>
          he_cop.coprime_dvd_left (Finset.dvd_prod_of_mem e (Finset.mem_univ i))
        have hd_pair := (squarefree_prod_coord hd_sf).2
        have he_pair := (squarefree_prod_coord he_sf).2
        cases x with
        | none =>
          cases y with
          | none => exact absurd rfl hxy
          | some j => dsimp only [M]; exact (coprime_lcm_left (hd_cop_i j.1) (he_cop_i j.1)).symm
        | some i =>
          cases y with
          | none => dsimp only [M]; exact coprime_lcm_left (hd_cop_i i.1) (he_cop_i i.1)
          | some j =>
            have hij : i.1 ≠ j.1 := fun h => hxy (congrArg some (Subtype.ext h))
            dsimp only [M]
            exact coprime_lcm_left
              (coprime_lcm_right (hd_pair i.1 (Finset.mem_univ _) j.1 (Finset.mem_univ _) hij) (hpc i.1 j.1 hij))
              (coprime_lcm_right (hpc j.1 i.1 hij.symm).symm (he_pair i.1 (Finset.mem_univ _) j.1 (Finset.mem_univ _) hij))
      obtain ⟨x₀, hx₀⟩ := exists_crt_finset Finset.univ M c hM_cop
      set q := W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)
      have hMprod : ∏ x : Option (↥Em), M x = q := by
        rw [Fintype.prod_option]; dsimp only [M, q]; congr 1
        exact Finset.prod_attach Em (fun i => Nat.lcm (d i) (e i))
      have hq_pos : 1 ≤ q := Nat.mul_pos hW_pos (Finset.prod_pos fun i _ => Nat.lcm_pos (hd1 i) (he1 i))
      have hc_add : ∀ i : ↥Em, c (some i) + h i.1 ≡ 0 [MOD Nat.lcm (d i.1) (e i.1)] := fun i => by
        dsimp only [c, M]
        have hmpos : 0 < Nat.lcm (d i.1) (e i.1) := Nat.lcm_pos (hd1 i.1) (he1 i.1)
        have hlt : h i.1 % Nat.lcm (d i.1) (e i.1) < Nat.lcm (d i.1) (e i.1) := Nat.mod_lt _ hmpos
        rw [Nat.ModEq, Nat.add_mod, Nat.mod_mod, Nat.mod_add_mod, Nat.sub_add_cancel hlt.le, Nat.mod_self, Nat.zero_mod]
      have hcond_iff : ∀ n : ℕ, (n ≡ b [MOD W₀] ∧ ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i) ↔ n ≡ x₀ [MOD q] := by
        intro n; rw [← hMprod, ← hx₀ n]
        constructor
        · rintro ⟨hnb, hdiv⟩ x _
          cases x with
          | none => exact hnb
          | some i =>
            dsimp only [M]
            exact Nat.ModEq.add_right_cancel' (h i.1) ((Nat.modEq_zero_iff_dvd.mpr (hdiv i.1 i.2)).trans (hc_add i).symm)
        · intro hall
          refine ⟨hall none (Finset.mem_univ none), fun i hi => ?_⟩
          exact Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_right (h i) (hall (some ⟨i, hi⟩) (Finset.mem_univ _))).trans (hc_add ⟨i, hi⟩))
      set a_res := (x₀ + h m) % q
      -- Show `Nat.Coprime a_res q`
      have ha_cop : Nat.Coprime a_res q := by
        have hx0_cond := (hcond_iff x₀).mpr (Nat.ModEq.refl x₀)
        have hcop_x0 : Nat.Coprime (x₀ + h m) q := by
          dsimp only [q]
          refine Nat.Coprime.mul_right ?_ (Nat.Coprime.prod_right fun i hi => ?_)
          · -- `x₀ + h m ≡ b + h m [MOD W₀]`, and `Coprime (b + h m) W₀`
            have hmod : x₀ + h m ≡ b + h m [MOD W₀] := Nat.ModEq.add_right (h m) hx0_cond.1
            have h1 : Nat.gcd (x₀ + h m) W₀ = Nat.gcd (b + h m) W₀ := by
              rw [Nat.gcd_comm (x₀ + h m) W₀, Nat.gcd_rec W₀, Nat.gcd_comm (b + h m) W₀, Nat.gcd_rec W₀,
                show (x₀ + h m) % W₀ = (b + h m) % W₀ from hmod]
            rw [Nat.coprime_iff_gcd_eq_one, h1]; exact Nat.coprime_iff_gcd_eq_one.mp (hcop_b m)
          · -- Any prime `p ∣ x₀ + h m` and `p ∣ lcm(d i, e i)` divides `|h m - h i| ≤ D₀`, contradicting `Coprime lcm W₀`!
            rw [Nat.coprime_iff_gcd_eq_one]
            by_contra hne1
            obtain ⟨p, hpp, hpgcd⟩ := Nat.exists_prime_and_dvd hne1
            have hpm : p ∣ x₀ + h m := dvd_trans hpgcd (Nat.gcd_dvd_left _ _)
            have hpl : p ∣ Nat.lcm (d i) (e i) := dvd_trans hpgcd (Nat.gcd_dvd_right _ _)
            have hpi : p ∣ x₀ + h i := dvd_trans hpl (hx0_cond.2 i hi)
            have hp_int : (p : ℤ) ∣ (h m : ℤ) - (h i : ℤ) := by
              have hmZ : (p : ℤ) ∣ (x₀ : ℤ) + (h m : ℤ) := by exact_mod_cast hpm
              have hiZ : (p : ℤ) ∣ (x₀ : ℤ) + (h i : ℤ) := by exact_mod_cast hpi
              simpa using dvd_sub hmZ hiZ
            have hmi : m ≠ i := (Finset.mem_erase.mp hi).1.symm
            have hneZ := (hdiff m i hmi).1; have habsZ := (hdiff m i hmi).2
            have hpD : p ≤ D₀ := by
              have h1 := Nat.le_of_dvd (Int.natAbs_pos.mpr hneZ) (Int.natCast_dvd.mp hp_int)
              have h2 : (((h m : ℤ) - (h i : ℤ)).natAbs : ℤ) = |(h m : ℤ) - (h i : ℤ)| := Int.natCast_natAbs _
              omega
            have hpW : p ∣ W₀ := (prime_dvd_W_iff hpp).mpr hpD
            have hcop_lW : Nat.Coprime (Nat.lcm (d i) (e i)) W₀ :=
              coprime_lcm_left (hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i)))
                (he_cop.coprime_dvd_left (Finset.dvd_prod_of_mem e (Finset.mem_univ i)))
            exact hpp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp hcop_lW) ▸ Nat.dvd_gcd hpl hpW)
        have hgcd : Nat.gcd a_res q = Nat.gcd (x₀ + h m) q := by
          dsimp only [a_res]; rw [Nat.gcd_comm (x₀ + h m) q, Nat.gcd_rec q (x₀ + h m)]
        rw [Nat.coprime_iff_gcd_eq_one, hgcd]; exact Nat.coprime_iff_gcd_eq_one.mp hcop_x0
      -- Exact count in terms of `primeCountAP q a_res y₂ - primeCountAP q a_res y₁`
      have hcnt_eq : ((((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m) ∧
              ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i)).card : ℝ)) =
          (Stage2DirichletAP.primeCountAP q a_res y₂ : ℝ) -
            (Stage2DirichletAP.primeCountAP q a_res y₁ : ℝ) := by
        have hy₁_fl : ⌊y₁⌋₊ + 1 = A + h m := by
          dsimp only [y₁]; rw [Nat.floor_natCast]; omega
        have hy₂_fl : ⌊y₂⌋₊ + 1 = B + h m := by
          dsimp only [y₂]; rw [Nat.floor_natCast]; omega
        have hsub_r : (Finset.range (A + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q]) ⊆
            (Finset.range (B + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q]) :=
          Finset.filter_subset_filter _ (Finset.range_mono (by omega))
        have hcard_bij : ((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m) ∧
              ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i)).card +
            ((Finset.range (A + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q])).card =
            ((Finset.range (B + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q])).card := by
          have hsdiff : ((Finset.range (B + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q])) \
              ((Finset.range (A + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q])) =
              (Finset.Ico (A + h m) (B + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q]) := by
            ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
            constructor
            · rintro ⟨⟨hpB, hp⟩, hnot⟩
              refine ⟨⟨?_, hpB⟩, hp⟩
              by_contra hlt; exact hnot ⟨by omega, hp⟩
            · rintro ⟨⟨hpA, hpB⟩, hp⟩
              exact ⟨⟨hpB, hp⟩, fun h => by omega⟩
          have hshift : ((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m) ∧
                ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i)).card =
              ((Finset.Ico (A + h m) (B + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q])).card := by
            refine Finset.card_bij (fun n _ => n + h m) ?_ ?_ ?_
            · intro n hn
              simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
              refine ⟨⟨by omega, by omega⟩, hn.2.2.1, ?_⟩
              have hnx : n ≡ x₀ [MOD q] := (hcond_iff n).mp ⟨hn.2.1, hn.2.2.2⟩
              exact (Nat.ModEq.add_right (h m) hnx).trans (Nat.mod_modEq (x₀ + h m) q).symm
            · intro n₁ _ n₂ _ heq; omega
            · intro p hp
              simp only [Finset.mem_filter, Finset.mem_Ico] at hp
              refine ⟨p - h m, ?_, Nat.sub_add_cancel (by omega)⟩
              simp only [Finset.mem_filter, Finset.mem_Ico]
              have hmod : (p - h m) + h m ≡ x₀ + h m [MOD q] := by
                rw [Nat.sub_add_cancel (by omega)]
                exact hp.2.2.trans (Nat.mod_modEq (x₀ + h m) q)
              have hnx := (hcond_iff (p - h m)).mpr (Nat.ModEq.add_right_cancel' (h m) hmod)
              refine ⟨⟨by omega, by omega⟩, hnx.1, ?_, hnx.2⟩
              rw [Nat.sub_add_cancel (by omega)]; exact hp.2.1
          rw [hshift, ← hsdiff, Finset.card_sdiff_add_card_eq_card hsub_r]
        unfold Stage2DirichletAP.primeCountAP
        rw [hy₁_fl, hy₂_fl]
        have hR : (((Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m) ∧
              ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i)).card : ℝ) +
            (((Finset.range (A + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q])).card : ℝ) =
            (((Finset.range (B + h m)).filter (fun p => p.Prime ∧ p ≡ a_res [MOD q])).card : ℝ) := by
          exact_mod_cast hcard_bij
        linarith
      -- `q.totient = W₀.totient * ∏_{i ∈ Em} (lcm(d i, e i)).totient`
      have hphi_q : (q.totient : ℝ) = ((W₀.totient : ℝ)) * ∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ) := by
        have hq_nat : q.totient = W₀.totient * ∏ i ∈ Em, (Nat.lcm (d i) (e i)).totient := by
          rw [← hMprod, totient_prod_of_pairwise_coprime Finset.univ M hM_cop, Fintype.prod_option]
          dsimp only [M]; congr 1
          exact Finset.prod_attach Em (fun i => (Nat.lcm (d i) (e i)).totient)
        exact_mod_cast hq_nat
      -- Bound `|(primeCountAP y₂ - primeCountAP y₁) - Δπ / φ(q)| ≤ E_sup y₂ q + E_sup y₁ q`
      have ha_mem : a_res ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq_pos), ha_cop⟩
      have hne_q : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty := ⟨a_res, ha_mem⟩
      have hE2 : |(Stage2DirichletAP.primeCountAP q a_res y₂ : ℝ) -
            (((Finset.range (B + h m)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)| ≤ E_sup y₂ q := by
        have hy₂_fl : ⌊y₂⌋₊ + 1 = B + h m := by dsimp only [y₂]; rw [Nat.floor_natCast]; omega
        dsimp only [E_sup]; rw [dif_pos hne_q, hy₂_fl]
        exact Finset.le_sup' (f := fun a => |(Stage2DirichletAP.primeCountAP q a y₂ : ℝ) -
          (((Finset.range (B + h m)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|) ha_mem
      have hE1 : |(Stage2DirichletAP.primeCountAP q a_res y₁ : ℝ) -
            (((Finset.range (A + h m)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)| ≤ E_sup y₁ q := by
        have hy₁_fl : ⌊y₁⌋₊ + 1 = A + h m := by dsimp only [y₁]; rw [Nat.floor_natCast]; omega
        dsimp only [E_sup]; rw [dif_pos hne_q, hy₁_fl]
        exact Finset.le_sup' (f := fun a => |(Stage2DirichletAP.primeCountAP q a y₁ : ℝ) -
          (((Finset.range (A + h m)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|) ha_mem
      have herr_cnt : |((Stage2DirichletAP.primeCountAP q a_res y₂ : ℝ) -
            (Stage2DirichletAP.primeCountAP q a_res y₁ : ℝ)) - Δπ / (q.totient : ℝ)| ≤
          E_sup y₂ q + E_sup y₁ q := by
        have hrew : ((Stage2DirichletAP.primeCountAP q a_res y₂ : ℝ) -
              (Stage2DirichletAP.primeCountAP q a_res y₁ : ℝ)) - Δπ / (q.totient : ℝ) =
            ((Stage2DirichletAP.primeCountAP q a_res y₂ : ℝ) -
              (((Finset.range (B + h m)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)) -
            ((Stage2DirichletAP.primeCountAP q a_res y₁ : ℝ) -
              (((Finset.range (A + h m)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)) := by
          dsimp only [Δπ]; ring
        rw [hrew]
        exact (abs_sub _ _).trans (add_le_add hE2 hE1)
      rw [hcnt_eq, ← hphi_q]
      set diff := ((Stage2DirichletAP.primeCountAP q a_res y₂ : ℝ) -
        (Stage2DirichletAP.primeCountAP q a_res y₁ : ℝ)) - Δπ / (q.totient : ℝ)
      have hmul_abs : -(lamVar W₀ R T d * lamVar W₀ R T e * diff) ≤
          |lamVar W₀ R T d| * |lamVar W₀ R T e| * (E_sup y₂ q + E_sup y₁ q) := by
        calc -(lamVar W₀ R T d * lamVar W₀ R T e * diff)
            ≤ |lamVar W₀ R T d * lamVar W₀ R T e * diff| := neg_le_abs _
          _ = |lamVar W₀ R T d| * |lamVar W₀ R T e| * |diff| := by rw [abs_mul, abs_mul]
          _ ≤ |lamVar W₀ R T d| * |lamVar W₀ R T e| * (E_sup y₂ q + E_sup y₁ q) :=
              mul_le_mul_of_nonneg_left herr_cnt (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      dsimp only [diff] at hmul_abs; linarith
    · -- `¬ PairwiseCoprimeCross d e`: filtered set is empty!
      rw [if_neg hpc]
      have hempty : (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h m) ∧
          ∀ i ∈ Em, Nat.lcm (d i) (e i) ∣ n + h i) = ∅ := by
        ext n; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ _ _ hdiv
        unfold PairwiseCoprimeCross at hpc; push Not at hpc
        obtain ⟨i, j, hij, hnc⟩ := hpc
        have him : i ≠ m := fun hi => hnc (by rw [hi, hdm]; exact Nat.coprime_one_left _)
        have hjm : j ≠ m := fun hj => hnc (by rw [hj, hem]; exact Nat.coprime_one_right _)
        obtain ⟨p, hpp, hpgcd⟩ := Nat.exists_prime_and_dvd hnc
        have hpd : p ∣ d i := dvd_trans hpgcd (Nat.gcd_dvd_left _ _)
        have hpe : p ∣ e j := dvd_trans hpgcd (Nat.gcd_dvd_right _ _)
        have hpni : p ∣ n + h i := dvd_trans hpd (dvd_trans (Nat.dvd_lcm_left _ _) (hdiv i (Finset.mem_erase.mpr ⟨him, Finset.mem_univ i⟩)))
        have hpnj : p ∣ n + h j := dvd_trans hpe (dvd_trans (Nat.dvd_lcm_right _ _) (hdiv j (Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩)))
        have hp_int : (p : ℤ) ∣ (h i : ℤ) - (h j : ℤ) := by
          have hiZ : (p : ℤ) ∣ (n : ℤ) + (h i : ℤ) := by exact_mod_cast hpni
          have hjZ : (p : ℤ) ∣ (n : ℤ) + (h j : ℤ) := by exact_mod_cast hpnj
          simpa using dvd_sub hiZ hjZ
        have hpD : p ≤ D₀ := by
          have h1 := Nat.le_of_dvd (Int.natAbs_pos.mpr (hdiff i j hij).1) (Int.natCast_dvd.mp hp_int)
          have h2 : (((h i : ℤ) - (h j : ℤ)).natAbs : ℤ) = |(h i : ℤ) - (h j : ℤ)| := Int.natCast_natAbs _
          have := (hdiff i j hij).2; omega
        have hpW : p ∣ W₀ := (prime_dvd_W_iff hpp).mpr hpD
        exact hpp.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp
          (hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem d (Finset.mem_univ i)))) ▸ Nat.dvd_gcd hpd hpW)
      rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
  -- Step 4: Bound the Bombieri–Vinogradov error sum via Cauchy–Schwarz + `sum_pow_omega_div_le`!
  have hLmax : ∀ d : Fin (k + 1) → ℕ, |lamVar W₀ R T d| ≤ C_lam * (Real.log (X : ℝ)) ^ (2 * (k + 1)) := by
    intro d
    have h1 := abs_lamVar_le (W₀ := W₀) hR T d
    have hlogR_le : Real.log R ≤ Real.log (X : ℝ) := Real.log_le_log hR_pos hRX.le
    have hlog2R_le : Real.log (2 * R) ≤ 2 * Real.log (X : ℝ) := by
      have h2R : 2 * R ≤ (3 * X : ℕ) := by push_cast; linarith
      exact (Real.log_le_log (by positivity) h2R).trans hlog3X_le
    have hbase : Real.exp 2 * Real.log R * (6 * Real.log (2 * R)) ≤ 12 * Real.exp 2 * (Real.log (X : ℝ)) ^ 2 := by
      have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR1
      have hlog2R_nn : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
      calc Real.exp 2 * Real.log R * (6 * Real.log (2 * R))
          ≤ Real.exp 2 * Real.log (X : ℝ) * (6 * (2 * Real.log (X : ℝ))) := by gcongr
        _ = 12 * Real.exp 2 * (Real.log (X : ℝ)) ^ 2 := by ring
    calc |lamVar W₀ R T d|
        ≤ T.bound * (Real.exp 2 * Real.log R * (6 * Real.log (2 * R))) ^ (k + 1) := h1
      _ ≤ T.bound * (12 * Real.exp 2 * (Real.log (X : ℝ)) ^ 2) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have := Real.log_nonneg hR1; have := Real.log_nonneg (by linarith : 1 ≤ 2 * R); positivity) hbase _) T.bound_nonneg
      _ = C_lam * (Real.log (X : ℝ)) ^ (2 * (k + 1)) := by
          dsimp only [C_lam]; rw [mul_pow, ← pow_mul]; ring
  -- Helper: bound `∑_{q ≤ Q_x, sqfree} M_k^{ω(q)} * E_sup x q` for `x ∈ {y₁, y₂}`
  have hCS_bv : ∀ x : ℝ, (A + h m - 1 : ℕ) ≤ x → x ≤ (3 * X : ℕ) →
      ∑ q ∈ (Finset.Icc 1 ⌊(W₀ : ℝ) * R ^ 2⌋₊).filter Squarefree,
          ((M_k : ℝ) ^ (q.primeFactors.card)) * E_sup x q ≤
        C_cs * (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * (k + 1) + 4) := by
    intro x hx_lo hx_hi
    have hx15 : (15 : ℝ) ≤ x := le_trans (by exact_mod_cast (show 15 ≤ A + h m - 1 by omega)) hx_lo
    have hx4 : 4 ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    have hx_halfX : Real.sqrt (X : ℝ) ≤ x := by
      have hsq : Real.sqrt (X : ℝ) ≤ (X : ℝ) - 1 := by
        have h1 : Real.sqrt (X : ℝ) ≤ (X : ℝ) / 4 := by
          have hsq4 : (Real.sqrt (X : ℝ)) ^ 2 ≤ ((X : ℝ) / 4) ^ 2 := by
            rw [Real.sq_sqrt hX_pos.le]; nlinarith [show (16 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX16]
          nlinarith [Real.sqrt_nonneg (X : ℝ)]
        linarith [show (16 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX16]
      have hlo' : (X : ℝ) - 1 ≤ x := by
        have : X - 1 ≤ A + h m - 1 := by omega
        have hR' : ((X - 1 : ℕ) : ℝ) ≤ ((A + h m - 1 : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega : 1 ≤ X), Nat.cast_one] at hR'
        linarith
      linarith
    have hlogx_ge : Real.log (X : ℝ) / 2 ≤ Real.log x := by
      have h1 := Real.log_le_log (Real.sqrt_pos.mpr hX_pos) hx_halfX
      rwa [Real.log_sqrt hX_pos.le] at h1
    have hlogx_pos : 0 < Real.log x := by linarith
    set Q_bv : ℕ := ⌊Real.sqrt x / (Real.log x) ^ B_bv⌋₊
    set Q_R : ℕ := ⌊(W₀ : ℝ) * R ^ 2⌋₊
    have hQR_le_Qb : Q_R ≤ Q_bv := by
      refine Nat.floor_mono ?_
      have hlogx_le : Real.log x ≤ Real.log ((3 * X : ℕ) : ℝ) := Real.log_le_log hx_pos hx_hi
      have hpow_le : (Real.log x) ^ B_bv ≤ (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv :=
        Real.rpow_le_rpow hlogx_pos.le hlogx_le hBbv_pos.le
      calc (W₀ : ℝ) * R ^ 2
          ≤ Real.sqrt ((A + h m - 1 : ℕ) : ℝ) / (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv := hQR
        _ ≤ Real.sqrt x / (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv :=
            div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hx_lo) (by positivity)
        _ ≤ Real.sqrt x / (Real.log x) ^ B_bv :=
            div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (Real.rpow_pos_of_pos hlogx_pos _) hpow_le
    have hsubQ : (Finset.Icc 1 Q_R).filter Squarefree ⊆ Finset.Icc 1 Q_bv :=
      fun q hq => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1,
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2.trans hQR_le_Qb⟩
    have hQR_le_3X : Q_R ≤ 3 * X := by
      have h1 : (Q_R : ℝ) ≤ (W₀ : ℝ) * R ^ 2 := Nat.floor_le (by positivity)
      have h2 : (W₀ : ℝ) * R ^ 2 ≤ Real.sqrt x := by
        have hlogx_ge1 : 1 ≤ Real.log x := by linarith
        have hpow_ge1 : 1 ≤ (Real.log x) ^ B_bv := Real.one_le_rpow hlogx_ge1 hBbv_pos.le
        calc (W₀ : ℝ) * R ^ 2 ≤ Real.sqrt x / (Real.log x) ^ B_bv := by
              have hlogx_le : Real.log x ≤ Real.log ((3 * X : ℕ) : ℝ) := Real.log_le_log hx_pos hx_hi
              have hpow_le : (Real.log x) ^ B_bv ≤ (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv :=
                Real.rpow_le_rpow hlogx_pos.le hlogx_le hBbv_pos.le
              exact hQR.trans ((div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hx_lo) (by positivity)).trans
                (div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (Real.rpow_pos_of_pos hlogx_pos _) hpow_le))
          _ ≤ Real.sqrt x := div_le_self (Real.sqrt_nonneg x) hpow_ge1
      have h3 : Real.sqrt x ≤ x := by nlinarith [Real.sq_sqrt hx_pos.le, Real.sqrt_nonneg x]
      exact_mod_cast (h1.trans (h2.trans (h3.trans hx_hi)))
    -- Pointwise trivial bound `q * E_sup x q ≤ 3 * x * Real.exp 2 * Real.log (3 * X)` for `1 ≤ q ≤ Q_R`
    have htriv : ∀ q ∈ (Finset.Icc 1 Q_R).filter Squarefree,
        (q : ℝ) * E_sup x q ≤ 3 * x * (Real.exp 2 * Real.log ((3 * X : ℕ) : ℝ)) := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      have hqQR : q ≤ Q_R := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
      have hq_le_sqrt : (q : ℝ) ≤ Real.sqrt x := by
        have h1 : (q : ℝ) ≤ (W₀ : ℝ) * R ^ 2 := (Nat.cast_le.mpr hqQR).trans (Nat.floor_le (by positivity))
        have hlogx_ge1 : 1 ≤ Real.log x := by linarith
        have hpow_ge1 : 1 ≤ (Real.log x) ^ B_bv := Real.one_le_rpow hlogx_ge1 hBbv_pos.le
        have hlogx_le : Real.log x ≤ Real.log ((3 * X : ℕ) : ℝ) := Real.log_le_log hx_pos hx_hi
        have hpow_le : (Real.log x) ^ B_bv ≤ (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv :=
          Real.rpow_le_rpow hlogx_pos.le hlogx_le hBbv_pos.le
        exact h1.trans (hQR.trans ((div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hx_lo) (by positivity)).trans
          ((div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (Real.rpow_pos_of_pos hlogx_pos _) hpow_le).trans
            (div_le_self (Real.sqrt_nonneg x) hpow_ge1))))
      have hE_bd : E_sup x q ≤ 3 * x / (q.totient : ℝ) := by
        dsimp only [E_sup]; split_ifs with hne
        · rw [Finset.sup'_le_iff]; intro a _
          have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq1)
          have hphi_le_q : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
          have hpiAP_le : (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤ 2 * x / (q.totient : ℝ) := by
            have hsub_ap : (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
                (Finset.Ico 0 (⌊x⌋₊ + 1)).filter (fun p => p ≡ a [MOD q]) := by
              intro p hp; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hp ⊢
              exact ⟨⟨Nat.zero_le p, hp.1⟩, hp.2.2⟩
            have h1 : (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤
                (((Finset.Ico 0 (⌊x⌋₊ + 1)).filter (fun p => p ≡ a [MOD q])).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub_ap
            have h2 := (abs_le.mp (card_Ico_modEq_sub_div_le hq1 0 (⌊x⌋₊ + 1) a (Nat.zero_le _))).2
            simp only [Nat.sub_zero] at h2
            have hfl : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ x + 1 := by push_cast; linarith [Nat.floor_le hx_pos.le]
            have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq1
            have hdiv1 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) / (q : ℝ) + 1 ≤ 2 * x / (q : ℝ) := by
              rw [div_add_one hqpos.ne', div_le_div_iff_of_pos_right hqpos]
              have hq_le_x : (q : ℝ) + 1 ≤ x := by nlinarith [Real.sq_sqrt hx_pos.le, Real.sqrt_nonneg x]
              linarith
            have hdiv2 : 2 * x / (q : ℝ) ≤ 2 * x / (q.totient : ℝ) :=
              div_le_div_of_nonneg_left (by positivity) hphi_pos hphi_le_q
            linarith
          have hpi_le : (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ) ≤ x / (q.totient : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ hphi_pos.le
            have hsub_p : (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime ⊆ Finset.Icc 1 ⌊x⌋₊ := by
              intro p hp; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
              exact ⟨hp.2.one_le, Nat.lt_succ_iff.mp hp.1⟩
            have hc : ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card ≤ ⌊x⌋₊ := by
              calc _ ≤ (Finset.Icc 1 ⌊x⌋₊).card := Finset.card_le_card hsub_p
                _ = ⌊x⌋₊ := by simp
            exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hx_pos.le)
          have hxphi_nn : 0 ≤ x / (q.totient : ℝ) := by positivity
          have hrew3 : 3 * x / (q.totient : ℝ) = 2 * x / (q.totient : ℝ) + x / (q.totient : ℝ) := by ring
          rw [abs_le]; constructor <;> linarith [show (0 : ℝ) ≤ (Stage2DirichletAP.primeCountAP q a x : ℝ) by positivity,
            show (0 : ℝ) ≤ (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ) by positivity]
        · positivity
      have hqphi := nat_div_totient_le hq1 (by exact_mod_cast (show 16 ≤ 3 * X by omega) : (16 : ℝ) ≤ ((3 * X : ℕ) : ℝ))
        (by exact_mod_cast (hqQR.trans hQR_le_3X))
      calc (q : ℝ) * E_sup x q ≤ (q : ℝ) * (3 * x / (q.totient : ℝ)) :=
            mul_le_mul_of_nonneg_left hE_bd (Nat.cast_nonneg _)
        _ = 3 * x * ((q : ℝ) / (q.totient : ℝ)) := by ring
        _ ≤ 3 * x * (Real.exp 2 * Real.log ((3 * X : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hqphi (by positivity)
    have hEsup_nn : ∀ q : ℕ, 0 ≤ E_sup x q := fun q => by
      dsimp only [E_sup]; split_ifs with hne
      · obtain ⟨a, ha⟩ := hne
        exact (abs_nonneg _).trans (Finset.le_sup' (f := fun a => |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
          (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|) ha)
      · exact le_rfl
    -- Apply Cauchy–Schwarz!
    set Sq := (Finset.Icc 1 Q_R).filter Squarefree
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Sq
      (fun q => (M_k : ℝ) ^ (q.primeFactors.card) / Real.sqrt (q : ℝ))
      (fun q => Real.sqrt (q : ℝ) * E_sup x q)
    have hlhs_eq : ∑ q ∈ Sq, ((M_k : ℝ) ^ (q.primeFactors.card) / Real.sqrt (q : ℝ)) *
          (Real.sqrt (q : ℝ) * E_sup x q) =
        ∑ q ∈ Sq, (M_k : ℝ) ^ (q.primeFactors.card) * E_sup x q := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqpos : (0 : ℝ) < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1)
      field_simp [hqpos.ne']
    have hF1 : ∑ q ∈ Sq, ((M_k : ℝ) ^ (q.primeFactors.card) / Real.sqrt (q : ℝ)) ^ 2 ≤
        (3 * Real.log (X : ℝ)) ^ (M_k ^ 2) := by
      have heq1 : ∑ q ∈ Sq, ((M_k : ℝ) ^ (q.primeFactors.card) / Real.sqrt (q : ℝ)) ^ 2 =
          ∑ q ∈ Sq, ((M_k ^ 2 : ℕ) : ℝ) ^ (q.primeFactors.card) / (q : ℝ) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, mul_comm _ 2, pow_mul, Nat.cast_pow]
      rw [heq1]
      have hsub3X : Sq ⊆ (Finset.Icc 1 (3 * X)).filter Squarefree :=
        Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hQR_le_3X)
      calc ∑ q ∈ Sq, ((M_k ^ 2 : ℕ) : ℝ) ^ (q.primeFactors.card) / (q : ℝ)
          ≤ ∑ q ∈ (Finset.Icc 1 (3 * X)).filter Squarefree, ((M_k ^ 2 : ℕ) : ℝ) ^ (q.primeFactors.card) / (q : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub3X fun _ _ _ => by positivity
        _ ≤ (Real.log ((3 * X : ℕ) : ℝ) + 1) ^ (M_k ^ 2) := sum_pow_omega_div_le (M_k ^ 2) (3 * X) (by omega)
        _ ≤ (3 * Real.log (X : ℝ)) ^ (M_k ^ 2) :=
            pow_le_pow_left₀ (by have := Real.log_nonneg (show (1 : ℝ) ≤ (3 * X : ℕ) by exact_mod_cast (by omega)); linarith)
              (by linarith) _
    have hF2 : ∑ q ∈ Sq, (Real.sqrt (q : ℝ) * E_sup x q) ^ 2 ≤
        (54 * Real.exp 2 * C_bv * (2 : ℝ) ^ A_bv) * (X : ℝ) ^ 2 *
          Real.log (X : ℝ) / (Real.log (X : ℝ)) ^ A_bv := by
      have hbv_x : ∑ q ∈ Finset.Icc 1 Q_bv, E_sup x q ≤ C_bv * x / (Real.log x) ^ A_bv := hBV x hx4
      have hbv_Sq : ∑ q ∈ Sq, E_sup x q ≤ C_bv * x / (Real.log x) ^ A_bv :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsubQ fun q _ _ => hEsup_nn q).trans hbv_x
      have hlogx_pow : (Real.log (X : ℝ) / 2) ^ A_bv ≤ (Real.log x) ^ A_bv :=
        Real.rpow_le_rpow (by positivity) hlogx_ge (by dsimp only [A_bv]; positivity)
      have hdiv_pow : (Real.log (X : ℝ)) ^ A_bv / (2 : ℝ) ^ A_bv ≤ (Real.log x) ^ A_bv := by
        rwa [Real.div_rpow hlogX_pos.le (by norm_num)] at hlogx_pow
      calc ∑ q ∈ Sq, (Real.sqrt (q : ℝ) * E_sup x q) ^ 2
          = ∑ q ∈ Sq, ((q : ℝ) * E_sup x q) * E_sup x q := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
        _ ≤ ∑ q ∈ Sq, (3 * x * (Real.exp 2 * Real.log ((3 * X : ℕ) : ℝ))) * E_sup x q :=
            Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_right (htriv q hq) (hEsup_nn q)
        _ = 3 * x * (Real.exp 2 * Real.log ((3 * X : ℕ) : ℝ)) * ∑ q ∈ Sq, E_sup x q := by rw [← Finset.mul_sum]
        _ ≤ 3 * x * (Real.exp 2 * (2 * Real.log (X : ℝ))) * (C_bv * x / (Real.log x) ^ A_bv) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog3X_le (Real.exp_pos 2).le) (by positivity))
              hbv_Sq (Finset.sum_nonneg fun q _ => hEsup_nn q) (by positivity)
        _ ≤ 3 * ((3 * X : ℕ) : ℝ) * (Real.exp 2 * (2 * Real.log (X : ℝ))) *
              (C_bv * ((3 * X : ℕ) : ℝ) / ((Real.log (X : ℝ)) ^ A_bv / (2 : ℝ) ^ A_bv)) := by
            gcongr
        _ = (54 * Real.exp 2 * C_bv * (2 : ℝ) ^ A_bv) * (X : ℝ) ^ 2 *
              Real.log (X : ℝ) / (Real.log (X : ℝ)) ^ A_bv := by
            push_cast
            field_simp [(Real.rpow_pos_of_pos hlogX_pos A_bv).ne', (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) A_bv).ne']
            ring
    rw [hlhs_eq] at hCS
    have hsq_bd : (∑ q ∈ Sq, (M_k : ℝ) ^ (q.primeFactors.card) * E_sup x q) ^ 2 ≤
        (C_cs * (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * (k + 1) + 4)) ^ 2 := by
      have hCcs_sq : C_cs ^ 2 = (3 : ℝ) ^ (M_k ^ 2) * (54 * Real.exp 2 * C_bv * (2 : ℝ) ^ A_bv) :=
        Real.sq_sqrt (by positivity)
      have hexp_le : (Real.log (X : ℝ)) ^ (M_k ^ 2) * Real.log (X : ℝ) / (Real.log (X : ℝ)) ^ A_bv ≤
          1 / ((Real.log (X : ℝ)) ^ (4 * (k + 1) + 4)) ^ 2 := by
        rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogX_pos _) (sq_pos_of_pos (pow_pos hlogX_pos _)), one_mul,
          ← pow_mul, ← pow_succ, ← pow_add, ← Real.rpow_natCast (Real.log (X : ℝ))]
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
        dsimp only [A_bv]; push_cast; linarith
      calc (∑ q ∈ Sq, (M_k : ℝ) ^ (q.primeFactors.card) * E_sup x q) ^ 2
          ≤ (∑ q ∈ Sq, ((M_k : ℝ) ^ (q.primeFactors.card) / Real.sqrt (q : ℝ)) ^ 2) *
              (∑ q ∈ Sq, (Real.sqrt (q : ℝ) * E_sup x q) ^ 2) := hCS
        _ ≤ (3 * Real.log (X : ℝ)) ^ (M_k ^ 2) *
              ((54 * Real.exp 2 * C_bv * (2 : ℝ) ^ A_bv) * (X : ℝ) ^ 2 *
                Real.log (X : ℝ) / (Real.log (X : ℝ)) ^ A_bv) :=
            mul_le_mul hF1 hF2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = C_cs ^ 2 * (X : ℝ) ^ 2 *
              ((Real.log (X : ℝ)) ^ (M_k ^ 2) * Real.log (X : ℝ) / (Real.log (X : ℝ)) ^ A_bv) := by
            rw [hCcs_sq, mul_pow]; ring
        _ ≤ C_cs ^ 2 * (X : ℝ) ^ 2 * (1 / ((Real.log (X : ℝ)) ^ (4 * (k + 1) + 4)) ^ 2) :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
        _ = (C_cs * (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * (k + 1) + 4)) ^ 2 := by ring
    have hnn_lhs : 0 ≤ ∑ q ∈ Sq, (M_k : ℝ) ^ (q.primeFactors.card) * E_sup x q :=
      Finset.sum_nonneg fun q _ => mul_nonneg (by positivity) (hEsup_nn q)
    have hnn_rhs : 0 ≤ C_cs * (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * (k + 1) + 4) := by positivity
    nlinarith [sq_nonneg ((∑ q ∈ Sq, (M_k : ℝ) ^ (q.primeFactors.card) * E_sup x q) -
      C_cs * (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * (k + 1) + 4))]
  -- Step 5: Sum `hde_err` over `(d, e) ∈ Vm ×ˢ Vm` and group error by `q = W₀ * ∏_{i ∈ Em} lcm(d i, e i)`
  have hW_sf : Squarefree W₀ := by
    dsimp only [W₀, W, primorial]
    refine squarefree_prod_of_pairwise ?_ ?_
    · intro p hp; exact (Finset.mem_filter.mp hp).2.squarefree
    · intro p hp q hq hpq
      exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq
  set Sq := (Finset.Icc 1 ⌊(W₀ : ℝ) * R ^ 2⌋₊).filter Squarefree
  have hgroup_err : ∑ d ∈ Vm, ∑ e ∈ Vm,
        (if PairwiseCoprimeCross d e then
          |lamVar W₀ R T d| * |lamVar W₀ R T e| *
            (E_sup y₂ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)) + E_sup y₁ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)))
        else 0) ≤
      C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by
    have hEsup_nn : ∀ (x : ℝ) (q : ℕ), 0 ≤ E_sup x q := fun x q => by
      dsimp only [E_sup]; split_ifs with hne
      · obtain ⟨a, ha⟩ := hne
        exact (abs_nonneg _).trans (Finset.le_sup' (f := fun a => |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
          (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)|) ha)
      · exact le_rfl
    set Pset := (Vm ×ˢ Vm).filter (fun de => PairwiseCoprimeCross de.1 de.2)
    let qOf : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ) → ℕ := fun de => W₀ * ∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i)
    have hmaps_Sq : ∀ de ∈ Pset, qOf de ∈ Sq := by
      intro de hde
      have hdeP := Finset.mem_product.mp (Finset.mem_filter.mp hde).1
      have hpc := (Finset.mem_filter.mp hde).2
      obtain ⟨hd1, hd_prod, hd_sf, hd_cop⟩ := (mem_validTupleSet hR_pos.le).mp (Finset.mem_filter.mp hdeP.1).1
      obtain ⟨he1, he_prod, he_sf, he_cop⟩ := (mem_validTupleSet hR_pos.le).mp (Finset.mem_filter.mp hdeP.2).1
      have hr_pos : 1 ≤ ∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i) :=
        Finset.prod_pos fun i _ => Nat.lcm_pos (hd1 i) (he1 i)
      have hr_le : ((∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i) : ℕ) : ℝ) ≤ R ^ 2 := by
        have h1 : ∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i) ≤ (∏ i, de.1 i) * (∏ i, de.2 i) := by
          calc ∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i)
              ≤ ∏ i ∈ Em, (de.1 i * de.2 i) := Finset.prod_le_prod' fun i _ =>
                Nat.le_of_dvd (Nat.mul_pos (hd1 i) (he1 i)) (Nat.lcm_dvd_mul _ _)
            _ = (∏ i ∈ Em, de.1 i) * (∏ i ∈ Em, de.2 i) := Finset.prod_mul_distrib
            _ ≤ (∏ i, de.1 i) * (∏ i, de.2 i) := by
                have hdm := (Finset.mem_filter.mp hdeP.1).2
                have hem := (Finset.mem_filter.mp hdeP.2).2
                have h1' := Finset.mul_prod_erase Finset.univ de.1 (Finset.mem_univ m)
                have h2' := Finset.mul_prod_erase Finset.univ de.2 (Finset.mem_univ m)
                rw [hdm, one_mul] at h1'; rw [hem, one_mul] at h2'
                rw [h1', h2']
        calc ((∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i) : ℕ) : ℝ)
            ≤ ((∏ i, de.1 i : ℕ) : ℝ) * ((∏ i, de.2 i : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ R * R := mul_le_mul hd_prod he_prod (Nat.cast_nonneg _) hR_pos.le
          _ = R ^ 2 := (sq R).symm
      have hr_sf : Squarefree (∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i)) := by
        refine squarefree_prod_of_pairwise ?_ ?_
        · intro i _
          have hdi := (squarefree_prod_coord hd_sf).1 i (Finset.mem_univ i)
          have hei := (squarefree_prod_coord he_sf).1 i (Finset.mem_univ i)
          have hmul : Nat.lcm (de.1 i) (de.2 i) = de.1 i * (de.2 i / Nat.gcd (de.1 i) (de.2 i)) := by
            have h1 := Nat.gcd_mul_lcm (de.1 i) (de.2 i)
            have h2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right (de.1 i) (de.2 i))
            have hgpos : 0 < Nat.gcd (de.1 i) (de.2 i) := Nat.gcd_pos_of_pos_left _ (hd1 i)
            exact Nat.eq_of_mul_eq_mul_left hgpos (by
              calc Nat.gcd (de.1 i) (de.2 i) * Nat.lcm (de.1 i) (de.2 i) = de.1 i * de.2 i := h1
                _ = de.1 i * (Nat.gcd (de.1 i) (de.2 i) * (de.2 i / Nat.gcd (de.1 i) (de.2 i))) := by rw [h2]
                _ = Nat.gcd (de.1 i) (de.2 i) * (de.1 i * (de.2 i / Nat.gcd (de.1 i) (de.2 i))) := by ring)
          rw [hmul]
          have hcop_q : Nat.Coprime (de.1 i) (de.2 i / Nat.gcd (de.1 i) (de.2 i)) := by
            rw [Nat.coprime_iff_gcd_eq_one]
            by_contra hne1
            obtain ⟨p, hpp, hpg⟩ := Nat.exists_prime_and_dvd hne1
            have hp1 : p ∣ de.1 i := dvd_trans hpg (Nat.gcd_dvd_left _ _)
            have hpq : p ∣ de.2 i / Nat.gcd (de.1 i) (de.2 i) := dvd_trans hpg (Nat.gcd_dvd_right _ _)
            have hp2 : p ∣ de.2 i := dvd_trans hpq (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
            have hpgcd : p ∣ Nat.gcd (de.1 i) (de.2 i) := Nat.dvd_gcd hp1 hp2
            have hp2sq : p * p ∣ de.2 i := by
              rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_right (de.1 i) (de.2 i))]
              exact mul_dvd_mul hpgcd hpq
            exact hpp.not_isUnit (hei p hp2sq)
          exact (Nat.squarefree_mul hcop_q).mpr ⟨hdi, hei.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))⟩
        · intro i _ j _ hij
          exact coprime_lcm_left
            (coprime_lcm_right ((squarefree_prod_coord hd_sf).2 i (Finset.mem_univ i) j (Finset.mem_univ j) hij) (hpc i j hij))
            (coprime_lcm_right (hpc j i hij.symm).symm ((squarefree_prod_coord he_sf).2 i (Finset.mem_univ i) j (Finset.mem_univ j) hij))
      have hr_copW : Nat.Coprime W₀ (∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i)) :=
        Nat.Coprime.prod_right fun i _ =>
          (coprime_lcm_left (hd_cop.coprime_dvd_left (Finset.dvd_prod_of_mem de.1 (Finset.mem_univ i)))
            (he_cop.coprime_dvd_left (Finset.dvd_prod_of_mem de.2 (Finset.mem_univ i)))).symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hW_pos hr_pos,
        Nat.le_floor (by dsimp only [qOf]; rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_left hr_le (Nat.cast_nonneg _))⟩,
        (Nat.squarefree_mul hr_copW).mpr ⟨hW_sf, hr_sf⟩⟩
    have hfiber_le : ∀ q ∈ Sq,
        ((Pset.filter (fun de => qOf de = q)).card : ℝ) ≤ (M_k : ℝ) ^ (q.primeFactors.card) := by
      intro q hq
      have hqsf : Squarefree q := (Finset.mem_filter.mp hq).2
      by_cases hWq : W₀ ∣ q
      · set r := q / W₀
        have hrsf : Squarefree r := hqsf.squarefree_of_dvd (Nat.div_dvd_of_dvd hWq)
        have hfeq : Pset.filter (fun de => qOf de = q) =
            (Vm ×ˢ Vm).filter (fun de => PairwiseCoprimeCross de.1 de.2 ∧
              ∏ i ∈ Em, Nat.lcm (de.1 i) (de.2 i) = r) := by
          ext de; simp only [Pset, Finset.mem_filter, qOf, and_assoc]
          refine and_congr_right fun _ => and_congr_right fun _ => ?_
          constructor
          · intro h1; dsimp only [r]; rw [← h1, Nat.mul_div_cancel_left _ hW_pos]
          · intro h1; dsimp only [r] at h1; rw [h1, Nat.mul_div_cancel' hWq]
        rw [hfeq]
        have hle_r := mult_lcm_pair_le (W₀ := W₀) hR_pos.le m r hrsf
        have hcard_pf : r.primeFactors.card ≤ q.primeFactors.card :=
          Finset.card_le_card (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hWq) hqsf.ne_zero)
        exact hle_r.trans (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ M_k by omega)) hcard_pf)
      · have hempty : Pset.filter (fun de => qOf de = q) = ∅ := by
          ext de; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro _ hEq; exact hWq (hEq ▸ dvd_mul_right W₀ _)
        rw [hempty, Finset.card_empty, Nat.cast_zero]; positivity
    calc ∑ d ∈ Vm, ∑ e ∈ Vm,
            (if PairwiseCoprimeCross d e then
              |lamVar W₀ R T d| * |lamVar W₀ R T e| * (E_sup y₂ (qOf (d, e)) + E_sup y₁ (qOf (d, e)))
            else 0)
        = ∑ de ∈ Pset, |lamVar W₀ R T de.1| * |lamVar W₀ R T de.2| * (E_sup y₂ (qOf de) + E_sup y₁ (qOf de)) := by
          rw [← Finset.sum_product', Finset.sum_filter]
      _ ≤ ∑ de ∈ Pset, (C_lam * (Real.log (X : ℝ)) ^ (2 * (k + 1))) ^ 2 * (E_sup y₂ (qOf de) + E_sup y₁ (qOf de)) := by
          refine Finset.sum_le_sum fun de _ => mul_le_mul_of_nonneg_right ?_ (add_nonneg (hEsup_nn _ _) (hEsup_nn _ _))
          rw [sq]
          exact mul_le_mul (hLmax de.1) (hLmax de.2) (abs_nonneg _) (by positivity)
      _ = (C_lam * (Real.log (X : ℝ)) ^ (2 * (k + 1))) ^ 2 * ∑ de ∈ Pset, (E_sup y₂ (qOf de) + E_sup y₁ (qOf de)) := by
          rw [← Finset.mul_sum]
      _ = (C_lam * (Real.log (X : ℝ)) ^ (2 * (k + 1))) ^ 2 *
            ∑ q ∈ Sq, ((Pset.filter (fun de => qOf de = q)).card : ℝ) * (E_sup y₂ q + E_sup y₁ q) := by
          congr 1
          rw [← Finset.sum_fiberwise_of_maps_to hmaps_Sq]
          refine Finset.sum_congr rfl fun q _ => ?_
          have h1 : ∀ de ∈ Pset.filter (fun de => qOf de = q),
              E_sup y₂ (qOf de) + E_sup y₁ (qOf de) = E_sup y₂ q + E_sup y₁ q := fun de hde => by
            rw [(Finset.mem_filter.mp hde).2]
          rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C_lam * (Real.log (X : ℝ)) ^ (2 * (k + 1))) ^ 2 *
            ∑ q ∈ Sq, (M_k : ℝ) ^ (q.primeFactors.card) * (E_sup y₂ q + E_sup y₁ q) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q hq => ?_) (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right (hfiber_le q hq) (add_nonneg (hEsup_nn _ _) (hEsup_nn _ _))
      _ = (C_lam * (Real.log (X : ℝ)) ^ (2 * (k + 1))) ^ 2 *
            ((∑ q ∈ Sq, (M_k : ℝ) ^ (q.primeFactors.card) * E_sup y₂ q) +
             (∑ q ∈ Sq, (M_k : ℝ) ^ (q.primeFactors.card) * E_sup y₁ q)) := by
          congr 1; simp_rw [mul_add]; rw [Finset.sum_add_distrib]
      _ ≤ (C_lam * (Real.log (X : ℝ)) ^ (2 * (k + 1))) ^ 2 *
            (C_cs * (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * (k + 1) + 4) +
             C_cs * (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * (k + 1) + 4)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add
            (hCS_bv y₂ (by dsimp only [y₂]; exact_mod_cast (show A + h m - 1 ≤ B + h m - 1 by omega))
              (by dsimp only [y₂]; exact_mod_cast (show B + h m - 1 ≤ 3 * X by omega)))
            (hCS_bv y₁ le_rfl (by dsimp only [y₁]; exact_mod_cast (show A + h m - 1 ≤ 3 * X by omega))))
            (sq_nonneg _)
      _ = C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by
          dsimp only [C_err]
          rw [mul_pow, ← pow_mul, show 2 * (k + 1) * 2 = 4 * (k + 1) by ring, pow_add]
          field_simp [(pow_pos hlogX_pos (4 * (k + 1))).ne', (pow_pos hlogX_pos 4).ne']
          ring
  -- Final combination of main term `Δπ / φ(W₀) * Q1Sum` and BV error `hgroup_err`!
  have hsum_all := Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => hde_err d hd e he
  have hsplit_main : ∑ d ∈ Vm, ∑ e ∈ Vm,
        (if PairwiseCoprimeCross d e then
          lamVar W₀ R T d * lamVar W₀ R T e *
            (Δπ / (((W₀).totient : ℝ) * ∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ))) -
          |lamVar W₀ R T d| * |lamVar W₀ R T e| *
            (E_sup y₂ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)) + E_sup y₁ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)))
        else 0) =
      (Δπ / (W₀.totient : ℝ)) * Q1Sum W₀ R T m -
      ∑ d ∈ Vm, ∑ e ∈ Vm,
        (if PairwiseCoprimeCross d e then
          |lamVar W₀ R T d| * |lamVar W₀ R T e| *
            (E_sup y₂ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)) + E_sup y₁ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)))
        else 0) := by
    have hpt : ∀ d e,
        (if PairwiseCoprimeCross d e then
          lamVar W₀ R T d * lamVar W₀ R T e *
            (Δπ / (((W₀).totient : ℝ) * ∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ))) -
          |lamVar W₀ R T d| * |lamVar W₀ R T e| *
            (E_sup y₂ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)) + E_sup y₁ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)))
        else 0) =
        (Δπ / (W₀.totient : ℝ)) *
          (if PairwiseCoprimeCross d e then
            lamVar W₀ R T d * lamVar W₀ R T e / (∏ i ∈ Em, ((Nat.lcm (d i) (e i)).totient : ℝ))
          else 0) -
        (if PairwiseCoprimeCross d e then
          |lamVar W₀ R T d| * |lamVar W₀ R T e| *
            (E_sup y₂ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)) + E_sup y₁ (W₀ * ∏ i ∈ Em, Nat.lcm (d i) (e i)))
        else 0) := fun d e => by split_ifs <;> ring
    simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]; rfl
  rw [hsplit_main] at hsum_all
  linarith

/-! ## Section 5: Discharging `MAnalyticCore` and `AnalyticCore` Unconditionally -/

/-- Prime count difference lower bound on `[A + s, B + s)` via unconditional Siegel–Walfisz (`q = 1`). -/
private lemma pi_diff_lower :
    ∃ c_sw C_sw : ℝ, 0 < c_sw ∧ 0 < C_sw ∧
      ∀ (X A B s : ℕ), 16 ≤ X → X ≤ A → A ≤ B → B ≤ 2 * X → s ≤ X →
        (((B - A : ℕ) : ℝ) / Real.log ((3 * X : ℕ) : ℝ)) -
          6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) ≤
        (((Finset.range (B + s)).filter Nat.Prime).card : ℝ) -
          (((Finset.range (A + s)).filter Nat.Prime).card : ℝ) := by
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := Stage10SiegelWalfiszFull.siegel_walfisz_pi_real
  obtain ⟨C_sw, hC_sw, hsw1⟩ := hsw_all 1 zero_lt_one
  refine ⟨c_sw, C_sw, hc_sw, hC_sw, fun X A B s hX16 hXA hAB hB2X hsX => ?_⟩
  set y₁ : ℝ := ((A + s - 1 : ℕ) : ℝ)
  set y₂ : ℝ := ((B + s - 1 : ℕ) : ℝ)
  have hy1_ge15 : (15 : ℝ) ≤ y₁ := by dsimp only [y₁]; exact_mod_cast (show 15 ≤ A + s - 1 by omega)
  have hy1_le_y2 : y₁ ≤ y₂ := by dsimp only [y₁, y₂]; exact_mod_cast (show A + s - 1 ≤ B + s - 1 by omega)
  have hy2_le_3X : y₂ ≤ ((3 * X : ℕ) : ℝ) := by dsimp only [y₂]; exact_mod_cast (show B + s - 1 ≤ 3 * X by omega)
  have hy1_ge4 : 4 ≤ y₁ := by linarith
  have hy2_ge4 : 4 ≤ y₂ := by linarith
  have hlog_ge1 : ∀ x : ℝ, 4 ≤ x → (1 : ℝ) ≤ (Real.log x) ^ (1 : ℝ) := fun x hx => by
    rw [Real.rpow_one]
    have h1 : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hsw_y1 := hsw1 y₁ hy1_ge4 1 (by simpa using hlog_ge1 y₁ hy1_ge4) 0 (Nat.coprime_one_right 0)
  have hsw_y2 := hsw1 y₂ hy2_ge4 1 (by simpa using hlog_ge1 y₂ hy2_ge4) 0 (Nat.coprime_one_right 0)
  simp only [Nat.totient_one, Nat.cast_one, div_one] at hsw_y1 hsw_y2
  have hpiAP_eq : ∀ n : ℕ, 1 ≤ n →
      (Stage2DirichletAP.primeCountAP 1 0 ((n - 1 : ℕ) : ℝ) : ℝ) =
        (((Finset.range n).filter Nat.Prime).card : ℝ) := fun n hn => by
    unfold Stage2DirichletAP.primeCountAP
    rw [Nat.floor_natCast, Nat.sub_add_cancel hn]
    congr 2; ext p; simp [Nat.modEq_one]
  rw [hpiAP_eq (A + s) (by omega)] at hsw_y1
  rw [hpiAP_eq (B + s) (by omega)] at hsw_y2
  -- Evaluate `∫_2^{y₂} 1/log t - ∫_2^{y₁} 1/log t = ∫_{y₁}^{y₂} 1/log t ≥ (y₂ - y₁) / log (3 * X)`
  have hcont_invlog : ∀ a b : ℝ, 2 ≤ a → a ≤ b → ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc a b) := by
    intro a b ha hab
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.div (Real.continuousOn_log.mono fun t ht => ne_of_gt (by linarith [ht.1])) fun t ht => ?_
    exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  have hint_sub : (∫ t in (2 : ℝ)..y₂, 1 / Real.log t) - (∫ t in (2 : ℝ)..y₁, 1 / Real.log t) =
      ∫ t in y₁..y₂, 1 / Real.log t := by
    have hadd : (∫ t in (2 : ℝ)..y₁, 1 / Real.log t) + (∫ t in y₁..y₂, 1 / Real.log t) =
        ∫ t in (2 : ℝ)..y₂, 1 / Real.log t :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hcont_invlog 2 y₁ le_rfl (by linarith)).intervalIntegrable)
        ((hcont_invlog y₁ y₂ (by linarith) hy1_le_y2).intervalIntegrable)
    linarith
  have hint_lo : (((B - A : ℕ) : ℝ) / Real.log ((3 * X : ℕ) : ℝ)) ≤ ∫ t in y₁..y₂, 1 / Real.log t := by
    have hlog3X_pos : 0 < Real.log ((3 * X : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < 3 * X by omega))
    have hconst : ∫ _t in y₁..y₂, (1 / Real.log ((3 * X : ℕ) : ℝ)) =
        (y₂ - y₁) / Real.log ((3 * X : ℕ) : ℝ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hdiff_eq : y₂ - y₁ = ((B - A : ℕ) : ℝ) := by
      dsimp only [y₁, y₂]
      have h1 : (B + s - 1 : ℕ) = (A + s - 1 : ℕ) + (B - A) := by omega
      have hR : ((B + s - 1 : ℕ) : ℝ) = ((A + s - 1 : ℕ) : ℝ) + ((B - A : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    rw [← hdiff_eq, ← hconst]
    refine intervalIntegral.integral_mono_on hy1_le_y2 intervalIntegrable_const
      ((hcont_invlog y₁ y₂ (by linarith) hy1_le_y2).intervalIntegrable) fun t ht => ?_
    have ht_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact one_div_le_one_div_of_le ht_pos (Real.log_le_log (by linarith [ht.1]) (ht.2.trans hy2_le_3X))
  -- Compare `C_sw * (y₂ * exp(-c_sw √(log y₂)) + y₁ * exp(-c_sw √(log y₁))) ≤ 6 * C_sw * X * exp(-c_sw √(log X / 2))`
  have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  have hy1_ge_sqrt : Real.sqrt (X : ℝ) ≤ y₁ := by
    have hsq : Real.sqrt (X : ℝ) ≤ (X : ℝ) / 4 := by
      have : (Real.sqrt (X : ℝ)) ^ 2 ≤ ((X : ℝ) / 4) ^ 2 := by
        rw [Real.sq_sqrt hX_pos.le]; nlinarith [show (16 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX16]
      nlinarith [Real.sqrt_nonneg (X : ℝ)]
    have hlo' : (X : ℝ) - 1 ≤ y₁ := by
      have h1 : ((X - 1 : ℕ) : ℝ) ≤ y₁ := by dsimp only [y₁]; exact_mod_cast (show X - 1 ≤ A + s - 1 by omega)
      rwa [Nat.cast_sub (by omega : 1 ≤ X), Nat.cast_one] at h1
    linarith [show (16 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX16]
  have hlogy1_ge : Real.log (X : ℝ) / 2 ≤ Real.log y₁ := by
    have h1 := Real.log_le_log (Real.sqrt_pos.mpr hX_pos) hy1_ge_sqrt
    rwa [Real.log_sqrt hX_pos.le] at h1
  have hlogy2_ge : Real.log (X : ℝ) / 2 ≤ Real.log y₂ :=
    hlogy1_ge.trans (Real.log_le_log (by linarith) hy1_le_y2)
  have hexp1 : Real.exp (-c_sw * Real.sqrt (Real.log y₁)) ≤ Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt hlogy1_ge])
  have hexp2 : Real.exp (-c_sw * Real.sqrt (Real.log y₂)) ≤ Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt hlogy2_ge])
  have herr_sum : C_sw * y₂ * Real.exp (-c_sw * Real.sqrt (Real.log y₂)) +
      C_sw * y₁ * Real.exp (-c_sw * Real.sqrt (Real.log y₁)) ≤
      6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) := by
    have hy2_3X : y₂ ≤ 3 * (X : ℝ) := by simpa [Nat.cast_mul] using hy2_le_3X
    have hy1_3X : y₁ ≤ 3 * (X : ℝ) := hy1_le_y2.trans hy2_3X
    have h1 : C_sw * y₂ * Real.exp (-c_sw * Real.sqrt (Real.log y₂)) ≤
        3 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) := by
      calc C_sw * y₂ * Real.exp (-c_sw * Real.sqrt (Real.log y₂))
          ≤ C_sw * (3 * (X : ℝ)) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hy2_3X hC_sw.le) hexp2 (Real.exp_pos _).le (by positivity)
        _ = 3 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) := by ring
    have h2 : C_sw * y₁ * Real.exp (-c_sw * Real.sqrt (Real.log y₁)) ≤
        3 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) := by
      calc C_sw * y₁ * Real.exp (-c_sw * Real.sqrt (Real.log y₁))
          ≤ C_sw * (3 * (X : ℝ)) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hy1_3X hC_sw.le) hexp1 (Real.exp_pos _).le (by positivity)
        _ = 3 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) := by ring
    linarith
  linarith [(abs_le.mp hsw_y1).2, (abs_le.mp hsw_y2).1, hint_sub, hint_lo, herr_sum]

/-- **MASTER MULTIDIMENSIONAL SELBERG SIEVE THEOREM (UNCONDITIONAL, `ϑ = 1/2`)**:
for any admissible tuple `H` of cardinality `k + 1`, any `m : ℕ`, and any symmetric Lipschitz
simplex test function `T : SimplexTestFn (k + 1)` with `0 < I_{k+1}(T.F)` and
`4 * m * I_{k+1}(T.F) < (k + 1) * J_k^{(0)}(T.F)`, the `m + 1`-tuple analytic core
`MAnalyticCore H (m + 1)` holds UNCONDITIONALLY! -/
theorem exists_maynard_tao_sieve_core {H : Finset ℕ} (hadm : Admissible H)
    {k : ℕ} (hcard : H.card = k + 1) (m : ℕ)
    (T : SimplexTestFn (k + 1))
    (hI_pos : 0 < maynardI (k + 1) T.F)
    (hratio : 4 * (m : ℝ) * maynardI (k + 1) T.F < ((k + 1 : ℕ) : ℝ) * maynardJ0 k T.F) :
    Nonempty (MAnalyticCore H (m + 1)) := by
  classical
  -- Step 1: Enumerate `H` via `h : Fin (k + 1) ↪ ℕ`
  let eH : Fin (k + 1) ≃ ↥H := (H.equivFinOfCardEq hcard).symm
  let h : Fin (k + 1) ↪ ℕ := eH.toEmbedding.trans (Function.Embedding.subtype _)
  have hh_mem : ∀ i : Fin (k + 1), h i ∈ H := fun i => (eH i).2
  have hH_eq : Finset.univ.map h = H := by
    ext x; simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact hh_mem i
    · intro hx; exact ⟨eH.symm ⟨x, hx⟩, by simp [h]⟩
  have hmaxH : ∃ M_H : ℕ, ∀ i : Fin (k + 1), h i ≤ M_H :=
    ⟨∑ i : Fin (k + 1), h i, fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩
  obtain ⟨M_H, hM_H⟩ := hmaxH
  -- Step 2: Choose exponent `δ_exp ∈ (0, 1/8)` and margin `η > 0`
  have hJ_pos : 0 < maynardJ0 k T.F := by
    have h1 : 0 ≤ 4 * (m : ℝ) * maynardI (k + 1) T.F := by positivity
    have h2 : 0 < ((k + 1 : ℕ) : ℝ) * maynardJ0 k T.F := lt_of_le_of_lt h1 hratio
    exact pos_of_mul_pos_right h2 (by positivity)
  set I_val := maynardI (k + 1) T.F
  set J_val := maynardJ0 k T.F
  set gap : ℝ := ((k + 1 : ℕ) : ℝ) * J_val / 4 - (m : ℝ) * I_val
  have hgap_pos : 0 < gap := by dsimp only [gap]; linarith
  set δ_exp : ℝ := min (1 / 16) (gap / (2 * ((k + 1 : ℕ) : ℝ) * J_val))
  have hδexp_pos : 0 < δ_exp := lt_min (by norm_num) (by positivity)
  have hδexp_le16 : δ_exp ≤ 1 / 16 := min_le_left _ _
  have hα_pos : (0 : ℝ) < 1 / 4 - δ_exp := by linarith
  set α : ℝ := 1 / 4 - δ_exp
  set η : ℝ := α * ((k + 1 : ℕ) : ℝ) * J_val - (m : ℝ) * I_val
  have hη_pos : 0 < η := by
    have hδ_le : δ_exp ≤ gap / (2 * ((k + 1 : ℕ) : ℝ) * J_val) := min_le_right _ _
    have hmul : δ_exp * (((k + 1 : ℕ) : ℝ) * J_val) ≤ gap / 2 := by
      have hpos : 0 < 2 * ((k + 1 : ℕ) : ℝ) * J_val := by positivity
      have h1 := (le_div_iff₀ hpos).mp hδ_le
      linarith
    dsimp only [η, α, gap] at hmul ⊢; linarith
  -- Step 3: Choose fixed `D₀ ≥ max 6 M_H` large enough that `E1_D0 ≤ J_val / 2` and combined `D₀`-error `≤ η / 4`
  have htend_E1 := tendsto_E1_D0 k T.bound
  have htend_E2 : Filter.Tendsto (fun D₀ : ℕ =>
      T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) Filter.atTop (nhds 0) := by
    have hδ : Filter.Tendsto (fun D₀ : ℕ => (2 : ℝ) / ((D₀ - 2 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
      have hnat : Filter.Tendsto (fun D₀ : ℕ => ((D₀ - 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
        rw [Filter.tendsto_atTop_atTop]; intro x; refine ⟨Nat.ceil x + 2, fun n hn => ?_⟩
        exact (Nat.le_ceil x).trans (by exact_mod_cast (show Nat.ceil x ≤ n - 2 by omega))
      exact tendsto_const_nhds.div_atTop hnat
    have h1 := (((tendsto_const_nhds (x := (1 : ℝ))).add hδ).pow ((k + 1) * k)).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using h1.const_mul (T.bound ^ 2)
  have htend_comb : Filter.Tendsto (fun D₀ : ℕ =>
      α * ((k + 1 : ℕ) : ℝ) * E1_D0 k T.bound D₀ +
      (m : ℝ) * (T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1))) Filter.atTop (nhds 0) := by
    have := (htend_E1.const_mul (α * ((k + 1 : ℕ) : ℝ))).add (htend_E2.const_mul (m : ℝ))
    simpa using this
  have hev1 := (htend_E1.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < J_val / 2)))
  have hev2 := (htend_comb.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < η / 4)))
  rw [Filter.eventually_atTop] at hev1 hev2
  obtain ⟨D₁, hD₁⟩ := hev1
  obtain ⟨D₂, hD₂⟩ := hev2
  set D₀ : ℕ := max (max 6 M_H) (max D₁ D₂)
  have hD6 : 6 ≤ D₀ := (le_max_left 6 M_H).trans (le_max_left _ _)
  have hDM : M_H ≤ D₀ := (le_max_right 6 M_H).trans (le_max_left _ _)
  have hE1_half : E1_D0 k T.bound D₀ ≤ J_val / 2 := (hD₁ D₀ ((le_max_left D₁ D₂).trans (le_max_right _ _))).le
  have hEcomb : α * ((k + 1 : ℕ) : ℝ) * E1_D0 k T.bound D₀ +
      (m : ℝ) * (T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) ≤ η / 4 :=
    (hD₂ D₀ ((le_max_right D₁ D₂).trans (le_max_right _ _))).le
  have hdiff : ∀ i j : Fin (k + 1), i ≠ j → (h i : ℤ) - (h j : ℤ) ≠ 0 ∧ |(h i : ℤ) - (h j : ℤ)| ≤ (D₀ : ℤ) := by
    intro i j hij
    have hne : h i ≠ h j := fun heq => hij (h.injective heq)
    have hiM : h i ≤ D₀ := (hM_H i).trans hDM
    have hjM : h j ≤ D₀ := (hM_H j).trans hDM
    refine ⟨by omega, ?_⟩
    rw [abs_le]; constructor <;> omega
  -- Step 4: Fix W-trick `W₀ = W D₀`, `b`, and dyadic sieve weights `w`
  set W₀ := W D₀
  have hW_pos : 1 ≤ W₀ := W_pos D₀
  have hW_posR : (0 : ℝ) < (W₀ : ℝ) := Nat.cast_pos.mpr hW_pos
  have hphiW_pos : (0 : ℝ) < (W₀.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hW_pos)
  set cW : ℝ := (W₀.totient : ℝ) / (W₀ : ℝ)
  have hcW_pos : 0 < cW := div_pos hphiW_pos hW_posR
  obtain ⟨b, hb_cop⟩ := exists_W_trick_residue hadm D₀
  have hcop_b : ∀ i : Fin (k + 1), Nat.Coprime (b + h i) W₀ := fun i => hb_cop (h i) (hh_mem i)
  let R_of : ℕ → ℝ := fun j => ((2 ^ j : ℕ) : ℝ) ^ α
  let w : ℕ → ℝ := fun n =>
    if 2 ^ 10 ≤ n then sieveWeight h W₀ (R_of (Nat.log 2 n)) T n else 0
  have hw_nn : ∀ n, 0 ≤ w n := fun n => by
    dsimp only [w]; split_ifs
    · unfold sieveWeight; exact sq_nonneg _
    · exact le_rfl
  -- Step 5: Gather uniform constants across `i : Fin (k + 1)` from `Q2Sum_asymp_upper`, `Q1Sum_asymp_lower`, `S1_m_interval_lower`, `pi_diff_lower`
  obtain ⟨K₂, hK₂_nn, hQ2_asymp⟩ := Q2Sum_asymp_upper hD6 T
  have hQ1_all : ∀ i : Fin (k + 1), ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ R : ℝ, Real.exp 4 ≤ R →
      (cW * Real.log R) ^ (k + 2) * (J_val - E1_D0 k T.bound D₀) -
        K₁ * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) ≤ Q1Sum W₀ R T i :=
    fun i => Q1Sum_asymp_lower hD6 T i
  choose K₁_f hK₁_nn hQ1_f using hQ1_all
  set K₁ : ℝ := ∑ i : Fin (k + 1), K₁_f i
  have hK₁_max : ∀ i : Fin (k + 1), K₁_f i ≤ K₁ := fun i =>
    Finset.single_le_sum (fun j _ => hK₁_nn j) (Finset.mem_univ i)
  have hK₁_nonneg : 0 ≤ K₁ := Finset.sum_nonneg fun i _ => hK₁_nn i
  have hS1_all : ∀ i : Fin (k + 1), ∃ B_bv C_err : ℝ, 0 < B_bv ∧ 0 ≤ C_err ∧
      ∀ (X A B : ℕ) (R : ℝ),
        16 ≤ X → X ≤ A → A ≤ B → B ≤ 2 * X → h i ≤ X →
        Real.exp 4 ≤ R → R < (X : ℝ) →
        (W₀ : ℝ) * R ^ 2 ≤ Real.sqrt ((A + h i - 1 : ℕ) : ℝ) / (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv →
        ((((Finset.range (B + h i)).filter Nat.Prime).card : ℝ) -
          (((Finset.range (A + h i)).filter Nat.Prime).card : ℝ)) / (W₀.totient : ℝ) *
          Q1Sum W₀ R T i - C_err * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 ≤
        ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h i)),
          sieveWeight h W₀ R T n :=
    fun i => S1_m_interval_lower hD6 hdiff hcop_b T i
  choose B_bv_f C_err_f hBbv_f hCerr_f hS1_f using hS1_all
  set B_bv : ℝ := ∑ i : Fin (k + 1), B_bv_f i
  have hBbv_ge : ∀ i : Fin (k + 1), B_bv_f i ≤ B_bv := fun i =>
    Finset.single_le_sum (fun j _ => (hBbv_f j).le) (Finset.mem_univ i)
  have hBbv_pos : 0 < B_bv := lt_of_lt_of_le (hBbv_f 0) (hBbv_ge 0)
  set C_bv_tot : ℝ := ∑ i : Fin (k + 1), C_err_f i
  have hCbv_nn : 0 ≤ C_bv_tot := Finset.sum_nonneg fun i _ => hCerr_f i
  obtain ⟨c_sw, C_sw, hc_sw, hC_sw, hpi_lo⟩ := pi_diff_lower
  -- Step 6: Prove dyadic block lower bound for all `j ≥ J₀` and all `[A, B) ⊆ [2^j, 2^(j+1)]`!
  -- First collect `isLittleO` thresholds for `X = 2^j → ∞`:
  have htend_X : Filter.Tendsto (fun j : ℕ => ((2 ^ j : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]; intro x; refine ⟨Nat.ceil x + 1, fun j hj => ?_⟩
    have h1 : j ≤ 2 ^ j := (Nat.lt_two_pow_self (n := j)).le
    exact (Nat.le_ceil x).trans (by exact_mod_cast (show Nat.ceil x ≤ 2 ^ j by omega))
  have htend_logX : Filter.Tendsto (fun j : ℕ => Real.log ((2 ^ j : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp htend_X
  -- (a) `R_of j ≥ exp 4` and `R_of j < 2^j`
  have hev_R : ∀ᶠ j in Filter.atTop, Real.exp 4 ≤ R_of j ∧ R_of j < ((2 ^ j : ℕ) : ℝ) := by
    filter_upwards [htend_X.eventually_ge_atTop (max 16 ((Real.exp 4) ^ (α⁻¹) + 1))] with j hj
    have hX16 : (16 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := (le_max_left _ _).trans hj
    have hXpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
    constructor
    · have h1 : (Real.exp 4) ^ (α⁻¹) ≤ ((2 ^ j : ℕ) : ℝ) := by linarith [le_max_right (16 : ℝ) ((Real.exp 4) ^ (α⁻¹) + 1)]
      have h2 := Real.rpow_le_rpow (by positivity) h1 hα_pos.le
      rw [← Real.rpow_mul (Real.exp_pos 4).le, inv_mul_cancel₀ hα_pos.ne', Real.rpow_one] at h2
      exact h2
    · calc R_of j = ((2 ^ j : ℕ) : ℝ) ^ α := rfl
        _ < ((2 ^ j : ℕ) : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by dsimp only [α]; linarith)
        _ = ((2 ^ j : ℕ) : ℝ) := Real.rpow_one _
  -- (b) BV range condition: `W₀ * (R_of j)^2 ≤ √(2^j - 1) / (log (3 * 2^j))^B_bv`
  -- Since `W₀ * X^(2*α) = W₀ * X^(1/2 - 2*δ_exp)` and `√(X - 1) ≥ √(X/2) = X^(1/2) / √2`,
  -- we need `(log (3 X))^B_bv / X^(2 * δ_exp) ≤ 1 / (√2 * W₀)`!
  have hev_BV : ∀ᶠ j in Filter.atTop,
      (W₀ : ℝ) * (R_of j) ^ 2 ≤ Real.sqrt (((2 ^ j - 1 : ℕ) : ℝ)) / (Real.log ((3 * 2 ^ j : ℕ) : ℝ)) ^ B_bv := by
    have hlo : Filter.Tendsto (fun x : ℝ => (Real.log (3 * x)) ^ B_bv / x ^ (2 * δ_exp)) Filter.atTop (nhds 0) := by
      have h1 := ((isLittleO_log_rpow_atTop (show 0 < (2 * δ_exp) / B_bv by positivity)).tendsto_div_nhds_zero).comp
        (Filter.tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num))
      have h2 : Filter.Tendsto (fun x : ℝ => (Real.log (3 * x) / (3 * x) ^ ((2 * δ_exp) / B_bv)) ^ B_bv) Filter.atTop (nhds 0) := by
        have := h1.rpow_const (p := B_bv) (Or.inr hBbv_pos.le)
        simpa [Real.zero_rpow hBbv_pos.ne'] using this
      have h3 := h2.const_mul ((3 : ℝ) ^ (2 * δ_exp))
      rw [mul_zero] at h3
      refine h3.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      have h3x : (0 : ℝ) < 3 * x := by linarith
      have hlog3x : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
      rw [Real.div_rpow hlog3x (Real.rpow_pos_of_pos h3x _).le, ← Real.rpow_mul h3x.le,
        div_mul_cancel₀ _ hBbv_pos.ne', Real.mul_rpow (by norm_num) (by linarith)]
      field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (2 * δ_exp)).ne']
    have hev0 := (hlo.comp htend_X).eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * (W₀ : ℝ))))
    filter_upwards [hev0, htend_X.eventually_ge_atTop 16] with j hj hX16
    have hXpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
    have h3eq : ((3 * 2 ^ j : ℕ) : ℝ) = 3 * ((2 ^ j : ℕ) : ℝ) := by push_cast; rfl
    rw [h3eq]
    have hsqrt_lo : ((2 ^ j : ℕ) : ℝ) ^ ((1 : ℝ) / 2) / 2 ≤ Real.sqrt (((2 ^ j - 1 : ℕ) : ℝ)) := by
      rw [← Real.sqrt_eq_rpow]
      have h1 : ((2 ^ j : ℕ) : ℝ) / 4 ≤ ((2 ^ j - 1 : ℕ) : ℝ) := by
        have h2j1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        rw [Nat.cast_sub h2j1, Nat.cast_one]; linarith
      calc Real.sqrt ((2 ^ j : ℕ) : ℝ) / 2 = Real.sqrt (((2 ^ j : ℕ) : ℝ) / 4) := by
            rw [Real.sqrt_div hXpos.le, show Real.sqrt (4 : ℝ) = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        _ ≤ Real.sqrt (((2 ^ j - 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt h1
    have hlog3_pos : 0 < Real.log (3 * ((2 ^ j : ℕ) : ℝ)) := Real.log_pos (by linarith)
    have hR2 : (R_of j) ^ 2 = ((2 ^ j : ℕ) : ℝ) ^ (2 * α) := by
      dsimp only [R_of]; rw [← Real.rpow_natCast (((2 ^ j : ℕ) : ℝ) ^ α) 2, ← Real.rpow_mul hXpos.le]
      congr 1; push_cast; ring
    have hmul_pow : ((2 ^ j : ℕ) : ℝ) ^ (2 * α) * ((2 ^ j : ℕ) : ℝ) ^ (2 * δ_exp) =
        ((2 ^ j : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hXpos]; congr 1; dsimp only [α]; ring
    have hj' : (Real.log (3 * ((2 ^ j : ℕ) : ℝ))) ^ B_bv ≤
        ((2 ^ j : ℕ) : ℝ) ^ (2 * δ_exp) / (2 * (W₀ : ℝ)) := by
      have h1 := (div_lt_iff₀ (Real.rpow_pos_of_pos hXpos _)).mp hj
      linarith [show 1 / (2 * (W₀ : ℝ)) * ((2 ^ j : ℕ) : ℝ) ^ (2 * δ_exp) =
        ((2 ^ j : ℕ) : ℝ) ^ (2 * δ_exp) / (2 * (W₀ : ℝ)) by ring]
    rw [hR2, le_div_iff₀ (Real.rpow_pos_of_pos hlog3_pos _)]
    calc (W₀ : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (2 * α) * (Real.log (3 * ((2 ^ j : ℕ) : ℝ))) ^ B_bv
        ≤ (W₀ : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (2 * α) * (((2 ^ j : ℕ) : ℝ) ^ (2 * δ_exp) / (2 * (W₀ : ℝ))) :=
          mul_le_mul_of_nonneg_left hj' (by positivity)
      _ = ((2 ^ j : ℕ) : ℝ) ^ (2 * α) * ((2 ^ j : ℕ) : ℝ) ^ (2 * δ_exp) / 2 := by
          field_simp [hW_posR.ne']
      _ = ((2 ^ j : ℕ) : ℝ) ^ ((1 : ℝ) / 2) / 2 := by rw [hmul_pow]
      _ ≤ Real.sqrt (((2 ^ j - 1 : ℕ) : ℝ)) := hsqrt_lo
  -- (c) `S2` additive error `m * (∑ |lamVar|)^2 ≤ X / (log X)^4`!
  -- Since `∑ |lamVar| ≤ R * (log R + 1)^k * C_lam * (log X)^(2k+2) = O(X^α * (log X)^(3k+2))`,
  -- its square is `O(X^(1/2 - 2 δ_exp) * (log X)^(6k+4)) = o(X / (log X)^4)`!
  have hev_S2err : ∀ᶠ j in Filter.atTop,
      (m : ℝ) * (∑ d ∈ validTupleSet k W₀ (R_of j), |lamVar W₀ (R_of j) T d|) ^ 2 ≤
        ((2 ^ j : ℕ) : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 := by
    set C_s2 : ℝ := (m : ℝ) * (T.bound * (12 * Real.exp 2) ^ (k + 1) * (2 : ℝ) ^ k) ^ 2
    have hlo : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ (6 * k + 8 : ℕ) / x ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) := by
      have h1 := ((isLittleO_log_rpow_atTop (show (0 : ℝ) < (1 / 2) / (6 * k + 8 : ℕ) by positivity)).tendsto_div_nhds_zero)
      have h2 := h1.pow (6 * k + 8)
      rw [zero_pow (by omega)] at h2
      refine h2.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      rw [div_pow, ← Real.rpow_natCast (x ^ _) (6 * k + 8), ← Real.rpow_mul (by linarith)]
      congr 2; field_simp [show ((6 * k + 8 : ℕ) : ℝ) ≠ 0 by positivity]
    have hev0 := (hlo.comp htend_X).eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (C_s2 + 1)))
    filter_upwards [hev0, hev_R, htend_X.eventually_ge_atTop 16] with j hj hRj hX16
    set X : ℕ := 2 ^ j
    set R : ℝ := R_of j
    have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
    have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos 4) hRj.1
    have hR1 : 1 ≤ R := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hRj.1
    have hlogX_ge2 : 2 ≤ Real.log (X : ℝ) := by
      have h1 : Real.exp 2 ≤ (16 : ℝ) := by
        have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        calc Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le he 2
          _ ≤ 16 := by norm_num
      have h3 := Real.log_le_log (Real.exp_pos 2) (h1.trans hX16)
      rwa [Real.log_exp] at h3
    have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
    have hlogR_le : Real.log R ≤ Real.log (X : ℝ) := Real.log_le_log hRpos hRj.2.le
    have hlog2R_le : Real.log (2 * R) ≤ 2 * Real.log (X : ℝ) := by
      have h1 : 2 * R ≤ (X : ℝ) ^ 2 := by nlinarith
      calc Real.log (2 * R) ≤ Real.log ((X : ℝ) ^ 2) := Real.log_le_log (by positivity) h1
        _ = 2 * Real.log (X : ℝ) := by rw [Real.log_pow]; ring
    have hLmax : ∀ d ∈ validTupleSet k W₀ R,
        |lamVar W₀ R T d| ≤ T.bound * (12 * Real.exp 2) ^ (k + 1) * (Real.log (X : ℝ)) ^ (2 * (k + 1)) := fun d _ => by
      have h1 := abs_lamVar_le (W₀ := W₀) hRj.1 T d
      have hbase : Real.exp 2 * Real.log R * (6 * Real.log (2 * R)) ≤ 12 * Real.exp 2 * (Real.log (X : ℝ)) ^ 2 := by
        have := Real.log_nonneg hR1; have := Real.log_nonneg (by linarith : 1 ≤ 2 * R)
        calc Real.exp 2 * Real.log R * (6 * Real.log (2 * R))
            ≤ Real.exp 2 * Real.log (X : ℝ) * (6 * (2 * Real.log (X : ℝ))) := by gcongr
          _ = 12 * Real.exp 2 * (Real.log (X : ℝ)) ^ 2 := by ring
      calc |lamVar W₀ R T d| ≤ T.bound * (Real.exp 2 * Real.log R * (6 * Real.log (2 * R))) ^ (k + 1) := h1
        _ ≤ T.bound * (12 * Real.exp 2 * (Real.log (X : ℝ)) ^ 2) ^ (k + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have := Real.log_nonneg hR1; have := Real.log_nonneg (by linarith : 1 ≤ 2 * R); positivity) hbase _) T.bound_nonneg
        _ = T.bound * (12 * Real.exp 2) ^ (k + 1) * (Real.log (X : ℝ)) ^ (2 * (k + 1)) := by
            rw [mul_pow, ← pow_mul]; ring
    have hsum_lam : ∑ d ∈ validTupleSet k W₀ R, |lamVar W₀ R T d| ≤
        T.bound * (12 * Real.exp 2) ^ (k + 1) * (2 : ℝ) ^ k * R * (Real.log (X : ℝ)) ^ (3 * k + 2) := by
      calc ∑ d ∈ validTupleSet k W₀ R, |lamVar W₀ R T d|
          ≤ ((validTupleSet k W₀ R).card : ℝ) * (T.bound * (12 * Real.exp 2) ^ (k + 1) * (Real.log (X : ℝ)) ^ (2 * (k + 1))) := by
            calc _ ≤ ∑ _d ∈ validTupleSet k W₀ R, (T.bound * (12 * Real.exp 2) ^ (k + 1) * (Real.log (X : ℝ)) ^ (2 * (k + 1))) :=
                  Finset.sum_le_sum hLmax
              _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (R * (Real.log R + 1) ^ k) * (T.bound * (12 * Real.exp 2) ^ (k + 1) * (Real.log (X : ℝ)) ^ (2 * (k + 1))) :=
            mul_le_mul_of_nonneg_right (card_validTupleSet_le k W₀ hR1) (by have := T.bound_nonneg; positivity)
        _ ≤ (R * (2 * Real.log (X : ℝ)) ^ k) * (T.bound * (12 * Real.exp 2) ^ (k + 1) * (Real.log (X : ℝ)) ^ (2 * (k + 1))) := by
            have hlr1 : Real.log R + 1 ≤ 2 * Real.log (X : ℝ) := by linarith
            have hpk : (Real.log R + 1) ^ k ≤ (2 * Real.log (X : ℝ)) ^ k :=
              pow_le_pow_left₀ (by linarith [Real.log_nonneg hR1]) hlr1 k
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpk hRpos.le)
              (by have := T.bound_nonneg; positivity)
        _ = T.bound * (12 * Real.exp 2) ^ (k + 1) * (2 : ℝ) ^ k * R * (Real.log (X : ℝ)) ^ (3 * k + 2) := by
            rw [mul_pow, show 3 * k + 2 = k + 2 * (k + 1) by ring, pow_add]; ring
    have hR2_le : R ^ 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := by
      dsimp only [R, R_of]
      rw [← Real.rpow_natCast (((X : ℝ)) ^ α) 2, ← Real.rpow_mul hXpos.le]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp only [α]; push_cast; linarith)
    have hsq_half : (X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ ((1 : ℝ) / 2) = (X : ℝ) := by
      rw [← Real.rpow_add hXpos]; norm_num
    have hj' : C_s2 * (Real.log (X : ℝ)) ^ (6 * k + 8) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := by
      have h1 : (Real.log (X : ℝ)) ^ (6 * k + 8) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) / (C_s2 + 1) := by
        have := (div_lt_iff₀ (Real.rpow_pos_of_pos hXpos _)).mp hj
        linarith [show 1 / (C_s2 + 1) * (X : ℝ) ^ ((1 : ℝ) / 2) = (X : ℝ) ^ ((1 : ℝ) / 2) / (C_s2 + 1) by ring]
      have h2 : C_s2 * ((X : ℝ) ^ ((1 : ℝ) / 2) / (C_s2 + 1)) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [Real.rpow_pos_of_pos hXpos ((1 : ℝ) / 2)]
      exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2
    calc (m : ℝ) * (∑ d ∈ validTupleSet k W₀ R, |lamVar W₀ R T d|) ^ 2
        ≤ (m : ℝ) * (T.bound * (12 * Real.exp 2) ^ (k + 1) * (2 : ℝ) ^ k * R * (Real.log (X : ℝ)) ^ (3 * k + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hsum_lam 2) (Nat.cast_nonneg _)
      _ = C_s2 * R ^ 2 * (Real.log (X : ℝ)) ^ (6 * k + 4) := by
          dsimp only [C_s2]; rw [show 6 * k + 4 = (3 * k + 2) * 2 by ring, pow_mul]; ring
      _ ≤ C_s2 * (X : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (X : ℝ)) ^ (6 * k + 4) := by gcongr
      _ = (X : ℝ) ^ ((1 : ℝ) / 2) * (C_s2 * (Real.log (X : ℝ)) ^ (6 * k + 8)) / (Real.log (X : ℝ)) ^ 4 := by
          rw [show 6 * k + 8 = (6 * k + 4) + 4 by ring, pow_add]
          field_simp [(pow_pos hlogX_pos 4).ne']; ring
      _ ≤ (X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ ((1 : ℝ) / 2) / (Real.log (X : ℝ)) ^ 4 := by gcongr
      _ = (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by rw [hsq_half]
  -- (d) SW error times `(cW * log R)^(k + 2) * J_val` is `≤ X / (log X)^4`!
  have hev_SW : ∀ᶠ j in Filter.atTop,
      ((k + 1 : ℕ) : ℝ) * (6 * C_sw * ((2 ^ j : ℕ) : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log ((2 ^ j : ℕ) : ℝ) / 2)) / (W₀.totient : ℝ)) *
        ((cW * Real.log (R_of j)) ^ (k + 2) * J_val) ≤
      ((2 ^ j : ℕ) : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 := by
    set C_sw_tot : ℝ := ((k + 1 : ℕ) : ℝ) * (6 * C_sw / (W₀.totient : ℝ)) * cW ^ (k + 2) * J_val
    have hCsw_nn : 0 ≤ C_sw_tot := by positivity
    have htend_exp : Filter.Tendsto (fun L : ℝ => L ^ (k + 6) * Real.exp (-c_sw * Real.sqrt (L / 2))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun u : ℝ => u ^ (2 * (k + 6)) * Real.exp (-(c_sw / Real.sqrt 2) * u)) Filter.atTop (nhds 0) := by
        have hpos : 0 < c_sw / Real.sqrt 2 := by positivity
        have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * (k + 6))).comp
          (Filter.tendsto_id.const_mul_atTop hpos)
        have h3 := h2.const_mul (((c_sw / Real.sqrt 2) ^ (2 * (k + 6)))⁻¹)
        rw [mul_zero] at h3
        refine h3.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u _
        simp only [Function.comp_apply, id_eq, mul_pow]
        field_simp [(pow_pos hpos (2 * (k + 6))).ne']
      have h4 := h1.comp (Real.tendsto_sqrt_atTop)
      refine h4.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with L hL
      have hL0 : 0 ≤ L := by linarith
      simp only [Function.comp_apply]
      rw [pow_mul, Real.sq_sqrt hL0, Real.sqrt_div hL0 2]
      congr 2; ring
    have hev0 := (htend_exp.comp htend_logX).eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (C_sw_tot + 1)))
    filter_upwards [hev0, hev_R, htend_X.eventually_ge_atTop 16] with j hj hRj hX16
    set X : ℕ := 2 ^ j
    set R : ℝ := R_of j
    have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
    have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
    have hlogR_le : Real.log R ≤ Real.log (X : ℝ) := Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 4) hRj.1) hRj.2.le
    have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hRj.1)
    have hj' : C_sw_tot * ((Real.log (X : ℝ)) ^ (k + 6) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2))) ≤ 1 := by
      have h1 : C_sw_tot * (1 / (C_sw_tot + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      exact (mul_le_mul_of_nonneg_left hj.le hCsw_nn).trans h1
    calc ((k + 1 : ℕ) : ℝ) * (6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) / (W₀.totient : ℝ)) *
            ((cW * Real.log R) ^ (k + 2) * J_val)
        ≤ ((k + 1 : ℕ) : ℝ) * (6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) / (W₀.totient : ℝ)) *
            ((cW * Real.log (X : ℝ)) ^ (k + 2) * J_val) := by
          gcongr
      _ = (X : ℝ) * (C_sw_tot * ((Real.log (X : ℝ)) ^ (k + 6) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)))) /
            (Real.log (X : ℝ)) ^ 4 := by
          dsimp only [C_sw_tot]
          rw [mul_pow, show k + 6 = (k + 2) + 4 by ring, pow_add]
          field_simp [(pow_pos hlogX_pos 4).ne', hphiW_pos.ne']
          ring
      _ ≤ (X : ℝ) * 1 / (Real.log (X : ℝ)) ^ 4 := by gcongr
      _ = (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by rw [mul_one]
  -- (e) Lower-order `(log R)^(-1/2)` and `log X / log (3 X)` margins for `j ≥ J₀`
  have hev_margin : ∀ᶠ j in Filter.atTop,
      -- (1) `Q1_lo > 0`: `K₁ / √(log R) ≤ cW^(k+2) * (J_val / 4)`
      K₁ / Real.sqrt (Real.log (R_of j)) ≤ cW ^ (k + 2) * (J_val / 4) ∧
      -- (2) `log X / log (3 X) ≥ 1 - η / (8 * α * (k + 1) * J_val)`
      α * (1 - Real.log ((2 ^ j : ℕ) : ℝ) / Real.log ((3 * 2 ^ j : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) * J_val ≤ η / 8 ∧
      -- (3) `(K₁ * α * (k + 1) / cW^(k+2) + m * K₂ / cW^(k+1)) / √(log R) ≤ η / 8`
      (α * ((k + 1 : ℕ) : ℝ) * K₁ / cW ^ (k + 2) + (m : ℝ) * K₂ / cW ^ (k + 1)) /
          Real.sqrt (Real.log (R_of j)) ≤ η / 8 ∧
      -- (4) Main term beats total additive error on `[N, 2N)`:
      3 * (C_bv_tot + 2) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 <
        (1 / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) := by
    have htend_logR : Filter.Tendsto (fun j : ℕ => Real.log (R_of j)) Filter.atTop Filter.atTop := by
      have h1 := htend_logX.const_mul_atTop hα_pos
      refine h1.congr' ?_
      filter_upwards [htend_X.eventually_ge_atTop 1] with j hj
      dsimp only [R_of]; rw [Real.log_rpow (by linarith)]
    have htend_inv_sqrt : Filter.Tendsto (fun j : ℕ => (Real.sqrt (Real.log (R_of j)))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp htend_logR)
    have h1 := (by simpa only [mul_zero] using htend_inv_sqrt.const_mul K₁ :
      Filter.Tendsto (fun j => K₁ * (Real.sqrt (Real.log (R_of j)))⁻¹) Filter.atTop (nhds 0)).eventually
      (Iio_mem_nhds (by positivity : (0 : ℝ) < cW ^ (k + 2) * (J_val / 4)))
    have h2 : ∀ᶠ j in Filter.atTop,
        α * (1 - Real.log ((2 ^ j : ℕ) : ℝ) / Real.log ((3 * 2 ^ j : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) * J_val ≤ η / 8 := by
      have ht : Filter.Tendsto (fun j : ℕ => Real.log 3 / Real.log ((2 ^ j : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop htend_logX
      have h2' := (by simpa only [mul_zero] using ht.const_mul (α * ((k + 1 : ℕ) : ℝ) * J_val) :
        Filter.Tendsto (fun j => α * ((k + 1 : ℕ) : ℝ) * J_val * (Real.log 3 / Real.log ((2 ^ j : ℕ) : ℝ)))
          Filter.atTop (nhds 0)).eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < η / 8))
      filter_upwards [h2', htend_X.eventually_ge_atTop 16] with j hj hX16
      have hXpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
      have hlogX_pos : 0 < Real.log ((2 ^ j : ℕ) : ℝ) := Real.log_pos (by linarith)
      have hlog3X : Real.log ((3 * 2 ^ j : ℕ) : ℝ) = Real.log 3 + Real.log ((2 ^ j : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Real.log_mul (by norm_num) hXpos.ne']; norm_cast
      have hlog3X_pos : 0 < Real.log ((3 * 2 ^ j : ℕ) : ℝ) := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
      have hdiff_le : 1 - Real.log ((2 ^ j : ℕ) : ℝ) / Real.log ((3 * 2 ^ j : ℕ) : ℝ) ≤
          Real.log 3 / Real.log ((2 ^ j : ℕ) : ℝ) := by
        rw [one_sub_div hlog3X_pos.ne', hlog3X]
        have hnum : Real.log 3 + Real.log ((2 ^ j : ℕ) : ℝ) - Real.log ((2 ^ j : ℕ) : ℝ) = Real.log 3 := by ring
        rw [hnum]
        exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hlogX_pos (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)])
      calc α * (1 - Real.log ((2 ^ j : ℕ) : ℝ) / Real.log ((3 * 2 ^ j : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) * J_val
          = α * ((k + 1 : ℕ) : ℝ) * J_val * (1 - Real.log ((2 ^ j : ℕ) : ℝ) / Real.log ((3 * 2 ^ j : ℕ) : ℝ)) := by ring
        _ ≤ α * ((k + 1 : ℕ) : ℝ) * J_val * (Real.log 3 / Real.log ((2 ^ j : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiff_le (by positivity)
        _ ≤ η / 8 := hj.le
    have ht3 : Filter.Tendsto (fun j => (α * ((k + 1 : ℕ) : ℝ) * K₁ / cW ^ (k + 2) + (m : ℝ) * K₂ / cW ^ (k + 1)) *
        (Real.sqrt (Real.log (R_of j)))⁻¹) Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using htend_inv_sqrt.const_mul
        (α * ((k + 1 : ℕ) : ℝ) * K₁ / cW ^ (k + 2) + (m : ℝ) * K₂ / cW ^ (k + 1))
    have h3 := ht3.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < η / 8))
    have h4 : ∀ᶠ j in Filter.atTop,
        3 * (C_bv_tot + 2) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 <
          (1 / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) := by
      have ht0 : Filter.Tendsto (fun j : ℕ => 3 * (C_bv_tot + 2) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop ((Filter.tendsto_pow_atTop (by omega : 4 ≠ 0)).comp htend_logX)
      have h4a := ht0.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < (1 / (W₀ : ℝ)) * (cW * 1) ^ (k + 1) * (η / 2)))
      filter_upwards [h4a, htend_logR.eventually_ge_atTop 1] with j hj hlogR1
      calc 3 * (C_bv_tot + 2) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4
          < (1 / (W₀ : ℝ)) * (cW * 1) ^ (k + 1) * (η / 2) := hj
        _ ≤ (1 / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) := by gcongr
    filter_upwards [h1, h2, h3, h4] with j hj1 hj2 hj3 hj4
    refine ⟨?_, hj2, ?_, hj4⟩
    · simpa [div_eq_mul_inv, mul_zero] using hj1.le
    · simpa [div_eq_mul_inv, mul_zero] using hj3.le
  -- Combine all `∀ᶠ j` conditions into a single threshold `J₀ ≥ 10`!
  have hall_j : ∀ᶠ j in Filter.atTop,
      10 ≤ j ∧ 16 ≤ 2 ^ j ∧ M_H ≤ 2 ^ j ∧
      (Real.exp 4 ≤ R_of j ∧ R_of j < ((2 ^ j : ℕ) : ℝ)) ∧
      (W₀ : ℝ) * (R_of j) ^ 2 ≤ Real.sqrt (((2 ^ j - 1 : ℕ) : ℝ)) / (Real.log ((3 * 2 ^ j : ℕ) : ℝ)) ^ B_bv ∧
      (m : ℝ) * (∑ d ∈ validTupleSet k W₀ (R_of j), |lamVar W₀ (R_of j) T d|) ^ 2 ≤
        ((2 ^ j : ℕ) : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 ∧
      ((k + 1 : ℕ) : ℝ) * (6 * C_sw * ((2 ^ j : ℕ) : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log ((2 ^ j : ℕ) : ℝ) / 2)) / (W₀.totient : ℝ)) *
        ((cW * Real.log (R_of j)) ^ (k + 2) * J_val) ≤ ((2 ^ j : ℕ) : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 ∧
      (K₁ / Real.sqrt (Real.log (R_of j)) ≤ cW ^ (k + 2) * (J_val / 4) ∧
       α * (1 - Real.log ((2 ^ j : ℕ) : ℝ) / Real.log ((3 * 2 ^ j : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) * J_val ≤ η / 8 ∧
       (α * ((k + 1 : ℕ) : ℝ) * K₁ / cW ^ (k + 2) + (m : ℝ) * K₂ / cW ^ (k + 1)) /
          Real.sqrt (Real.log (R_of j)) ≤ η / 8 ∧
       3 * (C_bv_tot + 2) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 <
          (1 / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2)) := by
    filter_upwards [Filter.eventually_ge_atTop (max 10 (M_H + 4)), hev_R, hev_BV, hev_S2err, hev_SW, hev_margin] with j hj h1 h2 h3 h4 h5
    have hj10 : 10 ≤ j := (le_max_left _ _).trans hj
    have h2j16 : 16 ≤ 2 ^ j := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hMH : M_H ≤ 2 ^ j := le_trans (by have := (le_max_right 10 (M_H + 4)).trans hj; omega)
      (Nat.lt_two_pow_self (n := j)).le
    exact ⟨hj10, h2j16, hMH, h1, h2, h3, h4, h5⟩
  rw [Filter.eventually_atTop] at hall_j
  obtain ⟨J₀, hJ₀⟩ := hall_j
  -- Step 7: Prove the dyadic block lower bound on ANY `[A, B) ⊆ [2^j, 2^(j+1)]` with `j ≥ J₀`!
  have hdyadic : ∀ (j A B : ℕ), J₀ ≤ j → 2 ^ j ≤ A → A ≤ B → B ≤ 2 ^ (j + 1) →
      (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) -
        (C_bv_tot + 2) * ((2 ^ j : ℕ) : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 ≤
      (∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]), w n * (primeShiftCount H n : ℝ)) -
        (m : ℝ) * ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]), w n := by
    intro j A B hj hXA hAB hB2X
    obtain ⟨hj10, hX16, hMH, hRj, hBVj, hS2ej, hSWj, hK1m, hlogm, herr_m, _⟩ := hJ₀ j hj
    set X : ℕ := 2 ^ j
    set R : ℝ := R_of j
    have h2X : 2 ^ (j + 1) = 2 * X := by dsimp only [X]; rw [pow_succ]; ring
    rw [h2X] at hB2X
    have hlogR4 : 4 ≤ Real.log R := by
      have := Real.log_le_log (Real.exp_pos 4) hRj.1; rwa [Real.log_exp] at this
    have hlogR_pos : 0 < Real.log R := by linarith
    have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hlogR_eq : Real.log R = α * Real.log (X : ℝ) := by
      dsimp only [R, R_of]; exact Real.log_rpow (Nat.cast_pos.mpr (by omega)) α
    -- On `[A, B) ⊆ [2^j, 2^(j+1))`, `w n = sieveWeight h W₀ R T n`!
    have hw_eq : ∀ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]),
        w n = sieveWeight h W₀ R T n := by
      intro n hn
      have hnI := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
      have hn10 : 2 ^ 10 ≤ n := (Nat.pow_le_pow_right (by norm_num) hj10).trans (hXA.trans hnI.1)
      have hlogn : Nat.log 2 n = j := by
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · exact hXA.trans hnI.1
        · calc n < B := hnI.2
            _ ≤ 2 * X := hB2X
            _ = 2 ^ (j + 1) := h2X.symm
      dsimp only [w]; rw [if_pos hn10, hlogn]
    -- Rewrite `S₂` on `[A, B)` and upper bound via `S2_interval_upper` + `Q2Sum_asymp_upper`
    have hS2_up : (m : ℝ) * ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]), w n ≤
        (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log R) ^ (k + 1) *
          ((m : ℝ) * (I_val + T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) +
            ((m : ℝ) * K₂ / cW ^ (k + 1)) / Real.sqrt (Real.log R)) +
        (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by
      rw [Finset.sum_congr rfl hw_eq]
      have h1 := S2_interval_upper hdiff hRj.1 T b A B hAB
      have h2 := hQ2_asymp R hRj.1
      have hpow_half : (Real.log R) ^ (((k + 1 : ℕ) : ℝ) - 1 / 2) =
          (Real.log R) ^ (k + 1) / Real.sqrt (Real.log R) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.log R) (k + 1), ← Real.rpow_sub hlogR_pos]
      have h2' : Q2Sum W₀ R T ≤ (cW * Real.log R) ^ (k + 1) *
            ((I_val + T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) +
              (K₂ / cW ^ (k + 1)) / Real.sqrt (Real.log R)) := by
        rw [hpow_half] at h2
        have hrew : (cW * Real.log R) ^ (k + 1) * ((K₂ / cW ^ (k + 1)) / Real.sqrt (Real.log R)) =
            K₂ * ((Real.log R) ^ (k + 1) / Real.sqrt (Real.log R)) := by
          rw [mul_pow]; field_simp [(pow_pos hcW_pos (k + 1)).ne', (Real.sqrt_pos.mpr hlogR_pos).ne']
        linarith [mul_add ((cW * Real.log R) ^ (k + 1))
          (I_val + T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1))
          ((K₂ / cW ^ (k + 1)) / Real.sqrt (Real.log R))]
      have h3 := mul_le_mul_of_nonneg_left
        (h1.trans (add_le_add (mul_le_mul_of_nonneg_left h2' (div_nonneg (Nat.cast_nonneg _) hW_posR.le)) le_rfl))
        (Nat.cast_nonneg m)
      have hrew_m : (m : ℝ) * ((((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * ((cW * Real.log R) ^ (k + 1) *
            ((I_val + T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) +
              (K₂ / cW ^ (k + 1)) / Real.sqrt (Real.log R)))) =
          (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log R) ^ (k + 1) *
            ((m : ℝ) * (I_val + T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) +
              ((m : ℝ) * K₂ / cW ^ (k + 1)) / Real.sqrt (Real.log R)) := by ring
      linarith
    -- Rewrite `S₁` on `[A, B)` as `∑_{i : Fin (k + 1)} S₁^{(i)}` and lower bound via `S1_m_interval_lower` + `Q1Sum_asymp_lower` + `pi_diff_lower`!
    have hS1_split : ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]), w n * (primeShiftCount H n : ℝ) =
        ∑ i : Fin (k + 1), ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h i)),
          sieveWeight h W₀ R T n := by
      have hcnt : ∀ n : ℕ, (primeShiftCount H n : ℝ) =
          ∑ i : Fin (k + 1), if Nat.Prime (n + h i) then (1 : ℝ) else 0 := fun n => by
        unfold primeShiftCount
        rw [← hH_eq, Finset.filter_map, Finset.card_map, Finset.sum_boole]
        rfl
      have h1 : ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]), w n * (primeShiftCount H n : ℝ) =
          ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]),
            ∑ i : Fin (k + 1), if Nat.Prime (n + h i) then sieveWeight h W₀ R T n else 0 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hw_eq n hn, hcnt n, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext n; simp [and_assoc]
    -- Common lower bound `Q1_lo > 0` for all `i : Fin (k + 1)`
    set Q1_lo : ℝ := (cW * Real.log R) ^ (k + 2) * (J_val - E1_D0 k T.bound D₀) -
      K₁ * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2)
    have hpow_half2 : (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) =
        (Real.log R) ^ (k + 2) / Real.sqrt (Real.log R) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.log R) (k + 2), ← Real.rpow_sub hlogR_pos]
    have hQ1_lo_eq : Q1_lo = (cW * Real.log R) ^ (k + 2) *
        (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R)) := by
      dsimp only [Q1_lo]; rw [hpow_half2, mul_pow]
      field_simp [(pow_pos hcW_pos (k + 2)).ne', (Real.sqrt_pos.mpr hlogR_pos).ne']
    have hQ1_lo_pos : 0 ≤ Q1_lo := by
      rw [hQ1_lo_eq]
      refine mul_nonneg (by positivity) ?_
      have hK1_div : (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R) ≤ J_val / 4 := by
        rw [div_right_comm, div_le_iff₀ (pow_pos hcW_pos (k + 2))]
        linarith
      linarith
    have hQ1_lo_le_J : Q1_lo ≤ (cW * Real.log R) ^ (k + 2) * J_val := by
      dsimp only [Q1_lo]
      have h1 : 0 ≤ (cW * Real.log R) ^ (k + 2) * E1_D0 k T.bound D₀ :=
        mul_nonneg (by positivity) (E1_D0_nonneg _ _ _)
      have h2 : 0 ≤ K₁ * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) := by positivity
      linarith
    have hS1_i_lo : ∀ i : Fin (k + 1),
        (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log R) ^ (k + 1) *
          ((Real.log (X : ℝ) / Real.log ((3 * X : ℕ) : ℝ)) * α *
            (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R))) -
        (6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) / (W₀.totient : ℝ)) *
          ((cW * Real.log R) ^ (k + 2) * J_val) -
        C_err_f i * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 ≤
        ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀] ∧ Nat.Prime (n + h i)),
          sieveWeight h W₀ R T n := by
      intro i
      have hhiX : h i ≤ X := (hM_H i).trans hMH
      have hQR_i : (W₀ : ℝ) * R ^ 2 ≤ Real.sqrt ((A + h i - 1 : ℕ) : ℝ) / (Real.log ((3 * X : ℕ) : ℝ)) ^ (B_bv_f i) := by
        have hsq : Real.sqrt (((X - 1 : ℕ) : ℝ)) ≤ Real.sqrt ((A + h i - 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast (show X - 1 ≤ A + h i - 1 by omega))
        have hlog3_ge1 : 1 ≤ Real.log ((3 * X : ℕ) : ℝ) := by
          have h1 : Real.exp 1 ≤ ((3 * X : ℕ) : ℝ) := by
            have : (3 : ℝ) ≤ ((3 * X : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ 3 * X by omega)
            linarith [Real.exp_one_lt_d9]
          have h2 := Real.log_le_log (Real.exp_pos 1) h1
          rwa [Real.log_exp] at h2
        have hpow_le : (Real.log ((3 * X : ℕ) : ℝ)) ^ (B_bv_f i) ≤ (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv :=
          Real.rpow_le_rpow_of_exponent_le hlog3_ge1 (hBbv_ge i)
        calc (W₀ : ℝ) * R ^ 2
            ≤ Real.sqrt (((X - 1 : ℕ) : ℝ)) / (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv := hBVj
          _ ≤ Real.sqrt ((A + h i - 1 : ℕ) : ℝ) / (Real.log ((3 * X : ℕ) : ℝ)) ^ B_bv :=
              div_le_div_of_nonneg_right hsq (by positivity)
          _ ≤ Real.sqrt ((A + h i - 1 : ℕ) : ℝ) / (Real.log ((3 * X : ℕ) : ℝ)) ^ (B_bv_f i) :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos (by linarith) _) hpow_le
      have hS1i := hS1_f i X A B R hX16 hXA hAB hB2X hhiX hRj.1 hRj.2 hQR_i
      have hQ1i : Q1_lo ≤ Q1Sum W₀ R T i := by
        have h1 := hQ1_f i R hRj.1
        have h2 : K₁_f i * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) ≤
            K₁ * (Real.log R) ^ (((k + 2 : ℕ) : ℝ) - 1 / 2) :=
          mul_le_mul_of_nonneg_right (hK₁_max i) (by positivity)
        linarith
      have hΔπ_nn : 0 ≤ (((Finset.range (B + h i)).filter Nat.Prime).card : ℝ) -
          (((Finset.range (A + h i)).filter Nat.Prime).card : ℝ) := by
        have hsub : (Finset.range (A + h i)).filter Nat.Prime ⊆ (Finset.range (B + h i)).filter Nat.Prime :=
          Finset.filter_subset_filter _ (Finset.range_mono (by omega))
        have hc : ((Finset.range (A + h i)).filter Nat.Prime).card ≤ ((Finset.range (B + h i)).filter Nat.Prime).card :=
          Finset.card_le_card hsub
        have hR : (((Finset.range (A + h i)).filter Nat.Prime).card : ℝ) ≤
            (((Finset.range (B + h i)).filter Nat.Prime).card : ℝ) := by exact_mod_cast hc
        linarith
      have hpi_i := hpi_lo X A B (h i) hX16 hXA hAB hB2X hhiX
      have hmul1 : ((((Finset.range (B + h i)).filter Nat.Prime).card : ℝ) -
            (((Finset.range (A + h i)).filter Nat.Prime).card : ℝ)) / (W₀.totient : ℝ) * Q1_lo ≤
          ((((Finset.range (B + h i)).filter Nat.Prime).card : ℝ) -
            (((Finset.range (A + h i)).filter Nat.Prime).card : ℝ)) / (W₀.totient : ℝ) * Q1Sum W₀ R T i :=
        mul_le_mul_of_nonneg_left hQ1i (div_nonneg hΔπ_nn hphiW_pos.le)
      have hmul2 : ((((B - A : ℕ) : ℝ) / Real.log ((3 * X : ℕ) : ℝ)) -
            6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2))) / (W₀.totient : ℝ) * Q1_lo ≤
          ((((Finset.range (B + h i)).filter Nat.Prime).card : ℝ) -
            (((Finset.range (A + h i)).filter Nat.Prime).card : ℝ)) / (W₀.totient : ℝ) * Q1_lo :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpi_i hphiW_pos.le) hQ1_lo_pos
      have hsw_term : (6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) / (W₀.totient : ℝ)) * Q1_lo ≤
          (6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) / (W₀.totient : ℝ)) *
            ((cW * Real.log R) ^ (k + 2) * J_val) :=
        mul_le_mul_of_nonneg_left hQ1_lo_le_J (by positivity)
      have hmain_rew : ((((B - A : ℕ) : ℝ) / Real.log ((3 * X : ℕ) : ℝ)) / (W₀.totient : ℝ)) * Q1_lo =
          (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log R) ^ (k + 1) *
            ((Real.log (X : ℝ) / Real.log ((3 * X : ℕ) : ℝ)) * α *
              (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R))) := by
        rw [hQ1_lo_eq, pow_succ (cW * Real.log R) (k + 1), hlogR_eq]
        dsimp only [cW]
        have hlog3X_ne : Real.log ((3 * X : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < 3 * X by omega))).ne'
        field_simp [hW_posR.ne', hphiW_pos.ne', hlog3X_ne]
      rw [sub_div, sub_mul, hmain_rew] at hmul2
      linarith
    -- Sum `hS1_i_lo` over `i : Fin (k + 1)` and subtract `hS2_up`!
    have hS1_tot := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hS1_i_lo i
    rw [← hS1_split] at hS1_tot
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_mul, ← Finset.sum_div] at hS1_tot
    -- Compare the leading coefficient of `((B - A) / W₀) * (cW * log R)^(k + 1)` against `η / 2`!
    set Lratio := Real.log (X : ℝ) / Real.log ((3 * X : ℕ) : ℝ)
    have hLratio_le1 : Lratio ≤ 1 := by
      dsimp only [Lratio]
      have hlog3X_pos : 0 < Real.log ((3 * X : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < 3 * X by omega))
      rw [div_le_one hlog3X_pos]
      exact Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast (show X ≤ 3 * X by omega))
    have hLratio_nn : 0 ≤ Lratio := by
      dsimp only [Lratio]
      exact div_nonneg hlogX_pos.le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * X by omega)))
    have hcoef_ge : η / 2 ≤
        ((k + 1 : ℕ) : ℝ) * (Lratio * α * (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R))) -
        ((m : ℝ) * (I_val + T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) +
          ((m : ℝ) * K₂ / cW ^ (k + 1)) / Real.sqrt (Real.log R)) := by
      have hL_E1 : Lratio * (α * ((k + 1 : ℕ) : ℝ) * E1_D0 k T.bound D₀) ≤
          α * ((k + 1 : ℕ) : ℝ) * E1_D0 k T.bound D₀ :=
        mul_le_of_le_one_left (mul_nonneg (by positivity) (E1_D0_nonneg _ _ _)) hLratio_le1
      have hL_K1 : Lratio * (α * ((k + 1 : ℕ) : ℝ) * (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R)) ≤
          α * ((k + 1 : ℕ) : ℝ) * (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R) :=
        mul_le_of_le_one_left (by positivity) hLratio_le1
      have hη_def : α * ((k + 1 : ℕ) : ℝ) * J_val - (m : ℝ) * I_val = η := rfl
      have hL_J : α * ((k + 1 : ℕ) : ℝ) * J_val - Lratio * α * ((k + 1 : ℕ) : ℝ) * J_val =
          α * (1 - Lratio) * ((k + 1 : ℕ) : ℝ) * J_val := by ring
      have hrew_k1 : α * ((k + 1 : ℕ) : ℝ) * K₁ / cW ^ (k + 2) / Real.sqrt (Real.log R) =
          α * ((k + 1 : ℕ) : ℝ) * (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R) := by ring
      rw [add_div, hrew_k1] at herr_m
      have hrew_main : ((k + 1 : ℕ) : ℝ) * (Lratio * α * (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R))) =
          Lratio * α * ((k + 1 : ℕ) : ℝ) * J_val -
          Lratio * (α * ((k + 1 : ℕ) : ℝ) * E1_D0 k T.bound D₀) -
          Lratio * (α * ((k + 1 : ℕ) : ℝ) * (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R)) := by ring
      rw [hrew_main]; linarith
    have hmul_coef := mul_le_mul_of_nonneg_left hcoef_ge
      (mul_nonneg (div_nonneg (Nat.cast_nonneg (B - A)) hW_posR.le) (pow_nonneg (mul_nonneg hcW_pos.le hlogR_pos.le) (k + 1)))
    have hadd_err : C_bv_tot * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 +
        ((k + 1 : ℕ) : ℝ) * (6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) / (W₀.totient : ℝ)) *
          ((cW * Real.log R) ^ (k + 2) * J_val) +
        (X : ℝ) / (Real.log (X : ℝ)) ^ 4 ≤
        (C_bv_tot + 2) * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by
      have h1 : (C_bv_tot + 2) * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 =
          C_bv_tot * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 +
          (X : ℝ) / (Real.log (X : ℝ)) ^ 4 + (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by ring
      linarith
    have hS1_tot' : (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log R) ^ (k + 1) *
          (((k + 1 : ℕ) : ℝ) * (Lratio * α * (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R)))) -
        ((k + 1 : ℕ) : ℝ) * (6 * C_sw * (X : ℝ) * Real.exp (-c_sw * Real.sqrt (Real.log (X : ℝ) / 2)) / (W₀.totient : ℝ)) *
          ((cW * Real.log R) ^ (k + 2) * J_val) -
        C_bv_tot * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 ≤
        ∑ n ∈ (Finset.Ico A B).filter (fun n => n ≡ b [MOD W₀]), w n * (primeShiftCount H n : ℝ) := by
      have hrew1 : ((k + 1 : ℕ) : ℝ) * ((((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log R) ^ (k + 1) *
            (Lratio * α * (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R)))) =
          (((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log R) ^ (k + 1) *
            (((k + 1 : ℕ) : ℝ) * (Lratio * α * (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R)))) := by ring
      have hrew2 : (∑ i : Fin (k + 1), C_err_f i * (X : ℝ)) / (Real.log (X : ℝ)) ^ 4 =
          C_bv_tot * (X : ℝ) / (Real.log (X : ℝ)) ^ 4 := by
        rw [← Finset.sum_mul]
      linarith
    linarith [mul_sub ((((B - A : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log R) ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * (Lratio * α * (J_val - E1_D0 k T.bound D₀ - (K₁ / cW ^ (k + 2)) / Real.sqrt (Real.log R))))
      ((m : ℝ) * (I_val + T.bound ^ 2 * ((1 + 2 / ((D₀ - 2 : ℕ) : ℝ)) ^ ((k + 1) * k) - 1)) +
        ((m : ℝ) * K₂ / cW ^ (k + 1)) / Real.sqrt (Real.log R))]
  -- Step 8: Assemble `MAnalyticCore H (m + 1)` by splitting `[N, 2N)` into TWO dyadic pieces at `2^(j+1)`!
  refine ⟨⟨W₀, b, w, hw_nn, hb_cop, 2 ^ J₀, fun N hN => ?_⟩⟩
  simp only [Nat.add_sub_cancel]
  set j := Nat.log 2 N
  have hj_ge : J₀ ≤ j := Nat.le_log_of_pow_le (by norm_num) hN
  have hN_ge : 2 ^ j ≤ N := Nat.pow_log_le_self 2 (by have : 1 ≤ 2 ^ J₀ := Nat.one_le_two_pow; omega)
  have hN_lt : N < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h2N_le : 2 * N ≤ 2 ^ (j + 2) := by
    have : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
    omega
  have hsplit_Ico : wInterval N W₀ b =
      (Finset.Ico N (2 ^ (j + 1))).filter (fun n => n ≡ b [MOD W₀]) ∪
      (Finset.Ico (2 ^ (j + 1)) (2 * N)).filter (fun n => n ≡ b [MOD W₀]) := by
    ext n; simp only [wInterval, Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, hmod⟩
      by_cases hlt : n < 2 ^ (j + 1)
      · exact Or.inl ⟨⟨h1, hlt⟩, hmod⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hmod⟩
    · rintro (⟨⟨h1, h2⟩, hmod⟩ | ⟨⟨h1, h2⟩, hmod⟩)
      · exact ⟨⟨h1, by omega⟩, hmod⟩
      · exact ⟨⟨by omega, h2⟩, hmod⟩
  have hdisj : Disjoint
      ((Finset.Ico N (2 ^ (j + 1))).filter (fun n => n ≡ b [MOD W₀]))
      ((Finset.Ico (2 ^ (j + 1)) (2 * N)).filter (fun n => n ≡ b [MOD W₀])) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h1).1).2
    have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1; omega
  have hS1_eq : S₁ H w N W₀ b =
      (∑ n ∈ (Finset.Ico N (2 ^ (j + 1))).filter (fun n => n ≡ b [MOD W₀]), w n * (primeShiftCount H n : ℝ)) +
      (∑ n ∈ (Finset.Ico (2 ^ (j + 1)) (2 * N)).filter (fun n => n ≡ b [MOD W₀]), w n * (primeShiftCount H n : ℝ)) := by
    unfold S₁; rw [hsplit_Ico, Finset.sum_union hdisj]
  have hS2_eq : S₂ w N W₀ b =
      (∑ n ∈ (Finset.Ico N (2 ^ (j + 1))).filter (fun n => n ≡ b [MOD W₀]), w n) +
      (∑ n ∈ (Finset.Ico (2 ^ (j + 1)) (2 * N)).filter (fun n => n ≡ b [MOD W₀]), w n) := by
    unfold S₂; rw [hsplit_Ico, Finset.sum_union hdisj]
  have hpiece1 := hdyadic j N (2 ^ (j + 1)) hj_ge hN_ge hN_lt.le le_rfl
  have hpiece2 := hdyadic (j + 1) (2 ^ (j + 1)) (2 * N) (by omega) le_rfl (by omega) h2N_le
  -- Combine both pieces using `R_of j ≤ R_of (j + 1)` and `(2^(j+1) - N) + (2*N - 2^(j+1)) = N`!
  have hR_mono : R_of j ≤ R_of (j + 1) := by
    dsimp only [R_of]
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hα_pos.le
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)
  have hlogR_mono : Real.log (R_of j) ≤ Real.log (R_of (j + 1)) :=
    Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 4) (hJ₀ j hj_ge).2.2.2.1.1) hR_mono
  have hlogR_j_pos : 0 < Real.log (R_of j) := by
    have := Real.log_le_log (Real.exp_pos 4) (hJ₀ j hj_ge).2.2.2.1.1; rw [Real.log_exp] at this; linarith
  have hpowR_mono : (cW * Real.log (R_of j)) ^ (k + 1) ≤ (cW * Real.log (R_of (j + 1))) ^ (k + 1) :=
    pow_le_pow_left₀ (mul_nonneg hcW_pos.le hlogR_j_pos.le) (mul_le_mul_of_nonneg_left hlogR_mono hcW_pos.le) _
  have hlen_sum : ((2 ^ (j + 1) - N : ℕ) : ℝ) + ((2 * N - 2 ^ (j + 1) : ℕ) : ℝ) = (N : ℝ) := by
    have hnat : (2 ^ (j + 1) - N) + (2 * N - 2 ^ (j + 1)) = N := by omega
    exact_mod_cast hnat
  have hlogX_j_pos : 0 < Real.log ((2 ^ j : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 ^ j by have := (hJ₀ j hj_ge).2.1; omega))
  have hlogX_mono : Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log ((2 ^ (j + 1) : ℕ) : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr Nat.one_le_two_pow) (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j))
  have herr_comb : (C_bv_tot + 2) * ((2 ^ j : ℕ) : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 +
      (C_bv_tot + 2) * ((2 ^ (j + 1) : ℕ) : ℝ) / (Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ^ 4 ≤
      (N : ℝ) * (3 * (C_bv_tot + 2) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4) := by
    have h2j_le_N : ((2 ^ j : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge
    have h2j1_le_2N : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
      have : 2 ^ (j + 1) ≤ 2 * N := by omega
      exact_mod_cast this
    have h1 : (C_bv_tot + 2) * ((2 ^ (j + 1) : ℕ) : ℝ) / (Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ^ 4 ≤
        (C_bv_tot + 2) * (2 * (N : ℝ)) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 := by
      refine (div_le_div_of_nonneg_left (by positivity) (pow_pos hlogX_j_pos 4)
        (pow_le_pow_left₀ hlogX_j_pos.le hlogX_mono 4)).trans ?_
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2j1_le_2N (by positivity)) (by positivity)
    have h2 : (C_bv_tot + 2) * ((2 ^ j : ℕ) : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 ≤
        (C_bv_tot + 2) * (N : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2j_le_N (by positivity)) (by positivity)
    linarith [show (C_bv_tot + 2) * (N : ℝ) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 +
        (C_bv_tot + 2) * (2 * (N : ℝ)) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4 =
        (N : ℝ) * (3 * (C_bv_tot + 2) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4) by ring]
  have hmain_comb : (N : ℝ) * ((1 / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2)) ≤
      (((2 ^ (j + 1) - N : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) +
      (((2 * N - 2 ^ (j + 1) : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log (R_of (j + 1))) ^ (k + 1) * (η / 2) := by
    have h2 : (((2 * N - 2 ^ (j + 1) : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) ≤
        (((2 * N - 2 ^ (j + 1) : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log (R_of (j + 1))) ^ (k + 1) * (η / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowR_mono (div_nonneg (Nat.cast_nonneg _) hW_posR.le)) (by positivity)
    have hsum_eq : (((2 ^ (j + 1) - N : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) +
        (((2 * N - 2 ^ (j + 1) : ℕ) : ℝ) / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) =
        (N : ℝ) * ((1 / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2)) := by
      calc _ = ((((2 ^ (j + 1) - N : ℕ) : ℝ) + ((2 * N - 2 ^ (j + 1) : ℕ) : ℝ)) / (W₀ : ℝ)) *
              (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) := by ring
        _ = ((N : ℝ) / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2) := by rw [hlen_sum]
        _ = _ := by ring
    linarith
  have hstrict : (N : ℝ) * (3 * (C_bv_tot + 2) / (Real.log ((2 ^ j : ℕ) : ℝ)) ^ 4) <
      (N : ℝ) * ((1 / (W₀ : ℝ)) * (cW * Real.log (R_of j)) ^ (k + 1) * (η / 2)) :=
    mul_lt_mul_of_pos_left (hJ₀ j hj_ge).2.2.2.2.2.2.2.2.2.2 (Nat.cast_pos.mpr (by have : 1 ≤ 2 ^ J₀ := Nat.one_le_two_pow; omega))
  rw [hS1_eq, hS2_eq]
  linarith

/-- Noncomputable `MAnalyticCore H (m + 1)` extracted via `Classical.choice` from `exists_maynard_tao_sieve_core`. -/
def maynard_tao_sieve_core {H : Finset ℕ} (hadm : Admissible H)
    {k : ℕ} (hcard : H.card = k + 1) (m : ℕ)
    (T : SimplexTestFn (k + 1))
    (hI_pos : 0 < maynardI (k + 1) T.F)
    (hratio : 4 * (m : ℝ) * maynardI (k + 1) T.F < ((k + 1 : ℕ) : ℝ) * maynardJ0 k T.F) :
    MAnalyticCore H (m + 1) :=
  Classical.choice (exists_maynard_tao_sieve_core hadm hcard m T hI_pos hratio)

/-- Direct conversion from `MAnalyticCore H 2` (`S₁ > 1 * S₂`) to `AnalyticCore H` (`S₁ > S₂`). -/
def analyticCore_of_mAnalyticCore_two {H : Finset ℕ} (core : MAnalyticCore H 2) : AnalyticCore H where
  W := core.W
  b := core.b
  w := core.w
  w_nonneg := core.w_nonneg
  w_trick := core.w_trick
  dominance := by
    obtain ⟨N₀, hN₀⟩ := core.dominance
    refine ⟨N₀, fun N hN => ?_⟩
    have h := hN₀ N hN
    norm_num at h
    exact h

end RHDirect.MaynardTao

