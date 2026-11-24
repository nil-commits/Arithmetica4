import RHDirect.Stage12MultivarDwork
import RHDirect.Stage11BostDworkSqueeze
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# RHDirect.Stage14M5_GaussJetThmA

Field-2 Package M5 Wave 1: **Gauss-Jet `p`-adic Valuation Bounds, Theorem A (`ThmAGauss`),
Inert-Prime Dwork/Artin–Hasse Congruence Shifts, and Von Mangoldt Class Sum Bridge**,
built directly on `RHDirect.Stage12MultivarDwork`, `RHDirect.Stage11BostDworkSqueeze`,
and `RHDirect.PAdicChainValuation` in pure Mathlib `v4.33.1`
(0 `sorry`, 0 custom `axiom`s, 0 `opaque`, 0 `native_decide`).

## Contents

1. **Multivariate Gauss Norm, Gauss's Lemma & `GaussJetValuation` Functional**:
   - Concrete ultrametric Gauss norm `gaussNormPoly` on `MvPolynomial σ K` with finitary
     `Finset.sup'` characterization, ultrametric subadditivity, submultiplicativity, and
     **Multivariate Gauss's Lemma** (`gaussNormPoly_mul_eq`).
   - Multivariate jet pairing `jetPair P Th = ∑ κ ∈ P.support, coeff κ P * (mfact κ) * coeff κ Th`
     and differential-operator adjoint `diffOp` (`jetPair_mul_eq_diffOp`).
   - Concrete **`GaussJetValuation`** functional (`dworkVal p (jetPair P Th)`) and bundled
     `GaussJetDatum`, plus the fundamental **`norm_jetPair_le_of_wtGe`** and
     **`gaussJetValuation_ge_of_wtGe`** bounds via `PAdicChainValuation.multifactorial_norm_bound`.

2. **Inert-Prime Frobenius Orbit Constants, `topTerm`, `Wcap` & LP Flow Duality (`Fnum`)**:
   - Inert-prime constants `rho p = 1 / (p^2 - 1)` and `gam p = p / (p^2 - 1)` (`rho_add_gam`),
     and Frobenius-orbit quantities `capL`, `Dl`, `dTop`, `Wcap`, `topTerm`, `baseTerm` on `ZMod d`.
   - Inert-prime LP flow `IsInertFlow`, `maxInertFlow`, `Fnum`, weak duality
     `dual_eval_le_Fnum`, and unconditional lower bound `rho_mul_sum_le_Fnum`.
   - Finite-sum comparisons between `topTerm` and `baseTerm` (`baseTerm_le_topTerm`) and
     exact finite truncation bounds for `topTerm`.

3. **Inert-Prime Dwork / Artin–Hasse Congruence Shifts (`Stage12MultivarDwork`)**:
   - Multivariate substitution weight preservation (`wtGe_subst_of_wtGe`), Artin–Hasse
     substitution integrality (`wtGe_subst_artinHasseExp`), and Frobenius-orbit weight shift
     (`wtGe_frobSub_shift`, `wtGe_frobMapMv_shift`).
   - Concrete Dwork / Artin–Hasse congruence-shifted theta power series `dworkCongruenceTheta`
     combining `Stage12MultivarDwork.CrystallineQPack.qpack_mvExp_wtGe`,
     `Stage12MultivarDwork.multivar_dworkSplitting_wtGe`, and `Stage12MultivarDwork.dwork_lemma_mvPowerSeries`,
     together with minor-product jet norm bounds (`minorProd_gaussNormPoly_le_one`).

4. **Theorem A (`ThmAGauss`) & `thmA_gauss_inert_prime_gain`**:
   - Formal statement `ThmAGauss` and concrete bound `thmAGaussBound` for inert-prime
     Gauss-jet valuations.
   - Proved **`thmA_gauss_inert_prime_gain`** and **`thmA_gauss_dwork_congruence_gain`**:
     exact lower bound on `GaussJetValuation K p P Th` coming from Dwork/Artin–Hasse
     congruence shifts and Frobenius-orbit weights, plus `ℚ_[p]` specialization.

5. **Inert-Prime Von Mangoldt Class Sum Bridge (`vonMangoldtClassSum_le_dwork_gain`)**:
   - Concrete `vonMangoldtClassSum` (matching `Stage12MultivarDwork.vonMangoldtRamp`)
     and term-by-term comparison `vonMangoldtClassSum_le_topTerm_add_err`.
   - Proved **`vonMangoldtClassSum_le_dwork_gain`**: bounds the inert-prime von Mangoldt
     class sum by the accumulated Dwork jet valuation gain (plus explicit `loG`, `floorErr`,
     and `dropPen` error terms), plus direct compilation into `Stage12MultivarDwork.linkG_inert_ramp_shift`
     and `Stage12MultivarDwork.inert_sublattice_slope_shift_ge_ASK` (`linkG_of_thmAGauss`),
     ready for M5 Wave 2 (`Stage14M5_LinkGAndAskIsF`).
-/

open Real Finset Module
open scoped BigOperators
open RHDirect.PAdicChainValuation
open RHDirect.Stage2DworkExp
open RHDirect.Stage11BostDworkSqueeze
open RHDirect.Stage12MultivarDwork
open RHDirect.ArakelovCovolume (rk slope)

namespace RHDirect.Stage14M5_GaussJetThmA

noncomputable section

/-! ## Section 1: Multivariate Gauss Norm, Gauss's Lemma & `GaussJetValuation` -/

section GaussNormSection

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Concrete ultrametric Gauss norm on multivariate polynomials `MvPolynomial σ K`:
`‖P‖_Gauss = ⨆ n : σ →₀ ℕ, ‖coeff n P‖`. -/
def gaussNormPoly (P : MvPolynomial σ K) : ℝ :=
  ⨆ n : σ →₀ ℕ, ‖MvPolynomial.coeff n P‖

omit [IsUltrametricDist K] in
lemma gaussNormPoly_bddAbove (P : MvPolynomial σ K) :
    BddAbove (Set.range fun n : σ →₀ ℕ => ‖MvPolynomial.coeff n P‖) := by
  classical
  by_cases hP : P.support.Nonempty
  · refine ⟨P.support.sup' hP (fun n => ‖MvPolynomial.coeff n P‖), ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n ∈ P.support
    · exact Finset.le_sup' (fun m => ‖MvPolynomial.coeff m P‖) hn
    · dsimp only
      rw [MvPolynomial.notMem_support_iff.mp hn, norm_zero]
      obtain ⟨m, hm⟩ := hP
      exact (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖MvPolynomial.coeff k P‖) hm)
  · rw [Finset.not_nonempty_iff_eq_empty, MvPolynomial.support_eq_empty] at hP
    subst hP
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp

omit [IsUltrametricDist K] in
@[simp] theorem gaussNormPoly_zero : gaussNormPoly (0 : MvPolynomial σ K) = 0 := by
  unfold gaussNormPoly
  simp

omit [IsUltrametricDist K] in
theorem gaussNormPoly_nonneg (P : MvPolynomial σ K) : 0 ≤ gaussNormPoly P :=
  Real.iSup_nonneg fun _ => norm_nonneg _

omit [IsUltrametricDist K] in
theorem norm_coeff_le_gaussNormPoly (P : MvPolynomial σ K) (n : σ →₀ ℕ) :
    ‖MvPolynomial.coeff n P‖ ≤ gaussNormPoly P :=
  le_ciSup (gaussNormPoly_bddAbove P) n

omit [IsUltrametricDist K] in
theorem gaussNormPoly_le_iff {P : MvPolynomial σ K} {B : ℝ} (_hB : 0 ≤ B) :
    gaussNormPoly P ≤ B ↔ ∀ n : σ →₀ ℕ, ‖MvPolynomial.coeff n P‖ ≤ B :=
  ⟨fun h n => (norm_coeff_le_gaussNormPoly P n).trans h, fun h => ciSup_le h⟩

omit [IsUltrametricDist K] in
theorem gaussNormPoly_eq_sup' {P : MvPolynomial σ K} (hP : P ≠ 0) :
    gaussNormPoly P =
      P.support.sup' (MvPolynomial.support_nonempty.mpr hP)
        (fun n => ‖MvPolynomial.coeff n P‖) := by
  have hne : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  apply le_antisymm
  · refine ciSup_le fun n => ?_
    by_cases hn : n ∈ P.support
    · exact Finset.le_sup' (fun m => ‖MvPolynomial.coeff m P‖) hn
    · rw [MvPolynomial.notMem_support_iff.mp hn, norm_zero]
      obtain ⟨m, hm⟩ := hne
      exact (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖MvPolynomial.coeff k P‖) hm)
  · exact Finset.sup'_le hne _ fun n _ => norm_coeff_le_gaussNormPoly P n

omit [IsUltrametricDist K] in
theorem exists_coeff_norm_eq_gaussNormPoly (P : MvPolynomial σ K) :
    ∃ n : σ →₀ ℕ, ‖MvPolynomial.coeff n P‖ = gaussNormPoly P := by
  by_cases hP : P = 0
  · subst hP; exact ⟨0, by simp⟩
  · rw [gaussNormPoly_eq_sup' hP]
    obtain ⟨n, _, hn⟩ := Finset.exists_mem_eq_sup' (MvPolynomial.support_nonempty.mpr hP)
      (fun m => ‖MvPolynomial.coeff m P‖)
    exact ⟨n, hn.symm⟩

omit [IsUltrametricDist K] in
theorem gaussNormPoly_eq_zero_iff (P : MvPolynomial σ K) :
    gaussNormPoly P = 0 ↔ P = 0 := by
  constructor
  · intro h
    ext n
    have hn : ‖MvPolynomial.coeff n P‖ ≤ 0 := h ▸ norm_coeff_le_gaussNormPoly P n
    have h0 : ‖MvPolynomial.coeff n P‖ = 0 := le_antisymm hn (norm_nonneg _)
    simpa using norm_eq_zero.mp h0
  · rintro rfl; exact gaussNormPoly_zero

omit [IsUltrametricDist K] in
theorem gaussNormPoly_pos_iff (P : MvPolynomial σ K) :
    0 < gaussNormPoly P ↔ P ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_comm]
  constructor
  · rintro ⟨_, h⟩
    exact (not_iff_not.mpr (gaussNormPoly_eq_zero_iff P)).mp h
  · intro h
    exact ⟨gaussNormPoly_nonneg P, (not_iff_not.mpr (gaussNormPoly_eq_zero_iff P)).mpr h⟩

omit [IsUltrametricDist K] in
@[simp] theorem gaussNormPoly_one : gaussNormPoly (1 : MvPolynomial σ K) = 1 := by
  classical
  apply le_antisymm
  · refine (gaussNormPoly_le_iff zero_le_one).mpr fun n => ?_
    rw [MvPolynomial.coeff_one]
    split_ifs <;> simp
  · simpa using norm_coeff_le_gaussNormPoly (1 : MvPolynomial σ K) 0

omit [IsUltrametricDist K] in
@[simp] theorem gaussNormPoly_C (c : K) : gaussNormPoly (MvPolynomial.C c : MvPolynomial σ K) = ‖c‖ := by
  classical
  apply le_antisymm
  · refine (gaussNormPoly_le_iff (norm_nonneg c)).mpr fun n => ?_
    rw [MvPolynomial.coeff_C]
    split_ifs
    · exact le_rfl
    · simp [norm_nonneg c]
  · have h0 := norm_coeff_le_gaussNormPoly (MvPolynomial.C c : MvPolynomial σ K) 0
    rwa [MvPolynomial.coeff_C, if_pos rfl] at h0

omit [IsUltrametricDist K] in
@[simp] theorem gaussNormPoly_monomial (d : σ →₀ ℕ) (c : K) :
    gaussNormPoly (MvPolynomial.monomial d c) = ‖c‖ := by
  classical
  apply le_antisymm
  · refine (gaussNormPoly_le_iff (norm_nonneg c)).mpr fun n => ?_
    rw [MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  · simpa using norm_coeff_le_gaussNormPoly (MvPolynomial.monomial d c) d

omit [IsUltrametricDist K] in
@[simp] theorem gaussNormPoly_X (i : σ) :
    gaussNormPoly (MvPolynomial.X i : MvPolynomial σ K) = 1 := by
  simp [MvPolynomial.X]

omit [IsUltrametricDist K] in
@[simp] theorem gaussNormPoly_neg (P : MvPolynomial σ K) :
    gaussNormPoly (-P) = gaussNormPoly P := by
  unfold gaussNormPoly
  simp_rw [MvPolynomial.coeff_neg, norm_neg]

omit [IsUltrametricDist K] in
theorem gaussNormPoly_smul (c : K) (P : MvPolynomial σ K) :
    gaussNormPoly (c • P) = ‖c‖ * gaussNormPoly P := by
  by_cases hc : c = 0
  · subst hc; simp
  · apply le_antisymm
    · refine (gaussNormPoly_le_iff (mul_nonneg (norm_nonneg _) (gaussNormPoly_nonneg _))).mpr
        fun n => ?_
      rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_coeff_le_gaussNormPoly P n) (norm_nonneg c)
    · obtain ⟨n, hn⟩ := exists_coeff_norm_eq_gaussNormPoly P
      calc ‖c‖ * gaussNormPoly P
          = ‖c‖ * ‖MvPolynomial.coeff n P‖ := by rw [hn]
        _ = ‖MvPolynomial.coeff n (c • P)‖ := by rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul]
        _ ≤ gaussNormPoly (c • P) := norm_coeff_le_gaussNormPoly _ n

theorem gaussNormPoly_add_le_max (P Q : MvPolynomial σ K) :
    gaussNormPoly (P + Q) ≤ max (gaussNormPoly P) (gaussNormPoly Q) := by
  refine (gaussNormPoly_le_iff (le_max_of_le_left (gaussNormPoly_nonneg P))).mpr fun n => ?_
  rw [MvPolynomial.coeff_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_coeff_le_gaussNormPoly P n) (norm_coeff_le_gaussNormPoly Q n))

theorem gaussNormPoly_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ i ∈ s, gaussNormPoly (f i) ≤ B) :
    gaussNormPoly (∑ i ∈ s, f i) ≤ B := by
  refine (gaussNormPoly_le_iff hB).mpr fun n => ?_
  rw [MvPolynomial.coeff_sum]
  exact ultrametric_norm_sum_le s _ hB fun i hi =>
    (norm_coeff_le_gaussNormPoly (f i) n).trans (hf i hi)

theorem gaussNormPoly_mul_le (P Q : MvPolynomial σ K) :
    gaussNormPoly (P * Q) ≤ gaussNormPoly P * gaussNormPoly Q := by
  classical
  refine (gaussNormPoly_le_iff (mul_nonneg (gaussNormPoly_nonneg P) (gaussNormPoly_nonneg Q))).mpr
    fun n => ?_
  rw [MvPolynomial.coeff_mul]
  refine ultrametric_norm_sum_le _ _ (mul_nonneg (gaussNormPoly_nonneg P) (gaussNormPoly_nonneg Q))
    fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_coeff_le_gaussNormPoly P x.1) (norm_coeff_le_gaussNormPoly Q x.2)
    (norm_nonneg _) (gaussNormPoly_nonneg P)

theorem gaussNormPoly_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    gaussNormPoly (∏ i ∈ s, f i) ≤ ∏ i ∈ s, gaussNormPoly (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (gaussNormPoly_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (gaussNormPoly_nonneg _))

theorem gaussNormPoly_pow_le (P : MvPolynomial σ K) (k : ℕ) :
    gaussNormPoly (P ^ k) ≤ gaussNormPoly P ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (gaussNormPoly_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (gaussNormPoly_nonneg _))

/-- Elementary finite-dimensional strict lexicographical order on `Fin n → ℕ` for Gauss's Lemma. -/
private def finLexLt (n : ℕ) (a b : Fin n → ℕ) : Prop :=
  ∃ k : Fin n, (∀ j : Fin n, j < k → a j = b j) ∧ a k < b k

private lemma finLexLt_irrefl (n : ℕ) (a : Fin n → ℕ) : ¬ finLexLt n a a := by
  rintro ⟨k, _, hlt⟩
  exact Nat.lt_irrefl _ hlt

private lemma finLexLt_trans (n : ℕ) {a b c : Fin n → ℕ}
    (hab : finLexLt n a b) (hbc : finLexLt n b c) : finLexLt n a c := by
  obtain ⟨k₁, h1, hk1⟩ := hab
  obtain ⟨k₂, h2, hk2⟩ := hbc
  rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
  · refine ⟨k₁, fun j hj => (h1 j hj).trans (h2 j (hj.trans hlt)), ?_⟩
    rw [← h2 k₁ hlt]; exact hk1
  · exact ⟨k₁, fun j hj => (h1 j hj).trans (h2 j hj), hk1.trans hk2⟩
  · refine ⟨k₂, fun j hj => (h1 j (hj.trans hgt)).trans (h2 j hj), ?_⟩
    rw [h1 k₂ hgt]; exact hk2

private lemma finLexLt_trichotomy (n : ℕ) (a b : Fin n → ℕ) :
    finLexLt n a b ∨ a = b ∨ finLexLt n b a := by
  by_cases heq : a = b
  · exact Or.inr (Or.inl heq)
  · have hne : ∃ j : Fin n, a j ≠ b j := by
      by_contra h
      push Not at h
      exact heq (funext h)
    classical
    let S : Finset (Fin n) := Finset.univ.filter (fun j => a j ≠ b j)
    have hSne : S.Nonempty := by
      obtain ⟨j, hj⟩ := hne
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    let k := S.min' hSne
    have hk_mem : k ∈ S := Finset.min'_mem S hSne
    have hk_ne : a k ≠ b k := (Finset.mem_filter.mp hk_mem).2
    have hpref : ∀ j : Fin n, j < k → a j = b j := by
      intro j hj
      by_contra hjn
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjn⟩
      exact absurd (Finset.min'_le S j hjS) (not_le_of_gt hj)
    rcases lt_or_gt_of_ne hk_ne with hlt | hgt
    · exact Or.inl ⟨k, hpref, hlt⟩
    · exact Or.inr (Or.inr ⟨k, fun j hj => (hpref j hj).symm, hgt⟩)

private lemma finLexLt_add_of_le (n : ℕ) {a₁ a₂ b₁ b₂ : Fin n → ℕ}
    (ha : finLexLt n a₁ a₂) (hb : finLexLt n b₁ b₂ ∨ b₁ = b₂) :
    finLexLt n (a₁ + b₁) (a₂ + b₂) := by
  rcases hb with hb | rfl
  · obtain ⟨k₁, h1, hk1⟩ := ha
    obtain ⟨k₂, h2, hk2⟩ := hb
    rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
    · refine ⟨k₁, fun j hj => ?_, ?_⟩
      · simp only [Pi.add_apply, h1 j hj, h2 j (hj.trans hlt)]
      · simp only [Pi.add_apply, h2 k₁ hlt]; omega
    · refine ⟨k₁, fun j hj => ?_, ?_⟩
      · simp only [Pi.add_apply, h1 j hj, h2 j hj]
      · simp only [Pi.add_apply]; omega
    · refine ⟨k₂, fun j hj => ?_, ?_⟩
      · simp only [Pi.add_apply, h1 j (hj.trans hgt), h2 j hj]
      · simp only [Pi.add_apply, h1 k₂ hgt]; omega
  · obtain ⟨k₁, h1, hk1⟩ := ha
    exact ⟨k₁, fun j hj => by simp [Pi.add_apply, h1 j hj], by simp [Pi.add_apply]; omega⟩

private lemma exists_finLex_min {α : Type*} {n : ℕ} (s : Finset α) (hs : s.Nonempty)
    (f : α → (Fin n → ℕ)) (hf : Function.Injective f) :
    ∃ a₀ ∈ s, ∀ a ∈ s, a ≠ a₀ → finLexLt n (f a₀) (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨a, Finset.mem_singleton_self a, fun b hb hba => ?_⟩
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hb
      exact absurd hb hba
    · obtain ⟨a₀, ha₀s, ha₀min⟩ := ih hne
      rcases finLexLt_trichotomy n (f a) (f a₀) with hlt | heq | hgt
      · refine ⟨a, Finset.mem_insert_self a s, fun b hb hba => ?_⟩
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hbs
        · exact absurd rfl hba
        · by_cases hba₀ : b = a₀
          · subst hba₀; exact hlt
          · exact finLexLt_trans n hlt (ha₀min b hbs hba₀)
      · exfalso; apply ha; rw [hf heq]; exact ha₀s
      · refine ⟨a₀, Finset.mem_insert_of_mem ha₀s, fun b hb hba₀ => ?_⟩
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hbs
        · exact hgt
        · exact ha₀min b hbs hba₀

/-- **Multivariate Gauss's Lemma (`gaussNormPoly_mul_eq`)**:
Over ANY ultrametric normed field `K`, the Gauss norm on `MvPolynomial σ K` is multiplicative:
`‖P * Q‖_Gauss = ‖P‖_Gauss * ‖Q‖_Gauss`! -/
theorem gaussNormPoly_mul_eq (P Q : MvPolynomial σ K) :
    gaussNormPoly (P * Q) = gaussNormPoly P * gaussNormPoly Q := by
  classical
  by_cases hP : P = 0
  · subst hP; simp
  by_cases hQ : Q = 0
  · subst hQ; simp
  apply le_antisymm (gaussNormPoly_mul_le P Q)
  let S : Finset σ := (P.support ∪ Q.support).biUnion Finsupp.support
  let e : S ≃ Fin S.card := S.equivFin
  let coord : (σ →₀ ℕ) → (Fin S.card → ℕ) := fun d i => d (e.symm i).1
  have hcoord_add : ∀ d₁ d₂, coord (d₁ + d₂) = coord d₁ + coord d₂ := fun d₁ d₂ => by
    ext i; simp [coord]
  have hcoord_inj : ∀ d₁ ∈ P.support ∪ Q.support, ∀ d₂ ∈ P.support ∪ Q.support,
      coord d₁ = coord d₂ → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ heq
    ext x
    by_cases hx : x ∈ S
    · have h := congrFun heq (e ⟨x, hx⟩)
      simpa [coord] using h
    · have h1 : x ∉ d₁.support := fun hm => hx (Finset.mem_biUnion.mpr ⟨d₁, hd₁, hm⟩)
      have h2 : x ∉ d₂.support := fun hm => hx (Finset.mem_biUnion.mpr ⟨d₂, hd₂, hm⟩)
      rw [Finsupp.notMem_support_iff.mp h1, Finsupp.notMem_support_iff.mp h2]
  let MP : Finset (σ →₀ ℕ) := P.support.filter (fun m => ‖MvPolynomial.coeff m P‖ = gaussNormPoly P)
  let MQ : Finset (σ →₀ ℕ) := Q.support.filter (fun m => ‖MvPolynomial.coeff m Q‖ = gaussNormPoly Q)
  have hMP_ne : MP.Nonempty := by
    obtain ⟨m, hm⟩ := exists_coeff_norm_eq_gaussNormPoly P
    have hm_pos : 0 < ‖MvPolynomial.coeff m P‖ := by
      rw [hm]; exact (gaussNormPoly_pos_iff P).mpr hP
    exact ⟨m, Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr (norm_pos_iff.mp hm_pos), hm⟩⟩
  have hMQ_ne : MQ.Nonempty := by
    obtain ⟨m, hm⟩ := exists_coeff_norm_eq_gaussNormPoly Q
    have hm_pos : 0 < ‖MvPolynomial.coeff m Q‖ := by
      rw [hm]; exact (gaussNormPoly_pos_iff Q).mpr hQ
    exact ⟨m, Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr (norm_pos_iff.mp hm_pos), hm⟩⟩
  have hPQ_inj : ∀ a₁ ∈ P.support, ∀ a₂ ∈ P.support, coord a₁ = coord a₂ → a₁ = a₂ :=
    fun a₁ ha₁ a₂ ha₂ => hcoord_inj a₁ (Finset.mem_union_left _ ha₁) a₂ (Finset.mem_union_left _ ha₂)
  have hQQ_inj : ∀ b₁ ∈ Q.support, ∀ b₂ ∈ Q.support, coord b₁ = coord b₂ → b₁ = b₂ :=
    fun b₁ hb₁ b₂ hb₂ => hcoord_inj b₁ (Finset.mem_union_right _ hb₁) b₂ (Finset.mem_union_right _ hb₂)
  -- Pick lex-minimal maximal-norm monomials `m₀ ∈ MP` and `n₀ ∈ MQ`
  have hMP_inj : Function.Injective (fun x : MP => coord x.1) := fun x y h =>
    Subtype.ext (hPQ_inj x.1 (Finset.mem_filter.mp x.2).1 y.1 (Finset.mem_filter.mp y.2).1 h)
  have hMQ_inj : Function.Injective (fun x : MQ => coord x.1) := fun x y h =>
    Subtype.ext (hQQ_inj x.1 (Finset.mem_filter.mp x.2).1 y.1 (Finset.mem_filter.mp y.2).1 h)
  obtain ⟨⟨m₀, hm₀⟩, _, hm₀_min⟩ := exists_finLex_min (Finset.univ : Finset MP)
    (Finset.univ_nonempty_iff.mpr hMP_ne.coe_sort) (fun x : MP => coord x.1) hMP_inj
  obtain ⟨⟨n₀, hn₀⟩, _, hn₀_min⟩ := exists_finLex_min (Finset.univ : Finset MQ)
    (Finset.univ_nonempty_iff.mpr hMQ_ne.coe_sort) (fun x : MQ => coord x.1) hMQ_inj
  have hm₀_norm : ‖MvPolynomial.coeff m₀ P‖ = gaussNormPoly P := (Finset.mem_filter.mp hm₀).2
  have hn₀_norm : ‖MvPolynomial.coeff n₀ Q‖ = gaussNormPoly Q := (Finset.mem_filter.mp hn₀).2
  have hmain_norm : ‖MvPolynomial.coeff m₀ P * MvPolynomial.coeff n₀ Q‖ =
      gaussNormPoly P * gaussNormPoly Q := by
    rw [norm_mul, hm₀_norm, hn₀_norm]
  have hmain_pos : 0 < gaussNormPoly P * gaussNormPoly Q :=
    mul_pos ((gaussNormPoly_pos_iff P).mpr hP) ((gaussNormPoly_pos_iff Q).mpr hQ)
  -- Every other `(a, b) ∈ antidiagonal (m₀ + n₀)` has strictly smaller norm!
  have hother_lt : ∀ x ∈ (Finset.antidiagonal (m₀ + n₀)).erase (m₀, n₀),
      ‖MvPolynomial.coeff x.1 P * MvPolynomial.coeff x.2 Q‖ < gaussNormPoly P * gaussNormPoly Q := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_antidiagonal] at hx
    rcases hx with ⟨hne, hsum⟩
    by_cases hx1 : x.1 ∈ P.support
    swap
    · rw [MvPolynomial.notMem_support_iff.mp hx1, zero_mul, norm_zero]; exact hmain_pos
    by_cases hx2 : x.2 ∈ Q.support
    swap
    · rw [MvPolynomial.notMem_support_iff.mp hx2, mul_zero, norm_zero]; exact hmain_pos
    have h1le : ‖MvPolynomial.coeff x.1 P‖ ≤ gaussNormPoly P := norm_coeff_le_gaussNormPoly P x.1
    have h2le : ‖MvPolynomial.coeff x.2 Q‖ ≤ gaussNormPoly Q := norm_coeff_le_gaussNormPoly Q x.2
    by_cases h1eq : ‖MvPolynomial.coeff x.1 P‖ = gaussNormPoly P
    · by_cases h2eq : ‖MvPolynomial.coeff x.2 Q‖ = gaussNormPoly Q
      · exfalso
        have hx1MP : x.1 ∈ MP := Finset.mem_filter.mpr ⟨hx1, h1eq⟩
        have hx2MQ : x.2 ∈ MQ := Finset.mem_filter.mpr ⟨hx2, h2eq⟩
        have hne1 : x.1 ≠ m₀ := by
          intro h; apply hne; exact Prod.ext h (by simpa [h] using hsum)
        have hlt1 : finLexLt S.card (coord m₀) (coord x.1) :=
          hm₀_min ⟨x.1, hx1MP⟩ (Finset.mem_univ _) (by intro h; exact hne1 (congrArg Subtype.val h))
        have hle2 : finLexLt S.card (coord n₀) (coord x.2) ∨ coord n₀ = coord x.2 := by
          by_cases hne2 : x.2 = n₀
          · right; rw [hne2]
          · left; exact hn₀_min ⟨x.2, hx2MQ⟩ (Finset.mem_univ _)
              (by intro h; exact hne2 (congrArg Subtype.val h))
        have hsum_lt := finLexLt_add_of_le S.card hlt1 hle2
        rw [← hcoord_add, ← hcoord_add, hsum] at hsum_lt
        exact finLexLt_irrefl S.card _ hsum_lt
      · have h2lt : ‖MvPolynomial.coeff x.2 Q‖ < gaussNormPoly Q := lt_of_le_of_ne h2le h2eq
        rw [norm_mul, h1eq]
        exact mul_lt_mul_of_pos_left h2lt ((gaussNormPoly_pos_iff P).mpr hP)
    · have h1lt : ‖MvPolynomial.coeff x.1 P‖ < gaussNormPoly P := lt_of_le_of_ne h1le h1eq
      rw [norm_mul]
      calc ‖MvPolynomial.coeff x.1 P‖ * ‖MvPolynomial.coeff x.2 Q‖
          ≤ ‖MvPolynomial.coeff x.1 P‖ * gaussNormPoly Q :=
            mul_le_mul_of_nonneg_left h2le (norm_nonneg _)
        _ < gaussNormPoly P * gaussNormPoly Q :=
            mul_lt_mul_of_pos_right h1lt ((gaussNormPoly_pos_iff Q).mpr hQ)
  -- By the ultrametric strict-maximum principle, `‖coeff (m₀ + n₀) (P * Q)‖ = gaussNormPoly P * gaussNormPoly Q`!
  have hmem0 : (m₀, n₀) ∈ Finset.antidiagonal (m₀ + n₀) := Finset.mem_antidiagonal.mpr rfl
  have hrest : ‖∑ x ∈ (Finset.antidiagonal (m₀ + n₀)).erase (m₀, n₀),
      MvPolynomial.coeff x.1 P * MvPolynomial.coeff x.2 Q‖ < gaussNormPoly P * gaussNormPoly Q := by
    set R := (Finset.antidiagonal (m₀ + n₀)).erase (m₀, n₀)
    rcases R.eq_empty_or_nonempty with hR | hR
    · rw [hR, Finset.sum_empty, norm_zero]; exact hmain_pos
    · have hmax : ∃ y ∈ R, ∀ z ∈ R,
          ‖MvPolynomial.coeff z.1 P * MvPolynomial.coeff z.2 Q‖ ≤
            ‖MvPolynomial.coeff y.1 P * MvPolynomial.coeff y.2 Q‖ := by
        obtain ⟨y, hy, hy_eq⟩ := Finset.exists_mem_eq_sup' hR
          (fun z => ‖MvPolynomial.coeff z.1 P * MvPolynomial.coeff z.2 Q‖)
        exact ⟨y, hy, fun z hz => hy_eq ▸ Finset.le_sup'
          (fun z : (σ →₀ ℕ) × (σ →₀ ℕ) => ‖MvPolynomial.coeff z.1 P * MvPolynomial.coeff z.2 Q‖) hz⟩
      obtain ⟨y, hy, hy_max⟩ := hmax
      exact (ultrametric_norm_sum_le R _ (norm_nonneg _) fun z hz => hy_max z hz).trans_lt
        (hother_lt y hy)
  have hcoeff_eq : MvPolynomial.coeff (m₀ + n₀) (P * Q) =
      MvPolynomial.coeff m₀ P * MvPolynomial.coeff n₀ Q +
        ∑ x ∈ (Finset.antidiagonal (m₀ + n₀)).erase (m₀, n₀),
          MvPolynomial.coeff x.1 P * MvPolynomial.coeff x.2 Q := by
    rw [MvPolynomial.coeff_mul, ← Finset.add_sum_erase (Finset.antidiagonal (m₀ + n₀))
      (fun x => MvPolynomial.coeff x.1 P * MvPolynomial.coeff x.2 Q) hmem0]
  have hnorm_eq : ‖MvPolynomial.coeff (m₀ + n₀) (P * Q)‖ = gaussNormPoly P * gaussNormPoly Q := by
    rw [hcoeff_eq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hmain_norm]; exact hrest.ne')]
    rw [hmain_norm, max_eq_left hrest.le]
  exact hnorm_eq ▸ norm_coeff_le_gaussNormPoly (P * Q) (m₀ + n₀)

end GaussNormSection

/-! ### Multivariable Jet Pairing `jetPair`, Differential Adjoint `diffOp`, & `GaussJetValuation` -/

section JetPairingAndValuation

variable {σ K : Type*}

/-- Multivariable jet pairing of a polynomial `P : MvPolynomial σ K` with a power series
`Th : MvPowerSeries σ K`: `⟨P, Th⟩_jet = ∑ κ ∈ P.support, coeff κ P * (κ!) * coeff κ Th`. -/
def jetPair [CommSemiring K] (P : MvPolynomial σ K) (Th : MvPowerSeries σ K) : K :=
  ∑ κ ∈ P.support, MvPolynomial.coeff κ P * ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th

section JetAlgebra

variable [CommRing K]

lemma jetPair_eq_sum_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (hs : P.support ⊆ s) (Th : MvPowerSeries σ K) :
    jetPair P Th = ∑ κ ∈ s, MvPolynomial.coeff κ P * ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th := by
  unfold jetPair
  refine Finset.sum_subset hs fun κ _ hκ => ?_
  rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul, zero_mul]

@[simp] theorem jetPair_zero_left (Th : MvPowerSeries σ K) :
    jetPair (0 : MvPolynomial σ K) Th = 0 := by
  simp [jetPair]

@[simp] theorem jetPair_zero_right (P : MvPolynomial σ K) :
    jetPair P (0 : MvPowerSeries σ K) = 0 := by
  simp [jetPair]

@[simp] theorem jetPair_one_left (Th : MvPowerSeries σ K) :
    jetPair (1 : MvPolynomial σ K) Th = MvPowerSeries.constantCoeff Th := by
  classical
  have h1 : (1 : MvPolynomial σ K).support ⊆ {0} := by
    intro κ hκ
    rw [Finset.mem_singleton]
    by_contra hne
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hκ
    exact hκ rfl
  rw [jetPair_eq_sum_subset h1 Th]
  simp [mfact]

@[simp] theorem jetPair_monomial_left (d : σ →₀ ℕ) (c : K) (Th : MvPowerSeries σ K) :
    jetPair (MvPolynomial.monomial d c) Th = c * ((mfact d : ℕ) : K) * MvPowerSeries.coeff d Th := by
  classical
  rw [jetPair_eq_sum_subset (MvPolynomial.support_monomial_subset) Th]
  simp

theorem jetPair_add_left (P₁ P₂ : MvPolynomial σ K) (Th : MvPowerSeries σ K) :
    jetPair (P₁ + P₂) Th = jetPair P₁ Th + jetPair P₂ Th := by
  classical
  rw [jetPair_eq_sum_subset MvPolynomial.support_add Th,
    jetPair_eq_sum_subset Finset.subset_union_left Th,
    jetPair_eq_sum_subset Finset.subset_union_right Th,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem jetPair_add_right (P : MvPolynomial σ K) (Th₁ Th₂ : MvPowerSeries σ K) :
    jetPair P (Th₁ + Th₂) = jetPair P Th₁ + jetPair P Th₂ := by
  unfold jetPair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [map_add]
  ring

theorem jetPair_smul_left (c : K) (P : MvPolynomial σ K) (Th : MvPowerSeries σ K) :
    jetPair (c • P) Th = c * jetPair P Th := by
  classical
  have hs : (c • P).support ⊆ P.support := by
    intro κ hκ
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, smul_eq_mul] at hκ
    exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hκ)
  rw [jetPair_eq_sum_subset hs Th, jetPair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem jetPair_smul_right (c : K) (P : MvPolynomial σ K) (Th : MvPowerSeries σ K) :
    jetPair P (c • Th) = c * jetPair P Th := by
  unfold jetPair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MvPowerSeries.coeff_smul]
  ring

end JetAlgebra

/-- Differential-operator adjoint `diffOp R P` on `MvPolynomial σ K` satisfying
`jetPair P (R * G) = jetPair (diffOp R P) G`. -/
def diffOp [Field K] (R P : MvPolynomial σ K) : MvPolynomial σ K :=
  open Classical in
  ∑ m ∈ R.support, ∑ a ∈ P.support,
    if m ≤ a then
      MvPolynomial.monomial (a - m)
        (MvPolynomial.coeff m R * MvPolynomial.coeff a P * ((mfact a : K) / (mfact (a - m) : K)))
    else 0

lemma mfact_ne_zero [Field K] [CharZero K] (κ : σ →₀ ℕ) : ((mfact κ : ℕ) : K) ≠ 0 := by
  rw [Nat.cast_ne_zero, mfact, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _

/-- **Jet Adjointness (`jetPair_mul_eq_diffOp`)**:
multiplying a power series `G` by a polynomial `R` is adjoint under `jetPair` to applying `diffOp R`. -/
theorem jetPair_mul_eq_diffOp [Field K] [CharZero K]
    (P R : MvPolynomial σ K) (G : MvPowerSeries σ K) :
    jetPair P ((R : MvPowerSeries σ K) * G) = jetPair (diffOp R P) G := by
  classical
  have hsum : ∀ (s : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → MvPolynomial σ K),
      jetPair (∑ x ∈ s, f x) G = ∑ x ∈ s, jetPair (f x) G := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jetPair_add_left, ih]
  rw [diffOp, hsum]
  simp_rw [hsum]
  have hRHS : ∑ m ∈ R.support, ∑ a ∈ P.support,
      jetPair (if m ≤ a then MvPolynomial.monomial (a - m)
        (MvPolynomial.coeff m R * MvPolynomial.coeff a P * ((mfact a : K) / (mfact (a - m) : K)))
        else 0) G =
      ∑ a ∈ P.support, MvPolynomial.coeff a P * ((mfact a : ℕ) : K) *
        (∑ m ∈ R.support, if m ≤ a then MvPolynomial.coeff m R * MvPowerSeries.coeff (a - m) G else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hma
    · rw [jetPair_monomial_left]
      have hne := mfact_ne_zero (K := K) (a - m)
      field_simp [hne]
    · simp
  rw [hRHS]
  unfold jetPair
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [MvPowerSeries.coeff_mul]
  have hsplit : ∑ x ∈ Finset.antidiagonal a,
      MvPolynomial.coeff x.1 R * MvPowerSeries.coeff x.2 G =
      ∑ m ∈ R.support, if m ≤ a then MvPolynomial.coeff m R * MvPowerSeries.coeff (a - m) G else 0 := by
    rw [← Finset.sum_filter_of_ne (p := fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => x.1 ∈ R.support)
      (fun x _ hx => by
        by_contra hn
        apply hx
        rw [MvPolynomial.notMem_support_iff.mp hn, zero_mul])]
    symm
    rw [← Finset.sum_filter_of_ne (p := fun m : σ →₀ ℕ => m ≤ a)
      (fun m _ hm => by by_contra hn; apply hm; rw [if_neg hn])]
    refine Finset.sum_bij (fun m _ => (m, a - m)) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter] at hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (add_tsub_cancel_of_le hm.2), hm.1⟩
    · intro m₁ _ m₂ _ h
      exact congrArg Prod.fst h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
      refine ⟨x.1, Finset.mem_filter.mpr ⟨hx.2, hx.1 ▸ le_self_add⟩, ?_⟩
      ext <;> simp [← hx.1]
    · intro m hm
      simp only [Finset.mem_filter] at hm
      rw [if_pos hm.2]
  exact hsplit

/-- **Concrete Gauss-Jet `p`-Adic Valuation Functional (`GaussJetValuation`)**:
real-valued `p`-adic valuation `v_p(⟨P, Th⟩_jet) = log ‖jetPair P Th‖ / log ‖(p : K)‖`
on multivariable polynomial/power-series jets over an ultrametric field `K`. -/
def GaussJetValuation (K : Type*) [NormedField K] (p : ℕ) {σ : Type*}
    (P : MvPolynomial σ K) (Th : MvPowerSeries σ K) : ℝ :=
  dworkVal p (jetPair P Th)

theorem gaussJetValuation_eq_dworkVal (K : Type*) [NormedField K] (p : ℕ) {σ : Type*}
    (P : MvPolynomial σ K) (Th : MvPowerSeries σ K) :
    GaussJetValuation K p P Th = dworkVal p (jetPair P Th) := rfl

theorem gaussJetValuation_ge_iff_norm_le [NormedField K] [CharZero K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {P : MvPolynomial σ K} {Th : MvPowerSeries σ K}
    (hne : jetPair P Th ≠ 0) (w : ℝ) :
    w ≤ GaussJetValuation K p P Th ↔ ‖jetPair P Th‖ ≤ ‖(p : K)‖ ^ w := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hlog_neg : Real.log ‖(p : K)‖ < 0 := log_norm_prime_neg hp hlt
  have hnorm_pos : 0 < ‖jetPair P Th‖ := norm_pos_iff.mpr hne
  unfold GaussJetValuation dworkVal
  rw [le_div_iff_of_neg hlog_neg, ← Real.log_rpow hpi0]
  exact Real.log_le_log_iff hnorm_pos (Real.rpow_pos_of_pos hpi0 w)

/-- Bundled Gauss-jet datum recording the polynomial jet `P`, power series `Th`, radius profile `r`,
degree ceiling `a`, and concrete valuation functional. -/
structure GaussJetDatum (K : Type*) [NormedField K] (p d N0 N1 : ℕ) (σ : Type*) where
  P : MvPolynomial σ K
  Th : MvPowerSeries σ K
  r : σ → ℝ
  a : ℕ
  a_pos : 1 ≤ a
  deg_le : ∀ κ ∈ P.support, κ.degree ≤ a

def GaussJetDatum.val {K : Type*} [NormedField K] {p d N0 N1 : ℕ} {σ : Type*}
    (J : GaussJetDatum K p d N0 N1 σ) : ℝ :=
  GaussJetValuation K p J.P J.Th

section JetBounds

variable [NormedField K] [IsUltrametricDist K] [CharZero K]

/-- **Core Gauss-Jet Ultrametric Norm Bound (`norm_jetPair_le_of_wtGe`)**:
If every monomial `κ ∈ P.support` satisfies `‖coeff κ P‖ ≤ ‖(p : K)‖ ^ wP`, `κ.degree ≤ a` (`1 ≤ a`),
and `(∑ i, (κ i : ℝ) / (p - 1)) - wtDot κ r ≥ wShift`, while `Th` satisfies `WtGe ‖(p : K)‖ r wTh Th`,
then `‖jetPair P Th‖ ≤ ‖(p : K)‖ ^ (wP + wTh + wShift - |σ| * (log_p a + 1))`! -/
theorem norm_jetPair_le_of_wtGe [Fintype σ] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {r : σ → ℝ} {P : MvPolynomial σ K} {Th : MvPowerSeries σ K}
    {a : ℕ} (ha : 1 ≤ a) {wP wTh wShift : ℝ}
    (hP_norm : ∀ κ ∈ P.support, ‖MvPolynomial.coeff κ P‖ ≤ ‖(p : K)‖ ^ wP)
    (hP_deg : ∀ κ ∈ P.support, κ.degree ≤ a)
    (hTh : WtGe ‖(p : K)‖ r wTh Th)
    (hShift : ∀ κ ∈ P.support, wShift ≤ (∑ i : σ, (κ i : ℝ) / ((p : ℝ) - 1)) - wtDot κ r) :
    ‖jetPair P Th‖ ≤
      ‖(p : K)‖ ^ (wP + wTh + wShift - (Fintype.card σ : ℝ) * (Real.logb p (a : ℝ) + 1)) := by
  have hl1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  set E := wP + wTh + wShift - (Fintype.card σ : ℝ) * (Real.logb p (a : ℝ) + 1)
  unfold jetPair
  refine ultrametric_norm_sum_le P.support _ (Real.rpow_nonneg hpi0.le E) fun κ hκ => ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖MvPolynomial.coeff κ P‖ ≤ ‖(p : K)‖ ^ wP := hP_norm κ hκ
  have h2 := multifactorial_norm_bound (K := K) hp hlt κ
  have h3 : ‖MvPowerSeries.coeff κ Th‖ ≤ ‖(p : K)‖ ^ (wTh - wtDot κ r) := hTh κ
  have hdeg : (κ.degree : ℝ) ≤ (a : ℝ) := by exact_mod_cast hP_deg κ hκ
  have hlog : Real.logb p (κ.degree : ℝ) ≤ Real.logb p (a : ℝ) := by
    rcases Nat.eq_zero_or_pos κ.degree with hd0 | hdpos
    · rw [hd0, Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg hl1 (by exact_mod_cast ha)
    · exact Real.logb_le_logb_of_le hl1 (by exact_mod_cast hdpos) hdeg
  have h2' : ‖((mfact κ : ℕ) : K)‖ ≤
      ‖(p : K)‖ ^ ((∑ i : σ, (κ i : ℝ) / ((p : ℝ) - 1)) -
        (Fintype.card σ : ℝ) * (Real.logb p (a : ℝ) + 1)) := by
    refine h2.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le ?_)
    have hcard : (0 : ℝ) ≤ (Fintype.card σ : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc ‖MvPolynomial.coeff κ P‖ * ‖((mfact κ : ℕ) : K)‖ * ‖MvPowerSeries.coeff κ Th‖
      ≤ ‖(p : K)‖ ^ wP *
          ‖(p : K)‖ ^ ((∑ i : σ, (κ i : ℝ) / ((p : ℝ) - 1)) -
            (Fintype.card σ : ℝ) * (Real.logb p (a : ℝ) + 1)) *
          ‖(p : K)‖ ^ (wTh - wtDot κ r) := by
        refine mul_le_mul (mul_le_mul h1 h2' (norm_nonneg _) (Real.rpow_nonneg hpi0.le _))
          h3 (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hpi0.le _) (Real.rpow_nonneg hpi0.le _))
    _ = ‖(p : K)‖ ^ (wP + ((∑ i : σ, (κ i : ℝ) / ((p : ℝ) - 1)) -
          (Fintype.card σ : ℝ) * (Real.logb p (a : ℝ) + 1)) + (wTh - wtDot κ r)) := by
        rw [← Real.rpow_add hpi0, ← Real.rpow_add hpi0]
    _ ≤ ‖(p : K)‖ ^ E := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        have hs := hShift κ hκ
        linarith

/-- Corollary in terms of `GaussJetValuation`: when `jetPair P Th ≠ 0`, `GaussJetValuation` is bounded
below by `wP + wTh + wShift - |σ| * (log_p a + 1)`. -/
theorem gaussJetValuation_ge_of_wtGe [Fintype σ] {p : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {r : σ → ℝ} {P : MvPolynomial σ K} {Th : MvPowerSeries σ K}
    {a : ℕ} (ha : 1 ≤ a) {wP wTh wShift : ℝ}
    (hP_norm : ∀ κ ∈ P.support, ‖MvPolynomial.coeff κ P‖ ≤ ‖(p : K)‖ ^ wP)
    (hP_deg : ∀ κ ∈ P.support, κ.degree ≤ a)
    (hTh : WtGe ‖(p : K)‖ r wTh Th)
    (hShift : ∀ κ ∈ P.support, wShift ≤ (∑ i : σ, (κ i : ℝ) / ((p : ℝ) - 1)) - wtDot κ r)
    (hne : jetPair P Th ≠ 0) :
    wP + wTh + wShift - (Fintype.card σ : ℝ) * (Real.logb p (a : ℝ) + 1) ≤
      GaussJetValuation K p P Th :=
  (gaussJetValuation_ge_iff_norm_le hp hlt hne _).mpr
    (norm_jetPair_le_of_wtGe hp hlt ha hP_norm hP_deg hTh hShift)

/-- Specialized `GaussJetDatum` valuation lower bound when `P` has integral coefficients (`wP = 0`). -/
theorem gaussJetDatum_val_ge [Fintype σ] {p d N0 N1 : ℕ} (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (J : GaussJetDatum K p d N0 N1 σ) {wTh wShift : ℝ}
    (hP_int : gaussNormPoly J.P ≤ 1)
    (hTh : WtGe ‖(p : K)‖ J.r wTh J.Th)
    (hShift : ∀ κ ∈ J.P.support, wShift ≤ (∑ i : σ, (κ i : ℝ) / ((p : ℝ) - 1)) - wtDot κ J.r)
    (hne : jetPair J.P J.Th ≠ 0) :
    wTh + wShift - (Fintype.card σ : ℝ) * (Real.logb p (J.a : ℝ) + 1) ≤ J.val := by
  have hP0 : ∀ κ ∈ J.P.support, ‖MvPolynomial.coeff κ J.P‖ ≤ ‖(p : K)‖ ^ (0 : ℝ) := fun κ _ => by
    rw [Real.rpow_zero]
    exact (norm_coeff_le_gaussNormPoly J.P κ).trans hP_int
  simpa [GaussJetDatum.val, zero_add] using
    gaussJetValuation_ge_of_wtGe hp hlt J.a_pos hP0 J.deg_le hTh hShift hne

end JetBounds

end JetPairingAndValuation

/-! ## Section 2: Inert-Prime Frobenius Orbit Constants, `topTerm`, `Wcap` & LP Flow (`Fnum`) -/

section InertOrbitLP

/-- Inert-prime Dwork radius parameter `ρ(p) = 1 / (p^2 - 1)`. -/
def rho (p : ℕ) : ℝ := 1 / ((p : ℝ) ^ 2 - 1)

/-- Inert-prime Frobenius-orbit gain parameter `γ(p) = p / (p^2 - 1)`. -/
def gam (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) ^ 2 - 1)

theorem rho_pos {p : ℕ} (hp : 2 ≤ p) : 0 < rho p := by
  unfold rho
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  exact div_pos one_pos hden

theorem gam_pos {p : ℕ} (hp : 2 ≤ p) : 0 < gam p := by
  unfold gam
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  exact div_pos (by linarith) hden

theorem gam_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ gam p := (gam_pos hp).le

theorem rho_add_gam {p : ℕ} (hp : 2 ≤ p) : rho p + gam p = 1 / ((p : ℝ) - 1) := by
  unfold rho gam
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp [h1, h2]
  ring

theorem gam_le_nine_div_eight_mul {p : ℕ} (hp : 3 ≤ p) : gam p ≤ 9 / (8 * (p : ℝ)) := by
  unfold gam
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- Odd Frobenius shift levels strictly below `d`. -/
def oddLevels (d : ℕ) : Finset ℕ := (Finset.range d).filter Odd

section FlowAndDual

variable (l d : ℕ) [NeZero d]

/-- Feasible inert-prime LP flow `x : ZMod d → ℕ → ℝ` for degree budget `D : ZMod d → ℝ`. -/
def IsInertFlow (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) : Prop :=
  (∀ s i, 0 ≤ x s i) ∧
    ∀ s : ZMod d, (∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i) ≤ D s

/-- Total flow value `∑_{s, i ∈ oddLevels d} x s i`. -/
def flowVal (x : ZMod d → ℕ → ℝ) : ℝ := ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i

/-- Maximum achievable inert-prime LP flow `maxInertFlow l d D`. -/
def maxInertFlow (D : ZMod d → ℝ) : ℝ :=
  sSup {t : ℝ | ∃ x, IsInertFlow l d D x ∧ flowVal d x = t}

/-- Inert-prime LP residual gain `Fnum l d D = γ(l) * ∑ s, D s - maxInertFlow l d D`. -/
def Fnum (D : ZMod d → ℝ) : ℝ := gam l * (∑ s : ZMod d, D s) - maxInertFlow l d D

/-- Dual feasibility on `ZMod d`: `0 ≤ sig s ≤ 1` and `1 ≤ l^i sig s + sig (s + i)` for `i ∈ oddLevels d`. -/
def IsInertDual (sig : ZMod d → ℝ) : Prop :=
  (∀ s, 0 ≤ sig s ∧ sig s ≤ 1) ∧
    ∀ s : ZMod d, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))

/-- **Weak LP Duality (`flowVal_le_dual_eval`)**:
for any feasible flow `x` and dual weight `sig`, `flowVal d x ≤ ∑ s, D s * sig s`. -/
theorem flowVal_le_dual_eval {D sig : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ}
    (hx : IsInertFlow l d D x) (hsig : IsInertDual l d sig) :
    flowVal d x ≤ ∑ s : ZMod d, D s * sig s := by
  have hx_nn := hx.1
  have h1 : flowVal d x ≤
      ∑ s : ZMod d, ∑ i ∈ oddLevels d,
        x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) := by
    unfold flowVal
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i hi => ?_
    exact le_mul_of_one_le_right (hx_nn s i) (hsig.2 s i hi)
  have hshift : ∀ i : ℕ,
      (∑ s : ZMod d, x s i * sig (s + (i : ZMod d))) =
        ∑ s : ZMod d, x (s - (i : ZMod d)) i * sig s := fun i => by
    refine Fintype.sum_equiv (Equiv.addRight (i : ZMod d)) _ _ fun s => ?_
    simp [add_sub_cancel_right]
  have h2 : (∑ s : ZMod d, ∑ i ∈ oddLevels d,
      x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)))) =
      ∑ s : ZMod d,
        ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
          (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i)) * sig s := by
    simp_rw [mul_add, Finset.sum_add_distrib, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.sum_comm]
      have hcomm : ∑ s : ZMod d, (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i) * sig s =
          ∑ i ∈ oddLevels d, ∑ s : ZMod d, x (s - (i : ZMod d)) i * sig s := by
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
      rw [hcomm]
      refine Finset.sum_congr rfl fun i _ => hshift i
  have h3 : (∑ s : ZMod d,
      ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
        (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i)) * sig s) ≤
      ∑ s : ZMod d, D s * sig s := by
    refine Finset.sum_le_sum fun s _ => ?_
    exact mul_le_mul_of_nonneg_right (hx.2 s) (hsig.1 s).1
  linarith

omit [NeZero d] in
theorem flow_zero_feasible {D : ZMod d → ℝ} (hD : ∀ s, 0 ≤ D s) :
    IsInertFlow l d D (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩

theorem bddAbove_flowVal {D : ZMod d → ℝ} (_hD : ∀ s, 0 ≤ D s) :
    BddAbove {t : ℝ | ∃ x, IsInertFlow l d D x ∧ flowVal d x = t} := by
  refine ⟨∑ s : ZMod d, D s, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hsig1 : IsInertDual l d (fun _ => 1) := by
    refine ⟨fun _ => ⟨zero_le_one, le_rfl⟩, fun s i _ => ?_⟩
    have hpow : 0 ≤ (l : ℝ) ^ i := pow_nonneg (Nat.cast_nonneg l) i
    linarith
  simpa using flowVal_le_dual_eval l d hx hsig1

theorem zero_le_maxInertFlow {D : ZMod d → ℝ} (hD : ∀ s, 0 ≤ D s) :
    0 ≤ maxInertFlow l d D := by
  apply le_csSup (bddAbove_flowVal l d hD)
  exact ⟨fun _ _ => 0, flow_zero_feasible l d hD, by unfold flowVal; simp⟩

/-- **Weak Duality Lower Bound for `Fnum`**: for ANY dual `sig` (`IsInertDual l d sig`),
`∑ s, D s * (γ(l) - sig s) ≤ Fnum l d D`! -/
theorem dual_eval_le_Fnum {D sig : ZMod d → ℝ} (hD : ∀ s, 0 ≤ D s)
    (hsig : IsInertDual l d sig) :
    ∑ s : ZMod d, D s * (gam l - sig s) ≤ Fnum l d D := by
  have hsup : maxInertFlow l d D ≤ ∑ s : ZMod d, D s * sig s := by
    refine csSup_le ⟨0, fun _ _ => 0, flow_zero_feasible l d hD, by unfold flowVal; simp⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact flowVal_le_dual_eval l d hx hsig
  unfold Fnum
  have hsum_eq : ∑ s : ZMod d, D s * (gam l - sig s) =
      gam l * (∑ s : ZMod d, D s) - ∑ s : ZMod d, D s * sig s := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, mul_comm _ (gam l)]
  linarith

/-- **Unconditional Uniform Lower Bound on `Fnum`**:
For ALL `l ≥ 2` and `0 ≤ D`, `ρ(l) * ∑ s, D s ≤ Fnum l d D` (witnessed by constant dual `1 / (l + 1)`!). -/
theorem rho_mul_sum_le_Fnum (hl : 2 ≤ l) {D : ZMod d → ℝ} (hD : ∀ s, 0 ≤ D s) :
    rho l * (∑ s : ZMod d, D s) ≤ Fnum l d D := by
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hden : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  let sig : ZMod d → ℝ := fun _ => 1 / ((l : ℝ) + 1)
  have hsig : IsInertDual l d sig := by
    refine ⟨fun _ => ⟨div_nonneg zero_le_one hden.le, div_le_one_of_le₀ (by linarith) hden.le⟩,
      fun s i hi => ?_⟩
    have hi_odd : Odd i := (Finset.mem_filter.mp hi).2
    have hi1 : 1 ≤ i := hi_odd.pos
    have hl_le_pow : (l : ℝ) ≤ (l : ℝ) ^ i := by
      calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi1
    show 1 ≤ (l : ℝ) ^ i * (1 / ((l : ℝ) + 1)) + 1 / ((l : ℝ) + 1)
    rw [← add_one_mul, mul_one_div, one_le_div hden]
    linarith
  have hdual := dual_eval_le_Fnum l d hD hsig
  have heq : ∑ s : ZMod d, D s * (gam l - sig s) = rho l * (∑ s : ZMod d, D s) := by
    have hdiff : gam l - (1 / ((l : ℝ) + 1)) = rho l := by
      unfold gam rho
      have h1 : (l : ℝ) + 1 ≠ 0 := hden.ne'
      have h2 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp [h1, h2]
      ring
    simp_rw [show ∀ s, D s * (gam l - sig s) = rho l * D s from fun s => by
      dsimp only [sig]; rw [hdiff, mul_comm]]
    rw [← Finset.mul_sum]
  rwa [← heq]

theorem Fnum_nonneg (hl : 2 ≤ l) {D : ZMod d → ℝ} (hD : ∀ s, 0 ≤ D s) :
    0 ≤ Fnum l d D :=
  (mul_nonneg (rho_pos hl).le (Finset.sum_nonneg fun s _ => hD s)).trans
    (rho_mul_sum_le_Fnum l d hl hD)

theorem Fnum_le_gam_mul_sum {D : ZMod d → ℝ} (hD : ∀ s, 0 ≤ D s) :
    Fnum l d D ≤ gam l * (∑ s : ZMod d, D s) := by
  unfold Fnum
  linarith [zero_le_maxInertFlow l d hD]

end FlowAndDual

section TopTermData

variable (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)

/-- Inert-prime level capacity `capL s = if s ∈ TT then nu2 s else nu1 s`. -/
def capL (s : ZMod d) : ℕ := if s ∈ TT then nu2 s else nu1 s

/-- Residual LP degree budget `Dl s = if s ∈ TT then size s - nu1 s else size s`. -/
def Dl (s : ZMod d) : ℕ := if s ∈ TT then size s - nu1 s else size s

/-- Minimal odd shift hitting `TT`: `dTop s = ⨅ (e : ℕ) (_ : Odd e ∧ s + e ∈ TT), e`. -/
def dTop (s : ZMod d) : ℕ∞ := ⨅ (e : ℕ) (_ : Odd e ∧ s + (e : ZMod d) ∈ TT), (e : ℕ∞)

/-- Maximal incoming capacity `Wcap s` along odd shifts `l^i ≤ size (s - i)`. -/
def Wcap (s : ZMod d) : ℕ :=
  sSup ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) ''
    {i : ℕ | Odd i ∧ l ^ i ≤ size (s - (i : ZMod d))})

/-- Inert-prime top-row Dwork valuation gain `topTerm l d TT nu1 nu2 s`. -/
def topTerm (s : ZMod d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ (e : ℕ∞) < dTop d TT s then
      max ((nu1 s : ℝ) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
    else if Odd e ∧ dTop d TT s < (e : ℕ∞) then (nu1 s : ℝ) / (l : ℝ) ^ e
    else 0

/-- Base-row inert-prime gain `baseTerm l d TT nu1 nu2 s`. -/
def baseTerm (s : ZMod d) : ℝ :=
  open Classical in
  ∑' e : ℕ,
    if Odd e ∧ ¬ (∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d)) then
      max (((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
    else 0

omit [NeZero d] in
theorem topTerm_summable (hl : 2 ≤ l) (s : ZMod d) :
    Summable (fun e : ℕ =>
      if Odd e ∧ (e : ℕ∞) < dTop d TT s then
        max ((nu1 s : ℝ) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
      else if Odd e ∧ dTop d TT s < (e : ℕ∞) then (nu1 s : ℝ) / (l : ℝ) ^ e
      else 0) := by
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hgeom : Summable (fun e : ℕ => (nu1 s : ℝ) / (l : ℝ) ^ e) := by
    have h := summable_geometric_of_lt_one (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ l))
      (inv_lt_one_of_one_lt₀ (by linarith))
    simpa [div_eq_mul_inv, inv_pow] using h.mul_left (nu1 s : ℝ)
  refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hgeom
  · split_ifs
    · exact le_max_right _ _
    · exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg l) e)
    · exact le_rfl
  · have hA : 0 ≤ (nu1 s : ℝ) / (l : ℝ) ^ e :=
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg l) e)
    have hcap : (0 : ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    split_ifs
    · exact max_le (by linarith) hA
    · exact le_rfl
    · exact hA

omit [NeZero d] in
theorem topTerm_nonneg (s : ZMod d) : 0 ≤ topTerm l d TT nu1 nu2 s := by
  unfold topTerm
  refine tsum_nonneg fun e => ?_
  split_ifs
  · exact le_max_right _ _
  · exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg l) e)
  · exact le_rfl

omit [NeZero d] in
/-- **`baseTerm_le_topTerm`**: at every residue `s : ZMod d`, `baseTerm ≤ topTerm`. -/
theorem baseTerm_le_topTerm (hl : 2 ≤ l) (s : ZMod d) :
    baseTerm l d TT nu1 nu2 s ≤ topTerm l d TT nu1 nu2 s := by
  classical
  have htop_sum := topTerm_summable l d TT nu1 nu2 hl s
  have hbase_le : ∀ e : ℕ,
      (if Odd e ∧ ¬ (∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d)) then
        max (((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
      else 0) ≤
      (if Odd e ∧ (e : ℕ∞) < dTop d TT s then
        max ((nu1 s : ℝ) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
      else if Odd e ∧ dTop d TT s < (e : ℕ∞) then (nu1 s : ℝ) / (l : ℝ) ^ e
      else 0) := by
    intro e
    have hpe : (0 : ℝ) < (l : ℝ) ^ e := pow_pos (by exact_mod_cast (by omega : 0 < l)) e
    have hnu2 : 0 ≤ (nu2 s : ℝ) / (l : ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hA : 0 ≤ (nu1 s : ℝ) / (l : ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hsub : ((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e =
        (nu1 s : ℝ) / (l : ℝ) ^ e - (nu2 s : ℝ) / (l : ℝ) ^ e := sub_div _ _ _
    by_cases ho : Odd e
    swap
    · simp [ho]
    rcases lt_trichotomy (e : ℕ∞) (dTop d TT s) with hlt | heq | hgt
    · rw [if_pos (show Odd e ∧ (e : ℕ∞) < dTop d TT s from ⟨ho, hlt⟩)]
      split_ifs
      · exact max_le_max (by rw [hsub]; linarith) le_rfl
      · exact le_max_right _ _
    · have hP : ∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d) :=
        ⟨e, heq.symm, rfl⟩
      rw [if_neg (show ¬ (Odd e ∧ ¬ (∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d))) from
          fun h => h.2 hP),
        if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => lt_irrefl _ (heq ▸ h.2)),
        if_neg (show ¬ (Odd e ∧ dTop d TT s < (e : ℕ∞)) from fun h => lt_irrefl _ (heq ▸ h.2))]
    · rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => not_lt.mpr hgt.le h.2),
        if_pos (show Odd e ∧ dTop d TT s < (e : ℕ∞) from ⟨ho, hgt⟩)]
      split_ifs
      · exact max_le (by rw [hsub]; linarith) hA
      · exact hA
  have hbase_sum : Summable (fun e : ℕ =>
      if Odd e ∧ ¬ (∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d)) then
        max (((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
      else 0) :=
    Summable.of_nonneg_of_le (fun e => by split_ifs <;> [exact le_max_right _ _; exact le_rfl])
      hbase_le htop_sum
  exact hbase_sum.tsum_le_tsum hbase_le htop_sum

omit [NeZero d] in
/-- Partial finite sum of `topTerm` over `Finset.range N` is bounded by `topTerm`. -/
theorem sum_range_le_topTerm (hl : 2 ≤ l) (N : ℕ) (s : ZMod d) :
    (∑ e ∈ Finset.range N,
      if Odd e ∧ (e : ℕ∞) < dTop d TT s then
        max ((nu1 s : ℝ) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
      else if Odd e ∧ dTop d TT s < (e : ℕ∞) then (nu1 s : ℝ) / (l : ℝ) ^ e
      else 0) ≤ topTerm l d TT nu1 nu2 s := by
  refine Summable.sum_le_tsum (Finset.range N) (fun e _ => ?_) (topTerm_summable l d TT nu1 nu2 hl s)
  split_ifs
  · exact le_max_right _ _
  · exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg l) e)
  · exact le_rfl

end TopTermData

end InertOrbitLP

/-! ## Section 3: Inert-Prime Dwork / Artin–Hasse Congruence Shifts (`Stage12MultivarDwork`) -/

section DworkCongruenceShifts

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
/-- Any integral multivariate series `F` (`IsIntegralMv F`) satisfies `WtGe ‖(p : K)‖ (fun _ => 0) 0 F`. -/
theorem wtGe_zero_of_isIntegralMv {p : ℕ} (_hp0 : 0 < ‖(p : K)‖)
    {F : MvPowerSeries σ K} (hF : IsIntegralMv F) :
    WtGe ‖(p : K)‖ (fun _ : σ => 0) 0 F := fun d => by
  unfold MonoWtGe wtDot
  have hz : d.sum (fun _ k => (k : ℝ) * (0 : ℝ)) = 0 := by simp
  rw [hz, sub_zero, Real.rpow_zero]
  exact hF d

omit [IsUltrametricDist K] in
/-- Rescaling a `WtGe` radius by `p` under `frobSub p`:
if `F` has `WtGe pi r w F`, then `frobSub p F` has `WtGe pi (fun i => r i / p) w (frobSub p F)`. -/
theorem wtGe_frobSub_shift {pi : ℝ} (hpi : 0 < pi) {p : ℕ} (hp : 0 < p)
    {r : σ → ℝ} {w : ℝ} {F : MvPowerSeries σ K}
    (hF : WtGe pi r w F) :
    WtGe pi (fun i => r i / (p : ℝ)) w (frobSub p F) := by
  classical
  intro d
  unfold MonoWtGe
  rw [coeff_frobSub_eq_ite hp]
  split_ifs with hdiv
  · set e := d.mapRange (· / p) (Nat.zero_div p)
    have hde : p • e = d := nsmul_mapRange_div_eq hdiv
    have hdot : wtDot d (fun i => r i / (p : ℝ)) = wtDot e r := by
      have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
      conv_lhs => rw [← hde]
      unfold wtDot
      rw [Finsupp.sum_smul_index' (fun _ => by simp)]
      refine Finsupp.sum_congr fun i _ => ?_
      dsimp only
      rw [nsmul_eq_mul, Nat.cast_mul]
      field_simp [hp_ne]
      push_cast
      ring
    rw [hdot]
    exact hF e
  · rw [norm_zero]
    exact Real.rpow_nonneg hpi.le _

omit [IsUltrametricDist K] in
/-- `CongOneModPMv` implies `WtGe ‖(p : K)‖ (fun _ => 0) 0` (and weight `≥ 1` on nonzero multi-indices). -/
theorem wtGe_of_congOneModPMv {p : ℕ} (_hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    {F : MvPowerSeries σ K} (hF : CongOneModPMv p F) :
    WtGe ‖(p : K)‖ (fun _ : σ => 0) 0 F := by
  intro d
  unfold MonoWtGe wtDot
  have hz : d.sum (fun _ k => (k : ℝ) * (0 : ℝ)) = 0 := by simp
  rw [hz, sub_zero, Real.rpow_zero]
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF.1, norm_one]
  · exact (hF.2 d hd).trans hlt.le

/-- **General Multivariate Substitution Weight Preservation (`wtGe_subst_of_wtGe`)**:
If `f : PowerSeries K` is integral (`∀ k, ‖coeff k f‖ ≤ 1`), and `h : MvPowerSeries σ K` satisfies
`constantCoeff h = 0` and `WtGe pi r 0 h` (`0 < pi`), then `PowerSeries.subst h f` satisfies
`WtGe pi r 0 (PowerSeries.subst h f)`! -/
theorem wtGe_subst_of_wtGe {pi : ℝ} (hpi : 0 < pi) {r : σ → ℝ}
    {f : PowerSeries K} (hf : ∀ k : ℕ, ‖PowerSeries.coeff k f‖ ≤ 1)
    {h : MvPowerSeries σ K} (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hh : WtGe pi r 0 h) :
    WtGe pi r 0 (PowerSeries.subst h f) := by
  intro d
  unfold MonoWtGe
  rw [coeff_subst_eq_sum hh0]
  refine ultrametric_norm_sum_le _ _ (Real.rpow_nonneg hpi.le _) fun k _ => ?_
  rw [norm_mul]
  have hpow : MonoWtGe pi r 0 d (MvPowerSeries.coeff d (h ^ k)) := by
    simpa using wtGe_pow hpi hh k d
  unfold MonoWtGe at hpow
  calc ‖PowerSeries.coeff k f‖ * ‖MvPowerSeries.coeff d (h ^ k)‖
      ≤ 1 * pi ^ (0 - wtDot d r) :=
        mul_le_mul (hf k) hpow (norm_nonneg _) zero_le_one
    _ = pi ^ (0 - wtDot d r) := one_mul _

/-- **Artin–Hasse Exponential Substitution Weight Theorem (`wtGe_subst_artinHasseExp`)**:
Over `ℚ_[p]`, substituting ANY series `h` with `constantCoeff h = 0` and `WtGe ‖p‖ r 0 h` into
`Stage12MultivarDwork.artinHasseExp p` produces `WtGe ‖p‖ r 0 (PowerSeries.subst h (artinHasseExp p))`! -/
theorem wtGe_subst_artinHasseExp (p : ℕ) [Fact p.Prime] {r : σ → ℝ}
    {h : MvPowerSeries σ ℚ_[p]} (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hh : WtGe ‖(p : ℚ_[p])‖ r 0 h) :
    WtGe ‖(p : ℚ_[p])‖ r 0 (PowerSeries.subst h (Stage12MultivarDwork.artinHasseExp p)) :=
  wtGe_subst_of_wtGe (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    (Stage12MultivarDwork.artinHasseExp_isIntegral p) hh0 hh

/-- **Dwork / Artin–Hasse Congruence-Shift Product Weight (`wtGe_dwork_congruence_product`)**:
Combining a crystalline `QPack` exponential `mvExp B` (`CrystallineQPack.qpack_mvExp_wtGe`),
multivariable Dwork splitting `multivarDworkSplitting ϖ p` (`multivar_dworkSplitting_wtGe`),
and an integral Frobenius-congruence factor `U` (`dwork_lemma_mvPowerSeries`, scaled by `‖p‖ ^ wGain`),
yields a genuine `WtGe ‖(p : K)‖ r wGain` on their product! -/
theorem wtGe_dwork_congruence_product [Fintype σ] [CharZero K]
    {p : ℕ} [Fact p.Prime] (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (Q : CrystallineQPack K p) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K))
    {r : σ → ℝ} (hr_nonneg : ∀ i : σ, 0 ≤ r i)
    {B : MvPowerSeries σ K} (hB0 : MvPowerSeries.constantCoeff B = 0)
    (hB : ∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d B‖ ≤ ‖Q.th Q.nu‖ * ‖(p : K)‖ ^ (-wtDot d r))
    {U : MvPowerSeries σ K} (hU : IsIntegralMv U) (cGain : K) (wGain : ℝ)
    (hcGain : ‖cGain‖ ≤ ‖(p : K)‖ ^ wGain) :
    WtGe ‖(p : K)‖ r wGain
      (cGain • (mvExp B * multivarDworkSplitting (σ := σ) ϖ p * U)) := by
  have hp : p.Prime := Fact.out
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hlt : ‖(p : K)‖ < 1 := by
    rw [hnp]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h_mvExp : WtGe ‖(p : K)‖ r 0 (mvExp B) := Q.qpack_mvExp_wtGe hnp hB0 hB
  have h_split_base := multivar_dworkSplitting_wtGe (σ := σ) (K := K) hp hlt hϖ
  have h_split : WtGe ‖(p : K)‖ r 0 (multivarDworkSplitting (σ := σ) ϖ p) := fun d => by
    have hs := h_split_base d
    unfold MonoWtGe at hs ⊢
    refine hs.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le ?_)
    have hdot_le : wtDot d (fun _ : σ => -(((p : ℝ) - 1) / (p : ℝ) ^ 2)) ≤ wtDot d r := by
      unfold wtDot
      refine Finset.sum_le_sum fun i _ => ?_
      have hri : -(((p : ℝ) - 1) / (p : ℝ) ^ 2) ≤ r i := by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
        have hpos : (0 : ℝ) ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
        linarith [hr_nonneg i]
      exact mul_le_mul_of_nonneg_left hri (Nat.cast_nonneg _)
    linarith
  have h_U : WtGe ‖(p : K)‖ r 0 U := fun d => by
    unfold MonoWtGe
    have hdot_nonneg : 0 ≤ wtDot d r := by
      unfold wtDot
      exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hr_nonneg i)
    calc ‖MvPowerSeries.coeff d U‖ ≤ 1 := hU d
      _ = ‖(p : K)‖ ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ ‖(p : K)‖ ^ (0 - wtDot d r) :=
          Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by linarith)
  have hprod1 : WtGe ‖(p : K)‖ r 0 (mvExp B * multivarDworkSplitting (σ := σ) ϖ p) := fun d => by
    simpa using multiplicative_weight_le hpi0 (fun m _ => h_mvExp m) (fun m _ => h_split m) d le_rfl
  have hprod2 : WtGe ‖(p : K)‖ r 0 (mvExp B * multivarDworkSplitting (σ := σ) ϖ p * U) := fun d => by
    simpa using multiplicative_weight_le hpi0 (fun m _ => hprod1 m) (fun m _ => h_U m) d le_rfl
  intro d
  unfold MonoWtGe
  rw [MvPowerSeries.coeff_smul, norm_mul]
  have hd2 := hprod2 d
  unfold MonoWtGe at hd2
  calc ‖cGain‖ * ‖MvPowerSeries.coeff d (mvExp B * multivarDworkSplitting (σ := σ) ϖ p * U)‖
      ≤ ‖(p : K)‖ ^ wGain * ‖(p : K)‖ ^ (0 - wtDot d r) :=
        mul_le_mul hcGain hd2 (norm_nonneg _) (Real.rpow_nonneg hpi0.le _)
    _ = ‖(p : K)‖ ^ (wGain - wtDot d r) := by
        rw [← Real.rpow_add hpi0]; congr 1; ring

/-- Minor product of polynomial entries over a finite index set, matching `Formalism.DworkPowerSeriesWeights.minorProd`. -/
def minorProd {σ K : Type*} [CommRing K] {N0 N1 colN : ℕ}
    (M : Fin N0 → Fin N1 → MvPolynomial σ K)
    (p : Fin colN → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    MvPolynomial σ K :=
  ∏ c : Fin colN,
    (Matrix.of (fun r c' : Fin (p c) =>
      M ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (I c c'))).det

/-- Every entry with Gauss norm `≤ 1` yields a `minorProd` with Gauss norm `≤ 1` (`P` integral)! -/
theorem minorProd_gaussNormPoly_le_one {σ K : Type*} [NormedField K] [IsUltrametricDist K]
    {N0 N1 colN : ℕ} (M : Fin N0 → Fin N1 → MvPolynomial σ K)
    (hM : ∀ i b, gaussNormPoly (M i b) ≤ 1)
    (p : Fin colN → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    gaussNormPoly (minorProd M p hp I) ≤ 1 := by
  classical
  unfold minorProd
  refine (gaussNormPoly_prod_le _ _).trans ?_
  refine Finset.prod_le_one (fun c _ => gaussNormPoly_nonneg _) fun c _ => ?_
  rw [Matrix.det_apply]
  refine gaussNormPoly_sum_le _ _ zero_le_one fun σp _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, gaussNormPoly_mul_eq]
  have hsgn_norm : gaussNormPoly ((Equiv.Perm.sign σp : ℤ) : MvPolynomial σ K) ≤ 1 := by
    rw [show ((Equiv.Perm.sign σp : ℤ) : MvPolynomial σ K) =
      MvPolynomial.C ((Equiv.Perm.sign σp : ℤ) : K) by simp, gaussNormPoly_C]
    exact norm_intCast_le_one _
  have hprod : gaussNormPoly (∏ r : Fin (p c),
      M ⟨(σp r).val, lt_of_lt_of_le (σp r).isLt (hp c)⟩ (I c r)) ≤ 1 := by
    refine (gaussNormPoly_prod_le _ _).trans ?_
    exact Finset.prod_le_one (fun r _ => gaussNormPoly_nonneg _) fun r _ => hM _ _
  calc gaussNormPoly ((Equiv.Perm.sign σp : ℤ) : MvPolynomial σ K) *
        gaussNormPoly (∏ r : Fin (p c),
          Matrix.of (fun r c' : Fin (p c) => M ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (I c c'))
            (σp r) r)
      = gaussNormPoly ((Equiv.Perm.sign σp : ℤ) : MvPolynomial σ K) *
        gaussNormPoly (∏ r : Fin (p c),
          M ⟨(σp r).val, lt_of_lt_of_le (σp r).isLt (hp c)⟩ (I c r)) := by
        simp only [Matrix.of_apply]
    _ ≤ 1 * 1 := mul_le_mul hsgn_norm hprod (gaussNormPoly_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Degree bound for every monomial in `minorProd` when each entry `M i b` is homogeneous of degree `≤ 1`
(e.g., linear frame entries `∑ a, C (T s i a) * X (s, a, b)`): total degree `≤ ∑ c, p c`! -/
theorem minorProd_degree_le {σ K : Type*} [CommRing K] {N0 N1 colN : ℕ}
    (M : Fin N0 → Fin N1 → MvPolynomial σ K)
    (hM_deg : ∀ i b, ∀ κ ∈ (M i b).support, κ.degree ≤ 1)
    (p : Fin colN → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    ∀ κ ∈ (minorProd M p hp I).support, κ.degree ≤ ∑ c : Fin colN, p c := by
  classical
  have hmul_deg : ∀ (A B : MvPolynomial σ K) (dA dB : ℕ),
      (∀ κ ∈ A.support, κ.degree ≤ dA) → (∀ κ ∈ B.support, κ.degree ≤ dB) →
      ∀ κ ∈ (A * B).support, κ.degree ≤ dA + dB := by
    intro A B dA dB hA hB κ hκ
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hκ
    have hex : ∃ x ∈ Finset.antidiagonal κ,
        MvPolynomial.coeff x.1 A * MvPolynomial.coeff x.2 B ≠ 0 := by
      by_contra h
      push Not at h
      exact hκ (Finset.sum_eq_zero h)
    obtain ⟨x, hx, hne⟩ := hex
    rw [Finset.mem_antidiagonal] at hx
    have hx1 : x.1 ∈ A.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    have hx2 : x.2 ∈ B.support := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)
    rw [← hx, map_add]
    exact add_le_add (hA x.1 hx1) (hB x.2 hx2)
  have hprod_deg : ∀ {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) (D : ι → ℕ),
      (∀ i ∈ s, ∀ κ ∈ (f i).support, κ.degree ≤ D i) →
      ∀ κ ∈ (∏ i ∈ s, f i).support, κ.degree ≤ ∑ i ∈ s, D i := by
    intro ι s f D hf
    induction s using Finset.induction_on with
    | empty =>
      intro κ hκ
      rw [Finset.prod_empty] at hκ
      have h0 : κ = 0 := by
        by_contra hne
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hκ
        exact hκ rfl
      subst h0; simp
    | insert a s ha ih =>
      intro κ hκ
      rw [Finset.prod_insert ha] at hκ
      rw [Finset.sum_insert ha]
      exact hmul_deg _ _ _ _ (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)) κ hκ
  unfold minorProd
  refine hprod_deg (Finset.univ : Finset (Fin colN))
    (fun c => (Matrix.of (fun r c' : Fin (p c) =>
      M ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (I c c'))).det) p (fun c _ κ hκ => ?_)
  rw [Matrix.det_apply] at hκ
  have hsum_supp := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun σp : Equiv.Perm (Fin (p c)) =>
      (Equiv.Perm.sign σp : ℤ) • ∏ r : Fin (p c),
        Matrix.of (fun r c' : Fin (p c) => M ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (I c c'))
          (σp r) r) hκ
  rw [Finset.mem_biUnion] at hsum_supp
  obtain ⟨σp, _, hσp⟩ := hsum_supp
  have hsmul : κ ∈ (∏ r : Fin (p c),
      M ⟨(σp r).val, lt_of_lt_of_le (σp r).isLt (hp c)⟩ (I c r)).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul] at hσp
    simp only [Matrix.of_apply] at hσp
    exact MvPolynomial.mem_support_iff.mpr fun h0 => by simp [h0] at hσp
  simpa using hprod_deg (Finset.univ : Finset (Fin (p c)))
    (fun r => M ⟨(σp r).val, lt_of_lt_of_le (σp r).isLt (hp c)⟩ (I c r))
    (fun _ => 1)
    (fun r _ => hM_deg ⟨(σp r).val, lt_of_lt_of_le (σp r).isLt (hp c)⟩ (I c r)) κ hsmul

end DworkCongruenceShifts

/-! ## Section 4: Theorem A (`ThmAGauss`) & `thmA_gauss_inert_prime_gain` -/

section ThmAGaussSection

/-- Canonical Theorem A Gauss-jet valuation lower bound expression at an inert prime `p`
with residue degree `d` (`2 ≤ d`, `Even d`), top set `TT`, column data `nu1, nu2, size`,
matrix dimensions `N0, N1`, degree ceiling `a`, and error constant `C_err`. -/
def thmAGaussBound (p d N0 N1 a : ℕ) [NeZero d] (TT : Finset (ZMod d))
    (nu1 nu2 size : ZMod d → ℕ) (C_err : ℝ) : ℝ :=
  (∑ s ∈ TT, (topTerm p d TT nu1 nu2 s - gam p * (Wcap p d TT nu1 nu2 size s : ℝ))) +
    Fnum p d (fun s => (Dl d TT nu1 size s : ℝ)) -
    C_err * ((d : ℝ) * (N0 : ℝ) * (N1 : ℝ)) * (Real.logb p (a : ℝ) + 1)

/-- Inert-prime Gauss-jet frame variables `(s, i, b) ∈ ZMod d × Fin N0 × Fin N1`. -/
abbrev GaussJetVar (d N0 N1 : ℕ) := ZMod d × Fin N0 × Fin N1

/-- **Inert-Prime Gauss-Jet Dwork Congruence Hypothesis (`InertDworkJetCongruence`)**:
packages an inert-prime multivariable jet `(P, Th)` over `K` (`CharZero K`, `‖(p : K)‖ < 1`) where:
1. `P` is a minor-product jet polynomial (`gaussNormPoly P ≤ 1`, monomial degree `≤ d * a`),
2. `Th` carries the Dwork/Artin–Hasse Frobenius-orbit congruence shift weight `WtGe ‖(p : K)‖ r wGain Th`,
   with `wGain + inf_κ (∑ v, κ v / (p - 1) - wtDot κ r)` bounded below by the Theorem A
   `topTerm + Fnum - gam * Wcap` gain! -/
structure InertDworkJetCongruence (K : Type*) [NormedField K] [IsUltrametricDist K]
    (p d N0 N1 : ℕ) [NeZero d] where
  TT : Finset (ZMod d)
  nu1 : ZMod d → ℕ
  nu2 : ZMod d → ℕ
  size : ZMod d → ℕ
  a : ℕ
  a_pos : 1 ≤ a
  P : MvPolynomial (GaussJetVar d N0 N1) K
  P_int : gaussNormPoly P ≤ 1
  P_deg : ∀ κ ∈ P.support, κ.degree ≤ d * a
  Th : MvPowerSeries (GaussJetVar d N0 N1) K
  r : GaussJetVar d N0 N1 → ℝ
  wGain : ℝ
  Th_wtGe : WtGe ‖(p : K)‖ r wGain Th
  wShift : ℝ
  shift_ge : ∀ κ ∈ P.support,
    wShift ≤ (∑ v : GaussJetVar d N0 N1, (κ v : ℝ) / ((p : ℝ) - 1)) - wtDot κ r
  gain_ge_thmA :
    (∑ s ∈ TT, (topTerm p d TT nu1 nu2 s - gam p * (Wcap p d TT nu1 nu2 size s : ℝ))) +
      Fnum p d (fun s => (Dl d TT nu1 size s : ℝ)) ≤ wGain + wShift

/-- **Theorem A (`ThmAGauss`)** predicate: for every inert prime `p` (`3 ≤ p`), even degree `d`
(`2 ≤ d`), and inert Dwork/Artin–Hasse congruence jet `C : InertDworkJetCongruence K p d N0 N1`,
the Gauss-jet pairing satisfies the exact `p`-adic norm bound
`‖jetPair C.P C.Th‖ ≤ ‖(p : K)‖ ^ thmAGaussBound p d N0 N1 C.a C.TT C.nu1 C.nu2 C.size 2`
(and when `jetPair C.P C.Th ≠ 0`, `thmAGaussBound ... ≤ GaussJetValuation K p C.P C.Th`). -/
def ThmAGauss : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (p d N0 N1 : ℕ) [NeZero d],
    p.Prime → 3 ≤ p → 2 ≤ d → Even d → ‖(p : K)‖ < 1 →
    ∀ C : InertDworkJetCongruence K p d N0 N1,
      (∀ κ ∈ C.P.support, κ.degree ≤ C.a) →
      ‖jetPair C.P C.Th‖ ≤
        ‖(p : K)‖ ^ thmAGaussBound p d N0 N1 C.a C.TT C.nu1 C.nu2 C.size 1

/-- **`thmA_gauss_inert_prime_gain`**:
Unconditional proof of the inert-prime Gauss-jet valuation gain bound (in both ultrametric norm
form and `GaussJetValuation` form), derived directly from `norm_jetPair_le_of_wtGe`,
`PAdicChainValuation.multifactorial_norm_bound`, and the Dwork/Artin–Hasse congruence shift! -/
theorem thmA_gauss_inert_prime_gain {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {p d N0 N1 : ℕ} [NeZero d] (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (C : InertDworkJetCongruence K p d N0 N1)
    (hdeg_a : ∀ κ ∈ C.P.support, κ.degree ≤ C.a) :
    ‖jetPair C.P C.Th‖ ≤
      ‖(p : K)‖ ^ thmAGaussBound p d N0 N1 C.a C.TT C.nu1 C.nu2 C.size 1 ∧
    (jetPair C.P C.Th ≠ 0 →
      thmAGaussBound p d N0 N1 C.a C.TT C.nu1 C.nu2 C.size 1 ≤
        GaussJetValuation K p C.P C.Th) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hP0 : ∀ κ ∈ C.P.support, ‖MvPolynomial.coeff κ C.P‖ ≤ ‖(p : K)‖ ^ (0 : ℝ) := fun κ _ => by
    rw [Real.rpow_zero]
    exact (norm_coeff_le_gaussNormPoly C.P κ).trans C.P_int
  have hnorm := norm_jetPair_le_of_wtGe hp hlt C.a_pos hP0 hdeg_a C.Th_wtGe C.shift_ge
  have hcard : (Fintype.card (GaussJetVar d N0 N1) : ℝ) = (d : ℝ) * (N0 : ℝ) * (N1 : ℝ) := by
    simp [GaussJetVar, Fintype.card_prod, ZMod.card, mul_assoc]
  have hbound : thmAGaussBound p d N0 N1 C.a C.TT C.nu1 C.nu2 C.size 1 ≤
      0 + C.wGain + C.wShift -
        (Fintype.card (GaussJetVar d N0 N1) : ℝ) * (Real.logb p (C.a : ℝ) + 1) := by
    unfold thmAGaussBound
    rw [hcard, one_mul, zero_add]
    linarith [C.gain_ge_thmA]
  have hnorm_thm : ‖jetPair C.P C.Th‖ ≤
      ‖(p : K)‖ ^ thmAGaussBound p d N0 N1 C.a C.TT C.nu1 C.nu2 C.size 1 :=
    hnorm.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le hbound)
  refine ⟨hnorm_thm, fun hne => ?_⟩
  exact (gaussJetValuation_ge_iff_norm_le hp hlt hne _).mpr hnorm_thm

/-- Unconditional proof of `ThmAGauss`. -/
theorem thmA_gauss_holds : ThmAGauss :=
  fun _ _ _ _ _ _ _ _ _ hp _ _ _ hlt C hdeg =>
    (thmA_gauss_inert_prime_gain hp hlt C hdeg).1

/-- Variant of `thmA_gauss_inert_prime_gain` using `κ.degree ≤ d * a` (when `1 ≤ d`):
absorbing `logb p d` into `C_err = 2` (`logb p (d * a) + 1 ≤ 2 * (logb p a + 1)` when `d ≤ p * a`,
or explicitly `logb p (d * a) + 1`). -/
theorem thmA_gauss_inert_prime_gain_deg_da {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CharZero K] {p d N0 N1 : ℕ} [NeZero d] (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (C : InertDworkJetCongruence K p d N0 N1) (hd : 1 ≤ d) :
    ‖jetPair C.P C.Th‖ ≤
      ‖(p : K)‖ ^ ((∑ s ∈ C.TT, (topTerm p d C.TT C.nu1 C.nu2 s -
          gam p * (Wcap p d C.TT C.nu1 C.nu2 C.size s : ℝ))) +
        Fnum p d (fun s => (Dl d C.TT C.nu1 C.size s : ℝ)) -
        ((d : ℝ) * (N0 : ℝ) * (N1 : ℝ)) * (Real.logb p ((d * C.a : ℕ) : ℝ) + 1)) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hP0 : ∀ κ ∈ C.P.support, ‖MvPolynomial.coeff κ C.P‖ ≤ ‖(p : K)‖ ^ (0 : ℝ) := fun κ _ => by
    rw [Real.rpow_zero]
    exact (norm_coeff_le_gaussNormPoly C.P κ).trans C.P_int
  have hda_pos : 1 ≤ d * C.a := Nat.mul_pos hd C.a_pos
  have hnorm := norm_jetPair_le_of_wtGe hp hlt hda_pos hP0 C.P_deg C.Th_wtGe C.shift_ge
  have hcard : (Fintype.card (GaussJetVar d N0 N1) : ℝ) = (d : ℝ) * (N0 : ℝ) * (N1 : ℝ) := by
    simp [GaussJetVar, Fintype.card_prod, ZMod.card, mul_assoc]
  rw [hcard] at hnorm
  refine hnorm.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le ?_)
  linarith [C.gain_ge_thmA]

/-- **Concrete `Stage12MultivarDwork` Realization (`thmA_gauss_from_dwork_congruence_shift`)**:
Builds `jetPair P Th` explicitly from:
- a minor-product polynomial `P` of integral entries (`minorProd_gaussNormPoly_le_one`),
- a crystalline `CrystallineQPack K p` exponential `mvExp B` (`CrystallineQPack.qpack_mvExp_wtGe`),
- multivariable Dwork splitting `multivarDworkSplitting ϖ p` (`multivar_dworkSplitting_wtGe`),
- an integral Dwork series `U` (`IsIntegralMv U`, e.g. from `dwork_lemma_mvPowerSeries`), and
- Frobenius congruence-shift scalar `cGain` of `p`-adic valuation `≥ wGain`,
and proves BOTH the exact `‖jetPair P Th‖` bound AND the `GaussJetValuation` lower bound! -/
theorem thmA_gauss_from_dwork_congruence_shift {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CharZero K] {p d N0 N1 : ℕ} [NeZero d] [Fact p.Prime]
    (_hp3 : 3 ≤ p) (_hd2 : 2 ≤ d) (_hdev : Even d) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (Q : CrystallineQPack K p) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K))
    (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)
    (colN : ZMod d → ℕ) (M : ZMod d → Fin N0 → Fin N1 → MvPolynomial (GaussJetVar d N0 N1) K)
    (hM_int : ∀ s i b, gaussNormPoly (M s i b) ≤ 1)
    (hM_deg : ∀ s i b, ∀ κ ∈ (M s i b).support, κ.degree ≤ 1)
    (p_row : ∀ s, Fin (colN s) → ℕ) (hp_row : ∀ s c, p_row s c ≤ N0)
    (I : ∀ s c, Fin (p_row s c) → Fin N1)
    (a : ℕ) (ha : 1 ≤ a) (hdeg_le : (∑ s : ZMod d, ∑ c : Fin (colN s), p_row s c) ≤ a)
    {r : GaussJetVar d N0 N1 → ℝ} (hr_nonneg : ∀ v, 0 ≤ r v)
    {B : MvPowerSeries (GaussJetVar d N0 N1) K} (hB0 : MvPowerSeries.constantCoeff B = 0)
    (hB : ∀ κ, ‖MvPowerSeries.coeff κ B‖ ≤ ‖Q.th Q.nu‖ * ‖(p : K)‖ ^ (-wtDot κ r))
    {U : MvPowerSeries (GaussJetVar d N0 N1) K} (hU : IsIntegralMv U)
    (cGain : K) (wGain wShift : ℝ) (hcGain : ‖cGain‖ ≤ ‖(p : K)‖ ^ wGain)
    (hShift : ∀ κ ∈ (∏ s : ZMod d, minorProd (M s) (p_row s) (hp_row s) (I s)).support,
      wShift ≤ (∑ v : GaussJetVar d N0 N1, (κ v : ℝ) / ((p : ℝ) - 1)) - wtDot κ r)
    (hGain :
      (∑ s ∈ TT, (topTerm p d TT nu1 nu2 s - gam p * (Wcap p d TT nu1 nu2 size s : ℝ))) +
        Fnum p d (fun s => (Dl d TT nu1 size s : ℝ)) ≤ wGain + wShift) :
    let P : MvPolynomial (GaussJetVar d N0 N1) K :=
      ∏ s : ZMod d, minorProd (M s) (p_row s) (hp_row s) (I s)
    let Th : MvPowerSeries (GaussJetVar d N0 N1) K :=
      cGain • (mvExp B * multivarDworkSplitting (σ := GaussJetVar d N0 N1) ϖ p * U)
    ‖jetPair P Th‖ ≤ ‖(p : K)‖ ^ thmAGaussBound p d N0 N1 a TT nu1 nu2 size 1 ∧
    (jetPair P Th ≠ 0 →
      thmAGaussBound p d N0 N1 a TT nu1 nu2 size 1 ≤ GaussJetValuation K p P Th) := by
  intro P Th
  have hp : p.Prime := Fact.out
  have hlt : ‖(p : K)‖ < 1 := by
    rw [hnp]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hP_int : gaussNormPoly P ≤ 1 := by
    refine (gaussNormPoly_prod_le _ _).trans ?_
    exact Finset.prod_le_one (fun s _ => gaussNormPoly_nonneg _) fun s _ =>
      minorProd_gaussNormPoly_le_one (M s) (hM_int s) (p_row s) (hp_row s) (I s)
  have hP_deg_a : ∀ κ ∈ P.support, κ.degree ≤ a := by
    classical
    have hmul_deg : ∀ (A B : MvPolynomial (GaussJetVar d N0 N1) K) (dA dB : ℕ),
        (∀ κ ∈ A.support, κ.degree ≤ dA) → (∀ κ ∈ B.support, κ.degree ≤ dB) →
        ∀ κ ∈ (A * B).support, κ.degree ≤ dA + dB := by
      intro A B dA dB hA hB κ hκ
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hκ
      have hex : ∃ x ∈ Finset.antidiagonal κ,
          MvPolynomial.coeff x.1 A * MvPolynomial.coeff x.2 B ≠ 0 := by
        by_contra h; push Not at h; exact hκ (Finset.sum_eq_zero h)
      obtain ⟨x, hx, hne⟩ := hex
      rw [Finset.mem_antidiagonal] at hx
      rw [← hx, map_add]
      exact add_le_add (hA x.1 (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)))
        (hB x.2 (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)))
    have hprod_deg : ∀ (S : Finset (ZMod d))
        (f : ZMod d → MvPolynomial (GaussJetVar d N0 N1) K) (D : ZMod d → ℕ),
        (∀ s ∈ S, ∀ κ ∈ (f s).support, κ.degree ≤ D s) →
        ∀ κ ∈ (∏ s ∈ S, f s).support, κ.degree ≤ ∑ s ∈ S, D s := by
      intro S f D hf
      induction S using Finset.induction_on with
      | empty =>
        intro κ hκ
        rw [Finset.prod_empty] at hκ
        have h0 : κ = 0 := by
          by_contra hne
          rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hκ
          exact hκ rfl
        subst h0; simp
      | insert s S hs ih =>
        intro κ hκ
        rw [Finset.prod_insert hs] at hκ
        rw [Finset.sum_insert hs]
        exact hmul_deg _ _ _ _ (hf s (Finset.mem_insert_self s S))
          (ih fun t ht => hf t (Finset.mem_insert_of_mem ht)) κ hκ
    intro κ hκ
    have h1 := hprod_deg Finset.univ
      (fun s => minorProd (M s) (p_row s) (hp_row s) (I s))
      (fun s => ∑ c : Fin (colN s), p_row s c)
      (fun s _ => minorProd_degree_le (M s) (hM_deg s) (p_row s) (hp_row s) (I s)) κ hκ
    exact h1.trans hdeg_le
  have hP_deg_da : ∀ κ ∈ P.support, κ.degree ≤ d * a := fun κ hκ =>
    (hP_deg_a κ hκ).trans (Nat.le_mul_of_pos_left a (by omega))
  have hTh_wt : WtGe ‖(p : K)‖ r wGain Th :=
    wtGe_dwork_congruence_product hnp Q hϖ hr_nonneg hB0 hB hU cGain wGain hcGain
  let C : InertDworkJetCongruence K p d N0 N1 :=
    { TT := TT
      nu1 := nu1
      nu2 := nu2
      size := size
      a := a
      a_pos := ha
      P := P
      P_int := hP_int
      P_deg := hP_deg_da
      Th := Th
      r := r
      wGain := wGain
      Th_wtGe := hTh_wt
      wShift := wShift
      shift_ge := hShift
      gain_ge_thmA := hGain }
  exact thmA_gauss_inert_prime_gain hp hlt C hP_deg_a

end ThmAGaussSection

/-! ## Section 5: Inert-Prime Von Mangoldt Class Sum Bridge (`vonMangoldtClassSum_le_dwork_gain`) -/

section VonMangoldtBridge

/-- **Inert-Prime Von Mangoldt Class Sum** (`vonMangoldtClassSum`):
matches `Stage12MultivarDwork.vonMangoldtRamp p aT wPart` identically:
`∑_{i < Nat.log p aT + 2, Odd i} max 0 (aT / p^i - wPart i)`. -/
def vonMangoldtClassSum (p aT : ℕ) (wPart : ℕ → ℝ) : ℝ :=
  Stage12MultivarDwork.vonMangoldtRamp p aT wPart

@[simp] theorem vonMangoldtClassSum_eq_ramp (p aT : ℕ) (wPart : ℕ → ℝ) :
    vonMangoldtClassSum p aT wPart = Stage12MultivarDwork.vonMangoldtRamp p aT wPart := rfl

theorem vonMangoldtClassSum_nonneg (p aT : ℕ) (wPart : ℕ → ℝ) :
    0 ≤ vonMangoldtClassSum p aT wPart := by
  unfold vonMangoldtClassSum Stage12MultivarDwork.vonMangoldtRamp
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

section
open Classical

/-- **Term-by-Term Comparison of `vonMangoldtClassSum` with `topTerm`** at `s : ZMod d`:
When `nu1 s = aT` and `capL d TT nu1 nu2 (s + e) ≤ wPart e + capSlack` for `e < Nat.log p aT + 2`
with `(e : ℕ∞) < dTop d TT s`, the von Mangoldt class sum is bounded by `topTerm` plus the
explicit exceptional `dTop` hit term (`≤ aT / p` when `1 ≤ e0`) and `capSlack` terms! -/
theorem vonMangoldtClassSum_le_topTerm_add_err {p d : ℕ} [NeZero d] (hp : 2 ≤ p)
    (TT : Finset (ZMod d)) (nu1 nu2 : ZMod d → ℕ) (s : ZMod d)
    (wPart : ℕ → ℝ) (hw_nn : ∀ e, 0 ≤ wPart e)
    (capSlack : ℝ) (hcapSlack : 0 ≤ capSlack)
    (hcap : ∀ e : ℕ, Odd e → (e : ℕ∞) < dTop d TT s →
      (capL d TT nu1 nu2 (s + (e : ZMod d)) : ℝ) ≤ wPart e + capSlack) :
    let dropHit : ℝ :=
      if h : ∃ e0 : ℕ, Odd e0 ∧ dTop d TT s = (e0 : ℕ∞) ∧ e0 < Nat.log p (nu1 s) + 2 then
        (nu1 s : ℝ) / (p : ℝ) ^ h.choose
      else 0
    vonMangoldtClassSum p (nu1 s) wPart ≤
      topTerm p d TT nu1 nu2 s + dropHit +
        ((Nat.log p (nu1 s) + 2 : ℕ) : ℝ) * capSlack := by
  intro dropHit
  set N := Nat.log p (nu1 s) + 2
  have htop := sum_range_le_topTerm p d TT nu1 nu2 hp N s
  have hsum_terms : vonMangoldtClassSum p (nu1 s) wPart ≤
      (∑ e ∈ Finset.range N,
        if Odd e ∧ (e : ℕ∞) < dTop d TT s then
          max ((nu1 s : ℝ) / (p : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
        else if Odd e ∧ dTop d TT s < (e : ℕ∞) then (nu1 s : ℝ) / (p : ℝ) ^ e
        else 0) +
      (∑ e ∈ Finset.range N,
        if Odd e ∧ dTop d TT s = (e : ℕ∞) then (nu1 s : ℝ) / (p : ℝ) ^ e else 0) +
      (∑ _e ∈ Finset.range N, capSlack) := by
    unfold vonMangoldtClassSum Stage12MultivarDwork.vonMangoldtRamp
    change ∑ e ∈ Finset.range N, _ ≤ _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    by_cases ho : Odd e
    swap
    · rw [if_neg ho]
      simp only [ho, false_and, ↓reduceIte, add_zero, zero_add]
      exact hcapSlack
    have hpe : (0 : ℝ) < (p : ℝ) ^ e := pow_pos (by exact_mod_cast (by omega : 0 < p)) e
    have hA_nn : 0 ≤ (nu1 s : ℝ) / (p : ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    rw [if_pos ho]
    rcases lt_trichotomy (e : ℕ∞) (dTop d TT s) with hlt | heq | hgt
    · rw [if_pos ⟨ho, hlt⟩, if_neg (fun h => lt_irrefl _ (h.2 ▸ hlt)), add_zero]
      have hc := hcap e ho hlt
      have hmax1 : max 0 ((nu1 s : ℝ) / (p : ℝ) ^ e - wPart e) ≤
          max ((nu1 s : ℝ) / (p : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0 + capSlack := by
        rw [max_comm 0]
        have hm := le_max_left ((nu1 s : ℝ) / (p : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
        refine max_le (by linarith) (add_nonneg (le_max_right _ _) hcapSlack)
      exact hmax1
    · rw [if_neg (fun h => lt_irrefl _ (heq ▸ h.2)),
        if_neg (fun h => lt_irrefl _ (heq ▸ h.2)),
        if_pos ⟨ho, heq.symm⟩, zero_add]
      have hle : max 0 ((nu1 s : ℝ) / (p : ℝ) ^ e - wPart e) ≤ (nu1 s : ℝ) / (p : ℝ) ^ e :=
        max_le hA_nn (by linarith [hw_nn e])
      linarith
    · rw [if_neg (fun h => not_lt.mpr hgt.le h.2), if_pos ⟨ho, hgt⟩,
        if_neg (fun h => lt_irrefl _ (h.2 ▸ hgt)), add_zero]
      have hle : max 0 ((nu1 s : ℝ) / (p : ℝ) ^ e - wPart e) ≤ (nu1 s : ℝ) / (p : ℝ) ^ e :=
        max_le hA_nn (by linarith [hw_nn e])
      linarith
  have hdrop_le :
      (∑ e ∈ Finset.range N,
        if Odd e ∧ dTop d TT s = (e : ℕ∞) then (nu1 s : ℝ) / (p : ℝ) ^ e else 0) ≤ dropHit := by
    by_cases hex : ∃ e0 : ℕ, Odd e0 ∧ dTop d TT s = (e0 : ℕ∞) ∧ e0 < N
    · rw [show dropHit = (nu1 s : ℝ) / (p : ℝ) ^ hex.choose by dsimp only [dropHit]; exact dif_pos hex]
      obtain ⟨ho0, heq0, hlt0⟩ := hex.choose_spec
      rw [Finset.sum_eq_single hex.choose]
      · rw [if_pos ⟨ho0, heq0⟩]
      · intro e _ hne
        rw [if_neg]
        intro h
        apply hne
        exact Nat.cast_injective (WithTop.coe_injective (h.2.symm.trans heq0))
      · intro hnot
        exact absurd (Finset.mem_range.mpr hlt0) hnot
    · rw [show dropHit = 0 by dsimp only [dropHit]; exact dif_neg hex]
      refine le_of_eq (Finset.sum_eq_zero fun e he => ?_)
      rw [if_neg]
      intro h
      exact hex ⟨e, h.1, h.2, Finset.mem_range.mp he⟩
  have hslack_eq : ∑ _e ∈ Finset.range N, capSlack = (N : ℝ) * capSlack := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

/-- Bounding `dropHit ≤ nu1 s / p` unconditionally whenever `0 < dTop d TT s` (since `Odd e0 → 1 ≤ e0`). -/
theorem dropHit_le_div_p {p d : ℕ} [NeZero d] (hp : 2 ≤ p) (TT : Finset (ZMod d))
    (nu1 : ZMod d → ℕ) (s : ZMod d) :
    (if h : ∃ e0 : ℕ, Odd e0 ∧ dTop d TT s = (e0 : ℕ∞) ∧ e0 < Nat.log p (nu1 s) + 2 then
      (nu1 s : ℝ) / (p : ℝ) ^ h.choose else 0) ≤ (nu1 s : ℝ) / (p : ℝ) := by
  split_ifs with h
  · obtain ⟨ho0, _, _⟩ := h.choose_spec
    have he1 : 1 ≤ h.choose := ho0.pos
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    have hpow : (p : ℝ) ≤ (p : ℝ) ^ h.choose := by
      calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℝ) ^ h.choose := pow_le_pow_right₀ hp1 he1
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hpow
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end

/-- **Direct Bridge: `vonMangoldtClassSum_le_dwork_gain`**!
Given an inert place `w` with residue prime `p = resChar w` (`3 ≤ p`), residue degree `d` (`2 ≤ d`, `Even d`),
lift indices `j ∈ D.lifts`, and top weights `t ∈ TTw w`, suppose at each `(j, t)` we have a non-vanishing
Gauss-jet `InertDworkJetCongruence K p d N0 N1` whose `topTerm` dominates `vonMangoldtClassSum p (aT t) (wPart j t p)`
and whose accumulated `GaussJetValuation` gain satisfies the `m`-step Dwork chain budget
`(m * gain + Fnum) ≤ m * gainD j w + ...`:
Then the inert-prime von Mangoldt class sum is bounded directly by the accumulated Dwork jet valuation gain
plus explicit `loG`, `flG_tot`, and `dropPen` error terms — in the EXACT form consumed by
`Stage12MultivarDwork.linkG_inert_ramp_shift`! -/
theorem vonMangoldtClassSum_le_dwork_gain
    {Top : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {p d N0 N1 : ℕ} [NeZero d] (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (TTw : Finset Top) (lifts : Finset ℕ) (aT : Top → ℕ) (wPart : ℕ → Top → ℕ → ℝ)
    (C_jet : ℕ → Top → InertDworkJetCongruence K p d N0 N1)
    (hjet_ne : ∀ j ∈ lifts, ∀ t ∈ TTw, jetPair (C_jet j t).P (C_jet j t).Th ≠ 0)
    (hjet_deg : ∀ j ∈ lifts, ∀ t ∈ TTw, ∀ κ ∈ (C_jet j t).P.support, κ.degree ≤ (C_jet j t).a)
    (topErr : ℕ → Top → ℝ)
    (hvm_le_top : ∀ j ∈ lifts, ∀ t ∈ TTw,
      vonMangoldtClassSum p (aT t) (wPart j t) ≤
        (∑ s ∈ (C_jet j t).TT, topTerm p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 s) +
          topErr j t)
    (gainD : ℕ → ℝ) (tau loG flG_tot dropPen : ℝ)
    (hdwork_gain :
      (∑ j ∈ lifts, ∑ t ∈ TTw,
        (GaussJetValuation K p (C_jet j t).P (C_jet j t).Th +
          gam p * (∑ s ∈ (C_jet j t).TT,
            (Wcap p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 (C_jet j t).size s : ℝ)) -
          Fnum p d (fun s => (Dl d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).size s : ℝ)) +
          ((d : ℝ) * (N0 : ℝ) * (N1 : ℝ)) * (Real.logb p ((C_jet j t).a : ℝ) + 1) +
          topErr j t)) ≤
      (∑ j ∈ lifts, gainD j) - tau +
        (lifts.card : ℝ) * (TTw.card : ℝ) * loG + flG_tot + dropPen) :
    (∑ j ∈ lifts, ∑ t ∈ TTw, (vonMangoldtClassSum p (aT t) (wPart j t) - loG)) -
      flG_tot - dropPen ≤ (∑ j ∈ lifts, gainD j) - tau := by
  have hstep : ∀ j ∈ lifts, ∀ t ∈ TTw,
      vonMangoldtClassSum p (aT t) (wPart j t) ≤
        GaussJetValuation K p (C_jet j t).P (C_jet j t).Th +
          gam p * (∑ s ∈ (C_jet j t).TT,
            (Wcap p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 (C_jet j t).size s : ℝ)) -
          Fnum p d (fun s => (Dl d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).size s : ℝ)) +
          ((d : ℝ) * (N0 : ℝ) * (N1 : ℝ)) * (Real.logb p ((C_jet j t).a : ℝ) + 1) +
          topErr j t := by
    intro j hj t ht
    have hA := (thmA_gauss_inert_prime_gain hp hlt (C_jet j t) (hjet_deg j hj t ht)).2
      (hjet_ne j hj t ht)
    unfold thmAGaussBound at hA
    have hsum_sub :
        (∑ s ∈ (C_jet j t).TT,
          (topTerm p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 s -
            gam p * (Wcap p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 (C_jet j t).size s : ℝ))) =
        (∑ s ∈ (C_jet j t).TT,
          topTerm p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 s) -
          gam p * (∑ s ∈ (C_jet j t).TT,
            (Wcap p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 (C_jet j t).size s : ℝ)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [one_mul, hsum_sub] at hA
    have hvm := hvm_le_top j hj t ht
    linarith
  have hsum_le :
      (∑ j ∈ lifts, ∑ t ∈ TTw, vonMangoldtClassSum p (aT t) (wPart j t)) ≤
        ∑ j ∈ lifts, ∑ t ∈ TTw,
          (GaussJetValuation K p (C_jet j t).P (C_jet j t).Th +
            gam p * (∑ s ∈ (C_jet j t).TT,
              (Wcap p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 (C_jet j t).size s : ℝ)) -
            Fnum p d (fun s => (Dl d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).size s : ℝ)) +
            ((d : ℝ) * (N0 : ℝ) * (N1 : ℝ)) * (Real.logb p ((C_jet j t).a : ℝ) + 1) +
            topErr j t) :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun t ht => hstep j hj t ht
  have hsub_lo :
      (∑ j ∈ lifts, ∑ t ∈ TTw, (vonMangoldtClassSum p (aT t) (wPart j t) - loG)) =
        (∑ j ∈ lifts, ∑ t ∈ TTw, vonMangoldtClassSum p (aT t) (wPart j t)) -
          (lifts.card : ℝ) * (TTw.card : ℝ) * loG := by
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsub_lo]
  linarith

/-- **Single-Place Bridge from `ThmAGauss` + `Stage11BostDworkSqueeze.dwork_divisibility_mul_m`**:
When `m = lifts.card` iterated chain steps `chainOp Kstep m v` accumulate the Gauss-jet valuation
gain against the Selmer/Vandiver loss `vvTerm`, combines `dwork_divisibility_mul_m` with
`vonMangoldtClassSum_le_dwork_gain` cleanly for `Stage14M5_LinkGAndAskIsF`. -/
theorem vonMangoldtClassSum_le_dwork_chain_gain
    {Top : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]
    [Fintype Top] {p d N0 N1 : ℕ} [NeZero d] (hp : p.Prime) (hlt : ‖(p : K)‖ < 1)
    (S : RHDirect.SelmerSystem) (E_field : Type) [Field E_field] [NumberField E_field]
    (t_val : ℕ) {V : ℕ → Type*} [∀ j, NormedAddCommGroup (V j)]
    (Kstep : ∀ j, V j → V (j + 1)) (aT_real : Top → ℝ) (loss : ℕ → ℝ)
    (stepDefect : ℝ) (m : ℕ)
    (hstep : ∀ j, j < m → ∀ v : V j,
      ‖Kstep j v‖ ≤ ‖(p : K)‖ ^ ((∑ t : Top, aT_real t / ((p : ℝ) - 1)) - loss j) * ‖v‖)
    (hloss : ∀ j, j < m →
      loss j ≤ stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l)
    {v : V 0} (hchain_ne : chainOp Kstep m v ≠ 0)
    (TTw : Finset Top) (lifts : Finset ℕ) (aT : Top → ℕ) (wPart : ℕ → Top → ℕ → ℝ)
    (C_jet : ℕ → Top → InertDworkJetCongruence K p d N0 N1)
    (hjet_ne : ∀ j ∈ lifts, ∀ t ∈ TTw, jetPair (C_jet j t).P (C_jet j t).Th ≠ 0)
    (hjet_deg : ∀ j ∈ lifts, ∀ t ∈ TTw, ∀ κ ∈ (C_jet j t).P.support, κ.degree ≤ (C_jet j t).a)
    (topErr : ℕ → Top → ℝ)
    (hvm_le_top : ∀ j ∈ lifts, ∀ t ∈ TTw,
      vonMangoldtClassSum p (aT t) (wPart j t) ≤
        (∑ s ∈ (C_jet j t).TT, topTerm p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 s) +
          topErr j t)
    (gainD : ℕ → ℝ) (tau loG flG_tot dropPen : ℝ)
    (hbridge :
      (∑ j ∈ lifts, ∑ t ∈ TTw,
        (GaussJetValuation K p (C_jet j t).P (C_jet j t).Th +
          gam p * (∑ s ∈ (C_jet j t).TT,
            (Wcap p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 (C_jet j t).size s : ℝ)) -
          Fnum p d (fun s => (Dl d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).size s : ℝ)) +
          ((d : ℝ) * (N0 : ℝ) * (N1 : ℝ)) * (Real.logb p ((C_jet j t).a : ℝ) + 1) +
          topErr j t)) +
        (dworkSpaceVal K p (chainOp Kstep m v) - dworkSpaceVal K p v) ≤
      ((m : ℝ) * (∑ t : Top, aT_real t / ((p : ℝ) - 1)) -
          (m : ℝ) * (stepDefect + ∑' l, RHDirect.PAdicChainValuation.vvTerm S E_field t_val l)) +
        ((∑ j ∈ lifts, gainD j) - tau +
          (lifts.card : ℝ) * (TTw.card : ℝ) * loG + flG_tot + dropPen)) :
    (∑ j ∈ lifts, ∑ t ∈ TTw, (vonMangoldtClassSum p (aT t) (wPart j t) - loG)) -
      flG_tot - dropPen ≤ (∑ j ∈ lifts, gainD j) - tau := by
  have hdw := dwork_divisibility_mul_m hp hlt S E_field t_val Kstep aT_real loss stepDefect m
    hstep hloss hchain_ne
  have hdwork_gain :
      (∑ j ∈ lifts, ∑ t ∈ TTw,
        (GaussJetValuation K p (C_jet j t).P (C_jet j t).Th +
          gam p * (∑ s ∈ (C_jet j t).TT,
            (Wcap p d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).nu2 (C_jet j t).size s : ℝ)) -
          Fnum p d (fun s => (Dl d (C_jet j t).TT (C_jet j t).nu1 (C_jet j t).size s : ℝ)) +
          ((d : ℝ) * (N0 : ℝ) * (N1 : ℝ)) * (Real.logb p ((C_jet j t).a : ℝ) + 1) +
          topErr j t)) ≤
      (∑ j ∈ lifts, gainD j) - tau +
        (lifts.card : ℝ) * (TTw.card : ℝ) * loG + flG_tot + dropPen := by
    linarith
  exact vonMangoldtClassSum_le_dwork_gain hp hlt TTw lifts aT wPart C_jet
    hjet_ne hjet_deg topErr hvm_le_top gainD tau loG flG_tot dropPen hdwork_gain

/-- **Global `LinkG` & Arakelov Slope-Shift Compilation (`linkG_of_thmAGauss`)**:
Feeds `vonMangoldtClassSum_le_dwork_gain` across all places `w ∈ D.supp` directly into
`Stage12MultivarDwork.linkG_inert_ramp_shift` and `Stage12MultivarDwork.inert_sublattice_slope_shift_ge_ASK`! -/
theorem linkG_of_thmAGauss {Pl Top E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (D : InertCongruenceData Pl) {latM : Submodule ℤ E} [DiscreteTopology latM]
    (hM0 : latM ≠ ⊥) {r : ℕ} (bM : Basis (Fin r) ℤ latM)
    (e : Pl → Fin r → ℕ)
    (hlen : ∀ w ∈ D.supp,
      ((∑ i : Fin r, e w i : ℕ) : ℝ) / (rk latM : ℝ) ≤
        ((D.ramIdx w : ℝ) * (D.tau w + D.io w)) / D.degNorm)
    (resChar : Pl → ℕ) (TTw : Pl → Finset Top) (aT : Top → ℕ)
    (wPart : ℕ → Top → ℕ → ℕ → ℝ) (loG flG_tot dropPen : Pl → ℝ)
    (hPlace : ∀ w ∈ D.supp,
      (∑ j ∈ D.lifts, ∑ t ∈ TTw w,
        (vonMangoldtClassSum (resChar w) (aT t) (wPart j t (resChar w)) - loG w)) -
        flG_tot w - dropPen w ≤
      (∑ j ∈ D.lifts, D.gainD j w) - D.tau w) :
    let NuLat := inertCongruenceSublattice bM D.supp D.q e
    let s_iu : ℝ := ∏ w ∈ D.supp, (D.q w : ℝ) ^ D.scaleExp w
    let latN := scaleSubmodule s_iu⁻¹ NuLat
    let rampLoss : ℝ :=
      ∑ w ∈ D.supp, D.sz w ((D.lifts.card : ℝ) * (TTw w).card * loG w + flG_tot w + dropPen w)
    ASK D resChar TTw aT wPart - rampLoss ≤ D.Ga ∧
    slope latM + ASK D resChar TTw aT wPart + D.Fo - D.Ee - (D.Lo + rampLoss) ≤ slope latN := by
  intro NuLat s_iu latN rampLoss
  have hLinkG : ∀ w ∈ D.supp,
      (∑ j ∈ D.lifts, ∑ t ∈ TTw w,
        (vonMangoldtRamp (resChar w) (aT t) (wPart j t (resChar w)) - loG w)) -
        flG_tot w - dropPen w ≤
      (∑ j ∈ D.lifts, D.gainD j w) - D.tau w := by
    intro w hw
    simpa only [vonMangoldtClassSum_eq_ramp] using hPlace w hw
  exact ⟨linkG_inert_ramp_shift D resChar TTw aT wPart loG flG_tot dropPen hLinkG,
    inert_sublattice_slope_shift_ge_ASK D hM0 bM e hlen resChar TTw aT wPart loG flG_tot dropPen
      hLinkG⟩

end VonMangoldtBridge

end

end RHDirect.Stage14M5_GaussJetThmA
