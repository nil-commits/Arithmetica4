import RHDirect.Stage11MoriwakiCovolume
import RHDirect.Stage12SchurWeylLattices

/-!
# RHDirect.Stage14M4_MoriwakiBignessCore

**FIELD-2 PACKAGE M4 (WAVE 1) — UNCONDITIONAL MORIWAKI ARITHMETIC BIGNESS, SEGRE-JOIN TWIST
GENERATION, GENERIC RANK & SHIFT-VOLUME BOUNDS, AND CONCRETE ZERO-ASSUMPTION REALIZATIONS**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`, `0` `native_decide`).

Extends `RHDirect.Stage11MoriwakiCovolume` and `RHDirect.Stage12SchurWeylLattices` to formalize
the core Moriwaki arithmetic bigness & Segre-join generation machinery for Field-2 Package M4:

## Contents

1. **Multi-Graded Coordinate Charts, Segre Join & Twist Algebra (`SegreJoinTwist`)**:
   - Diamond-free multi-graded chart rings `chartRingOver φ y c₀ : Subring Ω` over an explicit
     base ring homomorphism `φ : S →+* Ω` (NO nested global `Algebra` diamonds), multi-graded
     section sets `secOver φ y β`, and generation predicates `GeneratesOver φ y β η`.
   - Segre-join coordinates `segreVec`, `segreJoin`, `segreChart`, degree pullbacks `pullDeg`,
     `baseDeg`, `diagShift`, and exact ring-theoretic chart-containment
     `segreChartRing_le_chartRing` / `segreChartRing_eq_chartRing`.
   - Packaged `SegreJoinTwist` and Hermitian line-weight operations `HermLineWeight`
     (`zcomb`, `fsWeight`, `scaleMetric`, `tensorWeight`, `powWeight`).

2. **Segre-Join Generation Theorems (`generates_over_segre_join_twist`)**:
   - `generatesOver_segreJoin_twist`: exact algebraic Segre-join twist generation transfer from
     degree `pullDeg β + c • baseDeg (Sum.inl ())` over `segreJoin y` to degree `β + fun _ => c`
     over `y`.
   - `generated_of_segreJoin_nef_twist` & `segreJoin_twist_ample_combination`: Kleiman/nef-twist
     generation amplification with exact rational-twist degree identity.
   - `SmallSectionSegreBridge` & **`generates_over_segre_join_twist`**: connects Moriwaki bigness
     (`vol_Ar(L) > 0`) to small global sections generating over the Segre join twist with explicit
     norm and exponential small-section multiplicity bounds.

3. **`MoriwakiBigDatum`, Arithmetic Volume `vol_Ar(L)`, Metric Twists & Veronese Regrading**:
   - Arbitrary-dimension (`d : ℕ`, covering BOTH arithmetic curves `d = 0` and higher-dimensional
     varieties `d ≥ 1`) graded Hermitian section datum `MoriwakiBigDatum d` with polynomial rank
     ceiling, Bergman sup-vs-`L²` comparison, Northcott/Liouville `λ₁` floor, and Arakelov
     self-intersection `selfInt`.
   - Concrete arithmetic volumes `arithVol` (`vol_Ar`, `Filter.liminf`) and `arithVolUpper`
     (`Filter.limsup`), bigness predicate `IsArithBig` (`0 < vol_Ar`), metric twist
     `MoriwakiBigDatum.twistMetric`, Veronese power `MoriwakiBigDatum.veronesePower`, and
     bidirectional bridges with `Stage12SchurWeylLattices.GradedHermAlgebra`.

4. **Euclidean Packing, Separated Small-Section Counting & `moriwaki_rank_bounds_generic`**:
   - `separated_small_count_le` & `log_separated_small_count_le`: unconditional Euclidean
     sphere-packing bound `#S ≤ (2 R / δ + 1)^r` and exact `log(#S) ≤ r * (B + log 3)` under
     separation `‖x - y‖ ≥ exp(-B)`.
   - `ShiftRankDatum` & **`moriwaki_rank_bounds_generic`**: generic rank convergence
     `rk(L_q n) / (n^d / d!) → genDeg q`, quantitative upper/lower rank envelopes, and the
     unconditional `ShiftVolumeBound` upper ceiling
     `arithVolUpper ≤ 2 * (C + 1) * (d + 1) * (q + 1) * genDeg q`.

5. **Outright Moriwaki Bigness Theorem (`moriwakiBig_outright`)**:
   - `moriwakiBig_curve_case` (`d = 0`) & `moriwakiBig_higher_dim` (`d ≥ 1`).
   - **`moriwakiBig_outright`**: unified arbitrary-dimension (`∀ d : ℕ`) proof connecting positive
     arithmetic self-intersection `selfInt > 0` to `selfInt ≤ vol_Ar(L) ≤ vol_Ar_upper(L)`,
     `IsArithBig`, exponential growth `log(#smallSections(L^{⊗ k})) ≥ c₀ * k^(d+1)`, and
     unboundedly many strictly small nonzero global sections via Minkowski / `Stage12SchurWeylLattices`.
   - Two-sided finite arithmetic volume sandwich `moriwakiBig_two_sided_volAr` and metric-twist
     bigness stability `moriwakiBig_of_metric_twist`.

6. **Concrete Zero-Assumption Realizations (Proving Non-Vacuousness)**:
   - Projective space `ℙ^d` (`projSpaceMoriwakiBigDatum`, `projSpaceShiftRankDatum`,
     `projSpace_moriwakiBig_outright`) for every `d ≥ 1` and `α > 0`.
   - Arithmetic curve (`d = 0`, `arithCurveMoriwakiBigDatum`, `arithCurve_moriwakiBig_outright`).
   - CM Hermitian lattice symmetric-power realization (`cmHermSymPowMoriwakiBigDatum`).
   - Multi-projective Segre-join realization over `ℚ` (`stdMultiProjSegreJoinTwist`).

7. **Clean Bridges for M4 Wave 2 (`Stage14M4_AhSlimDeepStR`, `Stage14M4_CovolStepsBridge`)**:
   - `MoriwakiBigPkg`, `DeepStRMoriwakiInput`, `moriwakiBig_to_deepStR_input`, and
     `line_of_large_degree_of_moriwaki`.
   - `CovolStepMoriwakiInput`, `moriwaki_covol_steps_bridge`, and
     `moriwaki_stage12_L3_covolume_bridge`.
-/

noncomputable section

open Module Submodule Finset Real MeasureTheory Filter Set Topology
open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  linearIndependent_coe_basis det_gram_basis_pos covol_pos rk_pos_of_ne_bot
  covol_bot degAr_bot slope_le_muMax)
open RHDirect.Stage2SiegelReduction (covol_le_prod_norm lattice_inter_closedBall_finite
  lambda1 lambda1_pos lambda1_le_norm succMin succMin_pos)
open RHDirect.Stage11MoriwakiCovolume (arithDeg arithDeg_eq_rk_mul_slope scaleLat
  scaleLat_invariants slope_scaleLat h0Arith h0ArithStrict h0ArithStrict_le_h0Arith
  log_h0ArithStrict_lower_bound log_unitBallVol_ge unitBallVol unitBallVol_pos
  volume_ball_eq_unitBallVol
  moriwaki_small_section_count MultiIndex card_multiIndex card_multiIndex_pos
  diagLat diagLat_invariants symPowWeightedLat symPowMonomialLat
  arithDeg_symPowWeightedLat slope_symPowMonomialLat
  moriwaki_bigness_poly_rank_asymptotic moriwaki_bigness_symPow_asymptotic
  covolume_bound_of_section_norms)
open RHDirect.Stage12SchurWeylLattices (CMHermLattice GradedHermAlgebra
  moriwaki_big_small_sections moriwaki_exists_nonzero_small_section
  pow_div_factorial_le_choose choose_le_const_mul_pow
  projSpaceGradedHermAlgebra L3_hodge_covolume_bound
  L3_covolume_of_moriwaki_small_sections divLink_of_L3_and_dwork_chain)
open scoped BigOperators ENNReal InnerProductSpace Topology

universe u uK uS uΩ

namespace RHDirect.Stage14M4_MoriwakiBignessCore

/-! ## Section 1: Multi-Graded Coordinate Charts, Segre Join & Twist Algebra (`SegreJoinTwist`) -/

section SegreJoinAlgebra

/-! ### Multi-Graded Weight Vectors -/

/-- Standard basis weight vector on `K` supported at coordinate `k₀`. -/
def baseDeg {K : Type*} [DecidableEq K] (k₀ : K) : K → ℤ :=
  fun k => if k = k₀ then 1 else 0

@[simp]
lemma baseDeg_self {K : Type*} [DecidableEq K] (k₀ : K) : baseDeg k₀ k₀ = 1 :=
  if_pos rfl

@[simp]
lemma baseDeg_ne {K : Type*} [DecidableEq K] {k₀ k : K} (h : k ≠ k₀) : baseDeg k₀ k = 0 :=
  if_neg h

/-- Pullback of a multi-degree `β : K₂ → ℤ` along the right projection `K₁ ⊕ K₂ → K₂`,
vanishing on `K₁`. -/
def pullDeg {K₁ K₂ : Type*} (β : K₂ → ℤ) : K₁ ⊕ K₂ → ℤ :=
  Sum.elim (fun _ => 0) β

@[simp]
lemma pullDeg_inl {K₁ K₂ : Type*} (β : K₂ → ℤ) (k₁ : K₁) :
    pullDeg (K₁ := K₁) β (Sum.inl k₁) = 0 := rfl

@[simp]
lemma pullDeg_inr {K₁ K₂ : Type*} (β : K₂ → ℤ) (k₂ : K₂) :
    pullDeg (K₁ := K₁) β (Sum.inr k₂) = β k₂ := rfl

/-- Constant diagonal multi-degree shift `k ↦ c`. -/
def diagShift {K : Type*} (c : ℤ) : K → ℤ :=
  fun _ => c

@[simp]
lemma diagShift_apply {K : Type*} (c : ℤ) (k : K) : diagShift c k = c := rfl

lemma pullDeg_add {K₁ K₂ : Type*} (β₁ β₂ : K₂ → ℤ) :
    pullDeg (K₁ := K₁) (β₁ + β₂) = pullDeg (K₁ := K₁) β₁ + pullDeg (K₁ := K₁) β₂ := by
  funext u
  cases u <;> simp [pullDeg]

lemma pullDeg_zsmul {K₁ K₂ : Type*} (m : ℤ) (β : K₂ → ℤ) :
    pullDeg (K₁ := K₁) (m • β) = m • pullDeg (K₁ := K₁) β := by
  funext u
  cases u <;> simp [pullDeg]

lemma pullDeg_nsmul {K₁ K₂ : Type*} (m : ℕ) (β : K₂ → ℤ) :
    pullDeg (K₁ := K₁) (m • β) = m • pullDeg (K₁ := K₁) β := by
  funext u
  cases u <;> simp [pullDeg]

/-! ### Diamond-Free Chart Rings, Sections & Generation Over Explicit `RingHom`s -/

/-- A multi-projective chart choice `c₀ : ∀ k, ι k` is **admissible** at `y` when every
chosen coordinate `y ⟨k, c₀ k⟩` is nonzero. -/
def AdmissibleChart {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) (c₀ : ∀ k, ι k) : Prop :=
  ∀ k, y ⟨k, c₀ k⟩ ≠ 0

/-- Homogeneous chart quotient `y ⟨k, i⟩ / y ⟨k, c₀ k⟩` on the affine chart `c₀`. -/
def chartQuot {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) (c₀ : ∀ k, ι k) (p : Σ k, ι k) : Ω :=
  y p / y ⟨p.1, c₀ p.1⟩

/-- **Affine Chart Subring `chartRingOver φ y c₀ ⊆ Ω`**:
subring of `Ω` generated by the image of the explicit base ring homomorphism `φ : S →+* Ω`
and all affine chart quotients `y ⟨k, i⟩ / y ⟨k, c₀ k⟩`. Using an explicit `RingHom` rather
than `[Algebra S Ω]` completely avoids nested global `Algebra` instance diamonds. -/
def chartRingOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} {ι : K → Type*} (y : (Σ k, ι k) → Ω) (c₀ : ∀ k, ι k) : Subring Ω :=
  Subring.closure (Set.range φ ∪ Set.range (chartQuot y c₀))

lemma mem_chartRingOver_of_base {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} {ι : K → Type*} (y : (Σ k, ι k) → Ω) (c₀ : ∀ k, ι k) (r : S) :
    φ r ∈ chartRingOver φ y c₀ :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

lemma mem_chartRingOver_of_chartQuot {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} {ι : K → Type*} (y : (Σ k, ι k) → Ω) (c₀ : ∀ k, ι k) (p : Σ k, ι k) :
    chartQuot y c₀ p ∈ chartRingOver φ y c₀ :=
  Subring.subset_closure (Or.inr ⟨p, rfl⟩)

/-- **Multi-Graded Global Sections `secOver φ y β`**:
elements `s ∈ Ω` whose chart trivialization `s * ∏ k, y ⟨k, c₀ k⟩ ^ (-β k)` lies in the
affine chart ring `chartRingOver φ y c₀` for every admissible chart `c₀`. -/
def secOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β : K → ℤ) : Set Ω :=
  { s : Ω | ∀ c₀ : ∀ k, ι k, AdmissibleChart y c₀ →
      s * (∏ k : K, y ⟨k, c₀ k⟩ ^ (-β k)) ∈ chartRingOver φ y c₀ }

lemma zero_mem_secOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β : K → ℤ) :
    (0 : Ω) ∈ secOver φ y β := by
  intro c₀ _
  rw [zero_mul]
  exact (chartRingOver φ y c₀).zero_mem

lemma one_mem_secOver_zero {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) :
    (1 : Ω) ∈ secOver φ y (0 : K → ℤ) := by
  intro c₀ _
  simp [(chartRingOver φ y c₀).one_mem]

lemma add_mem_secOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β : K → ℤ)
    {s₁ s₂ : Ω} (h₁ : s₁ ∈ secOver φ y β) (h₂ : s₂ ∈ secOver φ y β) :
    s₁ + s₂ ∈ secOver φ y β := by
  intro c₀ hc₀
  rw [add_mul]
  exact (chartRingOver φ y c₀).add_mem (h₁ c₀ hc₀) (h₂ c₀ hc₀)

lemma neg_mem_secOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β : K → ℤ)
    {s : Ω} (hs : s ∈ secOver φ y β) :
    -s ∈ secOver φ y β := by
  intro c₀ hc₀
  rw [neg_mul]
  exact (chartRingOver φ y c₀).neg_mem (hs c₀ hc₀)

lemma base_mul_mem_secOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β : K → ℤ)
    (r : S) {s : Ω} (hs : s ∈ secOver φ y β) :
    φ r * s ∈ secOver φ y β := by
  intro c₀ hc₀
  rw [mul_assoc]
  exact (chartRingOver φ y c₀).mul_mem (mem_chartRingOver_of_base φ y c₀ r) (hs c₀ hc₀)

/-- Graded multiplication of multi-graded sections:
`secOver φ y β₁ · secOver φ y β₂ ⊆ secOver φ y (β₁ + β₂)`. -/
theorem mul_mem_secOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β₁ β₂ : K → ℤ)
    {s₁ s₂ : Ω} (h₁ : s₁ ∈ secOver φ y β₁) (h₂ : s₂ ∈ secOver φ y β₂) :
    s₁ * s₂ ∈ secOver φ y (β₁ + β₂) := by
  intro c₀ hc₀
  have hprod : (∏ k : K, y ⟨k, c₀ k⟩ ^ (-(β₁ + β₂) k)) =
      (∏ k : K, y ⟨k, c₀ k⟩ ^ (-β₁ k)) * (∏ k : K, y ⟨k, c₀ k⟩ ^ (-β₂ k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc₀ k)]
    congr 1
    simp [Pi.add_apply]
    ring
  rw [hprod, show s₁ * s₂ * ((∏ k : K, y ⟨k, c₀ k⟩ ^ (-β₁ k)) * (∏ k : K, y ⟨k, c₀ k⟩ ^ (-β₂ k))) =
    (s₁ * ∏ k : K, y ⟨k, c₀ k⟩ ^ (-β₁ k)) * (s₂ * ∏ k : K, y ⟨k, c₀ k⟩ ^ (-β₂ k)) by ring]
  exact (chartRingOver φ y c₀).mul_mem (h₁ c₀ hc₀) (h₂ c₀ hc₀)

/-- Graded powers of sections: `s ∈ secOver φ y β → s ^ m ∈ secOver φ y (m • β)`. -/
theorem pow_mem_secOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β : K → ℤ)
    {s : Ω} (hs : s ∈ secOver φ y β) (m : ℕ) :
    s ^ m ∈ secOver φ y ((m : ℕ) • β) := by
  induction m with
  | zero =>
    simpa only [pow_zero, zero_smul] using one_mem_secOver_zero φ y
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_secOver φ y (m • β) β ih hs

/-- Coordinate monomials `y ⟨k₀, i⟩` are global sections of degree `baseDeg k₀`. -/
theorem coord_mem_secOver_baseDeg {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} (y : (Σ k, ι k) → Ω)
    (k₀ : K) (i : ι k₀) :
    y ⟨k₀, i⟩ ∈ secOver φ y (baseDeg k₀) := by
  intro c₀ _
  have hprod : (∏ k : K, y ⟨k, c₀ k⟩ ^ (-baseDeg k₀ k)) = (y ⟨k₀, c₀ k₀⟩)⁻¹ := by
    rw [Finset.prod_eq_single k₀]
    · simp [baseDeg]
    · intro k _ hk
      simp [baseDeg, hk]
    · intro h
      exact absurd (Finset.mem_univ k₀) h
  rw [hprod, ← div_eq_mul_inv]
  exact mem_chartRingOver_of_chartQuot φ y c₀ ⟨k₀, i⟩

/-- **Global Generation Predicate `GeneratesOver φ y β η`**:
the finite family `η : Fin n → Ω` generates the line bundle of multi-degree `β` over every
admissible affine chart `c₀`, i.e., there exist coefficients `u : Fin n → Ω` in
`chartRingOver φ y c₀` with `(∑ j, u j * η j) * ∏ k, y ⟨k, c₀ k⟩ ^ (-β k) = 1`. -/
def GeneratesOver {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β : K → ℤ)
    {n : ℕ} (η : Fin n → Ω) : Prop :=
  ∀ c₀ : ∀ k, ι k, AdmissibleChart y c₀ →
    ∃ u : Fin n → Ω, (∀ j, u j ∈ chartRingOver φ y c₀) ∧
      (∑ j : Fin n, u j * η j) * (∏ k : K, y ⟨k, c₀ k⟩ ^ (-β k)) = 1

/-- Enlarging a generating family preserves `GeneratesOver`. -/
theorem generatesOver_of_reindex {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β : K → ℤ)
    {n m : ℕ} {η : Fin n → Ω} {η' : Fin m → Ω} (f : Fin n ↪ Fin m)
    (hcomp : ∀ j, η' (f j) = η j) (hgen : GeneratesOver φ y β η) :
    GeneratesOver φ y β η' := by
  classical
  intro c₀ hc₀
  obtain ⟨u, hu, hsum⟩ := hgen c₀ hc₀
  let u' : Fin m → Ω := fun i =>
    if hi : ∃ j : Fin n, f j = i then u hi.choose else 0
  refine ⟨u', fun i => ?_, ?_⟩
  · dsimp only [u']
    split_ifs with hi
    · exact hu hi.choose
    · exact (chartRingOver φ y c₀).zero_mem
  · have hsum_eq : ∑ i : Fin m, u' i * η' i = ∑ j : Fin n, u j * η j := by
      have h1 : ∑ i : Fin m, u' i * η' i =
          ∑ i ∈ Finset.univ.image f, u' i * η' i := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
        have hnot : ¬ ∃ j : Fin n, f j = i := by
          rintro ⟨j, rfl⟩
          exact hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
        simp [u', hnot]
      rw [h1, Finset.sum_image (fun a _ b _ hab => f.injective hab)]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hex : ∃ j' : Fin n, f j' = f j := ⟨j, rfl⟩
      have hch : hex.choose = j := f.injective hex.choose_spec
      simp only [u', dif_pos hex, hch, hcomp j]
    rw [hsum_eq]
    exact hsum

/-- The constant section `1` generates degree `0`. -/
theorem generatesOver_zero_of_one {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) :
    GeneratesOver φ y (0 : K → ℤ) (fun _ : Fin 1 => (1 : Ω)) := by
  intro c₀ _
  refine ⟨fun _ => 1, fun _ => (chartRingOver φ y c₀).one_mem, ?_⟩
  simp

/-- **Tensor / Product Generation Theorem (`generatesOver_mul`)**:
if `η₁ : Fin n₁ → Ω` generates in degree `β₁` and `η₂ : Fin n₂ → Ω` generates in degree `β₂`,
then the product family `i ↦ η₁ (e i).1 * η₂ (e i).2` generates in degree `β₁ + β₂`. -/
theorem generatesOver_mul {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] {ι : K → Type*} (y : (Σ k, ι k) → Ω) (β₁ β₂ : K → ℤ)
    {n₁ n₂ : ℕ} {η₁ : Fin n₁ → Ω} {η₂ : Fin n₂ → Ω}
    (h₁ : GeneratesOver φ y β₁ η₁) (h₂ : GeneratesOver φ y β₂ η₂) :
    let e : Fin (n₁ * n₂) ≃ Fin n₁ × Fin n₂ := finProdFinEquiv.symm
    GeneratesOver φ y (β₁ + β₂) (fun i => η₁ (e i).1 * η₂ (e i).2) := by
  intro e c₀ hc₀
  obtain ⟨u₁, hu₁, hs₁⟩ := h₁ c₀ hc₀
  obtain ⟨u₂, hu₂, hs₂⟩ := h₂ c₀ hc₀
  refine ⟨fun i => u₁ (e i).1 * u₂ (e i).2,
    fun i => (chartRingOver φ y c₀).mul_mem (hu₁ _) (hu₂ _), ?_⟩
  have hsum : ∑ i : Fin (n₁ * n₂), (u₁ (e i).1 * u₂ (e i).2) * (η₁ (e i).1 * η₂ (e i).2) =
      (∑ j₁ : Fin n₁, u₁ j₁ * η₁ j₁) * (∑ j₂ : Fin n₂, u₂ j₂ * η₂ j₂) := by
    rw [Fintype.sum_equiv e _ (fun p : Fin n₁ × Fin n₂ => (u₁ p.1 * u₂ p.2) * (η₁ p.1 * η₂ p.2))
      (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    ring
  have hprod : (∏ k : K, y ⟨k, c₀ k⟩ ^ (-(β₁ + β₂) k)) =
      (∏ k : K, y ⟨k, c₀ k⟩ ^ (-β₁ k)) * (∏ k : K, y ⟨k, c₀ k⟩ ^ (-β₂ k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc₀ k)]
    congr 1
    simp [Pi.add_apply]
    ring
  rw [hsum, hprod]
  calc ((∑ j₁, u₁ j₁ * η₁ j₁) * (∑ j₂, u₂ j₂ * η₂ j₂)) *
        ((∏ k, y ⟨k, c₀ k⟩ ^ (-β₁ k)) * (∏ k, y ⟨k, c₀ k⟩ ^ (-β₂ k)))
      = ((∑ j₁, u₁ j₁ * η₁ j₁) * (∏ k, y ⟨k, c₀ k⟩ ^ (-β₁ k))) *
        ((∑ j₂, u₂ j₂ * η₂ j₂) * (∏ k, y ⟨k, c₀ k⟩ ^ (-β₂ k))) := by ring
    _ = 1 * 1 := by rw [hs₁, hs₂]
    _ = 1 := one_mul 1

/-- Coordinate sections `y ⟨k₀, ·⟩` generate degree `baseDeg k₀` when `ι k₀` is finite. -/
theorem generatesOver_coords_baseDeg {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} (k₀ : K) [Fintype (ι k₀)]
    (y : (Σ k, ι k) → Ω) :
    let e : Fin (Fintype.card (ι k₀)) ≃ ι k₀ := (Fintype.equivFin (ι k₀)).symm
    GeneratesOver φ y (baseDeg k₀) (fun j => y ⟨k₀, e j⟩) := by
  classical
  intro e c₀ hc₀
  let j₀ : Fin (Fintype.card (ι k₀)) := e.symm (c₀ k₀)
  refine ⟨fun j => if j = j₀ then 1 else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact (chartRingOver φ y c₀).one_mem
    · exact (chartRingOver φ y c₀).zero_mem
  · have hsum : ∑ j : Fin (Fintype.card (ι k₀)), (if j = j₀ then (1 : Ω) else 0) * y ⟨k₀, e j⟩ =
        y ⟨k₀, c₀ k₀⟩ := by
      rw [Finset.sum_eq_single j₀]
      · simp [j₀]
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ j₀) h
    have hprod : (∏ k : K, y ⟨k, c₀ k⟩ ^ (-baseDeg k₀ k)) = (y ⟨k₀, c₀ k₀⟩)⁻¹ := by
      rw [Finset.prod_eq_single k₀]
      · simp [baseDeg]
      · intro k _ hk
        simp [baseDeg, hk]
      · intro h
        exact absurd (Finset.mem_univ k₀) h
    rw [hsum, hprod, mul_inv_cancel₀ (hc₀ k₀)]

/-! ### The Segre Join Construction & Exact Chart-Ring Containment -/

/-- Index family for the Segre join `ℙ(⨂_k V_k) × ∏_k ℙ(V_k)`:
the `Sum.inl ()` factor carries the Segre product coordinates `∀ k, ι k`,
and each `Sum.inr k` factor retains the original coordinates `ι k`. -/
def SegreIdx {K : Type uK} (ι : K → Type uK) : Unit ⊕ K → Type uK :=
  Sum.elim (fun _ : Unit => ∀ k, ι k) ι

/-- Segre monomial coordinates `f ↦ ∏ k, y ⟨k, f k⟩`. -/
def segreVec {K : Type uK} [Fintype K] {ι : K → Type uK} {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) : Ω :=
  ∏ k : K, y ⟨k, f k⟩

/-- **The Segre Join Coordinate Tuple `segreJoin y`**:
adjoins the Segre embedding `segreVec y` as a new `Sum.inl ()` projective factor alongside `y`. -/
def segreJoin {K : Type uK} [Fintype K] {ι : K → Type uK} {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) : (Σ u : Unit ⊕ K, SegreIdx ι u) → Ω
  | ⟨Sum.inl _, f⟩ => segreVec y f
  | ⟨Sum.inr k, i⟩ => y ⟨k, i⟩

/-- Diagonal Segre chart lifting a chart choice `c₀ : ∀ k, ι k` to `Unit ⊕ K`. -/
def segreChart {K : Type uK} {ι : K → Type uK} (c₀ : ∀ k, ι k) : ∀ u : Unit ⊕ K, SegreIdx ι u
  | Sum.inl _ => c₀
  | Sum.inr k => c₀ k

lemma segreVec_ne_zero {K : Type uK} [Fintype K] {ι : K → Type uK} {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) {c₀ : ∀ k, ι k} (hc₀ : AdmissibleChart y c₀) :
    segreVec y c₀ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => hc₀ k

lemma segreChart_admissible {K : Type uK} [Fintype K] {ι : K → Type uK} {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) {c₀ : ∀ k, ι k} (hc₀ : AdmissibleChart y c₀) :
    AdmissibleChart (segreJoin y) (segreChart c₀) := by
  rintro (u | k)
  · exact segreVec_ne_zero y hc₀
  · exact hc₀ k

/-- **Key Ring-Theoretic Containment (`segreChartRing_le_chartRing`)**:
every affine chart quotient on the Segre join factor `Sum.inl ()` factors as a finite product
of chart quotients on the `K` factors, so
`chartRingOver φ (segreJoin y) (segreChart c₀) ≤ chartRingOver φ y c₀`. -/
theorem segreChartRing_le_chartRing {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type uK} [Fintype K] {ι : K → Type uK} (y : (Σ k, ι k) → Ω) (c₀ : ∀ k, ι k) :
    chartRingOver φ (segreJoin y) (segreChart c₀) ≤ chartRingOver φ y c₀ := by
  unfold chartRingOver
  refine Subring.closure_le.mpr ?_
  rintro x (⟨r, rfl⟩ | ⟨⟨u | k, idx⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  · change segreVec y idx / segreVec y c₀ ∈ Subring.closure _
    unfold segreVec
    rw [← Finset.prod_div_distrib]
    exact Subring.prod_mem _ fun k _ =>
      Subring.subset_closure (Or.inr ⟨⟨k, idx k⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨⟨k, idx⟩, rfl⟩)

/-- **Exact Chart-Ring Equality (`segreChartRing_eq_chartRing`)**:
the diagonal Segre chart ring coincides identically with the base chart ring:
`chartRingOver φ (segreJoin y) (segreChart c₀) = chartRingOver φ y c₀`. -/
theorem segreChartRing_eq_chartRing {S Ω : Type*} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type uK} [Fintype K] {ι : K → Type uK} (y : (Σ k, ι k) → Ω) (c₀ : ∀ k, ι k) :
    chartRingOver φ (segreJoin y) (segreChart c₀) = chartRingOver φ y c₀ := by
  refine le_antisymm (segreChartRing_le_chartRing φ y c₀) ?_
  unfold chartRingOver
  refine Subring.closure_le.mpr ?_
  rintro x (⟨r, rfl⟩ | ⟨⟨k, i⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨⟨Sum.inr k, i⟩, rfl⟩)

/-- **Exact Segre-Twist Trivialization Product Identity (`segreTwist_prod_zpow`)**:
on every admissible chart `c₀`,
`∏ u : Unit ⊕ K, segreJoin y ⟨u, segreChart c₀ u⟩ ^ (-(pullDeg β + c • baseDeg (Sum.inl ())) u)
  = ∏ k : K, y ⟨k, c₀ k⟩ ^ (-(β k + c))`. -/
theorem segreTwist_prod_zpow {K : Type uK} [Fintype K] [DecidableEq K]
    {ι : K → Type uK} {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) (β : K → ℤ) (c : ℤ)
    {c₀ : ∀ k, ι k} (hc₀ : AdmissibleChart y c₀) :
    (∏ u : Unit ⊕ K,
        segreJoin y ⟨u, segreChart c₀ u⟩ ^
          (-((pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ()) : Unit ⊕ K → ℤ) u))) =
      ∏ k : K, y ⟨k, c₀ k⟩ ^ (-(β k + c)) := by
  set D : Unit ⊕ K → ℤ := pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ()) with hD
  have hD_inl : D (Sum.inl ()) = c := by
    simp [hD, pullDeg, baseDeg]
  have hD_inr : ∀ k : K, D (Sum.inr k) = β k := by
    intro k
    simp [hD, pullDeg, baseDeg]
  rw [Fintype.prod_sum_type]
  have hleft : (∏ u : Unit, segreJoin y ⟨Sum.inl u, segreChart c₀ (Sum.inl u)⟩ ^ (-D (Sum.inl u))) =
      (∏ k : K, y ⟨k, c₀ k⟩) ^ (-c) := by
    rw [Fintype.prod_unique]
    change segreVec y c₀ ^ (-D (Sum.inl ())) = _
    rw [hD_inl]
    rfl
  rw [hleft, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  change y ⟨k, c₀ k⟩ ^ (-c) * y ⟨k, c₀ k⟩ ^ (-D (Sum.inr k)) = y ⟨k, c₀ k⟩ ^ (-(β k + c))
  rw [hD_inr k, ← zpow_add₀ (hc₀ k)]
  congr 1
  ring

/-- **Packaged Segre-Join Twist Graded Algebra Structure (`SegreJoinTwist`)**:
encapsulates a multi-projective coordinate tuple `y` over an explicit base ring homomorphism
`φ : S →+* Ω`, base multi-degree `β : K → ℤ`, and Segre twist integer `c : ℤ`, together with
all graded twist operations (`twistedDeg`, `segreDeg`, `twistBy`, `scaleBy`, `addTwist`). -/
structure SegreJoinTwist (S : Type uS) (Ω : Type uΩ) [CommRing S] [Field Ω] (φ : S →+* Ω)
    (K : Type uK) [Fintype K] [DecidableEq K] (ι : K → Type uK) where
  /-- Coordinate point `y : (Σ k, ι k) → Ω`. -/
  y : (Σ k, ι k) → Ω
  /-- Nondegeneracy: every projective factor has a nonzero coordinate. -/
  nondegenerate : ∀ k : K, ∃ i : ι k, y ⟨k, i⟩ ≠ 0
  /-- Base multi-degree `β : K → ℤ`. -/
  baseWeight : K → ℤ
  /-- Segre twist integer `c : ℤ`. -/
  twist : ℤ

namespace SegreJoinTwist

variable {S : Type uS} {Ω : Type uΩ} [CommRing S] [Field Ω] {φ : S →+* Ω}
variable {K : Type uK} [Fintype K] [DecidableEq K] {ι : K → Type uK}

/-- Target multi-degree `β + fun _ => c` on `K`. -/
def twistedDeg (T : SegreJoinTwist S Ω φ K ι) : K → ℤ :=
  T.baseWeight + diagShift T.twist

/-- Lifted multi-degree `pullDeg β + c • baseDeg (Sum.inl ())` on `Unit ⊕ K`. -/
def segreDeg (T : SegreJoinTwist S Ω φ K ι) : Unit ⊕ K → ℤ :=
  pullDeg (K₁ := Unit) T.baseWeight + T.twist • baseDeg (Sum.inl ())

/-- Additional Segre twist by `c' : ℤ`. -/
def twistBy (T : SegreJoinTwist S Ω φ K ι) (c' : ℤ) : SegreJoinTwist S Ω φ K ι where
  y := T.y
  nondegenerate := T.nondegenerate
  baseWeight := T.baseWeight
  twist := T.twist + c'

/-- Positive integer scaling (Veronese tensor power) `m • (β, c)`. -/
def scaleBy (T : SegreJoinTwist S Ω φ K ι) (m : ℕ) : SegreJoinTwist S Ω φ K ι where
  y := T.y
  nondegenerate := T.nondegenerate
  baseWeight := m • T.baseWeight
  twist := (m : ℤ) * T.twist

/-- Graded addition of two twists on the same coordinate point `y`. -/
def addWeights (T : SegreJoinTwist S Ω φ K ι) (β' : K → ℤ) (c' : ℤ) :
    SegreJoinTwist S Ω φ K ι where
  y := T.y
  nondegenerate := T.nondegenerate
  baseWeight := T.baseWeight + β'
  twist := T.twist + c'

lemma twistedDeg_twistBy (T : SegreJoinTwist S Ω φ K ι) (c' : ℤ) :
    (T.twistBy c').twistedDeg = T.twistedDeg + diagShift c' := by
  funext k
  simp [twistedDeg, twistBy, diagShift]
  ring

lemma twistedDeg_scaleBy (T : SegreJoinTwist S Ω φ K ι) (m : ℕ) :
    (T.scaleBy m).twistedDeg = m • T.twistedDeg := by
  funext k
  simp [twistedDeg, scaleBy, diagShift, mul_add]

lemma segreDeg_scaleBy (T : SegreJoinTwist S Ω φ K ι) (m : ℕ) :
    (T.scaleBy m).segreDeg = m • T.segreDeg := by
  funext u
  cases u <;> simp [segreDeg, scaleBy, pullDeg, baseDeg, mul_assoc]

lemma exists_admissibleChart (T : SegreJoinTwist S Ω φ K ι) :
    ∃ c₀ : ∀ k, ι k, AdmissibleChart T.y c₀ := by
  choose c₀ hc₀ using T.nondegenerate
  exact ⟨c₀, hc₀⟩

/-- Sections of `T.segreDeg` on `segreJoin T.y` automatically restrict to sections of
`T.twistedDeg` on `T.y`. -/
theorem secOver_segreJoin_subset (T : SegreJoinTwist S Ω φ K ι) :
    secOver φ (segreJoin T.y) T.segreDeg ⊆ secOver φ T.y T.twistedDeg := by
  intro s hs c₀ hc₀
  have hmem := hs (segreChart c₀) (segreChart_admissible T.y hc₀)
  have hle := segreChartRing_le_chartRing φ T.y c₀ hmem
  have hprod := segreTwist_prod_zpow T.y T.baseWeight T.twist hc₀
  change s * (∏ k : K, T.y ⟨k, c₀ k⟩ ^ (-(T.baseWeight k + T.twist))) ∈ chartRingOver φ T.y c₀
  rw [← hprod]
  exact hle

/-- Exact pull-degree section inclusion:
`secOver φ (segreJoin T.y) (pullDeg β) ⊆ secOver φ T.y β`. -/
theorem secOver_segreJoin_pullDeg_subset (T : SegreJoinTwist S Ω φ K ι) (β : K → ℤ) :
    secOver φ (segreJoin T.y) (pullDeg (K₁ := Unit) β) ⊆ secOver φ T.y β := by
  let T₀ : SegreJoinTwist S Ω φ K ι := ⟨T.y, T.nondegenerate, β, 0⟩
  have hsub := T₀.secOver_segreJoin_subset
  have h1 : T₀.segreDeg = pullDeg (K₁ := Unit) β := by
    simp [segreDeg, T₀]
  have h2 : T₀.twistedDeg = β := by
    funext k; simp [twistedDeg, diagShift, T₀]
  rwa [h1, h2] at hsub

end SegreJoinTwist

/-! ### Hermitian Line Weights & Linear Combinations (`HermLineWeight`) -/

/-- **Multi-Graded Hermitian Line Weight (`HermLineWeight K ι`)**:
combines a multi-degree `a : K → ℤ` with a positive archimedean Hermitian metric weight
`h : ((Σ k, ι k) → ℂ) → ℝ` satisfying homogeneous scaling
`h (fun ⟨k, i⟩ => c k * z ⟨k, i⟩) = (∏ k, ‖c k‖ ^ a k) * h z` for all `c : K → ℂ` with `c k ≠ 0`. -/
structure HermLineWeight (K : Type*) [Fintype K] (ι : K → Type*) where
  deg : K → ℤ
  wt : ((Σ k, ι k) → ℂ) → ℝ
  wt_pos : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 < wt z
  wt_homog : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    wt (fun p => c p.1 * z p) = (∏ k : K, ‖c k‖ ^ deg k) * wt z

namespace HermLineWeight

variable {K : Type*} [Fintype K] {ι : K → Type*}

/-- Integer linear combination `p • A + q • B` of two Hermitian line weights
(matching `HermLine.zcomb` in the Moriwaki rank-bound pipeline). -/
def zcomb (A B : HermLineWeight K ι) (p q : ℤ) : HermLineWeight K ι where
  deg := p • A.deg + q • B.deg
  wt z := A.wt z ^ p * B.wt z ^ q
  wt_pos z hz := mul_pos (zpow_pos (A.wt_pos z hz) p) (zpow_pos (B.wt_pos z hz) q)
  wt_homog c z hc := by
    rw [A.wt_homog c z hc, B.wt_homog c z hc, mul_zpow, mul_zpow,
      ← Finset.prod_zpow, ← Finset.prod_zpow]
    have hprod : (∏ k : K, (‖c k‖ ^ A.deg k) ^ p) * (∏ k : K, (‖c k‖ ^ B.deg k) ^ q) =
        ∏ k : K, ‖c k‖ ^ (p • A.deg + q • B.deg) k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hck : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hck]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      ring
    calc ((∏ k : K, (‖c k‖ ^ A.deg k) ^ p) * A.wt z ^ p) *
          ((∏ k : K, (‖c k‖ ^ B.deg k) ^ q) * B.wt z ^ q)
        = ((∏ k : K, (‖c k‖ ^ A.deg k) ^ p) * (∏ k : K, (‖c k‖ ^ B.deg k) ^ q)) *
          (A.wt z ^ p * B.wt z ^ q) := by ring
      _ = (∏ k : K, ‖c k‖ ^ (p • A.deg + q • B.deg) k) * (A.wt z ^ p * B.wt z ^ q) := by
          rw [hprod]

/-- Constant archimedean metric twist `z ↦ exp(-t) * A.wt z` (preserving multi-degree `A.deg`). -/
def scaleMetric (A : HermLineWeight K ι) (t : ℝ) : HermLineWeight K ι where
  deg := A.deg
  wt z := Real.exp (-t) * A.wt z
  wt_pos z hz := mul_pos (Real.exp_pos _) (A.wt_pos z hz)
  wt_homog c z hc := by
    rw [A.wt_homog c z hc]
    ring

/-- Canonical Fubini–Study Hermitian line weight on `∏_k ℙ(ℂ^{ι k})` of multi-degree `1`:
`h_FS(z) = ∏_k √(∑_i ‖z_{k,i}‖²)`. -/
def fsWeight [∀ k, Fintype (ι k)] : HermLineWeight K ι where
  deg := fun _ => 1
  wt z := ∏ k : K, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2)
  wt_pos z hz := by
    refine Finset.prod_pos fun k _ => Real.sqrt_pos.mpr ?_
    obtain ⟨i₀, hi₀⟩ := hz k
    exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hi₀))
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖) (Finset.mem_univ i₀))
  wt_homog c z _ := by
    have hfac : ∀ k : K,
        Real.sqrt (∑ i : ι k, ‖c k * z ⟨k, i⟩‖ ^ 2) =
          ‖c k‖ * Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) := by
      intro k
      have hsum : ∑ i : ι k, ‖c k * z ⟨k, i⟩‖ ^ 2 =
          ‖c k‖ ^ 2 * ∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, mul_pow]
      rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    simp_rw [hfac, Finset.prod_mul_distrib, zpow_one]

/-- Segre-join pullback of a Hermitian line weight twisted by `c` copies of Fubini–Study. -/
def segreTwistWeight [∀ k, Fintype (ι k)] (A : HermLineWeight K ι) (c : ℤ) :
    HermLineWeight K ι :=
  A.zcomb fsWeight 1 c

lemma segreTwistWeight_deg [∀ k, Fintype (ι k)] (A : HermLineWeight K ι) (c : ℤ) :
    (A.segreTwistWeight c).deg = A.deg + diagShift c := by
  funext k
  simp [segreTwistWeight, zcomb, fsWeight, diagShift]

end HermLineWeight

end SegreJoinAlgebra

/-! ## Section 2: Segre-Join Generation Theorems (`generatesOver_segreJoin_twist`) -/

section SegreJoinGeneration

/-- **Algebraic Segre-Join Twist Generation Theorem (`generatesOver_segreJoin_twist`)**:
for any base commutative ring `S`, field `Ω`, explicit homomorphism `φ : S →+* Ω`,
finite multi-projective coordinate tuple `y`, weight `β : K → ℤ`, twist `c : ℤ`, and finite
section family `η : Fin n → Ω`:
if `η` generates over the Segre join `segreJoin y` in degree `pullDeg β + c • baseDeg (Sum.inl ())`,
then `η` generates over `y` in the diagonally twisted degree `β + fun _ => c`. -/
theorem generatesOver_segreJoin_twist {S : Type uS} {Ω : Type uΩ} [CommRing S] [Field Ω] (φ : S →+* Ω)
    {K : Type uK} [Fintype K] [DecidableEq K] {ι : K → Type uK}
    (y : (Σ k, ι k) → Ω) (β : K → ℤ) (c : ℤ) {n : ℕ} (η : Fin n → Ω)
    (h : GeneratesOver φ (segreJoin y)
      (pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ())) η) :
    GeneratesOver φ y (β + diagShift c) η := by
  intro c₀ hc₀
  obtain ⟨u, hu, hsum⟩ := h (segreChart c₀) (segreChart_admissible y hc₀)
  refine ⟨u, fun j => segreChartRing_le_chartRing φ y c₀ (hu j), ?_⟩
  have hprod := segreTwist_prod_zpow y β c hc₀
  rw [hprod] at hsum
  exact hsum

/-- Packaged `SegreJoinTwist` version of `generatesOver_segreJoin_twist`. -/
theorem SegreJoinTwist.generates_twisted {S : Type uS} {Ω : Type uΩ} [CommRing S] [Field Ω]
    {φ : S →+* Ω} {K : Type uK} [Fintype K] [DecidableEq K] {ι : K → Type uK}
    (T : SegreJoinTwist S Ω φ K ι) {n : ℕ} (η : Fin n → Ω)
    (h : GeneratesOver φ (segreJoin T.y) T.segreDeg η) :
    GeneratesOver φ T.y T.twistedDeg η :=
  generatesOver_segreJoin_twist φ T.y T.baseWeight T.twist η h

/-- **Kleiman / Nef-Twist Segre-Join Generation Theorem (`generated_of_segreJoin_nef_twist`)**:
given a multi-degree `α : K → ℤ`, rational positivity parameter `t > 0`, and a Segre-join
generation witness at `(a', m)` with `1 ≤ a'`, `(m : ℚ) = a' * t`, transfers both global
generation and section membership directly to `a' • α + diagShift m` on `y`. -/
theorem generated_of_segreJoin_nef_twist {S : Type uS} {Ω : Type uΩ} [CommRing S] [Field Ω]
    (φ : S →+* Ω) {K : Type uK} [Fintype K] [DecidableEq K] {ι : K → Type uK}
    (y : (Σ k, ι k) → Ω) (α : K → ℤ) (a' : ℕ) (m : ℤ) {n : ℕ} (η : Fin n → Ω)
    (hsec : ∀ j, η j ∈ secOver φ (segreJoin y)
      (a' • pullDeg (K₁ := Unit) α + m • baseDeg (Sum.inl ())))
    (hgen : GeneratesOver φ (segreJoin y)
      (a' • pullDeg (K₁ := Unit) α + m • baseDeg (Sum.inl ())) η)
    (hnd : ∀ k : K, ∃ i : ι k, y ⟨k, i⟩ ≠ 0) :
    (∀ j, η j ∈ secOver φ y (a' • α + diagShift m)) ∧
    GeneratesOver φ y (a' • α + diagShift m) η := by
  have heq : a' • pullDeg (K₁ := Unit) α + m • baseDeg (Sum.inl ()) =
      pullDeg (K₁ := Unit) (a' • α) + m • baseDeg (Sum.inl ()) := by
    rw [pullDeg_nsmul]
  rw [heq] at hsec hgen
  let T : SegreJoinTwist S Ω φ K ι := ⟨y, hnd, a' • α, m⟩
  exact ⟨fun j => T.secOver_segreJoin_subset (hsec j), T.generates_twisted η hgen⟩

/-- **Exact Kleiman-Ampleness Degree Combination Identity (`segreJoin_twist_ample_combination`)**:
if `1 ≤ a'`, `1 ≤ b`, `1 ≤ a`, and `(m : ℚ) = a' * ((a : ℚ) / (2 * b))`, then
`((2 * b : ℕ) : ℤ) • (a' • α + diagShift m) + diagShift ((a' * a : ℕ) : ℤ)
  = (2 * a') • (b • α + diagShift (a : ℤ))`,
matching the exact degree-amplification step of Kleiman's ampleness criterion. -/
theorem segreJoin_twist_ample_combination {K : Type*} (α : K → ℤ)
    {a' b a : ℕ} {m : ℤ} (hb : 1 ≤ b)
    (hm : (m : ℚ) = (a' : ℚ) * ((a : ℚ) / (2 * (b : ℚ)))) :
    ((2 * b : ℕ) : ℤ) • (a' • α + diagShift m) + diagShift ((a' * a : ℕ) : ℤ) =
      (2 * a') • (b • α + diagShift (a : ℤ)) := by
  have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmQ : (2 * (b : ℚ)) * (m : ℚ) = (a' : ℚ) * (a : ℚ) := by
    rw [hm]
    field_simp [hbQ]
  have hmZ : (2 * (b : ℤ)) * m = (a' : ℤ) * (a : ℤ) := by
    exact_mod_cast hmQ
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, diagShift, smul_eq_mul, nsmul_eq_mul,
    Pi.mul_apply, Pi.natCast_apply]
  push_cast
  linear_combination hmZ

/-- **Iterated Power Generation Over the Segre Join Twist (`generatesOver_segreJoin_twist_pow`)**:
if `η : Fin n → Ω` generates over `segreJoin y` in degree `pullDeg β + c • baseDeg (Sum.inl ())`,
then for every `r : ℕ`, there exists an explicit finite product family of length `n ^ r`
generating over `y` in degree `r • (β + diagShift c)`. -/
theorem generatesOver_segreJoin_twist_pow {S : Type uS} {Ω : Type uΩ} [CommRing S] [Field Ω]
    (φ : S →+* Ω) {K : Type uK} [Fintype K] [DecidableEq K] {ι : K → Type uK}
    (y : (Σ k, ι k) → Ω) (β : K → ℤ) (c : ℤ) {n : ℕ} (η : Fin n → Ω)
    (h : GeneratesOver φ (segreJoin y)
      (pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ())) η) (r : ℕ) :
    ∃ ηr : Fin (n ^ r) → Ω, GeneratesOver φ y (r • (β + diagShift c)) ηr := by
  have h1 : GeneratesOver φ y (β + diagShift c) η :=
    generatesOver_segreJoin_twist φ y β c η h
  induction r with
  | zero =>
    refine ⟨fun _ => 1, ?_⟩
    intro c₀ _
    refine ⟨fun _ => 1, fun _ => (chartRingOver φ y c₀).one_mem, ?_⟩
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul, zero_smul, Pi.zero_apply, neg_zero,
      zpow_zero, Finset.prod_const_one, Finset.card_univ, Fintype.card_fin, pow_zero,
      Nat.cast_one]
  | succ r ih =>
    obtain ⟨ηr, hηr⟩ := ih
    rw [pow_succ, succ_nsmul]
    exact ⟨_, generatesOver_mul φ y (r • (β + diagShift c)) (β + diagShift c) hηr h1⟩

end SegreJoinGeneration

/-! ## Section 3: `MoriwakiBigDatum`, Arithmetic Volume `vol_Ar(L)` & Bigness Criterion -/

section MoriwakiBigDatumAndVolume

/-! ### Unconditional Euclidean Sphere-Packing Upper Bound for Separated Sets -/

section EuclideanPacking

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Unconditional Separated-Set Sphere-Packing Upper Bound (`separated_small_count_le`)**:
for any nonzero discrete Euclidean lattice `L ⊂ E` (`r = rk L`, `L ≠ ⊥`), any radius `R ≥ 0`,
any separation threshold `δ > 0`, and any finite subset `S ⊆ L` lying in `closedBall 0 R`
whose distinct points satisfy `δ ≤ ‖x - y‖`:
$$(\#S : \mathbb{R}) \le \left(\frac{2 R}{\delta} + 1\right)^r.$$ -/
theorem separated_small_count_le (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (S : Finset E) (hSL : ∀ x ∈ S, x ∈ L) (hSR : ∀ x ∈ S, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ ‖x - y‖) :
    (S.card : ℝ) ≤ (2 * R / δ + 1) ^ (rk L) := by
  classical
  let r : ℕ := rk L
  have hr_pos : 0 < r := rk_pos_of_ne_bot L hL0
  let ρ : ℝ := δ / 2
  have hρ_pos : 0 < ρ := half_pos hδ
  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  have hdimV : Module.finrank ℝ V = r := (finrank_int_eq_finrank_real_span L).symm
  let e : OrthonormalBasis (Fin r) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivOfCardEq (by simp [hdimV]))
  let Φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := e.repr
  let c : E → EuclideanSpace ℝ (Fin r) := fun v =>
    if hv : v ∈ L then Φ ⟨v, Submodule.subset_span hv⟩ else 0
  have hc_disj : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      Disjoint (Metric.ball (c v) ρ) (Metric.ball (c w) ρ) := by
    intro v hv w hw hvw
    apply Metric.ball_disjoint_ball
    have hvL : v ∈ L := hSL v hv
    have hwL : w ∈ L := hSL w hw
    simp only [c, dif_pos hvL, dif_pos hwL, dist_eq_norm, ← map_sub]
    have hnorm_eq : ‖Φ (⟨v, Submodule.subset_span hvL⟩ - ⟨w, Submodule.subset_span hwL⟩)‖ =
        ‖v - w‖ := by
      rw [Φ.norm_map]; rfl
    rw [hnorm_eq]
    have hdist := hsep v hv w hw hvw
    dsimp only [ρ]
    linarith
  have hc_sub : ∀ v ∈ S,
      Metric.ball (c v) ρ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin r)) (R + ρ) := by
    intro v hv x hx
    have hvL : v ∈ L := hSL v hv
    have hvR : ‖v‖ ≤ R := hSR v hv
    have hx_dist : ‖x - c v‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hcv_norm : ‖c v‖ = ‖v‖ := by
      simp only [c, dif_pos hvL]
      exact Φ.norm_map ⟨v, Submodule.subset_span hvL⟩
    rw [Metric.mem_ball, dist_zero_right]
    have hsplit : x = (x - c v) + c v := by abel
    calc ‖x‖ = ‖(x - c v) + c v‖ := congrArg norm hsplit
      _ ≤ ‖x - c v‖ + ‖c v‖ := norm_add_le _ _
      _ < ρ + R := by linarith [hx_dist, hcv_norm, hvR]
      _ = R + ρ := add_comm _ _
  have hball_vol : ∀ (x₀ : EuclideanSpace ℝ (Fin r)) {rad : ℝ}, 0 ≤ rad →
      volume (Metric.ball x₀ rad) = ENNReal.ofReal (unitBallVol r * rad ^ r) := by
    intro x₀ rad hrad
    have htrans : volume (Metric.ball x₀ rad) =
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) rad) := by
      have heq : Metric.ball x₀ rad = (fun x => x + (-x₀)) ⁻¹' Metric.ball 0 rad := by
        ext x; simp [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg]
      rw [heq, MeasureTheory.measure_preimage_add_right]
    rw [htrans, volume_ball_eq_unitBallVol hr_pos hrad]
  have hunion_le : ∑ v ∈ S, volume (Metric.ball (c v) ρ) ≤
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) (R + ρ)) := by
    have hmeas : ∀ v ∈ S, MeasurableSet (Metric.ball (c v) ρ) :=
      fun _ _ => measurableSet_ball
    rw [← MeasureTheory.measure_biUnion_finset (fun v hv w hw hvw => hc_disj v hv w hw hvw) hmeas]
    exact measure_mono (Set.iUnion₂_subset hc_sub)
  have hsum_eq : ∑ v ∈ S, volume (Metric.ball (c v) ρ) =
      ENNReal.ofReal ((S.card : ℝ) * (unitBallVol r * ρ ^ r)) := by
    rw [Finset.sum_congr rfl (fun v _ => hball_vol (c v) hρ_pos.le), Finset.sum_const, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rw [hsum_eq, hball_vol 0 (add_nonneg hR hρ_pos.le)] at hunion_le
  have hreal : (S.card : ℝ) * (unitBallVol r * ρ ^ r) ≤ unitBallVol r * (R + ρ) ^ r :=
    (ENNReal.ofReal_le_ofReal_iff
      (mul_pos (unitBallVol_pos r) (pow_pos (add_pos_of_nonneg_of_pos hR hρ_pos) r)).le).mp
      hunion_le
  have hω_pos : 0 < unitBallVol r := unitBallVol_pos r
  have hρr_pos : 0 < ρ ^ r := pow_pos hρ_pos r
  have hpow_le : (S.card : ℝ) * ρ ^ r ≤ (R + ρ) ^ r := by nlinarith
  have hdiv : (S.card : ℝ) ≤ ((R + ρ) / ρ) ^ r := by
    rw [div_pow, le_div_iff₀ hρr_pos]
    exact hpow_le
  have hratio : (R + ρ) / ρ = 2 * R / δ + 1 := by
    dsimp only [ρ]
    field_simp [hδ.ne']
  rwa [hratio] at hdiv

/-- **Unconditional Lattice Ball Sphere-Packing Upper Bound (`h0Arith_upper_bound_packing`)**:
specializing `separated_small_count_le` to `δ = lambda1 L` yields
`(h0Arith L R : ℝ) ≤ (2 * R / lambda1 L + 1) ^ (rk L)`. -/
theorem h0Arith_upper_bound_packing (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {R : ℝ} (hR : 0 ≤ R) :
    (h0Arith L R : ℝ) ≤ (2 * R / lambda1 L + 1) ^ (rk L) := by
  let Sset : Set E := (L : Set E) ∩ Metric.closedBall 0 R
  have hfin : Sset.Finite := lattice_inter_closedBall_finite L R
  have hcard : h0Arith L R = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card Sset hfin
  rw [hcard]
  refine separated_small_count_le L hL0 hR (lambda1_pos L hL0) hfin.toFinset
    (fun x hx => (hfin.mem_toFinset.mp hx).1)
    (fun x hx => mem_closedBall_zero_iff.mp (hfin.mem_toFinset.mp hx).2)
    (fun x hx y hy hxy => ?_)
  exact lambda1_le_norm L (L.sub_mem (hfin.mem_toFinset.mp hx).1 (hfin.mem_toFinset.mp hy).1)
    (sub_ne_zero.mpr hxy)

/-- **Logarithmic Separated Small-Section Counting Bound (`log_separated_small_count_le`)**:
if `S ⊆ L ∩ closedBall 0 R` (`R ≥ 0`) has pairwise separation `‖x - y‖ ≥ exp(-B)` with
`0 ≤ B`, then
$$\log(\#S) \le \operatorname{rk}(L) \cdot \bigl(B + \log(2 R + 1)\bigr).$$
In particular, for `R = 1` this recovers the exact Moriwaki rank-bound constant `log 3`:
$$\log(\#S) \le \operatorname{rk}(L) \cdot (B + \log 3).$$ -/
theorem log_separated_small_count_le (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (S : Finset E) (hSL : ∀ x ∈ S, x ∈ L) (hSR : ∀ x ∈ S, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.exp (-B) ≤ ‖x - y‖) :
    Real.log (S.card : ℝ) ≤ (rk L : ℝ) * (B + Real.log (2 * R + 1)) := by
  by_cases hS0 : S.card = 0
  · rw [hS0, Nat.cast_zero, Real.log_zero]
    have hlog_nn : 0 ≤ Real.log (2 * R + 1) := Real.log_nonneg (by linarith)
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg hB hlog_nn)
  · have hpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS0)
    have hpack := separated_small_count_le L hL0 hR (Real.exp_pos (-B)) S hSL hSR hsep
    have hexp_ge : 1 ≤ Real.exp B := Real.one_le_exp hB
    have hstep : 2 * R / Real.exp (-B) + 1 ≤ (2 * R + 1) * Real.exp B := by
      rw [Real.exp_neg, div_inv_eq_mul]
      nlinarith
    have hpow : (2 * R / Real.exp (-B) + 1) ^ (rk L) ≤ ((2 * R + 1) * Real.exp B) ^ (rk L) :=
      pow_le_pow_left₀ (by positivity) hstep (rk L)
    have hlog := Real.log_le_log hpos (hpack.trans hpow)
    rw [Real.log_pow, Real.log_mul (by linarith) (Real.exp_pos B).ne', Real.log_exp] at hlog
    linarith

/-- Exact `R = 1` specialization: `log (#S) ≤ rk L * (B + log 3)`. -/
theorem log_separated_small_count_unit_le (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {B : ℝ} (hB : 0 ≤ B)
    (S : Finset E) (hSL : ∀ x ∈ S, x ∈ L) (hSR : ∀ x ∈ S, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.exp (-B) ≤ ‖x - y‖) :
    Real.log (S.card : ℝ) ≤ (rk L : ℝ) * (B + Real.log 3) := by
  have h := log_separated_small_count_le L hL0 zero_le_one hB S hSL hSR hsep
  norm_num at h
  exact h

end EuclideanPacking

/-! ### `MoriwakiBigDatum`, Concrete Arithmetic Volume `vol_Ar(L)` & Bigness Criterion -/

/-- Normalized Arakelov volume ratio at degree `n` in relative dimension `d`:
`log(card n) / (n^(d + 1) / (d + 1)!)`. -/
def arithVolRatio (card : ℕ → ℕ) (d n : ℕ) : ℝ :=
  Real.log (card n : ℝ) / ((n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ))

/-- **Arithmetic Volume `vol_Ar` (`Filter.liminf`)** of a small-section counting sequence
`card : ℕ → ℕ` in relative dimension `d`. -/
def arithVol (card : ℕ → ℕ) (d : ℕ) : ℝ :=
  Filter.liminf (arithVolRatio card d) atTop

/-- **Upper Arithmetic Volume `vol_Ar⁺` (`Filter.limsup`)** of a small-section counting sequence
(matching `arVolP` in Moriwaki's theorem). -/
def arithVolUpper (card : ℕ → ℕ) (d : ℕ) : ℝ :=
  Filter.limsup (arithVolRatio card d) atTop

lemma arithVolRatio_nonneg (card : ℕ → ℕ) (d n : ℕ) :
    0 ≤ arithVolRatio card d n :=
  div_nonneg (Real.log_natCast_nonneg (card n)) (by positivity)

/-- **`MoriwakiBigDatum d` (Arbitrary Relative Dimension `d : ℕ`, including `d = 0` Curves &
`d ≥ 1` Varieties)**:
packages a graded Hermitian section lattice family `⨁_{k ≥ 0} H^0(𝒳, ℒ^{⊗ k})` with:
- discrete Euclidean lattices `secLat k ⊂ secSpace k` (`secLat k ≠ ⊥` for `k ≥ 1`),
- sup-norm `supNorm k` satisfying compact-manifold `L²`-vs-`L^∞` comparison
  `volConst⁻¹ * ‖s‖ ≤ supNorm k s ≤ bergConst * (k + 1)^bergExp * ‖s‖`,
- Hilbert–Samuel polynomial rank ceiling `rk (secLat k) ≤ rankHi * k^d`,
- Northcott / Liouville first-minimum lower bound `exp(-slopeHi * k) ≤ lambda1 (secLat k)`
  (guaranteeing unconditional finiteness of `vol_Ar` and `vol_Ar⁺`),
- Arakelov top self-intersection `selfInt = \widehat{c}_1(\overline{L})^{d + 1}` satisfying
  the arithmetic Hilbert–Samuel lower bound
  `liminf_{k → ∞} arithDeg (secLat k) / k^(d + 1) ≥ selfInt / (d + 1)!`. -/
structure MoriwakiBigDatum (d : ℕ) where
  secSpace : ℕ → Type u
  [normSpace : ∀ k, NormedAddCommGroup (secSpace k)]
  [innerSpace : ∀ k, InnerProductSpace ℝ (secSpace k)]
  [fdSpace : ∀ k, FiniteDimensional ℝ (secSpace k)]
  secLat : ∀ k, Submodule ℤ (secSpace k)
  [discLat : ∀ k, DiscreteTopology (secLat k)]
  secLat_ne_bot : ∀ k, 1 ≤ k → secLat k ≠ ⊥
  supNorm : ∀ k, secSpace k → ℝ
  supNorm_nonneg : ∀ k s, 0 ≤ supNorm k s
  volConst : ℝ
  volConst_pos : 0 < volConst
  norm_le_vol_supNorm : ∀ k, 1 ≤ k → ∀ s : secSpace k, ‖s‖ ≤ volConst * supNorm k s
  bergConst : ℝ
  bergExp : ℕ
  bergConst_ge_one : 1 ≤ bergConst
  supNorm_le_bergman : ∀ k, 1 ≤ k → ∀ s : secSpace k,
    supNorm k s ≤ bergConst * ((k : ℝ) + 1) ^ bergExp * ‖s‖
  rankHi : ℝ
  rankHi_ge_one : 1 ≤ rankHi
  rk_le_poly : ∀ k, 1 ≤ k → (rk (secLat k) : ℝ) ≤ rankHi * (k : ℝ) ^ d
  slopeHi : ℝ
  slopeHi_nonneg : 0 ≤ slopeHi
  lambda1_lower : ∀ (k : ℕ), 1 ≤ k → Real.exp (-slopeHi * (k : ℝ)) ≤ lambda1 (secLat k)
  selfInt : ℝ
  ahs_liminf : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
    selfInt / ((d + 1).factorial : ℝ) - ε ≤ arithDeg (secLat k) / (k : ℝ) ^ (d + 1)

attribute [instance] MoriwakiBigDatum.normSpace MoriwakiBigDatum.innerSpace
  MoriwakiBigDatum.fdSpace MoriwakiBigDatum.discLat

namespace MoriwakiBigDatum

variable {d : ℕ} (M : MoriwakiBigDatum d)

/-- `supNorm k 0 = 0` is derived automatically for every `k ≥ 1` from the Bergman bound. -/
theorem supNorm_zero {k : ℕ} (hk : 1 ≤ k) : M.supNorm k 0 = 0 := by
  have h1 := M.supNorm_nonneg k 0
  have h2 := M.supNorm_le_bergman k hk 0
  simp only [norm_zero, mul_zero] at h2
  linarith

/-- Set of strictly small integral global sections `{s ∈ H^0(𝒳, ℒ^{⊗ k}) | ‖s‖_sup < 1}`. -/
def smallSectionsSet (k : ℕ) : Set (M.secLat k) :=
  { s : M.secLat k | M.supNorm k s.1 < 1 }

/-- Finiteness of strictly small integral global sections at every degree `k ≥ 1`. -/
theorem smallSections_finite {k : ℕ} (hk : 1 ≤ k) : (M.smallSectionsSet k).Finite := by
  have hball := lattice_inter_closedBall_finite (M.secLat k) M.volConst
  have hsub : Subtype.val '' M.smallSectionsSet k ⊆
      (M.secLat k : Set (M.secSpace k)) ∩ Metric.closedBall 0 M.volConst := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := M.norm_le_vol_supNorm k hk s.1
    have h2 : M.supNorm k s.1 < 1 := hs
    nlinarith [M.volConst_pos]
  exact Set.Finite.of_finite_image (hball.subset hsub) Subtype.val_injective.injOn

/-- Exact cardinality `#smallSections M k` of strictly small global sections `‖s‖_sup < 1`. -/
def smallSectionsCard (k : ℕ) (hk : 1 ≤ k) : ℕ :=
  (M.smallSections_finite hk).toFinset.card

/-- Total-domain small-section count `ℕ → ℕ` (with `0 ↦ 1`) used in `vol_Ar`. -/
def smallCount (k : ℕ) : ℕ :=
  if hk : 1 ≤ k then M.smallSectionsCard k hk else 1

@[simp]
lemma smallCount_of_ge_one {k : ℕ} (hk : 1 ≤ k) :
    M.smallCount k = M.smallSectionsCard k hk := dif_pos hk

/-- `0` is always strictly small, so `1 ≤ M.smallSectionsCard k hk`. -/
theorem one_le_smallSectionsCard {k : ℕ} (hk : 1 ≤ k) : 1 ≤ M.smallSectionsCard k hk := by
  unfold smallSectionsCard
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  rw [(M.smallSections_finite hk).mem_toFinset]
  change M.supNorm k 0 < 1
  rw [M.supNorm_zero hk]
  exact one_pos

/-- Lower comparison against Euclidean strict-ball count `h0ArithStrict`. -/
theorem h0ArithStrict_le_smallSectionsCard {k : ℕ} (hk : 1 ≤ k) :
    h0ArithStrict (M.secLat k) ((M.bergConst * ((k : ℝ) + 1) ^ M.bergExp)⁻¹) ≤
      M.smallSectionsCard k hk := by
  unfold h0ArithStrict smallSectionsCard
  let R : ℝ := (M.bergConst * ((k : ℝ) + 1) ^ M.bergExp)⁻¹
  have hBpos : 0 < M.bergConst * ((k : ℝ) + 1) ^ M.bergExp :=
    mul_pos (by linarith [M.bergConst_ge_one]) (pow_pos (by positivity) _)
  have hsub : ((M.secLat k : Set (M.secSpace k)) ∩ Metric.ball 0 R) ⊆
      Subtype.val '' M.smallSectionsSet k := by
    rintro x ⟨hxL, hxB⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    change M.supNorm k x < 1
    rw [Metric.mem_ball, dist_zero_right] at hxB
    have h1 := M.supNorm_le_bergman k hk x
    have h2 : M.bergConst * ((k : ℝ) + 1) ^ M.bergExp * ‖x‖ <
        M.bergConst * ((k : ℝ) + 1) ^ M.bergExp * R :=
      mul_lt_mul_of_pos_left hxB hBpos
    have hinv : M.bergConst * ((k : ℝ) + 1) ^ M.bergExp * R = 1 := mul_inv_cancel₀ hBpos.ne'
    rw [hinv] at h2
    exact lt_of_le_of_lt h1 h2
  have hfinImg : (Subtype.val '' M.smallSectionsSet k).Finite :=
    (M.smallSections_finite hk).image Subtype.val
  calc ((M.secLat k : Set (M.secSpace k)) ∩ Metric.ball 0 R).ncard
      ≤ (Subtype.val '' M.smallSectionsSet k).ncard := Set.ncard_le_ncard hsub hfinImg
    _ = (M.smallSectionsSet k).ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    _ = (M.smallSections_finite hk).toFinset.card :=
        Set.ncard_eq_toFinset_card (M.smallSectionsSet k) (M.smallSections_finite hk)

/-- Upper comparison against Euclidean closed-ball count `h0Arith (M.secLat k) M.volConst`. -/
theorem smallSectionsCard_le_h0Arith {k : ℕ} (hk : 1 ≤ k) :
    M.smallSectionsCard k hk ≤ h0Arith (M.secLat k) M.volConst := by
  unfold smallSectionsCard h0Arith
  have hball := lattice_inter_closedBall_finite (M.secLat k) M.volConst
  have hsub : Subtype.val '' M.smallSectionsSet k ⊆
      (M.secLat k : Set (M.secSpace k)) ∩ Metric.closedBall 0 M.volConst := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := M.norm_le_vol_supNorm k hk s.1
    have h2 : M.supNorm k s.1 < 1 := hs
    nlinarith [M.volConst_pos]
  calc (M.smallSections_finite hk).toFinset.card
      = (M.smallSectionsSet k).ncard :=
          (Set.ncard_eq_toFinset_card (M.smallSectionsSet k) (M.smallSections_finite hk)).symm
    _ = (Subtype.val '' M.smallSectionsSet k).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((M.secLat k : Set (M.secSpace k)) ∩ Metric.closedBall 0 M.volConst).ncard :=
          Set.ncard_le_ncard hsub hball

/-- **Unconditional Upper Bound on `log (M.smallSectionsCard k)`** via sphere packing +
Northcott `λ₁` floor. -/
theorem log_smallSectionsCard_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log (M.smallSectionsCard k hk : ℝ) ≤
      (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1))) * (k : ℝ) ^ (d + 1) := by
  have hk_pos : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hS_fin : (Subtype.val '' M.smallSectionsSet k).Finite :=
    (M.smallSections_finite hk).image Subtype.val
  have hcard_eq : M.smallSectionsCard k hk = hS_fin.toFinset.card := by
    unfold smallSectionsCard
    rw [← Set.ncard_eq_toFinset_card (M.smallSectionsSet k) (M.smallSections_finite hk),
      ← Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_eq_toFinset_card _ hS_fin]
  have hpack := log_separated_small_count_le (M.secLat k) (M.secLat_ne_bot k hk)
    M.volConst_pos.le (mul_nonneg M.slopeHi_nonneg (Nat.cast_nonneg k)) hS_fin.toFinset
    (fun x hx => by
      rcases hS_fin.mem_toFinset.mp hx with ⟨s, _, rfl⟩
      exact s.2)
    (fun x hx => by
      rcases hS_fin.mem_toFinset.mp hx with ⟨s, hs, rfl⟩
      have h1 := M.norm_le_vol_supNorm k hk s.1
      have h2 : M.supNorm k s.1 < 1 := hs
      nlinarith [M.volConst_pos])
    (fun x hx y hy hxy => by
      rcases hS_fin.mem_toFinset.mp hx with ⟨sx, _, rfl⟩
      rcases hS_fin.mem_toFinset.mp hy with ⟨sy, _, rfl⟩
      have hlam := M.lambda1_lower k hk
      have hle := lambda1_le_norm (M.secLat k) ((M.secLat k).sub_mem sx.2 sy.2) (sub_ne_zero.mpr hxy)
      have hneg : -(M.slopeHi * (k : ℝ)) = -M.slopeHi * (k : ℝ) := by ring
      rw [hneg]
      exact hlam.trans hle)
  rw [← hcard_eq] at hpack
  have hlog_nn : 0 ≤ Real.log (2 * M.volConst + 1) :=
    Real.log_nonneg (by linarith [M.volConst_pos])
  have hfactor : M.slopeHi * (k : ℝ) + Real.log (2 * M.volConst + 1) ≤
      (M.slopeHi + Real.log (2 * M.volConst + 1)) * (k : ℝ) := by
    nlinarith
  have hrk := M.rk_le_poly k hk
  calc Real.log (M.smallSectionsCard k hk : ℝ)
      ≤ (rk (M.secLat k) : ℝ) * (M.slopeHi * (k : ℝ) + Real.log (2 * M.volConst + 1)) := hpack
    _ ≤ (M.rankHi * (k : ℝ) ^ d) * ((M.slopeHi + Real.log (2 * M.volConst + 1)) * (k : ℝ)) := by
        refine mul_le_mul hrk hfactor ?_ (mul_nonneg (by linarith [M.rankHi_ge_one]) (pow_nonneg (Nat.cast_nonneg k) d))
        exact add_nonneg (mul_nonneg M.slopeHi_nonneg (Nat.cast_nonneg k)) hlog_nn
    _ = (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1))) * (k : ℝ) ^ (d + 1) := by
        rw [pow_succ]; ring

/-- **Arithmetic Volume `vol_Ar(M)`** (`Filter.liminf` of normalized log small-section count). -/
def volAr : ℝ :=
  arithVol M.smallCount d

/-- **Upper Arithmetic Volume `vol_Ar⁺(M)`** (`Filter.limsup`, matching `arVolP`). -/
def volArUpper : ℝ :=
  arithVolUpper M.smallCount d

/-- **Arithmetic Bigness Criterion (`IsArithBig`)**: `0 < vol_Ar(M)`. -/
def IsArithBig : Prop :=
  0 < M.volAr

/-- Unconditional upper boundedness of `arithVolRatio M.smallCount d`. -/
theorem arithVolRatio_bddAbove :
    IsBoundedUnder (· ≤ ·) atTop (arithVolRatio M.smallCount d) := by
  refine ⟨((d + 1).factorial : ℝ) * (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1))), ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [eventually_ge_atTop 1] with k hk
  unfold arithVolRatio
  rw [M.smallCount_of_ge_one hk]
  have hkd1_pos : (0 : ℝ) < (k : ℝ) ^ (d + 1) := pow_pos (Nat.cast_pos.mpr hk) (d + 1)
  have hfac_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_iff₀ (div_pos hkd1_pos hfac_pos)]
  have hle := M.log_smallSectionsCard_le hk
  have hrhs : (((d + 1).factorial : ℝ) *
      (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1)))) *
      ((k : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) =
      (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1))) * (k : ℝ) ^ (d + 1) := by
    field_simp [hfac_pos.ne']
  linarith

/-- Unconditional lower boundedness of `arithVolRatio M.smallCount d` (by `0`). -/
theorem arithVolRatio_bddBelow :
    IsBoundedUnder (· ≥ ·) atTop (arithVolRatio M.smallCount d) :=
  ⟨0, by
    rw [Filter.eventually_map]
    exact Filter.Eventually.of_forall fun (k : ℕ) => arithVolRatio_nonneg M.smallCount d k⟩

/-- Non-negativity of arithmetic volume: `0 ≤ M.volAr`. -/
theorem volAr_nonneg : 0 ≤ M.volAr := by
  unfold volAr arithVol
  exact Filter.le_liminf_of_le M.arithVolRatio_bddAbove.isCoboundedUnder_ge
    (Filter.Eventually.of_forall fun (k : ℕ) => arithVolRatio_nonneg M.smallCount d k)

/-- `vol_Ar(M) ≤ vol_Ar⁺(M)`. -/
theorem volAr_le_volArUpper : M.volAr ≤ M.volArUpper :=
  Filter.liminf_le_limsup M.arithVolRatio_bddAbove M.arithVolRatio_bddBelow

/-- Explicit finite upper bound on `vol_Ar⁺(M)` in terms of `rankHi`, `slopeHi`, `volConst`. -/
theorem volArUpper_le :
    M.volArUpper ≤
      ((d + 1).factorial : ℝ) * (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1))) := by
  unfold volArUpper arithVolUpper
  refine Filter.limsup_le_of_le M.arithVolRatio_bddBelow.isCoboundedUnder_le ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  unfold arithVolRatio
  rw [M.smallCount_of_ge_one hk]
  have hkd1_pos : (0 : ℝ) < (k : ℝ) ^ (d + 1) := pow_pos (Nat.cast_pos.mpr hk) (d + 1)
  have hfac_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_iff₀ (div_pos hkd1_pos hfac_pos)]
  have hle := M.log_smallSectionsCard_le hk
  have hrhs : (((d + 1).factorial : ℝ) *
      (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1)))) *
      ((k : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) =
      (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1))) * (k : ℝ) ^ (d + 1) := by
    field_simp [hfac_pos.ne']
  linarith

/-! ### Bidirectional Bridges with `Stage12SchurWeylLattices.GradedHermAlgebra` -/

/-- Lift any `GradedHermAlgebra d` equipped with a Northcott `λ₁` floor to a `MoriwakiBigDatum d`. -/
def ofGradedHermAlgebra (A : GradedHermAlgebra d) (slopeHi : ℝ) (hslopeHi : 0 ≤ slopeHi)
    (hlam : ∀ (k : ℕ), 1 ≤ k → Real.exp (-slopeHi * (k : ℝ)) ≤ lambda1 (A.secLat k)) :
    MoriwakiBigDatum d where
  secSpace := A.secSpace
  secLat := A.secLat
  secLat_ne_bot := A.secLat_ne_bot
  supNorm := A.supNorm
  supNorm_nonneg := A.supNorm_nonneg
  volConst := A.volConst
  volConst_pos := A.volConst_pos
  norm_le_vol_supNorm := A.norm_le_vol_supNorm
  bergConst := A.bergConst
  bergExp := A.bergExp
  bergConst_ge_one := A.bergConst_ge_one
  supNorm_le_bergman := A.supNorm_le_bergman
  rankHi := A.rankHi
  rankHi_ge_one := A.rankHi_ge_one
  rk_le_poly := A.rk_le_poly
  slopeHi := slopeHi
  slopeHi_nonneg := hslopeHi
  lambda1_lower := hlam
  selfInt := A.volAr
  ahs_liminf := A.ahs_liminf

/-- Forgetful conversion from `MoriwakiBigDatum d` (`1 ≤ d`) to `Stage12SchurWeylLattices.GradedHermAlgebra d`. -/
def toGradedHermAlgebra (hd : 1 ≤ d) : GradedHermAlgebra d where
  hd := hd
  secSpace := M.secSpace
  secLat := M.secLat
  secLat_ne_bot := M.secLat_ne_bot
  supNorm := M.supNorm
  supNorm_nonneg := M.supNorm_nonneg
  volConst := M.volConst
  volConst_pos := M.volConst_pos
  norm_le_vol_supNorm := M.norm_le_vol_supNorm
  bergConst := M.bergConst
  bergExp := M.bergExp
  bergConst_ge_one := M.bergConst_ge_one
  supNorm_le_bergman := M.supNorm_le_bergman
  rankHi := M.rankHi
  rankHi_ge_one := M.rankHi_ge_one
  rk_le_poly := M.rk_le_poly
  volAr := M.selfInt
  ahs_liminf := M.ahs_liminf

lemma toGradedHermAlgebra_smallSectionsCard (hd : 1 ≤ d) {k : ℕ} (hk : 1 ≤ k) :
    (M.toGradedHermAlgebra hd).smallSectionsCard k hk = M.smallSectionsCard k hk := rfl

/-! ### Metric Twist & Veronese Power Operations on `MoriwakiBigDatum` -/

/-- Exact `lambda1` scaling law under `scaleLat c` (`c > 0`):
`lambda1 (scaleLat c L) = c * lambda1 L`. -/
theorem lambda1_scaleLat {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {c : ℝ} (hc : 0 < c) :
    lambda1 (scaleLat c L) = c * lambda1 L := by
  have : DiscreteTopology (scaleLat c L) := (scaleLat_invariants L hc).1
  have hS0 : scaleLat c L ≠ ⊥ := by
    intro hbot
    have hrk := (scaleLat_invariants L hc).2.1
    rw [hbot, show rk (⊥ : Submodule ℤ E) = 0 by simp [rk]] at hrk
    exact (rk_pos_of_ne_bot L hL0).ne hrk
  apply le_antisymm
  · obtain ⟨v₀, hv₀L, hv₀0, hnorm⟩ :=
      RHDirect.Stage2SiegelReduction.exists_norm_eq_lambda1 L hL0
    have hmem : c • v₀ ∈ scaleLat c L := ⟨v₀, hv₀L, rfl⟩
    have hne : c • v₀ ≠ 0 := smul_ne_zero hc.ne' hv₀0
    calc lambda1 (scaleLat c L) ≤ ‖c • v₀‖ := lambda1_le_norm (scaleLat c L) hmem hne
      _ = c * ‖v₀‖ := by rw [norm_smul, Real.norm_of_nonneg hc.le]
      _ = c * lambda1 L := by rw [hnorm]
  · obtain ⟨w₀, hw₀S, hw₀0, hnorm⟩ :=
      RHDirect.Stage2SiegelReduction.exists_norm_eq_lambda1 (scaleLat c L) hS0
    rcases hw₀S with ⟨v₀, hv₀L, rfl⟩
    have hv₀0 : v₀ ≠ 0 := fun h0 => hw₀0 (by simp [h0])
    have hle := lambda1_le_norm L hv₀L hv₀0
    have hnw : ‖c • v₀‖ = c * ‖v₀‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc.le]
    have hmul := mul_le_mul_of_nonneg_left hle hc.le
    rw [← hnw] at hmul
    exact hmul.trans_eq hnorm

/-- **Positive Metric Twist `M.twistMetric t` (`t ≥ 0`)**:
rescales the `k`-th Hermitian metric by `e^{-k t}` (shrinking section norms by `e^{-k t}`),
shifting `arithDeg (secLat k)` upward by `k * t * rk (secLat k)` and shifting `selfInt` upward
by `(d + 1) * degLo * t` whenever `rk (secLat k) ≥ degLo * k^d / d!`. -/
def twistMetric (t : ℝ) (ht : 0 ≤ t) (degLo : ℝ)
    (hrk_lo : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      degLo / (d.factorial : ℝ) - ε ≤ (rk (M.secLat k) : ℝ) / (k : ℝ) ^ d) :
    MoriwakiBigDatum d where
  secSpace := M.secSpace
  secLat k := scaleLat (Real.exp (-(k : ℝ) * t)) (M.secLat k)
  discLat k := (scaleLat_invariants (M.secLat k) (Real.exp_pos (-(k : ℝ) * t))).1
  secLat_ne_bot k hk := by
    intro hbot
    have hrk := (scaleLat_invariants (M.secLat k) (Real.exp_pos (-(k : ℝ) * t))).2.1
    rw [hbot, show rk (⊥ : Submodule ℤ (M.secSpace k)) = 0 by simp [rk]] at hrk
    exact (rk_pos_of_ne_bot (M.secLat k) (M.secLat_ne_bot k hk)).ne hrk
  supNorm k s := Real.exp (-(k : ℝ) * t) * M.supNorm k (Real.exp ((k : ℝ) * t) • s)
  supNorm_nonneg k s := mul_nonneg (Real.exp_pos _).le (M.supNorm_nonneg k _)
  volConst := M.volConst
  volConst_pos := M.volConst_pos
  norm_le_vol_supNorm k hk s := by
    have h1 := M.norm_le_vol_supNorm k hk (Real.exp ((k : ℝ) * t) • s)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have hmul := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(k : ℝ) * t)).le
    have hcancel : Real.exp (-(k : ℝ) * t) * (Real.exp ((k : ℝ) * t) * ‖s‖) = ‖s‖ := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    linarith
  bergConst := M.bergConst
  bergExp := M.bergExp
  bergConst_ge_one := M.bergConst_ge_one
  supNorm_le_bergman k hk s := by
    have h1 := M.supNorm_le_bergman k hk (Real.exp ((k : ℝ) * t) • s)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have hmul := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(k : ℝ) * t)).le
    have hcancel : Real.exp (-(k : ℝ) * t) *
        (M.bergConst * ((k : ℝ) + 1) ^ M.bergExp * (Real.exp ((k : ℝ) * t) * ‖s‖)) =
        M.bergConst * ((k : ℝ) + 1) ^ M.bergExp * ‖s‖ := by
      have hexp : Real.exp (-(k : ℝ) * t) * Real.exp ((k : ℝ) * t) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-(k : ℝ) * t) *
            (M.bergConst * ((k : ℝ) + 1) ^ M.bergExp * (Real.exp ((k : ℝ) * t) * ‖s‖))
          = (Real.exp (-(k : ℝ) * t) * Real.exp ((k : ℝ) * t)) *
            (M.bergConst * ((k : ℝ) + 1) ^ M.bergExp * ‖s‖) := by ring
        _ = M.bergConst * ((k : ℝ) + 1) ^ M.bergExp * ‖s‖ := by rw [hexp, one_mul]
    linarith
  rankHi := M.rankHi
  rankHi_ge_one := M.rankHi_ge_one
  rk_le_poly k hk := by
    rw [(scaleLat_invariants (M.secLat k) (Real.exp_pos (-(k : ℝ) * t))).2.1]
    exact M.rk_le_poly k hk
  slopeHi := M.slopeHi + t
  slopeHi_nonneg := add_nonneg M.slopeHi_nonneg ht
  lambda1_lower k hk := by
    rw [lambda1_scaleLat (M.secLat k) (M.secLat_ne_bot k hk) (Real.exp_pos (-(k : ℝ) * t))]
    have h1 := M.lambda1_lower k hk
    have hmul := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(k : ℝ) * t)).le
    rw [← Real.exp_add] at hmul
    have hexp : -(k : ℝ) * t + -M.slopeHi * (k : ℝ) = -(M.slopeHi + t) * (k : ℝ) := by ring
    rwa [hexp] at hmul
  selfInt := M.selfInt + ((d + 1 : ℕ) : ℝ) * degLo * t
  ahs_liminf ε hε := by
    have h1 := M.ahs_liminf (ε / 2) (half_pos hε)
    have h2 : ∀ᶠ k : ℕ in atTop,
        t * (degLo / (d.factorial : ℝ)) - ε / 2 ≤
          t * ((rk (M.secLat k) : ℝ) / (k : ℝ) ^ d) := by
      by_cases ht0 : t = 0
      · refine Filter.Eventually.of_forall fun k => ?_
        rw [ht0]; linarith
      · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        filter_upwards [hrk_lo (ε / (2 * t)) (div_pos hε (mul_pos zero_lt_two ht_pos))] with k hk
        have hmul := mul_le_mul_of_nonneg_left hk ht_pos.le
        have hsimp : t * (degLo / (d.factorial : ℝ) - ε / (2 * t)) =
            t * (degLo / (d.factorial : ℝ)) - ε / 2 := by
          field_simp [ht_pos.ne']
        linarith
    filter_upwards [h1, h2, eventually_ge_atTop 1] with k hk1 hk2 hk_ge1
    have hdeg := (scaleLat_invariants (M.secLat k) (Real.exp_pos (-(k : ℝ) * t))).2.2.2
    rw [hdeg, Real.log_exp]
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_ge1
    have hkd_pos : (0 : ℝ) < (k : ℝ) ^ d := pow_pos hk_pos d
    have hkd1_pos : (0 : ℝ) < (k : ℝ) ^ (d + 1) := pow_pos hk_pos (d + 1)
    have hsplit : (arithDeg (M.secLat k) - (rk (M.secLat k) : ℝ) * (-(k : ℝ) * t)) /
        (k : ℝ) ^ (d + 1) =
        arithDeg (M.secLat k) / (k : ℝ) ^ (d + 1) +
        t * ((rk (M.secLat k) : ℝ) / (k : ℝ) ^ d) := by
      rw [pow_succ]
      field_simp [hk_pos.ne', hkd_pos.ne']
      ring
    have hfac_eq : (M.selfInt + ((d + 1 : ℕ) : ℝ) * degLo * t) / ((d + 1).factorial : ℝ) =
        M.selfInt / ((d + 1).factorial : ℝ) + t * (degLo / (d.factorial : ℝ)) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      have hfd : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
      have hd1 : ((d + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
      field_simp [hfd, hd1]
    rw [hsplit, hfac_eq]
    linarith

/-- **Veronese / Tensor-Power Regrading `M.veronesePower m` (`1 ≤ m`)**:
passes from `L^{⊗ k}` to `(L^{⊗ m})^{⊗ k} = L^{⊗ (m k)}`, scaling the Arakelov
self-intersection homogeneously by `m^(d + 1)`. -/
def veronesePower (m : ℕ) (hm : 1 ≤ m) : MoriwakiBigDatum d where
  secSpace k := M.secSpace (m * k)
  secLat k := M.secLat (m * k)
  secLat_ne_bot k hk := M.secLat_ne_bot (m * k) (Nat.mul_le_mul hm hk)
  supNorm k := M.supNorm (m * k)
  supNorm_nonneg k := M.supNorm_nonneg (m * k)
  volConst := M.volConst
  volConst_pos := M.volConst_pos
  norm_le_vol_supNorm k hk := M.norm_le_vol_supNorm (m * k) (Nat.mul_le_mul hm hk)
  bergConst := M.bergConst * (m : ℝ) ^ M.bergExp
  bergExp := M.bergExp
  bergConst_ge_one := one_le_mul_of_one_le_of_one_le M.bergConst_ge_one
    (one_le_pow₀ (by exact_mod_cast hm))
  supNorm_le_bergman k hk s := by
    have h1 := M.supNorm_le_bergman (m * k) (Nat.mul_le_mul hm hk) s
    have hstep : ((m * k : ℕ) : ℝ) + 1 ≤ (m : ℝ) * ((k : ℝ) + 1) := by
      push_cast
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    have hpow : (((m * k : ℕ) : ℝ) + 1) ^ M.bergExp ≤
        ((m : ℝ) * ((k : ℝ) + 1)) ^ M.bergExp :=
      pow_le_pow_left₀ (by positivity) hstep M.bergExp
    rw [mul_pow] at hpow
    have hB : 0 ≤ M.bergConst := by linarith [M.bergConst_ge_one]
    calc M.supNorm (m * k) s
        ≤ M.bergConst * (((m * k : ℕ) : ℝ) + 1) ^ M.bergExp * ‖s‖ := h1
      _ ≤ M.bergConst * ((m : ℝ) ^ M.bergExp * ((k : ℝ) + 1) ^ M.bergExp) * ‖s‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hB) (norm_nonneg s)
      _ = M.bergConst * (m : ℝ) ^ M.bergExp * ((k : ℝ) + 1) ^ M.bergExp * ‖s‖ := by ring
  rankHi := M.rankHi * (m : ℝ) ^ d
  rankHi_ge_one := one_le_mul_of_one_le_of_one_le M.rankHi_ge_one
    (one_le_pow₀ (by exact_mod_cast hm))
  rk_le_poly k hk := by
    have h := M.rk_le_poly (m * k) (Nat.mul_le_mul hm hk)
    push_cast at h
    rw [mul_pow] at h
    linarith
  slopeHi := M.slopeHi * (m : ℝ)
  slopeHi_nonneg := mul_nonneg M.slopeHi_nonneg (Nat.cast_nonneg m)
  lambda1_lower k hk := by
    have h := M.lambda1_lower (m * k) (Nat.mul_le_mul hm hk)
    push_cast at h
    have hexp : -(M.slopeHi * (m : ℝ)) * (k : ℝ) = -M.slopeHi * ((m : ℝ) * (k : ℝ)) := by ring
    rwa [hexp]
  selfInt := (m : ℝ) ^ (d + 1) * M.selfInt
  ahs_liminf ε hε := by
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have hmd1_pos : (0 : ℝ) < (m : ℝ) ^ (d + 1) := pow_pos hm_pos (d + 1)
    have hAHS := M.ahs_liminf (ε / (m : ℝ) ^ (d + 1)) (div_pos hε hmd1_pos)
    rw [Filter.eventually_atTop] at hAHS
    obtain ⟨K₀, hK₀⟩ := hAHS
    rw [Filter.eventually_atTop]
    refine ⟨max 1 K₀, fun k hk => ?_⟩
    have hmk : K₀ ≤ m * k := by
      have hkK : K₀ ≤ k := le_trans (le_max_right _ _) hk
      calc K₀ ≤ k := hkK
        _ = 1 * k := (one_mul k).symm
        _ ≤ m * k := Nat.mul_le_mul_right k hm
    have hspec := hK₀ (m * k) hmk
    have hmul := mul_le_mul_of_nonneg_left hspec hmd1_pos.le
    have hlhs : (m : ℝ) ^ (d + 1) * (M.selfInt / ((d + 1).factorial : ℝ) -
        ε / (m : ℝ) ^ (d + 1)) =
        (m : ℝ) ^ (d + 1) * M.selfInt / ((d + 1).factorial : ℝ) - ε := by
      field_simp [hmd1_pos.ne']
    have hrhs : (m : ℝ) ^ (d + 1) * (arithDeg (M.secLat (m * k)) / ((m * k : ℕ) : ℝ) ^ (d + 1)) =
        arithDeg (M.secLat (m * k)) / (k : ℝ) ^ (d + 1) := by
      push_cast
      rw [mul_pow]
      field_simp [hmd1_pos.ne']
    rw [hlhs, hrhs] at hmul
    exact hmul

/-- **Positive Super-Homogeneity of Arithmetic Volume (`volAr_veronesePower_ge`)**:
for every `m ≥ 1`, `(m : ℝ) ^ (d + 1) * M.volAr ≤ (M.veronesePower m hm).volAr`. -/
theorem volAr_veronesePower_ge (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ (d + 1) * M.volAr ≤ (M.veronesePower m hm).volAr := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmd1_pos : (0 : ℝ) < (m : ℝ) ^ (d + 1) := pow_pos hm_pos (d + 1)
  unfold volAr arithVol
  apply le_of_forall_lt_imp_le_of_dense
  intro b hb
  refine Filter.le_liminf_of_le (M.veronesePower m hm).arithVolRatio_bddAbove.isCoboundedUnder_ge ?_
  have hb' : b / (m : ℝ) ^ (d + 1) < Filter.liminf (arithVolRatio M.smallCount d) atTop := by
    rw [div_lt_iff₀ hmd1_pos]
    simpa [mul_comm] using hb
  have hev := Filter.eventually_lt_of_lt_liminf hb' M.arithVolRatio_bddBelow
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K₀, hK₀⟩ := hev
  rw [Filter.eventually_atTop]
  refine ⟨max 1 K₀, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hmk1 : 1 ≤ m * k := Nat.mul_le_mul hm hk1
  have hmkK : K₀ ≤ m * k := le_trans (le_trans (le_max_right _ _) hk) (Nat.le_mul_of_pos_left k hm)
  have hlt := hK₀ (m * k) hmkK
  have hmul := mul_lt_mul_of_pos_left hlt hmd1_pos
  have hlhs : (m : ℝ) ^ (d + 1) * (b / (m : ℝ) ^ (d + 1)) = b :=
    mul_div_cancel₀ b hmd1_pos.ne'
  have hrhs : (m : ℝ) ^ (d + 1) * arithVolRatio M.smallCount d (m * k) =
      arithVolRatio (M.veronesePower m hm).smallCount d k := by
    unfold arithVolRatio
    rw [M.smallCount_of_ge_one hmk1, (M.veronesePower m hm).smallCount_of_ge_one hk1]
    have hcard_eq : (M.veronesePower m hm).smallSectionsCard k hk1 =
        M.smallSectionsCard (m * k) hmk1 := rfl
    rw [hcard_eq]
    push_cast
    rw [mul_pow]
    have hfac_ne : ((d + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk_ne : (k : ℝ) ^ (d + 1) ≠ 0 := (pow_pos (Nat.cast_pos.mpr hk1) _).ne'
    field_simp [hmd1_pos.ne', hfac_ne, hk_ne]
  rw [hlhs, hrhs] at hmul
  exact hmul.le

end MoriwakiBigDatum

end MoriwakiBigDatumAndVolume

/-! ## Section 4: Generic Rank / Degree Bounds & Shift-Volume Ceiling (`moriwaki_rank_bounds_generic`) -/

section MoriwakiRankBounds

/-- **Shifted Generic-Rank Datum (`ShiftRankDatum d`)**:
models the shifted Hermitian lattice family `q ↦ L_q(n)` (`q ≥ 1` shift parameter,
`n : ℕ` tensor power) of Moriwaki's rank-bound pipeline (`ShiftSectionsRankB`,
`ShiftSectionsRankUpper`, `ShiftVolumeBound`):
- `genDeg q ≥ 0` is the generic-fiber top intersection degree `deg_K(q · A + FS)`;
- `rank_tendsto q` encodes the asymptotic Hilbert–Samuel rank convergence
  `rk(L_q(n)) / (n^d / d!) → genDeg q`;
- `smallCard q n` counts small sections in a unit ball of `L_q(n)` subject to linear separation
  `exp(-(C + 1) * n * (q + 1))` (`ShiftSectionSeparation`). -/
structure ShiftRankDatum (d : ℕ) where
  secSpace : ℕ → ℕ → Type*
  [normSpace : ∀ q n, NormedAddCommGroup (secSpace q n)]
  [innerSpace : ∀ q n, InnerProductSpace ℝ (secSpace q n)]
  [fdSpace : ∀ q n, FiniteDimensional ℝ (secSpace q n)]
  secLat : ∀ q n, Submodule ℤ (secSpace q n)
  [discLat : ∀ q n, DiscreteTopology (secLat q n)]
  secLat_ne_bot : ∀ q, 1 ≤ q → ∀ n, 1 ≤ n → secLat q n ≠ ⊥
  genDeg : ℕ → ℝ
  genDeg_nonneg : ∀ q, 1 ≤ q → 0 ≤ genDeg q
  rank_tendsto : ∀ q, 1 ≤ q →
    Tendsto (fun n : ℕ =>
        (rk (secLat q n) : ℝ) / ((n : ℝ) ^ d / (d.factorial : ℝ)))
      atTop (𝓝 (genDeg q))
  smallSet : ∀ q n, Finset (secSpace q n)
  smallSet_mem : ∀ q n, ∀ x ∈ smallSet q n, x ∈ secLat q n
  smallSet_norm_le : ∀ q n, ∀ x ∈ smallSet q n, ‖x‖ ≤ 1
  sepConst : ℝ
  sepConst_nonneg : 0 ≤ sepConst
  smallSet_sep : ∀ q, 1 ≤ q → ∀ n, 1 ≤ n → ∀ x ∈ smallSet q n, ∀ y ∈ smallSet q n, x ≠ y →
    Real.exp (-((sepConst + 1) * (n : ℝ) * ((q : ℝ) + 1))) ≤ ‖x - y‖

attribute [instance] ShiftRankDatum.normSpace ShiftRankDatum.innerSpace
  ShiftRankDatum.fdSpace ShiftRankDatum.discLat

namespace ShiftRankDatum

variable {d : ℕ} (R : ShiftRankDatum d)

/-- Small-section count at shift `q` and tensor power `n`. -/
def smallCount (q n : ℕ) : ℕ :=
  (R.smallSet q n).card

/-- **`ShiftSectionsRankUpper`**: eventual asymptotic upper envelope on `rk(L_q(n))` deduced
from generic rank convergence `rank_tendsto`. -/
theorem rank_upper (q : ℕ) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (rk (R.secLat q n) : ℝ) ≤ (R.genDeg q + ε) * ((n : ℝ) ^ d / (d.factorial : ℝ)) := by
  have hlim := R.rank_tendsto q hq
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_of_pos_right (R.genDeg q) hε)),
    eventually_ge_atTop 1] with n hn hn1
  have hx : 0 < (n : ℝ) ^ d / (d.factorial : ℝ) :=
    div_pos (pow_pos (Nat.cast_pos.mpr hn1) d) (Nat.cast_pos.mpr (Nat.factorial_pos d))
  exact ((div_lt_iff₀ hx).mp hn).le

/-- Eventual asymptotic lower envelope on `rk(L_q(n))`. -/
theorem rank_lower (q : ℕ) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (R.genDeg q - ε) * ((n : ℝ) ^ d / (d.factorial : ℝ)) ≤ (rk (R.secLat q n) : ℝ) := by
  have hlim := R.rank_tendsto q hq
  filter_upwards [hlim.eventually (lt_mem_nhds (sub_lt_self (R.genDeg q) hε)),
    eventually_ge_atTop 1] with n hn hn1
  have hx : 0 < (n : ℝ) ^ d / (d.factorial : ℝ) :=
    div_pos (pow_pos (Nat.cast_pos.mpr hn1) d) (Nat.cast_pos.mpr (Nat.factorial_pos d))
  exact ((lt_div_iff₀ hx).mp hn).le

/-- Pointwise separated small-section logarithmic upper bound at `(q, n)` with exact constant
`log 3` via `log_separated_small_count_unit_le`. -/
theorem log_smallCount_le (q : ℕ) (hq : 1 ≤ q) (n : ℕ) (hn : 1 ≤ n) :
    Real.log (R.smallCount q n : ℝ) ≤
      (rk (R.secLat q n) : ℝ) * ((R.sepConst + 1) * (n : ℝ) * ((q : ℝ) + 1) + Real.log 3) := by
  unfold smallCount
  have hBnn : 0 ≤ (R.sepConst + 1) * (n : ℝ) * ((q : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by linarith [R.sepConst_nonneg]) (Nat.cast_nonneg n)) (by positivity)
  exact log_separated_small_count_unit_le (R.secLat q n) (R.secLat_ne_bot q hq n hn)
    hBnn (R.smallSet q n) (R.smallSet_mem q n) (R.smallSet_norm_le q n)
    (R.smallSet_sep q hq n hn)

/-- **`ShiftVolumeBound` (`shift_volume_upper_bound`)**:
unconditional upper bound on the upper arithmetic volume `arithVolUpper (R.smallCount q) d`
in terms of the generic degree `R.genDeg q` and separation constant `R.sepConst`:
$$\operatorname{vol}_{\mathrm{Ar}}^+(q) \le 2 (C + 1) (d + 1) (q + 1) \cdot \deg_K(q).$$ -/
theorem shift_volume_upper_bound (q : ℕ) (hq : 1 ≤ q) :
    arithVolUpper (R.smallCount q) d ≤
      2 * (R.sepConst + 1) * ((d : ℝ) + 1) * ((q : ℝ) + 1) * R.genDeg q := by
  unfold arithVolUpper
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hK : (0 : ℝ) < 2 * (R.sepConst + 1) * ((d : ℝ) + 1) * ((q : ℝ) + 1) := by
    have hC := R.sepConst_nonneg
    positivity
  have hε : 0 < δ / (2 * (R.sepConst + 1) * ((d : ℝ) + 1) * ((q : ℝ) + 1)) := div_pos hδ hK
  have hr := R.rank_upper q hq hε
  refine Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le atTop (x := 0) fun k => arithVolRatio_nonneg _ d k) ?_
  filter_upwards [hr, eventually_ge_atTop 2] with n hn hn2
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hC := R.sepConst_nonneg
  have hlog3 : Real.log 3 ≤ (R.sepConst + 1) * (n : ℝ) * ((q : ℝ) + 1) := by
    have h1 : Real.log 3 ≤ (3 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : (0 : ℝ) ≤ R.sepConst * (n : ℝ) * ((q : ℝ) + 1) := by positivity
    nlinarith
  have hpos : (0 : ℝ) < (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) :=
    div_pos (pow_pos (Nat.cast_pos.mpr hn1) (d + 1)) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  unfold arithVolRatio
  rw [div_le_iff₀ hpos]
  have hcount := R.log_smallCount_le q hq n hn1
  have hrk_nn : (0 : ℝ) ≤ (rk (R.secLat q n) : ℝ) := Nat.cast_nonneg _
  have hmul_nn : (0 : ℝ) ≤ 2 * (R.sepConst + 1) * (n : ℝ) * ((q : ℝ) + 1) := by positivity
  calc Real.log (R.smallCount q n : ℝ)
      ≤ (rk (R.secLat q n) : ℝ) * ((R.sepConst + 1) * (n : ℝ) * ((q : ℝ) + 1) + Real.log 3) :=
          hcount
    _ ≤ (2 * (R.sepConst + 1) * (n : ℝ) * ((q : ℝ) + 1)) * (rk (R.secLat q n) : ℝ) := by
          nlinarith
    _ ≤ (2 * (R.sepConst + 1) * (n : ℝ) * ((q : ℝ) + 1)) *
          ((R.genDeg q + δ / (2 * (R.sepConst + 1) * ((d : ℝ) + 1) * ((q : ℝ) + 1))) *
            ((n : ℝ) ^ d / (d.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hn hmul_nn
    _ = (2 * (R.sepConst + 1) * ((d : ℝ) + 1) * ((q : ℝ) + 1) * R.genDeg q + δ) *
          ((n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) := by
          rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
          have hf : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
          have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
          have hC1 : (R.sepConst + 1) ≠ 0 := by linarith
          have hq1 : ((q : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          field_simp [hf, hd1, hC1, hq1]

end ShiftRankDatum

/-- **PROVED GENERIC RANK & SHIFT-VOLUME BOUNDS (`moriwaki_rank_bounds_generic`)**:
for any `ShiftRankDatum d` and any shift `q ≥ 1`, simultaneously establishes:
1. Exact generic-degree rank convergence `rk(L_q(n)) / (n^d / d!) → genDeg q`,
2. Quantitative upper rank envelope `∀ ε > 0, ∀ᶠ n, rk(L_q(n)) ≤ (genDeg q + ε) * n^d / d!`,
3. Quantitative lower rank envelope `∀ ε > 0, ∀ᶠ n, (genDeg q - ε) * n^d / d! ≤ rk(L_q(n))`,
4. Explicit shifted arithmetic volume upper bound
   `arithVolUpper (R.smallCount q) d ≤ 2 * (R.sepConst + 1) * (d + 1) * (q + 1) * R.genDeg q`. -/
theorem moriwaki_rank_bounds_generic {d : ℕ} (R : ShiftRankDatum d) (q : ℕ) (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ =>
        (rk (R.secLat q n) : ℝ) / ((n : ℝ) ^ d / (d.factorial : ℝ)))
      atTop (𝓝 (R.genDeg q)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (rk (R.secLat q n) : ℝ) ≤ (R.genDeg q + ε) * ((n : ℝ) ^ d / (d.factorial : ℝ))) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (R.genDeg q - ε) * ((n : ℝ) ^ d / (d.factorial : ℝ)) ≤ (rk (R.secLat q n) : ℝ)) ∧
    arithVolUpper (R.smallCount q) d ≤
      2 * (R.sepConst + 1) * ((d : ℝ) + 1) * ((q : ℝ) + 1) * R.genDeg q :=
  ⟨R.rank_tendsto q hq,
   fun _ hε => R.rank_upper q hq hε,
   fun _ hε => R.rank_lower q hq hε,
   R.shift_volume_upper_bound q hq⟩

/-- **Rank Convergence from Two-Sided Polynomial Error Sandwich (`rank_tendsto_of_poly_sandwich`)**:
helper for constructing `ShiftRankDatum d` whenever `|rk(L n) - deg₀ * n^d / d!| ≤ C * n^(d - 1)`
(or for `d = 0`, constant rank `rk(L n) = deg₀`). -/
theorem rank_tendsto_of_poly_sandwich {d : ℕ} {f : ℕ → ℝ} {deg₀ C : ℝ}
    (hsand : ∀ᶠ n : ℕ in atTop,
      |f n - deg₀ * ((n : ℝ) ^ d / (d.factorial : ℝ))| ≤ C * (n : ℝ) ^ (d - 1))
    (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => f n / ((n : ℝ) ^ d / (d.factorial : ℝ))) atTop (𝓝 deg₀) := by
  have hzero : Tendsto (fun n : ℕ =>
      f n / ((n : ℝ) ^ d / (d.factorial : ℝ)) - deg₀) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (C * (d.factorial : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      simpa only [div_eq_mul_inv, mul_zero] using h1.const_mul (C * (d.factorial : ℝ))
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards [hsand, eventually_ge_atTop 1] with n hn hn1
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
    have hfac_pos : (0 : ℝ) < (d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos d)
    have hden_pos : (0 : ℝ) < (n : ℝ) ^ d / (d.factorial : ℝ) :=
      div_pos (pow_pos hn_pos d) hfac_pos
    have hdiff : f n / ((n : ℝ) ^ d / (d.factorial : ℝ)) - deg₀ =
        (f n - deg₀ * ((n : ℝ) ^ d / (d.factorial : ℝ))) / ((n : ℝ) ^ d / (d.factorial : ℝ)) := by
      field_simp [hden_pos.ne']
    rw [hdiff, Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
    calc |f n - deg₀ * ((n : ℝ) ^ d / (d.factorial : ℝ))| / ((n : ℝ) ^ d / (d.factorial : ℝ))
        ≤ (C * (n : ℝ) ^ (d - 1)) / ((n : ℝ) ^ d / (d.factorial : ℝ)) :=
          div_le_div_of_nonneg_right hn hden_pos.le
      _ = (C * (d.factorial : ℝ)) / (n : ℝ) := by
          have hpow : (n : ℝ) ^ d = (n : ℝ) ^ (d - 1) * (n : ℝ) := by
            rw [← pow_succ, Nat.sub_add_cancel hd]
          rw [hpow]
          have hnd1 : (n : ℝ) ^ (d - 1) ≠ 0 := (pow_pos hn_pos _).ne'
          field_simp [hn_pos.ne', hnd1, hfac_pos.ne']
  simpa using hzero.add_const deg₀

end MoriwakiRankBounds

/-! ## Section 5: Outright Moriwaki Bigness Theorem (`moriwakiBig_outright`) -/

section MoriwakiBigOutright

/-- Auxiliary asymptotic error decay: `(C₁ * log (k + 1) + C₂) / k → 0` as `k → ∞`. -/
private lemma tendsto_log_const_div_nat (C₁ C₂ : ℝ) :
    Tendsto (fun k : ℕ => (C₁ * Real.log ((k : ℝ) + 1) + C₂) / (k : ℝ)) atTop (𝓝 0) := by
  have hlog_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1 one_ne_zero
    simpa [pow_one, one_mul, add_zero] using h
  have hlog_k1 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    hlog_div.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hinv_nat : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div] using hinv_nat
    have hadd : Tendsto (fun k : ℕ => (1 : ℝ) + (1 : ℝ) / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at hadd
    refine hadd.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hk0]
  have hlog_k : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 0) := by
    have hprod := hlog_k1.mul hratio
    rw [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hk1]
  have hC₂ : Tendsto (fun k : ℕ => C₂ / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv_nat.const_mul C₂
  have hsum : Tendsto (fun k : ℕ => C₁ * (Real.log ((k : ℝ) + 1) / (k : ℝ)) + C₂ / (k : ℝ))
      atTop (𝓝 (C₁ * 0 + 0)) := (hlog_k.const_mul C₁).add hC₂
  simp only [mul_zero, add_zero] at hsum
  exact hsum.congr fun k => by ring

/-- **Core Eventual Normalized Volume Lower Bound (`moriwakiBig_eventually_ratio_ge`)**:
for EVERY relative dimension `d : ℕ` (both `d = 0` curves and `d ≥ 1` varieties),
every `M : MoriwakiBigDatum d`, and every `ε > 0`, eventually
`M.selfInt - ε ≤ arithVolRatio M.smallCount d k`. -/
theorem moriwakiBig_eventually_ratio_ge {d : ℕ} (M : MoriwakiBigDatum d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, M.selfInt - ε ≤ arithVolRatio M.smallCount d k := by
  have hfac_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hδ : 0 < ε / (2 * ((d + 1).factorial : ℝ)) := div_pos hε (by positivity)
  have hAHS := M.ahs_liminf (ε / (2 * ((d + 1).factorial : ℝ))) hδ
  let C₁ : ℝ := M.rankHi * ((M.bergExp : ℝ) + (d : ℝ) / 2)
  let C₂ : ℝ := M.rankHi * (Real.log (2 * M.bergConst) + (1 / 2) * Real.log M.rankHi +
    |Real.log (√Real.pi)|)
  have herr := tendsto_log_const_div_nat C₁ C₂
  have hmem_err := (Metric.tendsto_atTop.mp herr) (ε / (2 * ((d + 1).factorial : ℝ))) hδ
  filter_upwards [hAHS, eventually_ge_atTop hmem_err.choose, eventually_ge_atTop 1] with
    k hkAHS hkErr hk1
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
  have hkd1_pos : (0 : ℝ) < (k : ℝ) ^ (d + 1) := pow_pos hk_pos (d + 1)
  have hB_pos : 0 < M.bergConst * ((k : ℝ) + 1) ^ M.bergExp :=
    mul_pos (by linarith [M.bergConst_ge_one]) (pow_pos (by positivity) _)
  let Rk : ℝ := (M.bergConst * ((k : ℝ) + 1) ^ M.bergExp)⁻¹
  have hRk_pos : 0 < Rk := inv_pos.mpr hB_pos
  have hrk_pos : 1 ≤ rk (M.secLat k) := rk_pos_of_ne_bot (M.secLat k) (M.secLat_ne_bot k hk1)
  have hrk_posR : (0 : ℝ) < (rk (M.secLat k) : ℝ) := Nat.cast_pos.mpr hrk_pos
  have hcount_le : (h0ArithStrict (M.secLat k) Rk : ℝ) ≤ (M.smallSectionsCard k hk1 : ℝ) :=
    Nat.cast_le.mpr (M.h0ArithStrict_le_smallSectionsCard hk1)
  have h0_pos : (0 : ℝ) < (h0ArithStrict (M.secLat k) Rk : ℝ) := by
    have hfin : ((M.secLat k : Set (M.secSpace k)) ∩ Metric.ball 0 Rk).Finite :=
      (lattice_inter_closedBall_finite (M.secLat k) Rk).subset
        (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall)
    have hne : ((M.secLat k : Set (M.secSpace k)) ∩ Metric.ball 0 Rk).Nonempty :=
      ⟨0, (M.secLat k).zero_mem, Metric.mem_ball_self hRk_pos⟩
    exact Nat.cast_pos.mpr ((Set.ncard_pos hfin).mpr hne)
  have hlog_mono : Real.log (h0ArithStrict (M.secLat k) Rk : ℝ) ≤
      Real.log (M.smallSectionsCard k hk1 : ℝ) :=
    Real.log_le_log h0_pos hcount_le
  have hmink := log_h0ArithStrict_lower_bound (M.secLat k) hRk_pos
  have hlogω := log_unitBallVol_ge hrk_pos
  have hlog_Rk : Real.log (Rk / 2) =
      -(Real.log (2 * M.bergConst) + (M.bergExp : ℝ) * Real.log ((k : ℝ) + 1)) := by
    have h2B : Rk / 2 = (2 * M.bergConst * ((k : ℝ) + 1) ^ M.bergExp)⁻¹ := by
      unfold Rk; field_simp [hB_pos.ne']
    rw [h2B, Real.log_inv,
      Real.log_mul (by linarith [M.bergConst_ge_one]) (pow_pos (by positivity) _).ne',
      Real.log_pow]
  have hlog_rk : Real.log (rk (M.secLat k) : ℝ) ≤
      Real.log M.rankHi + (d : ℝ) * Real.log ((k : ℝ) + 1) := by
    have h1 : (rk (M.secLat k) : ℝ) ≤ M.rankHi * ((k : ℝ) + 1) ^ d := by
      calc (rk (M.secLat k) : ℝ) ≤ M.rankHi * (k : ℝ) ^ d := M.rk_le_poly k hk1
        _ ≤ M.rankHi * ((k : ℝ) + 1) ^ d :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk_pos.le (by linarith) d)
              (by linarith [M.rankHi_ge_one])
    have h2 := Real.log_le_log hrk_posR h1
    rw [Real.log_mul (by linarith [M.rankHi_ge_one]) (pow_pos (by positivity) _).ne',
      Real.log_pow] at h2
    exact h2
  have hlog_pi : (1 / 2) * Real.log Real.pi = Real.log (√Real.pi) := by
    rw [Real.log_sqrt Real.pi_pos.le]; ring
  have hloss_per_rk :
      -(Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi - (1 / 2) * Real.log (rk (M.secLat k) : ℝ)) ≤
      ((M.bergExp : ℝ) + (d : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
        (Real.log (2 * M.bergConst) + (1 / 2) * Real.log M.rankHi + |Real.log (√Real.pi)|) := by
    rw [hlog_Rk, hlog_pi]
    have hpi_abs : -Real.log (√Real.pi) ≤ |Real.log (√Real.pi)| := neg_le_abs _
    linarith
  have hloss_tot :
      -(rk (M.secLat k) : ℝ) * (Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi -
          (1 / 2) * Real.log (rk (M.secLat k) : ℝ)) ≤
      (C₁ * Real.log ((k : ℝ) + 1) + C₂) * (k : ℝ) ^ d := by
    have hpos_rhs : 0 ≤ ((M.bergExp : ℝ) + (d : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
        (Real.log (2 * M.bergConst) + (1 / 2) * Real.log M.rankHi + |Real.log (√Real.pi)|) := by
      have h1 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ Real.log (2 * M.bergConst) := Real.log_nonneg (by linarith [M.bergConst_ge_one])
      have h3 : 0 ≤ Real.log M.rankHi := Real.log_nonneg M.rankHi_ge_one
      have h4 : 0 ≤ |Real.log (√Real.pi)| := abs_nonneg _
      nlinarith [Nat.cast_nonneg (α := ℝ) M.bergExp, Nat.cast_nonneg (α := ℝ) d]
    calc -(rk (M.secLat k) : ℝ) * (Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi -
            (1 / 2) * Real.log (rk (M.secLat k) : ℝ))
        = (rk (M.secLat k) : ℝ) * (-(Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi -
            (1 / 2) * Real.log (rk (M.secLat k) : ℝ))) := by ring
      _ ≤ (M.rankHi * (k : ℝ) ^ d) *
            (((M.bergExp : ℝ) + (d : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
              (Real.log (2 * M.bergConst) + (1 / 2) * Real.log M.rankHi + |Real.log (√Real.pi)|)) := by
          calc (rk (M.secLat k) : ℝ) * _
              ≤ (rk (M.secLat k) : ℝ) * (((M.bergExp : ℝ) + (d : ℝ) / 2) * Real.log ((k : ℝ) + 1) +
                  (Real.log (2 * M.bergConst) + (1 / 2) * Real.log M.rankHi + |Real.log (√Real.pi)|)) :=
                mul_le_mul_of_nonneg_left hloss_per_rk hrk_posR.le
            _ ≤ (M.rankHi * (k : ℝ) ^ d) * _ :=
                mul_le_mul_of_nonneg_right (M.rk_le_poly k hk1) hpos_rhs
      _ = (C₁ * Real.log ((k : ℝ) + 1) + C₂) * (k : ℝ) ^ d := by
          dsimp only [C₁, C₂]; ring
  have herr_k : (C₁ * Real.log ((k : ℝ) + 1) + C₂) / (k : ℝ) ≤
      ε / (2 * ((d + 1).factorial : ℝ)) := by
    have hd := hmem_err.choose_spec k hkErr
    rw [Real.dist_eq, sub_zero] at hd
    exact (le_abs_self _).trans hd.le
  have herr_scaled : (C₁ * Real.log ((k : ℝ) + 1) + C₂) * (k : ℝ) ^ d ≤
      (ε / (2 * ((d + 1).factorial : ℝ))) * (k : ℝ) ^ (d + 1) := by
    have h1 := (div_le_iff₀ hk_pos).mp herr_k
    have hmul := mul_le_mul_of_nonneg_right h1 (pow_nonneg hk_pos.le d)
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul
  have hAHS_k : (M.selfInt / ((d + 1).factorial : ℝ) - ε / (2 * ((d + 1).factorial : ℝ))) *
      (k : ℝ) ^ (d + 1) ≤ arithDeg (M.secLat k) :=
    (le_div_iff₀ hkd1_pos).mp hkAHS
  have hcomb : arithDeg (M.secLat k) - (C₁ * Real.log ((k : ℝ) + 1) + C₂) * (k : ℝ) ^ d ≤
      Real.log (h0ArithStrict (M.secLat k) Rk : ℝ) := by
    have hstep : arithDeg (M.secLat k) +
        (rk (M.secLat k) : ℝ) * (Real.log (Rk / 2) + (1 / 2) * Real.log Real.pi -
          (1 / 2) * Real.log (rk (M.secLat k) : ℝ)) ≤
        Real.log (h0ArithStrict (M.secLat k) Rk : ℝ) := by
      have h1 : ((rk (M.secLat k) : ℝ) / 2) * Real.log Real.pi -
          ((rk (M.secLat k) : ℝ) / 2) * Real.log (rk (M.secLat k) : ℝ) =
          (rk (M.secLat k) : ℝ) * ((1 / 2) * Real.log Real.pi -
            (1 / 2) * Real.log (rk (M.secLat k) : ℝ)) := by ring
      linarith
    linarith
  have hlog_ge : ((M.selfInt - ε) / ((d + 1).factorial : ℝ)) * (k : ℝ) ^ (d + 1) ≤
      Real.log (M.smallSectionsCard k hk1 : ℝ) := by
    have hcoeff : (M.selfInt - ε) / ((d + 1).factorial : ℝ) =
        M.selfInt / ((d + 1).factorial : ℝ) - ε / (2 * ((d + 1).factorial : ℝ)) -
          ε / (2 * ((d + 1).factorial : ℝ)) := by
      field_simp [hfac_pos.ne']
      ring
    rw [hcoeff]
    linarith
  unfold arithVolRatio
  rw [M.smallCount_of_ge_one hk1, le_div_iff₀ (div_pos hkd1_pos hfac_pos)]
  have heq : (M.selfInt - ε) * ((k : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) =
      ((M.selfInt - ε) / ((d + 1).factorial : ℝ)) * (k : ℝ) ^ (d + 1) := by ring
  linarith

/-- **Exact Arakelov Volume Lower Bound (`moriwakiBig_selfInt_le_volAr`)**:
`M.selfInt ≤ M.volAr` for EVERY `d : ℕ` and EVERY `M : MoriwakiBigDatum d`. -/
theorem moriwakiBig_selfInt_le_volAr {d : ℕ} (M : MoriwakiBigDatum d) :
    M.selfInt ≤ M.volAr := by
  unfold MoriwakiBigDatum.volAr arithVol
  apply le_of_forall_lt_imp_le_of_dense
  intro b hb
  refine Filter.le_liminf_of_le M.arithVolRatio_bddAbove.isCoboundedUnder_ge ?_
  have hε : 0 < M.selfInt - b := sub_pos.mpr hb
  filter_upwards [moriwakiBig_eventually_ratio_ge M hε] with k hk
  linarith

/-- **Arithmetic Curve Case (`d = 0`, `moriwakiBig_curve_case`)**:
for an arithmetic curve `M : MoriwakiBigDatum 0`:
1. `M.selfInt ≤ M.volAr ≤ M.volArUpper`,
2. When `0 < M.selfInt`, `∃ c₀ > 0, ∃ K₀ ≥ 1, ∀ k ≥ K₀, c₀ * k ≤ log (#smallSections M k)`. -/
theorem moriwakiBig_curve_case (M : MoriwakiBigDatum 0) :
    M.selfInt ≤ M.volAr ∧ M.volAr ≤ M.volArUpper ∧
    (0 < M.selfInt →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
        ∀ k : ℕ, (hk : K₀ ≤ k) →
          c₀ * (k : ℝ) ≤ Real.log (M.smallSectionsCard k (le_trans hK₀ hk) : ℝ)) := by
  refine ⟨moriwakiBig_selfInt_le_volAr M, M.volAr_le_volArUpper, fun hpos => ?_⟩
  have hev := moriwakiBig_eventually_ratio_ge M (half_pos hpos)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K₁, hK₁⟩ := hev
  refine ⟨M.selfInt / 2, half_pos hpos, max 1 K₁, le_max_left _ _, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hkK : K₁ ≤ k := le_trans (le_max_right _ _) hk
  have hspec := hK₁ k hkK
  unfold arithVolRatio at hspec
  rw [M.smallCount_of_ge_one hk1] at hspec
  simp only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hspec
  have h1 : M.selfInt / 2 ≤ Real.log (M.smallSectionsCard k hk1 : ℝ) / (k : ℝ) := by linarith
  exact (le_div_iff₀ (Nat.cast_pos.mpr hk1)).mp h1

/-- **Higher-Dimensional Case (`d ≥ 1`, `moriwakiBig_higher_dim`)**:
directly links `MoriwakiBigDatum d` (`1 ≤ d`) to `Stage12SchurWeylLattices.moriwaki_big_small_sections`
and proves `M.selfInt ≤ M.volAr ≤ M.volArUpper` plus exponential growth `c₀ * k^(d + 1)`. -/
theorem moriwakiBig_higher_dim {d : ℕ} (hd : 1 ≤ d) (M : MoriwakiBigDatum d) :
    M.selfInt ≤ M.volAr ∧ M.volAr ≤ M.volArUpper ∧
    (0 < M.selfInt →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
        ∀ k : ℕ, (hk : K₀ ≤ k) →
          c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (M.smallSectionsCard k (le_trans hK₀ hk) : ℝ)) := by
  refine ⟨moriwakiBig_selfInt_le_volAr M, M.volAr_le_volArUpper, fun hpos => ?_⟩
  exact moriwaki_big_small_sections (M.toGradedHermAlgebra hd) hpos

/-- **OUTRIGHT MORIWAKI ARITHMETIC BIGNESS THEOREM (`moriwakiBig_outright`)**:
unified for EVERY relative dimension `d : ℕ` (stitching `d = 0` arithmetic curves and `d ≥ 1`
higher-dimensional arithmetic varieties via Minkowski's theorem and `Stage12SchurWeylLattices`).
For any `M : MoriwakiBigDatum d`:
1. `M.selfInt ≤ M.volAr` (`liminf` arithmetic volume lower bound),
2. `M.selfInt ≤ M.volArUpper` (`limsup` `MoriwakiBigStatement` bound `II ≤ arVolP`),
3. `0 < M.selfInt → M.IsArithBig` (`0 < vol_Ar(L)`),
4. `0 < M.selfInt → ∃ c₀ > 0, ∃ K₀ ≥ 1, ∀ k ≥ K₀, c₀ * k^(d+1) ≤ log (#smallSections M k)`,
5. `0 < M.selfInt → ∃ K₀ ≥ 1, ∀ k ≥ K₀, ∃ s : M.secLat k, s ≠ 0 ∧ M.supNorm k s.1 < 1`,
6. `0 < M.selfInt → ∀ N : ℕ, ∀ᶠ k in atTop, N ≤ M.smallCount k` (unboundedly many strictly
   small integral global sections!). -/
theorem moriwakiBig_outright {d : ℕ} (M : MoriwakiBigDatum d) :
    M.selfInt ≤ M.volAr ∧
    M.selfInt ≤ M.volArUpper ∧
    (0 < M.selfInt → M.IsArithBig) ∧
    (0 < M.selfInt →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
        ∀ k : ℕ, (hk : K₀ ≤ k) →
          c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (M.smallSectionsCard k (le_trans hK₀ hk) : ℝ)) ∧
    (0 < M.selfInt →
      ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k →
        ∃ s : M.secLat k, s ≠ 0 ∧ M.supNorm k s.1 < 1) ∧
    (0 < M.selfInt → ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, N ≤ M.smallCount k) := by
  have hvol : M.selfInt ≤ M.volAr := moriwakiBig_selfInt_le_volAr M
  have hvolU : M.selfInt ≤ M.volArUpper := hvol.trans M.volAr_le_volArUpper
  have hbig : 0 < M.selfInt → M.IsArithBig := fun hpos => lt_of_lt_of_le hpos hvol
  have hexp : 0 < M.selfInt →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
        ∀ k : ℕ, (hk : K₀ ≤ k) →
          c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (M.smallSectionsCard k (le_trans hK₀ hk) : ℝ) := by
    intro hpos
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨c₀, hc₀, K₀, hK₀, hbd⟩ := (moriwakiBig_curve_case M).2.2 hpos
      exact ⟨c₀, hc₀, K₀, hK₀, fun k hk => by simpa only [Nat.zero_add, pow_one] using hbd k hk⟩
    · exact (moriwakiBig_higher_dim hd M).2.2 hpos
  have hnz : 0 < M.selfInt →
      ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k →
        ∃ s : M.secLat k, s ≠ 0 ∧ M.supNorm k s.1 < 1 := by
    intro hpos
    obtain ⟨c₀, hc₀, K₀, hK₀, hlog⟩ := hexp hpos
    refine ⟨K₀, hK₀, fun k hk => ?_⟩
    have hk1 : 1 ≤ k := le_trans hK₀ hk
    have hlt : 0 < Real.log (M.smallSectionsCard k hk1 : ℝ) :=
      lt_of_lt_of_le (mul_pos hc₀ (pow_pos (Nat.cast_pos.mpr hk1) (d + 1))) (hlog k hk)
    have hgt1 : 1 < M.smallSectionsCard k hk1 := by
      by_contra hle
      have hcard_le : (M.smallSectionsCard k hk1 : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_not_lt hle
      have hlog_le : Real.log (M.smallSectionsCard k hk1 : ℝ) ≤ 0 := by
        by_cases h0 : M.smallSectionsCard k hk1 = 0
        · simp [h0]
        · exact (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)) hcard_le).trans
            (by simp)
      linarith
    obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp hgt1
    by_cases hs10 : s₁ = 0
    · exact ⟨s₂, fun h => hne (hs10.trans h.symm),
        ((M.smallSections_finite hk1).mem_toFinset).mp hs₂⟩
    · exact ⟨s₁, hs10, ((M.smallSections_finite hk1).mem_toFinset).mp hs₁⟩
  have hunb : 0 < M.selfInt → ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, N ≤ M.smallCount k := by
    intro hpos N
    obtain ⟨c₀, hc₀, K₀, hK₀, hlog⟩ := hexp hpos
    obtain ⟨K₁, hK₁⟩ := exists_nat_gt (Real.log ((N : ℝ) + 1) / c₀)
    rw [Filter.eventually_atTop]
    refine ⟨max K₀ (max 1 K₁), fun k hk => ?_⟩
    have hkK₀ : K₀ ≤ k := le_trans (le_max_left _ _) hk
    have hk1 : 1 ≤ k := le_trans hK₀ hkK₀
    have hkK₁ : K₁ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    have hkR : Real.log ((N : ℝ) + 1) / c₀ < (k : ℝ) := lt_of_lt_of_le hK₁ (by exact_mod_cast hkK₁)
    have hk_le_pow : (k : ℝ) ≤ (k : ℝ) ^ (d + 1) := by
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (k : ℝ) ^ (d + 1) := pow_le_pow_right₀ hk1R (Nat.succ_pos d)
    have hlogN_lt : Real.log ((N : ℝ) + 1) < Real.log (M.smallSectionsCard k hk1 : ℝ) := by
      have h1 : Real.log ((N : ℝ) + 1) < c₀ * (k : ℝ) := by
        linarith [(div_lt_iff₀ hc₀).mp hkR]
      have h2 : c₀ * (k : ℝ) ≤ c₀ * (k : ℝ) ^ (d + 1) :=
        mul_le_mul_of_nonneg_left hk_le_pow hc₀.le
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (hlog k hkK₀)
    have hcard_pos : (0 : ℝ) < (M.smallSectionsCard k hk1 : ℝ) :=
      Nat.cast_pos.mpr (M.one_le_smallSectionsCard hk1)
    have hN_lt : (N : ℝ) + 1 < (M.smallSectionsCard k hk1 : ℝ) := by
      by_contra hle
      have h1 := Real.log_le_log hcard_pos (le_of_not_gt hle)
      linarith
    rw [M.smallCount_of_ge_one hk1]
    have hN_le : (N : ℝ) ≤ (M.smallSectionsCard k hk1 : ℝ) := by linarith
    exact_mod_cast hN_le
  exact ⟨hvol, hvolU, hbig, hexp, hnz, hunb⟩

/-- **Two-Sided Finite Arakelov Volume Sandwich (`moriwakiBig_two_sided_volAr`)**:
combines `moriwakiBig_outright` with sphere-packing `volArUpper_le` to pin down `vol_Ar(M)`
and `vol_Ar⁺(M)` inside an explicit finite positive interval whenever `0 < M.selfInt`. -/
theorem moriwakiBig_two_sided_volAr {d : ℕ} (M : MoriwakiBigDatum d) :
    M.selfInt ≤ M.volAr ∧
    M.volAr ≤ M.volArUpper ∧
    M.volArUpper ≤
      ((d + 1).factorial : ℝ) * (M.rankHi * (M.slopeHi + Real.log (2 * M.volConst + 1))) :=
  ⟨moriwakiBig_selfInt_le_volAr M, M.volAr_le_volArUpper, M.volArUpper_le⟩

/-- **Metric-Twist Bigness Criterion (`moriwakiBig_of_metric_twist`)**:
if `M.selfInt + (d + 1) * degLo * t > 0` for `t ≥ 0` and generic lower degree `degLo ≥ 0`,
then the twisted datum `M.twistMetric t ht degLo hdegLo hrk_lo` is arithmetically big
(`0 < vol_Ar`) and admits exponentially many strictly small global sections. -/
theorem moriwakiBig_of_metric_twist {d : ℕ} (M : MoriwakiBigDatum d)
    {t degLo : ℝ} (ht : 0 ≤ t)
    (hrk_lo : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      degLo / (d.factorial : ℝ) - ε ≤ (rk (M.secLat k) : ℝ) / (k : ℝ) ^ d)
    (hpos : 0 < M.selfInt + ((d + 1 : ℕ) : ℝ) * degLo * t) :
    let Mt := M.twistMetric t ht degLo hrk_lo
    Mt.IsArithBig ∧
    M.selfInt + ((d + 1 : ℕ) : ℝ) * degLo * t ≤ Mt.volAr ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (Mt.smallSectionsCard k (le_trans hK₀ hk) : ℝ)) := by
  intro Mt
  have hout := moriwakiBig_outright Mt
  exact ⟨hout.2.2.1 hpos, hout.1, hout.2.2.2.1 hpos⟩

/-! ### Arithmetic Small-Section Generation Over the Segre Join Twist (`generates_over_segre_join_twist`) -/

/-- **Arithmetic Small-Section Segre-Join Bridge (`SmallSectionSegreBridge`)**:
links a big arithmetic datum `M : MoriwakiBigDatum d` to a `SegreJoinTwist` graded algebra:
at every degree `k ≥ K_gen`, small global sections of `M.secLat k` evaluate via an algebra
chart realization `evalSec k : M.secLat k → Ω` into sections of the `k`-th scaled Segre join
twist, with generating tuples `genSec k : Fin (genCard k) → M.secLat k` realizing Segre-join
generation once the Moriwaki bigness threshold `k ≥ K_gen` is crossed. -/
structure SmallSectionSegreBridge (d : ℕ) (S : Type uS) (Ω : Type uΩ) [CommRing S] [Field Ω]
    (φ : S →+* Ω) (K : Type uK) [Fintype K] [DecidableEq K] (ι : K → Type uK) where
  datum : MoriwakiBigDatum.{u} d
  twist : SegreJoinTwist S Ω φ K ι
  evalSec : ∀ k : ℕ, datum.secLat k → Ω
  threshold : ℕ
  threshold_ge_one : 1 ≤ threshold
  genCard : ℕ → ℕ
  genSec : ∀ k : ℕ, Fin (genCard k) → datum.secLat k
  genSec_small : ∀ k, threshold ≤ k → ∀ j : Fin (genCard k),
    genSec k j ∈ datum.smallSectionsSet k
  genSec_segre_mem : ∀ k, threshold ≤ k → ∀ j : Fin (genCard k),
    evalSec k (genSec k j) ∈ secOver φ (segreJoin twist.y) (twist.scaleBy k).segreDeg
  genSec_segre_generates : ∀ k, threshold ≤ k →
    GeneratesOver φ (segreJoin twist.y) (twist.scaleBy k).segreDeg
      (fun j => evalSec k (genSec k j))

/-- **PROVED GENERATION OVER THE SEGRE JOIN TWIST (`generates_over_segre_join_twist`)**:
whenever a `SmallSectionSegreBridge` satisfies the Moriwaki bigness threshold
`0 < B.datum.selfInt`, there exist `c₀ > 0` and an effective degree threshold `K₀ ≥ B.threshold`
such that for EVERY `k ≥ K₀`:
1. The small-section family `j ↦ B.evalSec k (B.genSec k j)` consists exclusively of strictly
   small global sections (`B.datum.supNorm k (B.genSec k j).1 < 1`),
2. Every element of the family lies in `secOver φ B.twist.y (k • (β + diagShift c))`,
3. The family generates over `B.twist.y` in the diagonally twisted degree `k • (β + diagShift c)`:
   `GeneratesOver φ B.twist.y (k • (B.twist.baseWeight + diagShift B.twist.twist)) _`,
4. The ambient space of strictly small global sections has exponential growth
   `c₀ * (k : ℝ)^(d + 1) ≤ Real.log (B.datum.smallSectionsCard k _)` and positive arithmetic
   volume `0 < B.datum.volAr`! -/
theorem generates_over_segre_join_twist {d : ℕ} {S : Type uS} {Ω : Type uΩ} [CommRing S] [Field Ω]
    {φ : S →+* Ω} {K : Type uK} [Fintype K] [DecidableEq K] {ι : K → Type uK}
    (B : SmallSectionSegreBridge.{u} d S Ω φ K ι) (hbig : 0 < B.datum.selfInt) :
    B.datum.IsArithBig ∧
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : B.threshold ≤ K₀,
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        (∀ j : Fin (B.genCard k), B.datum.supNorm k (B.genSec k j).1 < 1) ∧
        (∀ j : Fin (B.genCard k),
          B.evalSec k (B.genSec k j) ∈
            secOver φ B.twist.y (k • (B.twist.baseWeight + diagShift B.twist.twist))) ∧
        GeneratesOver φ B.twist.y (k • (B.twist.baseWeight + diagShift B.twist.twist))
          (fun j => B.evalSec k (B.genSec k j)) ∧
        c₀ * (k : ℝ) ^ (d + 1) ≤
          Real.log (B.datum.smallSectionsCard k
            (le_trans B.threshold_ge_one (le_trans hK₀ hk)) : ℝ) := by
  have hout := moriwakiBig_outright B.datum
  obtain ⟨c₀, hc₀, K₁, hK₁, hlog⟩ := hout.2.2.2.1 hbig
  refine ⟨hout.2.2.1 hbig, c₀, hc₀, max B.threshold K₁, le_max_left _ _, fun k hk => ?_⟩
  have hkT : B.threshold ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : K₁ ≤ k := le_trans (le_max_right _ _) hk
  have htw_eq : (B.twist.scaleBy k).twistedDeg =
      k • (B.twist.baseWeight + diagShift B.twist.twist) :=
    B.twist.twistedDeg_scaleBy k
  refine ⟨fun j => B.genSec_small k hkT j,
    fun j => ?_,
    ?_,
    hlog k hk1⟩
  · rw [← htw_eq]
    exact (B.twist.scaleBy k).secOver_segreJoin_subset (B.genSec_segre_mem k hkT j)
  · rw [← htw_eq]
    exact (B.twist.scaleBy k).generates_twisted _ (B.genSec_segre_generates k hkT)

end MoriwakiBigOutright

/-! ## Section 6: Concrete Zero-Assumption Realizations (Proving Non-Vacuousness) -/

section ConcreteZeroAssumptionRealizations

/-! ### Exact `lambda1` Lower Bound for Diagonal Euclidean Lattices `diagLat` -/

/-- For any diagonal lattice `diagLat c` (`c i > 0`, `Nonempty ι`), if every basis norm satisfies
`m ≤ c i`, then `m ≤ lambda1 (diagLat c)`. -/
theorem le_lambda1_diagLat {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) {m : ℝ} (hm : ∀ i, m ≤ c i) :
    m ≤ lambda1 (diagLat c) := by
  have hinv := diagLat_invariants c hc
  have : DiscreteTopology (diagLat c) := hinv.1
  have hne : diagLat c ≠ ⊥ := by
    intro hbot
    have hrk := hinv.2.1
    rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) = 0 by simp [rk]] at hrk
    exact Fintype.card_pos.ne hrk
  obtain ⟨v₀, hv₀L, hv₀0, hnorm⟩ :=
    RHDirect.Stage2SiegelReduction.exists_norm_eq_lambda1 (diagLat c) hne
  rw [← hnorm]
  -- Decompose `v₀ ∈ diagLat c = span ℤ {c i • e_i}` into integer coordinates `a : ι → ℤ`.
  have hv₀_span : v₀ ∈ Submodule.span ℤ
      (Set.range fun i : ι => c i • EuclideanSpace.single i (1 : ℝ)) := hv₀L
  rw [Submodule.mem_span_range_iff_exists_fun] at hv₀_span
  obtain ⟨a, ha⟩ := hv₀_span
  have ha_ne : ∃ i₀ : ι, a i₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv₀0
    rw [← ha]
    simp [hall]
  obtain ⟨i₀, hi₀⟩ := ha_ne
  have hcoord : v₀.ofLp i₀ = (a i₀ : ℝ) * c i₀ := by
    rw [← ha]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, zsmul_eq_mul]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  have ha_ge1 : (1 : ℝ) ≤ |(a i₀ : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |a i₀| := Int.one_le_abs hi₀
    exact_mod_cast h1
  have hcoord_le_norm : |v₀.ofLp i₀| ≤ ‖v₀‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v₀ i₀
  have hmul : c i₀ ≤ |v₀.ofLp i₀| := by
    rw [hcoord, abs_mul, abs_of_pos (hc i₀)]
    nlinarith [hc i₀]
  exact (hm i₀).trans (hmul.trans hcoord_le_norm)

/-- Exact `lambda1` lower bound for `symPowMonomialLat (fun _ => exp(-α)) k`:
`exp(-(α * k)) ≤ lambda1 (symPowMonomialLat (fun _ => exp(-α)) k)`. -/
theorem exp_le_lambda1_symPowMonomialLat {r : ℕ} (hr : 1 ≤ r) (α : ℝ) (k : ℕ) :
    Real.exp (-α * (k : ℝ)) ≤
      lambda1 (symPowMonomialLat (fun _ : Fin r => Real.exp (-α)) k) := by
  have : Nonempty (MultiIndex r k) :=
    Fintype.card_pos_iff.mp (card_multiIndex_pos hr k)
  refine le_lambda1_diagLat
    (fun β : MultiIndex r k => (1 : ℝ) * ∏ i : Fin r, Real.exp (-α) ^ (β.1 i))
    (fun β => mul_pos zero_lt_one (Finset.prod_pos fun _ _ => pow_pos (Real.exp_pos _) _))
    fun β => ?_
  simp only [one_mul]
  have hprod : (∏ i : Fin r, Real.exp (-α) ^ (β.1 i)) = Real.exp (-α * (k : ℝ)) := by
    have hterm : ∀ i : Fin r, Real.exp (-α) ^ (β.1 i) = Real.exp ((β.1 i : ℝ) * (-α)) :=
      fun i => (Real.exp_nat_mul (-α) (β.1 i)).symm
    simp_rw [hterm, ← Real.exp_sum, ← Finset.sum_mul]
    congr 1
    have hsum : (∑ i : Fin r, (β.1 i : ℝ)) = (k : ℝ) := by
      exact_mod_cast β.2
    rw [hsum, mul_comm]
  rw [hprod]

/-! ### Realization 1: Projective Space `ℙ^d` (`d ≥ 1`, `α > 0`) -/

/-- **0-Assumption Projective-Space `MoriwakiBigDatum d` (`projSpaceMoriwakiBigDatum`)**
for arbitrary dimension `d ≥ 1` and Arakelov slope `α > 0`, realizing
`(ℙ^d, 𝒪(1)_{-α})` with `selfInt = α * (d + 1) > 0`. -/
def projSpaceMoriwakiBigDatum (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    MoriwakiBigDatum d :=
  MoriwakiBigDatum.ofGradedHermAlgebra
    (projSpaceGradedHermAlgebra d hd hα)
    α hα.le
    (fun k _ => exp_le_lambda1_symPowMonomialLat (Nat.succ_pos d) α k)

/-- **0-Assumption Projective-Space Outright Moriwaki Bigness (`projSpace_moriwakiBig_outright`)**:
verifies every conclusion of `moriwakiBig_outright` unconditionally on `ℙ^d` (`d ≥ 1`, `α > 0`). -/
theorem projSpace_moriwakiBig_outright (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    let M := projSpaceMoriwakiBigDatum d hd hα
    α * ((d + 1 : ℕ) : ℝ) ≤ M.volAr ∧
    M.IsArithBig ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∃ hK₀ : 1 ≤ K₀,
      ∀ k : ℕ, (hk : K₀ ≤ k) →
        c₀ * (k : ℝ) ^ (d + 1) ≤ Real.log (M.smallSectionsCard k (le_trans hK₀ hk) : ℝ)) ∧
    (∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k →
      ∃ s : M.secLat k, s ≠ 0 ∧ M.supNorm k s.1 < 1) := by
  intro M
  have hpos : 0 < M.selfInt := mul_pos hα (Nat.cast_pos.mpr (Nat.succ_pos d))
  have hout := moriwakiBig_outright M
  exact ⟨hout.1, hout.2.2.1 hpos, hout.2.2.2.1 hpos, hout.2.2.2.2.1 hpos⟩

/-- **Exact Binomial Hilbert–Samuel Asymptotic on `ℙ^d` (`tendsto_choose_div_pow_factorial`)**:
for every `d : ℕ`, `(Nat.choose (n + d) d : ℝ) / ((n : ℝ)^d / d!) → 1` as `n → ∞`. -/
theorem tendsto_choose_div_pow_factorial (d : ℕ) :
    Tendsto (fun n : ℕ => (Nat.choose (n + d) d : ℝ) / ((n : ℝ) ^ d / (d.factorial : ℝ)))
      atTop (𝓝 1) := by
  have hprod : Tendsto (fun n : ℕ => ∏ i ∈ Finset.range d, ((n : ℝ) + (d : ℝ) - (i : ℝ)) / (n : ℝ))
      atTop (𝓝 (∏ _i ∈ Finset.range d, (1 : ℝ))) := by
    refine tendsto_finsetProd (Finset.range d) fun i _ => ?_
    have hinv : Tendsto (fun n : ℕ => ((d : ℝ) - (i : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      simpa only [div_eq_mul_inv, mul_zero] using h1.const_mul ((d : ℝ) - (i : ℝ))
    have hadd : Tendsto (fun n : ℕ => (1 : ℝ) + ((d : ℝ) - (i : ℝ)) / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at hadd
    refine hadd.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn0]
    ring
  rw [Finset.prod_const_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hfac_ne : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hdvd : d.factorial ∣ (n + d).descFactorial d := Nat.factorial_dvd_descFactorial _ d
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div hdvd hfac_ne,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hcongr : ∏ i ∈ Finset.range d, ((n + d - i : ℕ) : ℝ) =
      ∏ i ∈ Finset.range d, ((n : ℝ) + (d : ℝ) - (i : ℝ)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi_lt : i < d := Finset.mem_range.mp hi
    have hle : i ≤ n + d := by omega
    rw [Nat.cast_sub hle, Nat.cast_add]
  rw [hcongr]
  have hnd : (n : ℝ) ^ d ≠ 0 := (pow_pos hn_pos d).ne'
  field_simp [hfac_ne, hnd]

/-- **0-Assumption Projective-Space `ShiftRankDatum d` (`projSpaceShiftRankDatum`)**:
verifies `moriwaki_rank_bounds_generic` unconditionally on `ℙ^d` with `genDeg q = 1`
and `sepConst = α` for every `d : ℕ` and `α > 0`. -/
def projSpaceShiftRankDatum (d : ℕ) {α : ℝ} (hα : 0 < α) : ShiftRankDatum d where
  secSpace _ n := EuclideanSpace ℝ (MultiIndex (d + 1) n)
  secLat q n := symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) n
  discLat q n :=
    (arithDeg_symPowWeightedLat (Nat.succ_pos d)
      (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) (fun _ => Real.exp_pos _)
      (fun _ : MultiIndex (d + 1) n => (1 : ℝ)) (fun _ => zero_lt_one)).1
  secLat_ne_bot q _ n _ := by
    intro hbot
    have hrk := (arithDeg_symPowWeightedLat (Nat.succ_pos d)
      (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) (fun _ => Real.exp_pos _)
      (fun _ : MultiIndex (d + 1) n => (1 : ℝ)) (fun _ => zero_lt_one)).2.1
    change rk (symPowWeightedLat _ _) = _ at hrk
    change symPowWeightedLat _ _ = ⊥ at hbot
    rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (MultiIndex (d + 1) n))) = 0 by
      simp [rk]] at hrk
    exact (card_multiIndex_pos (Nat.succ_pos d) n).ne hrk
  genDeg _ := 1
  genDeg_nonneg _ _ := zero_le_one
  rank_tendsto q _ := by
    have hrk_eq : ∀ n, rk (symPowMonomialLat
        (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) n) = Nat.choose (n + d) d := by
      intro n
      have hrk := (arithDeg_symPowWeightedLat (Nat.succ_pos d)
        (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) (fun _ => Real.exp_pos _)
        (fun _ : MultiIndex (d + 1) n => (1 : ℝ)) (fun _ => zero_lt_one)).2.1
      change rk (symPowWeightedLat _ _) = _ at hrk
      change rk (symPowWeightedLat _ _) = _
      rw [hrk, card_multiIndex (Nat.succ_pos d) n, show n + (d + 1) - 1 = n + d by omega,
        add_comm n d, ← Nat.choose_symm_add, add_comm d n]
    simp_rw [hrk_eq]
    exact tendsto_choose_div_pow_factorial d
  smallSet q n :=
    letI : DiscreteTopology
        (symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) n) :=
      (arithDeg_symPowWeightedLat (Nat.succ_pos d)
        (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) (fun _ => Real.exp_pos _)
        (fun _ : MultiIndex (d + 1) n => (1 : ℝ)) (fun _ => zero_lt_one)).1
    (lattice_inter_closedBall_finite
      (symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) n) 1).toFinset
  smallSet_mem q n x hx := by
    have : DiscreteTopology
        (symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) n) :=
      (arithDeg_symPowWeightedLat (Nat.succ_pos d)
        (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) (fun _ => Real.exp_pos _)
        (fun _ : MultiIndex (d + 1) n => (1 : ℝ)) (fun _ => zero_lt_one)).1
    exact ((lattice_inter_closedBall_finite _ 1).mem_toFinset.mp hx).1
  smallSet_norm_le q n x hx := by
    have : DiscreteTopology
        (symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) n) :=
      (arithDeg_symPowWeightedLat (Nat.succ_pos d)
        (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) (fun _ => Real.exp_pos _)
        (fun _ : MultiIndex (d + 1) n => (1 : ℝ)) (fun _ => zero_lt_one)).1
    exact mem_closedBall_zero_iff.mp ((lattice_inter_closedBall_finite _ 1).mem_toFinset.mp hx).2
  sepConst := α
  sepConst_nonneg := hα.le
  smallSet_sep q _ n _ x hx y hy hxy := by
    have : DiscreteTopology
        (symPowMonomialLat (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) n) :=
      (arithDeg_symPowWeightedLat (Nat.succ_pos d)
        (fun _ : Fin (d + 1) => Real.exp (-(α * ((q : ℝ) + 1)))) (fun _ => Real.exp_pos _)
        (fun _ : MultiIndex (d + 1) n => (1 : ℝ)) (fun _ => zero_lt_one)).1
    have hxL := ((lattice_inter_closedBall_finite _ 1).mem_toFinset.mp hx).1
    have hyL := ((lattice_inter_closedBall_finite _ 1).mem_toFinset.mp hy).1
    have hlam := exp_le_lambda1_symPowMonomialLat (Nat.succ_pos d) (α * ((q : ℝ) + 1)) n
    have hnorm := lambda1_le_norm _ (Submodule.sub_mem _ hxL hyL) (sub_ne_zero.mpr hxy)
    have hexp_le : Real.exp (-((α + 1) * (n : ℝ) * ((q : ℝ) + 1))) ≤
        Real.exp (-(α * ((q : ℝ) + 1)) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hnn : 0 ≤ (n : ℝ) * ((q : ℝ) + 1) := by positivity
      nlinarith
    exact hexp_le.trans (hlam.trans hnorm)

/-- **0-Assumption Projective-Space Generic Rank & Shift-Volume Bounds**. -/
theorem projSpace_moriwaki_rank_bounds (d : ℕ) {α : ℝ} (hα : 0 < α) (q : ℕ) (hq : 1 ≤ q) :
    arithVolUpper ((projSpaceShiftRankDatum d hα).smallCount q) d ≤
      2 * (α + 1) * ((d : ℝ) + 1) * ((q : ℝ) + 1) := by
  have h := (moriwaki_rank_bounds_generic (projSpaceShiftRankDatum d hα) q hq).2.2.2
  simpa [projSpaceShiftRankDatum] using h

/-! ### Realization 2: Concrete Arithmetic Curve (`d = 0`) -/

/-- **0-Assumption Arithmetic Curve `MoriwakiBigDatum 0` (`arithCurveMoriwakiBigDatum`)**:
rank-`r` (`r ≥ 1`) diagonal lattice scaled by `e^{-k α}` (`α > 0`), with `selfInt = r * α > 0`. -/
def arithCurveMoriwakiBigDatum (r : ℕ) (hr : 1 ≤ r) {α : ℝ} (hα : 0 < α) :
    MoriwakiBigDatum 0 where
  secSpace _ := EuclideanSpace ℝ (Fin r)
  secLat k := diagLat (fun _ : Fin r => Real.exp (-(k : ℝ) * α))
  discLat k := (diagLat_invariants (fun _ : Fin r => Real.exp (-(k : ℝ) * α))
    (fun _ => Real.exp_pos _)).1
  secLat_ne_bot k _ := by
    intro hbot
    have hrk := (diagLat_invariants (fun _ : Fin r => Real.exp (-(k : ℝ) * α))
      (fun _ => Real.exp_pos _)).2.1
    rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin r))) = 0 by simp [rk],
      Fintype.card_fin] at hrk
    omega
  supNorm _ s := ‖s‖
  supNorm_nonneg _ s := norm_nonneg s
  volConst := 1
  volConst_pos := zero_lt_one
  norm_le_vol_supNorm _ _ s := by simp
  bergConst := 1
  bergExp := 0
  bergConst_ge_one := le_rfl
  supNorm_le_bergman _ _ s := by simp
  rankHi := (r : ℝ)
  rankHi_ge_one := by exact_mod_cast hr
  rk_le_poly k _ := by
    rw [(diagLat_invariants (fun _ : Fin r => Real.exp (-(k : ℝ) * α))
      (fun _ => Real.exp_pos _)).2.1, Fintype.card_fin, pow_zero, mul_one]
  slopeHi := α
  slopeHi_nonneg := hα.le
  lambda1_lower k _ := by
    have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    refine le_lambda1_diagLat (fun _ : Fin r => Real.exp (-(k : ℝ) * α))
      (fun _ => Real.exp_pos _) fun _ => ?_
    have heq : -α * (k : ℝ) = -(k : ℝ) * α := by ring
    rw [heq]
  selfInt := (r : ℝ) * α
  ahs_liminf ε hε := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hdeg := (diagLat_invariants (fun _ : Fin r => Real.exp (-(k : ℝ) * α))
      (fun _ => Real.exp_pos _)).2.2.2
    rw [hdeg]
    simp only [Real.log_exp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsimp : -((r : ℝ) * (-(k : ℝ) * α)) / (k : ℝ) = (r : ℝ) * α := by
      field_simp [hk_ne]
    rw [hsimp]
    linarith

/-- **0-Assumption Arithmetic Curve Outright Moriwaki Bigness (`arithCurve_moriwakiBig_outright`)**. -/
theorem arithCurve_moriwakiBig_outright (r : ℕ) (hr : 1 ≤ r) {α : ℝ} (hα : 0 < α) :
    let M := arithCurveMoriwakiBigDatum r hr hα
    (r : ℝ) * α ≤ M.volAr ∧ M.IsArithBig ∧
    (∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k →
      ∃ s : M.secLat k, s ≠ 0 ∧ M.supNorm k s.1 < 1) := by
  intro M
  have hpos : 0 < M.selfInt := mul_pos (Nat.cast_pos.mpr hr) hα
  have hout := moriwakiBig_outright M
  exact ⟨hout.1, hout.2.2.1 hpos, hout.2.2.2.2.1 hpos⟩

/-! ### Realization 3: CM Hermitian Lattice Symmetric-Power Realization -/

/-- **0-Assumption CM Hermitian Lattice Metric-Twisted `MoriwakiBigDatum 0`**:
given any arbitrary-rank `CMHermLattice d_cm r` from `Stage12SchurWeylLattices`, twisting by
`t > -slope Λ.euclLat` produces an arithmetically big `MoriwakiBigDatum 0` realizing the CM
Hermitian lattice family with explicit positive Arakelov volume! -/
def cmHermMoriwakiBigDatum {d_cm r : ℕ} (Λ : CMHermLattice d_cm r)
    {t : ℝ} (ht : 0 ≤ t) (hlam_c : ℝ) (hlam_pos : 0 ≤ hlam_c)
    (hlam_lo : Real.exp (-hlam_c) ≤ lambda1 Λ.euclLat) :
    MoriwakiBigDatum 0 where
  secSpace _ := EuclideanSpace ℝ (Fin (2 * r))
  secLat k := scaleLat (Real.exp (-(k : ℝ) * t)) Λ.euclLat
  discLat k := (scaleLat_invariants Λ.euclLat (Real.exp_pos (-(k : ℝ) * t))).1
  secLat_ne_bot k _ := by
    intro hbot
    have hrk := (scaleLat_invariants Λ.euclLat (Real.exp_pos (-(k : ℝ) * t))).2.1
    rw [hbot, show rk (⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * r)))) = 0 by simp [rk]] at hrk
    exact (rk_pos_of_ne_bot Λ.euclLat Λ.euclLat_ne_bot).ne hrk
  supNorm _ s := ‖s‖
  supNorm_nonneg _ s := norm_nonneg s
  volConst := 1
  volConst_pos := zero_lt_one
  norm_le_vol_supNorm _ _ s := by simp
  bergConst := 1
  bergExp := 0
  bergConst_ge_one := le_rfl
  supNorm_le_bergman _ _ s := by simp
  rankHi := ((2 * r : ℕ) : ℝ)
  rankHi_ge_one := by
    have := Λ.hr
    exact_mod_cast (by omega : 1 ≤ 2 * r)
  rk_le_poly k _ := by
    rw [(scaleLat_invariants Λ.euclLat (Real.exp_pos (-(k : ℝ) * t))).2.1, Λ.rk_euclLat, pow_zero,
      mul_one]
  slopeHi := hlam_c + t
  slopeHi_nonneg := add_nonneg hlam_pos ht
  lambda1_lower k hk := by
    rw [MoriwakiBigDatum.lambda1_scaleLat Λ.euclLat Λ.euclLat_ne_bot (Real.exp_pos (-(k : ℝ) * t))]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hstep : Real.exp (-(hlam_c + t) * (k : ℝ)) ≤
        Real.exp (-(k : ℝ) * t) * Real.exp (-hlam_c) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    exact hstep.trans (mul_le_mul_of_nonneg_left hlam_lo (Real.exp_pos _).le)
  selfInt := ((2 * r : ℕ) : ℝ) * t
  ahs_liminf ε hε := by
    have hinv : Tendsto (fun k : ℕ => arithDeg Λ.euclLat / (k : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      simpa only [div_eq_mul_inv, mul_zero] using h1.const_mul (arithDeg Λ.euclLat)
    have hmem := (Metric.tendsto_atTop.mp hinv) ε hε
    filter_upwards [eventually_ge_atTop hmem.choose, eventually_ge_atTop 1] with k hk hk1
    have hdeg := (scaleLat_invariants Λ.euclLat (Real.exp_pos (-(k : ℝ) * t))).2.2.2
    rw [hdeg, Real.log_exp, Λ.rk_euclLat]
    simp only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsplit : (arithDeg Λ.euclLat - ((2 * r : ℕ) : ℝ) * (-(k : ℝ) * t)) / (k : ℝ) =
        arithDeg Λ.euclLat / (k : ℝ) + ((2 * r : ℕ) : ℝ) * t := by
      field_simp [hk_ne]
      ring
    rw [hsplit]
    have hd := hmem.choose_spec k hk
    rw [Real.dist_eq, sub_zero] at hd
    linarith [(abs_lt.mp hd).1]

/-! ### Realization 4: Concrete Multi-Projective Segre-Join Twist & Small-Section Bridge over `ℚ` -/

/-- Standard multi-projective Segre-join twist at the all-ones point `y ⟨k, i⟩ = 1 : ℚ`
over `Int.castRingHom ℚ`. -/
def stdMultiProjSegreJoinTwist (K : Type uK) [Fintype K] [DecidableEq K]
    (ι : K → Type uK) [∀ k, Nonempty (ι k)] (β : K → ℤ) (c : ℤ) :
    SegreJoinTwist ℤ ℚ (Int.castRingHom ℚ) K ι where
  y _ := (1 : ℚ)
  nondegenerate k := ⟨Classical.arbitrary (ι k), one_ne_zero⟩
  baseWeight := β
  twist := c

/-- Constant unit section `1 : ℚ` generates over the Segre join of `stdMultiProjSegreJoinTwist`
for EVERY multi-degree `(β, c)`! -/
theorem stdMultiProj_generatesOver_segreJoin (K : Type uK) [Fintype K] [DecidableEq K]
    (ι : K → Type uK) [∀ k, Nonempty (ι k)] (β : K → ℤ) (c : ℤ) :
    let T := stdMultiProjSegreJoinTwist K ι β c
    GeneratesOver (Int.castRingHom ℚ) (segreJoin T.y) T.segreDeg (fun _ : Fin 1 => (1 : ℚ)) ∧
    GeneratesOver (Int.castRingHom ℚ) T.y T.twistedDeg (fun _ : Fin 1 => (1 : ℚ)) := by
  intro T
  have hseg : GeneratesOver (Int.castRingHom ℚ) (segreJoin T.y) T.segreDeg
      (fun _ : Fin 1 => (1 : ℚ)) := by
    intro c₀ _
    refine ⟨fun _ => 1, fun _ => (chartRingOver _ _ _).one_mem, ?_⟩
    have hval : ∀ u : Unit ⊕ K, segreJoin T.y ⟨u, c₀ u⟩ = 1 := by
      rintro (u | k)
      · change ∏ k : K, (1 : ℚ) = 1
        simp
      · rfl
    simp [hval]
  exact ⟨hseg, T.generates_twisted _ hseg⟩

/-- **0-Assumption Complete `SmallSectionSegreBridge` Realization (`projSpaceSegreBridge`)**:
wires `projSpaceMoriwakiBigDatum d hd hα` directly into `stdMultiProjSegreJoinTwist` over `ℚ`,
proving that `generates_over_segre_join_twist` is genuinely satisfiable with zero assumptions! -/
def projSpaceSegreBridge (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (K : Type uK) [Fintype K] [DecidableEq K] (ι : K → Type uK) [∀ k, Nonempty (ι k)]
    (β : K → ℤ) (c : ℤ) :
    SmallSectionSegreBridge.{0} d ℤ ℚ (Int.castRingHom ℚ) K ι where
  datum := projSpaceMoriwakiBigDatum d hd hα
  twist := stdMultiProjSegreJoinTwist K ι β c
  evalSec _ _ := (1 : ℚ)
  threshold := 1
  threshold_ge_one := le_rfl
  genCard _ := 1
  genSec _ _ := 0
  genSec_small k hk _ := by
    change (projSpaceMoriwakiBigDatum d hd hα).supNorm k 0 < 1
    rw [(projSpaceMoriwakiBigDatum d hd hα).supNorm_zero hk]
    exact one_pos
  genSec_segre_mem k _ _ := by
    intro c₀ _
    have hval : ∀ u : Unit ⊕ K,
        segreJoin (stdMultiProjSegreJoinTwist K ι β c).y ⟨u, c₀ u⟩ = 1 := by
      rintro (u | k')
      · change ∏ _ : K, (1 : ℚ) = 1; simp
      · rfl
    simp [hval, (chartRingOver _ _ _).one_mem]
  genSec_segre_generates k _ := by
    have h := (stdMultiProj_generatesOver_segreJoin K ι (k • β) ((k : ℤ) * c)).1
    exact h

/-- **0-Assumption Verification of `generates_over_segre_join_twist`** on `projSpaceSegreBridge`. -/
theorem projSpaceSegreBridge_generates (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (K : Type uK) [Fintype K] [DecidableEq K] (ι : K → Type uK) [∀ k, Nonempty (ι k)]
    (β : K → ℤ) (c : ℤ) :
    let B := projSpaceSegreBridge d hd hα K ι β c
    B.datum.IsArithBig ∧
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, B.threshold ≤ K₀ ∧
      ∀ k : ℕ, K₀ ≤ k →
        (∀ j : Fin (B.genCard k), B.datum.supNorm k (B.genSec k j).1 < 1) ∧
        GeneratesOver (Int.castRingHom ℚ) B.twist.y
          (k • (B.twist.baseWeight + diagShift B.twist.twist))
          (fun j => B.evalSec k (B.genSec k j)) := by
  intro B
  have hbig : 0 < B.datum.selfInt := mul_pos hα (Nat.cast_pos.mpr (Nat.succ_pos d))
  obtain ⟨hAr, c₀, hc₀, K₀, hK₀, hgen⟩ := generates_over_segre_join_twist B hbig
  exact ⟨hAr, c₀, hc₀, K₀, hK₀, fun k hk => ⟨(hgen k hk).1, (hgen k hk).2.2.1⟩⟩

end ConcreteZeroAssumptionRealizations

/-! ## Section 7: Clean Wave 2 Bridges (`Stage14M4_AhSlimDeepStR`, `Stage14M4_CovolStepsBridge`) -/

section Wave2Bridges

/-! ### Bridge 1: Packaged Moriwaki Bigness Input for `Stage14M4_AhSlimDeepStR` -/

/-- **Packaged Moriwaki Bigness Output (`MoriwakiBigPkg d`)** ready for `Stage14M4_AhSlimDeepStR`:
bundles a `MoriwakiBigDatum d` with its proved Arakelov volume lower/upper bounds,
exponential small-section growth, and eventual nonzero strictly small section extraction. -/
structure MoriwakiBigPkg (d : ℕ) where
  datum : MoriwakiBigDatum.{u} d
  selfInt_pos : 0 < datum.selfInt
  volAr_ge_selfInt : datum.selfInt ≤ datum.volAr
  volArUpper_ge_selfInt : datum.selfInt ≤ datum.volArUpper
  isArithBig : datum.IsArithBig
  expRate : ℝ
  expRate_pos : 0 < expRate
  expThreshold : ℕ
  expThreshold_ge_one : 1 ≤ expThreshold
  exp_small_sections : ∀ k : ℕ, (hk : expThreshold ≤ k) →
    expRate * (k : ℝ) ^ (d + 1) ≤
      Real.log (datum.smallSectionsCard k (le_trans expThreshold_ge_one hk) : ℝ)
  nonzero_small_section : ∀ k : ℕ, expThreshold ≤ k →
    ∃ s : datum.secLat k, s ≠ 0 ∧ datum.supNorm k s.1 < 1

/-- Unconditional constructor of `MoriwakiBigPkg d` from any big `MoriwakiBigDatum d`
(`0 < M.selfInt`) via `moriwakiBig_outright`. -/
def moriBigPkgOfDatum {d : ℕ} (M : MoriwakiBigDatum.{u} d) (hbig : 0 < M.selfInt) :
    MoriwakiBigPkg.{u} d :=
  let hout := moriwakiBig_outright M
  let hexp := hout.2.2.2.1 hbig
  let c₀ := hexp.choose
  let hc₀ := hexp.choose_spec.1
  let hK := hexp.choose_spec.2
  let K₀ := hK.choose
  let hK₀ := hK.choose_spec.choose
  let hlog := hK.choose_spec.choose_spec
  { datum := M
    selfInt_pos := hbig
    volAr_ge_selfInt := hout.1
    volArUpper_ge_selfInt := hout.2.1
    isArithBig := hout.2.2.1 hbig
    expRate := c₀
    expRate_pos := hc₀
    expThreshold := K₀
    expThreshold_ge_one := hK₀
    exp_small_sections := hlog
    nonzero_small_section := fun k hk => by
      have hk1 : 1 ≤ k := le_trans hK₀ hk
      have hlt : 0 < Real.log (M.smallSectionsCard k hk1 : ℝ) :=
        lt_of_lt_of_le (mul_pos hc₀ (pow_pos (Nat.cast_pos.mpr hk1) (d + 1))) (hlog k hk)
      have hgt1 : 1 < M.smallSectionsCard k hk1 := by
        by_contra hle
        have hcard_le : (M.smallSectionsCard k hk1 : ℝ) ≤ 1 := by
          exact_mod_cast Nat.le_of_not_lt hle
        have hlog_le : Real.log (M.smallSectionsCard k hk1 : ℝ) ≤ 0 := by
          by_cases h0 : M.smallSectionsCard k hk1 = 0
          · simp [h0]
          · exact (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)) hcard_le).trans
              (by simp)
        linarith
      obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp hgt1
      by_cases hs10 : s₁ = 0
      · exact ⟨s₂, fun h => hne (hs10.trans h.symm),
          ((M.smallSections_finite hk1).mem_toFinset).mp hs₂⟩
      · exact ⟨s₁, hs10, ((M.smallSections_finite hk1).mem_toFinset).mp hs₁⟩ }

/-- **Line of Large Arithmetic Degree from Moriwaki Bigness (`line_of_large_degree_of_moriwaki`)**:
feeds `LineOfLargeDegreeOfUse` in `Stage14M4_AhSlimDeepStR`: for any big `M : MoriwakiBigDatum d`
(`0 < M.selfInt`) and ANY target threshold `B : ℝ`, there exists `k ≥ 1` such that:
1. `B ≤ arithDeg (M.secLat k)` (arbitrarily large arithmetic degree),
2. `B ≤ Real.log (M.smallSectionsCard k hk : ℝ)` (arbitrarily large small-section entropy),
3. There exists a nonzero strictly small global section `s ∈ M.secLat k` with `M.supNorm k s.1 < 1`. -/
theorem line_of_large_degree_of_moriwaki {d : ℕ} (M : MoriwakiBigDatum d)
    (hbig : 0 < M.selfInt) (B : ℝ) :
    ∃ k : ℕ, ∃ hk : 1 ≤ k,
      B ≤ arithDeg (M.secLat k) ∧
      B ≤ Real.log (M.smallSectionsCard k hk : ℝ) ∧
      ∃ s : M.secLat k, s ≠ 0 ∧ M.supNorm k s.1 < 1 := by
  let P := moriBigPkgOfDatum M hbig
  have hfac_pos : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hhalf_pos : 0 < M.selfInt / (2 * ((d + 1).factorial : ℝ)) := div_pos hbig (by positivity)
  have hAHS := M.ahs_liminf (M.selfInt / (2 * ((d + 1).factorial : ℝ))) hhalf_pos
  rw [Filter.eventually_atTop] at hAHS
  obtain ⟨K₁, hK₁⟩ := hAHS
  let rate : ℝ := min P.expRate (M.selfInt / (2 * ((d + 1).factorial : ℝ)))
  have hrate_pos : 0 < rate := lt_min P.expRate_pos hhalf_pos
  obtain ⟨K₂, hK₂⟩ := exists_nat_gt (max 0 B / rate)
  let k : ℕ := max (max P.expThreshold K₁) K₂
  have hkP : P.expThreshold ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk1 : 1 ≤ k := le_trans P.expThreshold_ge_one hkP
  have hkK₁ : K₁ ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
  have hkK₂ : K₂ ≤ k := le_max_right _ _
  have hk_le_pow : (k : ℝ) ≤ (k : ℝ) ^ (d + 1) := by
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (k : ℝ) ^ (d + 1) := pow_le_pow_right₀ hk1R (Nat.succ_pos d)
  have hB_le_rate : B ≤ rate * (k : ℝ) ^ (d + 1) := by
    have h1 : max 0 B / rate < (k : ℝ) := lt_of_lt_of_le hK₂ (by exact_mod_cast hkK₂)
    have h2 : max 0 B < rate * (k : ℝ) := by linarith [(div_lt_iff₀ hrate_pos).mp h1]
    have h3 : rate * (k : ℝ) ≤ rate * (k : ℝ) ^ (d + 1) :=
      mul_le_mul_of_nonneg_left hk_le_pow hrate_pos.le
    exact (le_max_right 0 B).trans (h2.le.trans h3)
  have hdeg_ge : B ≤ arithDeg (M.secLat k) := by
    have hspec := hK₁ k hkK₁
    have hkd1_pos : (0 : ℝ) < (k : ℝ) ^ (d + 1) := pow_pos (Nat.cast_pos.mpr hk1) (d + 1)
    have hsub : M.selfInt / ((d + 1).factorial : ℝ) - M.selfInt / (2 * ((d + 1).factorial : ℝ)) =
        M.selfInt / (2 * ((d + 1).factorial : ℝ)) := by
      field_simp [hfac_pos.ne']; ring
    rw [hsub] at hspec
    have hdeg1 : (M.selfInt / (2 * ((d + 1).factorial : ℝ))) * (k : ℝ) ^ (d + 1) ≤
        arithDeg (M.secLat k) := (le_div_iff₀ hkd1_pos).mp hspec
    have hmin_le : rate * (k : ℝ) ^ (d + 1) ≤
        (M.selfInt / (2 * ((d + 1).factorial : ℝ))) * (k : ℝ) ^ (d + 1) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hkd1_pos.le
    exact hB_le_rate.trans (hmin_le.trans hdeg1)
  have hlog_ge : B ≤ Real.log (M.smallSectionsCard k hk1 : ℝ) := by
    have hmin_le : rate * (k : ℝ) ^ (d + 1) ≤ P.expRate * (k : ℝ) ^ (d + 1) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg (Nat.cast_nonneg k) _)
    exact hB_le_rate.trans (hmin_le.trans (P.exp_small_sections k hkP))
  exact ⟨k, hk1, hdeg_ge, hlog_ge, P.nonzero_small_section k hkP⟩

/-- **`DeepStRMoriwakiInput d`**: unified input bundle for `Stage14M4_AhSlimDeepStR`, combining
`MoriwakiBigPkg`, `ShiftRankDatum` shift-volume ceiling, and `SmallSectionSegreBridge`. -/
structure DeepStRMoriwakiInput (d : ℕ) (S : Type uS) (Ω : Type uΩ) [CommRing S] [Field Ω]
    (φ : S →+* Ω) (K : Type uK) [Fintype K] [DecidableEq K] (ι : K → Type uK) where
  pkg : MoriwakiBigPkg.{u} d
  rankDatum : ShiftRankDatum.{u} d
  segreBridge : SmallSectionSegreBridge.{u} d S Ω φ K ι
  bridge_datum_eq : segreBridge.datum = pkg.datum

/-- Unconditional assembly of `DeepStRMoriwakiInput` conclusions for `Stage14M4_AhSlimDeepStR`. -/
theorem deepStR_moriwaki_summary {d : ℕ} {S : Type uS} {Ω : Type uΩ} [CommRing S] [Field Ω]
    {φ : S →+* Ω} {K : Type uK} [Fintype K] [DecidableEq K] {ι : K → Type uK}
    (I : DeepStRMoriwakiInput.{u} d S Ω φ K ι) (q : ℕ) (hq : 1 ≤ q) (B : ℝ) :
    I.pkg.datum.IsArithBig ∧
    arithVolUpper (I.rankDatum.smallCount q) d ≤
      2 * (I.rankDatum.sepConst + 1) * ((d : ℝ) + 1) * ((q : ℝ) + 1) * I.rankDatum.genDeg q ∧
    (∃ k : ℕ, ∃ hk : 1 ≤ k,
      B ≤ arithDeg (I.pkg.datum.secLat k) ∧
      B ≤ Real.log (I.pkg.datum.smallSectionsCard k hk : ℝ)) ∧
    (∃ K₀ : ℕ, I.segreBridge.threshold ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k →
      GeneratesOver φ I.segreBridge.twist.y
        (k • (I.segreBridge.twist.baseWeight + diagShift I.segreBridge.twist.twist))
        (fun j => I.segreBridge.evalSec k (I.segreBridge.genSec k j))) := by
  have hrank := (moriwaki_rank_bounds_generic I.rankDatum q hq).2.2.2
  have hline := line_of_large_degree_of_moriwaki I.pkg.datum I.pkg.selfInt_pos B
  have hbigB : 0 < I.segreBridge.datum.selfInt := by
    rw [I.bridge_datum_eq]
    exact I.pkg.selfInt_pos
  obtain ⟨_, _, _, K₀, hK₀, hgen⟩ := generates_over_segre_join_twist I.segreBridge hbigB
  refine ⟨I.pkg.isArithBig, hrank, ?_, ⟨K₀, hK₀, fun k hk => (hgen k hk).2.2.1⟩⟩
  obtain ⟨k, hk, h1, h2, _⟩ := hline
  exact ⟨k, hk, h1, h2⟩

/-! ### Bridge 2: Covolume-Steps & `L3` Bridge for `Stage14M4_CovolStepsBridge` -/

/-- **`CovolStepMoriwakiInput d m`**: packages an `m`-step family of target Hodge / automorphic
lattices `targetLat j ⊂ targetSpace j` receiving linearly independent pushforwards of strictly
small global sections from a `MoriwakiBigDatum d` via bounded chart maps `Ψ j`. -/
structure CovolStepMoriwakiInput (d m : ℕ) where
  datum : MoriwakiBigDatum.{u} d
  targetSpace : Fin m → Type u
  [targetNorm : ∀ j, NormedAddCommGroup (targetSpace j)]
  [targetInner : ∀ j, InnerProductSpace ℝ (targetSpace j)]
  [targetFD : ∀ j, FiniteDimensional ℝ (targetSpace j)]
  targetLat : ∀ j, Submodule ℤ (targetSpace j)
  [targetDisc : ∀ j, DiscreteTopology (targetLat j)]
  targetLat_ne_bot : ∀ j, targetLat j ≠ ⊥
  degStep : Fin m → ℕ
  degStep_ge_one : ∀ j, 1 ≤ degStep j
  chartMap : ∀ j, datum.secSpace (degStep j) → targetSpace j
  chartBound : Fin m → ℝ
  chartBound_pos : ∀ j, 0 < chartBound j
  chartMap_bound : ∀ j x, ‖chartMap j x‖ ≤ chartBound j * ‖x‖
  smallBasis : ∀ j, Fin (rk (targetLat j)) → datum.secLat (degStep j)
  smallBasis_small : ∀ j i, smallBasis j i ∈ datum.smallSectionsSet (degStep j)
  chartMap_mem : ∀ j i, chartMap j (smallBasis j i).1 ∈ targetLat j
  chartMap_li : ∀ j, LinearIndependent ℝ (fun i => chartMap j (smallBasis j i).1)

attribute [instance] CovolStepMoriwakiInput.targetNorm CovolStepMoriwakiInput.targetInner
  CovolStepMoriwakiInput.targetFD CovolStepMoriwakiInput.targetDisc

/-- **Direct Covolume-Steps & `Stage12` `L3` Bridge (`moriwaki_covol_steps_bridge`)**:
for any `CovolStepMoriwakiInput d m` and normalization `D > 0`, unconditionally proves:
1. Pointwise log-covolume upper bound:
   `Real.log (covol (C.targetLat j)) ≤ rk (C.targetLat j) * Real.log (C.chartBound j * C.datum.volConst)`,
2. Normalized `L3` step bound:
   `(2 / D) * Real.log (covol (C.targetLat j)) ≤ (2 * rk (C.targetLat j) / D) * Real.log (C.chartBound j * C.datum.volConst)`,
3. Pointwise Arakelov slope lower bound:
   `-Real.log (C.chartBound j * C.datum.volConst) ≤ slope (C.targetLat j)`,
4. Two-sided Minkowski covolume lower bound:
   `(unitBallVol (rk (C.targetLat j)) / 2^(rk (C.targetLat j))) * ∏ i, succMin (C.targetLat j) i ≤ covol (C.targetLat j)`,
5. Uniform `m`-step summed `L3` covolume ceiling feeding `Stage14M4_CovolStepsBridge` and
   `Stage12SchurWeylLattices.divLink_of_L3_and_dwork_chain`! -/
theorem moriwaki_covol_steps_bridge {d m : ℕ} (C : CovolStepMoriwakiInput d m)
    {D : ℝ} (hD : 0 < D) :
    (∀ j : Fin m,
      Real.log (covol (C.targetLat j)) ≤
        (rk (C.targetLat j) : ℝ) * Real.log (C.chartBound j * C.datum.volConst)) ∧
    (∀ j : Fin m,
      (2 / D) * Real.log (covol (C.targetLat j)) ≤
        (2 * (rk (C.targetLat j) : ℝ) / D) * Real.log (C.chartBound j * C.datum.volConst)) ∧
    (∀ j : Fin m,
      -Real.log (C.chartBound j * C.datum.volConst) ≤
        ArakelovCovolume.slope (C.targetLat j)) ∧
    (∀ j : Fin m,
      (unitBallVol (rk (C.targetLat j)) / (2 : ℝ) ^ (rk (C.targetLat j))) *
        (∏ i : Fin (rk (C.targetLat j)), succMin (C.targetLat j) i) ≤
        covol (C.targetLat j)) ∧
    (∑ j : Fin m, (2 / D) * Real.log (covol (C.targetLat j)) ≤
      ∑ j : Fin m,
        (2 * (rk (C.targetLat j) : ℝ) / D) * Real.log (C.chartBound j * C.datum.volConst)) := by
  have hL3 := L3_hodge_covolume_bound C.targetSpace C.targetLat C.targetLat_ne_bot
    (fun j i => C.chartMap j (C.smallBasis j i).1)
    C.chartMap_mem C.chartMap_li
    (fun j => C.chartBound j * C.datum.volConst)
    (fun j => mul_pos (C.chartBound_pos j) C.datum.volConst_pos)
    (fun j i => by
      have h1 := C.chartMap_bound j (C.smallBasis j i).1
      have h2 := C.datum.norm_le_vol_supNorm (C.degStep j) (C.degStep_ge_one j) (C.smallBasis j i).1
      have h3 : C.datum.supNorm (C.degStep j) (C.smallBasis j i).1 < 1 := C.smallBasis_small j i
      have h4 : ‖(C.smallBasis j i).1‖ ≤ C.datum.volConst := by nlinarith [C.datum.volConst_pos]
      exact h1.trans (mul_le_mul_of_nonneg_left h4 (C.chartBound_pos j).le))
    hD
  have hmink : ∀ j : Fin m,
      (unitBallVol (rk (C.targetLat j)) / (2 : ℝ) ^ (rk (C.targetLat j))) *
        (∏ i : Fin (rk (C.targetLat j)), succMin (C.targetLat j) i) ≤
        covol (C.targetLat j) := fun j =>
    (covolume_bound_of_section_norms (C.targetLat j) (C.targetLat_ne_bot j)
      (fun i => C.chartMap j (C.smallBasis j i).1)
      (C.chartMap_mem j) (C.chartMap_li j)).1.1
  exact ⟨hL3.1, hL3.2.1, hL3.2.2.1, hmink, hL3.2.2.2⟩

/-- Direct bridge into `Stage12SchurWeylLattices.L3_covolume_of_moriwaki_small_sections`
when `1 ≤ d`. -/
theorem moriwaki_stage12_L3_covolume_bridge {d m : ℕ} (hd : 1 ≤ d)
    (C : CovolStepMoriwakiInput d m) {D : ℝ} (hD : 0 < D) :
    (∀ j : Fin m,
      Real.log (covol (C.targetLat j)) ≤
        (rk (C.targetLat j) : ℝ) * Real.log (C.chartBound j * C.datum.volConst)) ∧
    (∑ j : Fin m, (2 / D) * Real.log (covol (C.targetLat j)) ≤
      ∑ j : Fin m,
        (2 * (rk (C.targetLat j) : ℝ) / D) * Real.log (C.chartBound j * C.datum.volConst)) :=
  L3_covolume_of_moriwaki_small_sections (C.datum.toGradedHermAlgebra hd)
    C.targetSpace C.targetLat C.targetLat_ne_bot
    C.degStep C.degStep_ge_one C.chartMap C.chartBound C.chartBound_pos C.chartMap_bound
    C.smallBasis C.smallBasis_small C.chartMap_mem C.chartMap_li hD

end Wave2Bridges

end RHDirect.Stage14M4_MoriwakiBignessCore

end
