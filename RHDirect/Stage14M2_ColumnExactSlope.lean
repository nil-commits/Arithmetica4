import RHDirect.Stage14Contracts
import RHDirect.Stage14M2_HLatNumberField
import RHDirect.Stage14M2_WeylHookBranching

/-!
# RHDirect.Stage14M2_ColumnExactSlope

Field-2 Package M2 (Wave 2): **Exact Column-Lattice Slope (`bc_mu_column_lattice`,
`q_lattice_slope_exact`, `column_lattice_exact_slope_nf`) and Unconditional `ConclusionF5`
(`lower_slope_inequality_family`) via Weyl Hook-Length Branching over CM Number Fields**.

Zero `sorry`, zero custom `axiom`s, zero `native_decide`, zero `opaque`.

## Main Deliverables (Aligned with `Stage14Contracts.M2HLatBostContract` / `HLatAnchor`)

1. **Section 1 — `HLatAnchor` Bridges, Determinant Twists & `q_lattice_slope_exact`**:
   - Canonical zero-drift adapters `concreteLatOfAnchor`, `anchorOfConcreteLat`, `anchorOfHLat`,
     `anchorOfCMHerm`, `anchorOfExtPow`, `anchorOfTensor`, `anchorOfDual`, `anchorOfScale`,
     `anchorOfColumnTensor`, `detTwistAnchor`, and `anchorOfDomWeight`.
   - Exact rational / Euclidean `ℤ`-lattice exterior-power and column-tensor slope identities
     (`q_lattice_slope_exact`, `q_lattice_slope_exact_domWeight`, `q_lattice_slope_exact_of_gram`,
     `q_lattice_slope_exact_sublattice`).
2. **Section 2 — Complex-to-Real Frame Determinant, Unit/Free `HLat K` Covolumes &
   `bc_mu_column_lattice`**:
   - Elementary block-conjugation proof of `det_realMatrixOfComplex`
     (`(realMatrixOfComplex M).det = Complex.normSq M.det`), `covol_mulVec_fullRank`, and
     exact frame-change covariance `covol_zRealize_frame_change` / `mu_zRealize_frame_change`
     for arbitrary good `HLat K` (arbitrary Steinitz class and place-dependent archimedean frames).
   - Self-duality proof of exact unit-lattice invariants (`unitHLat_mu_eq_zero`,
     `unitHLat_slope_eq`, `unitHLat_covol_eq`) and general free `HLat K` formulas
     (`freeHLat_covol_eq`, `freeHLat_slope_eq`, `freeHLat_mu_eq`).
   - **`bc_mu_column_lattice`**: exact column-lattice slope & base-change invariance for
     `SchurFunctorColumnLat` and `HLat K`.
3. **Section 3 — Number-Field Column-Lattice Exact Slope Identity (`column_lattice_exact_slope_nf`)**:
   - **`column_lattice_exact_slope_nf`**: exact number-field column-lattice rank, slope,
     normalized slope, and log-covolume identities incorporating the discriminant / different-ideal
     normalization via `Stage14M2_HLatNumberField.absNorm_differentIdeal_eq_discr`.
   - Extensions to ideal twists (`column_lattice_exact_slope_nf_twist`), sublattices
     (`column_lattice_exact_slope_nf_sublattice`), dual lattices
     (`column_lattice_exact_slope_nf_dual`), free lattices (`column_lattice_exact_slope_nf_free`),
     orthogonal direct sums (`column_lattice_exact_slope_nf_directSum`), and arbitrary integer
     dominant weights (`column_lattice_exact_slope_nf_domWeight`).
4. **Section 4 — Weyl Hook-Length Branching Lower Bound & `lower_slope_inequality_family`
   (`ConclusionF5`)**:
   - Stirling-sharpened and coarse number-field Schur-functor slope lower bounds
     (`schur_nf_slope_lower_stirling`, `schur_nf_slope_lower_coarse`,
     `schur_nf_mu_lower_stirling`).
   - Standard Fock / Weyl Gram duality bridge (`conclusionF5_of_standard_slope_lower`).
   - **`lower_slope_inequality_family`** (`ConclusionF5`): uniform unconditional lower bound on
     `muM` over CM number-field host families and `CMHermLattice` families, directly aligned with
     `Stage14Contracts.M2HLatBostContract.conclusionF5_column_slope_lower` and
     `Stage14Contracts.M2FiberCert.slopes` for M2 Wave 3 (`Stage14M2_SlopesMFAndBost`), plus a
     0-assumption concrete CM column-lattice family instantiation.
-/

noncomputable section

open Module Submodule Finset Real Matrix NumberField IsDedekindDomain
open scoped BigOperators Matrix ComplexOrder Pointwise

open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  linearIndependent_coe_basis det_gram_basis_pos covol_pos rk_pos_of_ne_bot
  gram_sum_smul_eq_transpose_mul)
open RHDirect.Stage4ArakelovBost (muMin muMin_le_slope_le_muMax dualLat
  discreteTopology_dualLat rk_dualLat covol_dualLat degAr_dualLat slope_dualLat
  discreteTopology_of_fin_basis_real_li)
open RHDirect.Stage11BostDworkSqueeze (latIndex covol_eq_index_mul_covol
  degAr_eq_degAr_sub_log_index)
open RHDirect.Stage11MoriwakiCovolume (arithDeg scaleLat scaleLat_invariants slope_scaleLat
  tensorLat tensorLat_invariants slope_tensor_eq_add slope_eq_arithDeg_div_rk)
open RHDirect.Stage12SchurWeylLattices (Partition ConcreteEuclideanLat CMHermLattice
  NumberFieldHLat extPowLat extPowLat_invariants slope_extPowLat
  iterTensorLat iterTensorLat_invariants columnTensorLat column_lattice_exact_slope
  muMin_sub_log_le_muMin_of_fullRank schur_branching_slope_lower
  mul_choose_pred_eq)
open RHDirect.Stage14Contracts (HLatAnchor M2HLatBostContract M2FiberCert Field2FiberShell)
open RHDirect.Stage14M2_HLatNumberField (HLat vecAt fcoord normAt majAt realizeHLat zRealize
  rkK logDiscDivDeg discShift degHLat slopeHLat muDef muMaxDef muMinDef lcvDef
  discreteTopology_zRealize_of_fg rk_zRealize_eq isZLattice_zRealize_of_good
  toNumberFieldHLat two_mul_card_infinitePlace zRealize_ne_bot zRealize_span_eq
  linearIndependent_realizeHLat_integralBasis realizeHLat_injective
  inner_realizeHLat_eq_sum_majAt vecAt_smul_basis twist_index muDef_sublattice_index
  dualLatO dualFrame dualFrame_frameOK dualHLat absNorm_differentIdeal_eq_discr
  hlat_duality_slope_neg directSumHLat directSumHLat_good directSumHLat_invariants)
open RHDirect.Stage14M2_WeylHookBranching (DomWeight SchurFunctorColumnLat
  hook_length_stirling_bound stirling_log_factorial_upper stirling_log_factorial_lower_all
  stdFockGram cNu HasColWeight standard_slope_lower standard_slope_lower_of_hook_bound)

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RHDirect.Stage14M2_ColumnExactSlope

/-! ## Section 1: Canonical `HLatAnchor` Bridges, Determinant Twists & `q_lattice_slope_exact` -/

section AnchorBridgesAndQLatticeSlope

/-- Convert a `Stage14Contracts.HLatAnchor` directly to `ConcreteEuclideanLat`. -/
def concreteLatOfAnchor (H : HLatAnchor) : ConcreteEuclideanLat where
  E := H.E
  L := H.L
  discL := H.disc
  ne_bot := H.ne_bot

/-- Convert a `ConcreteEuclideanLat` directly to `Stage14Contracts.HLatAnchor`. -/
def anchorOfConcreteLat (A : ConcreteEuclideanLat) : HLatAnchor where
  E := A.E
  L := A.L
  disc := A.discL
  ne_bot := A.ne_bot

@[simp] lemma concreteLatOfAnchor_rk (H : HLatAnchor) :
    rk (concreteLatOfAnchor H).L = H.rk := rfl

@[simp] lemma concreteLatOfAnchor_covol (H : HLatAnchor) :
    covol (concreteLatOfAnchor H).L = H.covol := rfl

@[simp] lemma concreteLatOfAnchor_degAr (H : HLatAnchor) :
    degAr (concreteLatOfAnchor H).L = H.degAr := rfl

@[simp] lemma concreteLatOfAnchor_slope (H : HLatAnchor) :
    ArakelovCovolume.slope (concreteLatOfAnchor H).L = H.slope := rfl

@[simp] lemma anchorOfConcreteLat_rk (A : ConcreteEuclideanLat) :
    (anchorOfConcreteLat A).rk = rk A.L := rfl

@[simp] lemma anchorOfConcreteLat_covol (A : ConcreteEuclideanLat) :
    (anchorOfConcreteLat A).covol = covol A.L := rfl

@[simp] lemma anchorOfConcreteLat_degAr (A : ConcreteEuclideanLat) :
    (anchorOfConcreteLat A).degAr = degAr A.L := rfl

@[simp] lemma anchorOfConcreteLat_slope (A : ConcreteEuclideanLat) :
    (anchorOfConcreteLat A).slope = ArakelovCovolume.slope A.L := rfl

@[simp] lemma anchorOfConcreteLat_muMax (A : ConcreteEuclideanLat) :
    (anchorOfConcreteLat A).muMax = muMax A.L := rfl

lemma anchor_rk_pos (H : HLatAnchor) : 0 < H.rk :=
  rk_pos_of_ne_bot H.L H.ne_bot

lemma anchor_covol_pos (H : HLatAnchor) : 0 < H.covol :=
  covol_pos H.L

lemma anchor_degAr_eq_neg_log_covol (H : HLatAnchor) :
    H.degAr = -Real.log H.covol := rfl

lemma anchor_slope_eq_neg_log_covol_div_rk (H : HLatAnchor) :
    H.slope = -Real.log H.covol / (H.rk : ℝ) := rfl

lemma anchor_log_covol_div_rk_eq_neg_slope (H : HLatAnchor) :
    Real.log H.covol / (H.rk : ℝ) = -H.slope := by
  rw [anchor_slope_eq_neg_log_covol_div_rk H, neg_div, neg_neg]

lemma anchor_neg_le_slope_iff_log_covol_div_rk_le (H : HLatAnchor) (B : ℝ) :
    -B ≤ H.slope ↔ Real.log H.covol / (H.rk : ℝ) ≤ B := by
  rw [anchor_log_covol_div_rk_eq_neg_slope H]
  constructor <;> intro h <;> linarith

/-- Canonical `HLatAnchor` attached to a good nonzero `Stage14M2_HLatNumberField.HLat K`. -/
def anchorOfHLat {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) : HLatAnchor where
  E := EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)
  L := A.zRealize
  disc := discreteTopology_zRealize_of_fg A.b A.X hG.1 A.L hG.2.1
  ne_bot := zRealize_ne_bot A.b A.X hG.1 hA0

/-- Canonical `ConcreteEuclideanLat` attached to a good nonzero `HLat K`. -/
def concreteLatOfHLat {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) : ConcreteEuclideanLat :=
  concreteLatOfAnchor (anchorOfHLat A hG hA0)

theorem anchorOfHLat_rk {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    (anchorOfHLat A hG hA0).rk = Module.finrank ℚ K * A.rank :=
  rk_zRealize_eq A.b A.X hG.1 A.L hG.2.1

theorem anchorOfHLat_rank_pos {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    0 < A.rank := by
  have h1 := anchor_rk_pos (anchorOfHLat A hG hA0)
  rw [anchorOfHLat_rk A hG hA0] at h1
  exact Nat.pos_of_mul_pos_left h1

theorem anchorOfHLat_slope_eq_slopeHLat {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    (anchorOfHLat A hG hA0).slope = slopeHLat A.b A.X A.L := rfl

theorem anchorOfHLat_mu_eq {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    A.mu = 2 * (anchorOfHLat A hG hA0).slope - Real.log 2 + logDiscDivDeg K := rfl

theorem anchorOfHLat_slope_eq_from_mu {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    (anchorOfHLat A hG hA0).slope = (A.mu + Real.log 2 - logDiscDivDeg K) / 2 := by
  have h := anchorOfHLat_mu_eq A hG hA0
  linarith

theorem anchorOfHLat_lcv_eq {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    A.lcv = (2 / (Module.finrank ℚ K : ℝ)) * Real.log (anchorOfHLat A hG hA0).covol := rfl

theorem anchorOfHLat_log_covol_div_rk_eq_lcv {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) :
    Real.log (anchorOfHLat A hG hA0).covol / ((anchorOfHLat A hG hA0).rk : ℝ) =
      A.lcv / (2 * (A.rank : ℝ)) := by
  rw [anchorOfHLat_rk A hG hA0, anchorOfHLat_lcv_eq A hG hA0]
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hr : (A.rank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (anchorOfHLat_rank_pos A hG hA0).ne'
  push_cast
  field_simp [hn, hr]

/-- Canonical `HLatAnchor` attached to a `CMHermLattice d r`. -/
def anchorOfCMHerm {d r : ℕ} (Λ : CMHermLattice d r) : HLatAnchor :=
  anchorOfConcreteLat (SchurFunctorColumnLat.concreteLatOfCMHerm Λ)

theorem anchorOfCMHerm_rk {d r : ℕ} (Λ : CMHermLattice d r) :
    (anchorOfCMHerm Λ).rk = 2 * r :=
  Λ.rk_euclLat

theorem anchorOfCMHerm_slope {d r : ℕ} (Λ : CMHermLattice d r) :
    (anchorOfCMHerm Λ).slope = -(1 / 4) * Real.log d - Real.log Λ.H.det.re / (2 * (r : ℝ)) :=
  Λ.slope_eq

/-- Exterior-power `HLatAnchor`: `⋀^k H` (`1 ≤ k ≤ H.rk`). -/
def anchorOfExtPow (H : HLatAnchor) {k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ H.rk) : HLatAnchor :=
  anchorOfConcreteLat ((concreteLatOfAnchor H).extPow hk1 hkr)

/-- Tensor-product `HLatAnchor`: `H₁ ⊗ H₂`. -/
def anchorOfTensor (H₁ H₂ : HLatAnchor) : HLatAnchor :=
  anchorOfConcreteLat ((concreteLatOfAnchor H₁).tensor (concreteLatOfAnchor H₂))

/-- Dual `HLatAnchor`: `H* = dualLat H.L`. -/
def anchorOfDual (H : HLatAnchor) : HLatAnchor where
  E := H.E
  L := dualLat H.L
  disc := discreteTopology_dualLat H.L
  ne_bot := by
    intro hbot
    have hrk := rk_dualLat H.L
    rw [hbot, show rk (⊥ : Submodule ℤ H.E) = 0 by simp [rk]] at hrk
    exact (anchor_rk_pos H).ne hrk

/-- Rescaled `HLatAnchor`: `c • H` for `c > 0`. -/
def anchorOfScale (H : HLatAnchor) {c : ℝ} (hc : 0 < c) : HLatAnchor where
  E := H.E
  L := scaleLat c H.L
  disc := (scaleLat_invariants H.L hc).1
  ne_bot := by
    intro hbot
    have hrk := (scaleLat_invariants H.L hc).2.1
    rw [hbot, show rk (⊥ : Submodule ℤ H.E) = 0 by simp [rk]] at hrk
    exact (anchor_rk_pos H).ne hrk

/-- Column-tensor `HLatAnchor`: `⨂_{j < lam_0} ⋀^{lam'_j} H`. -/
def anchorOfColumnTensor (H : HLatAnchor) (lam : Partition H.rk) : HLatAnchor :=
  anchorOfConcreteLat (columnTensorLat (concreteLatOfAnchor H) lam)

theorem anchorOfExtPow_invariants (H : HLatAnchor) {k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ H.rk) :
    (anchorOfExtPow H hk1 hkr).rk = Nat.choose H.rk k ∧
    (anchorOfExtPow H hk1 hkr).covol = H.covol ^ (Nat.choose (H.rk - 1) (k - 1)) ∧
    (anchorOfExtPow H hk1 hkr).degAr = (Nat.choose (H.rk - 1) (k - 1) : ℝ) * H.degAr ∧
    (anchorOfExtPow H hk1 hkr).slope = (k : ℝ) * H.slope := by
  obtain ⟨_, hrk, hcov, hdeg, hsl⟩ := extPowLat_invariants H.L hk1 hkr
  exact ⟨hrk, hcov, hdeg, hsl⟩

theorem anchorOfTensor_invariants (H₁ H₂ : HLatAnchor) :
    (anchorOfTensor H₁ H₂).rk = H₁.rk * H₂.rk ∧
    (anchorOfTensor H₁ H₂).covol = H₁.covol ^ H₂.rk * H₂.covol ^ H₁.rk ∧
    (anchorOfTensor H₁ H₂).degAr = (H₂.rk : ℝ) * H₁.degAr + (H₁.rk : ℝ) * H₂.degAr ∧
    (anchorOfTensor H₁ H₂).slope = H₁.slope + H₂.slope := by
  obtain ⟨_, hrk, hcov, hdeg⟩ := tensorLat_invariants H₁.L H₂.L
  exact ⟨hrk, hcov, hdeg, slope_tensor_eq_add H₁.L H₂.L H₁.ne_bot H₂.ne_bot⟩

theorem anchorOfDual_invariants (H : HLatAnchor) :
    (anchorOfDual H).rk = H.rk ∧
    (anchorOfDual H).covol = H.covol⁻¹ ∧
    (anchorOfDual H).degAr = -H.degAr ∧
    (anchorOfDual H).slope = -H.slope :=
  ⟨rk_dualLat H.L, covol_dualLat H.L, degAr_dualLat H.L, slope_dualLat H.L⟩

theorem anchorOfScale_invariants (H : HLatAnchor) {c : ℝ} (hc : 0 < c) :
    (anchorOfScale H hc).rk = H.rk ∧
    (anchorOfScale H hc).covol = c ^ H.rk * H.covol ∧
    (anchorOfScale H hc).degAr = H.degAr - (H.rk : ℝ) * Real.log c ∧
    (anchorOfScale H hc).slope = H.slope - Real.log c := by
  obtain ⟨_, hrk, hcov, hdeg⟩ := scaleLat_invariants H.L hc
  exact ⟨hrk, hcov, hdeg, slope_scaleLat H.L H.ne_bot hc⟩

/-- Concrete determinant line-lattice `det H = ⋀^{rk H} H` of rank `1`, covolume `H.covol`,
and slope `H.rk * H.slope = H.degAr`. -/
def detAnchor (H : HLatAnchor) : HLatAnchor :=
  anchorOfExtPow H (anchor_rk_pos H) le_rfl

theorem detAnchor_invariants (H : HLatAnchor) :
    (detAnchor H).rk = 1 ∧
    (detAnchor H).covol = H.covol ∧
    (detAnchor H).degAr = H.degAr ∧
    (detAnchor H).slope = (H.rk : ℝ) * H.slope := by
  obtain ⟨hrk, hcov, hdeg, hsl⟩ := anchorOfExtPow_invariants H (anchor_rk_pos H) le_rfl
  rw [Nat.choose_self] at hrk hcov hdeg
  rw [pow_one] at hcov
  rw [Nat.cast_one, one_mul] at hdeg
  exact ⟨hrk, hcov, hdeg, hsl⟩

/-- Concrete `n`-th tensor power of a `ConcreteEuclideanLat` (`iterTensorLat (List.replicate n A)`). -/
def tensorPowAnchor (H : HLatAnchor) (n : ℕ) : HLatAnchor :=
  anchorOfConcreteLat (iterTensorLat (List.replicate n (concreteLatOfAnchor H)))

theorem tensorPowAnchor_invariants (H : HLatAnchor) (n : ℕ) :
    (tensorPowAnchor H n).rk = H.rk ^ n ∧
    (tensorPowAnchor H n).slope = (n : ℝ) * H.slope := by
  obtain ⟨hrk, hsl⟩ := iterTensorLat_invariants (List.replicate n (concreteLatOfAnchor H))
  rw [List.map_replicate, List.prod_replicate] at hrk
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul] at hsl
  exact ⟨hrk, hsl⟩

/-- Concrete integer determinant-twist line-lattice `(det H)^{⊗ c}` for ANY `c : ℤ`
(positive, zero, or negative), built using `detAnchor`, `tensorPowAnchor`, and `anchorOfDual`. -/
def detTwistAnchor (H : HLatAnchor) (c : ℤ) : HLatAnchor :=
  if 0 ≤ c then
    tensorPowAnchor (detAnchor H) c.toNat
  else
    anchorOfDual (tensorPowAnchor (detAnchor H) (-c).toNat)

theorem detTwistAnchor_invariants (H : HLatAnchor) (c : ℤ) :
    (detTwistAnchor H c).rk = 1 ∧
    (detTwistAnchor H c).slope = (c : ℝ) * (H.rk : ℝ) * H.slope ∧
    (detTwistAnchor H c).covol = H.covol ^ c := by
  obtain ⟨hdet_rk, _, _, hdet_sl⟩ := detAnchor_invariants H
  have hcov_of_sl : ∀ (D : HLatAnchor), D.rk = 1 → D.slope = (c : ℝ) * (H.rk : ℝ) * H.slope →
      D.covol = H.covol ^ c := by
    intro D hDrk hDsl
    have hlog : Real.log D.covol = Real.log (H.covol ^ c) := by
      have h1 := anchor_log_covol_div_rk_eq_neg_slope D
      rw [hDrk, Nat.cast_one, div_one, hDsl] at h1
      have h2 := anchor_log_covol_div_rk_eq_neg_slope H
      have hrk_ne : (H.rk : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (anchor_rk_pos H).ne'
      have hHlog : Real.log H.covol = -(H.rk : ℝ) * H.slope := by
        have := (div_eq_iff hrk_ne).mp h2
        linarith
      rw [Real.log_zpow, hHlog]
      linarith
    exact Real.log_injOn_pos (anchor_covol_pos D) (zpow_pos (anchor_covol_pos H) c) hlog
  by_cases hc : 0 ≤ c
  · have hdef : detTwistAnchor H c = tensorPowAnchor (detAnchor H) c.toNat := if_pos hc
    rw [hdef]
    obtain ⟨hrk, hsl⟩ := tensorPowAnchor_invariants (detAnchor H) c.toNat
    rw [hdet_rk, one_pow] at hrk
    rw [hdet_sl] at hsl
    have hcast : ((c.toNat : ℕ) : ℝ) = (c : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hc
    rw [hcast, ← mul_assoc] at hsl
    exact ⟨hrk, hsl, hcov_of_sl _ hrk hsl⟩
  · have hdef : detTwistAnchor H c = anchorOfDual (tensorPowAnchor (detAnchor H) (-c).toNat) :=
      if_neg hc
    rw [hdef]
    obtain ⟨hrkD, _, _, hslD⟩ := anchorOfDual_invariants (tensorPowAnchor (detAnchor H) (-c).toNat)
    obtain ⟨hrk, hsl⟩ := tensorPowAnchor_invariants (detAnchor H) (-c).toNat
    rw [hdet_rk, one_pow] at hrk
    rw [hrk] at hrkD
    rw [hdet_sl] at hsl
    rw [hsl] at hslD
    have hneg : 0 ≤ -c := by omega
    have hcast : (((-c).toNat : ℕ) : ℝ) = -(c : ℝ) := by
      have h1 : (((-c).toNat : ℕ) : ℤ) = -c := Int.toNat_of_nonneg hneg
      exact_mod_cast h1
    rw [hcast] at hslD
    have hsl' : (anchorOfDual (tensorPowAnchor (detAnchor H) (-c).toNat)).slope =
        (c : ℝ) * (H.rk : ℝ) * H.slope := by linarith
    exact ⟨hrkD, hsl', hcov_of_sl _ hrkD hsl'⟩

/-- Full integer dominant-weight column-tensor lattice `anchorOfDomWeight H w`:
`(⨂_{j < w_0 - w_{r-1}} ⋀^{colLen j} H) ⊗ (det H)^{⊗ w_{r-1}}` for ANY `w : DomWeight H.rk`. -/
def anchorOfDomWeight (H : HLatAnchor) (w : DomWeight H.rk) : HLatAnchor :=
  anchorOfTensor (anchorOfColumnTensor H w.toPartition) (detTwistAnchor H w.detShift)

/-- **MAIN DELIVERABLE #1A — Exact Rational / `ℤ`-Lattice Column-Tensor Slope Formula
(`q_lattice_slope_exact`)**:
For ANY `H : HLatAnchor` and ANY partition `lam : Partition H.rk`:
1. `rk (anchorOfColumnTensor H lam) = ∏ j ∈ Finset.range lam.maxPart, Nat.choose H.rk (lam.colLen j)`,
2. **`slope (anchorOfColumnTensor H lam) = (lam.weight : ℝ) * H.slope`**,
3. `degAr (anchorOfColumnTensor H lam) = (lam.weight : ℝ) * ((anchorOfColumnTensor H lam).rk : ℝ) * H.slope`,
4. `Real.log (anchorOfColumnTensor H lam).covol / ((anchorOfColumnTensor H lam).rk : ℝ) = (lam.weight : ℝ) * (Real.log H.covol / (H.rk : ℝ))`. -/
theorem q_lattice_slope_exact (H : HLatAnchor) (lam : Partition H.rk) :
    (anchorOfColumnTensor H lam).rk =
      ∏ j ∈ Finset.range lam.maxPart, Nat.choose H.rk (lam.colLen j) ∧
    (anchorOfColumnTensor H lam).slope = (lam.weight : ℝ) * H.slope ∧
    (anchorOfColumnTensor H lam).degAr =
      (lam.weight : ℝ) * ((anchorOfColumnTensor H lam).rk : ℝ) * H.slope ∧
    Real.log (anchorOfColumnTensor H lam).covol / ((anchorOfColumnTensor H lam).rk : ℝ) =
      (lam.weight : ℝ) * (Real.log H.covol / (H.rk : ℝ)) := by
  obtain ⟨hrk, hsl⟩ := column_lattice_exact_slope (concreteLatOfAnchor H) lam
  have hrk' : (anchorOfColumnTensor H lam).rk =
      ∏ j ∈ Finset.range lam.maxPart, Nat.choose H.rk (lam.colLen j) := hrk
  have hsl' : (anchorOfColumnTensor H lam).slope = (lam.weight : ℝ) * H.slope := hsl
  have hrk_pos : (0 : ℝ) < ((anchorOfColumnTensor H lam).rk : ℝ) :=
    Nat.cast_pos.mpr (anchor_rk_pos (anchorOfColumnTensor H lam))
  have hdeg : (anchorOfColumnTensor H lam).degAr =
      (lam.weight : ℝ) * ((anchorOfColumnTensor H lam).rk : ℝ) * H.slope := by
    have h1 : (anchorOfColumnTensor H lam).slope =
        (anchorOfColumnTensor H lam).degAr / ((anchorOfColumnTensor H lam).rk : ℝ) := rfl
    rw [hsl'] at h1
    have h2 := (eq_div_iff hrk_pos.ne').mp h1
    linarith
  have hlog : Real.log (anchorOfColumnTensor H lam).covol / ((anchorOfColumnTensor H lam).rk : ℝ) =
      (lam.weight : ℝ) * (Real.log H.covol / (H.rk : ℝ)) := by
    rw [anchor_log_covol_div_rk_eq_neg_slope (anchorOfColumnTensor H lam), hsl',
      anchor_log_covol_div_rk_eq_neg_slope H]
    ring
  exact ⟨hrk', hsl', hdeg, hlog⟩

/-- Exact dominant-weight (`DomWeight H.rk`) column-tensor slope formula valid for ALL
integer dominant weights `w` (including negative entries via `detTwistAnchor`):
`slope (anchorOfDomWeight H w) = (∑ i : Fin H.rk, (w.w i : ℝ)) * H.slope`. -/
theorem q_lattice_slope_exact_domWeight (H : HLatAnchor) (w : DomWeight H.rk) :
    (anchorOfDomWeight H w).rk =
      ∏ j ∈ Finset.range w.toPartition.maxPart, Nat.choose H.rk (w.toPartition.colLen j) ∧
    (anchorOfDomWeight H w).slope = (∑ i : Fin H.rk, (w.w i : ℝ)) * H.slope := by
  obtain ⟨hrkT, _, _, hslT⟩ := anchorOfTensor_invariants
    (anchorOfColumnTensor H w.toPartition) (detTwistAnchor H w.detShift)
  obtain ⟨hrkC, hslC, _, _⟩ := q_lattice_slope_exact H w.toPartition
  obtain ⟨hrkD, hslD, _⟩ := detTwistAnchor_invariants H w.detShift
  refine ⟨by rw [anchorOfDomWeight, hrkT, hrkC, hrkD, mul_one], ?_⟩
  rw [anchorOfDomWeight, hslT, hslC, hslD]
  have hsum : (w.toPartition.weight : ℝ) + (w.detShift : ℝ) * (H.rk : ℝ) =
      ∑ i : Fin H.rk, (w.w i : ℝ) := by
    unfold Partition.weight DomWeight.toPartition
    simp only [Nat.cast_sum]
    have hcard : (w.detShift : ℝ) * (H.rk : ℝ) = ∑ _i : Fin H.rk, (w.detShift : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    rw [hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((w.natW i : ℕ) : ℝ) = (w.w i : ℝ) - (w.detShift : ℝ) := by
      exact_mod_cast w.natW_cast i
    linarith
  rw [← add_mul, hsum]

/-- Exact Gram-matrix rational column-lattice slope formula:
for any `ℤ`-basis `b` of `H.L` (`r = H.rk`),
`slope (anchorOfColumnTensor H lam) = -(lam.weight : ℝ) * log (det (gram b)) / (2 * r)`. -/
theorem q_lattice_slope_exact_of_gram (H : HLatAnchor) (lam : Partition H.rk)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ H.L) :
    (anchorOfColumnTensor H lam).slope =
      -(lam.weight : ℝ) *
        Real.log (Matrix.gram ℝ (fun i => (b i : H.E))).det / (2 * (H.rk : ℝ)) := by
  rw [(q_lattice_slope_exact H lam).2.1, anchor_slope_eq_neg_log_covol_div_rk H]
  change (lam.weight : ℝ) * (-Real.log (covol H.L) / (H.rk : ℝ)) = _
  rw [covol_eq_sqrt_det_gram H.L b, Real.log_sqrt (det_gram_basis_pos H.L b).le]
  ring

/-- Exact sublattice-index shift for rational column-tensor lattices:
if `H'.L ≤ H.L` inside the same ambient space `H.E` with `H'.rk = H.rk`, then
`slope (anchorOfColumnTensor H' lam) = (lam.weight : ℝ) * (H.slope - log [H : H'] / H.rk)`. -/
theorem q_lattice_slope_exact_sublattice {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {L' L : Submodule ℤ E} [DiscreteTopology L] [DiscreteTopology L']
    (hL0 : L ≠ ⊥) (hL'0 : L' ≠ ⊥) (hle : L' ≤ L) (hrk : rk L' = rk L)
    (lam : Partition (rk L')) :
    let H : HLatAnchor := ⟨E, L, hL0⟩
    let H' : HLatAnchor := ⟨E, L', hL'0⟩
    (anchorOfColumnTensor H' lam).slope =
      (lam.weight : ℝ) * (H.slope - Real.log (latIndex L L' : ℝ) / (H.rk : ℝ)) := by
  intro H H'
  rw [(q_lattice_slope_exact H' lam).2.1]
  have hdeg := degAr_eq_degAr_sub_log_index hle hrk
  have hsl' : H'.slope = H.slope - Real.log (latIndex L L' : ℝ) / (H.rk : ℝ) := by
    change degAr L' / (rk L' : ℝ) = degAr L / (rk L : ℝ) - Real.log (latIndex L L' : ℝ) / (rk L : ℝ)
    rw [hrk, hdeg, sub_div]
  rw [hsl']
  rfl

end AnchorBridgesAndQLatticeSlope

/-! ## Section 2: Complex-to-Real Frame Determinant, Unit/Free `HLat K` Covolumes &
`bc_mu_column_lattice` -/

section ComplexRealDetAndBaseChange

/-! ### Elementary Complex-to-Real Matrix Determinant (`(realMatrixOfComplex M).det = normSq M.det`) -/

/-- Canonical real `(ι × Fin 2) × (ι × Fin 2)` matrix representing left multiplication by
`M : Matrix ι ι ℂ` on `ℂ^ι ≅ ℝ^{ι × Fin 2}` (real part at `0`, imaginary part at `1`). -/
def realMatrixOfComplex {ι : Type*} (M : Matrix ι ι ℂ) :
    Matrix (ι × Fin 2) (ι × Fin 2) ℝ :=
  Matrix.of fun p q =>
    if p.2 = 0 then
      if q.2 = 0 then (M p.1 q.1).re else -(M p.1 q.1).im
    else
      if q.2 = 0 then (M p.1 q.1).im else (M p.1 q.1).re

/-- Equivalence `ι × Fin 2 ≃ ι ⊕ ι` splitting real coordinates (`0 ↦ inl`) and imaginary
coordinates (`1 ↦ inr`). -/
def prodFin2EquivSum (ι : Type*) : (ι × Fin 2) ≃ (ι ⊕ ι) where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun s := match s with | Sum.inl i => (i, 0) | Sum.inr i => (i, 1)
  left_inv p := by
    rcases p with ⟨i, r⟩
    fin_cases r <;> rfl
  right_inv s := by
    cases s <;> rfl

/-- **Exact Complex-to-Real Determinant Theorem (`det_realMatrixOfComplex`)**:
for ANY `M : Matrix ι ι ℂ` over any finite index type `ι`,
`(realMatrixOfComplex M).det = Complex.normSq M.det` (`= ‖M.det‖ ^ 2`). -/
theorem det_realMatrixOfComplex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    (realMatrixOfComplex M).det = Complex.normSq M.det := by
  let e := prodFin2EquivSum ι
  let A : Matrix ι ι ℝ := M.map Complex.re
  let B : Matrix ι ι ℝ := M.map Complex.im
  have hreidx : (realMatrixOfComplex M).submatrix e.symm e.symm =
      Matrix.fromBlocks A (-B) B A := by
    ext s t
    cases s with
    | inl i =>
      cases t with
      | inl j => simp [realMatrixOfComplex, e, prodFin2EquivSum, A]
      | inr j => simp [realMatrixOfComplex, e, prodFin2EquivSum, B]
    | inr i =>
      cases t with
      | inl j => simp [realMatrixOfComplex, e, prodFin2EquivSum, B]
      | inr j => simp [realMatrixOfComplex, e, prodFin2EquivSum, A]
  have hdet_eq : (realMatrixOfComplex M).det = (Matrix.fromBlocks A (-B) B A).det := by
    rw [← hreidx, Matrix.det_submatrix_equiv_self e.symm (realMatrixOfComplex M)]
  -- Lift to `ℂ` and diagonalize via `Q' * R * Q = fromBlocks M 0 0 M̄`.
  let Ac : Matrix ι ι ℂ := A.map Complex.ofReal
  let Bc : Matrix ι ι ℂ := B.map Complex.ofReal
  let Mc : Matrix ι ι ℂ := M.map (starRingEnd ℂ)
  have hM_eq : Ac + Complex.I • Bc = M := by
    ext i j
    simp only [Ac, Bc, A, B, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [mul_comm, Complex.re_add_im]
  have hMc_eq : Ac - Complex.I • Bc = Mc := by
    ext i j
    simp only [Ac, Bc, Mc, A, B, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    apply Complex.ext <;> simp
  let R : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := Matrix.fromBlocks Ac (-Bc) Bc Ac
  have hR_map : (Complex.ofRealHom.mapMatrix (Matrix.fromBlocks A (-B) B A)) = R := by
    ext s t
    cases s <;> cases t <;> simp [R, Ac, Bc, A, B]
  let Q : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    Matrix.fromBlocks (1 : Matrix ι ι ℂ) 1 (-Complex.I • (1 : Matrix ι ι ℂ)) (Complex.I • 1)
  let Q' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
    Matrix.fromBlocks ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) ((Complex.I / 2 : ℂ) • 1)
      ((1 / 2 : ℂ) • 1) (-(Complex.I / 2 : ℂ) • 1)
  have hQ'Q : Q' * Q = 1 := by
    dsimp only [Q', Q]
    rw [Matrix.fromBlocks_multiply]
    have h11 : ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * 1 +
        ((Complex.I / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * (-Complex.I • (1 : Matrix ι ι ℂ)) = 1 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.mul_one, Matrix.mul_smul,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases h : i = j
      · subst h; simp; ring_nf; rw [Complex.I_sq]; norm_num
      · simp [h]
    have h12 : ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * 1 +
        ((Complex.I / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * (Complex.I • (1 : Matrix ι ι ℂ)) = 0 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.mul_one, Matrix.mul_smul,
        Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, smul_eq_mul]
      by_cases h : i = j
      · subst h; simp; ring_nf; rw [Complex.I_sq]; norm_num
      · simp [h]
    have h21 : ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * 1 +
        (-(Complex.I / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * (-Complex.I • (1 : Matrix ι ι ℂ)) = 0 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.mul_one, Matrix.mul_smul,
        Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, smul_eq_mul]
      by_cases h : i = j
      · subst h; simp; ring_nf; rw [Complex.I_sq]; norm_num
      · simp [h]
    have h22 : ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * 1 +
        (-(Complex.I / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * (Complex.I • (1 : Matrix ι ι ℂ)) = 1 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.mul_one, Matrix.mul_smul,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases h : i = j
      · subst h; simp; ring_nf; rw [Complex.I_sq]; norm_num
      · simp [h]
    rw [h11, h12, h21, h22, Matrix.fromBlocks_one]
  have hRQ : R * Q = Matrix.fromBlocks M Mc (-Complex.I • M) (Complex.I • Mc) := by
    dsimp only [R, Q]
    rw [Matrix.fromBlocks_multiply]
    have h11 : Ac * 1 + -Bc * (-Complex.I • 1) = M := by
      rw [Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, ← hM_eq]
      ext i j; simp
    have h12 : Ac * 1 + -Bc * (Complex.I • 1) = Mc := by
      rw [Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, ← hMc_eq]
      ext i j; simp [sub_eq_add_neg]
    have h21 : Bc * 1 + Ac * (-Complex.I • 1) = -Complex.I • M := by
      rw [Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, ← hM_eq]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring_nf; rw [Complex.I_sq]; ring
    have h22 : Bc * 1 + Ac * (Complex.I • 1) = Complex.I • Mc := by
      rw [Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, ← hMc_eq]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring_nf; rw [Complex.I_sq]; ring
    rw [h11, h12, h21, h22]
  have hQ'RQ : Q' * R * Q = Matrix.fromBlocks M 0 0 Mc := by
    rw [Matrix.mul_assoc, hRQ]
    dsimp only [Q']
    rw [Matrix.fromBlocks_multiply]
    have h11 : ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * M +
        ((Complex.I / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * (-Complex.I • M) = M := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.smul_apply, smul_eq_mul]
      ring_nf; rw [Complex.I_sq]; ring
    have h12 : ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * Mc +
        ((Complex.I / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * (Complex.I • Mc) = 0 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul]
      ring_nf; rw [Complex.I_sq]; ring
    have h21 : ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * M +
        (-(Complex.I / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * (-Complex.I • M) = 0 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul]
      ring_nf; rw [Complex.I_sq]; ring
    have h22 : ((1 / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * Mc +
        (-(Complex.I / 2 : ℂ) • (1 : Matrix ι ι ℂ)) * (Complex.I • Mc) = Mc := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.smul_apply, smul_eq_mul]
      ring_nf; rw [Complex.I_sq]; ring
    rw [h11, h12, h21, h22]
  have hdetC : R.det = M.det * starRingEnd ℂ M.det := by
    have h1 := congrArg Matrix.det hQ'RQ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁] at h1
    have h2 := congrArg Matrix.det hQ'Q
    rw [Matrix.det_mul, Matrix.det_one] at h2
    have hMc_det : Mc.det = starRingEnd ℂ M.det := by
      simpa [Mc] using (RingHom.map_det (starRingEnd ℂ) M).symm
    rw [hMc_det] at h1
    calc R.det = (Q'.det * Q.det) * R.det := by rw [h2, one_mul]
      _ = Q'.det * R.det * Q.det := by ring
      _ = M.det * starRingEnd ℂ M.det := h1
  have hcast : (((Matrix.fromBlocks A (-B) B A).det : ℝ) : ℂ) = (Complex.normSq M.det : ℂ) := by
    have hmap : (((Matrix.fromBlocks A (-B) B A).det : ℝ) : ℂ) = R.det := by
      rw [← hR_map]
      exact RingHom.map_det Complex.ofRealHom _
    rw [hmap, hdetC, Complex.mul_conj]
  rw [hdet_eq]
  exact Complex.ofReal_injective hcast

/-- Determinant of a block-diagonal matrix indexed by `α × β`:
`det (blockDiag M) = ∏ a : α, (M a).det`. -/
def blockDiagMat {α β : Type*} [DecidableEq α] (M : α → Matrix β β ℝ) :
    Matrix (α × β) (α × β) ℝ :=
  Matrix.of fun p q => if p.1 = q.1 then M p.1 p.2 q.2 else 0

private lemma det_blockDiagMat_fin {β : Type*} [Fintype β] [DecidableEq β] :
    ∀ (n : ℕ) (M : Fin n → Matrix β β ℝ),
      (blockDiagMat M).det = ∏ i : Fin n, (M i).det := by
  intro n
  induction n with
  | zero =>
    intro M
    simp [Matrix.det_isEmpty]
  | succ m ih =>
    intro M
    let e : (Fin (m + 1) × β) ≃ ((Fin m × β) ⊕ β) :=
      { toFun := fun p => if h : p.1.1 < m then Sum.inl (⟨p.1.1, h⟩, p.2) else Sum.inr p.2
        invFun := fun s => match s with
          | Sum.inl q => (q.1.castSucc, q.2)
          | Sum.inr b => (Fin.last m, b)
        left_inv := fun p => by
          rcases p with ⟨i, b⟩
          by_cases h : i.1 < m
          · simp [h]
          · have hi : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; have := i.2; omega)
            simp [hi]
        right_inv := fun s => by
          cases s with
          | inl q => simp [q.1.2]
          | inr b => simp }
    have hsub : (blockDiagMat M).submatrix e.symm e.symm =
        Matrix.fromBlocks (blockDiagMat (fun i : Fin m => M i.castSucc)) 0 0 (M (Fin.last m)) := by
      ext s t
      cases s with
      | inl p =>
        cases t with
        | inl q =>
          simp only [Matrix.submatrix_apply, blockDiagMat, Matrix.of_apply,
            Matrix.fromBlocks_apply₁₁, e, Equiv.coe_fn_symm_mk, Fin.castSucc_inj]
        | inr b =>
          simp only [Matrix.submatrix_apply, blockDiagMat, Matrix.of_apply,
            Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, e, Equiv.coe_fn_symm_mk]
          exact if_neg (Fin.castSucc_ne_last p.1)
      | inr a =>
        cases t with
        | inl q =>
          simp only [Matrix.submatrix_apply, blockDiagMat, Matrix.of_apply,
            Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, e, Equiv.coe_fn_symm_mk]
          exact if_neg (Fin.castSucc_ne_last q.1).symm
        | inr b =>
          simp only [Matrix.submatrix_apply, blockDiagMat, Matrix.of_apply,
            Matrix.fromBlocks_apply₂₂, e, Equiv.coe_fn_symm_mk, ↓reduceIte]
    rw [← Matrix.det_submatrix_equiv_self e.symm (blockDiagMat M), hsub,
      Matrix.det_fromBlocks_zero₂₁, ih, Fin.prod_univ_castSucc]

theorem det_blockDiagMat {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : α → Matrix β β ℝ) :
    (blockDiagMat M).det = ∏ a : α, (M a).det := by
  let e := Fintype.equivFin α
  let eP : (Fin (Fintype.card α) × β) ≃ (α × β) := Equiv.prodCongr e.symm (Equiv.refl β)
  have hsub : (blockDiagMat M).submatrix eP eP = blockDiagMat (fun i => M (e.symm i)) := by
    ext ⟨i, b⟩ ⟨j, c⟩
    simp only [Matrix.submatrix_apply, blockDiagMat, Matrix.of_apply, eP, Equiv.prodCongr_apply,
      Equiv.refl_apply, Prod.map_apply]
    simp [e.symm.injective.eq_iff]
  rw [← Matrix.det_submatrix_equiv_self eP (blockDiagMat M), hsub,
    det_blockDiagMat_fin (Fintype.card α) (fun i => M (e.symm i))]
  exact Fintype.prod_equiv e.symm (fun i => (M (e.symm i)).det) (fun a => (M a).det) fun _ => rfl

/-- Exact covolume scaling under any invertible real linear map `M.mulVec` on `EuclideanSpace ℝ α`
applied to a full-rank `ℤ`-lattice `Λ` (`rk Λ = Fintype.card α`):
`covol (Λ.map T_M) = |M.det| * covol Λ`. -/
theorem covol_mulVec_fullRank {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℝ) (hM : IsUnit M.det)
    (Λ : Submodule ℤ (EuclideanSpace ℝ α)) [DiscreteTopology Λ]
    (hfull : rk Λ = Fintype.card α) :
    let T : EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ α :=
      { toFun := fun w => WithLp.toLp 2 (M.mulVec w.ofLp)
        map_add' := fun u v => by ext a; simp [Matrix.mulVec_add]
        map_smul' := fun c u => by ext a; simp [Matrix.mulVec_smul] }
    DiscreteTopology (Λ.map (T.restrictScalars ℤ)) ∧
    rk (Λ.map (T.restrictScalars ℤ)) = rk Λ ∧
    covol (Λ.map (T.restrictScalars ℤ)) = |M.det| * covol Λ := by
  classical
  intro T
  have hT_inv : ∃ T' : EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ α,
      (∀ w, T' (T w) = w) ∧ (∀ w, T (T' w) = w) := by
    refine ⟨{ toFun := fun w => WithLp.toLp 2 (M⁻¹.mulVec w.ofLp)
              map_add' := fun u v => by ext a; simp [Matrix.mulVec_add]
              map_smul' := fun c u => by ext a; simp [Matrix.mulVec_smul] }, fun w => ?_, fun w => ?_⟩
    · ext a
      change (M⁻¹.mulVec (M.mulVec w.ofLp)) a = w.ofLp a
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
    · ext a
      change (M.mulVec (M⁻¹.mulVec w.ofLp)) a = w.ofLp a
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  obtain ⟨T', hT'T, hTT'⟩ := hT_inv
  have hT_inj : Function.Injective T := fun u v h => by rw [← hT'T u, ← hT'T v, h]
  let eZ : Λ ≃ₗ[ℤ] Λ.map (T.restrictScalars ℤ) :=
    { toFun := fun x => ⟨T x.1, x.1, x.2, rfl⟩
      invFun := fun y => ⟨T' y.1, by
        rcases y.2 with ⟨x, hx, hxy⟩
        have hx' : T' y.1 = x := by rw [← hxy]; exact hT'T x
        rwa [hx']⟩
      map_add' := fun x y => Subtype.ext (map_add T x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul T c x.1)
      left_inv := fun x => Subtype.ext (hT'T x.1)
      right_inv := fun y => Subtype.ext (hTT' y.1) }
  have hDisc : DiscreteTopology (Λ.map (T.restrictScalars ℤ)) := by
    refine DiscreteTopology.of_continuous_injective (f := eZ.symm) ?_ eZ.symm.injective
    exact Continuous.subtype_mk (T'.continuous_of_finiteDimensional.comp continuous_subtype_val) _
  have hrk_eq : rk (Λ.map (T.restrictScalars ℤ)) = rk Λ := eZ.symm.finrank_eq
  refine ⟨hDisc, hrk_eq, ?_⟩
  let b : Module.Basis (Fin (rk Λ)) ℤ Λ :=
    (Module.Free.chooseBasis ℤ Λ).reindex
      (Fintype.equivOfCardEq (by
        rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ Λ), Fintype.card_fin]; rfl))
  let bT : Module.Basis (Fin (rk Λ)) ℤ (Λ.map (T.restrictScalars ℤ)) := b.map eZ
  let eα : α ≃ Fin (rk Λ) := (Fintype.equivFin α).trans (finCongr hfull.symm)
  let B : Matrix (Fin (rk Λ)) (Fin (rk Λ)) ℝ :=
    Matrix.of fun i j => (b j : EuclideanSpace ℝ α) (eα.symm i)
  let M' : Matrix (Fin (rk Λ)) (Fin (rk Λ)) ℝ := M.submatrix eα.symm eα.symm
  have hM'_det : M'.det = M.det := Matrix.det_submatrix_equiv_self eα.symm M
  have hgram_b : Matrix.gram ℝ (fun j => (b j : EuclideanSpace ℝ α)) = Bᵀ * B := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    rw [← Fintype.sum_equiv eα.symm
      (fun k => (b j : EuclideanSpace ℝ α) (eα.symm k) * (b i : EuclideanSpace ℝ α) (eα.symm k))
      (fun a => (b j : EuclideanSpace ℝ α) a * (b i : EuclideanSpace ℝ α) a)
      (fun _ => rfl)]
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hMB_apply : ∀ i j, (M' * B) i j = (bT j : EuclideanSpace ℝ α) (eα.symm i) := by
    intro i j
    change (∑ k : Fin (rk Λ), M (eα.symm i) (eα.symm k) * (b j : EuclideanSpace ℝ α) (eα.symm k)) =
      (M.mulVec (b j : EuclideanSpace ℝ α).ofLp) (eα.symm i)
    unfold Matrix.mulVec dotProduct
    exact Fintype.sum_equiv eα.symm
      (fun k => M (eα.symm i) (eα.symm k) * (b j : EuclideanSpace ℝ α) (eα.symm k))
      (fun a => M (eα.symm i) a * (b j : EuclideanSpace ℝ α) a)
      (fun _ => rfl)
  have hgram_bT : Matrix.gram ℝ (fun j => (bT j : EuclideanSpace ℝ α)) = (M' * B)ᵀ * (M' * B) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    simp only [Matrix.transpose_apply, star_trivial]
    rw [← Fintype.sum_equiv eα.symm
      (fun k => (bT j : EuclideanSpace ℝ α) (eα.symm k) * (bT i : EuclideanSpace ℝ α) (eα.symm k))
      (fun a => (bT j : EuclideanSpace ℝ α) a * (bT i : EuclideanSpace ℝ α) a)
      (fun _ => rfl)]
    refine Finset.sum_congr rfl fun k _ => by rw [hMB_apply k i, hMB_apply k j, mul_comm]
  rw [covol_eq_sqrt_det_gram (Λ.map (T.restrictScalars ℤ)) bT, covol_eq_sqrt_det_gram Λ b,
    hgram_bT, hgram_b, Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, hM'_det]
  have hrew : M.det * B.det * (M.det * B.det) = M.det ^ 2 * (B.det * B.det) := by ring
  rw [hrew, Real.sqrt_mul (sq_nonneg M.det), Real.sqrt_sq_eq_abs]

/-! ### Exact Frame-Change Covariance for Arbitrary Good `HLat K` -/

/-- Exact archimedean frame-change formula for ANY finitely generated full-rank `𝓞 K`-lattice `L`
over a totally complex number field `K`:
`covol (zRealize b X L) = (∏ v, (Complex.normSq (X v).det)⁻¹) * covol (zRealize b 1 L)`. -/
theorem covol_zRealize_eq_prod_det_mul_unitFrame {K V ι : Type*} [Field K] [NumberField K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V)
    (hL : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) :
    covol (zRealize b X L) =
      (∏ v : InfinitePlace K, (Complex.normSq (X v).det)⁻¹) *
        covol (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L) := by
  classical
  have h1X : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix ι ι ℂ)).det := fun _ => by simp
  haveI : DiscreteTopology (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L) :=
    discreteTopology_zRealize_of_fg b (fun _ => 1) h1X L hL
  haveI : DiscreteTopology (zRealize b X L) :=
    discreteTopology_zRealize_of_fg b X hX L hL
  let M : Matrix (InfinitePlace K × ι × Fin 2) (InfinitePlace K × ι × Fin 2) ℝ :=
    blockDiagMat (fun v => realMatrixOfComplex (X v)⁻¹)
  have hM_det : M.det = ∏ v : InfinitePlace K, (Complex.normSq (X v).det)⁻¹ := by
    rw [det_blockDiagMat]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [det_realMatrixOfComplex, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀]
  have hM_det_pos : 0 < M.det := by
    rw [hM_det]
    refine Finset.prod_pos fun v _ => inv_pos.mpr (Complex.normSq_pos.mpr (hX v).ne_zero)
  have hM_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM_det_pos.ne'
  have hfull : rk (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L) =
      Fintype.card (InfinitePlace K × ι × Fin 2) := by
    rw [rk_zRealize_eq b (fun _ => 1) h1X L hL]
    unfold rkK
    rw [hsp, finrank_top, Module.finrank_eq_card_basis b,
      Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    have h2 := two_mul_card_infinitePlace (K := K)
    nlinarith
  let T : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
    { toFun := fun w => WithLp.toLp 2 (M.mulVec w.ofLp)
      map_add' := fun u v => by ext a; simp [Matrix.mulVec_add]
      map_smul' := fun c u => by ext a; simp [Matrix.mulVec_smul] }
  have hT_real : ∀ x : V, T (realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) x) = realizeHLat b X x := by
    intro x
    ext ⟨v, i, r⟩
    have hvec1 : ∀ w j, fcoord b (fun _ => (1 : Matrix ι ι ℂ)) w x j = vecAt b w x j := fun w j => by
      change ((1 : Matrix ι ι ℂ)⁻¹ *ᵥ vecAt b w x) j = vecAt b w x j
      have h1inv : (1 : Matrix ι ι ℂ)⁻¹ = 1 := Matrix.inv_eq_right_inv (Matrix.one_mul 1)
      rw [h1inv, Matrix.one_mulVec]
    have hmul : (M.mulVec (realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) x).ofLp) (v, i, r) =
        ∑ j : ι,
          (if r = 0 then
            ((X v)⁻¹ i j).re * (vecAt b v x j).re - ((X v)⁻¹ i j).im * (vecAt b v x j).im
          else
            ((X v)⁻¹ i j).im * (vecAt b v x j).re + ((X v)⁻¹ i j).re * (vecAt b v x j).im) := by
      unfold Matrix.mulVec dotProduct
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single v]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Fin.sum_univ_two]
        have h0 : (realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) x).ofLp (v, j, 0) =
            (vecAt b v x j).re := by
          change realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) x (v, j, 0) = _
          rw [RHDirect.Stage14M2_HLatNumberField.realizeHLat_apply0, hvec1]
        have h1 : (realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) x).ofLp (v, j, 1) =
            (vecAt b v x j).im := by
          change realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) x (v, j, 1) = _
          rw [RHDirect.Stage14M2_HLatNumberField.realizeHLat_apply1, hvec1]
        rw [h0, h1]
        fin_cases r
        · simp [M, blockDiagMat, realMatrixOfComplex]; ring
        · simp [M, blockDiagMat, realMatrixOfComplex]
      · intro w _ hwv
        refine Finset.sum_eq_zero fun p _ => ?_
        simp [M, blockDiagMat, Ne.symm hwv]
      · intro hv; exact absurd (Finset.mem_univ v) hv
    change (M.mulVec (realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) x).ofLp) (v, i, r) =
      realizeHLat b X x (v, i, r)
    rw [hmul]
    have hfc : fcoord b X v x i = ∑ j : ι, (X v)⁻¹ i j * vecAt b v x j := rfl
    fin_cases r
    · change (∑ j : ι, if (0 : Fin 2) = 0 then _ else _) = realizeHLat b X x (v, i, 0)
      rw [RHDirect.Stage14M2_HLatNumberField.realizeHLat_apply0, hfc, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => by simp [Complex.mul_re]
    · change (∑ j : ι, if (1 : Fin 2) = 0 then _ else _) = realizeHLat b X x (v, i, 1)
      rw [RHDirect.Stage14M2_HLatNumberField.realizeHLat_apply1, hfc, Complex.im_sum]
      refine Finset.sum_congr rfl fun j _ => by simp [Complex.mul_im]; ring
  have hmap_eq : (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L).map (T.restrictScalars ℤ) =
      zRealize b X L := by
    ext w
    constructor
    · rintro ⟨_, ⟨x, hxL, rfl⟩, rfl⟩
      exact ⟨x, hxL, (hT_real x).symm⟩
    · rintro ⟨x, hxL, rfl⟩
      exact ⟨realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) x, ⟨x, hxL, rfl⟩, hT_real x⟩
  obtain ⟨_, _, hcov⟩ := covol_mulVec_fullRank M hM_unit (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L) hfull
  rw [hmap_eq, abs_of_pos hM_det_pos, hM_det] at hcov
  exact hcov

/-- Exact frame-change formula for normalized slope `muDef` (valid for ANY good `HLat K`, even with
nontrivial Steinitz class!):
`muDef b X L - muDef b Y L = (4 / ([K : ℚ] * #ι)) * ∑ v, (log ‖(X v).det‖ - log ‖(Y v).det‖)`. -/
theorem muDef_frame_change {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (b : Module.Basis ι K V) (X Y : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hY : ∀ v, IsUnit (Y v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) :
    muDef b X L - muDef b Y L =
      (4 / ((Module.finrank ℚ K : ℝ) * (Fintype.card ι : ℝ))) *
        ∑ v : InfinitePlace K, (Real.log ‖(X v).det‖ - Real.log ‖(Y v).det‖) := by
  have h1X : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix ι ι ℂ)).det := fun _ => by simp
  haveI : DiscreteTopology (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L) :=
    discreteTopology_zRealize_of_fg b (fun _ => 1) h1X L hL
  haveI : DiscreteTopology (zRealize b X L) := discreteTopology_zRealize_of_fg b X hX L hL
  haveI : DiscreteTopology (zRealize b Y L) := discreteTopology_zRealize_of_fg b Y hY L hL
  have hcovX := covol_zRealize_eq_prod_det_mul_unitFrame b X hX L hL hsp
  have hcovY := covol_zRealize_eq_prod_det_mul_unitFrame b Y hY L hL hsp
  have hlog_det : ∀ (Z : InfinitePlace K → Matrix ι ι ℂ) (hZ : ∀ v, IsUnit (Z v).det),
      Real.log (covol (zRealize b Z L)) =
        -2 * (∑ v : InfinitePlace K, Real.log ‖(Z v).det‖) +
          Real.log (covol (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L)) := by
    intro Z hZ
    have hcovZ := covol_zRealize_eq_prod_det_mul_unitFrame b Z hZ L hL hsp
    have hprod_pos : 0 < ∏ v : InfinitePlace K, (Complex.normSq (Z v).det)⁻¹ :=
      Finset.prod_pos fun v _ => inv_pos.mpr (Complex.normSq_pos.mpr (hZ v).ne_zero)
    rw [hcovZ, Real.log_mul hprod_pos.ne' (covol_pos _).ne',
      Real.log_prod (fun v _ => (inv_pos.mpr (Complex.normSq_pos.mpr (hZ v).ne_zero)).ne')]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Real.log_inv, Complex.normSq_eq_norm_sq, Real.log_pow]
    ring
  have hrkX : rk (zRealize b X L) = Module.finrank ℚ K * Fintype.card ι := by
    rw [rk_zRealize_eq b X hX L hL]
    unfold rkK
    rw [hsp, finrank_top, Module.finrank_eq_card_basis b]
  have hrkY : rk (zRealize b Y L) = Module.finrank ℚ K * Fintype.card ι := by
    rw [rk_zRealize_eq b Y hY L hL]
    unfold rkK
    rw [hsp, finrank_top, Module.finrank_eq_card_basis b]
  have hden_ne : (Module.finrank ℚ K : ℝ) * (Fintype.card ι : ℝ) ≠ 0 := by
    have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
    have hi : 0 < Fintype.card ι := Fintype.card_pos
    positivity
  unfold muDef slopeHLat ArakelovCovolume.slope degAr
  rw [hrkX, hrkY, hlog_det X hX, hlog_det Y hY, Finset.sum_sub_distrib]
  push_cast
  field_simp [hden_ne]
  ring

/-! ### Exact Invariants of the Canonical Unit `𝓞 K`-Lattice (`unitHLat K`) & Free `HLat K` -/

/-- Canonical rank-1 unit Hermitian lattice `(K, 1, 1, 𝓞 K)` over a number field `K`. -/
def unitHLat (K : Type) [Field K] [NumberField K] [StarRing K] : HLat K where
  V := K
  ι := PUnit.{1}
  b := Module.Basis.singleton PUnit.{1} K
  X := fun _ => 1
  L := Submodule.span (𝓞 K) {(1 : K)}

theorem unitHLat_good (K : Type) [Field K] [NumberField K] [StarRing K] :
    (unitHLat K).Good := by
  refine ⟨fun _ => by change IsUnit ((1 : Matrix PUnit.{1} PUnit.{1} ℂ).det); simp,
    ⟨{(1 : K)}, by change Submodule.span (𝓞 K) ({(1 : K)} : Finset K) = Submodule.span (𝓞 K) {(1 : K)}; simp⟩, ?_⟩
  change Submodule.span K ((Submodule.span (𝓞 K) {(1 : K)} : Submodule (𝓞 K) K) : Set K) = ⊤
  apply le_antisymm le_top
  intro x _
  have h1 : (1 : K) ∈ Submodule.span (𝓞 K) {(1 : K)} := Submodule.subset_span (Set.mem_singleton 1)
  have hx1 : x • (1 : K) ∈ Submodule.span K ((Submodule.span (𝓞 K) {(1 : K)} : Submodule (𝓞 K) K) : Set K) :=
    Submodule.smul_mem _ x (Submodule.subset_span h1)
  rwa [smul_eq_mul, mul_one] at hx1

theorem unitHLat_rank (K : Type) [Field K] [NumberField K] [StarRing K] :
    (unitHLat K).rank = 1 := by
  unfold HLat.rank rkK
  rw [(unitHLat_good K).2.2, finrank_top]
  exact Module.finrank_self K

theorem unitHLat_ne_bot (K : Type) [Field K] [NumberField K] [StarRing K] :
    (unitHLat K).L ≠ ⊥ := by
  intro hbot
  change Submodule.span (𝓞 K) {(1 : K)} = ⊥ at hbot
  have h1 : (1 : K) ∈ Submodule.span (𝓞 K) {(1 : K)} := Submodule.subset_span (Set.mem_singleton 1)
  rw [hbot, Submodule.mem_bot] at h1
  exact one_ne_zero h1

/-- **Self-Duality Vanishing (`unitHLat_mu_eq_zero`)**:
for every totally complex number field `K`, `(unitHLat K).mu = 0`, proved directly from
`hlat_duality_slope_neg` via the isometric identification `dualHLat (unitHLat K) ≃ unitHLat K`! -/
theorem unitHLat_mu_eq_zero (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] :
    (unitHLat K).mu = 0 := by
  have hG := unitHLat_good K
  have hr : 0 < (unitHLat K).rank := by rw [unitHLat_rank]; exact one_pos
  have hneg := (hlat_duality_slope_neg (unitHLat K) hG hr).1
  let b1 : Module.Basis PUnit.{1} K K := Module.Basis.singleton PUnit.{1} K
  let X1 : InfinitePlace K → Matrix PUnit.{1} PUnit.{1} ℂ := fun _ => 1
  let L1 : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have h1inv : (1 : Matrix PUnit.{1} PUnit.{1} ℂ)⁻¹ = 1 :=
    Matrix.inv_eq_right_inv (Matrix.one_mul 1)
  have hdualX : dualFrame X1 = X1 := by
    funext v
    unfold dualFrame
    simp only [X1, Matrix.transpose_one, h1inv]
  have hreal_eq : ∀ f : Module.Dual K K,
      realizeHLat b1.dualBasis (dualFrame X1) f = realizeHLat b1 X1 (f 1) := by
    intro f
    rw [hdualX]
    ext ⟨v, u, r⟩
    have hrepr : b1.dualBasis.repr f u = b1.repr (f 1) u := by
      have hu : u = PUnit.unit := rfl
      subst hu
      have h1 : b1.dualBasis.repr f PUnit.unit = f (b1 PUnit.unit) := by
        have hf := b1.dualBasis.sum_repr f
        have := congrArg (fun g : Module.Dual K K => g (b1 PUnit.unit)) hf
        simp only [LinearMap.smul_apply, smul_eq_mul, Module.Basis.dualBasis_apply_self,
          Fintype.sum_unique, ite_true, mul_one] at this
        exact this
      rw [h1]
      simp [b1]
    have hfc : fcoord b1.dualBasis X1 v f u = fcoord b1 X1 v (f 1) u := by
      change ((X1 v)⁻¹ *ᵥ vecAt b1.dualBasis v f) u = ((X1 v)⁻¹ *ᵥ vecAt b1 v (f 1)) u
      congr 1
      funext u'
      have hu' : u' = PUnit.unit := rfl
      subst hu'
      have hu : u = PUnit.unit := rfl
      rw [hu] at hrepr
      change v.embedding (b1.dualBasis.repr f PUnit.unit) = v.embedding (b1.repr (f 1) PUnit.unit)
      rw [hrepr]
    fin_cases r
    · change (fcoord b1.dualBasis X1 v f u).re = (fcoord b1 X1 v (f 1) u).re
      rw [hfc]
    · change (fcoord b1.dualBasis X1 v f u).im = (fcoord b1 X1 v (f 1) u).im
      rw [hfc]
  have hz_eq : zRealize b1.dualBasis (dualFrame X1) (dualLatO (K := K) L1) =
      zRealize b1 X1 L1 := by
    ext w
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨f 1, ?_, (hreal_eq f).symm⟩
      have h1mem : (1 : K) ∈ L1 := Submodule.subset_span (Set.mem_singleton 1)
      obtain ⟨z, hz⟩ := hf 1 h1mem
      have heq : f 1 = z • (1 : K) := by
        rw [← hz]; simp [Algebra.smul_def]
      rw [heq]
      exact Submodule.smul_mem _ z h1mem
    · rintro ⟨x, hx, rfl⟩
      let f : Module.Dual K K := LinearMap.mulLeft K x
      have hf : f ∈ dualLatO (K := K) L1 := by
        intro y hy
        rw [show L1 = Submodule.span (𝓞 K) {(1 : K)} from rfl, Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hy
        have hx' : x ∈ Submodule.span (𝓞 K) {(1 : K)} := hx
        rw [Submodule.mem_span_singleton] at hx'
        obtain ⟨b, rfl⟩ := hx'
        refine ⟨b * a, ?_⟩
        change algebraMap (𝓞 K) K (b * a) = f (a • (1 : K))
        simp [f, Algebra.smul_def]
      refine ⟨f, hf, ?_⟩
      change realizeHLat b1.dualBasis (dualFrame X1) f = realizeHLat b1 X1 x
      rw [hreal_eq f]
      simp [f]
  have hmu_eq : (dualHLat (unitHLat K)).mu = (unitHLat K).mu := by
    change 2 * ArakelovCovolume.slope (zRealize b1.dualBasis (dualFrame X1) (dualLatO (K := K) L1)) -
        Real.log 2 + logDiscDivDeg K =
      2 * ArakelovCovolume.slope (zRealize b1 X1 L1) - Real.log 2 + logDiscDivDeg K
    rw [hz_eq]
  linarith

/-- Exact `ℤ`-slope of `unitHLat K` with explicit different-ideal normalization via
`absNorm_differentIdeal_eq_discr`. -/
theorem unitHLat_slope_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] :
    slopeHLat (unitHLat K).b (unitHLat K).X (unitHLat K).L =
      (Real.log 2 -
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2 := by
  have h0 : (unitHLat K).mu = 0 := unitHLat_mu_eq_zero K
  have hdisc := absNorm_differentIdeal_eq_discr K
  change 2 * slopeHLat (unitHLat K).b (unitHLat K).X (unitHLat K).L - Real.log 2 +
    logDiscDivDeg K = 0 at h0
  unfold logDiscDivDeg at h0
  rw [← hdisc] at h0
  linarith

/-- Exact covolume of `unitHLat K`:
`covol (unitHLat K).zRealize = 2 ^ (-#InfinitePlace K) * √(Ideal.absNorm (differentIdeal ℤ (𝓞 K)))`. -/
theorem unitHLat_covol_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] :
    covol (unitHLat K).zRealize =
      (2 : ℝ) ^ (-(Fintype.card (InfinitePlace K) : ℤ)) *
        Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) := by
  haveI : DiscreteTopology (unitHLat K).zRealize :=
    discreteTopology_zRealize_of_fg _ _ (unitHLat_good K).1 _ (unitHLat_good K).2.1
  have hdiff_pos : (0 : ℝ) < (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) := by
    rw [absNorm_differentIdeal_eq_discr K]
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hrhs_pos : 0 < (2 : ℝ) ^ (-(Fintype.card (InfinitePlace K) : ℤ)) *
      Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) :=
    mul_pos (zpow_pos two_pos _) (Real.sqrt_pos.mpr hdiff_pos)
  apply Real.log_injOn_pos (covol_pos (unitHLat K).zRealize) hrhs_pos
  have hsl := unitHLat_slope_eq K
  have hrk : rk (unitHLat K).zRealize = Module.finrank ℚ K := by
    rw [rk_zRealize_eq _ _ (unitHLat_good K).1 _ (unitHLat_good K).2.1]
    change Module.finrank ℚ K * (unitHLat K).rank = Module.finrank ℚ K
    rw [unitHLat_rank, mul_one]
  have hn_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hdeg : -Real.log (covol (unitHLat K).zRealize) =
      (Module.finrank ℚ K : ℝ) *
        ((Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) := by
    have h1 : slopeHLat (unitHLat K).b (unitHLat K).X (unitHLat K).L =
        -Real.log (covol (unitHLat K).zRealize) / (rk (unitHLat K).zRealize : ℝ) := rfl
    rw [hsl, hrk] at h1
    have h2 := (eq_div_iff hn_pos.ne').mp h1
    linarith
  rw [Real.log_mul (zpow_pos two_pos _).ne' (Real.sqrt_pos.mpr hdiff_pos).ne',
    Real.log_zpow, Real.log_sqrt hdiff_pos.le]
  have hcard : (2 : ℝ) * (Fintype.card (InfinitePlace K) : ℝ) = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast two_mul_card_infinitePlace (K := K)
  have h1 : Real.log (covol (unitHLat K).zRealize) =
      -((Module.finrank ℚ K : ℝ) / 2) * Real.log 2 +
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / 2 := by
    have hcancel : (Module.finrank ℚ K : ℝ) *
        (Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) =
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) :=
      mul_div_cancel₀ _ hn_pos.ne'
    linarith
  rw [h1, ← hcard]
  push_cast
  ring

/-- **Exact Free `HLat K` Covolume Formula (`freeHLat_covol_eq`)**:
for ANY totally complex number field `K`, basis `b : Module.Basis ι K V`, invertible frame `X`,
and free `𝓞 K`-lattice `L₀ = span (𝓞 K) (range b)`:
`covol (zRealize b X L₀) = (∏ v, (normSq (X v).det)⁻¹) * (2^(-r₂) * √(absNorm (differentIdeal)))^#ι`. -/
theorem freeHLat_covol_eq {K V ι : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) :
    let L₀ : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)
    covol (zRealize b X L₀) =
      (∏ v : InfinitePlace K, (Complex.normSq (X v).det)⁻¹) *
        ((2 : ℝ) ^ (-(Fintype.card (InfinitePlace K) : ℤ)) *
          Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ)) ^ Fintype.card ι := by
  classical
  intro L₀
  have hL₀_fg : L₀.FG := ⟨Finset.univ.image b, by simp [L₀]⟩
  have hL₀_sp : Submodule.span K (L₀ : Set V) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  rw [covol_zRealize_eq_prod_det_mul_unitFrame b X hX L₀ hL₀_fg hL₀_sp, ← unitHLat_covol_eq K]
  congr 1
  -- Prove `covol (zRealize b 1 L₀) = (covol (unitHLat K).zRealize) ^ #ι` via block-diagonal Gram matrix!
  have h1X : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix ι ι ℂ)).det := fun _ => by simp
  haveI : DiscreteTopology (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L₀) :=
    discreteTopology_zRealize_of_fg b (fun _ => 1) h1X L₀ hL₀_fg
  haveI : DiscreteTopology (unitHLat K).zRealize :=
    discreteTopology_zRealize_of_fg _ _ (unitHLat_good K).1 _ (unitHLat_good K).2.1
  let κ := Free.ChooseBasisIndex ℤ (𝓞 K)
  -- Explicit `ℤ`-basis of `zRealize b 1 L₀` indexed by `ι × κ`.
  let vL : ι × κ → EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
    fun p => realizeHLat b (fun _ => (1 : Matrix ι ι ℂ)) (NumberField.integralBasis K p.2 • b p.1)
  have hspanL : zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L₀ =
      Submodule.span ℤ (Set.range vL) := by
    rw [show L₀ = Submodule.span (𝓞 K) (Set.range b) from rfl, zRealize_span_eq]
    congr 1; ext w
    simp only [Set.mem_range, Prod.exists, vL]
    exact ⟨fun ⟨k, i, h⟩ => ⟨i, k, h⟩, fun ⟨i, k, h⟩ => ⟨k, i, h⟩⟩
  have hvL_liR : LinearIndependent ℝ vL := by
    have h := linearIndependent_realizeHLat_integralBasis b (fun _ => (1 : Matrix ι ι ℂ)) h1X b
      b.linearIndependent
    exact h.comp (fun p : ι × κ => (p.2, p.1)) (fun _ _ hp => Prod.ext (Prod.mk.inj hp).2 (Prod.mk.inj hp).1)
  let bL : Module.Basis (ι × κ) ℤ (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L₀) :=
    Module.Basis.mk
      (v := fun p => ⟨vL p, hspanL ▸ Submodule.subset_span ⟨p, rfl⟩⟩)
      (LinearIndependent.of_comp (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L₀).subtype
        (hvL_liR.restrict_scalars fun a c h => by simpa [zsmul_eq_mul] using h))
      (by
        intro y _
        have hy : (y : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) ∈
            Submodule.span ℤ (Set.range vL) := hspanL ▸ y.2
        rw [Submodule.mem_span_range_iff_exists_fun] at hy
        obtain ⟨c, hc⟩ := hy
        have hy' : y = ∑ p : ι × κ, c p • ⟨vL p, hspanL ▸ Submodule.subset_span ⟨p, rfl⟩⟩ := by
          apply Subtype.ext; rw [Submodule.coe_sum]; simpa using hc.symm
        rw [hy']
        exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
  -- Explicit `ℤ`-basis of `zRealize b1 X1 L1` (`= (unitHLat K).zRealize`) indexed by `κ`.
  let b1 : Module.Basis PUnit.{1} K K := Module.Basis.singleton PUnit.{1} K
  let X1 : InfinitePlace K → Matrix PUnit.{1} PUnit.{1} ℂ := fun _ => 1
  let L1 : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have h1X1 : ∀ v : InfinitePlace K, IsUnit (X1 v).det := fun _ => by simp [X1]
  haveI : DiscreteTopology (zRealize b1 X1 L1) :=
    discreteTopology_zRealize_of_fg b1 X1 h1X1 L1 ⟨{1}, by simp [L1]⟩
  let u1 : κ → EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2) :=
    fun k => realizeHLat b1 X1 (NumberField.integralBasis K k • b1 PUnit.unit)
  have hspanU : zRealize b1 X1 L1 = Submodule.span ℤ (Set.range u1) := by
    have hL1 : L1 = Submodule.span (𝓞 K) (Set.range b1) := by
      unfold L1; congr 1; ext x; simp [b1]
    rw [hL1, zRealize_span_eq]
    congr 1; ext w
    simp only [Set.mem_range, Prod.exists, u1]
    exact ⟨fun ⟨k, ⟨⟩, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, PUnit.unit, h⟩⟩
  have hu1_liR : LinearIndependent ℝ u1 := by
    have h := linearIndependent_realizeHLat_integralBasis b1 X1 h1X1 b1 b1.linearIndependent
    exact h.comp (fun k : κ => (k, PUnit.unit)) (fun _ _ hk => (Prod.mk.inj hk).1)
  let bU : Module.Basis κ ℤ (zRealize b1 X1 L1) :=
    Module.Basis.mk
      (v := fun k => ⟨u1 k, hspanU ▸ Submodule.subset_span ⟨k, rfl⟩⟩)
      (LinearIndependent.of_comp (zRealize b1 X1 L1).subtype
        (hu1_liR.restrict_scalars fun a c h => by simpa [zsmul_eq_mul] using h))
      (by
        intro y _
        have hy : (y : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2)) ∈
            Submodule.span ℤ (Set.range u1) := hspanU ▸ y.2
        rw [Submodule.mem_span_range_iff_exists_fun] at hy
        obtain ⟨c, hc⟩ := hy
        have hy' : y = ∑ k : κ, c k • ⟨u1 k, hspanU ▸ Submodule.subset_span ⟨k, rfl⟩⟩ := by
          apply Subtype.ext; rw [Submodule.coe_sum]; simpa using hc.symm
        rw [hy']
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  -- Identify the Gram matrix of `bL` as `blockDiagMat (fun _ : ι => gram bU)`.
  let GU : Matrix κ κ ℝ := Matrix.gram ℝ (fun k => (bU k : EuclideanSpace ℝ (InfinitePlace K × PUnit.{1} × Fin 2)))
  have hgram_eq : Matrix.gram ℝ (fun p => (bL p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
      blockDiagMat (fun _ : ι => GU) := by
    ext ⟨i₁, k₁⟩ ⟨i₂, k₂⟩
    simp only [Matrix.gram_apply, blockDiagMat, Matrix.of_apply, GU, bL, bU, Module.Basis.coe_mk]
    rw [inner_realizeHLat_eq_sum_majAt, inner_realizeHLat_eq_sum_majAt]
    have h1invι : (1 : Matrix ι ι ℂ)⁻¹ = 1 := Matrix.inv_eq_right_inv (Matrix.one_mul 1)
    have h1inv1 : (1 : Matrix PUnit.{1} PUnit.{1} ℂ)⁻¹ = 1 := Matrix.inv_eq_right_inv (Matrix.one_mul 1)
    have hfcL : ∀ (v : InfinitePlace K) (i : ι) (k : κ),
        fcoord b (fun _ => (1 : Matrix ι ι ℂ)) v (NumberField.integralBasis K k • b i) =
          Pi.single i (v.embedding (NumberField.integralBasis K k)) := fun v i k => by
      change (1 : Matrix ι ι ℂ)⁻¹ *ᵥ vecAt b v (NumberField.integralBasis K k • b i) = _
      rw [h1invι, Matrix.one_mulVec, vecAt_smul_basis]
    have hfcU : ∀ (v : InfinitePlace K) (k : κ),
        fcoord b1 X1 v (NumberField.integralBasis K k • b1 PUnit.unit) =
          Pi.single PUnit.unit (v.embedding (NumberField.integralBasis K k)) := fun v k => by
      change (1 : Matrix PUnit.{1} PUnit.{1} ℂ)⁻¹ *ᵥ
        vecAt b1 v (NumberField.integralBasis K k • b1 PUnit.unit) = _
      rw [h1inv1, Matrix.one_mulVec, vecAt_smul_basis]
    by_cases hi : i₁ = i₂
    · subst hi
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun v _ => ?_
      congr 1
      unfold majAt
      rw [hfcL v i₁ k₁, hfcL v i₁ k₂, hfcU v k₁, hfcU v k₂]
      rw [Finset.sum_eq_single i₁]
      · simp
      · intro j _ hji; simp [Pi.single_eq_of_ne hji]
      · intro h; exact absurd (Finset.mem_univ i₁) h
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun v _ => ?_
      have h0 : majAt b (fun _ => (1 : Matrix ι ι ℂ)) v
          (NumberField.integralBasis K k₁ • b i₁) (NumberField.integralBasis K k₂ • b i₂) = 0 := by
        unfold majAt
        rw [hfcL v i₁ k₁, hfcL v i₂ k₂]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j = i₁
        · subst hj
          have hj2 : j ≠ i₂ := hi
          simp [Pi.single_eq_of_ne hj2]
        · simp [Pi.single_eq_of_ne hj]
      rw [h0, Complex.zero_re]
  change covol (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L₀) = covol (zRealize b1 X1 L1) ^ Fintype.card ι
  rw [covol_eq_sqrt_det_gram _ bL, covol_eq_sqrt_det_gram _ bU, hgram_eq, det_blockDiagMat,
    Finset.prod_const, Finset.card_univ]
  have hdetU_nn : 0 ≤ GU.det := (det_gram_basis_pos (zRealize b1 X1 L1) bU).le
  have hsqrt_pow : ∀ (x : ℝ) (n : ℕ), 0 ≤ x → Real.sqrt (x ^ n) = (Real.sqrt x) ^ n := by
    intro x n hx
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx m), ih]
  exact hsqrt_pow GU.det (Fintype.card ι) hdetU_nn

/-- **Exact Free `HLat K` Normalized Slope Formula (`freeHLat_mu_eq`)**:
for ANY totally complex number field `K`, nonempty finite `ι`, basis `b : Module.Basis ι K V`,
invertible frame `X`, and `L₀ = span (𝓞 K) (range b)`:
`muDef b X L₀ = (4 / ([K : ℚ] * #ι)) * ∑ v : InfinitePlace K, log ‖(X v).det‖`. -/
theorem freeHLat_mu_eq {K V ι : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) :
    let L₀ : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)
    muDef b X L₀ =
      (4 / ((Module.finrank ℚ K : ℝ) * (Fintype.card ι : ℝ))) *
        ∑ v : InfinitePlace K, Real.log ‖(X v).det‖ := by
  classical
  intro L₀
  have hL₀_fg : L₀.FG := ⟨Finset.univ.image b, by simp [L₀]⟩
  have hL₀_sp : Submodule.span K (L₀ : Set V) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  have h1X : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix ι ι ℂ)).det := fun _ => by simp
  have hcov1 := freeHLat_covol_eq b (fun _ => (1 : Matrix ι ι ℂ)) h1X
  simp only [Matrix.det_one, map_one, inv_one, Finset.prod_const_one, one_mul] at hcov1
  have hmu1 : muDef b (fun _ => (1 : Matrix ι ι ℂ)) L₀ = 0 := by
    haveI : DiscreteTopology (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L₀) :=
      discreteTopology_zRealize_of_fg b (fun _ => 1) h1X L₀ hL₀_fg
    have hrk1 : rk (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L₀) =
        Module.finrank ℚ K * Fintype.card ι := by
      rw [rk_zRealize_eq b (fun _ => 1) h1X L₀ hL₀_fg]
      unfold rkK
      rw [hL₀_sp, finrank_top, Module.finrank_eq_card_basis b]
    have hdiff_pos : (0 : ℝ) < (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) := by
      rw [absNorm_differentIdeal_eq_discr K]
      exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    have hlog1 : Real.log (covol (zRealize b (fun _ => (1 : Matrix ι ι ℂ)) L₀)) =
        (Fintype.card ι : ℝ) *
          (-(Fintype.card (InfinitePlace K) : ℝ) * Real.log 2 +
            Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / 2) := by
      rw [hcov1, Real.log_pow,
        Real.log_mul (zpow_pos two_pos _).ne' (Real.sqrt_pos.mpr hdiff_pos).ne',
        Real.log_zpow, Real.log_sqrt hdiff_pos.le]
      push_cast; ring
    have hcard : (2 : ℝ) * (Fintype.card (InfinitePlace K) : ℝ) = (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast two_mul_card_infinitePlace (K := K)
    have hn_ne : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hi_ne : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
    unfold muDef slopeHLat ArakelovCovolume.slope degAr logDiscDivDeg
    rw [hrk1, hlog1, ← absNorm_differentIdeal_eq_discr K]
    push_cast
    field_simp [hn_ne, hi_ne]
    rw [← hcard]
    ring
  have hchg := muDef_frame_change b X (fun _ => (1 : Matrix ι ι ℂ)) hX h1X L₀ hL₀_fg hL₀_sp
  simp only [Matrix.det_one, norm_one, Real.log_one, sub_zero, hmu1, sub_zero] at hchg
  exact hchg

/-- Exact `ℤ`-slope of any free `HLat K` with explicit different-ideal term. -/
theorem freeHLat_slope_eq {K V ι : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) :
    let L₀ : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)
    slopeHLat b X L₀ =
      (2 / ((Module.finrank ℚ K : ℝ) * (Fintype.card ι : ℝ))) *
          (∑ v : InfinitePlace K, Real.log ‖(X v).det‖) +
        (Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2 := by
  intro L₀
  have hmu := freeHLat_mu_eq b X hX
  change 2 * slopeHLat b X L₀ - Real.log 2 + logDiscDivDeg K = _ at hmu
  unfold logDiscDivDeg at hmu
  rw [← absNorm_differentIdeal_eq_discr K] at hmu
  have h4 : (4 : ℝ) / ((Module.finrank ℚ K : ℝ) * (Fintype.card ι : ℝ)) =
      2 * (2 / ((Module.finrank ℚ K : ℝ) * (Fintype.card ι : ℝ))) := by ring
  rw [h4] at hmu
  linarith

/-! ### `bc_mu_column_lattice` — Base-Change & Bost–Chen Column-Lattice Exact Slope -/

/-- Rescale the archimedean frame of `A : HLat K` by a positive place-dependent factor
`c : InfinitePlace K → ℝ` (`X v ↦ (c v : ℂ) • X v`). -/
def rescaleHLatFrame {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (c : InfinitePlace K → ℝ) : HLat K :=
  { A with X := fun v => (c v : ℂ) • A.X v }

theorem rescaleHLatFrame_good {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 < c v) :
    (rescaleHLatFrame A c).Good := by
  refine ⟨fun v => ?_, hG.2.1, hG.2.2⟩
  change IsUnit ((c v : ℂ) • A.X v).det
  rw [Matrix.det_smul]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hc v).ne'))).mul (hG.1 v)

theorem rescaleHLatFrame_mu {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [StarRing K] (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 < c v) :
    (rescaleHLatFrame A c).mu =
      A.mu + (4 / (Module.finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log (c v) := by
  haveI : Module.Finite K A.V := Module.Finite.of_basis A.b
  have hrank_pos := anchorOfHLat_rank_pos A hG hA0
  have hne : Nonempty A.ι := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have hcard0 : Fintype.card A.ι = 0 := Fintype.card_eq_zero
    have hV0 : Module.finrank K A.V = 0 := by rw [Module.finrank_eq_card_basis A.b, hcard0]
    have hle : A.rank ≤ Module.finrank K A.V := Submodule.finrank_le _
    omega
  let X' : InfinitePlace K → Matrix A.ι A.ι ℂ := fun v => (c v : ℂ) • A.X v
  have hX' : ∀ v : InfinitePlace K, IsUnit (X' v).det := (rescaleHLatFrame_good A hG c hc).1
  have hchg := muDef_frame_change A.b X' A.X hX' hG.1 A.L hG.2.1 hG.2.2
  have hterms : ∀ v : InfinitePlace K,
      Real.log ‖(X' v).det‖ - Real.log ‖(A.X v).det‖ =
        (Fintype.card A.ι : ℝ) * Real.log (c v) := by
    intro v
    change Real.log ‖((c v : ℂ) • A.X v).det‖ - Real.log ‖(A.X v).det‖ = _
    rw [Matrix.det_smul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (hc v).le,
      Real.log_mul (pow_pos (hc v) _).ne' (norm_pos_iff.mpr (hG.1 v).ne_zero).ne', Real.log_pow]
    ring
  have hsum_eq : ∑ v : InfinitePlace K,
      (Real.log ‖(X' v).det‖ - Real.log ‖(A.X v).det‖) =
      (Fintype.card A.ι : ℝ) * ∑ v : InfinitePlace K, Real.log (c v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => hterms v
  rw [hsum_eq] at hchg
  have hi_ne : (Fintype.card A.ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hn_ne : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hcalc : (4 / ((Module.finrank ℚ K : ℝ) * (Fintype.card A.ι : ℝ))) *
      ((Fintype.card A.ι : ℝ) * ∑ v : InfinitePlace K, Real.log (c v)) =
      (4 / (Module.finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log (c v) := by
    field_simp [hn_ne, hi_ne]
  rw [hcalc] at hchg
  change muDef A.b X' A.L = muDef A.b A.X A.L + _
  linarith

/-- **MAIN DELIVERABLE #1B — Bost–Chen / Base-Change Column-Lattice Exact Slope Theorem
(`bc_mu_column_lattice`)**:
Unifies the exact column-lattice slope for:
1. Any `S : SchurFunctorColumnLat`:
   `(anchorOfConcreteLat S.colLat).slope = (S.lam.weight : ℝ) * (anchorOfConcreteLat S.base).slope`
   and `Real.log (anchorOfConcreteLat S.colLat).covol / ((anchorOfConcreteLat S.colLat).rk : ℝ) = (S.lam.weight : ℝ) * (Real.log (anchorOfConcreteLat S.base).covol / ((anchorOfConcreteLat S.base).rk : ℝ))`.
2. Rescaled column lattices `scaleLat c` (`c > 0`):
   `(anchorOfColumnTensor (anchorOfScale H hc) lam).slope = (lam.weight : ℝ) * (H.slope - Real.log c)`.
3. Archimedean base change of a constant matrix frame `M : Matrix ι ι ℂ` (`IsUnit M.det`) from `ℚ`
   to ANY totally complex number field `K`:
   `muDef b (fun _ => M) (span (𝓞 K) (range b)) = (2 / (#ι : ℝ)) * Real.log ‖M.det‖`
   (completely invariant under base change of CM number field `K`!). -/
theorem bc_mu_column_lattice (S : SchurFunctorColumnLat) :
    (anchorOfConcreteLat S.colLat).rk =
      ∏ j ∈ Finset.range S.lam.maxPart, Nat.choose (anchorOfConcreteLat S.base).rk (S.lam.colLen j) ∧
    (anchorOfConcreteLat S.colLat).slope =
      (S.lam.weight : ℝ) * (anchorOfConcreteLat S.base).slope ∧
    Real.log (anchorOfConcreteLat S.colLat).covol / ((anchorOfConcreteLat S.colLat).rk : ℝ) =
      (S.lam.weight : ℝ) *
        (Real.log (anchorOfConcreteLat S.base).covol / ((anchorOfConcreteLat S.base).rk : ℝ)) := by
  have hq := q_lattice_slope_exact (anchorOfConcreteLat S.base) S.lam
  exact ⟨hq.1, hq.2.1, hq.2.2.2⟩

/-- Rescaled column-lattice slope shift (`bc_mu_column_lattice_scale`). -/
theorem bc_mu_column_lattice_scale (H : HLatAnchor) {c : ℝ} (hc : 0 < c)
    (lam : Partition (anchorOfScale H hc).rk) :
    (anchorOfColumnTensor (anchorOfScale H hc) lam).slope =
      (lam.weight : ℝ) * (H.slope - Real.log c) := by
  rw [(q_lattice_slope_exact (anchorOfScale H hc) lam).2.1, (anchorOfScale_invariants H hc).2.2.2]

/-- Base-change invariance of normalized Arakelov slope `muDef` under scalar extension to any
totally complex number field `K` (`bc_mu_base_change_invariance`). -/
theorem bc_mu_base_change_invariance {K V ι : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (b : Module.Basis ι K V) (M : Matrix ι ι ℂ) (hM : IsUnit M.det) :
    muDef b (fun _ => M) (Submodule.span (𝓞 K) (Set.range b)) =
      (2 / (Fintype.card ι : ℝ)) * Real.log ‖M.det‖ := by
  rw [freeHLat_mu_eq b (fun _ => M) (fun _ => hM), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (2 : ℝ) * (Fintype.card (InfinitePlace K) : ℝ) = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast two_mul_card_infinitePlace (K := K)
  have hn_ne : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hi_ne : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  field_simp [hn_ne, hi_ne]
  rw [← hcard]
  ring

/-- Place-dependent archimedean rescaling of a number-field column-tensor lattice. -/
theorem bc_mu_column_lattice_rescaleFrame {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 < c v)
    (lam : Partition (anchorOfHLat (rescaleHLatFrame A c) (rescaleHLatFrame_good A hG c hc) hA0).rk) :
    (anchorOfColumnTensor
        (anchorOfHLat (rescaleHLatFrame A c) (rescaleHLatFrame_good A hG c hc) hA0) lam).slope =
      (lam.weight : ℝ) *
        ((A.mu + Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2 +
          (2 / (Module.finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log (c v)) := by
  rw [(q_lattice_slope_exact _ lam).2.1,
    anchorOfHLat_slope_eq_from_mu (rescaleHLatFrame A c) (rescaleHLatFrame_good A hG c hc) hA0,
    rescaleHLatFrame_mu A hG hA0 c hc]
  unfold logDiscDivDeg
  rw [← absNorm_differentIdeal_eq_discr K]
  ring

end ComplexRealDetAndBaseChange

/-! ## Section 3: Number-Field Column-Lattice Exact Slope Identity
(`column_lattice_exact_slope_nf`) -/

section NumberFieldColumnExactSlope

/-- **MAIN DELIVERABLE #2 — Number-Field Column-Lattice Exact Slope Identity
(`column_lattice_exact_slope_nf`)**:
For ANY totally complex number field `K`, ANY good nonzero `A : HLat K` (`hG : A.Good`,
`hA0 : A.L ≠ ⊥`), and ANY partition `lam : Partition (anchorOfHLat A hG hA0).rk`, let
`H_A := anchorOfHLat A hG hA0` and `C := anchorOfColumnTensor H_A lam` (equivalently
`anchorOfConcreteLat (SchurFunctorColumnLat.ofNumberFieldHLat (toNumberFieldHLat A hG) _ lam).colLat`).
Incorporating the exact discriminant / different-ideal identity `absNorm_differentIdeal_eq_discr`:
1. `C.rk = ∏ j ∈ Finset.range lam.maxPart, Nat.choose (Module.finrank ℚ K * A.rank) (lam.colLen j)`,
2. **`C.slope = (lam.weight : ℝ) * ((A.mu + log 2 - log (Ideal.absNorm (differentIdeal ℤ (𝓞 K))) / [K : ℚ]) / 2)`**,
3. **`2 * C.slope - (lam.weight : ℝ) * log 2 + (lam.weight : ℝ) * (log (Ideal.absNorm (differentIdeal ℤ (𝓞 K))) / [K : ℚ]) = (lam.weight : ℝ) * A.mu`**,
4. **`Real.log C.covol / (C.rk : ℝ) = (lam.weight : ℝ) * (A.lcv / (2 * (A.rank : ℝ)))`** and
   `A.lcv / (A.rank : ℝ) = -A.mu - log 2 + log (Ideal.absNorm (differentIdeal ℤ (𝓞 K))) / [K : ℚ]`. -/
theorem column_lattice_exact_slope_nf {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (lam : Partition (anchorOfHLat A hG hA0).rk) :
    let H_A := anchorOfHLat A hG hA0
    let C := anchorOfColumnTensor H_A lam
    C.rk = ∏ j ∈ Finset.range lam.maxPart, Nat.choose (Module.finrank ℚ K * A.rank) (lam.colLen j) ∧
    C.slope = (lam.weight : ℝ) *
      ((A.mu + Real.log 2 -
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) ∧
    2 * C.slope - (lam.weight : ℝ) * Real.log 2 +
      (lam.weight : ℝ) *
        (Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) =
      (lam.weight : ℝ) * A.mu ∧
    Real.log C.covol / (C.rk : ℝ) = (lam.weight : ℝ) * (A.lcv / (2 * (A.rank : ℝ))) ∧
    A.lcv / (A.rank : ℝ) =
      -A.mu - Real.log 2 +
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  intro H_A C
  obtain ⟨hrk, hsl, _, hlog⟩ := q_lattice_slope_exact H_A lam
  have hrkA : H_A.rk = Module.finrank ℚ K * A.rank := anchorOfHLat_rk A hG hA0
  have hdisc := absNorm_differentIdeal_eq_discr K
  have hslA : H_A.slope =
      (A.mu + Real.log 2 -
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2 := by
    rw [anchorOfHLat_slope_eq_from_mu A hG hA0]
    unfold logDiscDivDeg
    rw [← hdisc]
  have hC_rk : C.rk =
      ∏ j ∈ Finset.range lam.maxPart, Nat.choose (Module.finrank ℚ K * A.rank) (lam.colLen j) := by
    rw [hrk]
    exact Finset.prod_congr rfl fun j _ => congrArg (fun n => Nat.choose n (lam.colLen j)) hrkA
  have hC_sl : C.slope = (lam.weight : ℝ) *
      ((A.mu + Real.log 2 -
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) := by
    rw [hsl, hslA]
  have hC_norm : 2 * C.slope - (lam.weight : ℝ) * Real.log 2 +
      (lam.weight : ℝ) *
        (Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) =
      (lam.weight : ℝ) * A.mu := by
    rw [hC_sl]; ring
  have hC_lcv : Real.log C.covol / (C.rk : ℝ) = (lam.weight : ℝ) * (A.lcv / (2 * (A.rank : ℝ))) := by
    rw [hlog, anchorOfHLat_log_covol_div_rk_eq_lcv A hG hA0]
  have hA_lcv : A.lcv / (A.rank : ℝ) =
      -A.mu - Real.log 2 +
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ) := by
    have h1 := anchorOfHLat_log_covol_div_rk_eq_lcv A hG hA0
    rw [anchor_log_covol_div_rk_eq_neg_slope H_A, hslA] at h1
    have hr : (A.rank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (anchorOfHLat_rank_pos A hG hA0).ne'
    have h2 : A.lcv / (2 * (A.rank : ℝ)) = (A.lcv / (A.rank : ℝ)) / 2 := by field_simp [hr]
    linarith
  exact ⟨hC_rk, hC_sl, hC_norm, hC_lcv, hA_lcv⟩

/-- Exact match between `anchorOfColumnTensor (anchorOfHLat A hG hA0) lam` and
`Stage14M2_WeylHookBranching.SchurFunctorColumnLat.ofNumberFieldHLat`. -/
theorem column_lattice_exact_slope_nf_schur {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (lam : Partition (rk (toNumberFieldHLat A hG).zRealize)) :
    let S := SchurFunctorColumnLat.ofNumberFieldHLat (toNumberFieldHLat A hG)
      (zRealize_ne_bot A.b A.X hG.1 hA0) lam
    ArakelovCovolume.slope S.colLat.L =
      (lam.weight : ℝ) *
        ((A.mu + Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) := by
  exact (column_lattice_exact_slope_nf A hG hA0 lam).2.1

/-- Number-field column-lattice exact slope for arbitrary integer dominant weights `w : DomWeight`. -/
theorem column_lattice_exact_slope_nf_domWeight {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (w : DomWeight (anchorOfHLat A hG hA0).rk) :
    (anchorOfDomWeight (anchorOfHLat A hG hA0) w).slope =
      (∑ i : Fin (anchorOfHLat A hG hA0).rk, (w.w i : ℝ)) *
        ((A.mu + Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) := by
  rw [(q_lattice_slope_exact_domWeight (anchorOfHLat A hG hA0) w).2,
    anchorOfHLat_slope_eq_from_mu A hG hA0]
  unfold logDiscDivDeg
  rw [← absNorm_differentIdeal_eq_discr K]

/-- Number-field column-lattice exact slope for the dual Hermitian lattice `dualHLat A`
(combining `hlat_duality_slope_neg` and `column_lattice_exact_slope_nf`). -/
theorem column_lattice_exact_slope_nf_dual {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (hDG : (dualHLat A).Good) (hD0 : (dualHLat A).L ≠ ⊥)
    (lam : Partition (anchorOfHLat (dualHLat A) hDG hD0).rk) :
    (anchorOfColumnTensor (anchorOfHLat (dualHLat A) hDG hD0) lam).slope =
      (lam.weight : ℝ) *
        ((-A.mu + Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) := by
  rw [(column_lattice_exact_slope_nf (dualHLat A) hDG hD0 lam).2.1,
    (hlat_duality_slope_neg A hG (anchorOfHLat_rank_pos A hG hA0)).1]

/-- Helper: `A.withL (𝔟 • A.L)` stays `Good` and nonzero for any nonzero ideal `𝔟 ≤ 𝓞 K`. -/
theorem withL_ideal_twist_good {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    (A.withL (𝔟 • A.L)).Good ∧ (A.withL (𝔟 • A.L)).L ≠ ⊥ := by
  have hfg : (𝔟 • A.L).FG := Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hG.2.1
  have hsp : Submodule.span K ((𝔟 • A.L : Submodule (𝓞 K) A.V) : Set A.V) = ⊤ := by
    apply le_antisymm le_top
    rw [← hG.2.2, Submodule.span_le]
    intro x hx
    obtain ⟨r, hr𝔟, hr0⟩ : ∃ r ∈ 𝔟, r ≠ 0 := by
      by_contra hall
      push Not at hall
      apply h𝔟
      rw [eq_bot_iff]
      intro r hr
      rw [Submodule.mem_bot]
      exact hall r hr
    have hrK : (algebraMap (𝓞 K) K r) ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hr0
    have hrx : r • x ∈ 𝔟 • A.L := Submodule.smul_mem_smul hr𝔟 hx
    have hsm : (algebraMap (𝓞 K) K r)⁻¹ • (r • x) ∈
        Submodule.span K ((𝔟 • A.L : Submodule (𝓞 K) A.V) : Set A.V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span hrx)
    rwa [← algebraMap_smul K r x, inv_smul_smul₀ hrK] at hsm
  have hne : 𝔟 • A.L ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.bot_coe, Submodule.span_zero_singleton] at hsp
    have hA_top : Submodule.span K (A.L : Set A.V) = ⊥ := hG.2.2.trans hsp.symm
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Submodule.span K (A.L : Set A.V) := Submodule.subset_span hx
    rwa [hA_top, Submodule.mem_bot] at hx'
  exact ⟨⟨hG.1, hfg, hsp⟩, hne⟩

/-- Exact normalized slope of an ideal-twisted `HLat K`:
`(A.withL (𝔟 • A.L)).mu = A.mu - 2 * log (Ideal.absNorm 𝔟) / [K : ℚ]`. -/
theorem mu_ideal_twist {K : Type} [Field K] [NumberField K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    (A.withL (𝔟 • A.L)).mu =
      A.mu - 2 * Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  have ⟨hG', _⟩ := withL_ideal_twist_good A hG hA0 𝔟 h𝔟
  have hrk : rkK (K := K) (𝔟 • A.L) = rkK (K := K) A.L := by
    unfold rkK
    have hsp' : Submodule.span K ((𝔟 • A.L : Submodule (𝓞 K) A.V) : Set A.V) = ⊤ := hG'.2.2
    rw [hsp', hG.2.2]
  have hidx := twist_index A.L hG.2.1 𝔟 h𝔟
  have hmu := muDef_sublattice_index A.b A.X hG.1 hG.2.1 hA0 Submodule.smul_le_right hrk
  rw [hidx, Nat.cast_pow, Real.log_pow] at hmu
  have hr_ne : (rkK (K := K) A.L : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (anchorOfHLat_rank_pos A hG hA0).ne'
  have hn_ne : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  change muDef A.b A.X (𝔟 • A.L) = muDef A.b A.X A.L - _
  rw [hmu]
  field_simp [hn_ne, hr_ne]

/-- **Ideal-Twisted Number-Field Column-Lattice Exact Slope (`column_lattice_exact_slope_nf_twist`)**:
combines `twist_index`, `muDef_sublattice_index`, and `absNorm_differentIdeal_eq_discr`. -/
theorem column_lattice_exact_slope_nf_twist {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥) (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥)
    (lam : Partition (anchorOfHLat (A.withL (𝔟 • A.L))
      (withL_ideal_twist_good A hG hA0 𝔟 h𝔟).1 (withL_ideal_twist_good A hG hA0 𝔟 h𝔟).2).rk) :
    (anchorOfColumnTensor
      (anchorOfHLat (A.withL (𝔟 • A.L))
        (withL_ideal_twist_good A hG hA0 𝔟 h𝔟).1 (withL_ideal_twist_good A hG hA0 𝔟 h𝔟).2)
      lam).slope =
    (lam.weight : ℝ) *
      ((A.mu + Real.log 2 -
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2 -
        Real.log (Ideal.absNorm 𝔟 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  rw [(column_lattice_exact_slope_nf (A.withL (𝔟 • A.L))
      (withL_ideal_twist_good A hG hA0 𝔟 h𝔟).1 (withL_ideal_twist_good A hG hA0 𝔟 h𝔟).2 lam).2.1,
    mu_ideal_twist A hG hA0 𝔟 h𝔟]
  ring

/-- **Full-Rank Congruence Sublattice Number-Field Column-Lattice Exact Slope
(`column_lattice_exact_slope_nf_sublattice`)**:
for any full-rank sublattice `L' ≤ A.L` (`hG' : (A.withL L').Good`, `hL'0 : L' ≠ ⊥`):
incorporates both `absNorm (differentIdeal ℤ (𝓞 K))` and `[A.L : L']`. -/
theorem column_lattice_exact_slope_nf_sublattice {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (L' : Submodule (𝓞 K) A.V) (hL'L : L' ≤ A.L)
    (hG' : (A.withL L').Good) (hL'0 : L' ≠ ⊥)
    (lam : Partition (anchorOfHLat (A.withL L') hG' hL'0).rk) :
    (anchorOfColumnTensor (anchorOfHLat (A.withL L') hG' hL'0) lam).slope =
      (lam.weight : ℝ) *
        ((A.mu + Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2 -
          Real.log (L'.toAddSubgroup.relIndex A.L.toAddSubgroup : ℝ) /
            ((Module.finrank ℚ K : ℝ) * (A.rank : ℝ))) := by
  have hrk : rkK (K := K) L' = rkK (K := K) A.L := by
    unfold rkK
    have hsp' : Submodule.span K (L' : Set A.V) = ⊤ := hG'.2.2
    rw [hsp', hG.2.2]
  have hmu := muDef_sublattice_index A.b A.X hG.1 hG.2.1 hA0 hL'L hrk
  rw [(column_lattice_exact_slope_nf (A.withL L') hG' hL'0 lam).2.1]
  change (lam.weight : ℝ) *
    ((muDef A.b A.X L' + Real.log 2 -
      Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) = _
  rw [hmu]
  unfold HLat.rank HLat.mu
  ring

/-- **Explicit Free Number-Field Column-Lattice Exact Slope (`column_lattice_exact_slope_nf_free`)**:
expresses the column-tensor slope purely in terms of archimedean frame determinants `‖(X v).det‖`
and the different ideal norm `Ideal.absNorm (differentIdeal ℤ (𝓞 K))`. -/
theorem column_lattice_exact_slope_nf_free {K V ι : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) :
    let A : HLat K := ⟨V, ι, b, X, Submodule.span (𝓞 K) (Set.range b)⟩
    have hG : A.Good := ⟨hX, by
      classical
      exact ⟨Finset.univ.image b, by simp [A]⟩, by
      apply le_antisymm le_top
      intro x _
      rw [← b.sum_repr x]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))⟩
    have hA0 : A.L ≠ ⊥ := by
      intro hbot
      obtain ⟨i₀⟩ := ‹Nonempty ι›
      have hi : b i₀ ∈ A.L := Submodule.subset_span ⟨i₀, rfl⟩
      rw [hbot, Submodule.mem_bot] at hi
      exact b.ne_zero i₀ hi
    ∀ (lam : Partition (anchorOfHLat A hG hA0).rk),
      (anchorOfColumnTensor (anchorOfHLat A hG hA0) lam).slope =
        (lam.weight : ℝ) *
          ((2 / ((Module.finrank ℚ K : ℝ) * (Fintype.card ι : ℝ))) *
              (∑ v : InfinitePlace K, Real.log ‖(X v).det‖) +
            (Real.log 2 -
              Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) /
                (Module.finrank ℚ K : ℝ)) / 2) := by
  intro A hG hA0 lam
  rw [(column_lattice_exact_slope_nf A hG hA0 lam).2.1]
  change (lam.weight : ℝ) *
    ((muDef b X (Submodule.span (𝓞 K) (Set.range b)) + Real.log 2 -
      Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) = _
  rw [freeHLat_mu_eq b X hX]
  ring

/-- **Direct-Sum Number-Field Column-Lattice Exact Slope (`column_lattice_exact_slope_nf_directSum`)**:
combines `directSumHLat_invariants` with `column_lattice_exact_slope_nf` for `directSumHLat A B`. -/
theorem column_lattice_exact_slope_nf_directSum {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A B : HLat K) (hA : A.Good) (hB : B.Good) (hA0 : A.L ≠ ⊥) (hB0 : B.L ≠ ⊥) :
    have hD : (directSumHLat A B).Good := directSumHLat_good A B hA hB
    have hD0 : (directSumHLat A B).L ≠ ⊥ := by
      intro hbot
      apply hA0
      rw [eq_bot_iff]
      intro a ha
      have hmem : (a, (0 : B.V)) ∈ A.L.prod B.L := ⟨ha, B.L.zero_mem⟩
      change A.L.prod B.L = ⊥ at hbot
      rw [hbot, Submodule.mem_bot] at hmem
      exact (Prod.ext_iff.mp hmem).1
    ∀ (lam : Partition (anchorOfHLat (directSumHLat A B) hD hD0).rk),
      (anchorOfColumnTensor (anchorOfHLat (directSumHLat A B) hD hD0) lam).slope =
        (lam.weight : ℝ) *
          (((A.mu * (A.rank : ℝ) + B.mu * (B.rank : ℝ)) / ((A.rank : ℝ) + (B.rank : ℝ)) +
            Real.log 2 -
            Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) := by
  intro hD hD0 lam
  have hinv := (directSumHLat_invariants A B hA hB).2.2.2.2 hA0 hB0
  have hr_pos : (0 : ℝ) < (A.rank : ℝ) + (B.rank : ℝ) := by
    have h1 := anchorOfHLat_rank_pos A hA hA0
    have h2 := anchorOfHLat_rank_pos B hB hB0
    positivity
  have hmuD : (directSumHLat A B).mu =
      (A.mu * (A.rank : ℝ) + B.mu * (B.rank : ℝ)) / ((A.rank : ℝ) + (B.rank : ℝ)) :=
    (eq_div_iff hr_pos.ne').mpr hinv.2.2
  rw [(column_lattice_exact_slope_nf (directSumHLat A B) hD hD0 lam).2.1, hmuD]

end NumberFieldColumnExactSlope

/-! ## Section 4: Weyl Hook-Length Branching Lower Bound & `lower_slope_inequality_family`
(`ConclusionF5`) -/

section ConclusionF5AndFamilyBounds

/-- Explicit Stirling hook-length penalty term
`stirlingHookPenalty lam = ∑ i : Fin r, ((ℓ_i + 1) * log (ℓ_i + 1) - ℓ_i)`
bounding `log (lam.hookProd)` from above via `hook_length_stirling_bound`. -/
def stirlingHookPenalty {r : ℕ} (lam : Partition r) : ℝ :=
  ∑ i : Fin r,
    (((lam.shiftedPart i : ℝ) + 1) * Real.log ((lam.shiftedPart i : ℝ) + 1) -
      (lam.shiftedPart i : ℝ))

theorem log_hookProd_le_stirlingHookPenalty {r : ℕ} (lam : Partition r) :
    Real.log (lam.hookProd : ℝ) ≤ stirlingHookPenalty lam :=
  (hook_length_stirling_bound lam).2.1

theorem stirlingHookPenalty_nonneg {r : ℕ} (lam : Partition r) :
    0 ≤ stirlingHookPenalty lam := by
  have h1 : (0 : ℝ) ≤ Real.log (lam.hookProd : ℝ) :=
    Real.log_nonneg (by exact_mod_cast lam.hookProd_pos)
  exact h1.trans (log_hookProd_le_stirlingHookPenalty lam)

/-- **Stirling-Sharpened Number-Field Schur-Functor Slope Lower Bound
(`schur_nf_slope_lower_stirling`)**:
Given a good nonzero `A : HLat K` over a totally complex number field `K`, a partition
`lam : Partition (anchorOfHLat A hG hA0).rk`, and a `SchurFunctorColumnLat` `S` on `A` with
semistability defect `slope S.colLat.L - muMin S.colLat.L ≤ Δ`:
combines `SchurFunctorColumnLat.slope_lower_stirling` with `column_lattice_exact_slope_nf`
(incorporating `absNorm (differentIdeal ℤ (𝓞 K))`) to bound `muMin S.schurLat.L` and
`(anchorOfConcreteLat S.schurLat).slope` from below! -/
theorem schur_nf_slope_lower_stirling {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (S : SchurFunctorColumnLat) (hbase : S.base = concreteLatOfHLat A hG hA0)
    {Δ : ℝ} (hΔ : ArakelovCovolume.slope S.colLat.L - muMin S.colLat.L ≤ Δ) :
    (S.lam.weight : ℝ) *
        ((A.mu + Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) -
        Δ - stirlingHookPenalty S.lam - Real.log S.branchConst ≤
      muMin S.schurLat.L ∧
    muMin S.schurLat.L ≤ (anchorOfConcreteLat S.schurLat).slope := by
  obtain ⟨h1, h2⟩ := S.slope_lower_stirling hΔ
  have hbase_sl : ArakelovCovolume.slope S.base.L =
      (A.mu + Real.log 2 -
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2 := by
    rw [hbase]
    change (anchorOfHLat A hG hA0).slope = _
    rw [anchorOfHLat_slope_eq_from_mu A hG hA0]
    unfold logDiscDivDeg
    rw [← absNorm_differentIdeal_eq_discr K]
  rw [hbase_sl] at h1
  exact ⟨h1, h2⟩

/-- **Coarse Elementary Number-Field Schur-Functor Slope Lower Bound
(`schur_nf_slope_lower_coarse`)**:
replaces `stirlingHookPenalty S.lam` by `|lam| * log (lam_0 + [K : ℚ] * A.rank)`. -/
theorem schur_nf_slope_lower_coarse {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A : HLat K) (hG : A.Good) (hA0 : A.L ≠ ⊥)
    (S : SchurFunctorColumnLat) (hbase : S.base = concreteLatOfHLat A hG hA0)
    {Δ : ℝ} (hΔ : ArakelovCovolume.slope S.colLat.L - muMin S.colLat.L ≤ Δ) :
    (S.lam.weight : ℝ) *
        ((A.mu + Real.log 2 -
          Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) -
        Δ - (S.lam.weight : ℝ) * Real.log ((S.lam.maxPart + Module.finrank ℚ K * A.rank : ℕ) : ℝ) -
        Real.log S.branchConst ≤
      muMin S.schurLat.L ∧
    muMin S.schurLat.L ≤ (anchorOfConcreteLat S.schurLat).slope := by
  have hres := (schur_branching_slope_lower S.base S.lam S.schurLat S.proj
    S.branchConst_pos S.proj_norm_le S.proj_full_span).2 Δ hΔ
  have hbase_rk : rk S.base.L = Module.finrank ℚ K * A.rank := by
    rw [hbase]
    exact anchorOfHLat_rk A hG hA0
  have hbase_sl : ArakelovCovolume.slope S.base.L =
      (A.mu + Real.log 2 -
        Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2 := by
    rw [hbase]
    change (anchorOfHLat A hG hA0).slope = _
    rw [anchorOfHLat_slope_eq_from_mu A hG hA0]
    unfold logDiscDivDeg
    rw [← absNorm_differentIdeal_eq_discr K]
  have hadd : (S.lam.maxPart + rk S.base.L : ℕ) = S.lam.maxPart + Module.finrank ℚ K * A.rank :=
    congrArg (S.lam.maxPart + ·) hbase_rk
  rw [hadd, hbase_sl] at hres
  exact hres

/-- **Normalized `HLat K` Schur-Functor Slope Lower Bound (`schur_nf_mu_lower_stirling`)**:
when the target Schur-functor lattice `S.schurLat` realizes a good nonzero `M : HLat K`, lifts
`schur_nf_slope_lower_stirling` directly to normalized slopes `M.muMin` and `M.mu`! -/
theorem schur_nf_mu_lower_stirling {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K]
    (A M : HLat K) (hGA : A.Good) (hA0 : A.L ≠ ⊥) (hGM : M.Good) (hM0 : M.L ≠ ⊥)
    (S : SchurFunctorColumnLat)
    (hbase : S.base = concreteLatOfHLat A hGA hA0)
    (htarg : S.schurLat = concreteLatOfHLat M hGM hM0)
    {Δ : ℝ} (hΔ : ArakelovCovolume.slope S.colLat.L - muMin S.colLat.L ≤ Δ) :
    (S.lam.weight : ℝ) * A.mu +
        ((S.lam.weight : ℝ) - 1) *
          (Real.log 2 -
            Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) -
        2 * Δ - 2 * stirlingHookPenalty S.lam - 2 * Real.log S.branchConst ≤
      M.muMin ∧
    M.muMin ≤ M.mu := by
  obtain ⟨h1, _⟩ := schur_nf_slope_lower_stirling A hGA hA0 S hbase hΔ
  have hzMin : 2 * muMin M.zRealize - Real.log 2 + logDiscDivDeg K ≤ M.muMin :=
    RHDirect.Stage14M2_HLatNumberField.zMuMin_le_muMinDef M.b M.X hGM.1 M.L hGM.2.1 hM0
  have hM_le : M.muMin ≤ M.mu :=
    (RHDirect.Stage14M2_HLatNumberField.muMinDef_le_muDef_le_muMaxDef
      M.b M.X hGM.1 M.L hGM.2.1 hM0).1
  have hS_muMin : muMin S.schurLat.L = muMin M.zRealize := by
    rw [htarg]; rfl
  rw [hS_muMin] at h1
  unfold logDiscDivDeg at hzMin
  rw [← absNorm_differentIdeal_eq_discr K] at hzMin
  exact ⟨by linarith, hM_le⟩

/-! ### Standard Fock / Weyl Gram Duality Bridge into `HLatAnchor` (`ConclusionF5`) -/

/-- Bridges `Stage14M2_WeylHookBranching.standard_slope_lower` directly into an `HLatAnchor`
slope & covolume lower bound (for lattices whose Gram matrix realizes `stdFockGram N hNorm eWeyl`). -/
theorem conclusionF5_of_standard_slope_lower
    (H : HLatAnchor) (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hNorm : ℚ) (hh : 0 < hNorm)
    (eWeyl eDual : Fin H.rk → MvPolynomial (Fin N × Fin N) ℤ)
    (hcol : ∀ i : Fin H.rk, HasColWeight N ν (eDual i))
    (hliDual : LinearIndependent ℤ eDual)
    (hdual : (stdFockGram N hNorm eWeyl).det * (stdFockGram N hNorm eDual).det = 1)
    (hcov : H.covol = ((stdFockGram N hNorm eWeyl).det : ℝ)) :
    -((∑ s : Fin N, (ν s : ℝ)) * Real.log (N : ℝ) + Real.log (cNu N ν hNorm)) ≤ H.slope ∧
    Real.log H.covol / (H.rk : ℝ) ≤
      (∑ s : Fin N, (ν s : ℝ)) * Real.log (N : ℝ) + Real.log (cNu N ν hNorm) := by
  have hμ : H.slope = -Real.log ((stdFockGram N hNorm eWeyl).det : ℝ) / (H.rk : ℝ) := by
    rw [anchor_slope_eq_neg_log_covol_div_rk H, hcov]
  have hlow := standard_slope_lower N hN ν hNorm hh (anchor_rk_pos H) eWeyl eDual hcol hliDual hdual hμ
  exact ⟨hlow, (anchor_neg_le_slope_iff_log_covol_div_rk_le H _).mp hlow⟩

/-- Hook-bound specialization of `conclusionF5_of_standard_slope_lower`. -/
theorem conclusionF5_of_standard_slope_lower_hook
    (H : HLatAnchor) (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hNorm : ℚ) (hh : 0 < hNorm)
    (eWeyl eDual : Fin H.rk → MvPolynomial (Fin N × Fin N) ℤ)
    (hcol : ∀ i : Fin H.rk, HasColWeight N ν (eDual i))
    (hliDual : LinearIndependent ℤ eDual)
    (hdual : (stdFockGram N hNorm eWeyl).det * (stdFockGram N hNorm eDual).det = 1)
    (hcov : H.covol = ((stdFockGram N hNorm eWeyl).det : ℝ))
    (hcNu_le : cNu N ν hNorm ≤ ((ν ⟨0, hN⟩ : ℝ) + (N : ℝ)) ^ (N * (N - 1) / 2)) :
    -((∑ s : Fin N, (ν s : ℝ)) * Real.log (N : ℝ) +
        ((N * (N - 1) / 2 : ℕ) : ℝ) * Real.log ((ν ⟨0, hN⟩ : ℝ) + (N : ℝ))) ≤ H.slope ∧
    Real.log H.covol / (H.rk : ℝ) ≤
      (∑ s : Fin N, (ν s : ℝ)) * Real.log (N : ℝ) +
        ((N * (N - 1) / 2 : ℕ) : ℝ) * Real.log ((ν ⟨0, hN⟩ : ℝ) + (N : ℝ)) := by
  have hμ : H.slope = -Real.log ((stdFockGram N hNorm eWeyl).det : ℝ) / (H.rk : ℝ) := by
    rw [anchor_slope_eq_neg_log_covol_div_rk H, hcov]
  have hlow := standard_slope_lower_of_hook_bound N hN ν hNorm hh (anchor_rk_pos H)
    eWeyl eDual hcol hliDual hdual hμ hcNu_le
  exact ⟨hlow, (anchor_neg_le_slope_iff_log_covol_div_rk_le H _).mp hlow⟩

/-! ### MAIN DELIVERABLE #3: `lower_slope_inequality_family` (`ConclusionF5`) &
`Stage14Contracts.M2HLatBostContract` / `M2FiberCert` Alignment -/

/-- **Direct `Stage14Contracts.M2HLatBostContract.conclusionF5_column_slope_lower` Discharge**:
for ANY family `baseLatM : ℕ → HLatAnchor`, verifies the exact `ConclusionF5` field of
`Stage14Contracts.M2HLatBostContract` verbatim. -/
theorem conclusionF5_column_slope_lower_of_anchor (baseLatM : ℕ → HLatAnchor) :
    ∀ (idx : ℕ) (cSlope nT a La m k : ℝ),
      0 ≤ cSlope → 0 ≤ nT → 0 ≤ a → 0 ≤ La → 0 ≤ m → 0 < k →
      (Real.log (baseLatM idx).covol / ((baseLatM idx).rk : ℝ) ≤
        cSlope * nT * a * La * (1 + m / k)) →
      -(cSlope * nT * a * La * (1 + m / k)) ≤ (baseLatM idx).slope := by
  intro idx cSlope nT a La m k _ _ _ _ _ _ hcov
  exact (anchor_neg_le_slope_iff_log_covol_div_rk_le (baseLatM idx) _).mpr hcov

/-- **MAIN DELIVERABLE #3 — Uniform Unconditional CM Host Family Lower Bound
(`lower_slope_inequality_family`, `ConclusionF5`)**:
Over ANY CM / totally complex number field `K` and ANY host family `A : ι → HLat K` of good nonzero
Hermitian lattices, with Schur-functor column lattices `S : ι → SchurFunctorColumnLat` rooted at
`A j` and landing in target `HLatAnchor`s `M : ι → HLatAnchor` (`M j = anchorOfConcreteLat (S j).schurLat`)
with semistability defects `Δ : ι → ℝ`:
1. Unconditionally for every `j : ι`:
   `((S j).lam.weight : ℝ) * ((A j).mu + log 2 - log (Ideal.absNorm (differentIdeal ℤ (𝓞 K))) / [K : ℚ]) / 2 - Δ j - stirlingHookPenalty (S j).lam - log (S j).branchConst ≤ muMin (M j).L ≤ (M j).slope`
   (and equivalently bounds `Real.log (M j).covol / (M j).rk` from above!),
2. Whenever the uniform host-family budget `cSlope * nT * a * La * (1 + m / k)` dominates the
   explicit Stirling + different-ideal + base-slope + defect cost at every `j : ι`, BOTH
   `-(cSlope * nT * a * La * (1 + m / k)) ≤ muMin (M j).L`,
   `-(cSlope * nT * a * La * (1 + m / k)) ≤ (M j).slope`, AND
   `Real.log (M j).covol / ((M j).rk : ℝ) ≤ cSlope * nT * a * La * (1 + m / k)`
   hold uniformly across the entire family `ι` — directly aligned with
   `Stage14Contracts.M2HLatBostContract` and `M2FiberCert.slopes`! -/
theorem lower_slope_inequality_family {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [StarRing K] {ι : Type*}
    (A : ι → HLat K) (hG : ∀ j, (A j).Good) (hA0 : ∀ j, (A j).L ≠ ⊥)
    (S : ι → SchurFunctorColumnLat)
    (hbase : ∀ j, (S j).base = concreteLatOfHLat (A j) (hG j) (hA0 j))
    (M : ι → HLatAnchor)
    (htarg : ∀ j, M j = anchorOfConcreteLat (S j).schurLat)
    (Δ : ι → ℝ)
    (hΔ : ∀ j, ArakelovCovolume.slope (S j).colLat.L - muMin (S j).colLat.L ≤ Δ j) :
    (∀ j : ι,
      ((S j).lam.weight : ℝ) *
          (((A j).mu + Real.log 2 -
            Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) -
          Δ j - stirlingHookPenalty (S j).lam - Real.log (S j).branchConst ≤
        muMin (M j).L ∧
      muMin (M j).L ≤ (M j).slope ∧
      Real.log (M j).covol / ((M j).rk : ℝ) ≤
        -((S j).lam.weight : ℝ) *
            (((A j).mu + Real.log 2 -
              Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) +
          Δ j + stirlingHookPenalty (S j).lam + Real.log (S j).branchConst) ∧
    (∀ (cSlope nT a La m k : ℝ),
      (∀ j : ι,
        -((S j).lam.weight : ℝ) *
            (((A j).mu + Real.log 2 -
              Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) +
          Δ j + stirlingHookPenalty (S j).lam + Real.log (S j).branchConst ≤
        cSlope * nT * a * La * (1 + m / k)) →
      ∀ j : ι,
        -(cSlope * nT * a * La * (1 + m / k)) ≤ muMin (M j).L ∧
        -(cSlope * nT * a * La * (1 + m / k)) ≤ (M j).slope ∧
        Real.log (M j).covol / ((M j).rk : ℝ) ≤ cSlope * nT * a * La * (1 + m / k)) := by
  have hpoint : ∀ j : ι,
      ((S j).lam.weight : ℝ) *
          (((A j).mu + Real.log 2 -
            Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) -
          Δ j - stirlingHookPenalty (S j).lam - Real.log (S j).branchConst ≤
        muMin (M j).L ∧
      muMin (M j).L ≤ (M j).slope ∧
      Real.log (M j).covol / ((M j).rk : ℝ) ≤
        -((S j).lam.weight : ℝ) *
            (((A j).mu + Real.log 2 -
              Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) +
          Δ j + stirlingHookPenalty (S j).lam + Real.log (S j).branchConst := by
    intro j
    obtain ⟨h1, h2⟩ := schur_nf_slope_lower_stirling (A j) (hG j) (hA0 j) (S j) (hbase j) (hΔ j)
    rw [htarg j]
    have hsl : ((S j).lam.weight : ℝ) *
          (((A j).mu + Real.log 2 -
            Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) -
          Δ j - stirlingHookPenalty (S j).lam - Real.log (S j).branchConst ≤
        (anchorOfConcreteLat (S j).schurLat).slope := h1.trans h2
    have hcov : Real.log (anchorOfConcreteLat (S j).schurLat).covol /
          ((anchorOfConcreteLat (S j).schurLat).rk : ℝ) ≤
        -((S j).lam.weight : ℝ) *
            (((A j).mu + Real.log 2 -
              Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) / (Module.finrank ℚ K : ℝ)) / 2) +
          Δ j + stirlingHookPenalty (S j).lam + Real.log (S j).branchConst := by
      rw [anchor_log_covol_div_rk_eq_neg_slope (anchorOfConcreteLat (S j).schurLat)]
      linarith
    exact ⟨h1, h2, hcov⟩
  refine ⟨hpoint, fun cSlope nT a La m k hbud j => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hpoint j
  have hbj := hbud j
  refine ⟨by linarith, by linarith, h3.trans hbj⟩

/-- **Stirling-Sharpened `CMHermLattice` Family `ConclusionF5` (`lower_slope_inequality_cmHerm_family`)**:
uniform unconditional lower bound across any family of arbitrary-rank CM Hermitian lattices
`Λ : ι → CMHermLattice d r` (with explicit discriminant `d`, determinant `det (Λ j).H`, and
Stirling hook-length penalty `stirlingHookPenalty`), aligned with `HLatAnchor`. -/
theorem lower_slope_inequality_cmHerm_family {ι : Type*} (d r : ℕ)
    (Λ : ι → CMHermLattice d r)
    (S : ι → SchurFunctorColumnLat)
    (hbase : ∀ j, (S j).base = SchurFunctorColumnLat.concreteLatOfCMHerm (Λ j))
    (M : ι → HLatAnchor)
    (htarg : ∀ j, M j = anchorOfConcreteLat (S j).schurLat)
    (Δ : ι → ℝ)
    (hΔ : ∀ j, ArakelovCovolume.slope (S j).colLat.L - muMin (S j).colLat.L ≤ Δ j) :
    ∀ j : ι,
      ((S j).lam.weight : ℝ) *
          (-(1 / 4) * Real.log (d : ℝ) - Real.log (Λ j).H.det.re / (2 * (r : ℝ))) -
        Δ j - stirlingHookPenalty (S j).lam - Real.log (S j).branchConst ≤
      muMin (M j).L ∧
    muMin (M j).L ≤ (M j).slope ∧
    Real.log (M j).covol / ((M j).rk : ℝ) ≤
      ((S j).lam.weight : ℝ) *
          ((1 / 4) * Real.log (d : ℝ) + Real.log (Λ j).H.det.re / (2 * (r : ℝ))) +
        Δ j + stirlingHookPenalty (S j).lam + Real.log (S j).branchConst := by
  intro j
  obtain ⟨h1, h2⟩ := (S j).slope_lower_stirling (hΔ j)
  have hbase_sl : ArakelovCovolume.slope (S j).base.L =
      -(1 / 4) * Real.log (d : ℝ) - Real.log (Λ j).H.det.re / (2 * (r : ℝ)) := by
    rw [hbase j]
    exact (Λ j).slope_eq
  rw [hbase_sl] at h1
  rw [htarg j]
  have hcov : Real.log (anchorOfConcreteLat (S j).schurLat).covol /
        ((anchorOfConcreteLat (S j).schurLat).rk : ℝ) ≤
      ((S j).lam.weight : ℝ) *
          ((1 / 4) * Real.log (d : ℝ) + Real.log (Λ j).H.det.re / (2 * (r : ℝ))) +
        Δ j + stirlingHookPenalty (S j).lam + Real.log (S j).branchConst := by
    rw [anchor_log_covol_div_rk_eq_neg_slope (anchorOfConcreteLat (S j).schurLat)]
    unfold stirlingHookPenalty
    change -(ArakelovCovolume.slope (S j).schurLat.L) ≤ _
    linarith
  exact ⟨h1, h2, hcov⟩

/-- **Wave-3 Fiber Compiler Bridge (`conclusionF5_fiber_slopes_lower`)**:
directly discharges the lower-bound half of `Stage14Contracts.M2FiberCert.slopes`:
`-(F.cSlope * #F.Top * F.a * F.La * (1 + F.R.m / F.R.k)) ≤ F.muM u0 u`
on any `Field2FiberShell` from a family of `HLatAnchor`s `M u0 u` whose slopes satisfy
`M u0 u ≤ F.muM u0 u` and whose log-covolume/rank ratios are bounded by the `ConclusionF5`
budget! -/
theorem conclusionF5_fiber_slopes_lower
    {ψ : PChar} {eL K cHH eps x : ℝ} {q d_aux e_page : ℕ}
    {hx1 : 1 < x} {heps : 0 < eps} {heps52 : eps < 1 / 52}
    (F : Field2FiberShell ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)
    (M : ∀ u0, F.W u0 → HLatAnchor)
    (hmuM : ∀ u0 (u : F.W u0), (M u0 u).slope ≤ F.muM u0 u)
    (hcov : ∀ u0 (u : F.W u0),
      Real.log (M u0 u).covol / ((M u0 u).rk : ℝ) ≤
        F.cSlope * (Fintype.card F.Top : ℝ) * F.a * F.La * (1 + (F.R.m : ℝ) / (F.R.k : ℝ))) :
    ∀ u0 (u : F.W u0),
      -(F.cSlope * (Fintype.card F.Top : ℝ) * F.a * F.La * (1 + (F.R.m : ℝ) / (F.R.k : ℝ))) ≤
        F.muM u0 u := by
  intro u0 u
  have h1 := (anchor_neg_le_slope_iff_log_covol_div_rk_le (M u0 u) _).mpr (hcov u0 u)
  exact h1.trans (hmuM u0 u)

/-- **Wave-3 Direct CM-Host-to-Fiber `ConclusionF5` Bridge (`conclusionF5_fiber_of_nf_branching`)**:
composes `lower_slope_inequality_family` directly into `Stage14Contracts.M2FiberCert.slopes.1`
for a `Field2FiberShell` whose automorphic lattices `M u0 u` arise via Weyl hook-length branching
from a CM number-field host family `A u0 u : HLat E_K`! -/
theorem conclusionF5_fiber_of_nf_branching
    {ψ : PChar} {eL K_c cHH eps x : ℝ} {q d_aux e_page : ℕ}
    {hx1 : 1 < x} {heps : 0 < eps} {heps52 : eps < 1 / 52}
    (F : Field2FiberShell ψ eL K_c cHH eps x q d_aux e_page hx1 heps heps52)
    {E_K : Type} [Field E_K] [NumberField E_K] [IsTotallyComplex E_K] [StarRing E_K]
    (A : ∀ u0, F.W u0 → HLat E_K)
    (hG : ∀ u0 u, (A u0 u).Good) (hA0 : ∀ u0 u, (A u0 u).L ≠ ⊥)
    (S : ∀ u0, F.W u0 → SchurFunctorColumnLat)
    (hbase : ∀ u0 u, (S u0 u).base = concreteLatOfHLat (A u0 u) (hG u0 u) (hA0 u0 u))
    (M : ∀ u0, F.W u0 → HLatAnchor)
    (htarg : ∀ u0 u, M u0 u = anchorOfConcreteLat (S u0 u).schurLat)
    (Δ : ∀ u0, F.W u0 → ℝ)
    (hΔ : ∀ u0 u, ArakelovCovolume.slope (S u0 u).colLat.L - muMin (S u0 u).colLat.L ≤ Δ u0 u)
    (hmuM : ∀ u0 u, (M u0 u).slope ≤ F.muM u0 u)
    (hbud : ∀ u0 u,
      -((S u0 u).lam.weight : ℝ) *
          (((A u0 u).mu + Real.log 2 -
            Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 E_K)) : ℝ) /
              (Module.finrank ℚ E_K : ℝ)) / 2) +
        Δ u0 u + stirlingHookPenalty (S u0 u).lam + Real.log (S u0 u).branchConst ≤
      F.cSlope * (Fintype.card F.Top : ℝ) * F.a * F.La * (1 + (F.R.m : ℝ) / (F.R.k : ℝ))) :
    ∀ u0 (u : F.W u0),
      -(F.cSlope * (Fintype.card F.Top : ℝ) * F.a * F.La * (1 + (F.R.m : ℝ) / (F.R.k : ℝ))) ≤
        F.muM u0 u := by
  intro u0 u
  have hfam := (lower_slope_inequality_family
    (ι := Σ u0' : F.U0, F.W u0')
    (fun p => A p.1 p.2) (fun p => hG p.1 p.2) (fun p => hA0 p.1 p.2)
    (fun p => S p.1 p.2) (fun p => hbase p.1 p.2)
    (fun p => M p.1 p.2) (fun p => htarg p.1 p.2)
    (fun p => Δ p.1 p.2) (fun p => hΔ p.1 p.2)).2
    F.cSlope (Fintype.card F.Top : ℝ) F.a F.La (F.R.m : ℝ) (F.R.k : ℝ)
    (fun p => hbud p.1 p.2) ⟨u0, u⟩
  exact hfam.2.1.trans (hmuM u0 u)

/-! ### 0-Assumption Concrete CM Column-Lattice Family Instantiation -/

/-- Concrete 0-assumption family of CM column-tensor `HLatAnchor`s built from
`CMHermLattice.std d r` and arbitrary partitions `lam : ℕ → Partition (2 * r)`. -/
def concreteCMColumnFamily (d r : ℕ) (hd : 0 < d) (hr : 1 ≤ r)
    (lam : ℕ → Partition (2 * r)) : ℕ → HLatAnchor :=
  fun idx =>
    anchorOfConcreteLat
      (SchurFunctorColumnLat.ofCMHermLattice (CMHermLattice.std d r hd hr) (lam idx)).colLat

/-- Exact unconditional slope & `ConclusionF5` theorem for `concreteCMColumnFamily`:
0 open assumptions, directly verifying non-vacuousness of `M2HLatBostContract.conclusionF5_column_slope_lower`! -/
theorem concreteCMColumnFamily_exact_slope_and_F5 (d r : ℕ) (hd : 0 < d) (hr : 1 ≤ r)
    (lam : ℕ → Partition (2 * r)) (idx : ℕ) :
    (concreteCMColumnFamily d r hd hr lam idx).slope =
      -((lam idx).weight : ℝ) * ((1 / 4) * Real.log (d : ℝ)) ∧
    Real.log (concreteCMColumnFamily d r hd hr lam idx).covol /
        ((concreteCMColumnFamily d r hd hr lam idx).rk : ℝ) =
      ((lam idx).weight : ℝ) * ((1 / 4) * Real.log (d : ℝ)) ∧
    ∀ (cSlope nT a La m k : ℝ),
      ((lam idx).weight : ℝ) * ((1 / 4) * Real.log (d : ℝ)) ≤
        cSlope * nT * a * La * (1 + m / k) →
      -(cSlope * nT * a * La * (1 + m / k)) ≤
        (concreteCMColumnFamily d r hd hr lam idx).slope := by
  have hsl : (concreteCMColumnFamily d r hd hr lam idx).slope =
      -((lam idx).weight : ℝ) * ((1 / 4) * Real.log (d : ℝ)) := by
    change ArakelovCovolume.slope
      (SchurFunctorColumnLat.ofCMHermLattice (CMHermLattice.std d r hd hr) (lam idx)).colLat.L = _
    rw [SchurFunctorColumnLat.colLat_slope_ofCMHermLattice]
    have hdet : (CMHermLattice.std d r hd hr).H.det.re = 1 := by
      simp [CMHermLattice.std]
    rw [hdet, Real.log_one, zero_div, sub_zero]
    ring
  have hlog : Real.log (concreteCMColumnFamily d r hd hr lam idx).covol /
        ((concreteCMColumnFamily d r hd hr lam idx).rk : ℝ) =
      ((lam idx).weight : ℝ) * ((1 / 4) * Real.log (d : ℝ)) := by
    rw [anchor_log_covol_div_rk_eq_neg_slope (concreteCMColumnFamily d r hd hr lam idx), hsl]
    ring
  refine ⟨hsl, hlog, fun cSlope nT a La m k hle => ?_⟩
  rw [hsl]
  linarith

end ConclusionF5AndFamilyBounds

end RHDirect.Stage14M2_ColumnExactSlope

end
