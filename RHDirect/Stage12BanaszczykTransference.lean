import RHDirect.Stage10GeometryOfNumbers
import RHDirect.Stage11BostDworkSqueeze
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# RHDirect.Stage12BanaszczykTransference

Unconditional, zero-`sorry`, zero-custom-`axiom`, zero-`native_decide` Lean 4 formalization of
**Banaszczyk's Transference Theorem (1993)** and its sharp `O(log n)` Arakelov slope-gap bridge
(exponentially beating LLL's `O(n)` defect) in pure Mathlib `v4.33.1`:

1. **Euclidean Dual Lattice (`dualLattice`), Discrete Lattice Gaussian Mass (`rho`, `rhoShift`)
   & Exact Multidimensional Poisson Summation**:
   - `dualLattice Λ := { y | ∀ x ∈ Λ, ∃ k : ℤ, inner ℝ x y = (k : ℝ) }`, proved equal to
     `Stage4ArakelovBost.dualLat Λ` for full-rank lattices `[DiscreteTopology Λ] [IsZLattice ℝ Λ]`,
     with `DiscreteTopology (dualLattice Λ)`, `IsZLattice ℝ (dualLattice Λ)`, double duality
     `dualLattice (dualLattice Λ) = Λ`, and `ZLattice.covolume (dualLattice Λ) = (ZLattice.covolume Λ)⁻¹`.
   - `rho s Λ := ∑' v : Λ, Real.exp (-Real.pi * ‖(v : E)‖^2 / s^2)` and
     `rhoShift s Λ u := ∑' v : Λ, Real.exp (-Real.pi * ‖(v : E) - u‖^2 / s^2)` with
     `summable_rho`, `summable_rhoShift`, `rho_pos`, `rhoShift_pos`.
   - **Exact Multidimensional Poisson Summation (`rhoShift_poisson_summation`, `rho_poisson_summation`)**:
     * `rhoShift s Λ u = (s ^ n / ZLattice.covolume Λ volume) * ∑' w : dualLattice Λ, Real.cos (2 * π * ⟪w, u⟫) * Real.exp (-π * s^2 * ‖w‖^2)`
     * `rho s Λ = (s ^ n / ZLattice.covolume Λ volume) * rho (1 / s) (dualLattice Λ)`
     * `rhoShift_le_rho`: `rhoShift s Λ u ≤ rho s Λ`
     * `rho_le_scale_mul_rho`: `0 < s₁ ≤ s₂ → rho s₂ Λ ≤ (s₂ / s₁) ^ n * rho s₁ Λ`.

2. **Unconditional Banaszczyk Gaussian Tail Bounds (1993, Lemma 1.5)**:
   - Exact Banaszczyk constant `banaszczykConst c := c * √(2 * π * e) * exp(-π * c^2) < 1` for
     every `c > 1 / √(2 * π)`, with `banaszczykConst 1 ≤ 1 / 2`.
   - **`banaszczyk_tail_bound_shift_exact`** & **`banaszczyk_tail_bound_exact`**: for all `n ≥ 1`,
     `s > 0`, `c > 1 / √(2 * π)`, and `u : E`:
     `∑' v : {v : Λ // c * √n * s < ‖(v : E) - u‖}, exp(-π ‖v - u‖^2 / s^2) ≤ (banaszczykConst c)^n * rho s Λ`.
   - **`banaszczyk_tail_bound`** & **`banaszczyk_tail_bound_shift`** (at `r = √n`, valid for all `n`):
     `∑' v : {v : Λ // √n < ‖(v : E) - u‖}, exp(-π ‖v - u‖^2) ≤ 2^(-n) * rho 1 Λ`.

3. **Unconditional Banaszczyk Transference Theorems (1993, Theorems 2.1 & 2.2)**:
   - **`banaszczyk_transference_key`**: for any `lam > 0` and `u : E` pairing integrally with all
     `y ∈ dualLattice Λ` of norm `< lam`, `∃ v ∈ Λ, ‖u - v‖ * lam ≤ n / 2`.
   - **`banaszczyk_covering_radius`**: `coveringRadius Λ * shortestNorm (dualLattice Λ) ≤ n / 2`
     (and `coveringRadius Λ * lambda1 (dualLattice Λ) ≤ n / 2`).
   - **`banaszczyk_transference_general`**: for every `i : Fin n`,
     `λ_{i+1}(Λ) * λ_{n-i}(Λ*) ≤ n` (both for `Stage10GeometryOfNumbers.successiveMinimum` and
     for arbitrary discrete lattices `L ⊂ E` via `Stage2SiegelReduction.succMin`!).
   - **`banaszczyk_transference_lambda1_lambdan`**: `1 ≤ λ₁(Λ) * λₙ(Λ*) ≤ n`.

4. **Direct `O(log n)` Arakelov Slope-Gap Bridge (`Stage10GeometryOfNumbers` + `Stage11BostDworkSqueeze`)**:
   - Exact `O(log r)` `muMin`–`λ_r` equivalence (`-log λ_r(L) ≤ muMin L ≤ -log λ_r(L) + log r`).
   - Exact `O(log r)` slope-gap and dual-slope-sum bounds:
     `muMax L + muMax (dualLat L) ≤ -log (λ₁(L) * λ₁(L*)) + log r`,
     `muMax L - slope L ≤ -log (λ₁(L) * λ₁(L*)) + log r`,
     yielding **`muMax L - slope L ≤ log r`** and **`muMax L + muMax (dualLat L) ≤ log r`**
     whenever `1 ≤ λ₁(L) * λ₁(L*)` — exponentially improving LLL's `O(r)` defect to `O(log r)`!
   - Covering-radius slope bounds (`coveringRadius Λ ≤ (n / 2) * exp (muMax (dualLattice Λ))`,
     `coveringRadius Λ ≤ (n / 2) * λₙ(Λ)`), average dual log-minima bound, and direct
     `hhBanaszczyk` / `hhBound_of_banaszczyk_transference` wiring into `Stage11BostDworkSqueeze`.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Module Submodule Finset Real Set Filter
open scoped BigOperators ENNReal Pointwise Matrix InnerProductSpace Real

namespace RHDirect.Stage12BanaszczykTransference

open RHDirect.ArakelovCovolume (rk covol degAr slopes muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram finrank_int_eq_finrank_real_span
  covol_pos rk_pos_of_ne_bot slope_le_muMax bost_slope_inequality)

open RHDirect.Stage2SiegelReduction (lambda1 lambda1_pos lambda1_le_norm
  succMin succMin_mono succMin_zero_eq_lambda1 succMin_pos)

open RHDirect.Stage4ArakelovBost (dualLat discreteTopology_dualLat rk_dualLat covol_dualLat
  degAr_dualLat slope_dualLat span_real_dualLat dualLat_dualLat
  muMin muMin_le_slope_le_muMax muMax_dualLat muMin_dualLat
  muMin_dual_lambda1_bounds neg_log_succMin_last_le_muMin
  one_le_lambda1_dualLat_mul_succMin_last)

open RHDirect.Stage10GeometryOfNumbers (basisOfZLattice covolume_eq_abs_det
  lattice_inter_closedBall_finite shortestNorm exists_shortest_nonzero_vector
  shortestNorm_eq_of_min successiveMinimum successiveMinimum_pos successiveMinimum_mono
  successiveMinimum_closedBall_zero_eq_shortestNorm)

open RHDirect.Stage11BostDworkSqueeze (covol_eq_zlattice_covolume_euclidean
  succMin_eq_stage10_successiveMinimum)

/-! ## Section 1: Euclidean Dual Lattice, Exact Covolume & Haar Scalar Factor -/

section DualLatticeBasics

/-- The **dual lattice** `Λ* = { y ∈ ℝ^n | ∀ x ∈ Λ, ⟪x, y⟫ ∈ ℤ }` of a lattice
`Λ ⊂ EuclideanSpace ℝ (Fin n)`. -/
def dualLattice {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    Submodule ℤ (EuclideanSpace ℝ (Fin n)) where
  carrier := { y | ∀ x ∈ Λ, ∃ k : ℤ, inner ℝ x y = (k : ℝ) }
  add_mem' := by
    intro y₁ y₂ hy₁ hy₂ x hx
    obtain ⟨k₁, hk₁⟩ := hy₁ x hx
    obtain ⟨k₂, hk₂⟩ := hy₂ x hx
    exact ⟨k₁ + k₂, by rw [inner_add_right, hk₁, hk₂, Int.cast_add]⟩
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨k, hk⟩ := hy x hx
    exact ⟨c * k, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hk, Int.cast_mul]⟩

lemma mem_dualLattice {n : ℕ} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))}
    {y : EuclideanSpace ℝ (Fin n)} :
    y ∈ dualLattice Λ ↔ ∀ x ∈ Λ, ∃ k : ℤ, inner ℝ x y = (k : ℝ) :=
  Iff.rfl

/-- For any full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, `dualLattice Λ` coincides verbatim
with `Stage4ArakelovBost.dualLat Λ`. -/
theorem dualLattice_eq_dualLat {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    dualLattice Λ = dualLat Λ := by
  ext y
  simp only [mem_dualLattice, dualLat, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, IsZLattice.span_top, Submodule.mem_top, true_and]
  constructor
  · intro hy x hx
    obtain ⟨k, hk⟩ := hy x hx
    exact ⟨k, by rw [real_inner_comm]; exact hk⟩
  · intro hy x hx
    obtain ⟨k, hk⟩ := hy x hx
    exact ⟨k, by rw [real_inner_comm]; exact hk⟩

instance instDiscreteTopologyDualLattice {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    DiscreteTopology (dualLattice Λ) := by
  rw [dualLattice_eq_dualLat Λ]
  exact discreteTopology_dualLat Λ

instance instIsZLatticeDualLattice {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    IsZLattice ℝ (dualLattice Λ) := by
  constructor
  rw [dualLattice_eq_dualLat Λ, span_real_dualLat Λ, IsZLattice.span_top]

/-- Double duality for full-rank Euclidean lattices: `(Λ*)* = Λ`. -/
theorem dualLattice_dualLattice {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    dualLattice (dualLattice Λ) = Λ := by
  rw [dualLattice_eq_dualLat (dualLattice Λ), dualLattice_eq_dualLat Λ, dualLat_dualLat Λ]

/-- Exact dual covolume formula: `ZLattice.covolume (dualLattice Λ) = (ZLattice.covolume Λ)⁻¹`. -/
theorem covolume_dualLattice {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ZLattice.covolume (dualLattice Λ) volume = (ZLattice.covolume Λ volume)⁻¹ := by
  rw [← covol_eq_zlattice_covolume_euclidean (dualLattice Λ),
    ← covol_eq_zlattice_covolume_euclidean Λ,
    dualLattice_eq_dualLat Λ, covol_dualLat Λ]

/-- Coordinate isomorphism `φ : ℝ^n ≃L[ℝ] (Fin n → ℝ)` induced by a `ℤ`-basis of `Λ`, together
with explicit bijections `(Fin n → ℤ) ≃ Λ`, `(Fin n → ℤ) ≃ dualLattice Λ`, and the **exact**
pushforward Haar measure identity `Measure.map φ.symm volume = (covol Λ)⁻¹ • volume`. -/
private theorem exists_coords_dualLattice_exact {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ))
      (B : (Fin n → ℤ) ≃ Λ)
      (D : (Fin n → ℤ) ≃ dualLattice Λ),
      (∀ k, ((B k : Λ) : EuclideanSpace ℝ (Fin n)) = φ.symm (fun i => (k i : ℝ))) ∧
      (∀ m x, inner ℝ ((D m : dualLattice Λ) : EuclideanSpace ℝ (Fin n)) x =
        ∑ i : Fin n, (m i : ℝ) * φ x i) ∧
      Measure.map φ.symm volume =
        Real.toNNReal (ZLattice.covolume Λ volume)⁻¹ •
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let b : Basis (Fin n) ℤ Λ := basisOfZLattice Λ
  let bR : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := b.ofZLatticeBasis ℝ
  let φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := bR.equivFun.toContinuousLinearEquiv
  have hφ : ∀ x i, φ x i = bR.repr x i := fun _ _ => rfl
  let d : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (LinearMap.toContinuousLinearMap (bR.coord i))
  have hd : ∀ i x, inner ℝ (d i) x = φ x i := fun i x => by
    simp [d, hφ, InnerProductSpace.toDual_symm_apply, Basis.coord_apply]
  let y : (Fin n → ℤ) → EuclideanSpace ℝ (Fin n) := fun m => ∑ i : Fin n, (m i : ℝ) • d i
  have hy : ∀ m x, inner ℝ (y m) x = ∑ i : Fin n, (m i : ℝ) * φ x i := fun m x => by
    simp [y, sum_inner, real_inner_smul_left, hd]
  have hφΛ : ∀ (x : Λ) i, φ (x : EuclideanSpace ℝ (Fin n)) i = (b.repr x i : ℝ) := fun x i => by
    rw [hφ, Basis.ofZLatticeBasis_repr_apply]
  have hmem : ∀ m, y m ∈ dualLattice Λ := by
    intro m x hx
    refine ⟨∑ i : Fin n, m i * b.repr ⟨x, hx⟩ i, ?_⟩
    rw [real_inner_comm, hy]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφΛ ⟨x, hx⟩ i]
  have hφb : ∀ j, φ (bR j) = Pi.single j 1 := by
    intro j; funext i
    rw [hφ, Basis.repr_self]
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hinj : Function.Injective y := by
    intro m m' h; funext j
    have h2 := congrArg (fun z => inner ℝ z (bR j)) h
    simp only [hy, hφb, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h2
    exact_mod_cast h2
  have hsurj : ∀ z ∈ dualLattice Λ, ∃ m, y m = z := by
    intro z hz
    have hbΛ : ∀ j, bR j ∈ Λ := fun j => by
      rw [Basis.ofZLatticeBasis_apply]; exact (b j).2
    choose m hm using fun j => hz (bR j) (hbΛ j)
    refine ⟨m, ?_⟩
    apply InnerProductSpace.ext_inner_left_basis bR
    intro j
    rw [real_inner_comm, hy, hφb]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    exact (hm j).symm
  let D : (Fin n → ℤ) ≃ dualLattice Λ :=
    Equiv.ofBijective (fun m => ⟨y m, hmem m⟩)
      ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun z => by
        obtain ⟨m, hm⟩ := hsurj z.1 z.2
        exact ⟨m, Subtype.ext hm⟩⟩
  refine ⟨φ, b.equivFun.symm.toEquiv, D, ?_, hy, ?_⟩
  · intro k
    apply φ.injective
    rw [φ.apply_symm_apply]
    funext i
    rw [hφΛ]
    have h3 := congr_fun (b.equivFun.apply_symm_apply k) i
    simp only [Basis.equivFun_apply] at h3
    exact_mod_cast h3
  · -- Compute the exact Haar scalar factor by evaluating on `F = ZSpan.fundamentalDomain bR`.
    have : (Measure.map φ.symm volume).IsAddHaarMeasure := φ.symm.isAddHaarMeasure_map _
    set ν : Measure (EuclideanSpace ℝ (Fin n)) := Measure.map φ.symm volume
    have hν := Measure.isAddLeftInvariant_eq_smul ν (volume : Measure (EuclideanSpace ℝ (Fin n)))
    set c : NNReal := ν.addHaarScalarFactor volume
    let F : Set (EuclideanSpace ℝ (Fin n)) := ZSpan.fundamentalDomain bR
    have hfund : IsAddFundamentalDomain Λ.toAddSubgroup F volume := ZLattice.isAddFundamentalDomain b volume
    have hF_meas : MeasurableSet F := ZSpan.fundamentalDomain_measurableSet bR
    have hF_ne_top : volume F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded bR).measure_lt_top.ne
    have hvolF : volume F = ENNReal.ofReal (ZLattice.covolume Λ volume) := by
      rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hfund, Measure.real,
        ENNReal.ofReal_toReal hF_ne_top]
    have hpre : φ.symm ⁻¹' F = Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
      ext s
      simp only [Set.mem_preimage, F, ZSpan.mem_fundamentalDomain, Set.mem_univ_pi, Set.mem_Ico]
      refine forall_congr' fun i => ?_
      have hrep : bR.repr (φ.symm s) i = s i := by
        have := congr_fun (φ.apply_symm_apply s) i
        simpa [hφ] using this
      rw [hrep]
    have hνF : ν F = 1 := by
      rw [Measure.map_apply φ.symm.continuous.measurable hF_meas, hpre,
        MeasureTheory.volume_pi, Measure.pi_pi]
      simp [Real.volume_Ico]
    have hνF' : ν F = (c : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) := by
      rw [hν, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hvolF]
    have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
    have hc_real : (c : ℝ) * ZLattice.covolume Λ volume = 1 := by
      have h1 : ((c : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume)).toReal = 1 := by
        rw [← hνF', hνF, ENNReal.toReal_one]
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hcov_pos.le] at h1
      exact h1
    have hc_eq : c = Real.toNNReal (ZLattice.covolume Λ volume)⁻¹ := by
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr hcov_pos.le)]
      exact eq_inv_of_mul_eq_one_left hc_real
    rw [hν, hc_eq]

end DualLatticeBasics

/-! ## Section 2: Discrete Lattice Gaussian Mass & Exact Multidimensional Poisson Summation -/

section DiscreteGaussianAndPoisson

/-- **Discrete lattice Gaussian mass** `ρ_s(Λ) := ∑_{v ∈ Λ} exp(-π ‖v‖² / s²)`. -/
def rho {n : ℕ} (s : ℝ) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∑' v : Λ, Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2)

/-- **Shifted discrete lattice Gaussian mass**
`ρ_s(Λ - u) := ∑_{v ∈ Λ} exp(-π ‖v - u‖² / s²)`. -/
def rhoShift {n : ℕ} (s : ℝ) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑' v : Λ, Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2)

/-- General Gaussian summability over any discrete lattice `L ⊂ E`. -/
theorem summable_exp_neg_mul_norm_add_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a)
    (w : E) : Summable fun z : L => Real.exp (-a * ‖(z : E) + w‖ ^ 2) := by
  classical
  set N : ℕ := Module.finrank ℤ L + 1 with hN
  have hr : (-(N : ℝ)) < -(Module.finrank ℤ L : ℝ) := by
    rw [hN]; push_cast; linarith
  have hs := ZLattice.summable_norm_sub_rpow L (-(N : ℝ)) hr (-w)
  set C : ℝ := max 1 ((N.factorial : ℝ) / a ^ N)
  have key : ∀ u : ℝ, 0 < u → Real.exp (-a * u ^ 2) ≤ C * u ^ (-(N : ℝ)) := by
    intro u hu
    rw [Real.rpow_neg hu.le, Real.rpow_natCast]
    rcases le_or_gt u 1 with h1 | h1
    · have h2 : 1 ≤ (u ^ N)⁻¹ := (one_le_inv₀ (pow_pos hu N)).2 (pow_le_one₀ hu.le h1)
      have h3 : Real.exp (-a * u ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
      calc Real.exp (-a * u ^ 2) ≤ 1 := h3
        _ ≤ 1 * (u ^ N)⁻¹ := by linarith
        _ ≤ C * (u ^ N)⁻¹ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · have h2 : (a * u) ^ N / (N.factorial : ℝ) ≤ Real.exp (a * u) :=
        Real.pow_div_factorial_le_exp _ (by positivity) N
      have h3 : Real.exp (a * u) ≤ Real.exp (a * u ^ 2) := Real.exp_le_exp.2 (by
        have hu2 : u ≤ u ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hu2 ha.le)
      rw [show -a * u ^ 2 = -(a * u ^ 2) by ring, Real.exp_neg]
      have hpos : 0 < (a * u) ^ N / (N.factorial : ℝ) := by positivity
      calc (Real.exp (a * u ^ 2))⁻¹ ≤ ((a * u) ^ N / (N.factorial : ℝ))⁻¹ :=
            inv_anti₀ hpos (h2.trans h3)
        _ = ((N.factorial : ℝ) / a ^ N) * (u ^ N)⁻¹ := by rw [mul_pow]; field_simp
        _ ≤ C * (u ^ N)⁻¹ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
    (f := fun z : L => C * ‖(z : E) - -w‖ ^ (-(N : ℝ)) + (if (z : E) + w = 0 then 1 else 0)) ?_ ?_
  · intro z
    by_cases hz : (z : E) + w = 0
    · simp [hz]
    · have hu : 0 < ‖(z : E) + w‖ := norm_pos_iff.2 hz
      simp only [hz, if_false, add_zero, sub_neg_eq_add]
      exact key _ hu
  · refine (hs.mul_left C).add ?_
    apply summable_of_hasFiniteSupport
    apply Set.Subsingleton.finite
    intro z1 h1 z2 h2
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at h1 h2
    apply Subtype.ext
    rw [eq_neg_of_add_eq_zero_left h1, eq_neg_of_add_eq_zero_left h2]

theorem summable_rhoShift {n : ℕ} {s : ℝ} (hs : 0 < s)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ]
    (u : EuclideanSpace ℝ (Fin n)) :
    Summable fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2) := by
  refine (summable_exp_neg_mul_norm_add_sq Λ (a := Real.pi / s ^ 2) (by positivity) (-u)).congr ?_
  intro v
  congr 1
  rw [sub_eq_add_neg]
  ring

theorem summable_rho {n : ℕ} {s : ℝ} (hs : 0 < s)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] :
    Summable fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2) := by
  simpa using summable_rhoShift hs Λ 0

lemma rhoShift_zero {n : ℕ} (s : ℝ) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    rhoShift s Λ 0 = rho s Λ := by
  simp [rhoShift, rho]

lemma one_le_rho {n : ℕ} {s : ℝ} (hs : 0 < s)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] :
    1 ≤ rho s Λ := by
  have h0 : Real.exp (-Real.pi * ‖((0 : Λ) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2) = 1 := by
    simp
  rw [← h0]
  exact (summable_rho hs Λ).le_tsum (0 : Λ) fun _ _ => (Real.exp_pos _).le

lemma rho_pos {n : ℕ} {s : ℝ} (hs : 0 < s)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] :
    0 < rho s Λ :=
  lt_of_lt_of_le zero_lt_one (one_le_rho hs Λ)

lemma rhoShift_pos {n : ℕ} {s : ℝ} (hs : 0 < s)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ]
    (u : EuclideanSpace ℝ (Fin n)) :
    0 < rhoShift s Λ u :=
  lt_of_lt_of_le (Real.exp_pos _)
    ((summable_rhoShift hs Λ u).le_tsum (0 : Λ) fun _ _ => (Real.exp_pos _).le)

lemma rhoShift_add_mem {n : ℕ} (s : ℝ) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ Λ) :
    rhoShift s Λ (u + w) = rhoShift s Λ u := by
  unfold rhoShift
  rw [← (Equiv.addRight (⟨w, hw⟩ : Λ)).tsum_eq]
  congr 1; funext v
  simp only [Equiv.coe_addRight, Submodule.coe_add]
  congr 3; abel_nf

lemma rhoShift_neg {n : ℕ} (s : ℝ) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) :
    rhoShift s Λ (-u) = rhoShift s Λ u := by
  unfold rhoShift
  rw [← (Equiv.neg Λ).tsum_eq]
  congr 1; funext v
  simp only [Equiv.neg_apply, Submodule.coe_neg]
  congr 3
  rw [← norm_neg]
  congr 1; abel_nf

lemma rho_mono {n : ℕ} {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hle : s₁ ≤ s₂)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] :
    rho s₁ Λ ≤ rho s₂ Λ := by
  have hs₂ : 0 < s₂ := lt_of_lt_of_le hs₁ hle
  refine hasSum_le (fun v => ?_) (summable_rho hs₁ Λ).hasSum (summable_rho hs₂ Λ).hasSum
  apply Real.exp_le_exp.mpr
  have hsq : s₁ ^ 2 ≤ s₂ ^ 2 := pow_le_pow_left₀ hs₁.le hle 2
  have hdiv : ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s₂ ^ 2 ≤
      ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s₁ ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hs₁ 2) hsq
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have h1 : Real.pi * (‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s₂ ^ 2) ≤
      Real.pi * (‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s₁ ^ 2) :=
    mul_le_mul_of_nonneg_left hdiv hpi
  linarith [show -Real.pi * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s₁ ^ 2 =
      -(Real.pi * (‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s₁ ^ 2)) by ring,
    show -Real.pi * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s₂ ^ 2 =
      -(Real.pi * (‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s₂ ^ 2)) by ring]

/-! ### Torus Fourier Analysis Helpers for Exact Multidimensional Poisson Summation -/

private theorem isQuotientMap_coe_unitAddTorus (ι : Type) [Fintype ι] :
    Topology.IsQuotientMap (fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) := by
  have hopen : IsOpenMap (fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)
  refine hopen.isQuotientMap (by fun_prop) ?_
  intro θ
  refine ⟨fun i => Function.surjInv QuotientAddGroup.mk_surjective (θ i), ?_⟩
  funext i
  exact Function.surjInv_eq QuotientAddGroup.mk_surjective (θ i)

private theorem exists_continuous_torus_lift_of_periodic {ι : Type} [Fintype ι]
    (G : (ι → ℝ) → ℂ) (hG : Continuous G)
    (hper : ∀ (s : ι → ℝ) (k : ι → ℤ), G (s + fun i => (k i : ℝ)) = G s) :
    ∃ F : C(UnitAddTorus ι, ℂ), ∀ s : ι → ℝ,
      F (fun i => ((s i : ℝ) : UnitAddCircle)) = G s := by
  have hq := isQuotientMap_coe_unitAddTorus ι
  have hfib : ∀ x y : ι → ℝ, (fun i => ((x i : ℝ) : UnitAddCircle)) =
      (fun i => ((y i : ℝ) : UnitAddCircle)) → G x = G y := by
    intro x y hxy
    have hk : ∀ i, ∃ k : ℤ, y i = x i + k := by
      intro i
      have h := congr_fun hxy i
      rw [QuotientAddGroup.eq] at h
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h
      refine ⟨k, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hk
      linarith
    choose k hk using hk
    have hy : y = x + fun i => (k i : ℝ) := funext hk
    rw [hy, hper]
  let F0 : UnitAddTorus ι → ℂ := fun θ => G (Function.surjInv hq.surjective θ)
  have hF0 : ∀ s : ι → ℝ, F0 (fun i => ((s i : ℝ) : UnitAddCircle)) = G s := fun s =>
    hfib _ _ (Function.surjInv_eq hq.surjective _)
  have hcont : Continuous F0 := by
    rw [hq.continuous_iff]
    have hcomp : (F0 ∘ fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) = G := funext hF0
    rw [hcomp]
    exact hG
  exact ⟨⟨F0, hcont⟩, hF0⟩

private theorem mFourierCoeff_periodization_eq_integral {ι : Type} [Fintype ι]
    (h : (ι → ℝ) → ℂ) (hh : Integrable h) (hcont : Continuous h)
    (F : C(UnitAddTorus ι, ℂ))
    (hF : ∀ s : ι → ℝ, F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : ι → ℤ, h (s + fun i => (k i : ℝ)))
    (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff F m =
      ∫ s, UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle)) * h s := by
  set ψ : (ι → ℝ) → ℂ :=
    fun s => UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle))
  have hqper : ∀ (s : ι → ℝ) (k : ι → ℤ),
      (fun i => (((s + fun i => (k i : ℝ)) i : ℝ) : UnitAddCircle)) =
        fun i => ((s i : ℝ) : UnitAddCircle) := by
    intro s k; funext i
    rw [QuotientAddGroup.eq]
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨-k i, ?_⟩
    rw [zsmul_eq_mul, mul_one, Pi.add_apply]; push_cast; ring
  have hψcont : Continuous ψ :=
    (UnitAddTorus.mFourier (-m)).continuous.comp (isQuotientMap_coe_unitAddTorus ι).continuous
  have hψle : ∀ s, ‖ψ s‖ ≤ 1 := fun s => by
    have := (UnitAddTorus.mFourier (-m)).norm_coe_le_norm (fun i => ((s i : ℝ) : UnitAddCircle))
    rwa [UnitAddTorus.mFourier_norm] at this
  set S : (ι → ℤ) → Set (ι → ℝ) := fun k => {s | ∀ i, s i ∈ Set.Ioc (k i : ℝ) (k i + 1)}
  have hSmeas : ∀ k, MeasurableSet (S k) := fun k => by
    have hS : S k = ⋂ i, (fun s : ι → ℝ => s i) ⁻¹' Set.Ioc (k i : ℝ) (k i + 1) := by
      ext s; simp [S]
    rw [hS]
    exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioc
  have hSmem : ∀ k s, s ∈ S k ↔ ∀ i, ⌈s i⌉ = k i + 1 := fun k s => by
    simp only [S, Set.mem_ofPred_eq, Set.mem_Ioc]
    refine forall_congr' fun i => ?_
    rw [Int.ceil_eq_iff]; push_cast
    exact ⟨fun ⟨h1, h2⟩ => ⟨by linarith, h2⟩, fun ⟨h1, h2⟩ => ⟨by linarith, h2⟩⟩
  have hSdisj : Pairwise (Function.onFun Disjoint S) := by
    intro k k' hne
    rw [Function.onFun, Set.disjoint_left]
    intro s h1 h2; apply hne; funext i
    have e1 := (hSmem k s).1 h1 i
    have e2 := (hSmem k' s).1 h2 i
    omega
  have hSunion : (⋃ k, S k) = Set.univ := by
    ext s; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨fun i => ⌈s i⌉ - 1, (hSmem _ s).2 fun i => by ring⟩
  have hS0 : S 0 = {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    ext s; simp [S]
  have htrans : ∀ k : ι → ℤ, (fun s => s + fun i => (k i : ℝ)) ⁻¹' S k = S 0 := by
    intro k; ext s
    simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc, Pi.add_apply, Pi.zero_apply,
      Int.cast_zero, zero_add]
    exact ⟨fun hs i => ⟨by linarith [(hs i).1], by linarith [(hs i).2]⟩,
      fun hs i => ⟨by linarith [(hs i).1], by linarith [(hs i).2]⟩⟩
  have hmp : ∀ k : ι → ℤ, MeasurePreserving (fun s : ι → ℝ => s + fun i => (k i : ℝ)) volume volume :=
    fun _ => measurePreserving_add_right volume _
  have hme : ∀ k : ι → ℤ, MeasurableEmbedding (fun s : ι → ℝ => s + fun i => (k i : ℝ)) :=
    fun _ => (Homeomorph.addRight _).measurableEmbedding
  have hfi : Integrable (fun s => ψ s * h s) := by
    refine Integrable.mono' hh.norm (hψcont.mul hcont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [norm_mul]
    calc ‖ψ s‖ * ‖h s‖ ≤ 1 * ‖h s‖ := mul_le_mul_of_nonneg_right (hψle s) (norm_nonneg _)
      _ = ‖h s‖ := one_mul _
  rw [UnitAddTorus.mFourierCoeff_eq_integral F m 0, ← hS0]
  have hint : ∀ s : ι → ℝ, UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle)) •
      F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : ι → ℤ, ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ)) := fun s => by
    rw [hF, smul_eq_mul, ← tsum_mul_left]
    congr 1; funext k; simp only [ψ, hqper]
  rw [integral_congr_ae (Filter.Eventually.of_forall hint), integral_tsum]
  · have hEach : ∀ k : ι → ℤ, ∫ s in S 0, ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ)) =
        ∫ s in S k, ψ s * h s := fun k => by
      rw [← htrans k]
      exact (hmp k).setIntegral_preimage_emb (hme k) (fun s => ψ s * h s) (S k)
    simp_rw [hEach]
    have hsum := hasSum_integral_iUnion hSmeas hSdisj hfi.integrableOn
    rw [hSunion, Measure.restrict_univ] at hsum
    exact hsum.tsum_eq
  · intro k
    exact ((hψcont.mul hcont).comp (continuous_add_const _)).aestronglyMeasurable
  · have hEach : ∀ k : ι → ℤ, ∫⁻ s in S 0,
        ‖ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ))‖ₑ =
        ∫⁻ s in S k, ‖ψ s * h s‖ₑ := fun k => by
      rw [← htrans k]
      exact (hmp k).setLIntegral_comp_preimage_emb (hme k) (fun s => ‖ψ s * h s‖ₑ) (S k)
    simp_rw [hEach]
    rw [← lintegral_iUnion hSmeas hSdisj, hSunion, Measure.restrict_univ]
    exact hfi.hasFiniteIntegral.ne

private theorem mFourier_coe_eq_exp' {ι : Type} [Fintype ι] (m : ι → ℤ) (s : ι → ℝ) :
    UnitAddTorus.mFourier m (fun i => ((s i : ℝ) : UnitAddCircle)) =
      Complex.exp (2 * π * Complex.I * ∑ i, (m i : ℂ) * (s i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

private theorem continuous_tsum_exp_neg_mul_norm_add_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {a : ℝ} (ha : 0 < a) :
    Continuous fun v : E => ∑' z : L, Real.exp (-a * ‖(z : E) + v‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro v0
  have hs := summable_exp_neg_mul_norm_add_sq L (a := a / 2) (by positivity) v0
  have hon : ContinuousOn (fun v : E => ∑' z : L, Real.exp (-a * ‖(z : E) + v‖ ^ 2))
      (Metric.ball v0 1) := by
    refine continuousOn_tsum (fun z => by fun_prop) (hs.mul_left (Real.exp a)) ?_
    intro z v hv
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : ‖(z : E) + v0‖ ≤ ‖(z : E) + v‖ + ‖v - v0‖ := by
      have hzv : (z : E) + v0 = ((z : E) + v) - (v - v0) := by abel
      rw [hzv]; exact norm_sub_le _ _
    have h2 : ‖v - v0‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hv
    have h3 := norm_nonneg ((z : E) + v)
    have h4 := norm_nonneg (v - v0)
    have h6 := norm_nonneg ((z : E) + v0)
    have h5 : ‖(z : E) + v0‖ ^ 2 ≤ 2 * ‖(z : E) + v‖ ^ 2 + 2 := by
      nlinarith [sq_nonneg (‖(z : E) + v‖ - ‖v - v0‖)]
    nlinarith [mul_le_mul_of_nonneg_left h5 ha.le]
  exact hon.continuousAt (Metric.ball_mem_nhds v0 one_pos)

/-- **Exact Multidimensional Gaussian Poisson Summation (`t`-form)**:
for every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, every `t > 0`, and every shift `v : E`:
`∑_{x ∈ Λ} exp(-π t ‖x + v‖²) = (covol Λ)⁻¹ t^{-n/2} ∑_{y ∈ Λ*} exp(-π ‖y‖² / t) cos(2π ⟪y, v⟫)`. -/
theorem poisson_summation_gaussian_exact {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (v : EuclideanSpace ℝ (Fin n)) :
    ∑' x : Λ, Real.exp (-Real.pi * t * ‖(x : EuclideanSpace ℝ (Fin n)) + v‖ ^ 2) =
      (ZLattice.covolume Λ volume)⁻¹ * t ^ (-(n : ℝ) / 2) *
        ∑' y : dualLattice Λ,
          Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / t) *
            Real.cos (2 * Real.pi * inner ℝ (y : EuclideanSpace ℝ (Fin n)) v) := by
  obtain ⟨φ, B, D, hB, hD, hν⟩ := exists_coords_dualLattice_exact Λ
  have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  -- Fourier transform of the pulled-back Gaussian with exact Haar factor `(covol Λ)⁻¹`.
  have hInt : Integrable (fun s : Fin n → ℝ =>
      (Real.exp (-Real.pi * t * ‖φ.symm s‖ ^ 2) : ℂ)) := by
    have hg : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ)) := by
      have h0 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := EuclideanSpace ℝ (Fin n)) (b := ((Real.pi * t : ℝ) : ℂ))
        (by simp; positivity) 0 (0 : EuclideanSpace ℝ (Fin n))
      refine h0.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [zero_mul, add_zero, Complex.ofReal_exp]
      congr 1; push_cast; ring
    have hgν : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ)) (Measure.map φ.symm volume) := by
      rw [hν]; exact hg.smul_measure_nnreal
    exact (integrable_map_equiv φ.symm.toHomeomorph.toMeasurableEquiv _).1 hgν
  have hG : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫ s : Fin n → ℝ, Complex.exp (-2 * π * Complex.I * (inner ℝ y (φ.symm s) : ℂ)) *
          (Real.exp (-Real.pi * t * ‖φ.symm s‖ ^ 2) : ℂ) =
        (((ZLattice.covolume Λ volume)⁻¹ * t ^ (-(n : ℝ) / 2) *
          Real.exp (-Real.pi * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
    intro y
    have step1 : ∫ s : Fin n → ℝ, Complex.exp (-2 * π * Complex.I * (inner ℝ y (φ.symm s) : ℂ)) *
          (Real.exp (-Real.pi * t * ‖φ.symm s‖ ^ 2) : ℂ) =
        ∫ x, Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
          (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ) ∂(Measure.map φ.symm volume) :=
      (integral_map_equiv φ.symm.toHomeomorph.toMeasurableEquiv
        (fun x => Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
          (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ))).symm
    rw [step1, hν, integral_smul_nnreal_measure]
    have step2 : ∀ x : EuclideanSpace ℝ (Fin n),
        Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
          (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ) =
        Complex.exp (-((Real.pi * t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2 +
          (-2 * π * Complex.I) * (inner ℝ y x : ℂ)) := fun x => by
      rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [step2]
    rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simp; positivity) _ y,
      finrank_euclideanSpace_fin]
    have e1 : ((π : ℂ) / ((π * t : ℝ) : ℂ)) ^ ((n : ℂ) / 2) =
        ((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
      rw [show ((π : ℂ) / ((π * t : ℝ) : ℂ)) = ((t⁻¹ : ℝ) : ℂ) by
        push_cast; field_simp]
      rw [show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_cpow (by positivity)]
      congr 1
      rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
      ring_nf
    have e2 : Complex.exp ((-2 * π * Complex.I) ^ 2 * (‖y‖ : ℂ) ^ 2 /
        (4 * ((π * t : ℝ) : ℂ))) = ((Real.exp (-Real.pi * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring
    rw [e1, e2, NNReal.smul_def, Complex.real_smul,
      Real.coe_toNNReal _ (inv_nonneg.mpr hcov_pos.le)]
    push_cast; ring
  have sum2 : Summable fun y : dualLattice Λ =>
      Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / t) := by
    refine (summable_exp_neg_mul_norm_add_sq (dualLattice Λ) (a := Real.pi / t)
      (by positivity) 0).congr fun z => ?_
    rw [add_zero]; ring_nf
  set P : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun w => ∑' x : Λ, Real.exp (-Real.pi * t * ‖(x : EuclideanSpace ℝ (Fin n)) + w‖ ^ 2)
  have hPcont : Continuous P := by
    refine (continuous_tsum_exp_neg_mul_norm_add_sq Λ (a := Real.pi * t)
      (by positivity)).congr fun w => ?_
    simp only [P]; congr 1; funext x; ring_nf
  have hPper : ∀ (w : EuclideanSpace ℝ (Fin n)) (z : Λ), P (w + z) = P w := by
    intro w z
    have e0 := (Equiv.addRight z).tsum_eq
      (fun x : Λ => Real.exp (-Real.pi * t * ‖(x : EuclideanSpace ℝ (Fin n)) + w‖ ^ 2))
    simp only [P]; rw [← e0]; congr 1; funext x
    simp only [Equiv.coe_addRight, Submodule.coe_add]; congr 3; abel_nf
  set G : (Fin n → ℝ) → ℂ := fun s => ((P (φ.symm s) : ℝ) : ℂ)
  have hGcont : Continuous G := Complex.continuous_ofReal.comp (hPcont.comp φ.symm.continuous)
  have hGper : ∀ (s : Fin n → ℝ) (k : Fin n → ℤ), G (s + fun i => (k i : ℝ)) = G s := by
    intro s k; simp only [G, map_add, ← hB k]; rw [hPper]
  obtain ⟨F, hF⟩ := exists_continuous_torus_lift_of_periodic G hGcont hGper
  set h : (Fin n → ℝ) → ℂ := fun s => (Real.exp (-Real.pi * t * ‖φ.symm s‖ ^ 2) : ℂ)
  have hhcont : Continuous h :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_norm.comp φ.symm.continuous).pow 2)))
  have hFh : ∀ s : Fin n → ℝ, F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : Fin n → ℤ, h (s + fun i => (k i : ℝ)) := by
    intro s; rw [hF]; simp only [G, P]
    rw [Complex.ofReal_tsum, ← B.tsum_eq]
    congr 1; funext k; simp only [h, map_add, hB k, add_comm]
  have hcoef : ∀ m : Fin n → ℤ, UnitAddTorus.mFourierCoeff F m =
      (((ZLattice.covolume Λ volume)⁻¹ * t ^ (-(n : ℝ) / 2) *
        Real.exp (-Real.pi * ‖((D m : dualLattice Λ) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / t) : ℝ) :
        ℂ) := by
    intro m
    rw [mFourierCoeff_periodization_eq_integral h hInt hhcont F hFh m, ← hG (D m)]
    congr 1; funext s
    rw [mFourier_coe_eq_exp', hD, φ.apply_symm_apply]
    congr 2
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  have hsumc : Summable (UnitAddTorus.mFourierCoeff F) := by
    have e1 : UnitAddTorus.mFourierCoeff F = fun m =>
        (((ZLattice.covolume Λ volume)⁻¹ * t ^ (-(n : ℝ) / 2) *
          Real.exp (-Real.pi * ‖((D m : dualLattice Λ) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / t) : ℝ) :
          ℂ) := funext hcoef
    rw [e1]
    apply Complex.summable_ofReal.2
    apply Summable.mul_left
    exact (D.summable_iff (f := fun y : dualLattice Λ =>
      Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / t))).2 sum2
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumc
    (fun i => ((φ v i : ℝ) : UnitAddCircle))
  rw [hF] at hs
  simp only [G, ContinuousLinearEquiv.symm_apply_apply] at hs
  have hre := Complex.reCLM.hasSum hs
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
  have hterm : ∀ m : Fin n → ℤ, (UnitAddTorus.mFourierCoeff F m •
      UnitAddTorus.mFourier m (fun i => ((φ v i : ℝ) : UnitAddCircle))).re =
      (ZLattice.covolume Λ volume)⁻¹ * t ^ (-(n : ℝ) / 2) *
        (Real.exp (-Real.pi * ‖((D m : dualLattice Λ) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / t) *
          Real.cos (2 * Real.pi * inner ℝ ((D m : dualLattice Λ) : EuclideanSpace ℝ (Fin n)) v)) := by
    intro m
    rw [hcoef, mFourier_coe_eq_exp', smul_eq_mul, Complex.re_ofReal_mul]
    have e2 : (2 * π * Complex.I * ∑ i, (m i : ℂ) * (φ v i : ℂ)) =
        ((2 * π * inner ℝ ((D m : dualLattice Λ) : EuclideanSpace ℝ (Fin n)) v : ℝ) : ℂ) *
          Complex.I := by
      rw [hD]; push_cast; ring
    rw [e2, Complex.exp_ofReal_mul_I_re]; ring
  have hre2 : HasSum (fun y : dualLattice Λ => (ZLattice.covolume Λ volume)⁻¹ * t ^ (-(n : ℝ) / 2) *
      (Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / t) *
        Real.cos (2 * Real.pi * inner ℝ (y : EuclideanSpace ℝ (Fin n)) v))) (P v) := by
    rw [← D.hasSum_iff]
    exact hre.congr_fun fun m => (hterm m).symm
  rw [← tsum_mul_left]
  exact hre2.tsum_eq.symm

/-- **Exact Multidimensional Shifted Poisson Summation Formula (`rhoShift_poisson_summation`)**:
for any full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, any `s > 0`, and any `u : ℝ^n`:
`rhoShift s Λ u = (s^n / covol Λ) * ∑'_{w ∈ Λ*} cos(2π ⟪w, u⟫) * exp(-π s² ‖w‖²)`. -/
theorem rhoShift_poisson_summation {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s : ℝ} (hs : 0 < s) (u : EuclideanSpace ℝ (Fin n)) :
    rhoShift s Λ u =
      (s ^ n / ZLattice.covolume Λ volume) *
        ∑' w : dualLattice Λ,
          Real.cos (2 * Real.pi * inner ℝ (w : EuclideanSpace ℝ (Fin n)) u) *
            Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
  have hP := poisson_summation_gaussian_exact Λ (t := 1 / s ^ 2) (by positivity) (-u)
  have hlhs : ∑' x : Λ, Real.exp (-Real.pi * (1 / s ^ 2) *
      ‖(x : EuclideanSpace ℝ (Fin n)) + -u‖ ^ 2) = rhoShift s Λ u := by
    unfold rhoShift; congr 1; funext x; congr 1; rw [← sub_eq_add_neg]; ring
  have hfac : (ZLattice.covolume Λ volume)⁻¹ * (1 / s ^ 2) ^ (-(n : ℝ) / 2) =
      s ^ n / ZLattice.covolume Λ volume := by
    have hs2 : (1 / s ^ 2 : ℝ) = s ^ (-(2 : ℝ)) := by
      rw [one_div, Real.rpow_neg hs.le, Real.rpow_two]
    rw [hs2, ← Real.rpow_mul hs.le, show (-(2 : ℝ)) * (-(n : ℝ) / 2) = (n : ℝ) by ring,
      Real.rpow_natCast, div_eq_mul_inv, mul_comm]
  have hrhs : (∑' y : dualLattice Λ,
      Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (1 / s ^ 2)) *
        Real.cos (2 * Real.pi * inner ℝ (y : EuclideanSpace ℝ (Fin n)) (-u))) =
      ∑' w : dualLattice Λ,
        Real.cos (2 * Real.pi * inner ℝ (w : EuclideanSpace ℝ (Fin n)) u) *
          Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    congr 1; funext w
    rw [inner_neg_right, mul_neg, Real.cos_neg, mul_comm]
    congr 2; field_simp [hs.ne']
  rw [hlhs, hfac, hrhs] at hP
  exact hP

/-- **Exact Multidimensional Poisson Summation Formula (`rho_poisson_summation`)**:
for any full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)` and any `s > 0`:
`rho s Λ = (s ^ n / ZLattice.covolume Λ volume) * rho (1 / s) (dualLattice Λ)`. -/
theorem rho_poisson_summation {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s : ℝ} (hs : 0 < s) :
    rho s Λ = (s ^ n / ZLattice.covolume Λ volume) * rho (1 / s) (dualLattice Λ) := by
  have h := rhoShift_poisson_summation Λ hs 0
  rw [rhoShift_zero] at h
  rw [h]
  congr 1
  unfold rho
  congr 1; funext w
  simp only [inner_zero_right, mul_zero, Real.cos_zero, one_mul]
  congr 1
  field_simp [hs.ne']

/-- Helper: multiplying a nonnegative summable function by a bounded function (`|θ| ≤ 1`)
preserves summability. -/
private lemma summable_mul_of_nonneg_of_abs_le_one {ι : Type*} {e θ : ι → ℝ} (he : Summable e)
    (he0 : ∀ i, 0 ≤ e i) (hθ : ∀ i, |θ i| ≤ 1) : Summable fun i => e i * θ i := by
  have h1 : Summable fun i => e i * θ i + e i := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (he.mul_left 2)
    · have := (abs_le.mp (hθ i)).1
      nlinarith [mul_nonneg (he0 i) (by linarith : 0 ≤ θ i + 1)]
    · have := (abs_le.mp (hθ i)).2
      nlinarith [mul_nonneg (he0 i) (by linarith : 0 ≤ 1 - θ i)]
  exact (h1.sub he).congr (fun i => by ring)

/-- **Shifted Gaussian Mass Domination (`rhoShift_le_rho`)**:
for any full-rank lattice `Λ`, any `s > 0`, and any shift `u : ℝ^n`,
`rhoShift s Λ u ≤ rho s Λ` (immediate from `cos(2π ⟪w, u⟫) ≤ 1` in Poisson summation). -/
theorem rhoShift_le_rho {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s : ℝ} (hs : 0 < s) (u : EuclideanSpace ℝ (Fin n)) :
    rhoShift s Λ u ≤ rho s Λ := by
  rw [rhoShift_poisson_summation Λ hs u, rho_poisson_summation Λ hs]
  have hpref : 0 ≤ s ^ n / ZLattice.covolume Λ volume :=
    div_nonneg (pow_nonneg hs.le n) (ZLattice.covolume_pos Λ volume).le
  refine mul_le_mul_of_nonneg_left ?_ hpref
  have hsumD : Summable fun w : dualLattice Λ =>
      Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    refine (summable_rho (by positivity : 0 < 1 / s) (dualLattice Λ)).congr fun w => ?_
    congr 1; field_simp [hs.ne']
  have hsumC : Summable fun w : dualLattice Λ =>
      Real.cos (2 * Real.pi * inner ℝ (w : EuclideanSpace ℝ (Fin n)) u) *
        Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    have h := summable_mul_of_nonneg_of_abs_le_one hsumD
      (fun _ => (Real.exp_pos _).le)
      (fun w => Real.abs_cos_le_one (2 * Real.pi * inner ℝ (w : EuclideanSpace ℝ (Fin n)) u))
    exact h.congr fun w => mul_comm _ _
  have hrhoD : rho (1 / s) (dualLattice Λ) = ∑' w : dualLattice Λ,
      Real.exp (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    unfold rho; congr 1; funext w; congr 1; field_simp [hs.ne']
  rw [hrhoD]
  refine hasSum_le (fun w => ?_) hsumC.hasSum hsumD.hasSum
  have hcos : Real.cos (2 * Real.pi * inner ℝ (w : EuclideanSpace ℝ (Fin n)) u) ≤ 1 :=
    Real.cos_le_one _
  nlinarith [Real.exp_pos (-Real.pi * s ^ 2 * ‖(w : EuclideanSpace ℝ (Fin n))‖ ^ 2)]

/-- **Banaszczyk Gaussian Scaling Inequality (`rho_le_scale_mul_rho`)**:
for any full-rank lattice `Λ ⊂ ℝ^n` and `0 < s₁ ≤ s₂`,
`rho s₂ Λ ≤ (s₂ / s₁) ^ n * rho s₁ Λ`. -/
theorem rho_le_scale_mul_rho {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hle : s₁ ≤ s₂) :
    rho s₂ Λ ≤ (s₂ / s₁) ^ n * rho s₁ Λ := by
  have hs₂ : 0 < s₂ := lt_of_lt_of_le hs₁ hle
  rw [rho_poisson_summation Λ hs₂, rho_poisson_summation Λ hs₁]
  have hcov : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  have hmono : rho (1 / s₂) (dualLattice Λ) ≤ rho (1 / s₁) (dualLattice Λ) :=
    rho_mono (by positivity) (one_div_le_one_div_of_le hs₁ hle) (dualLattice Λ)
  calc (s₂ ^ n / ZLattice.covolume Λ volume) * rho (1 / s₂) (dualLattice Λ)
      ≤ (s₂ ^ n / ZLattice.covolume Λ volume) * rho (1 / s₁) (dualLattice Λ) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (s₂ / s₁) ^ n * ((s₁ ^ n / ZLattice.covolume Λ volume) * rho (1 / s₁) (dualLattice Λ)) := by
        rw [div_pow]; field_simp [hs₁.ne', hcov.ne']

end DiscreteGaussianAndPoisson

/-! ## Section 3: Unconditional Banaszczyk Gaussian Tail Bounds (1993, Lemma 1.5) -/

section BanaszczykTailBounds

/-- The exact Banaszczyk (1993, Lemma 1.5) tail base constant:
`banaszczykConst c = c * √(2 * π * e) * exp(-π * c²)`. -/
def banaszczykConst (c : ℝ) : ℝ :=
  c * Real.sqrt (2 * Real.pi * Real.exp 1) * Real.exp (-Real.pi * c ^ 2)

lemma banaszczykConst_pos {c : ℝ} (hc : 0 < c) : 0 < banaszczykConst c := by
  unfold banaszczykConst
  have : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  positivity

/-- For every `c > 1 / √(2 * π)`, the Banaszczyk base constant is strictly less than `1`. -/
theorem banaszczykConst_lt_one {c : ℝ} (hc : 1 / Real.sqrt (2 * Real.pi) < c) :
    banaszczykConst c < 1 := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi
  have hc0 : 0 < c := lt_trans (div_pos one_pos hsq) hc
  set x : ℝ := c * Real.sqrt (2 * Real.pi)
  have hx1 : 1 < x := by
    dsimp only [x]
    rwa [div_lt_iff₀ hsq] at hc
  have hx2 : x ^ 2 = 2 * Real.pi * c ^ 2 := by
    dsimp only [x]
    rw [mul_pow, Real.sq_sqrt h2pi.le]; ring
  have hsqe : Real.sqrt (Real.exp 1) = Real.exp (1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul, one_mul]
  have hrewrite : banaszczykConst c = x * Real.exp ((1 - x ^ 2) / 2) := by
    unfold banaszczykConst
    rw [Real.sqrt_mul h2pi.le, hsqe]
    calc c * (Real.sqrt (2 * Real.pi) * Real.exp (1 / 2)) * Real.exp (-Real.pi * c ^ 2)
        = x * (Real.exp (1 / 2) * Real.exp (-Real.pi * c ^ 2)) := by dsimp only [x]; ring
      _ = x * Real.exp ((1 - x ^ 2) / 2) := by
          rw [← Real.exp_add]; congr 2; linarith [hx2]
  rw [hrewrite]
  -- Since `x > 1`, `x < exp(x - 1) < exp((x² - 1) / 2)`.
  have h1 : x ≤ Real.exp (x - 1) := by linarith [Real.add_one_le_exp (x - 1)]
  have h2 : Real.exp (x - 1) < Real.exp ((x ^ 2 - 1) / 2) :=
    Real.exp_strictMono (by nlinarith [sq_pos_of_pos (sub_pos.mpr hx1)])
  have h3 : x < Real.exp ((x ^ 2 - 1) / 2) := lt_of_le_of_lt h1 h2
  have hneg : Real.exp ((1 - x ^ 2) / 2) = (Real.exp ((x ^ 2 - 1) / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hneg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  exact h3

/-- Explicit numerical bound at `c = 1`: `banaszczykConst 1 = √(2πe) * exp(-π) ≤ 1 / 2`. -/
theorem banaszczykConst_one_le_half : banaszczykConst 1 ≤ 1 / 2 := by
  unfold banaszczykConst
  rw [one_mul, one_pow, mul_one, Real.exp_neg, ← div_eq_mul_inv]
  rw [div_le_iff₀ (Real.exp_pos Real.pi)]
  -- Need `√(2πe) ≤ (1 / 2) * exp π`, i.e., `4 * (2πe) ≤ (exp π)²`, i.e., `8πe ≤ exp(2π)`.
  have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_lt : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have he_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he_lt : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hexp3 : Real.exp 3 < Real.exp Real.pi := Real.exp_strictMono (by linarith)
  have hexp3_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hexp_pi_gt : (20 : ℝ) < Real.exp Real.pi := by nlinarith
  have hsq_le : 2 * Real.pi * Real.exp 1 ≤ ((1 / 2) * Real.exp Real.pi) ^ 2 := by nlinarith
  have hrhs_nn : 0 ≤ (1 / 2) * Real.exp Real.pi := by positivity
  calc Real.sqrt (2 * Real.pi * Real.exp 1)
      ≤ Real.sqrt (((1 / 2) * Real.exp Real.pi) ^ 2) := Real.sqrt_le_sqrt hsq_le
    _ = (1 / 2) * Real.exp Real.pi := Real.sqrt_sq hrhs_nn

/-- Helper: a `tsum` over a subtype `{v : α // P v}` of a nonnegative summable function `f` is
bounded by `∑' v : α, g v` for any nonnegative summable dominating function `g`. -/
private lemma tsum_subtype_le_tsum_of_nonneg {α : Type*} {P : α → Prop} {f g : α → ℝ}
    (hg : Summable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfg : ∀ x, P x → f x ≤ g x) :
    ∑' x : {x : α // P x}, f x.1 ≤ ∑' x : α, g x := by
  classical
  have hind : ∑' x : {x : α // P x}, f x.1 = ∑' x : α, if P x then f x else 0 := by
    have heq : ∑' x : {x : α // P x}, f x.1 = ∑' x : ({x : α | P x} : Set α), f x.1 :=
      (Equiv.subtypeEquivRight fun _ => Iff.rfl).tsum_eq (fun x : ({x : α | P x} : Set α) => f x.1)
    rw [heq, tsum_subtype ({x : α | P x}) f]
    simp [Set.indicator_apply]
  rw [hind]
  have hsum_ind : Summable (fun x : α => if P x then f x else 0) :=
    Summable.of_nonneg_of_le (fun x => by split_ifs <;> [exact hf0 x; exact le_rfl])
      (fun x => by split_ifs with hx <;> [exact hfg x hx; exact hg0 x]) hg
  refine hasSum_le (fun x => ?_) hsum_ind.hasSum hg.hasSum
  split_ifs with hx
  · exact hfg x hx
  · exact hg0 x

/-- Helper: congruence of `tsum` over subtypes with equivalent predicates. -/
private lemma tsum_subtype_congr_pred {α : Type*} {P Q : α → Prop} (hPQ : ∀ x, P x ↔ Q x)
    (f g : α → ℝ) (hfg : ∀ x, P x → f x = g x) :
    ∑' x : {x : α // P x}, f x.1 = ∑' x : {x : α // Q x}, g x.1 := by
  rw [← (Equiv.subtypeEquivRight hPQ).tsum_eq (fun x : {x : α // Q x} => g x.1)]
  congr 1; funext x; exact hfg x.1 x.2

/-- **UNCONDITIONAL BANASZCZYK SHIFTED GAUSSIAN TAIL BOUND (1993, Lemma 1.5 — Exact Constant)**:
For every dimension `n ≥ 1`, every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, every
`s > 0`, every `c > 1 / √(2 * π)`, and every shift `u : EuclideanSpace ℝ (Fin n)`:
`∑'_{v ∈ Λ, ‖v - u‖ > c √n s} exp(-π ‖v - u‖² / s²) ≤ (c √(2πe) exp(-π c²))^n * ρ_s(Λ)`. -/
theorem banaszczyk_tail_bound_shift_exact {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s c : ℝ} (hs : 0 < s) (hc : 1 / Real.sqrt (2 * Real.pi) < c)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑' v : {v : Λ // c * Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
      Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2) ≤
      (banaszczykConst c) ^ n * rho s Λ := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hsq2pi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi
  have hc0 : 0 < c := lt_trans (div_pos one_pos hsq2pi) hc
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hc2pi : 1 < 2 * Real.pi * c ^ 2 := by
    have h1 : 1 < c * Real.sqrt (2 * Real.pi) := (div_lt_iff₀ hsq2pi).mp hc
    have h2 : 1 ^ 2 < (c * Real.sqrt (2 * Real.pi)) ^ 2 := pow_lt_pow_left₀ h1 zero_le_one two_ne_zero
    rw [one_pow, mul_pow, Real.sq_sqrt h2pi.le] at h2
    linarith
  set τ : ℝ := 1 / (2 * Real.pi * c ^ 2)
  have hτ_pos : 0 < τ := by positivity
  have hτ_lt : τ < 1 := (div_lt_one (by positivity)).mpr hc2pi
  have h1mτ : 0 < 1 - τ := sub_pos.mpr hτ_lt
  set s' : ℝ := s / Real.sqrt τ
  have hsqτ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ_pos
  have hs'_pos : 0 < s' := div_pos hs hsqτ_pos
  have hs_le_s' : s ≤ s' := by
    dsimp only [s']
    rw [le_div_iff₀ hsqτ_pos]
    have hsqτ_le : Real.sqrt τ ≤ 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hτ_lt.le
    nlinarith
  have hs'2 : s' ^ 2 = s ^ 2 / τ := by
    dsimp only [s']; rw [div_pow, Real.sq_sqrt hτ_pos.le]
  -- Step 1: Bound the tail sum by `exp(-π (1 - τ) c² n) * rhoShift s' Λ u`.
  have hstep1 :
      ∑' v : {v : Λ // c * Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2) ≤
      Real.exp (-Real.pi * (1 - τ) * c ^ 2 * (n : ℝ)) * rhoShift s' Λ u := by
    rw [rhoShift, ← tsum_mul_left]
    refine tsum_subtype_le_tsum_of_nonneg
      (f := fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2))
      (g := fun v : Λ => Real.exp (-Real.pi * (1 - τ) * c ^ 2 * (n : ℝ)) *
        Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s' ^ 2))
      ((summable_rhoShift hs'_pos Λ u).mul_left _)
      (fun _ => (Real.exp_pos _).le)
      (fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) ?_
    intro v hv
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hv2 : c ^ 2 * (n : ℝ) * s ^ 2 ≤ ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hv.le 2
      have heq : (c * Real.sqrt (n : ℝ) * s) ^ 2 = c ^ 2 * (n : ℝ) * s ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hn_pos.le]
      linarith
    have hv_div : c ^ 2 * (n : ℝ) ≤ ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2 := by
      rw [le_div_iff₀ (pow_pos hs 2)]; exact hv2
    have hterm : -Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s' ^ 2 =
        -Real.pi * τ * (‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2) := by
      rw [hs'2]; field_simp [hs.ne', hτ_pos.ne']
    rw [hterm]
    have hcoeff : 0 ≤ Real.pi * (1 - τ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hv_div hcoeff
    linarith [show -Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2 =
      -(Real.pi * (1 - τ) * (‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2)) +
      -Real.pi * τ * (‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2) by ring]
  -- Step 2: `rhoShift s' Λ u ≤ rho s' Λ ≤ (s' / s)^n * rho s Λ = (1 / √τ)^n * rho s Λ`.
  have hstep2 : rhoShift s' Λ u ≤ (1 / Real.sqrt τ) ^ n * rho s Λ := by
    have h1 := rhoShift_le_rho Λ hs'_pos u
    have h2 := rho_le_scale_mul_rho Λ hs hs_le_s'
    have hrat : s' / s = 1 / Real.sqrt τ := by dsimp only [s']; field_simp [hs.ne']
    rw [hrat] at h2
    exact h1.trans h2
  -- Step 3: Exact algebraic simplification `exp(-π (1 - τ) c² n) * (1 / √τ)^n = (banaszczykConst c)^n`.
  have halg : Real.exp (-Real.pi * (1 - τ) * c ^ 2 * (n : ℝ)) * (1 / Real.sqrt τ) ^ n =
      (banaszczykConst c) ^ n := by
    have h1 : -Real.pi * (1 - τ) * c ^ 2 * (n : ℝ) = (n : ℝ) * (1 / 2 + -Real.pi * c ^ 2) := by
      dsimp only [τ]; field_simp [Real.pi_ne_zero, hc0.ne']; ring
    rw [h1, Real.exp_nat_mul, ← mul_pow]
    congr 1
    unfold banaszczykConst
    have hinv_sq : 1 / Real.sqrt τ = c * Real.sqrt (2 * Real.pi) := by
      dsimp only [τ]
      rw [one_div, one_div, Real.sqrt_inv, inv_inv, Real.sqrt_mul h2pi.le,
        Real.sqrt_sq hc0.le, mul_comm]
    have hsqe : Real.sqrt (Real.exp 1) = Real.exp (1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul, one_mul]
    rw [hinv_sq, Real.exp_add, Real.sqrt_mul h2pi.le, hsqe]
    ring
  calc ∑' v : {v : Λ // c * Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2)
      ≤ Real.exp (-Real.pi * (1 - τ) * c ^ 2 * (n : ℝ)) * rhoShift s' Λ u := hstep1
    _ ≤ Real.exp (-Real.pi * (1 - τ) * c ^ 2 * (n : ℝ)) * ((1 / Real.sqrt τ) ^ n * rho s Λ) :=
        mul_le_mul_of_nonneg_left hstep2 (Real.exp_pos _).le
    _ = (Real.exp (-Real.pi * (1 - τ) * c ^ 2 * (n : ℝ)) * (1 / Real.sqrt τ) ^ n) * rho s Λ := by
        ring
    _ = (banaszczykConst c) ^ n * rho s Λ := by rw [halg]

/-- **UNCONDITIONAL BANASZCZYK CENTERED GAUSSIAN TAIL BOUND (Exact Constant)**:
specialization of `banaszczyk_tail_bound_shift_exact` at `u = 0`. -/
theorem banaszczyk_tail_bound_exact {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s c : ℝ} (hs : 0 < s) (hc : 1 / Real.sqrt (2 * Real.pi) < c) :
    ∑' v : {v : Λ // c * Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n))‖},
      Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2) ≤
      (banaszczykConst c) ^ n * rho s Λ := by
  have h := banaszczyk_tail_bound_shift_exact hn Λ hs hc 0
  have heq :
      ∑' v : {v : Λ // c * Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n))‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2) =
      ∑' v : {v : Λ // c * Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - 0‖ ^ 2 / s ^ 2) := by
    refine tsum_subtype_congr_pred ?_
      (fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2))
      (fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖ ^ 2 / s ^ 2)) ?_
    · intro v; simp
    · intro v _; simp
  rw [heq]; exact h

/-- **UNCONDITIONAL BANASZCZYK SHIFTED `2^(-n)` TAIL BOUND (General Scale `s > 0`, All `n : ℕ`)**:
`∑'_{v ∈ Λ, ‖v - u‖ > √n * s} exp(-π ‖v - u‖² / s²) ≤ 2^(-n) * ρ_s(Λ)`. -/
theorem banaszczyk_tail_bound_scale {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {s : ℝ} (hs : 0 < s) (u : EuclideanSpace ℝ (Fin n)) :
    ∑' v : {v : Λ // Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
      Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2) ≤
      (2 : ℝ) ^ (-(n : ℝ)) * rho s Λ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : IsEmpty
        {v : Λ // Real.sqrt ((0 : ℕ) : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin 0)) - u‖} := by
      refine ⟨fun v => ?_⟩
      have h0 : (v.1 : EuclideanSpace ℝ (Fin 0)) - u = 0 := Subsingleton.elim _ _
      have hv := v.2
      rw [h0, norm_zero, Nat.cast_zero, Real.sqrt_zero, zero_mul] at hv
      exact lt_irrefl 0 hv
    rw [tsum_empty]
    have := rho_pos hs Λ
    positivity
  · have hc1 : 1 / Real.sqrt (2 * Real.pi) < 1 := by
      have h2pi : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hsq : 1 < Real.sqrt (2 * Real.pi) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one h2pi
      exact (div_lt_one (zero_lt_one.trans hsq)).mpr hsq
    have h := banaszczyk_tail_bound_shift_exact hn Λ hs hc1 u
    have heq :
        ∑' v : {v : Λ // Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
          Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2) =
        ∑' v : {v : Λ // 1 * Real.sqrt (n : ℝ) * s < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
          Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2) := by
      refine tsum_subtype_congr_pred ?_
        (fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2))
        (fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2)) ?_
      · intro v; simp
      · intro _ _; rfl
    rw [heq]
    have hpow : (banaszczykConst 1) ^ n ≤ (2 : ℝ) ^ (-(n : ℝ)) := by
      rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, ← inv_pow, ← one_div]
      exact pow_le_pow_left₀ (banaszczykConst_pos zero_lt_one).le banaszczykConst_one_le_half n
    exact h.trans (mul_le_mul_of_nonneg_right hpow (rho_pos hs Λ).le)

/-- **UNCONDITIONAL BANASZCZYK GAUSSIAN TAIL BOUND (`banaszczyk_tail_bound`)**:
For every dimension `n : ℕ` and every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`:
`∑'_{v ∈ Λ, √n < ‖v‖} exp(-π ‖v‖²) ≤ 2^(-n) * rho 1 Λ`. -/
theorem banaszczyk_tail_bound {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∑' v : {v : Λ // Real.sqrt (n : ℝ) < ‖(v : EuclideanSpace ℝ (Fin n))‖},
      Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      (2 : ℝ) ^ (-(n : ℝ)) * rho 1 Λ := by
  have h := banaszczyk_tail_bound_scale Λ zero_lt_one 0
  have heq :
      ∑' v : {v : Λ // Real.sqrt (n : ℝ) < ‖(v : EuclideanSpace ℝ (Fin n))‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2) =
      ∑' v : {v : Λ // Real.sqrt (n : ℝ) * 1 < ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - 0‖ ^ 2 / 1 ^ 2) := by
    refine tsum_subtype_congr_pred ?_
      (fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      (fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - 0‖ ^ 2 / 1 ^ 2)) ?_
    · intro v; simp
    · intro v _; simp
  rw [heq]; exact h

/-- **UNCONDITIONAL BANASZCZYK SHIFTED GAUSSIAN TAIL BOUND (`banaszczyk_tail_bound_shift`)**:
For every dimension `n : ℕ`, every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, and every
coset shift `u : EuclideanSpace ℝ (Fin n)`:
`∑'_{v ∈ Λ, √n < ‖v - u‖} exp(-π ‖v - u‖²) ≤ 2^(-n) * rho 1 Λ`. -/
theorem banaszczyk_tail_bound_shift {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑' v : {v : Λ // Real.sqrt (n : ℝ) < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
      Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2) ≤
      (2 : ℝ) ^ (-(n : ℝ)) * rho 1 Λ := by
  have h := banaszczyk_tail_bound_scale Λ zero_lt_one u
  have heq :
      ∑' v : {v : Λ // Real.sqrt (n : ℝ) < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2) =
      ∑' v : {v : Λ // Real.sqrt (n : ℝ) * 1 < ‖(v : EuclideanSpace ℝ (Fin n)) - u‖},
        Real.exp (-Real.pi * ‖(v.1 : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / 1 ^ 2) := by
    refine tsum_subtype_congr_pred ?_
      (fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2))
      (fun v : Λ => Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / 1 ^ 2)) ?_
    · intro v; simp
    · intro v _; simp
  rw [heq]; exact h

end BanaszczykTailBounds

/-! ## Section 4: Unconditional Banaszczyk Transference Theorems (Covering Radius & All Minima) -/

section BanaszczykTransferenceTheorems

private lemma one_le_inv_of_pos_of_le_one {τ : ℝ} (h : 0 < τ) (h' : τ ≤ 1) : 1 ≤ τ⁻¹ := by
  have h1 := mul_inv_cancel₀ h.ne'
  nlinarith [mul_nonneg (inv_pos.mpr h).le (sub_nonneg.mpr h')]

/-- Abstract dual-Gaussian Poisson contradiction inequality powering Banaszczyk's sharp
`n / 2` covering constant (for all `n ≥ 2`). -/
private theorem gauss_transference_abstract {X Y : Type*} (a a0 : X → ℝ) (q θ : Y → ℝ) (n c : ℝ)
    (hq : ∀ y, 0 ≤ q y) (ha0 : ∀ x, 0 ≤ a0 x) (hθ : ∀ y, |θ y| ≤ 1) (hc : 0 < c) (y0 : Y)
    (sA : ∀ t : ℝ, 0 < t → Summable fun x => Real.exp (-π * t * a x))
    (sA0 : ∀ t : ℝ, 0 < t → Summable fun x => Real.exp (-π * t * a0 x))
    (sQ : ∀ t : ℝ, 0 < t → Summable fun y => Real.exp (-π * q y / t))
    (Pu : ∀ t : ℝ, 0 < t → ∑' x, Real.exp (-π * t * a x) =
      c * t ^ (-n / 2) * ∑' y, Real.exp (-π * q y / t) * θ y)
    (P0 : ∀ t : ℝ, 0 < t → ∑' x, Real.exp (-π * t * a0 x) =
      c * t ^ (-n / 2) * ∑' y, Real.exp (-π * q y / t))
    (R2 l2 : ℝ) (hR : ∀ x, R2 ≤ a x) (hl : ∀ y, q y < l2 → θ y = 1)
    (s τ₁ τ₂ : ℝ) (hs : 0 < s) (h1 : 0 < τ₁) (h1' : τ₁ ≤ 1) (h2 : 0 < τ₂) (h2' : τ₂ ≤ 1) :
    1 ≤ Real.exp (-π * s * (1 - τ₁) * R2) * τ₁ ^ (-n / 2) +
      2 * (Real.exp (-π * (1 - τ₂) * l2 / s) * τ₂ ^ (-n / 2)) := by
  have hπ : 0 < π := Real.pi_pos
  have hst1 : 0 < s * τ₁ := mul_pos hs h1
  have hst2 : 0 < s / τ₂ := div_pos hs h2
  have hQs := sQ s hs
  have hQ1 := sQ _ hst1
  have hQ2 := sQ _ hst2
  have hK : 0 < c * s ^ (-n / 2) := mul_pos hc (Real.rpow_pos_of_pos hs _)
  have hA : 0 < τ₁ ^ (-n / 2) := Real.rpow_pos_of_pos h1 _
  have hT : 0 < τ₂ ^ (-n / 2) := Real.rpow_pos_of_pos h2 _
  have hE1 : 0 < Real.exp (-π * s * (1 - τ₁) * R2) := Real.exp_pos _
  have hE2 : 0 < Real.exp (-π * (1 - τ₂) * l2 / s) := Real.exp_pos _
  have hS0pos : 0 < ∑' y, Real.exp (-π * q y / s) :=
    lt_of_lt_of_le (Real.exp_pos _)
      (le_hasSum hQs.hasSum y0 (fun _ _ => (Real.exp_pos _).le))
  have up1 : ∑' x, Real.exp (-π * s * a x) ≤
      Real.exp (-π * s * (1 - τ₁) * R2) * ∑' x, Real.exp (-π * (s * τ₁) * a x) := by
    refine hasSum_le (fun x => ?_) (sA s hs).hasSum ((sA _ hst1).hasSum.mul_left _)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ π * s * (1 - τ₁) := mul_nonneg (mul_nonneg hπ.le hs.le) (sub_nonneg.mpr h1')
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr (hR x))]
  have hle1 : ∑' y, Real.exp (-π * q y / (s * τ₁)) * θ y ≤ ∑' y, Real.exp (-π * q y / s) := by
    refine hasSum_le (fun y => ?_)
      (summable_mul_of_nonneg_of_abs_le_one hQ1 (fun _ => (Real.exp_pos _).le) hθ).hasSum hQs.hasSum
    have hθ1 := (abs_le.mp (hθ y)).2
    have he := Real.exp_pos (-π * q y / (s * τ₁))
    have hmono : Real.exp (-π * q y / (s * τ₁)) ≤ Real.exp (-π * q y / s) := by
      apply Real.exp_le_exp.mpr
      have hw : 0 ≤ π * q y / s := div_nonneg (mul_nonneg hπ.le (hq y)) hs.le
      have e1 : -π * q y / (s * τ₁) = -(π * q y / s) * τ₁⁻¹ := by ring
      have e2 : -π * q y / s = -(π * q y / s) := by ring
      have hinv := one_le_inv_of_pos_of_le_one h1 h1'
      rw [e1, e2]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hinv)]
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hθ1)]
  have up2 : ∑' x, Real.exp (-π * (s * τ₁) * a x) ≤
      c * s ^ (-n / 2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
    rw [Pu _ hst1, Real.mul_rpow hs.le h1.le]
    calc c * (s ^ (-n / 2) * τ₁ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / (s * τ₁)) * θ y
        ≤ c * (s ^ (-n / 2) * τ₁ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / s) :=
          mul_le_mul_of_nonneg_left hle1 (mul_pos hc (mul_pos (Real.rpow_pos_of_pos hs _) hA)).le
      _ = c * s ^ (-n / 2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by ring
  have hup : ∑' y, Real.exp (-π * q y / s) * θ y ≤
      Real.exp (-π * s * (1 - τ₁) * R2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
    have h := (Pu s hs).symm.le.trans (up1.trans (mul_le_mul_of_nonneg_left up2 hE1.le))
    have h' : c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s) * θ y ≤
        c * s ^ (-n / 2) * (Real.exp (-π * s * (1 - τ₁) * R2) *
          (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s))) := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_left h' hK
  have hlow : ∑' y, Real.exp (-π * q y / s) -
      2 * Real.exp (-π * (1 - τ₂) * l2 / s) * ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
      ∑' y, Real.exp (-π * q y / s) * θ y := by
    refine hasSum_le (fun y => ?_) (hQs.hasSum.sub (hQ2.hasSum.mul_left _))
      (summable_mul_of_nonneg_of_abs_le_one hQs (fun _ => (Real.exp_pos _).le) hθ).hasSum
    have he := Real.exp_pos (-π * q y / s)
    have hf := Real.exp_pos (-π * q y / (s / τ₂))
    have hprod : 0 < 2 * Real.exp (-π * (1 - τ₂) * l2 / s) * Real.exp (-π * q y / (s / τ₂)) :=
      mul_pos (mul_pos two_pos hE2) hf
    by_cases hql : q y < l2
    · rw [hl y hql, mul_one]; linarith
    · have hql : l2 ≤ q y := not_lt.mp hql
      have hef : Real.exp (-π * q y / s) ≤
          Real.exp (-π * (1 - τ₂) * l2 / s) * Real.exp (-π * q y / (s / τ₂)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have e1 : -π * q y / (s / τ₂) = -π * q y * τ₂ / s := div_div_eq_mul_div _ _ _
        rw [e1]
        have key : -π * q y / s - (-π * (1 - τ₂) * l2 / s + -π * q y * τ₂ / s) =
            -(π * (1 - τ₂) * (q y - l2) / s) := by ring
        have hnn : 0 ≤ π * (1 - τ₂) * (q y - l2) / s :=
          div_nonneg (mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr h2')) (sub_nonneg.mpr hql)) hs.le
        linarith
      have hθ0 := (abs_le.mp (hθ y)).1
      nlinarith [mul_nonneg he.le (by linarith : 0 ≤ θ y + 1)]
  have hfB : ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
      τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s) := by
    have m : ∑' x, Real.exp (-π * (s / τ₂) * a0 x) ≤ ∑' x, Real.exp (-π * s * a0 x) := by
      refine hasSum_le (fun x => ?_) (sA0 _ hst2).hasSum (sA0 s hs).hasSum
      apply Real.exp_le_exp.mpr
      have hinv := one_le_inv_of_pos_of_le_one h2 h2'
      have hsle : s ≤ s / τ₂ := by
        rw [div_eq_mul_inv]; nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hinv)]
      nlinarith [mul_nonneg (mul_nonneg hπ.le (ha0 x)) (sub_nonneg.mpr hsle)]
    rw [P0 _ hst2, P0 s hs, Real.div_rpow hs.le h2.le] at m
    have hPT : s ^ (-n / 2) / τ₂ ^ (-n / 2) * τ₂ ^ (-n / 2) = s ^ (-n / 2) := by
      field_simp [hT.ne']
    have m3 : c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
        c * s ^ (-n / 2) * (τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
      have m2 := mul_le_mul_of_nonneg_right m hT.le
      calc c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / (s / τ₂))
          = c * (s ^ (-n / 2) / τ₂ ^ (-n / 2) * τ₂ ^ (-n / 2)) *
              ∑' y, Real.exp (-π * q y / (s / τ₂)) := by rw [hPT]
        _ = (c * (s ^ (-n / 2) / τ₂ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / (s / τ₂))) *
              τ₂ ^ (-n / 2) := by ring
        _ ≤ (c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) * τ₂ ^ (-n / 2) := m2
        _ = c * s ^ (-n / 2) * (τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by ring
    exact le_of_mul_le_mul_left m3 hK
  have hfin : (∑' y, Real.exp (-π * q y / s)) * 1 ≤
      (∑' y, Real.exp (-π * q y / s)) * (Real.exp (-π * s * (1 - τ₁) * R2) * τ₁ ^ (-n / 2) +
        2 * (Real.exp (-π * (1 - τ₂) * l2 / s) * τ₂ ^ (-n / 2))) := by
    nlinarith [mul_le_mul_of_nonneg_left hfB (mul_pos two_pos hE2).le]
  exact le_of_mul_le_mul_left hfin hS0pos

private theorem banaszczyk_numeric_main :
    9 / 4 * Real.exp (-(2 * π / 5)) + 2 * (4 * Real.exp (-(25 * π / 24))) < 1 := by
  have hpi := Real.pi_gt_d2
  have e1 := Real.exp_one_gt_d9
  have q1 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.256 by norm_num)
  have q2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.27 by norm_num)
  have p1 := Real.exp_pos 0.256
  have p2 := Real.exp_pos 0.27
  have hX : 3.5 < Real.exp (2 * π / 5) := by
    have h : Real.exp 1.256 ≤ Real.exp (2 * π / 5) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp 1.256 = Real.exp 1 * Real.exp 0.256 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hY : 26 < Real.exp (25 * π / 24) := by
    have h : Real.exp 3.27 ≤ Real.exp (25 * π / 24) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp 3.27 = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 0.27 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
    have e3 : 20 < Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
    nlinarith
  have hXp : 0 < Real.exp (2 * π / 5) := Real.exp_pos _
  have hYp : 0 < Real.exp (25 * π / 24) := Real.exp_pos _
  rw [Real.exp_neg, Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
  have ha : 1 / Real.exp (2 * π / 5) < 2 / 7 := by rw [div_lt_iff₀ hXp]; linarith
  have hb : 1 / Real.exp (25 * π / 24) < 1 / 26 := by rw [div_lt_iff₀ hYp]; linarith
  linarith

private lemma banaszczyk_factor_le (κ τ m : ℝ) (hτ : 0 < τ) (hm : 1 ≤ m)
    (hh : τ⁻¹ * Real.exp (-κ) ≤ 1) :
    Real.exp (-κ * m) * τ ^ (-m) ≤ τ⁻¹ * Real.exp (-κ) := by
  have hb : 0 < τ⁻¹ * Real.exp (-κ) := by positivity
  have key : Real.exp (-κ * m) * τ ^ (-m) = (τ⁻¹ * Real.exp (-κ)) ^ m := by
    rw [Real.mul_rpow (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le, Real.inv_rpow hτ.le,
      ← Real.rpow_neg hτ.le, ← Real.exp_mul]
    ring
  rw [key]
  calc (τ⁻¹ * Real.exp (-κ)) ^ m ≤ (τ⁻¹ * Real.exp (-κ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hb hh hm
    _ = τ⁻¹ * Real.exp (-κ) := Real.rpow_one _

/-- **UNCONDITIONAL BANASZCZYK KEY TRANSFERENCE THEOREM (`banaszczyk_transference_key`)**:
For EVERY dimension `n : ℕ`, every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, every
`lam > 0`, and every vector `u : ℝ^n` that pairs integrally with all dual vectors `y ∈ Λ*` of
norm `< lam`, there exists `v ∈ Λ` with `‖u - v‖ * lam ≤ n / 2`! -/
theorem banaszczyk_transference_key {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {lam : ℝ} (hlam : 0 < lam) (u : EuclideanSpace ℝ (Fin n))
    (hdual : ∀ y ∈ dualLattice Λ, ‖y‖ < lam → ∃ k : ℤ, inner ℝ u y = (k : ℝ)) :
    ∃ v ∈ Λ, ‖u - v‖ * lam ≤ (n : ℝ) / 2 := by
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · -- Small dimensions `n = 0` and `n = 1` directly via rounding.
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hn1) with rfl | rfl
    · -- `n = 0`
      refine ⟨0, Λ.zero_mem, ?_⟩
      have hu0 : u = 0 := Subsingleton.elim u 0
      simp [hu0]
    · -- `n = 1`
      let b : Basis (Fin 1) ℤ Λ := basisOfZLattice Λ
      let a : EuclideanSpace ℝ (Fin 1) := (b 0 : EuclideanSpace ℝ (Fin 1))
      have haΛ : a ∈ Λ := (b 0).2
      have ha0 : a ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
      have hmul : ∀ x ∈ Λ, ∃ k : ℤ, x = (k : ℝ) • a := by
        intro x hx
        refine ⟨b.repr ⟨x, hx⟩ 0, ?_⟩
        have hs := b.sum_repr ⟨x, hx⟩
        rw [Fin.sum_univ_one] at hs
        have h2 := congrArg Subtype.val hs
        rw [Int.cast_smul_eq_zsmul]
        exact h2.symm.trans (Submodule.coe_smul _ _)
      have hdim1 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1 := finrank_euclideanSpace_fin
      obtain ⟨t, rfl⟩ : ∃ t : ℝ, u = t • a := by
        obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' a ha0).mp hdim1 u
        exact ⟨c, hc.symm⟩
      have hα : 0 < ‖a‖ := norm_pos_iff.mpr ha0
      rw [Nat.cast_one]
      by_cases hc : lam * ‖a‖ ≤ 1
      · refine ⟨((round t : ℤ) : ℝ) • a, ?_, ?_⟩
        · rw [Int.cast_smul_eq_zsmul]; exact Λ.smul_mem _ haΛ
        · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
          calc |t - ((round t : ℤ) : ℝ)| * ‖a‖ * lam ≤ (1 / 2) * ‖a‖ * lam :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (abs_sub_round t) (norm_nonneg a)) hlam.le
            _ = (1 / 2) * (lam * ‖a‖) := by ring
            _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left hc (by norm_num)
            _ = 1 / 2 := by ring
      · push Not at hc
        have hα2 : ‖a‖ ^ 2 ≠ 0 := by positivity
        have key : ∀ s : ℝ, inner ℝ (s • a) ((‖a‖ ^ 2)⁻¹ • a) = s := fun s => by
          rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
            inv_mul_cancel₀ hα2, mul_one]
        have hnorm : ‖(‖a‖ ^ 2)⁻¹ • a‖ < lam := by
          rw [norm_smul, norm_inv, norm_pow, norm_norm]
          have e : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ = 1 := by
            rw [mul_assoc, ← sq, inv_mul_cancel₀ hα2]
          have hlt : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ < lam * ‖a‖ := by rw [e]; exact hc
          exact lt_of_mul_lt_mul_right hlt hα.le
        have hdual_mem : (‖a‖ ^ 2)⁻¹ • a ∈ dualLattice Λ := by
          intro x hx; obtain ⟨k, rfl⟩ := hmul x hx; exact ⟨k, key _⟩
        obtain ⟨m, hm⟩ := hdual ((‖a‖ ^ 2)⁻¹ • a) hdual_mem hnorm
        rw [key] at hm
        refine ⟨(m : ℝ) • a, ?_, ?_⟩
        · rw [Int.cast_smul_eq_zsmul]; exact Λ.smul_mem _ haΛ
        · rw [hm, sub_self, norm_zero, zero_mul]; norm_num
  · -- Dimensions `n ≥ 2`: exact dual-Gaussian Poisson contradiction!
    by_contra hcon
    push Not at hcon
    have hnR2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    set m : ℝ := (n : ℝ) / 2
    have hm1 : 1 ≤ m := by dsimp only [m]; linarith
    have hm0 : 0 < m := by linarith
    set R2 : ℝ := (m / lam) ^ 2
    set s : ℝ := 18 / 25 * lam ^ 2 / m
    have hs : 0 < s := by positivity
    have hR : ∀ x : Λ, R2 ≤ ‖(x : EuclideanSpace ℝ (Fin n)) + -u‖ ^ 2 := by
      intro x
      have h := hcon x x.2
      have h' : m / lam < ‖(x : EuclideanSpace ℝ (Fin n)) + -u‖ := by
        rw [div_lt_iff₀ hlam, ← sub_eq_add_neg, norm_sub_rev]
        dsimp only [m] at h ⊢; linarith
      exact pow_le_pow_left₀ (by positivity) h'.le 2
    have hl : ∀ y : dualLattice Λ, ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 < lam ^ 2 →
        Real.cos (2 * π * inner ℝ (y : EuclideanSpace ℝ (Fin n)) (-u)) = 1 := by
      intro y hy
      have hy' : ‖(y : EuclideanSpace ℝ (Fin n))‖ < lam := by
        nlinarith [norm_nonneg (y : EuclideanSpace ℝ (Fin n))]
      obtain ⟨k, hk⟩ := hdual y y.2 hy'
      rw [inner_neg_right, real_inner_comm, hk]
      have : 2 * π * -(k : ℝ) = ((-k : ℤ) : ℝ) * (2 * π) := by push_cast; ring
      rw [this, Real.cos_int_mul_two_pi]
    have hsumA : ∀ t : ℝ, 0 < t → ∀ w : EuclideanSpace ℝ (Fin n),
        Summable fun x : Λ => Real.exp (-π * t * ‖(x : EuclideanSpace ℝ (Fin n)) + w‖ ^ 2) :=
      fun t ht w => (summable_exp_neg_mul_norm_add_sq Λ (a := π * t) (by positivity) w).congr
        fun _ => by ring_nf
    have hsumQ : ∀ t : ℝ, 0 < t →
        Summable fun y : dualLattice Λ =>
          Real.exp (-π * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / t) :=
      fun t ht => (summable_exp_neg_mul_norm_add_sq (dualLattice Λ) (a := π / t)
        (by positivity) 0).congr fun _ => by rw [add_zero]; ring_nf
    have key := gauss_transference_abstract (X := Λ) (Y := dualLattice Λ)
      (fun x => ‖(x : EuclideanSpace ℝ (Fin n)) + -u‖ ^ 2)
      (fun x => ‖(x : EuclideanSpace ℝ (Fin n)) + 0‖ ^ 2)
      (fun y => ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      (fun y => Real.cos (2 * π * inner ℝ (y : EuclideanSpace ℝ (Fin n)) (-u)))
      (n : ℝ) (ZLattice.covolume Λ volume)⁻¹
      (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) (fun _ => Real.abs_cos_le_one _)
      (inv_pos.mpr (ZLattice.covolume_pos Λ volume)) 0
      (fun t ht => hsumA t ht (-u)) (fun t ht => hsumA t ht 0) hsumQ
      (fun t ht => poisson_summation_gaussian_exact Λ ht (-u))
      (fun t ht => by
        rw [poisson_summation_gaussian_exact Λ ht 0]
        simp only [inner_zero_right, mul_zero, Real.cos_zero, mul_one])
      R2 (lam ^ 2) hR hl s (4 / 9) (1 / 4) hs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hlam0 : lam ≠ 0 := hlam.ne'
    have hm0' : m ≠ 0 := hm0.ne'
    have e1 : -π * s * (1 - 4 / 9) * R2 = -(2 * π / 5) * m := by
      dsimp only [s, R2]; field_simp; ring
    have e2 : -π * (1 - 1 / 4) * lam ^ 2 / s = -(25 * π / 24) * m := by
      dsimp only [s]; field_simp; ring
    have e3 : -(n : ℝ) / 2 = -m := by dsimp only [m]; ring
    rw [e1, e2, e3] at key
    have hN := banaszczyk_numeric_main
    have hA : 0 < Real.exp (-(2 * π / 5)) := Real.exp_pos _
    have hB : 0 < Real.exp (-(25 * π / 24)) := Real.exp_pos _
    have f1 := banaszczyk_factor_le (2 * π / 5) (4 / 9) m (by norm_num) hm1 (by
      rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]; linarith)
    have f2 := banaszczyk_factor_le (25 * π / 24) (1 / 4) m (by norm_num) hm1 (by
      rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]; linarith)
    rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num] at f1
    rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at f2
    linarith

/-- The **covering radius** `μ(Λ) = sup_{x ∈ ℝ^n} dist(x, Λ)` of a lattice
`Λ ⊂ EuclideanSpace ℝ (Fin n)`. -/
def coveringRadius {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⨆ x : EuclideanSpace ℝ (Fin n), Metric.infDist x (Λ : Set (EuclideanSpace ℝ (Fin n)))

/-- Every point `x ∈ ℝ^n` is within distance `(n / 2) / λ₁(Λ*)` of a lattice point `v ∈ Λ`. -/
theorem exists_lattice_point_close_to_point {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ v ∈ Λ, ‖x - v‖ * shortestNorm (dualLattice Λ) ≤ (n : ℝ) / 2 := by
  obtain ⟨y₀, hy₀_mem, hy₀_ne, hy₀_min⟩ := exists_shortest_nonzero_vector hn (dualLattice Λ)
  have hlam_eq : shortestNorm (dualLattice Λ) = ‖y₀‖ :=
    shortestNorm_eq_of_min (dualLattice Λ) hy₀_mem hy₀_ne hy₀_min
  have hlam_pos : 0 < shortestNorm (dualLattice Λ) := by
    rw [hlam_eq]; exact norm_pos_iff.mpr hy₀_ne
  refine banaszczyk_transference_key Λ hlam_pos x ?_
  intro y hyD hy_lt
  have hy0 : y = 0 := by
    by_contra hne
    have hge := hy₀_min y hyD hne
    linarith
  exact ⟨0, by simp [hy0]⟩

lemma bddAbove_infDist_lattice {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    BddAbove (Set.range fun x : EuclideanSpace ℝ (Fin n) =>
      Metric.infDist x (Λ : Set (EuclideanSpace ℝ (Fin n)))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    dsimp only
    have hx : x = 0 := Subsingleton.elim x 0
    rw [hx, Metric.infDist_zero_of_mem Λ.zero_mem]
  · obtain ⟨y₀, hy₀_mem, hy₀_ne, hy₀_min⟩ := exists_shortest_nonzero_vector hn (dualLattice Λ)
    have hlam_pos : 0 < shortestNorm (dualLattice Λ) := by
      rw [shortestNorm_eq_of_min (dualLattice Λ) hy₀_mem hy₀_ne hy₀_min]
      exact norm_pos_iff.mpr hy₀_ne
    refine ⟨(n : ℝ) / (2 * shortestNorm (dualLattice Λ)), ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨v, hv, hxv⟩ := exists_lattice_point_close_to_point hn Λ x
    have hle : ‖x - v‖ ≤ (n : ℝ) / (2 * shortestNorm (dualLattice Λ)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    exact (Metric.infDist_le_dist_of_mem hv).trans (by rwa [dist_eq_norm])

lemma coveringRadius_nonneg {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    0 ≤ coveringRadius Λ :=
  le_ciSup_of_le (bddAbove_infDist_lattice Λ) 0 Metric.infDist_nonneg

lemma infDist_le_coveringRadius {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (x : EuclideanSpace ℝ (Fin n)) :
    Metric.infDist x (Λ : Set (EuclideanSpace ℝ (Fin n))) ≤ coveringRadius Λ :=
  le_ciSup (bddAbove_infDist_lattice Λ) x

/-- Every point `x ∈ ℝ^n` has a closest lattice point `v ∈ Λ` with `‖x - v‖ ≤ coveringRadius Λ`. -/
theorem exists_mem_norm_sub_le_coveringRadius {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ v ∈ Λ, ‖x - v‖ ≤ coveringRadius Λ := by
  have hS_fin : ((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩
      Metric.closedBall 0 (‖x‖ + ‖x‖)).Finite :=
    lattice_inter_closedBall_finite Λ (‖x‖ + ‖x‖)
  let F : Finset (EuclideanSpace ℝ (Fin n)) := hS_fin.toFinset
  have h0F : (0 : EuclideanSpace ℝ (Fin n)) ∈ F := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨Λ.zero_mem, by simp⟩
  obtain ⟨v, hvF, hv_min⟩ := Finset.exists_min_image F (fun w => dist x w) ⟨0, h0F⟩
  have hvΛ : v ∈ Λ := (hS_fin.mem_toFinset.mp hvF).1
  have hv_all : ∀ w ∈ Λ, dist x v ≤ dist x w := by
    intro w hw
    by_cases hle : ‖w‖ ≤ ‖x‖ + ‖x‖
    · exact hv_min w (hS_fin.mem_toFinset.mpr ⟨hw, by simpa using hle⟩)
    · have h0 : dist x v ≤ dist x 0 := hv_min 0 h0F
      have hw_gt : dist x 0 < dist x w := by
        rw [dist_zero_right, dist_eq_norm]
        have htri : ‖w‖ ≤ ‖x - w‖ + ‖x‖ := by
          have : w = -(x - w) + x := by abel
          calc ‖w‖ = ‖-(x - w) + x‖ := by rw [← this]
            _ ≤ ‖-(x - w)‖ + ‖x‖ := norm_add_le _ _
            _ = ‖x - w‖ + ‖x‖ := by rw [norm_neg]
        linarith
      exact h0.trans hw_gt.le
  have hdist_eq : dist x v = Metric.infDist x (Λ : Set (EuclideanSpace ℝ (Fin n))) := by
    apply le_antisymm
    · rw [Metric.infDist_eq_iInf]
      exact le_ciInf fun w => hv_all w.1 w.2
    · exact Metric.infDist_le_dist_of_mem hvΛ
  refine ⟨v, hvΛ, ?_⟩
  rw [← dist_eq_norm, hdist_eq]
  exact infDist_le_coveringRadius Λ x

/-- **UNCONDITIONAL BANASZCZYK COVERING RADIUS TRANSFERENCE THEOREM (1993, Theorem 2.2)**:
For every dimension `n ≥ 1` and every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`:
`coveringRadius Λ * shortestNorm (dualLattice Λ) ≤ n / 2`! -/
theorem banaszczyk_covering_radius {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    coveringRadius Λ * shortestNorm (dualLattice Λ) ≤ (n : ℝ) / 2 := by
  obtain ⟨y₀, hy₀_mem, hy₀_ne, hy₀_min⟩ := exists_shortest_nonzero_vector hn (dualLattice Λ)
  have hlam_pos : 0 < shortestNorm (dualLattice Λ) := by
    rw [shortestNorm_eq_of_min (dualLattice Λ) hy₀_mem hy₀_ne hy₀_min]
    exact norm_pos_iff.mpr hy₀_ne
  have hcov_le : coveringRadius Λ ≤ (n : ℝ) / (2 * shortestNorm (dualLattice Λ)) := by
    refine ciSup_le fun x => ?_
    obtain ⟨v, hv, hxv⟩ := exists_lattice_point_close_to_point hn Λ x
    have hle : ‖x - v‖ ≤ (n : ℝ) / (2 * shortestNorm (dualLattice Λ)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    exact (Metric.infDist_le_dist_of_mem hv).trans (by rwa [dist_eq_norm])
  have hmul := mul_le_mul_of_nonneg_right hcov_le hlam_pos.le
  have hrhs : (n : ℝ) / (2 * shortestNorm (dualLattice Λ)) * shortestNorm (dualLattice Λ) =
      (n : ℝ) / 2 := by field_simp [hlam_pos.ne']
  linarith

/-- Helper: `shortestNorm Λ = Stage2SiegelReduction.lambda1 Λ` for every full-rank lattice `Λ`
(`n ≥ 1`). -/
theorem shortestNorm_eq_lambda1 {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    shortestNorm Λ = lambda1 Λ := by
  have hΛ0 : Λ ≠ ⊥ := by
    intro h0
    have hrk : rk Λ = n := by unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
    rw [h0] at hrk
    simp [rk] at hrk
    omega
  rw [← succMin_zero_eq_lambda1 Λ hΛ0, ← successiveMinimum_closedBall_zero_eq_shortestNorm hn Λ]
  have h := succMin_eq_stage10_successiveMinimum Λ ⟨0, hn⟩
  convert h.symm using 2
  ext; rfl

/-- Covering radius transference stated with `Stage2SiegelReduction.lambda1`. -/
theorem banaszczyk_covering_radius_lambda1 {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    coveringRadius Λ * lambda1 (dualLattice Λ) ≤ (n : ℝ) / 2 := by
  rw [← shortestNorm_eq_lambda1 hn (dualLattice Λ)]
  exact banaszczyk_covering_radius hn Λ

/-- Helper: the real span of all lattice vectors strictly shorter than `λ_{k+1}(Λ)` has dimension
strictly less than `k + 1`. -/
private lemma finrank_span_lt_successiveMinimum {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (k : Fin n) :
    Module.finrank ℝ (Submodule.span ℝ
      {x : EuclideanSpace ℝ (Fin n) |
        x ∈ Λ ∧ ‖x‖ < successiveMinimum (Metric.closedBall 0 1) Λ k}) < k.1 + 1 := by
  by_contra hcon
  push Not at hcon
  set lam : ℝ := successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ k
  obtain ⟨s, hsS, hsspan, hsli⟩ := exists_linearIndependent ℝ
    {x : EuclideanSpace ℝ (Fin n) | x ∈ Λ ∧ ‖x‖ < lam}
  have hsfin : s.Finite := hsli.setFinite
  obtain ⟨T, hTs⟩ : ∃ T : Finset (EuclideanSpace ℝ (Fin n)), (T : Set _) = s :=
    ⟨hsfin.toFinset, hsfin.coe_toFinset⟩
  have hTli : LinearIndependent ℝ (Subtype.val : T → EuclideanSpace ℝ (Fin n)) := by
    have heq : (Subtype.val : T → EuclideanSpace ℝ (Fin n)) =
        (Subtype.val : s → EuclideanSpace ℝ (Fin n)) ∘ Equiv.setCongr hTs := rfl
    rw [heq]
    exact hsli.comp (Equiv.setCongr hTs) (Equiv.setCongr hTs).injective
  have hrange : Set.range (Subtype.val : T → EuclideanSpace ℝ (Fin n)) = s := by
    rw [← hTs]; ext x; simp
  have hcard : Module.finrank ℝ (Submodule.span ℝ s) = T.card := by
    rw [← hrange]
    simpa only [Fintype.card_coe] using finrank_span_eq_card hTli
  rw [hsspan] at hcard
  have hle : k.1 + 1 ≤ T.card := by omega
  obtain ⟨e⟩ : Nonempty (Fin (k.1 + 1) ↪ T) :=
    ⟨(Fin.castLEEmb hle).trans T.equivFin.symm.toEmbedding⟩
  let v : Fin (k.1 + 1) → EuclideanSpace ℝ (Fin n) := fun j => (e j : EuclideanSpace ℝ (Fin n))
  have hvli : LinearIndependent ℝ v := hTli.comp e e.injective
  have hvS : ∀ j, v j ∈ Λ ∧ ‖v j‖ < lam := fun j => hsS (hTs ▸ (e j).2)
  obtain ⟨j₀, -, hj₀_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (k.1 + 1))) (fun j => ‖v j‖)
      ⟨⟨0, Nat.succ_pos _⟩, Finset.mem_univ _⟩
  have ht_pos : 0 < ‖v j₀‖ := norm_pos_iff.mpr (hvli.ne_zero j₀)
  have ht_lt : ‖v j₀‖ < lam := (hvS j₀).2
  have ht_mem : ‖v j₀‖ ∈ { r : ℝ | 0 < r ∧ ∃ w : Fin (k.1 + 1) → EuclideanSpace ℝ (Fin n),
      (∀ j, w j ∈ Λ) ∧ LinearIndependent ℝ w ∧
      ∀ j, w j ∈ r • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 } := by
    refine ⟨ht_pos, v, fun j => (hvS j).1, hvli, fun j => ?_⟩
    refine ⟨‖v j₀‖⁻¹ • v j, ?_, smul_inv_smul₀ ht_pos.ne' (v j)⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr ht_pos.le), inv_mul_le_iff₀ ht_pos, mul_one]
    exact hj₀_max j (Finset.mem_univ j)
  have hinf : lam ≤ ‖v j₀‖ := by
    dsimp only [lam, successiveMinimum]
    exact csInf_le ⟨0, fun _ hr => hr.1.le⟩ ht_mem
  exact lt_irrefl lam (lt_of_le_of_lt hinf ht_lt)

/-- **UNCONDITIONAL BANASZCZYK GENERAL TRANSFERENCE THEOREM (1993, Theorem 2.1)**:
For EVERY dimension `n ≥ 1`, every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`, and every
index `i : Fin n` (0-indexed, corresponding to `λ_{i+1}(Λ) * λ_{n-i}(Λ*) ≤ n`):
`successiveMinimum B_n Λ i * successiveMinimum B_n (dualLattice Λ) ⟨n - 1 - i, _⟩ ≤ n`! -/
theorem banaszczyk_transference_general {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (i : Fin n) :
    successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ i *
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
        (dualLattice Λ) ⟨n - 1 - i.1, by omega⟩ ≤ (n : ℝ) := by
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1
  have h0B : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior B := by
    rw [mem_interior_iff_mem_nhds]; exact Metric.closedBall_mem_nhds 0 zero_lt_one
  let j : Fin n := ⟨n - 1 - i.1, by omega⟩
  set A : ℝ := successiveMinimum B Λ i
  set Bmin : ℝ := successiveMinimum B (dualLattice Λ) j
  have hBpos : 0 < Bmin := successiveMinimum_pos Metric.isBounded_closedBall h0B (dualLattice Λ) j
  set Sd : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    Submodule.span ℝ {y : EuclideanSpace ℝ (Fin n) | y ∈ dualLattice Λ ∧ ‖y‖ < Bmin}
  set V' : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    Submodule.span ℝ {x : EuclideanSpace ℝ (Fin n) | x ∈ Λ ∧ ‖x‖ < A}
  have hSd : Module.finrank ℝ Sd < j.1 + 1 := finrank_span_lt_successiveMinimum (dualLattice Λ) j
  have hV' : Module.finrank ℝ V' < i.1 + 1 := finrank_span_lt_successiveMinimum Λ i
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have h1 : Module.finrank ℝ Sd + Module.finrank ℝ Sdᗮ = n :=
    (Submodule.finrank_add_finrank_orthogonal Sd).trans hE
  have h2 : Module.finrank ℝ V' + Module.finrank ℝ V'ᗮ = n :=
    (Submodule.finrank_add_finrank_orthogonal V').trans hE
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Sdᗮ V'ᗮ
  have h4 : Module.finrank ℝ (Sdᗮ ⊔ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) ≤ n :=
    (Submodule.finrank_le _).trans hE.le
  have hne : (Sdᗮ ⊓ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) ≠ ⊥ := by
    intro h0; rw [h0, finrank_bot] at h3; dsimp only [j] at hSd; omega
  obtain ⟨u0, hu0W, hu0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hu0pos : 0 < ‖u0‖ := norm_pos_iff.2 hu0ne
  suffices hAB : A ≤ (n : ℝ) / Bmin by rwa [le_div_iff₀ hBpos] at hAB
  apply le_of_forall_pos_le_add
  intro ε hε
  set c : ℝ := (n : ℝ) / (2 * Bmin) + ε / 2
  have hc : 0 < c := by positivity
  set u : EuclideanSpace ℝ (Fin n) := (c / ‖u0‖) • u0
  have hun : ‖u‖ = c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc hu0pos), div_mul_cancel₀ _ hu0pos.ne']
  have huW : u ∈ (Sdᗮ ⊓ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :=
    Submodule.smul_mem _ _ hu0W
  have huSd : u ∈ Sdᗮ := (Submodule.mem_inf.1 huW).1
  have huV : u ∈ V'ᗮ := (Submodule.mem_inf.1 huW).2
  obtain ⟨l, hlM, hl⟩ := banaszczyk_transference_key Λ hBpos u (fun y hyD hyB => by
    have hySd : y ∈ Sd := Submodule.subset_span ⟨hyD, hyB⟩
    exact ⟨0, by rw [Submodule.inner_left_of_mem_orthogonal hySd huSd]; simp⟩)
  have hul : ‖u - l‖ ≤ (n : ℝ) / (2 * Bmin) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hlV : l ∉ V' := by
    intro hlV
    have hin : inner ℝ u l = 0 := Submodule.inner_left_of_mem_orthogonal hlV huV
    have hsq : ‖u - l‖ ^ 2 = ‖u‖ ^ 2 + ‖l‖ ^ 2 := by rw [@norm_sub_sq_real, hin]; ring
    have hsq2 : ‖u‖ ^ 2 ≤ ‖u - l‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg ‖l‖]
    have hge : ‖u‖ ≤ ‖u - l‖ := by nlinarith [norm_nonneg (u - l), norm_nonneg u]
    dsimp only [c] at hun
    linarith
  have hlA : A ≤ ‖l‖ := by
    by_contra hlt; push Not at hlt
    exact hlV (Submodule.subset_span ⟨hlM, hlt⟩)
  have htri : ‖l‖ ≤ ‖u‖ + ‖u - l‖ := by
    calc ‖l‖ = ‖u - (u - l)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - l‖ := norm_sub_le _ _
  have hhalf : (n : ℝ) / (2 * Bmin) + (n : ℝ) / (2 * Bmin) = (n : ℝ) / Bmin := by
    field_simp [hBpos.ne']; ring
  dsimp only [c] at hun
  linarith

/-- **UNCONDITIONAL BANASZCZYK `λ₁(Λ) * λₙ(Λ*) ≤ n` TRANSFERENCE THEOREM (Two-Sided Sandwich)**:
For every `n ≥ 1` and every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`:
`1 ≤ λ₁(Λ) * λₙ(Λ*) ≤ n` and `1 ≤ λₙ(Λ) * λ₁(Λ*) ≤ n`. -/
theorem banaszczyk_transference_lambda1_lambdan {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    1 ≤ shortestNorm Λ *
        successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
          (dualLattice Λ) ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ ∧
    shortestNorm Λ *
        successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
          (dualLattice Λ) ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ ≤ (n : ℝ) ∧
    successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
        Λ ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ * shortestNorm (dualLattice Λ) ≤ (n : ℝ) := by
  have h1 := banaszczyk_transference_general hn Λ ⟨0, hn⟩
  have h2 := banaszczyk_transference_general hn Λ ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
  rw [successiveMinimum_closedBall_zero_eq_shortestNorm hn Λ] at h1
  have hidx1 : (⟨n - 1 - 0, by omega⟩ : Fin n) = ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
    ext; simp
  have hidx2 : (⟨n - 1 - (n - 1), by omega⟩ : Fin n) = ⟨0, hn⟩ := by
    ext; simp
  rw [hidx1] at h1
  rw [hidx2, successiveMinimum_closedBall_zero_eq_shortestNorm hn (dualLattice Λ)] at h2
  have hlow : 1 ≤ shortestNorm Λ *
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
        (dualLattice Λ) ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
    have hD0 : dualLattice Λ ≠ ⊥ := by
      intro h0
      have hrk : rk (dualLattice Λ) = n := by
        unfold rk; rw [ZLattice.rank ℝ (dualLattice Λ), finrank_euclideanSpace_fin]
      rw [h0] at hrk; simp [rk] at hrk; omega
    have hlow' := one_le_lambda1_dualLat_mul_succMin_last (dualLattice Λ) hD0
    dsimp only at hlow'
    rw [← dualLattice_eq_dualLat (dualLattice Λ), dualLattice_dualLattice Λ] at hlow'
    rw [shortestNorm_eq_lambda1 hn Λ]
    have hsucc : succMin (dualLattice Λ)
        ⟨rk (dualLattice Λ) - 1, Nat.sub_lt (rk_pos_of_ne_bot _ hD0) zero_lt_one⟩ =
        successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
          (dualLattice Λ) ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      have h := succMin_eq_stage10_successiveMinimum (dualLattice Λ)
        ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
      convert h using 2
      ext
      simp only [Fin.val_cast]
      have hrk : rk (dualLattice Λ) = n := by
        unfold rk; rw [ZLattice.rank ℝ (dualLattice Λ), finrank_euclideanSpace_fin]
      rw [hrk]
    rwa [hsucc] at hlow'
  exact ⟨hlow, h1, h2⟩

/-- **GENERAL ISOMETRIC TRANSFER OF BANASZCZYK TRANSFERENCE TO ARBITRARY INNER PRODUCT SPACES**:
For ANY finite-dimensional real inner product space `E`, ANY nonzero discrete lattice `L ⊂ E`
(`r = rk L > 0`), and ANY index `i : Fin r`:
`succMin L i * succMin (dualLat L) ⟨r - 1 - i, _⟩ ≤ r`! -/
theorem banaszczyk_transference_succMin_general
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    (i : Fin (rk L)) :
    let _ := discreteTopology_dualLat L
    succMin L i *
      succMin (dualLat L) ⟨rk L - 1 - i.1, by rw [rk_dualLat L]; omega⟩ ≤ (rk L : ℝ) := by
  intro _
  let r := rk L
  have hr : 0 < r := rk_pos_of_ne_bot L hL0
  let V := Submodule.span ℝ (L : Set E)
  have hdim : Module.finrank ℝ V = r := (finrank_int_eq_finrank_real_span L).symm
  let e : OrthonormalBasis (Fin r) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivOfCardEq (by simp [hdim]))
  let iso : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := e.repr
  let L₀ : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin r)) := L₀.map (iso.toLinearMap.restrictScalars ℤ)
  let eL : L ≃ₗ[ℤ] Λ :=
    { toFun := fun x => ⟨iso ⟨x.1, Submodule.subset_span x.2⟩,
        ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2, rfl⟩⟩
      invFun := fun y => ⟨(iso.symm y.1 : E), by
        rcases y.2 with ⟨v, hv, hvEq⟩
        have hvy : iso.symm y.1 = v := by rw [← hvEq]; simp
        rw [hvy]; exact hv⟩
      map_add' := fun a b => Subtype.ext (by
        change iso ((⟨a.1, Submodule.subset_span a.2⟩ : V) + ⟨b.1, Submodule.subset_span b.2⟩) =
          iso ⟨a.1, Submodule.subset_span a.2⟩ + iso ⟨b.1, Submodule.subset_span b.2⟩
        exact map_add iso _ _)
      map_smul' := fun c a => Subtype.ext (by
        change iso (c • (⟨a.1, Submodule.subset_span a.2⟩ : V)) =
          c • iso ⟨a.1, Submodule.subset_span a.2⟩
        exact map_zsmul iso c _)
      left_inv := fun _ => Subtype.ext (by simp)
      right_inv := fun _ => Subtype.ext (by simp) }
  have : DiscreteTopology Λ :=
    DiscreteTopology.of_continuous_injective (f := eL.symm)
      (Continuous.subtype_mk
        (continuous_subtype_val.comp (iso.symm.continuous.comp continuous_subtype_val)) _)
      eL.symm.injective
  have hspanΛ : Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin r))) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have hmem : iso.symm y ∈ Submodule.span ℝ (L₀ : Set V) := by
      have : Submodule.span ℝ (L₀ : Set V) = ⊤ := Submodule.span_span_coe_preimage
      rw [this]; trivial
    have hmap : Submodule.map iso.toLinearMap (Submodule.span ℝ (L₀ : Set V)) =
        Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin r))) := by
      rw [Submodule.map_span]; rfl
    have : iso (iso.symm y) ∈ Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin r))) := by
      rw [← hmap]; exact ⟨iso.symm y, hmem, rfl⟩
    simpa using this
  have : IsZLattice ℝ Λ := ⟨hspanΛ⟩
  -- Check that `iso` transports `dualLat L` onto `dualLattice Λ`!
  have hmem_Λ : ∀ v : V, (v : E) ∈ L ↔ iso v ∈ Λ := by
    intro v; constructor
    · intro hv; exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, hwEq⟩; have := iso.injective hwEq; rwa [← this]
  have hmem_dual : ∀ w : V, (w : E) ∈ dualLat L ↔ iso w ∈ dualLattice Λ := by
    intro w; constructor
    · rintro ⟨_, hwZ⟩ x hxΛ
      rcases hxΛ with ⟨v, hvL, rfl⟩
      obtain ⟨k, hk⟩ := hwZ (v : E) hvL
      refine ⟨k, ?_⟩
      change inner ℝ (iso v) (iso w) = (k : ℝ)
      rw [iso.inner_map_map, real_inner_comm]
      exact hk
    · intro hwD
      refine ⟨w.2, fun x hxL => ?_⟩
      have hxV : x ∈ V := Submodule.subset_span hxL
      obtain ⟨k, hk⟩ := hwD (iso ⟨x, hxV⟩) ((hmem_Λ ⟨x, hxV⟩).mp hxL)
      refine ⟨k, ?_⟩
      change inner ℝ w ⟨x, hxV⟩ = (k : ℝ)
      rw [← iso.inner_map_map w ⟨x, hxV⟩, real_inner_comm]
      exact hk
  -- Identify `succMin L k = successiveMinimum B_r Λ k` and `succMin (dualLat L) k = successiveMinimum B_r (dualLattice Λ) k`.
  have hsuccL : ∀ k : Fin r,
      succMin L k = successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1) Λ k := by
    intro k
    rw [← succMin_eq_stage10_successiveMinimum Λ k]
    unfold succMin; congr 1; ext R
    simp only [Fin.val_cast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hR, v, hvL, hvli, hvn⟩
      refine ⟨hR, fun j => iso ⟨v j, Submodule.subset_span (hvL j)⟩,
        fun j => (hmem_Λ _).mp (hvL j), ?_, fun j => by simpa using hvn j⟩
      have hvliV : LinearIndependent ℝ (fun j => (⟨v j, Submodule.subset_span (hvL j)⟩ : V)) :=
        hvli.of_comp V.subtype
      exact hvliV.map' iso.toLinearMap iso.ker
    · rintro ⟨hR, w, hwΛ, hwli, hwn⟩
      refine ⟨hR, fun j => (iso.symm (w j) : E), fun j => (hmem_Λ _).mpr (by simpa using hwΛ j),
        ?_, fun j => by
          change ‖iso.symm (w j)‖ ≤ R
          rw [iso.symm.norm_map]; exact hwn j⟩
      exact (hwli.map' iso.symm.toLinearMap iso.symm.ker).map' V.subtype (Submodule.ker_subtype V)
  have hsuccD : ∀ k : Fin r,
      succMin (dualLat L) (k.cast (rk_dualLat L).symm) =
        successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1) (dualLattice Λ) k := by
    intro k
    rw [← succMin_eq_stage10_successiveMinimum (dualLattice Λ) k]
    unfold succMin; congr 1; ext R
    simp only [Fin.val_cast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hR, v, hvD, hvli, hvn⟩
      refine ⟨hR, fun j => iso ⟨v j, (hvD j).1⟩,
        fun j => (hmem_dual ⟨v j, (hvD j).1⟩).mp (hvD j), ?_, fun j => by simpa using hvn j⟩
      have hvliV : LinearIndependent ℝ (fun j => (⟨v j, (hvD j).1⟩ : V)) := hvli.of_comp V.subtype
      exact hvliV.map' iso.toLinearMap iso.ker
    · rintro ⟨hR, w, hwD, hwli, hwn⟩
      refine ⟨hR, fun j => (iso.symm (w j) : E),
        fun j => (hmem_dual (iso.symm (w j))).mpr (by simpa using hwD j),
        ?_, fun j => by
          change ‖iso.symm (w j)‖ ≤ R
          rw [iso.symm.norm_map]; exact hwn j⟩
      exact (hwli.map' iso.symm.toLinearMap iso.symm.ker).map' V.subtype (Submodule.ker_subtype V)
  have hB := banaszczyk_transference_general hr Λ i
  rw [← hsuccL i] at hB
  have hD_eq : successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1)
      (dualLattice Λ) ⟨r - 1 - i.1, by omega⟩ =
      succMin (dualLat L) ⟨r - 1 - i.1, by rw [rk_dualLat L]; omega⟩ := by
    have h := (hsuccD ⟨r - 1 - i.1, by omega⟩).symm
    convert h using 2
    ext; simp
  rw [hD_eq] at hB
  exact hB

end BanaszczykTransferenceTheorems

/-! ## Section 5: Direct `O(log n)` Arakelov Slope-Gap Bridge (`Stage10` + `Stage11`) -/

section ArakelovSlopeGapBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Sharp `O(log r)` Equivalence Between `muMin L` and `-log λ_r(L)`**:
for EVERY nonzero discrete lattice `L ⊂ E` (`r = rk L > 0`), combining `Stage4ArakelovBost`
with Banaszczyk's Transference Theorem (`λ_r(L) * λ₁(L*) ≤ r`):
`-log λ_r(L) ≤ muMin L ≤ -log λ_r(L) + log r`! -/
theorem banaszczyk_muMin_equiv_neg_log_succMin_last
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    let r := rk L
    let hr : 0 < r := rk_pos_of_ne_bot L hL0;
    -Real.log (succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩) ≤ muMin L ∧
    muMin L ≤ -Real.log (succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩) + Real.log (r : ℝ) := by
  intro r hr
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    have hbot : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    rw [h0, hbot] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  refine ⟨neg_log_succMin_last_le_muMin L hL0, ?_⟩
  have htr := banaszczyk_transference_succMin_general L hL0 ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩
  dsimp only at htr
  have hidx0 : (⟨r - 1 - (r - 1), by rw [rk_dualLat L]; omega⟩ : Fin (rk (dualLat L))) =
      ⟨0, rk_pos_of_ne_bot (dualLat L) hDL0⟩ := by ext; simp
  rw [hidx0, succMin_zero_eq_lambda1 (dualLat L) hDL0] at htr
  have hsucc_pos : 0 < succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ := succMin_pos L hL0 _
  have hlamD_pos : 0 < lambda1 (dualLat L) := lambda1_pos (dualLat L) hDL0
  have hlog := Real.log_le_log (mul_pos hsucc_pos hlamD_pos) htr
  rw [Real.log_mul hsucc_pos.ne' hlamD_pos.ne'] at hlog
  have hmuMin_le := (muMin_dual_lambda1_bounds L hL0).2
  linarith

/-- **Sharp `O(log r)` Equivalence Between `muMax (dualLat L)` and `log λ_r(L)`**:
`log λ_r(L) - log r ≤ muMax (dualLat L) ≤ log λ_r(L)`! -/
theorem banaszczyk_muMax_dual_equiv_log_succMin_last
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    let _ := discreteTopology_dualLat L
    let r := rk L
    let hr : 0 < r := rk_pos_of_ne_bot L hL0
    Real.log (succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩) - Real.log (r : ℝ) ≤
      muMax (dualLat L) ∧
    muMax (dualLat L) ≤ Real.log (succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩) := by
  intro _ r hr
  have h := banaszczyk_muMin_equiv_neg_log_succMin_last L hL0
  have hdual := muMax_dualLat L hL0
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- **Unconditional `O(log r)` Arakelov Slope-Gap & Dual-Slope-Sum Sandwich**:
for EVERY nonzero discrete lattice `L ⊂ E` (`r = rk L > 0`):
1. `muMax L + muMax (dualLat L) = muMax L - muMin L`,
2. `log (λ_r(L) / λ₁(L)) - log r ≤ muMax L + muMax (dualLat L) ≤ log (λ_r(L) / λ₁(L)) + (1/2) log r`,
3. `muMax L + muMax (dualLat L) ≤ -log (λ₁(L) * λ₁(dualLat L)) + log r`,
4. `muMax L - slope L ≤ -log (λ₁(L) * λ₁(dualLat L)) + log r`! -/
theorem banaszczyk_muMax_add_muMax_dual_sandwich
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥) :
    let _ := discreteTopology_dualLat L
    let r := rk L
    let hr : 0 < r := rk_pos_of_ne_bot L hL0
    muMax L + muMax (dualLat L) = muMax L - muMin L ∧
    Real.log (succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ / lambda1 L) - Real.log (r : ℝ) ≤
      muMax L + muMax (dualLat L) ∧
    muMax L + muMax (dualLat L) ≤
      Real.log (succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ / lambda1 L) +
        (1 / 2) * Real.log (r : ℝ) ∧
    muMax L + muMax (dualLat L) ≤
      -Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (r : ℝ) ∧
    muMax L - ArakelovCovolume.slope L ≤
      -Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (r : ℝ) := by
  intro _ r hr
  have : DiscreteTopology (dualLat L) := discreteTopology_dualLat L
  have hDL0 : dualLat L ≠ ⊥ := by
    intro h0
    have h1 : rk L = rk (dualLat L) := (rk_dualLat L).symm
    have hbot : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    rw [h0, hbot] at h1
    have hpos := rk_pos_of_ne_bot L hL0
    omega
  have heq : muMax L + muMax (dualLat L) = muMax L - muMin L := by
    rw [muMax_dualLat L hL0]; ring
  have hlamL : 0 < lambda1 L := lambda1_pos L hL0
  have hlamD : 0 < lambda1 (dualLat L) := lambda1_pos (dualLat L) hDL0
  have hsucc : 0 < succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ := succMin_pos L hL0 _
  have hL := RHDirect.Stage3ThetaSiegelBridge.muMax_le_half_log_rk_sub_log_lambda1 L hL0
  have hD := RHDirect.Stage3ThetaSiegelBridge.muMax_le_half_log_rk_sub_log_lambda1 (dualLat L) hDL0
  rw [rk_dualLat L] at hD
  have hmin := banaszczyk_muMin_equiv_neg_log_succMin_last L hL0
  have hlog_div : Real.log (succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩ / lambda1 L) =
      Real.log (succMin L ⟨r - 1, Nat.sub_lt hr zero_lt_one⟩) - Real.log (lambda1 L) :=
    Real.log_div hsucc.ne' hlamL.ne'
  have hlog_mul : Real.log (lambda1 L * lambda1 (dualLat L)) =
      Real.log (lambda1 L) + Real.log (lambda1 (dualLat L)) :=
    Real.log_mul hlamL.ne' hlamD.ne'
  have hslope : muMin L ≤ ArakelovCovolume.slope L := (muMin_le_slope_le_muMax L hL0).1
  refine ⟨heq, ?_, ?_, ?_, ?_⟩
  · rw [heq, hlog_div]; linarith [hL.1, hmin.2]
  · rw [heq, hlog_div]; linarith [hL.2, hmin.1]
  · rw [hlog_mul]; linarith [hL.2, hD.2]
  · rw [hlog_mul]; linarith [hL.2, hD.2, heq, hslope]

/-- **SHARP `O(log r)` ARAKELOV SLOPE-GAP BRIDGE (`banaszczyk_slope_gap_O_log`)**:
Whenever `c ≤ λ₁(L) * λ₁(L*)` (`0 < c`, in particular `c = 1` whenever `λ₁(L) ≥ 1` and
`λ₁(L*) ≥ 1`, e.g., integral/normalized lattices):
- `muMax L - ArakelovCovolume.slope L ≤ Real.log (rk L) - Real.log c`,
- `muMax L + muMax (dualLat L) ≤ Real.log (rk L) - Real.log c`!
At `c = 1`, both `muMax L - slope L ≤ log (rk L)` and `muMax L + muMax (dualLat L) ≤ log (rk L)`,
exponentially beating LLL's `O(rk L)` defect! -/
theorem banaszczyk_slope_gap_O_log
    (L : Submodule ℤ E) [DiscreteTopology L] (hL0 : L ≠ ⊥)
    {c : ℝ} (hc : 0 < c) (hprod : c ≤ lambda1 L * lambda1 (dualLat L)) :
    let _ := discreteTopology_dualLat L
    muMax L - ArakelovCovolume.slope L ≤ Real.log (rk L : ℝ) - Real.log c ∧
    muMax L + muMax (dualLat L) ≤ Real.log (rk L : ℝ) - Real.log c := by
  intro _
  have hS := banaszczyk_muMax_add_muMax_dual_sandwich L hL0
  have hlog : Real.log c ≤ Real.log (lambda1 L * lambda1 (dualLat L)) := Real.log_le_log hc hprod
  exact ⟨by linarith [hS.2.2.2.2], by linarith [hS.2.2.2.1]⟩

/-- Specialization of `banaszczyk_slope_gap_O_log` to `1 ≤ λ₁(Λ) * λ₁(dualLattice Λ)` on
`EuclideanSpace ℝ (Fin n)` (`n ≥ 1`):
`muMax Λ - slope Λ ≤ log n` AND `muMax Λ + muMax (dualLattice Λ) ≤ log n`! -/
theorem banaszczyk_slope_gap_O_log_euclidean {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hprod : 1 ≤ shortestNorm Λ * shortestNorm (dualLattice Λ)) :
    muMax Λ - ArakelovCovolume.slope Λ ≤ Real.log (n : ℝ) ∧
    muMax Λ + muMax (dualLattice Λ) ≤ Real.log (n : ℝ) := by
  have hΛ0 : Λ ≠ ⊥ := by
    intro h0
    have hrk : rk Λ = n := by unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
    rw [h0] at hrk; simp [rk] at hrk; omega
  have hrk : rk Λ = n := by unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
  have hprod' : 1 ≤ lambda1 Λ * lambda1 (dualLat Λ) := by
    rw [← shortestNorm_eq_lambda1 hn Λ, ← dualLattice_eq_dualLat Λ,
      ← shortestNorm_eq_lambda1 hn (dualLattice Λ)]
    exact hprod
  have h := banaszczyk_slope_gap_O_log Λ hΛ0 zero_lt_one hprod'
  rw [Real.log_one, sub_zero, hrk, ← dualLattice_eq_dualLat Λ] at h
  exact h

/-- **Banaszczyk Covering-Radius vs. Arakelov Slope & Last Successive Minimum**:
for every `n ≥ 1` and every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`:
1. `coveringRadius Λ ≤ (n / 2) * exp (muMax (dualLattice Λ))`,
2. `coveringRadius Λ ≤ (n / 2) * λₙ(Λ)` (polynomial `n / 2`, exponentially beating LLL/Babai's
   `2^{n/2}`!),
3. `0 < coveringRadius Λ → muMin Λ ≤ -log (coveringRadius Λ) + log (n / 2)`. -/
theorem banaszczyk_covering_radius_slope_bounds {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    coveringRadius Λ ≤ ((n : ℝ) / 2) * Real.exp (muMax (dualLattice Λ)) ∧
    coveringRadius Λ ≤ ((n : ℝ) / 2) *
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ
        ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ ∧
    (0 < coveringRadius Λ →
      muMin Λ ≤ -Real.log (coveringRadius Λ) + Real.log ((n : ℝ) / 2)) := by
  have hΛ0 : Λ ≠ ⊥ := by
    intro h0
    have hrk : rk Λ = n := by unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
    rw [h0] at hrk; simp [rk] at hrk; omega
  have hD0 : dualLattice Λ ≠ ⊥ := by
    intro h0
    have hrk : rk (dualLattice Λ) = n := by
      unfold rk; rw [ZLattice.rank ℝ (dualLattice Λ), finrank_euclideanSpace_fin]
    rw [h0] at hrk; simp [rk] at hrk; omega
  have hcov := banaszczyk_covering_radius_lambda1 hn Λ
  have hlamD : 0 < lambda1 (dualLattice Λ) := lambda1_pos (dualLattice Λ) hD0
  have h1_le_exp : (lambda1 (dualLattice Λ))⁻¹ ≤ Real.exp (muMax (dualLattice Λ)) := by
    have hlo := (RHDirect.Stage3ThetaSiegelBridge.muMax_le_half_log_rk_sub_log_lambda1
      (dualLattice Λ) hD0).1
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_neg, Real.exp_log hlamD] at h
  have hcov_div : coveringRadius Λ ≤ ((n : ℝ) / 2) * (lambda1 (dualLattice Λ))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hlamD]; exact hcov
  have h1 : coveringRadius Λ ≤ ((n : ℝ) / 2) * Real.exp (muMax (dualLattice Λ)) :=
    hcov_div.trans (mul_le_mul_of_nonneg_left h1_le_exp (by positivity))
  have h2 : coveringRadius Λ ≤ ((n : ℝ) / 2) *
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ
        ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
    have hlow := one_le_lambda1_dualLat_mul_succMin_last Λ hΛ0
    dsimp only at hlow
    rw [← dualLattice_eq_dualLat Λ] at hlow
    have hsucc : succMin Λ ⟨rk Λ - 1, Nat.sub_lt (rk_pos_of_ne_bot Λ hΛ0) zero_lt_one⟩ =
        successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ
          ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      have h := succMin_eq_stage10_successiveMinimum Λ ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
      convert h using 2
      ext
      simp only [Fin.val_cast]
      have hrk : rk Λ = n := by unfold rk; rw [ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]
      rw [hrk]
    rw [hsucc] at hlow
    have hinv_le : (lambda1 (dualLattice Λ))⁻¹ ≤
        successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ
          ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      rw [inv_le_iff_one_le_mul₀' hlamD]; exact hlow
    exact hcov_div.trans (mul_le_mul_of_nonneg_left hinv_le (by positivity))
  refine ⟨h1, h2, ?_⟩
  intro hcr_pos
  have hlog := Real.log_le_log (mul_pos hcr_pos hlamD) hcov
  rw [Real.log_mul hcr_pos.ne' hlamD.ne'] at hlog
  have hmu := (muMin_dual_lambda1_bounds Λ hΛ0).2
  rw [← dualLattice_eq_dualLat Λ] at hmu
  linarith

/-- **Banaszczyk Average Dual Log-Successive-Minima Bound**:
for every `n ≥ 1` and every full-rank lattice `Λ ⊂ EuclideanSpace ℝ (Fin n)`:
`(1 / n) * ∑_{i=0}^{n-1} (log λ_{i+1}(Λ) + log λ_{i+1}(Λ*)) ≤ log n`! -/
theorem banaszczyk_avg_dual_log_succMin_le_log {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    let B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1
    (∑ i : Fin n,
      (Real.log (successiveMinimum B Λ i) +
       Real.log (successiveMinimum B (dualLattice Λ) i))) / (n : ℝ) ≤
      Real.log (n : ℝ) := by
  intro B
  have h0B : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior B := by
    rw [mem_interior_iff_mem_nhds]; exact Metric.closedBall_mem_nhds 0 zero_lt_one
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  -- Reindex the dual sum by `i ↦ ⟨n - 1 - i, _⟩`.
  let rev : Fin n ≃ Fin n :=
    { toFun := fun i => ⟨n - 1 - i.1, by omega⟩
      invFun := fun i => ⟨n - 1 - i.1, by omega⟩
      left_inv := fun i => by ext; dsimp; omega
      right_inv := fun i => by ext; dsimp; omega }
  have hsum_rev : ∑ i : Fin n, Real.log (successiveMinimum B (dualLattice Λ) i) =
      ∑ i : Fin n, Real.log (successiveMinimum B (dualLattice Λ) (rev i)) :=
    (Equiv.sum_comp rev fun i => Real.log (successiveMinimum B (dualLattice Λ) i)).symm
  rw [Finset.sum_add_distrib, hsum_rev, ← Finset.sum_add_distrib]
  have hterm : ∀ i : Fin n,
      Real.log (successiveMinimum B Λ i) +
        Real.log (successiveMinimum B (dualLattice Λ) (rev i)) ≤ Real.log (n : ℝ) := by
    intro i
    have hpos1 := successiveMinimum_pos Metric.isBounded_closedBall h0B Λ i
    have hpos2 := successiveMinimum_pos Metric.isBounded_closedBall h0B (dualLattice Λ) (rev i)
    rw [← Real.log_mul hpos1.ne' hpos2.ne']
    exact Real.log_le_log (mul_pos hpos1 hpos2) (banaszczyk_transference_general hn Λ i)
  have hsum_le : ∑ i : Fin n,
      (Real.log (successiveMinimum B Λ i) +
       Real.log (successiveMinimum B (dualLattice Λ) (rev i))) ≤
      (n : ℝ) * Real.log (n : ℝ) := by
    calc _ ≤ ∑ _i : Fin n, Real.log (n : ℝ) := Finset.sum_le_sum fun i _ => hterm i
      _ = (n : ℝ) * Real.log (n : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_le_iff₀ hn_pos]
  linarith

/-- **Banaszczyk `O(log r)` Ceiling `hhBanaszczyk`** — direct drop-in upgrade of
`Stage11BostDworkSqueeze.hhMinkowski`, eliminating `λ_r` completely in favor of
`-log (λ₁(L) * λ₁(L*)) + log (rk L)`! -/
def hhBanaszczyk {ECC : Type*} [NormedAddCommGroup ECC] [InnerProductSpace ℝ ECC]
    [FiniteDimensional ℝ ECC]
    (L : Submodule ℤ ECC) [DiscreteTopology L]
    {W : Type*} [Fintype W] (d cCC h : W → ℝ) : ℝ :=
  max 1
    (-Real.log (lambda1 L * lambda1 (dualLat L)) + Real.log (rk L : ℝ) +
      RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u))

/-- **Direct Wiring into `Stage11BostDworkSqueeze`**: automatic discharge of all three `hhBound`
inequalities from `hhBanaszczyk`, `bost_slope_inequality`, and
`banaszczyk_muMax_add_muMax_dual_sandwich` with an `O(log r)` rank penalty instead of LLL's `O(r)`! -/
theorem hhBound_of_banaszczyk_transference
    {EN ECC : Type*} [NormedAddCommGroup EN] [InnerProductSpace ℝ EN] [FiniteDimensional ℝ EN]
    [NormedAddCommGroup ECC] [InnerProductSpace ℝ ECC] [FiniteDimensional ℝ ECC]
    {W : Type*} [Fintype W] [Nonempty W]
    (latN : W → Submodule ℤ EN) [∀ u, DiscreteTopology (latN u)] (hN0 : ∀ u, latN u ≠ ⊥)
    (latCC : Submodule ℤ ECC) [DiscreteTopology latCC] (hCC0 : latCC ≠ ⊥)
    (ιCC : ∀ u : W, latN u →ₗ[ℤ] latCC) (hι_inj : ∀ u, Function.Injective (ιCC u))
    (cCC d h : W → ℝ) (hd : ∀ u, 0 < d u)
    (hι_norm : ∀ u (x : latN u), ‖((ιCC u x : latCC) : ECC)‖ ≤ Real.exp (cCC u) * ‖(x : EN)‖)
    {x cHH eps : ℝ} (hx1 : 1 < x) (hcHH : 0 ≤ cHH) (_heps : 0 < eps)
    (hgap_le : -Real.log (lambda1 latCC * lambda1 (dualLat latCC)) + Real.log (rk latCC : ℝ) +
      RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u) ≤ x ^ cHH * Real.exp (x ^ eps)) :
    let HH := hhBanaszczyk latCC d cCC h
    RHDirect.SlopeInequality.wmean d (fun u => ArakelovCovolume.slope (latN u) - h u) -
        muMin latCC ≤ HH ∧
    0 < HH ∧
    HH ≤ x ^ cHH * Real.exp (x ^ eps) := by
  intro HH
  have h1 : RHDirect.SlopeInequality.wmean d (fun u => ArakelovCovolume.slope (latN u) - h u) -
      muMin latCC ≤ HH := by
    have hpt : ∀ u : W, ArakelovCovolume.slope (latN u) - h u ≤
        muMax latCC + (cCC u - h u) := fun u => by
      have hb := bost_slope_inequality (latN u) latCC (hN0 u) (ιCC u) (Real.exp (cCC u))
        (hι_inj u) (hι_norm u)
      rw [Real.log_exp] at hb
      linarith
    have hsum_pos : 0 < ∑ u : W, d u := Finset.sum_pos (fun u _ => hd u) Finset.univ_nonempty
    have hwmean_le : RHDirect.SlopeInequality.wmean d (fun u => ArakelovCovolume.slope (latN u) - h u) ≤
        muMax latCC + RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u) := by
      unfold RHDirect.SlopeInequality.wmean
      rw [← mul_div_cancel_left₀ (muMax latCC) hsum_pos.ne', mul_comm (∑ u : W, d u),
        ← add_div, div_le_div_iff_of_pos_right hsum_pos, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun u _ => ?_
      have hu := mul_le_mul_of_nonneg_left (hpt u) (hd u).le
      linarith
    have hS := banaszczyk_muMax_add_muMax_dual_sandwich latCC hCC0
    have hgap : muMax latCC - muMin latCC ≤
        -Real.log (lambda1 latCC * lambda1 (dualLat latCC)) + Real.log (rk latCC : ℝ) := by
      rw [← hS.1]; exact hS.2.2.2.1
    exact (show _ ≤ -Real.log (lambda1 latCC * lambda1 (dualLat latCC)) + Real.log (rk latCC : ℝ) +
      RHDirect.SlopeInequality.wmean d (fun u => cCC u - h u) by linarith).trans (le_max_right 1 _)
  have h2 : 0 < HH := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have h3 : HH ≤ x ^ cHH * Real.exp (x ^ eps) := by
    refine max_le ?_ hgap_le
    have hx_ge : 1 ≤ x ^ cHH := Real.one_le_rpow hx1.le hcHH
    have hexp_ge : 1 ≤ Real.exp (x ^ eps) :=
      Real.one_le_exp (Real.rpow_nonneg (zero_lt_one.trans hx1).le eps)
    exact one_le_mul_of_one_le_of_one_le hx_ge hexp_ge
  exact ⟨h1, h2, h3⟩

end ArakelovSlopeGapBridge

end RHDirect.Stage12BanaszczykTransference
