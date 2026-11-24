import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Algebra.Order.Round
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# RHDirect.Stage10GeometryOfNumbers

Unconditional, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of the core theorems of
the Geometry of Numbers in pure Mathlib `v4.33.1`:

1. **Concrete Blichfeldt's Theorem (`blichfeldt_theorem`) & General Minkowski `k`-Pairs Convex Body
   Theorem (`minkowski_convex_body_multiple`)**:
   - Full-rank lattice Blichfeldt theorem: if `volume S > k * covol(Λ)`, there exist `k + 1`
     distinct points `x_0, ..., x_k ∈ S` whose pairwise differences all lie in `Λ`.
   - Deduction of Minkowski's `k`-pairs theorem (van der Corput's theorem): any symmetric convex
     body `K` with `volume K > 2^n * k * covol(Λ)` contains at least `k` distinct nonzero opposite
     pairs `± v_1, ..., ± v_k ∈ (K ∩ Λ) \ {0}`.

2. **Unconditional Gauss 2D Lattice Reduction, Exact Hermite Constant `γ₂ = 2 / √3`, Hexagonal
   `A₂` Optimality & 2D Minkowski Second Theorem**:
   - `exists_gauss_reduced_basis`, `gauss_reduced_shortest_vector`, `hermite_dim2_le`,
     `hermite_dim2_hexagonal_tight` (exact equality `γ₂ = 2 / √3` and optimal 2D lattice sphere
     packing density `π / (2 √3)`), and `minkowski_second_theorem_dim2`.

3. **Unconditional Minkowski's Second Theorem on Successive Minima in Arbitrary Dimension `n ≥ 1`**:
   - Definition of `successiveMinimum K Λ k` (`k : Fin n`) for symmetric convex bodies `K`.
   - `minkowski_second_theorem_lower`: `(2^n / n!) * covol(Λ) ≤ (∏ i, λ_i) * (volume K).toReal`.
   - `minkowski_second_theorem_upper`: `(∏ i, λ_i) * (volume K).toReal ≤ 2^n * covol(Λ)` via
     inductive barycenter fiber compression.
   - `hermite_minkowski_bound_all_dims`: `λ₁(B_n, Λ)² ≤ (4 / ω_n^{2/n}) * covol(Λ)^{2/n}` for
     every `n ≥ 1`.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Module Submodule Finset Real Set
open scoped BigOperators ENNReal Pointwise Matrix

namespace RHDirect.Stage10GeometryOfNumbers

/-! ## Section 1: Blichfeldt's Theorem & Minkowski's `k`-Pairs Convex Body Theorem -/

section BlichfeldtAndMinkowski

/-- Helper: if a `tsum` of `{0, 1}`-valued indicators over a type `L` exceeds `k : ℕ`, then there
exist `k + 1` distinct elements of `L` at which the indicator is `1`. -/
private lemma exists_inj_of_lt_tsum_indicator_one {E L : Type*} {P : L → Set E} {x : E} {k : ℕ}
    (h : (k : ℝ≥0∞) < ∑' g : L, (P g).indicator (1 : E → ℝ≥0∞) x) :
    ∃ g : Fin (k + 1) → L, Function.Injective g ∧ ∀ i, x ∈ P (g i) := by
  classical
  let A : Set L := {γ : L | x ∈ P γ}
  have hterm : ∀ γ : L, (P γ).indicator (1 : E → ℝ≥0∞) x = if γ ∈ A then 1 else 0 := by
    intro γ
    by_cases hγ : x ∈ P γ
    · simp [hγ, A]
    · simp [hγ, A]
  simp_rw [hterm] at h
  by_cases hfin : A.Finite
  · have hsum : (∑' γ : L, if γ ∈ A then (1 : ℝ≥0∞) else 0) = (hfin.toFinset.card : ℝ≥0∞) := by
      rw [tsum_eq_sum (s := hfin.toFinset)]
      · rw [Finset.sum_congr rfl (fun γ hγ => if_pos (hfin.mem_toFinset.mp hγ))]
        simp
      · intro γ hγ
        simp only [hfin.mem_toFinset] at hγ
        simp [hγ]
    rw [hsum, Nat.cast_lt] at h
    have hcard : k + 1 ≤ hfin.toFinset.card := h
    obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hcard
    let e : Fin (k + 1) ≃ s := (Fintype.equivFinOfCardEq (by simp [hs_card])).symm
    refine ⟨fun i => (e i).1, ?_, ?_⟩
    · intro i j hij
      exact e.injective (Subtype.ext hij)
    · intro i
      exact hfin.mem_toFinset.mp (hs_sub (e i).2)
  · have hinf : A.Infinite := hfin
    obtain ⟨s, hs_sub, hs_card⟩ := hinf.exists_subset_card_eq (k + 1)
    let e : Fin (k + 1) ≃ s := (Fintype.equivFinOfCardEq (by simp [hs_card])).symm
    refine ⟨fun i => (e i).1, ?_, ?_⟩
    · intro i j hij
      exact e.injective (Subtype.ext hij)
    · intro i
      exact hs_sub (e i).2

/-- **General Blichfeldt's Theorem (1914)**: For any countable subgroup `L` of `E` with fundamental
domain `F` under a translation-invariant measure `μ`, and any null-measurable set `S` with
`k * μ F < μ S`, there exist `k + 1` distinct points `x_0, ..., x_k ∈ S` whose pairwise differences
all lie in `L`. -/
theorem blichfeldt_theorem_general {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    {μ : Measure E} {L : AddSubgroup E} [Countable L]
    [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    {F S : Set E} (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet S μ)
    {k : ℕ} (hvol : (k : ℝ≥0∞) * μ F < μ S) :
    ∃ x : Fin (k + 1) → E, Function.Injective x ∧ (∀ i, x i ∈ S) ∧ ∀ i j, x i - x j ∈ L := by
  have hmeas_sum :
      μ S = ∫⁻ y in F, (∑' g : L, (g +ᵥ S).indicator (1 : E → ℝ≥0∞) y) ∂μ := by
    rw [fund.measure_eq_tsum S]
    have hts : ∫⁻ y in F, (∑' g : L, (g +ᵥ S).indicator (1 : E → ℝ≥0∞) y) ∂μ =
        ∑' g : L, ∫⁻ y in F, (g +ᵥ S).indicator (1 : E → ℝ≥0∞) y ∂μ :=
      lintegral_tsum (fun g =>
        (aemeasurable_const.indicator₀
          ((hS.vadd g).mono_ac Measure.restrict_le_self.absolutelyContinuous)))
    rw [hts]
    congr 1
    ext g
    rw [lintegral_indicator₀
      ((hS.vadd g).mono_ac Measure.restrict_le_self.absolutelyContinuous)]
    simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply_univ]
    rw [Measure.restrict_apply₀' fund.nullMeasurableSet]
  have hex : ∃ y : E, (k : ℝ≥0∞) < ∑' g : L, (g +ᵥ S).indicator (1 : E → ℝ≥0∞) y := by
    by_contra hle
    push Not at hle
    have hbound :
        ∫⁻ y in F, (∑' g : L, (g +ᵥ S).indicator (1 : E → ℝ≥0∞) y) ∂μ ≤ (k : ℝ≥0∞) * μ F := by
      calc
        ∫⁻ y in F, (∑' g : L, (g +ᵥ S).indicator (1 : E → ℝ≥0∞) y) ∂μ
            ≤ ∫⁻ _ in F, (k : ℝ≥0∞) ∂μ := lintegral_mono (fun y => hle y)
        _ = (k : ℝ≥0∞) * μ F := by simp
    exact not_lt_of_ge (hmeas_sum ▸ hbound) hvol
  obtain ⟨y, hy⟩ := hex
  obtain ⟨g, hginj, hgmem⟩ := exists_inj_of_lt_tsum_indicator_one hy
  refine ⟨fun i => y - (g i : E), ?_, ?_, ?_⟩
  · intro i j hij
    have hsub : (g i : E) = (g j : E) := by
      have := congrArg (fun z => y - z) hij
      simpa using this
    exact hginj (Subtype.ext hsub)
  · intro i
    obtain ⟨s, hs, hgs⟩ := hgmem i
    have hys : y - (g i : E) = s := by
      rw [← hgs]
      change ((g i : E) + s) - (g i : E) = s
      exact add_sub_cancel_left (g i : E) s
    change y - (g i : E) ∈ S
    rwa [hys]
  · intro i j
    have hdiff : (y - (g i : E)) - (y - (g j : E)) = ((g j - g i : L) : E) := by
      push_cast
      abel
    change (y - (g i : E)) - (y - (g j : E)) ∈ L
    rw [hdiff]
    exact (g j - g i).2

/-- **Blichfeldt's Theorem for `ZSpan` lattices**: On any full-rank lattice `Λ = span ℤ (range b)`
in `EuclideanSpace ℝ (Fin n)`, if `volume S > k * volume (ZSpan.fundamentalDomain b)`, there exist
`k + 1` distinct points in `S` with all pairwise differences in `Λ`. -/
theorem blichfeldt_theorem_zspan {n : ℕ} (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : NullMeasurableSet S volume) {k : ℕ}
    (hvol : (k : ℝ≥0∞) * volume (ZSpan.fundamentalDomain b) < volume S) :
    ∃ x : Fin (k + 1) → EuclideanSpace ℝ (Fin n),
      Function.Injective x ∧ (∀ i, x i ∈ S) ∧
      ∀ i j, x i - x j ∈ Submodule.span ℤ (Set.range b) := by
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℤ (Set.range b)
  have : Countable L.toAddSubgroup := by
    refine Function.Injective.countable
      (f := fun x : L.toAddSubgroup => fun i : Fin n => ⌊b.repr x.1 i⌋) ?_
    intro x y hxy
    apply Subtype.ext
    have hfx : (ZSpan.floor b x.1 : EuclideanSpace ℝ (Fin n)) = x.1 :=
      ZSpan.floor_eq_self_of_mem b x.1 x.2
    have hfy : (ZSpan.floor b y.1 : EuclideanSpace ℝ (Fin n)) = y.1 :=
      ZSpan.floor_eq_self_of_mem b y.1 y.2
    rw [← hfx, ← hfy]
    apply b.repr.injective
    ext i
    rw [ZSpan.repr_floor_apply, ZSpan.repr_floor_apply]
    exact congrArg (Int.cast (R := ℝ)) (congrFun hxy i)
  have hfund : IsAddFundamentalDomain L.toAddSubgroup (ZSpan.fundamentalDomain b) volume :=
    ZSpan.isAddFundamentalDomain b volume
  exact blichfeldt_theorem_general (L := L.toAddSubgroup) hfund hS hvol

/-- **Concrete Blichfeldt's Theorem (`blichfeldt_theorem`)**: For any full-rank lattice `Λ` in
`EuclideanSpace ℝ (Fin n)` (`[DiscreteTopology Λ] [IsZLattice ℝ Λ]`) and any null-measurable set
`S` with `volume S > k * covol(Λ)`, there exist `k + 1` distinct points `x_0, ..., x_k ∈ S` with
all pairwise differences `x_i - x_j ∈ Λ`. -/
theorem blichfeldt_theorem {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : NullMeasurableSet S volume)
    {k : ℕ} (hvol : (k : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) < volume S) :
    ∃ x : Fin (k + 1) → EuclideanSpace ℝ (Fin n),
      Function.Injective x ∧ (∀ i, x i ∈ S) ∧ ∀ i j, x i - x j ∈ Λ := by
  let b : Basis (Fin n) ℤ Λ :=
    Module.Basis.reindex (Module.Free.chooseBasis ℤ Λ)
      (Fintype.equivOfCardEq (by
        rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
          ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]))
  have hfund : IsAddFundamentalDomain Λ.toAddSubgroup
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) volume :=
    ZLattice.isAddFundamentalDomain b volume
  have hne_top : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top.ne
  have hcov : ENNReal.ofReal (ZLattice.covolume Λ volume) =
      volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hfund,
      Measure.real, ENNReal.ofReal_toReal hne_top]
  rw [hcov] at hvol
  have : Countable Λ.toAddSubgroup :=
    Function.Injective.countable
      (f := fun x : Λ.toAddSubgroup => (b.repr ⟨x.1, x.2⟩ : Fin n → ℤ))
      (fun x y hxy => Subtype.ext (congrArg Subtype.val (b.repr.injective (Finsupp.ext (congrFun hxy)))))
  exact blichfeldt_theorem_general (L := Λ.toAddSubgroup) hfund hS hvol

/-- Helper: given `k + 1` distinct points in `EuclideanSpace ℝ (Fin n)`, choosing a point `x i₀`
of maximal Euclidean norm yields `k` nonzero differences `v_1, ..., v_k` that are pairwise distinct
and never negatives of one another (by the parallelogram law). -/
private lemma exists_distinct_pairs_of_inj_diffs {n k : ℕ}
    {x : Fin (k + 1) → EuclideanSpace ℝ (Fin n)} (hx : Function.Injective x) :
    ∃ (i₀ : Fin (k + 1)) (e : Fin k ≃ {i : Fin (k + 1) // i ≠ i₀}),
      let v : Fin k → EuclideanSpace ℝ (Fin n) := fun j => x (e j).1 - x i₀
      (∀ j, v j ≠ 0) ∧ (∀ j₁ j₂, j₁ ≠ j₂ → v j₁ ≠ v j₂ ∧ v j₁ ≠ -v j₂) := by
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (fun i => ‖x i‖) Finset.univ_nonempty
  have hcard : Fintype.card {i : Fin (k + 1) // i ≠ i₀} = k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    omega
  let e : Fin k ≃ {i : Fin (k + 1) // i ≠ i₀} := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨i₀, e, ?_, ?_⟩
  · intro j hzero
    have heq : x (e j).1 = x i₀ := sub_eq_zero.mp hzero
    exact (e j).2 (hx heq)
  · intro j₁ j₂ hne
    refine ⟨?_, ?_⟩
    · intro heq
      have : x (e j₁).1 = x (e j₂).1 := sub_left_inj.mp heq
      exact hne (e.injective (Subtype.ext (hx this)))
    · intro hneg
      dsimp only at hneg
      have hsum : x (e j₁).1 + x (e j₂).1 = (2 : ℝ) • x i₀ := by
        rw [two_smul]
        have h1 : (x (e j₁).1 - x i₀) + (x (e j₂).1 - x i₀) = 0 := by
          rw [hneg, neg_add_cancel]
        have h2 : x (e j₁).1 + x (e j₂).1 - (x i₀ + x i₀) = 0 := by
          calc
            x (e j₁).1 + x (e j₂).1 - (x i₀ + x i₀)
                = (x (e j₁).1 - x i₀) + (x (e j₂).1 - x i₀) := by abel
            _ = 0 := h1
        exact sub_eq_zero.mp h2
      have hpara : ‖x (e j₁).1 + x (e j₂).1‖ ^ 2 + ‖x (e j₁).1 - x (e j₂).1‖ ^ 2 =
          2 * ‖x (e j₁).1‖ ^ 2 + 2 * ‖x (e j₂).1‖ ^ 2 := by
        have hp := parallelogram_law_with_norm ℝ (x (e j₁).1) (x (e j₂).1)
        linarith [sq ‖x (e j₁).1 + x (e j₂).1‖, sq ‖x (e j₁).1 - x (e j₂).1‖,
          sq ‖x (e j₁).1‖, sq ‖x (e j₂).1‖]
      have hle1 : ‖x (e j₁).1‖ ≤ ‖x i₀‖ := hi₀ (e j₁).1 (Finset.mem_univ _)
      have hle2 : ‖x (e j₂).1‖ ≤ ‖x i₀‖ := hi₀ (e j₂).1 (Finset.mem_univ _)
      have hsq1 : ‖x (e j₁).1‖ ^ 2 ≤ ‖x i₀‖ ^ 2 := by nlinarith [norm_nonneg (x (e j₁).1)]
      have hsq2 : ‖x (e j₂).1‖ ^ 2 ≤ ‖x i₀‖ ^ 2 := by nlinarith [norm_nonneg (x (e j₂).1)]
      have hnorm_sum : ‖x (e j₁).1 + x (e j₂).1‖ ^ 2 = 4 * ‖x i₀‖ ^ 2 := by
        rw [hsum, norm_smul, Real.norm_ofNat]
        ring
      have hdiff_zero : ‖x (e j₁).1 - x (e j₂).1‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖x (e j₁).1 - x (e j₂).1‖]
      have hx_eq : x (e j₁).1 = x (e j₂).1 :=
        sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdiff_zero))
      exact hne (e.injective (Subtype.ext (hx hx_eq)))

/-- **Minkowski's `k`-Pairs Convex Body Theorem (`minkowski_convex_body_multiple`)** (van der
Corput 1936): Any symmetric convex set `K ⊆ ℝ^n` with `volume K > 2^n * k * covol(Λ)` contains at
least `k` distinct nonzero opposite pairs `± v_1, ..., ± v_k ∈ (K ∩ Λ) \ {0}`. -/
theorem minkowski_convex_body_multiple {n : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    {k : ℕ}
    (hvol : (2 ^ n * k : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) < volume K) :
    ∃ v : Fin k → EuclideanSpace ℝ (Fin n),
      (∀ i, v i ∈ K ∧ -v i ∈ K) ∧
      (∀ i, v i ∈ Λ ∧ -v i ∈ Λ) ∧
      (∀ i, v i ≠ 0) ∧
      (∀ i j, i ≠ j → v i ≠ v j ∧ v i ≠ -v j) := by
  have hS_vol : (k : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) <
      volume ((2⁻¹ : ℝ) • K) := by
    rw [Measure.addHaar_smul_of_nonneg volume (by positivity : (0 : ℝ) ≤ 2⁻¹) K,
      finrank_euclideanSpace_fin, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
    rw [← ENNReal.mul_lt_mul_iff_left (pow_ne_zero n (two_ne_zero' ℝ≥0∞)) (by finiteness)]
    calc
      (k : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) * (2 : ℝ≥0∞) ^ n
          = (2 ^ n * k : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume Λ volume) := by ring
      _ < volume K := hvol
      _ = (2 : ℝ≥0∞)⁻¹ ^ n * volume K * (2 : ℝ≥0∞) ^ n := by
        rw [mul_right_comm, ← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
          one_pow, one_mul]
  obtain ⟨x, hx_inj, hx_mem, hx_diff⟩ :=
    blichfeldt_theorem Λ ((hconv.smul (2⁻¹ : ℝ)).nullMeasurableSet volume) hS_vol
  obtain ⟨i₀, e, hv_ne, hv_pairs⟩ := exists_distinct_pairs_of_inj_diffs hx_inj
  refine ⟨fun j => x (e j).1 - x i₀, ?_, ?_, hv_ne, hv_pairs⟩
  · intro j
    obtain ⟨a, ha, ha_eq⟩ := Set.mem_smul_set.mp (hx_mem (e j).1)
    obtain ⟨c, hc, hc_eq⟩ := Set.mem_smul_set.mp (hx_mem i₀)
    have hmem : x (e j).1 - x i₀ ∈ K := by
      rw [← ha_eq, ← hc_eq, sub_eq_add_neg, ← smul_neg]
      exact hconv ha (hsymm c hc) (by positivity) (by positivity) (by norm_num)
    exact ⟨hmem, hsymm _ hmem⟩
  · intro j
    have hmem : x (e j).1 - x i₀ ∈ Λ := hx_diff (e j).1 i₀
    exact ⟨hmem, Λ.neg_mem hmem⟩

end BlichfeldtAndMinkowski

/-! ## Section 2: Lattice Basics, Gauss 2D Reduction & Exact Hermite Constant `γ₂ = 2 / √3` -/

section LatticeBasics

/-- Canonical `ℤ`-basis indexed by `Fin n` for a full-rank lattice `Λ ⊂ ℝ^n`. -/
def basisOfZLattice {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] : Basis (Fin n) ℤ Λ :=
  Module.Basis.reindex (Module.Free.chooseBasis ℤ Λ)
    (Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
        ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]))

/-- The intersection of any full-rank lattice in `ℝ^n` with any bounded set is finite. -/
theorem lattice_inter_isBounded_finite {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : Bornology.IsBounded S) :
    ((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ S).Finite := by
  let b := (basisOfZLattice Λ).ofZLatticeBasis ℝ
  have hspan : Submodule.span ℤ (Set.range b) = Λ := Basis.ofZLatticeBasis_span ℝ Λ _
  rw [← hspan]
  simpa [Set.inter_comm] using ZSpan.setFinite_inter b hS

/-- The intersection of any full-rank lattice in `ℝ^n` with any closed ball is finite. -/
theorem lattice_inter_closedBall_finite {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (R : ℝ) :
    ((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.closedBall 0 R).Finite :=
  lattice_inter_isBounded_finite Λ Metric.isBounded_closedBall

/-- Exact determinant formula for the covolume of a full-rank lattice `Λ ⊂ ℝ^n` with `ℤ`-basis `b`:
`covol(Λ) = |det (fun i j => (b i : ℝ^n) j)|`. -/
theorem covolume_eq_abs_det {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis (Fin n) ℤ Λ) :
    ZLattice.covolume Λ volume =
      |(Matrix.of (fun i j : Fin n => (b i : EuclideanSpace ℝ (Fin n)) j)).det| := by
  let b₀ : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hcov := ZLattice.covolume_eq_det_mul_measureReal Λ volume b b₀
  have hvol1 : volume (ZSpan.fundamentalDomain b₀) = 1 := by
    have hpre : (WithLp.toLp 2) ⁻¹' ZSpan.fundamentalDomain b₀ =
        ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)) := by
      ext x
      simp [ZSpan.mem_fundamentalDomain, b₀]
    rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
      (ZSpan.fundamentalDomain_measurableSet b₀).nullMeasurableSet, hpre,
      ZSpan.volume_fundamentalDomain (Pi.basisFun ℝ (Fin n))]
    have hmat : Matrix.of (⇑(Pi.basisFun ℝ (Fin n))) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [Matrix.one_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [hmat, Matrix.det_one]
    simp
  have hreal1 : volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    rw [Measure.real, hvol1, ENNReal.toReal_one]
  rw [hcov, hreal1, mul_one]
  congr 1
  rw [Basis.det_apply, ← Matrix.det_transpose]
  congr 1

/-- Shortest nonzero Euclidean norm `λ₁(Λ)` of a lattice `Λ ⊂ ℝ^n`. -/
def shortestNorm {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf { r : ℝ | ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ = r }

/-- Every full-rank lattice `Λ ⊂ ℝ^n` (`n ≥ 1`) admits a shortest nonzero vector. -/
theorem exists_shortest_nonzero_vector {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ u ∈ Λ, u ≠ 0 ∧ ∀ w ∈ Λ, w ≠ 0 → ‖u‖ ≤ ‖w‖ := by
  let e := basisOfZLattice Λ
  let u₀ : EuclideanSpace ℝ (Fin n) := e ⟨0, hn⟩
  have hu₀_mem : u₀ ∈ Λ := (e ⟨0, hn⟩).2
  have hu₀_ne : u₀ ≠ 0 := by
    intro h0
    exact e.ne_zero ⟨0, hn⟩ (Subtype.ext h0)
  let S : Set (EuclideanSpace ℝ (Fin n)) :=
    ((Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ Metric.closedBall 0 ‖u₀‖) \ {0}
  have hS_fin : S.Finite := (lattice_inter_closedBall_finite Λ ‖u₀‖).sdiff
  have hS_ne : hS_fin.toFinset.Nonempty := by
    refine ⟨u₀, hS_fin.mem_toFinset.mpr ?_⟩
    exact ⟨⟨hu₀_mem, by simp⟩, hu₀_ne⟩
  obtain ⟨u, hu_mem_fin, hu_min⟩ :=
    Finset.exists_min_image hS_fin.toFinset (fun x => ‖x‖) hS_ne
  have huS : u ∈ S := hS_fin.mem_toFinset.mp hu_mem_fin
  refine ⟨u, huS.1.1, huS.2, ?_⟩
  intro w hw hw_ne
  by_cases hle : ‖w‖ ≤ ‖u₀‖
  · exact hu_min w (hS_fin.mem_toFinset.mpr ⟨⟨hw, by simpa using hle⟩, hw_ne⟩)
  · have hu_le_u₀ : ‖u‖ ≤ ‖u₀‖ := by simpa using huS.1.2
    linarith

/-- If `u ∈ Λ \ {0}` attains minimal Euclidean norm in `Λ`, then `shortestNorm Λ = ‖u‖`. -/
theorem shortestNorm_eq_of_min {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    {u : EuclideanSpace ℝ (Fin n)} (hu_mem : u ∈ Λ) (hu_ne : u ≠ 0)
    (hu_min : ∀ w ∈ Λ, w ≠ 0 → ‖u‖ ≤ ‖w‖) :
    shortestNorm Λ = ‖u‖ := by
  unfold shortestNorm
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, by rintro _ ⟨v, _, _, rfl⟩; exact norm_nonneg v⟩ ⟨u, hu_mem, hu_ne, rfl⟩
  · refine le_csInf ⟨‖u‖, u, hu_mem, hu_ne, rfl⟩ ?_
    rintro _ ⟨w, hw, hw_ne, rfl⟩
    exact hu_min w hw hw_ne

/-- `shortestNorm Λ > 0` for any full-rank lattice `Λ ⊂ ℝ^n` (`n ≥ 1`). -/
theorem shortestNorm_pos {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    0 < shortestNorm Λ := by
  obtain ⟨u, hu_mem, hu_ne, hu_min⟩ := exists_shortest_nonzero_vector hn Λ
  rw [shortestNorm_eq_of_min Λ hu_mem hu_ne hu_min]
  exact norm_pos_iff.mpr hu_ne

/-- Every nonzero lattice vector has norm at least `shortestNorm Λ`. -/
theorem shortestNorm_le_norm {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ Λ) (hw_ne : w ≠ 0) :
    shortestNorm Λ ≤ ‖w‖ := by
  exact csInf_le ⟨0, by rintro _ ⟨v, _, _, rfl⟩; exact norm_nonneg v⟩ ⟨w, hw, hw_ne, rfl⟩

/-- The `k`-th **Minkowski successive minimum** `λ_{k+1}(K, Λ)` (`k : Fin n`) of a full-rank
lattice `Λ ⊂ ℝ^n` with respect to a set `K ⊆ ℝ^n`: the infimum of all `t > 0` such that `t • K`
contains `k + 1` `ℝ`-linearly independent vectors of `Λ`. -/
def successiveMinimum {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (k : Fin n) : ℝ :=
  sInf { t : ℝ | 0 < t ∧ ∃ v : Fin (k.1 + 1) → EuclideanSpace ℝ (Fin n),
    (∀ j, v j ∈ Λ) ∧ LinearIndependent ℝ v ∧ ∀ j, v j ∈ t • K }

end LatticeBasics

section GaussReductionDim2

/-- A pair `(u, v)` in `ℝ²` is **Gauss-reduced** if `0 < ‖u‖ ≤ ‖v‖` and `2 |⟪u, v⟫| ≤ ‖u‖²`. -/
def IsGaussReduced (u v : EuclideanSpace ℝ (Fin 2)) : Prop :=
  0 < ‖u‖ ∧ ‖u‖ ≤ ‖v‖ ∧ 2 * |inner ℝ u v| ≤ ‖u‖ ^ 2

/-- **Unconditional Existence of a Gauss-Reduced `ℤ`-Basis (`exists_gauss_reduced_basis`)**:
Every full-rank lattice `Λ ⊂ ℝ²` admits a `ℤ`-basis `(u, v)` satisfying `0 < ‖u‖ ≤ ‖v‖` and
`2 |⟪u, v⟫| ≤ ‖u‖²`. -/
theorem exists_gauss_reduced_basis (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ b : Basis (Fin 2) ℤ Λ,
      IsGaussReduced (b 0 : EuclideanSpace ℝ (Fin 2)) (b 1 : EuclideanSpace ℝ (Fin 2)) := by
  let e : Basis (Fin 2) ℤ Λ := basisOfZLattice Λ
  obtain ⟨u_val, hu_mem, hu_ne, hu_min⟩ := exists_shortest_nonzero_vector (by decide : 0 < 2) Λ
  let u : Λ := ⟨u_val, hu_mem⟩
  let a : ℤ := e.repr u 0
  let c : ℤ := e.repr u 1
  have hu_expand : u = a • e 0 + c • e 1 := by
    have h := e.sum_repr u
    rw [Fin.sum_univ_two] at h
    exact h.symm
  have hgcd : Int.gcd a c = 1 := by
    set d : ℕ := Int.gcd a c
    have hd_pos : 0 < d := by
      by_contra h0
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos h0
      have ha0 : a = 0 := (Int.gcd_eq_zero_iff.mp hd0).1
      have hc0 : c = 0 := (Int.gcd_eq_zero_iff.mp hd0).2
      have : u = 0 := by rw [hu_expand, ha0, hc0]; simp
      exact hu_ne (congrArg Subtype.val this)
    obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a c
    obtain ⟨c', hc'⟩ := Int.gcd_dvd_right a c
    let w : Λ := a' • e 0 + c' • e 1
    have hdw : (d : ℤ) • w = u := by
      have h1 : (d : ℤ) • w = a • e 0 + c • e 1 := by
        simp only [w, smul_add, ← mul_smul]
        rw [← ha', ← hc']
      rw [h1, ← hu_expand]
    have hw_ne : (w : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
      intro hw0
      have : u = 0 := by
        rw [← hdw]
        have : w = 0 := Subtype.ext hw0
        rw [this, smul_zero]
      exact hu_ne (congrArg Subtype.val this)
    have hnorm_u : ‖(u : EuclideanSpace ℝ (Fin 2))‖ = (d : ℝ) * ‖(w : EuclideanSpace ℝ (Fin 2))‖ := by
      have hcoe : (u : EuclideanSpace ℝ (Fin 2)) = (d : ℝ) • (w : EuclideanSpace ℝ (Fin 2)) := by
        have h1 : (u : EuclideanSpace ℝ (Fin 2)) = d • (w : EuclideanSpace ℝ (Fin 2)) := by
          have := congrArg (Subtype.val : Λ → EuclideanSpace ℝ (Fin 2)) hdw.symm
          simpa using this
        rw [h1, Nat.cast_smul_eq_nsmul]
      rw [hcoe, norm_smul, Real.norm_natCast]
    have hle : ‖(u : EuclideanSpace ℝ (Fin 2))‖ ≤ ‖(w : EuclideanSpace ℝ (Fin 2))‖ :=
      hu_min w.1 w.2 hw_ne
    have hw_pos : 0 < ‖(w : EuclideanSpace ℝ (Fin 2))‖ := norm_pos_iff.mpr hw_ne
    have hd_le : (d : ℝ) ≤ 1 := by nlinarith
    have hd_le_nat : d ≤ 1 := by exact_mod_cast hd_le
    omega
  let r : ℤ := Int.gcdA a c
  let s : ℤ := Int.gcdB a c
  have hbez : a * r + c * s = 1 := by
    have h := Int.gcd_eq_gcd_ab a c
    rw [hgcd] at h
    simpa [r, s] using h.symm
  let v₀ : Λ := (-s) • e 0 + r • e 1
  let k : ℤ := round (inner ℝ (u : EuclideanSpace ℝ (Fin 2)) (v₀ : EuclideanSpace ℝ (Fin 2)) /
    ‖(u : EuclideanSpace ℝ (Fin 2))‖ ^ 2)
  let v : Λ := v₀ - k • u
  have hrepr_u0 : e.repr u 0 = a := rfl
  have hrepr_u1 : e.repr u 1 = c := rfl
  have hrepr_v0 : e.repr v 0 = -s - k * a := by
    simp only [v, v₀, map_sub, map_add, map_smul, Finsupp.coe_sub, Finsupp.coe_add,
      Finsupp.coe_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Basis.repr_self,
      Finsupp.single_eq_same, hrepr_u0]
    have h10 : (Finsupp.single (1 : Fin 2) (1 : ℤ)) 0 = 0 :=
      Finsupp.single_eq_of_ne (by decide)
    rw [h10]
    ring
  have hrepr_v1 : e.repr v 1 = r - k * c := by
    simp only [v, v₀, map_sub, map_add, map_smul, Finsupp.coe_sub, Finsupp.coe_add,
      Finsupp.coe_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Basis.repr_self,
      Finsupp.single_eq_same, hrepr_u1]
    have h01 : (Finsupp.single (0 : Fin 2) (1 : ℤ)) 1 = 0 :=
      Finsupp.single_eq_of_ne (by decide)
    rw [h01]
    ring
  -- Construct the unimodular ℤ-linear equivalence `(Fin 2 → ℤ) ≃ₗ[ℤ] Λ` sending `e_0 ↦ u, e_1 ↦ v`.
  let φ : (Fin 2 → ℤ) ≃ₗ[ℤ] Λ :=
    { toFun := fun x => x 0 • u + x 1 • v
      map_add' := fun x y => by simp only [Pi.add_apply, add_smul]; abel
      map_smul' := fun t x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]
      invFun := fun w i =>
        if i = 0 then
          e.repr w 0 * r + e.repr w 1 * s + k * (e.repr w 1 * a - e.repr w 0 * c)
        else
          e.repr w 1 * a - e.repr w 0 * c
      left_inv := fun x => by
        ext i
        fin_cases i
        · change (e.repr (x 0 • u + x 1 • v) 0 * r + e.repr (x 0 • u + x 1 • v) 1 * s +
              k * (e.repr (x 0 • u + x 1 • v) 1 * a - e.repr (x 0 • u + x 1 • v) 0 * c)) = x 0
          simp only [map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrepr_u0, hrepr_u1, hrepr_v0, hrepr_v1]
          linear_combination (x 0) * hbez
        · change (e.repr (x 0 • u + x 1 • v) 1 * a - e.repr (x 0 • u + x 1 • v) 0 * c) = x 1
          simp only [map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrepr_u0, hrepr_u1, hrepr_v0, hrepr_v1]
          linear_combination (x 1) * hbez
      right_inv := fun w => by
        apply e.repr.injective
        ext i
        fin_cases i
        · change e.repr ((e.repr w 0 * r + e.repr w 1 * s +
              k * (e.repr w 1 * a - e.repr w 0 * c)) • u +
              (e.repr w 1 * a - e.repr w 0 * c) • v) 0 = e.repr w 0
          simp only [map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrepr_u0, hrepr_v0]
          linear_combination (e.repr w 0) * hbez
        · change e.repr ((e.repr w 0 * r + e.repr w 1 * s +
              k * (e.repr w 1 * a - e.repr w 0 * c)) • u +
              (e.repr w 1 * a - e.repr w 0 * c) • v) 1 = e.repr w 1
          simp only [map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrepr_u1, hrepr_v1]
          linear_combination (e.repr w 1) * hbez }
  let b : Basis (Fin 2) ℤ Λ := (Pi.basisFun ℤ (Fin 2)).map φ
  have hb0 : b 0 = u := by
    simp [b, φ]
  have hb1 : b 1 = v := by
    simp [b, φ]
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb0]
    exact norm_pos_iff.mpr hu_ne
  · rw [hb0, hb1]
    have hv_ne : (v : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
      intro hv0
      exact b.ne_zero 1 (hb1 ▸ Subtype.ext hv0)
    exact hu_min v.1 v.2 hv_ne
  · rw [hb0, hb1]
    have hu_sq_pos : 0 < ‖(u : EuclideanSpace ℝ (Fin 2))‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hu_ne)
    have hinner :
        inner ℝ (u : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 2)) =
          (inner ℝ (u : EuclideanSpace ℝ (Fin 2)) (v₀ : EuclideanSpace ℝ (Fin 2)) /
            ‖(u : EuclideanSpace ℝ (Fin 2))‖ ^ 2 - (k : ℝ)) *
          ‖(u : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
      have hv_coe : (v : EuclideanSpace ℝ (Fin 2)) =
          (v₀ : EuclideanSpace ℝ (Fin 2)) - (k : ℝ) • (u : EuclideanSpace ℝ (Fin 2)) := by
        simp [v, Int.cast_smul_eq_zsmul ℝ]
      rw [hv_coe, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
        sub_mul, div_mul_cancel₀ _ hu_sq_pos.ne']
    rw [hinner, abs_mul, abs_of_pos hu_sq_pos]
    have hround : |inner ℝ (u : EuclideanSpace ℝ (Fin 2)) (v₀ : EuclideanSpace ℝ (Fin 2)) /
        ‖(u : EuclideanSpace ℝ (Fin 2))‖ ^ 2 - (k : ℝ)| ≤ 1 / 2 :=
      abs_sub_round _
    nlinarith

/-- Key quadratic lower bound for a Gauss-reduced pair `(u, v)`: for ALL integers `m, n` with
`n ≠ 0`, `‖v‖ ≤ ‖m • u + n • v‖`. -/
theorem gauss_reduced_norm_ge_second {u v : EuclideanSpace ℝ (Fin 2)}
    (hred : IsGaussReduced u v) {m n : ℤ} (hn : n ≠ 0) :
    ‖v‖ ≤ ‖m • u + n • v‖ := by
  obtain ⟨hu_pos, huv, hinner⟩ := hred
  have hsq : ‖v‖ ^ 2 ≤ ‖m • u + n • v‖ ^ 2 := by
    have hexpand : ‖m • u + n • v‖ ^ 2 =
        (m : ℝ) ^ 2 * ‖u‖ ^ 2 + 2 * (m : ℝ) * (n : ℝ) * inner ℝ u v + (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by
      rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, norm_add_sq_real, norm_smul,
        norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
        inner_smul_left, inner_smul_right]
      simp only [conj_trivial]
      ring
    rw [hexpand]
    have hcross : -(|(m : ℝ)| * |(n : ℝ)| * ‖u‖ ^ 2) ≤ 2 * (m : ℝ) * (n : ℝ) * inner ℝ u v := by
      have h1 : |(m : ℝ) * (n : ℝ) * (2 * inner ℝ u v)| ≤ |(m : ℝ)| * |(n : ℝ)| * ‖u‖ ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have : 0 ≤ |(m : ℝ)| * |(n : ℝ)| := by positivity
        nlinarith
      have h2 := neg_abs_le ((m : ℝ) * (n : ℝ) * (2 * inner ℝ u v))
      linarith
    have hn_abs : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      exact_mod_cast this
    have hn_sq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
    have huv_sq : ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith
    have hquad : 0 ≤ |(m : ℝ)| ^ 2 - |(m : ℝ)| * |(n : ℝ)| + |(n : ℝ)| ^ 2 - 1 := by
      by_cases hm : m = 0
      · simp [hm]
        nlinarith
      · have hm_abs : (1 : ℝ) ≤ |(m : ℝ)| := by
          have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
          exact_mod_cast this
        nlinarith [sq_nonneg (|(m : ℝ)| - |(n : ℝ)|)]
    have hnonneg : 0 ≤ ((m : ℝ) ^ 2 - |(m : ℝ)| * |(n : ℝ)| + (n : ℝ) ^ 2 - 1) * ‖u‖ ^ 2 := by
      rw [← sq_abs (m : ℝ), ← sq_abs (n : ℝ)]
      exact mul_nonneg hquad (sq_nonneg ‖u‖)
    nlinarith
  nlinarith [norm_nonneg v, norm_nonneg (m • u + n • v)]

/-- **Gauss-Reduced Shortest Vector Theorem (`gauss_reduced_shortest_vector`)**:
If `b` is a Gauss-reduced `ℤ`-basis of `Λ ⊂ ℝ²`, then `b 0` is a shortest nonzero vector of `Λ`
(and hence `shortestNorm Λ = ‖(b 0 : ℝ²)‖`). -/
theorem gauss_reduced_shortest_vector (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    (b : Basis (Fin 2) ℤ Λ)
    (hred : IsGaussReduced (b 0 : EuclideanSpace ℝ (Fin 2)) (b 1 : EuclideanSpace ℝ (Fin 2))) :
    ∀ w ∈ Λ, w ≠ 0 → ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ≤ ‖w‖ := by
  intro w hw hw_ne
  let m : ℤ := b.repr ⟨w, hw⟩ 0
  let n : ℤ := b.repr ⟨w, hw⟩ 1
  have hw_eq : w = m • (b 0 : EuclideanSpace ℝ (Fin 2)) + n • (b 1 : EuclideanSpace ℝ (Fin 2)) := by
    have h := b.sum_repr ⟨w, hw⟩
    rw [Fin.sum_univ_two] at h
    have hval := congrArg (Subtype.val : Λ → EuclideanSpace ℝ (Fin 2)) h.symm
    simpa [m, n] using hval
  rw [hw_eq]
  by_cases hn : n = 0
  · rw [hn, zero_smul, add_zero] at hw_eq ⊢
    have hm : m ≠ 0 := by
      intro hm0
      rw [hm0, zero_smul] at hw_eq
      exact hw_ne hw_eq
    have hm_abs : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg (b 0 : EuclideanSpace ℝ (Fin 2))]
  · exact le_trans hred.2.1 (gauss_reduced_norm_ge_second hred hn)

/-- Exact 2D Gram/Lagrange covolume identity:
`covol(Λ)² = ‖u‖² ‖v‖² - ⟪u, v⟫²` for any `ℤ`-basis `(u, v)` of `Λ ⊂ ℝ²`. -/
theorem covolume_dim2_sq_eq (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis (Fin 2) ℤ Λ) :
    ZLattice.covolume Λ volume ^ 2 =
      ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 * ‖(b 1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2 -
        (inner ℝ (b 0 : EuclideanSpace ℝ (Fin 2)) (b 1 : EuclideanSpace ℝ (Fin 2))) ^ 2 := by
  rw [covolume_eq_abs_det Λ b, sq_abs]
  set u : EuclideanSpace ℝ (Fin 2) := (b 0).1
  set v : EuclideanSpace ℝ (Fin 2) := (b 1).1
  have hdet : (Matrix.of (fun i j : Fin 2 => (b i : EuclideanSpace ℝ (Fin 2)) j)).det =
      u 0 * v 1 - u 1 * v 0 := by
    rw [Matrix.det_fin_two]
    rfl
  have hu_sq : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  have hv_sq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  have huv : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    simp [mul_comm]
  rw [hdet, hu_sq, hv_sq, huv]
  ring

/-- Sharp product bound for a Gauss-reduced basis `(u, v)` of `Λ ⊂ ℝ²`:
`‖u‖ * ‖v‖ ≤ (2 / √3) * covol(Λ)`. -/
theorem gauss_reduced_prod_norm_le (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis (Fin 2) ℤ Λ)
    (hred : IsGaussReduced (b 0 : EuclideanSpace ℝ (Fin 2)) (b 1 : EuclideanSpace ℝ (Fin 2))) :
    ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ * ‖(b 1 : EuclideanSpace ℝ (Fin 2))‖ ≤
      (2 / √3) * ZLattice.covolume Λ volume := by
  set u : EuclideanSpace ℝ (Fin 2) := (b 0).1
  set v : EuclideanSpace ℝ (Fin 2) := (b 1).1
  obtain ⟨hu_pos, huv, hinner⟩ := hred
  have hinner_sq : 4 * (inner ℝ u v) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    have h1 : 4 * (inner ℝ u v) ^ 2 ≤ (‖u‖ ^ 2) ^ 2 := by
      have : (2 * |inner ℝ u v|) ^ 2 ≤ (‖u‖ ^ 2) ^ 2 := by nlinarith [abs_nonneg (inner ℝ u v)]
      rw [mul_pow, sq_abs] at this
      linarith
    have h2 : ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖u‖]
  have hcov_sq : (3 / 4 : ℝ) * (‖u‖ * ‖v‖) ^ 2 ≤ ZLattice.covolume Λ volume ^ 2 := by
    rw [covolume_dim2_sq_eq Λ b]
    nlinarith
  have hcov_nonneg : 0 ≤ ZLattice.covolume Λ volume := le_of_lt (ZLattice.covolume_pos Λ volume)
  have hsqrt3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hprod_sq : (‖u‖ * ‖v‖) ^ 2 ≤ ((2 / √3) * ZLattice.covolume Λ volume) ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith
  have hrhs_nonneg : 0 ≤ (2 / √3) * ZLattice.covolume Λ volume := by positivity
  nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]

/-- **Exact 2D Hermite Bound (`hermite_dim2_le`)**: Every rank-2 lattice `Λ ⊂ ℝ²` satisfies
`λ₁(Λ)² ≤ (2 / √3) * covol(Λ)`, attained by the first vector of any Gauss-reduced basis. -/
theorem hermite_dim2_le (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    shortestNorm Λ ^ 2 ≤ (2 / √3) * ZLattice.covolume Λ volume := by
  obtain ⟨b, hred⟩ := exists_gauss_reduced_basis Λ
  have hmin : shortestNorm Λ = ‖(b 0 : EuclideanSpace ℝ (Fin 2))‖ := by
    refine shortestNorm_eq_of_min Λ (b 0).2 ?_ (gauss_reduced_shortest_vector Λ b hred)
    exact norm_pos_iff.mp hred.1
  rw [hmin]
  have hprod := gauss_reduced_prod_norm_le Λ b hred
  nlinarith [hred.1, hred.2.1]

/-- First basis vector `(1, 0)` of the hexagonal `A₂` lattice in `ℝ²`. -/
def hexVec0 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- Second basis vector `(1/2, √3/2)` of the hexagonal `A₂` lattice in `ℝ²`. -/
def hexVec1 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1 / 2, √3 / 2]

/-- The `ℝ`-basis `((1, 0), (1/2, √3/2))` of `ℝ²` generating the hexagonal lattice `A₂`. -/
def hexagonalBasis : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Basis.mk
    (v := ![hexVec0, hexVec1])
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have h0 := congrFun (congrArg WithLp.ofLp hg) 0
      have h1 := congrFun (congrArg WithLp.ofLp hg) 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        hexVec0, hexVec1, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_zero, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
      have hsqrt3 : (0 : ℝ) < √3 / 2 := by positivity
      have hg1 : g 1 = 0 := by
        have : g 1 * (√3 / 2) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_right hsqrt3.ne'
      have hg0 : g 0 = 0 := by linarith
      intro i
      fin_cases i <;> assumption)
    (by
      intro x _
      rw [Submodule.mem_span_range_iff_exists_fun]
      have hsqrt3 : (√3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      refine ⟨![x 0 - x 1 / √3, 2 * x 1 / √3], ?_⟩
      rw [Fin.sum_univ_two]
      ext i
      fin_cases i
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hexVec0, hexVec1, WithLp.ofLp_add,
          WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        change (x 0 - x 1 / √3) * 1 + (2 * x 1 / √3) * (1 / 2) = x 0
        field_simp [hsqrt3]
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hexVec0, hexVec1, WithLp.ofLp_add,
          WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        change (x 0 - x 1 / √3) * 0 + (2 * x 1 / √3) * (√3 / 2) = x 1
        field_simp [hsqrt3]
        ring)

/-- The hexagonal lattice `A₂ = ℤ·(1, 0) ⊕ ℤ·(1/2, √3/2)` in `ℝ²`. -/
def hexagonalLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℤ (Set.range hexagonalBasis)

instance : DiscreteTopology hexagonalLattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range hexagonalBasis)))

instance : IsZLattice ℝ hexagonalLattice :=
  ⟨ZSpan.span_top hexagonalBasis⟩

lemma hexagonalBasis_zero : hexagonalBasis 0 = hexVec0 := by
  simp [hexagonalBasis]

lemma hexagonalBasis_one : hexagonalBasis 1 = hexVec1 := by
  simp [hexagonalBasis]

lemma norm_hexVec0 : ‖hexVec0‖ = 1 := by
  have hsq : ‖hexVec0‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [hexVec0]
  nlinarith [norm_nonneg hexVec0]

lemma norm_hexVec1 : ‖hexVec1‖ = 1 := by
  have hsq : ‖hexVec1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp only [hexVec1, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  nlinarith [norm_nonneg hexVec1]

lemma inner_hexVec0_hexVec1 : inner ℝ hexVec0 hexVec1 = 1 / 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp [hexVec0, hexVec1]

/-- Canonical `ℤ`-basis of `hexagonalLattice`. -/
private def hexagonalZBasis : Basis (Fin 2) ℤ hexagonalLattice :=
  Basis.mk
    (v := fun i => ⟨hexagonalBasis i, Submodule.subset_span ⟨i, rfl⟩⟩)
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hval : ∑ i : Fin 2, (g i : ℝ) • hexagonalBasis i = 0 := by
        have := congrArg (Subtype.val : hexagonalLattice → EuclideanSpace ℝ (Fin 2)) hg
        simpa [← Int.cast_smul_eq_zsmul ℝ] using this
      have hlin := Fintype.linearIndependent_iff.mp hexagonalBasis.linearIndependent
        (fun i => (g i : ℝ)) hval
      intro i
      exact_mod_cast hlin i)
    (by
      intro x _
      have hx : x.1 ∈ Submodule.span ℤ (Set.range hexagonalBasis) := x.2
      rw [Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, hc⟩ := hx
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨c, Subtype.ext ?_⟩
      simpa using hc)

/-- The hexagonal lattice `A₂` has exact covolume `√3 / 2`. -/
theorem covolume_hexagonalLattice :
    ZLattice.covolume hexagonalLattice volume = √3 / 2 := by
  rw [covolume_eq_abs_det hexagonalLattice hexagonalZBasis]
  have hdet :
      (Matrix.of (fun i j : Fin 2 =>
        (hexagonalZBasis i : EuclideanSpace ℝ (Fin 2)) j)).det = √3 / 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, hexagonalZBasis, Basis.mk_apply, hexagonalBasis_zero,
      hexagonalBasis_one, hexVec0, hexVec1, WithLp.ofLp_toLp, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  rw [hdet, abs_of_pos (by positivity)]

/-- **Exact Hermite Constant `γ₂ = 2 / √3` & Optimal 2D Lattice Sphere Packing Density
`π / (2 √3)` (`hermite_dim2_hexagonal_tight`)**:
1. The hexagonal lattice `A₂` has `shortestNorm A₂ = 1`, `covol(A₂) = √3 / 2`, and attains the
   exact equality `shortestNorm A₂ ^ 2 / covol(A₂) = 2 / √3`.
2. For EVERY rank-2 lattice `Λ ⊂ ℝ²`, the open balls of radius `shortestNorm Λ / 2` centered at
   lattice points are pairwise disjoint and have packing density at most `π / (2 √3)`, with exact
   equality for `A₂`! -/
theorem hermite_dim2_hexagonal_tight :
    shortestNorm hexagonalLattice = 1 ∧
    shortestNorm hexagonalLattice ^ 2 / ZLattice.covolume hexagonalLattice volume = 2 / √3 ∧
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2))
      (shortestNorm hexagonalLattice / 2))).toReal /
        ZLattice.covolume hexagonalLattice volume = Real.pi / (2 * √3) ∧
    (∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2))) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
      (∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y →
        Disjoint (Metric.ball x (shortestNorm Λ / 2)) (Metric.ball y (shortestNorm Λ / 2))) ∧
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2))
        (shortestNorm Λ / 2))).toReal / ZLattice.covolume Λ volume ≤ Real.pi / (2 * √3)) := by
  have hbZ0 : (hexagonalZBasis 0 : EuclideanSpace ℝ (Fin 2)) = hexVec0 := by
    simp [hexagonalZBasis, hexagonalBasis_zero]
  have hbZ1 : (hexagonalZBasis 1 : EuclideanSpace ℝ (Fin 2)) = hexVec1 := by
    simp [hexagonalZBasis, hexagonalBasis_one]
  have hred : IsGaussReduced (hexagonalZBasis 0 : EuclideanSpace ℝ (Fin 2))
      (hexagonalZBasis 1 : EuclideanSpace ℝ (Fin 2)) := by
    rw [hbZ0, hbZ1]
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_hexVec0]; norm_num
    · rw [norm_hexVec0, norm_hexVec1]
    · rw [inner_hexVec0_hexVec1, norm_hexVec0]; norm_num
  have hshort : shortestNorm hexagonalLattice = 1 := by
    have hmin := shortestNorm_eq_of_min hexagonalLattice (hexagonalZBasis 0).2
      (norm_pos_iff.mp hred.1)
      (gauss_reduced_shortest_vector hexagonalLattice hexagonalZBasis hred)
    rw [hmin, hbZ0, norm_hexVec0]
  have hsqrt3 : (√3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  refine ⟨hshort, ?_, ?_, ?_⟩
  · rw [hshort, covolume_hexagonalLattice]
    field_simp [hsqrt3]
  · rw [hshort, covolume_hexagonalLattice, EuclideanSpace.volume_ball_fin_two,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.toReal_ofReal Real.pi_nonneg]
    field_simp [hsqrt3]
  · intro Λ _ _
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      rw [Set.disjoint_left]
      intro z hzx hzy
      rw [Metric.mem_ball, dist_eq_norm] at hzx hzy
      have hdiff_mem : x - y ∈ Λ := Λ.sub_mem hx hy
      have hdiff_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have hle : shortestNorm Λ ≤ ‖x - y‖ := shortestNorm_le_norm Λ hdiff_mem hdiff_ne
      have htri : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
        calc
          ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
          _ = ‖z - x‖ + ‖z - y‖ := add_comm _ _
      linarith
    · have hs_nonneg : 0 ≤ shortestNorm Λ / 2 :=
        div_nonneg (le_of_lt (shortestNorm_pos (by decide : 0 < 2) Λ)) (by norm_num)
      rw [EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hs_nonneg, ENNReal.toReal_ofReal Real.pi_nonneg]
      have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
      have hherm := hermite_dim2_le Λ
      rw [div_le_iff₀ hcov_pos]
      have hpi_nonneg : 0 ≤ Real.pi := Real.pi_nonneg
      have h1 : (shortestNorm Λ / 2) ^ 2 * Real.pi = (Real.pi / 4) * shortestNorm Λ ^ 2 := by ring
      have h2 : Real.pi / (2 * √3) * ZLattice.covolume Λ volume =
          (Real.pi / 4) * ((2 / √3) * ZLattice.covolume Λ volume) := by
        field_simp [hsqrt3]
        ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hherm (by positivity)

/-- Helper: membership in `t • Metric.closedBall 0 1` (`t > 0`) is equivalent to `‖x‖ ≤ t`. -/
private lemma mem_smul_unitClosedBall_iff {n : ℕ} {t : ℝ} (ht : 0 < t)
    {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ t • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ↔ ‖x‖ ≤ t := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    nlinarith
  · intro hle
    refine ⟨t⁻¹ • x, ?_, smul_inv_smul₀ ht.ne' x⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    rw [inv_mul_le_iff₀ ht]
    simpa using hle

/-- **Sharp 2D Minkowski Second Theorem (`minkowski_second_theorem_dim2`)**:
For EVERY full-rank lattice `Λ ⊂ ℝ²`, the first two Euclidean successive minima satisfy
`λ₁(Λ) * λ₂(Λ) ≤ (2 / √3) * covol(Λ)` (attained by any Gauss-reduced basis `(u, v)`). -/
theorem minkowski_second_theorem_dim2 (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) Λ 0 *
      successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) Λ 1 ≤
        (2 / √3) * ZLattice.covolume Λ volume := by
  obtain ⟨b, hred⟩ := exists_gauss_reduced_basis Λ
  set u : EuclideanSpace ℝ (Fin 2) := (b 0).1
  set v : EuclideanSpace ℝ (Fin 2) := (b 1).1
  set B2 : Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall 0 1
  have hu_pos : 0 < ‖u‖ := hred.1
  have huv : ‖u‖ ≤ ‖v‖ := hred.2.1
  have hv_pos : 0 < ‖v‖ := lt_of_lt_of_le hu_pos huv
  have hlam0 : successiveMinimum B2 Λ 0 = ‖u‖ := by
    unfold successiveMinimum
    refine le_antisymm ?_ ?_
    · refine csInf_le ⟨0, by rintro t ⟨ht, _⟩; exact ht.le⟩ ?_
      refine ⟨hu_pos, fun _ => u, fun _ => (b 0).2, ?_, fun _ => (mem_smul_unitClosedBall_iff hu_pos).mpr le_rfl⟩
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have h0 : g 0 • u = 0 := by simpa using hg
      have hu_ne : u ≠ 0 := norm_pos_iff.mp hu_pos
      intro i
      fin_cases i
      exact (smul_eq_zero.mp h0).resolve_right hu_ne
    · refine le_csInf ⟨‖u‖, hu_pos, fun _ => u, fun _ => (b 0).2, ?_,
        fun _ => (mem_smul_unitClosedBall_iff hu_pos).mpr le_rfl⟩ ?_
      · rw [Fintype.linearIndependent_iff]
        intro g hg
        have h0 : g 0 • u = 0 := by simpa using hg
        intro i
        fin_cases i
        exact (smul_eq_zero.mp h0).resolve_right (norm_pos_iff.mp hu_pos)
      · rintro t ⟨ht, w, hw_mem, hw_li, hw_ball⟩
        have hw0_ne : w 0 ≠ 0 := hw_li.ne_zero 0
        have hge : ‖u‖ ≤ ‖w 0‖ := gauss_reduced_shortest_vector Λ b hred (w 0) (hw_mem 0) hw0_ne
        have hle : ‖w 0‖ ≤ t := (mem_smul_unitClosedBall_iff ht).mp (hw_ball 0)
        exact le_trans hge hle
  have hb_li : LinearIndependent ℝ (fun i : Fin 2 => (b i : EuclideanSpace ℝ (Fin 2))) := by
    have heq : (fun i : Fin 2 => (b i : EuclideanSpace ℝ (Fin 2))) = ⇑(b.ofZLatticeBasis ℝ) :=
      funext fun i => (b.ofZLatticeBasis_apply ℝ Λ i).symm
    rw [heq]
    exact (b.ofZLatticeBasis ℝ).linearIndependent
  have hlam1 : successiveMinimum B2 Λ 1 = ‖v‖ := by
    unfold successiveMinimum
    have hmem_v : ‖v‖ ∈ { t : ℝ | 0 < t ∧ ∃ w : Fin 2 → EuclideanSpace ℝ (Fin 2),
        (∀ j, w j ∈ Λ) ∧ LinearIndependent ℝ w ∧ ∀ j, w j ∈ t • B2 } := by
      refine ⟨hv_pos, fun i => (b i : EuclideanSpace ℝ (Fin 2)), fun i => (b i).2, hb_li, ?_⟩
      intro j
      fin_cases j
      · exact (mem_smul_unitClosedBall_iff hv_pos).mpr huv
      · exact (mem_smul_unitClosedBall_iff hv_pos).mpr le_rfl
    refine le_antisymm ?_ ?_
    · exact csInf_le ⟨0, by rintro t ⟨ht, _⟩; exact ht.le⟩ hmem_v
    · refine le_csInf ⟨‖v‖, hmem_v⟩ ?_
      rintro t ⟨ht, w, hw_mem, hw_li, hw_ball⟩
      have hex_n : ∃ j : Fin 2, b.repr ⟨w j, hw_mem j⟩ 1 ≠ 0 := by
        by_contra hall
        push Not at hall
        set α0 : ℝ := (b.repr ⟨w 0, hw_mem 0⟩ 0 : ℝ)
        set α1 : ℝ := (b.repr ⟨w 1, hw_mem 1⟩ 0 : ℝ)
        have hw0 : w 0 = α0 • u := by
          have h := b.sum_repr ⟨w 0, hw_mem 0⟩
          rw [Fin.sum_univ_two, hall 0, zero_smul, add_zero] at h
          have hval := congrArg (Subtype.val : Λ → EuclideanSpace ℝ (Fin 2)) h.symm
          simpa [u, α0, ← Int.cast_smul_eq_zsmul ℝ] using hval
        have hw1 : w 1 = α1 • u := by
          have h := b.sum_repr ⟨w 1, hw_mem 1⟩
          rw [Fin.sum_univ_two, hall 1, zero_smul, add_zero] at h
          have hval := congrArg (Subtype.val : Λ → EuclideanSpace ℝ (Fin 2)) h.symm
          simpa [u, α1, ← Int.cast_smul_eq_zsmul ℝ] using hval
        let c : Fin 2 → ℝ := fun i => if i = 0 then α1 else -α0
        have hlin : ∑ i : Fin 2, c i • w i = 0 := by
          rw [Fin.sum_univ_two]
          change α1 • w 0 + (-α0) • w 1 = 0
          rw [hw0, hw1, smul_smul, smul_smul, ← add_smul]
          have : α1 * α0 + (-α0) * α1 = 0 := by ring
          rw [this, zero_smul]
        have hc1_zero := Fintype.linearIndependent_iff.mp hw_li c hlin 1
        have hc1' : α0 = 0 := by
          have : -α0 = 0 := by simpa [c] using hc1_zero
          linarith
        have : w 0 = 0 := by rw [hw0, hc1', zero_smul]
        exact hw_li.ne_zero 0 this
      obtain ⟨j, hj⟩ := hex_n
      have hwj_eq : w j = b.repr ⟨w j, hw_mem j⟩ 0 • u + b.repr ⟨w j, hw_mem j⟩ 1 • v := by
        have h := b.sum_repr ⟨w j, hw_mem j⟩
        rw [Fin.sum_univ_two] at h
        have hval := congrArg (Subtype.val : Λ → EuclideanSpace ℝ (Fin 2)) h.symm
        simpa [u, v] using hval
      have hge : ‖v‖ ≤ ‖w j‖ := by
        rw [hwj_eq]
        exact gauss_reduced_norm_ge_second hred hj
      have hle : ‖w j‖ ≤ t := (mem_smul_unitClosedBall_iff ht).mp (hw_ball j)
      exact le_trans hge hle
  rw [hlam0, hlam1]
  exact gauss_reduced_prod_norm_le Λ b hred

end GaussReductionDim2

/-! ## Section 3: Unconditional Minkowski's Second Theorem in Arbitrary Dimension `n ≥ 1` -/

section MinkowskiSecondTheorem

/-- If `K` is convex and `0 ∈ K`, then `s ≤ t` (`0 ≤ s`) implies `s • K ⊆ t • K`. -/
lemma smul_subset_smul_of_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} (hconv : Convex ℝ K) (h0 : (0 : E) ∈ K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    s • K ⊆ t • K := by
  rintro _ ⟨x, hx, rfl⟩
  by_cases ht : t = 0
  · have hs0 : s = 0 := le_antisymm (ht ▸ hst) hs
    rw [hs0, ht]
    exact ⟨x, hx, rfl⟩
  · have ht_pos : 0 < t := lt_of_le_of_ne (le_trans hs hst) (Ne.symm ht)
    have hmem : (s / t) • x + (1 - s / t) • (0 : E) ∈ K :=
      hconv hx h0 (div_nonneg hs ht_pos.le)
        (sub_nonneg.mpr ((div_le_one ht_pos).mpr hst)) (by ring)
    refine ⟨(s / t) • x + (1 - s / t) • (0 : E), hmem, ?_⟩
    change t • ((s / t) • x + (1 - s / t) • (0 : E)) = s • x
    rw [smul_zero, add_zero, smul_smul, mul_div_cancel₀ _ ht_pos.ne']

/-- Every symmetric convex set containing an interior point contains `0`. -/
lemma zero_mem_of_symm_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) (hne : K.Nonempty) :
    (0 : E) ∈ K := by
  obtain ⟨x, hx⟩ := hne
  have hmem := hconv hx (hsymm x hx) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa [smul_neg] using hmem

/-- Helper: if `v : Fin m → E` is `ℝ`-linearly independent and `x ∉ span ℝ (range v)`, then
`Fin.snoc v x : Fin (m + 1) → E` is `ℝ`-linearly independent. -/
private lemma linearIndependent_fin_snoc {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} {v : Fin m → E} (hv : LinearIndependent ℝ v)
    {x : E} (hx : x ∉ Submodule.span ℝ (Set.range v)) :
    LinearIndependent ℝ (Fin.snoc (α := fun _ => E) v x) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  have hsnoc_cast : ∀ i : Fin m, Fin.snoc (α := fun _ => E) v x i.castSucc = v i :=
    fun i => by simp [Fin.snoc_castSucc]
  have hsnoc_last : Fin.snoc (α := fun _ => E) v x (Fin.last m) = x := by simp [Fin.snoc_last]
  simp_rw [hsnoc_cast, hsnoc_last] at hg
  have hglast : g (Fin.last m) = 0 := by
    by_contra hne
    have hx_eq : x = ∑ i : Fin m, ((g (Fin.last m))⁻¹ * (-g i.castSucc)) • v i := by
      have h1 : g (Fin.last m) • x = -(∑ i : Fin m, g i.castSucc • v i) :=
        eq_neg_of_add_eq_zero_right hg
      have h2 := congrArg (fun z : E => (g (Fin.last m))⁻¹ • z) h1
      simp only [inv_smul_smul₀ hne, Finset.smul_sum, smul_smul, ← Finset.sum_neg_distrib,
        ← neg_smul] at h2
      exact h2
    have hx_mem : x ∈ Submodule.span ℝ (Set.range v) := by
      rw [hx_eq]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact hx hx_mem
  rw [hglast, zero_smul, add_zero] at hg
  have hgcast : ∀ i : Fin m, g i.castSucc = 0 :=
    Fintype.linearIndependent_iff.mp hv (fun i => g i.castSucc) hg
  intro i
  refine Fin.lastCases hglast hgcast i

/-- The defining set of `successiveMinimum K Λ k` is nonempty whenever `0 ∈ interior K`. -/
lemma successiveMinimum_set_nonempty {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (k : Fin n) :
    { t : ℝ | 0 < t ∧ ∃ v : Fin (k.1 + 1) → EuclideanSpace ℝ (Fin n),
      (∀ j, v j ∈ Λ) ∧ LinearIndependent ℝ v ∧ ∀ j, v j ∈ t • K }.Nonempty := by
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  let b := basisOfZLattice Λ
  let M : ℝ := (∑ i : Fin n, ‖(b i : EuclideanSpace ℝ (Fin n))‖) + 1
  have hM_pos : 0 < M := by
    have : 0 ≤ ∑ i : Fin n, ‖(b i : EuclideanSpace ℝ (Fin n))‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  let t₀ : ℝ := 2 * M / δ
  have ht₀_pos : 0 < t₀ := by positivity
  let emb : Fin (k.1 + 1) ↪ Fin n :=
    ⟨fun j => ⟨j.1, lt_of_lt_of_le j.2 k.2⟩, fun a b h => Fin.ext (by simpa using h)⟩
  let v : Fin (k.1 + 1) → EuclideanSpace ℝ (Fin n) := fun j => (b (emb j) : EuclideanSpace ℝ (Fin n))
  refine ⟨t₀, ht₀_pos, v, fun j => (b (emb j)).2, ?_, ?_⟩
  · have hb_li : LinearIndependent ℝ (fun i : Fin n => (b i : EuclideanSpace ℝ (Fin n))) := by
      have heq : (fun i : Fin n => (b i : EuclideanSpace ℝ (Fin n))) = ⇑(b.ofZLatticeBasis ℝ) :=
        funext fun i => (b.ofZLatticeBasis_apply ℝ Λ i).symm
      rw [heq]
      exact (b.ofZLatticeBasis ℝ).linearIndependent
    exact hb_li.comp emb emb.injective
  · intro j
    refine ⟨t₀⁻¹ • v j, hball ?_, smul_inv_smul₀ ht₀_pos.ne' (v j)⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht₀_pos.le)]
    have hle_M : ‖v j‖ ≤ M := by
      have h1 : ‖v j‖ ≤ ∑ i : Fin n, ‖(b i : EuclideanSpace ℝ (Fin n))‖ :=
        Finset.single_le_sum (f := fun i : Fin n => ‖(b i : EuclideanSpace ℝ (Fin n))‖)
          (fun i _ => norm_nonneg _) (Finset.mem_univ (emb j))
      linarith
    rw [inv_mul_lt_iff₀ ht₀_pos]
    have hmul : t₀ * δ = 2 * M := div_mul_cancel₀ _ hδ_pos.ne'
    linarith

/-- Positivity of every successive minimum `0 < successiveMinimum K Λ k` for a bounded set `K`
containing `0` in its interior. -/
theorem successiveMinimum_pos {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbdd : Bornology.IsBounded K)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (k : Fin n) :
    0 < successiveMinimum K Λ k := by
  have hn : 0 < n := Nat.pos_of_ne_zero (Fin.pos_iff_nonempty.mpr ⟨k⟩).ne'
  obtain ⟨R, hR_pos, hKR⟩ : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.closedBall 0 R := by
    obtain ⟨R₀, hR₀⟩ := hbdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
    refine ⟨max R₀ 1, by positivity, hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hshort_pos : 0 < shortestNorm Λ := shortestNorm_pos hn Λ
  have hlb : shortestNorm Λ / R ≤ successiveMinimum K Λ k := by
    unfold successiveMinimum
    refine le_csInf (successiveMinimum_set_nonempty h0 Λ k) ?_
    rintro t ⟨ht, v, hv_mem, hv_li, hv_K⟩
    have hv0_ne : v 0 ≠ 0 := hv_li.ne_zero 0
    have hge : shortestNorm Λ ≤ ‖v 0‖ := shortestNorm_le_norm Λ (hv_mem 0) hv0_ne
    obtain ⟨y, hyK, hyv⟩ := Set.mem_smul_set.mp (hv_K 0)
    have hyR : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hKR hyK
    have hv0_le : ‖v 0‖ ≤ t * R := by
      rw [← hyv, norm_smul, Real.norm_of_nonneg ht.le]
      exact mul_le_mul_of_nonneg_left hyR ht.le
    rw [div_le_iff₀ hR_pos]
    linarith
  exact lt_of_lt_of_le (div_pos hshort_pos hR_pos) hlb

/-- Monotonicity of successive minima: `i ≤ j → successiveMinimum K Λ i ≤ successiveMinimum K Λ j`. -/
theorem successiveMinimum_mono {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {i j : Fin n} (hij : i ≤ j) :
    successiveMinimum K Λ i ≤ successiveMinimum K Λ j := by
  unfold successiveMinimum
  refine csInf_le_csInf ⟨0, by rintro t ⟨ht, _⟩; exact ht.le⟩
    (successiveMinimum_set_nonempty h0 Λ j) ?_
  rintro t ⟨ht, v, hv_mem, hv_li, hv_K⟩
  let emb : Fin (i.1 + 1) ↪ Fin (j.1 + 1) :=
    ⟨Fin.castLE (Nat.succ_le_succ hij), Fin.castLE_injective _⟩
  refine ⟨ht, v ∘ emb, fun m => hv_mem (emb m), hv_li.comp emb emb.injective, fun m => hv_K (emb m)⟩

/-- Attainment at a single index `k : Fin n`: for a compact convex body `K` with `0 ∈ interior K`,
there exist `k + 1` linearly independent vectors of `Λ` lying in `successiveMinimum K Λ k • K`. -/
theorem exists_attaining_vecs_at_k {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ K) (hcpt : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (k : Fin n) :
    ∃ w : Fin (k.1 + 1) → EuclideanSpace ℝ (Fin n),
      (∀ j, w j ∈ Λ) ∧ LinearIndependent ℝ w ∧ ∀ j, w j ∈ successiveMinimum K Λ k • K := by
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := interior_subset h0
  set lam : ℝ := successiveMinimum K Λ k
  have hlam_pos : 0 < lam := successiveMinimum_pos hcpt.isBounded h0 Λ k
  let S : Set (EuclideanSpace ℝ (Fin n)) :=
    (Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ ((lam + 1) • K)
  have hS_fin : S.Finite :=
    lattice_inter_isBounded_finite Λ
      ((hcpt.image (continuous_const_smul (lam + 1))).isBounded)
  have : Finite S := hS_fin.to_subtype
  have hseq : ∀ m : ℕ, ∃ w : Fin (k.1 + 1) → S,
      LinearIndependent ℝ (fun j => (w j : EuclideanSpace ℝ (Fin n))) ∧
      ∀ j, (w j : EuclideanSpace ℝ (Fin n)) ∈ (lam + 1 / ((m : ℝ) + 1)) • K := by
    intro m
    have hlt : lam < lam + 1 / ((m : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    have hmem_ex : ∃ t ∈ { t : ℝ | 0 < t ∧ ∃ v : Fin (k.1 + 1) → EuclideanSpace ℝ (Fin n),
        (∀ j, v j ∈ Λ) ∧ LinearIndependent ℝ v ∧ ∀ j, v j ∈ t • K },
        t < lam + 1 / ((m : ℝ) + 1) :=
      (csInf_lt_iff ⟨0, by rintro t ⟨ht, _⟩; exact ht.le⟩
        (successiveMinimum_set_nonempty h0 Λ k)).mp hlt
    obtain ⟨t, ⟨ht_pos, v, hv_mem, hv_li, hv_K⟩, ht_lt⟩ := hmem_ex
    have hle1 : lam + 1 / ((m : ℝ) + 1) ≤ lam + 1 := by
      have : 1 / ((m : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      linarith
    have hv_in_step : ∀ j, v j ∈ (lam + 1 / ((m : ℝ) + 1)) • K := fun j =>
      smul_subset_smul_of_le hconv h0K ht_pos.le ht_lt.le (hv_K j)
    have hv_in_S : ∀ j, v j ∈ S := fun j =>
      ⟨hv_mem j, smul_subset_smul_of_le hconv h0K (by positivity) hle1 (hv_in_step j)⟩
    exact ⟨fun j => ⟨v j, hv_in_S j⟩, hv_li, hv_in_step⟩
  choose f hf_li hf_mem using hseq
  obtain ⟨w, hw_inf⟩ := Finite.exists_infinite_fiber f
  obtain ⟨m₀, hm₀⟩ := hw_inf.nonempty
  refine ⟨fun j => (w j : EuclideanSpace ℝ (Fin n)), fun j => (w j).2.1, ?_, ?_⟩
  · have : (fun j => (w j : EuclideanSpace ℝ (Fin n))) =
        (fun j => (f m₀ j : EuclideanSpace ℝ (Fin n))) := by
      rw [hm₀]
    rw [this]
    exact hf_li m₀
  · intro j
    refine ⟨lam⁻¹ • (w j : EuclideanSpace ℝ (Fin n)), ?_, smul_inv_smul₀ hlam_pos.ne' _⟩
    -- Extract a strictly increasing sequence `m_r` in `f ⁻¹' {w}` and pass to the limit in closed `K`.
    have hmem_K : ∀ m : ℕ, f m = w →
        (lam + 1 / ((m : ℝ) + 1))⁻¹ • (w j : EuclideanSpace ℝ (Fin n)) ∈ K := by
      intro m hm
      have h1 : (w j : EuclideanSpace ℝ (Fin n)) ∈ (lam + 1 / ((m : ℝ) + 1)) • K := by
        rw [← hm]
        exact hf_mem m j
      obtain ⟨y, hyK, hy_eq⟩ := Set.mem_smul_set.mp h1
      have hpos : 0 < lam + 1 / ((m : ℝ) + 1) := by positivity
      have : (lam + 1 / ((m : ℝ) + 1))⁻¹ • (w j : EuclideanSpace ℝ (Fin n)) = y := by
        rw [← hy_eq, inv_smul_smul₀ hpos.ne']
      rwa [this]
    have hclos : lam⁻¹ • (w j : EuclideanSpace ℝ (Fin n)) ∈ closure K := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have htend : Filter.Tendsto
          (fun m : ℕ => (lam + 1 / ((m : ℝ) + 1))⁻¹ • (w j : EuclideanSpace ℝ (Fin n)))
          Filter.atTop (nhds (lam⁻¹ • (w j : EuclideanSpace ℝ (Fin n)))) := by
        refine Filter.Tendsto.smul_const ?_ _
        have h1 : Filter.Tendsto (fun m : ℕ => lam + 1 / ((m : ℝ) + 1))
            Filter.atTop (nhds (lam + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h1
        exact h1.inv₀ hlam_pos.ne'
      rw [Metric.tendsto_atTop] at htend
      obtain ⟨N, hN⟩ := htend ε hε
      obtain ⟨m, hm_eq, hm_ge⟩ : ∃ m ∈ f ⁻¹' {w}, N ≤ m := by
        by_contra hnone
        push Not at hnone
        have hsub : f ⁻¹' {w} ⊆ (Finset.range N : Set ℕ) := fun m hm =>
          Finset.mem_coe.mpr (Finset.mem_range.mpr (hnone m hm))
        exact (Set.infinite_coe_iff.mp hw_inf) ((Finset.finite_toSet (Finset.range N)).subset hsub)
      exact ⟨(lam + 1 / ((m : ℝ) + 1))⁻¹ • (w j : EuclideanSpace ℝ (Fin n)),
        hmem_K m hm_eq, by simpa [dist_comm] using hN m hm_ge⟩
    rwa [hcpt.isClosed.closure_eq] at hclos

/-- **Simultaneous Attainment of All Successive Minima (`exists_attaining_basis`)**:
For any compact convex body `K` with `0 ∈ interior K` and full-rank lattice `Λ ⊂ ℝ^n`, there exist
`n` linearly independent lattice vectors `v : Fin n → ℝ^n` with `v i ∈ successiveMinimum K Λ i • K`
for every `i : Fin n`. -/
theorem exists_attaining_basis {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ K) (hcpt : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
      (∀ i, v i ∈ Λ) ∧ LinearIndependent ℝ v ∧ ∀ i, v i ∈ successiveMinimum K Λ i • K := by
  suffices ∀ m : ℕ, (hm : m ≤ n) →
      ∃ v : Fin m → EuclideanSpace ℝ (Fin n),
        (∀ i, v i ∈ Λ) ∧ LinearIndependent ℝ v ∧
        ∀ i, v i ∈ successiveMinimum K Λ ⟨i.1, lt_of_lt_of_le i.2 hm⟩ • K by
    exact this n le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨v, hv_mem, hv_li, hv_K⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨w, hw_mem, hw_li, hw_K⟩ :=
      exists_attaining_vecs_at_k hconv hcpt h0 Λ ⟨m, hm⟩
    have hex : ∃ j : Fin (m + 1), w j ∉ Submodule.span ℝ (Set.range v) := by
      by_contra hall
      push Not at hall
      have hspan_le : Submodule.span ℝ (Set.range w) ≤ Submodule.span ℝ (Set.range v) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact hall j
      have hrw : Module.finrank ℝ (Submodule.span ℝ (Set.range w)) = m + 1 := by
        rw [finrank_span_eq_card hw_li, Fintype.card_fin]
      have hrv : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = m := by
        rw [finrank_span_eq_card hv_li, Fintype.card_fin]
      have hle := Submodule.finrank_mono hspan_le
      omega
    obtain ⟨j, hj⟩ := hex
    refine ⟨Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin n)) v (w j), ?_,
      linearIndependent_fin_snoc hv_li hj, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa using hw_mem j
      · intro l; simpa using hv_mem l
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa using hw_K j
      · intro l; simpa using hv_K l

/-- **Flag Containment Lemma (`flag_containment`)**:
If `v : Fin n → ℝ^n` attains all successive minima of `Λ` for `K`, then for every `k : Fin n` and
every `0 < t < successiveMinimum K Λ k`, any lattice point `x ∈ Λ ∩ (t • K)` lies in the
`k`-dimensional subspace `span ℝ { v j | j < k }`. -/
theorem flag_containment {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {v : Fin n → EuclideanSpace ℝ (Fin n)} (hv_mem : ∀ i, v i ∈ Λ) (hv_li : LinearIndependent ℝ v)
    (hv_K : ∀ i, v i ∈ successiveMinimum K Λ i • K)
    {k : Fin n} {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < successiveMinimum K Λ k)
    {x : EuclideanSpace ℝ (Fin n)} (hxΛ : x ∈ Λ) (hxK : x ∈ t • K) :
    x ∈ Submodule.span ℝ (v '' {j : Fin n | j < k}) := by
  classical
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := interior_subset h0
  let S : Finset (Fin n) := Finset.univ.filter fun m => t < successiveMinimum K Λ m
  have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, ht_lt⟩
  let k₀ : Fin n := S.min' ⟨k, hkS⟩
  have hk₀_mem : k₀ ∈ S := Finset.min'_mem S ⟨k, hkS⟩
  have hk₀_lt : t < successiveMinimum K Λ k₀ := (Finset.mem_filter.mp hk₀_mem).2
  have hk₀_le_k : k₀ ≤ k := Finset.min'_le S k hkS
  have hprev_le : ∀ j : Fin n, j < k₀ → successiveMinimum K Λ j ≤ t := by
    intro j hj
    by_contra hgt
    push Not at hgt
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hgt⟩
    exact not_le_of_gt hj (Finset.min'_le S j hjS)
  let emb : Fin k₀.1 ↪ Fin n :=
    ⟨fun j => ⟨j.1, lt_trans j.2 k₀.2⟩, fun a b h => Fin.ext (by simpa using h)⟩
  let v₀ : Fin k₀.1 → EuclideanSpace ℝ (Fin n) := v ∘ emb
  have hv₀_li : LinearIndependent ℝ v₀ := hv_li.comp emb emb.injective
  have hx_in_span : x ∈ Submodule.span ℝ (Set.range v₀) := by
    by_contra hx_not
    let w : Fin (k₀.1 + 1) → EuclideanSpace ℝ (Fin n) :=
      Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin n)) v₀ x
    have hw_li : LinearIndependent ℝ w := linearIndependent_fin_snoc hv₀_li hx_not
    have hw_mem : ∀ j, w j ∈ Λ := fun j =>
      Fin.lastCases (by simpa [w] using hxΛ) (fun l => by simpa [w, v₀] using hv_mem (emb l)) j
    have hw_K : ∀ j, w j ∈ t • K := fun j =>
      Fin.lastCases (by simpa [w] using hxK) (fun l => by
        have hlt_k₀ : emb l < k₀ := l.2
        have hle_t : successiveMinimum K Λ (emb l) ≤ t := hprev_le (emb l) hlt_k₀
        have hlam_nonneg : 0 ≤ successiveMinimum K Λ (emb l) :=
          Real.sInf_nonneg (by rintro r ⟨hr, _⟩; exact hr.le)
        simpa [w, v₀] using smul_subset_smul_of_le hconv h0K hlam_nonneg hle_t (hv_K (emb l))) j
    have hle : successiveMinimum K Λ k₀ ≤ t :=
      csInf_le ⟨0, by rintro r ⟨hr, _⟩; exact hr.le⟩ ⟨ht_pos, w, hw_mem, hw_li, hw_K⟩
    exact not_lt_of_ge hle hk₀_lt
  refine Submodule.span_mono ?_ hx_in_span
  rintro _ ⟨l, rfl⟩
  exact ⟨emb l, lt_of_lt_of_le l.2 hk₀_le_k, rfl⟩

/-- **Minkowski's Second Theorem — Lower Bound (`minkowski_second_theorem_lower`)**:
For EVERY `n ≥ 1`, every full-rank lattice `Λ ⊂ ℝ^n`, and every compact symmetric convex body
`K ⊆ ℝ^n` with `0 ∈ interior K`:
`(2^n / n!) * covol(Λ) ≤ (∏ i : Fin n, successiveMinimum K Λ i) * (volume K).toReal`. -/
theorem minkowski_second_theorem_lower {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hcpt : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ((2 : ℝ) ^ n / (n.factorial : ℝ)) * ZLattice.covolume Λ volume ≤
      (∏ i : Fin n, successiveMinimum K Λ i) * (volume K).toReal := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := interior_subset h0
  obtain ⟨v, hv_mem, hv_li, hv_K⟩ := exists_attaining_basis hconv hcpt h0 Λ
  let lam : Fin n → ℝ := fun i => successiveMinimum K Λ i
  have hlam_pos : ∀ i, 0 < lam i := fun i => successiveMinimum_pos hcpt.isBounded h0 Λ i
  let u : Fin n → EuclideanSpace ℝ (Fin n) := fun i => (lam i)⁻¹ • v i
  have hu_mem : ∀ i, u i ∈ K := fun i => by
    obtain ⟨y, hyK, hyv⟩ := Set.mem_smul_set.mp (hv_K i)
    have : u i = y := by
      dsimp only [u, lam]
      rw [← hyv, inv_smul_smul₀ (hlam_pos i).ne']
    rwa [this]
  -- Linear map `T : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)` sending `e_i ↦ u i`.
  let T : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun c => ∑ i : Fin n, c i • u i
      map_add' := fun c₁ c₂ => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  -- Cross-polytope `B₁ = { c : Fin n → ℝ | ∑ i, |c i| ≤ 1 }`.
  let B₁ : Set (Fin n → ℝ) := { c : Fin n → ℝ | ∑ i : Fin n, |c i| ≤ 1 }
  have hTB_sub : T '' B₁ ⊆ K := by
    rintro _ ⟨c, hc, rfl⟩
    let w : Option (Fin n) → ℝ := fun o =>
      match o with
      | none => 1 - ∑ i : Fin n, |c i|
      | some i => |c i|
    let p : Option (Fin n) → EuclideanSpace ℝ (Fin n) := fun o =>
      match o with
      | none => 0
      | some i => if 0 ≤ c i then u i else -u i
    have hw_nonneg : ∀ o ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ w o := by
      intro o _
      cases o with
      | none => exact sub_nonneg.mpr hc
      | some i => exact abs_nonneg (c i)
    have hw_sum : ∑ o : Option (Fin n), w o = 1 := by
      rw [Fintype.sum_option]
      simp [w]
    have hp_mem : ∀ o ∈ (Finset.univ : Finset (Option (Fin n))), p o ∈ K := by
      intro o _
      cases o with
      | none => exact h0K
      | some i =>
        dsimp only [p]
        split_ifs
        · exact hu_mem i
        · exact hsymm _ (hu_mem i)
    have hcomb := hconv.sum_mem hw_nonneg hw_sum hp_mem
    have hTc : T c = ∑ o : Option (Fin n), w o • p o := by
      rw [Fintype.sum_option]
      simp only [w, p, smul_zero, zero_add, T, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hci
      · rw [abs_of_nonneg hci]
      · rw [abs_of_neg (lt_of_not_ge hci), smul_neg, neg_smul, neg_neg]
    rwa [hTc]
  -- Exact volume of the L¹ unit ball `B₁`: `volume B₁ = ofReal (2^n / n!)`.
  have hvol_B₁ : volume B₁ = ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by
    have hB₁_eq : B₁ = {x : Fin n → ℝ | (∑ i : Fin n, |x i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ 1} := by
      ext c
      simp [B₁]
    rw [hB₁_eq, MeasureTheory.volume_sum_rpow_le (ι := Fin n) (p := 1) le_rfl 1]
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul, div_one]
    have hG2 : Real.Gamma (1 + 1 : ℝ) = 1 := by
      simpa using Real.Gamma_nat_eq_factorial 1
    have hGn : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n
    rw [hG2, hGn, mul_one]
  -- Express `volume (T '' B₁)` via `addHaar_image_linearMap` on `Fin n → ℝ`.
  let T_pi : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap.comp T
  have hvol_image :
      volume (T '' B₁) = ENNReal.ofReal |LinearMap.det T_pi| * volume B₁ := by
    have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
        volume volume := PiLp.volume_preserving_toLp (Fin n)
    have himg : (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' (T '' B₁) =
        T_pi '' B₁ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image, T_pi, LinearMap.comp_apply]
      constructor
      · rintro ⟨c, hc, hTc⟩
        exact ⟨c, hc, congrArg WithLp.ofLp hTc⟩
      · rintro ⟨c, hc, hTc⟩
        refine ⟨c, hc, ?_⟩
        exact (WithLp.ofLp_injective 2) hTc
    have hmeas_TB : NullMeasurableSet (T '' B₁) volume := by
      have hB₁_cpt : IsCompact B₁ := by
        refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
        · exact isClosed_le (continuous_finsetSum _ fun i _ =>
            continuous_abs.comp (continuous_apply i)) continuous_const
        · rw [Metric.isBounded_iff_subset_closedBall 0]
          refine ⟨1, fun c hc => ?_⟩
          rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
          intro i
          rw [Real.norm_eq_abs]
          exact le_trans (Finset.single_le_sum (f := fun j => |c j|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ i)) hc
      exact (hB₁_cpt.image T.continuous_of_finiteDimensional).measurableSet.nullMeasurableSet
    rw [← hmp.measure_preimage hmeas_TB, himg, Measure.addHaar_image_linearMap volume T_pi B₁]
  -- Relate `|det T_pi|` to `covol(Λ)` via the integer transition matrix from `basisOfZLattice Λ` to `v`.
  let bΛ := basisOfZLattice Λ
  let M_int : Matrix (Fin n) (Fin n) ℤ := fun i j => bΛ.repr ⟨v i, hv_mem i⟩ j
  let Mat_v : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => v i j
  let Mat_u : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => u i j
  let Mat_b : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (bΛ i : EuclideanSpace ℝ (Fin n)) j
  have hMat_v_eq : Mat_v = M_int.map (Int.cast : ℤ → ℝ) * Mat_b := by
    ext i j
    change (v i).ofLp j = ∑ k : Fin n, ((bΛ.repr ⟨v i, hv_mem i⟩ k : ℤ) : ℝ) *
      (bΛ k : EuclideanSpace ℝ (Fin n)).ofLp j
    have hsum : ∑ k : Fin n, (bΛ.repr ⟨v i, hv_mem i⟩ k : ℝ) • (bΛ k : EuclideanSpace ℝ (Fin n)) =
        v i := by
      have h := congrArg (Subtype.val : Λ → EuclideanSpace ℝ (Fin n)) (bΛ.sum_repr ⟨v i, hv_mem i⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
        ← Int.cast_smul_eq_zsmul ℝ] at h
      exact h
    have hval := congrFun (congrArg WithLp.ofLp hsum.symm) j
    simpa using hval
  have hMat_v_diag : Mat_v = Matrix.diagonal lam * Mat_u := by
    ext i j
    simp only [Mat_v, Mat_u, Matrix.of_apply, Matrix.diagonal_mul, u,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (hlam_pos i).ne', one_mul]
  have hdet_T_pi : LinearMap.det T_pi = Mat_u.det := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n)) T_pi, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp [T_pi, T, Mat_u]
  have hdet_v_ne : Mat_v.det ≠ 0 := by
    intro h0det
    obtain ⟨c, hc_ne, hc_mul⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0det
    have hsum0 : ∑ i : Fin n, c i • v i = 0 := by
      ext j
      have hj := congrFun hc_mul j
      simpa [Matrix.vecMul, dotProduct, Mat_v] using hj
    have hc0 : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp hv_li c hsum0
    exact hc_ne (funext hc0)
  have hdet_map : (M_int.map (Int.cast : ℤ → ℝ)).det = (M_int.det : ℝ) := by
    have h := (Int.castRingHom ℝ).map_det M_int
    simpa [RingHom.mapMatrix_apply] using h.symm
  have hM_det_ne : M_int.det ≠ 0 := by
    intro h0M
    have h1 : Mat_v.det = ((M_int.det : ℤ) : ℝ) * Mat_b.det := by
      rw [hMat_v_eq, Matrix.det_mul, hdet_map]
    rw [h0M, Int.cast_zero, zero_mul] at h1
    exact hdet_v_ne h1
  have hcov_le : ZLattice.covolume Λ volume ≤ (∏ i : Fin n, lam i) * |LinearMap.det T_pi| := by
    rw [covolume_eq_abs_det Λ bΛ]
    have h1 : |Mat_v.det| = |(M_int.det : ℝ)| * |Mat_b.det| := by
      rw [hMat_v_eq, Matrix.det_mul, abs_mul, hdet_map]
    have h2 : |Mat_v.det| = (∏ i : Fin n, lam i) * |LinearMap.det T_pi| := by
      rw [hMat_v_diag, Matrix.det_mul, Matrix.det_diagonal, abs_mul,
        abs_of_pos (Finset.prod_pos fun i _ => hlam_pos i), hdet_T_pi]
    have hM_ge1 : (1 : ℝ) ≤ |(M_int.det : ℝ)| := by
      have : (1 : ℤ) ≤ |M_int.det| := Int.one_le_abs hM_det_ne
      exact_mod_cast this
    change |Mat_b.det| ≤ (∏ i : Fin n, lam i) * |LinearMap.det T_pi|
    nlinarith [abs_nonneg Mat_b.det]
  have hvol_le : (volume (T '' B₁)).toReal ≤ (volume K).toReal :=
    ENNReal.toReal_mono hcpt.measure_lt_top.ne (measure_mono hTB_sub)
  have hvol_TB_real : (volume (T '' B₁)).toReal =
      |LinearMap.det T_pi| * ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by
    rw [hvol_image, hvol_B₁, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity)]
  have hprod_pos : 0 < ∏ i : Fin n, lam i := Finset.prod_pos fun i _ => hlam_pos i
  calc
    ((2 : ℝ) ^ n / (n.factorial : ℝ)) * ZLattice.covolume Λ volume
        ≤ ((2 : ℝ) ^ n / (n.factorial : ℝ)) * ((∏ i : Fin n, lam i) * |LinearMap.det T_pi|) :=
          mul_le_mul_of_nonneg_left hcov_le (by positivity)
    _ = (∏ i : Fin n, lam i) * (volume (T '' B₁)).toReal := by
          rw [hvol_TB_real]; ring
    _ ≤ (∏ i : Fin n, lam i) * (volume K).toReal :=
          mul_le_mul_of_nonneg_left hvol_le hprod_pos.le

/-! ### Barycenter Fiber Compression Engine & Unconditional Upper Bound -/

/-- The barycenter `(vol F)⁻¹ • ∫_{x ∈ F} x dx` of any closed, bounded, convex set `F ⊆ ℝ^ι` of
strictly positive volume belongs to `F`. -/
private lemma barycenter_mem_of_convex_isClosed {ι : Type*} [Fintype ι]
    {F : Set (ι → ℝ)} (hconv : Convex ℝ F) (hclosed : IsClosed F)
    (hbdd : Bornology.IsBounded F) (hpos : 0 < (volume F).toReal) :
    ((volume F).toReal)⁻¹ • (∫ x in F, x ∂volume) ∈ F := by
  by_contra hc
  obtain ⟨f, u, hfc, hfb⟩ := geometric_hahn_banach_point_closed hconv hclosed hc
  have hF_cpt : IsCompact F := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hF_fin : volume F < ⊤ := hbdd.measure_lt_top
  have hint_id : IntegrableOn (id : (ι → ℝ) → (ι → ℝ)) F volume :=
    continuousOn_id.integrableOn_compact hF_cpt
  have hint_f : IntegrableOn (fun x => f x) F volume :=
    f.continuous.continuousOn.integrableOn_compact hF_cpt
  have hint_const : IntegrableOn (fun _ : ι → ℝ => u) F volume :=
    integrableOn_const (hs := hF_fin.ne)
  have hcomp : f (∫ x in F, x ∂volume) = ∫ x in F, f x ∂volume :=
    (f.integral_comp_comm hint_id).symm
  have hmono : ∫ _ in F, u ∂volume ≤ ∫ x in F, f x ∂volume :=
    setIntegral_mono_on hint_const hint_f hclosed.measurableSet (fun b hb => (hfb b hb).le)
  have hconst_eq : ∫ _ in F, u ∂volume = (volume F).toReal * u := by
    rw [setIntegral_const, Measure.real, smul_eq_mul]
  have hfc_eq : f (((volume F).toReal)⁻¹ • (∫ x in F, x ∂volume)) =
      ((volume F).toReal)⁻¹ * ∫ x in F, f x ∂volume := by
    rw [map_smul, hcomp, smul_eq_mul]
  have hu_le : u ≤ f (((volume F).toReal)⁻¹ • (∫ x in F, x ∂volume)) := by
    rw [hfc_eq, ← mul_le_mul_iff_left₀ hpos, mul_right_comm, inv_mul_cancel₀ hpos.ne', one_mul]
    linarith
  linarith

/-- One step of inductive barycenter fiber compression on `Fin n → ℝ`, reducing from level `m` to
level `m - 1` (`1 ≤ m ≤ n`) while scaling volume by `(r_prev / r_curr)^m`. -/
private lemma compress_step {n m : ℕ} (hmn : m ≤ n)
    {K_pi : Set (Fin n → ℝ)} {Λ_pi : Submodule ℤ (Fin n → ℝ)}
    {r_prev r_curr : ℝ} (hr_prev_pos : 0 < r_prev) (hr_le : r_prev ≤ r_curr)
    (hflag : ∀ x ∈ Λ_pi, x ∈ r_prev • K_pi → ∀ j : Fin n, m - 1 ≤ j.1 → x j = 0)
    {S : Set (Fin n → ℝ)}
    (hS_meas : MeasurableSet S)
    (hS_bdd : Bornology.IsBounded S)
    (hS_fiber_conv : ∀ y : {i : Fin n // m ≤ i.1} → ℝ,
      Convex ℝ { x : {i : Fin n // ¬ m ≤ i.1} → ℝ |
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
          (fun i : Fin n => m ≤ i.1)).symm (y, x) ∈ S })
    (hS_fiber_closed : ∀ y : {i : Fin n // m ≤ i.1} → ℝ,
      IsClosed { x : {i : Fin n // ¬ m ≤ i.1} → ℝ |
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
          (fun i : Fin n => m ≤ i.1)).symm (y, x) ∈ S })
    (hS_diff : ∀ p ∈ S, ∀ q ∈ S, (∀ j : Fin n, m ≤ j.1 → p j = q j) → p - q ∈ r_curr • K_pi)
    (hS_lat : ∀ p ∈ S, ∀ q ∈ S, p - q ∈ Λ_pi → ∀ j : Fin n, m ≤ j.1 → p j = q j) :
    ∃ S' : Set (Fin n → ℝ),
      S' ⊆ S ∧
      MeasurableSet S' ∧
      Bornology.IsBounded S' ∧
      volume S' = ENNReal.ofReal ((r_prev / r_curr) ^ m) * volume S ∧
      (∀ y : {i : Fin n // m - 1 ≤ i.1} → ℝ,
        Convex ℝ { x : {i : Fin n // ¬ m - 1 ≤ i.1} → ℝ |
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
            (fun i : Fin n => m - 1 ≤ i.1)).symm (y, x) ∈ S' }) ∧
      (∀ y : {i : Fin n // m - 1 ≤ i.1} → ℝ,
        IsClosed { x : {i : Fin n // ¬ m - 1 ≤ i.1} → ℝ |
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
            (fun i : Fin n => m - 1 ≤ i.1)).symm (y, x) ∈ S' }) ∧
      (∀ p ∈ S', ∀ q ∈ S', (∀ j : Fin n, m - 1 ≤ j.1 → p j = q j) → p - q ∈ r_prev • K_pi) ∧
      (∀ p ∈ S', ∀ q ∈ S', p - q ∈ Λ_pi → ∀ j : Fin n, m - 1 ≤ j.1 → p j = q j) := by
  let Y := {i : Fin n // m ≤ i.1} → ℝ
  let X := {i : Fin n // ¬ m ≤ i.1} → ℝ
  let e : (Fin n → ℝ) ≃ᵐ Y × X :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i : Fin n => m ≤ i.1)
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i : Fin n => m ≤ i.1)
  have hr_curr_pos : 0 < r_curr := lt_of_lt_of_le hr_prev_pos hr_le
  set α : ℝ := r_prev / r_curr
  have hα_pos : 0 < α := div_pos hr_prev_pos hr_curr_pos
  have hα_le1 : α ≤ 1 := (div_le_one hr_curr_pos).mpr hr_le
  have hcardX : Fintype.card {i : Fin n // ¬ m ≤ i.1} = m := by
    have h1 : Fintype.card {i : Fin n // ¬ m ≤ i.1} = Fintype.card (Fin m) := by
      refine Fintype.card_congr ?_
      exact
        { toFun := fun i => ⟨i.1.1, Nat.lt_of_not_ge i.2⟩
          invFun := fun j => ⟨⟨j.1, lt_of_lt_of_le j.2 hmn⟩, Nat.not_le.mpr j.2⟩
          left_inv := fun i => Subtype.ext (Fin.ext rfl)
          right_inv := fun j => Fin.ext rfl }
    simpa using h1
  let T : Set (Y × X) := e.symm ⁻¹' S
  have hT_meas : MeasurableSet T := hS_meas.preimage e.symm.measurable
  have hvol_T : volume T = volume S := hmp.symm.measure_preimage hS_meas.nullMeasurableSet
  let F : Y → Set X := fun y => Prod.mk y ⁻¹' T
  have hF_eq : ∀ y : Y, F y = { x : X | e.symm (y, x) ∈ S } := fun _ => rfl
  have hF_bdd : ∀ y : Y, Bornology.IsBounded (F y) := by
    obtain ⟨R, hR⟩ := hS_bdd.subset_closedBall (0 : Fin n → ℝ)
    intro y
    rw [Metric.isBounded_iff_subset_closedBall (0 : X)]
    refine ⟨max R 0, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right R 0)]
    intro i
    have hmemS : e.symm (y, x) ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at hmemS
    have hi_le : ‖e.symm (y, x) i.1‖ ≤ R := le_trans (norm_le_pi_norm _ i.1) hmemS
    have hcoord : e.symm (y, x) i.1 = x i := by
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.2]
    rw [← hcoord]
    exact le_trans hi_le (le_max_left R 0)
  let v : Y → ℝ := fun y => ∫ x : X, T.indicator (fun _ => (1 : ℝ)) (y, x) ∂volume
  let w : Y → X := fun y => ∫ x : X, T.indicator (fun q => q.2) (y, x) ∂volume
  let c : Y → X := fun y => (v y)⁻¹ • w y
  have hv_meas : Measurable v :=
    ((stronglyMeasurable_const.indicator hT_meas).integral_prod_right').measurable
  have hw_meas : Measurable w :=
    ((continuous_snd.stronglyMeasurable.indicator hT_meas).integral_prod_right').measurable
  have hc_meas : Measurable c := hv_meas.inv.smul hw_meas
  have hv_eq : ∀ y : Y, v y = (volume (F y)).toReal := by
    intro y
    have hFy_meas : MeasurableSet (F y) := (hS_fiber_closed y).measurableSet
    have hfun : ∀ x : X, T.indicator (fun _ => (1 : ℝ)) (y, x) = (F y).indicator 1 x := by
      intro x
      by_cases hx : (y, x) ∈ T <;> simp [F, hx]
    dsimp only [v]
    simp_rw [hfun]
    rw [integral_indicator_one hFy_meas, Measure.real]
  have hw_eq : ∀ y : Y, w y = ∫ x in F y, x ∂volume := by
    intro y
    have hFy_meas : MeasurableSet (F y) := (hS_fiber_closed y).measurableSet
    have hfun : ∀ x : X, T.indicator (fun q => q.2) (y, x) = (F y).indicator (fun z => z) x := by
      intro x
      by_cases hx : (y, x) ∈ T <;> simp [F, hx]
    dsimp only [w]
    simp_rw [hfun]
    rw [integral_indicator hFy_meas]
  have hc_mem : ∀ y : Y, 0 < v y → c y ∈ F y := by
    intro y hvy
    dsimp only [c]
    rw [hv_eq y, hw_eq y]
    exact barycenter_mem_of_convex_isClosed (hS_fiber_conv y) (hS_fiber_closed y) (hF_bdd y)
      (hv_eq y ▸ hvy)
  let T' : Set (Y × X) :=
    { q : Y × X | 0 < v q.1 ∧ (q.1, c q.1 + α⁻¹ • (q.2 - c q.1)) ∈ T }
  have hT'_meas : MeasurableSet T' := by
    have h1 : MeasurableSet { q : Y × X | 0 < v q.1 } :=
      measurableSet_Ioi.preimage (hv_meas.comp measurable_fst)
    have hmap : Measurable (fun q : Y × X => (q.1, c q.1 + α⁻¹ • (q.2 - c q.1))) := by
      refine measurable_fst.prodMk ?_
      exact (hc_meas.comp measurable_fst).add
        ((measurable_snd.sub (hc_meas.comp measurable_fst)).const_smul α⁻¹)
    exact h1.inter (hT_meas.preimage hmap)
  have hT'_sub : T' ⊆ T := by
    rintro ⟨y, x'⟩ ⟨hvy, hx⟩
    have hcy : c y ∈ F y := hc_mem y hvy
    have hxF : c y + α⁻¹ • (x' - c y) ∈ F y := hx
    have hcomb : (1 - α) • c y + α • (c y + α⁻¹ • (x' - c y)) ∈ F y :=
      (hS_fiber_conv y) hcy hxF (sub_nonneg.mpr hα_le1) hα_pos.le (by ring)
    have hEq : (1 - α) • c y + α • (c y + α⁻¹ • (x' - c y)) = x' := by
      rw [smul_add, smul_inv_smul₀ hα_pos.ne', sub_smul, one_smul]
      abel
    rwa [hEq] at hcomb
  let F' : Y → Set X := fun y => Prod.mk y ⁻¹' T'
  have hF'_eq_pos : ∀ y : Y, 0 < v y → F' y = (c y - α • c y) +ᵥ (α • F y) := by
    intro y hvy
    ext x'
    simp only [F', T', Set.mem_preimage, Set.mem_ofPred_eq, hvy, true_and, Set.mem_vadd_set,
      Set.mem_smul_set, vadd_eq_add]
    constructor
    · intro hx
      refine ⟨α • (c y + α⁻¹ • (x' - c y)), ⟨c y + α⁻¹ • (x' - c y), hx, rfl⟩, ?_⟩
      rw [smul_add, smul_inv_smul₀ hα_pos.ne']
      abel
    · rintro ⟨_, ⟨x, hxF, rfl⟩, rfl⟩
      have hsimpl : c y + α⁻¹ • ((c y - α • c y + α • x) - c y) = x := by
        have h1 : (c y - α • c y + α • x) - c y = α • (x - c y) := by
          rw [smul_sub]; abel
        rw [h1, inv_smul_smul₀ hα_pos.ne']
        abel
      simpa [F, hsimpl] using hxF
  have hF'_vol : ∀ y : Y, volume (F' y) = ENNReal.ofReal (α ^ m) * volume (F y) := by
    intro y
    by_cases hvy : 0 < v y
    · rw [hF'_eq_pos y hvy, measure_vadd, Measure.addHaar_smul_of_nonneg volume hα_pos.le,
        Module.finrank_pi, hcardX]
    · have hF'_empty : F' y = ∅ := by
        ext x'
        simp [F', T', hvy]
      have hFy_zero : volume (F y) = 0 := by
        have hle0 : (volume (F y)).toReal ≤ 0 := by
          rw [← hv_eq y]
          exact le_of_not_gt hvy
        have hfin : volume (F y) ≠ ⊤ := (hF_bdd y).measure_lt_top.ne
        exact (ENNReal.toReal_eq_zero_iff (volume (F y))).mp
          (le_antisymm hle0 ENNReal.toReal_nonneg) |>.resolve_right hfin
      rw [hF'_empty, hFy_zero, measure_empty, mul_zero]
  have hvol_T' : volume T' = ENNReal.ofReal (α ^ m) * volume T := by
    have h1 : volume T' = ∫⁻ y : Y, volume (F' y) ∂volume := by
      rw [Measure.volume_eq_prod, Measure.prod_apply hT'_meas]
    have h2 : volume T = ∫⁻ y : Y, volume (F y) ∂volume := by
      rw [Measure.volume_eq_prod, Measure.prod_apply hT_meas]
    rw [h1, h2]
    simp_rw [hF'_vol]
    rw [lintegral_const_mul _ (measurable_measure_prodMk_left hT_meas)]
  have hF'_conv : ∀ y : Y, Convex ℝ (F' y) := by
    intro y
    by_cases hvy : 0 < v y
    · rw [hF'_eq_pos y hvy]
      exact ((hS_fiber_conv y).smul α).vadd (c y - α • c y)
    · have hF'_empty : F' y = ∅ := by ext x'; simp [F', T', hvy]
      rw [hF'_empty]
      exact convex_empty
  have hF'_closed : ∀ y : Y, IsClosed (F' y) := by
    intro y
    by_cases hvy : 0 < v y
    · have hcont : Continuous (fun x' : X => c y + α⁻¹ • (x' - c y)) :=
        continuous_const.add ((continuous_id.sub continuous_const).const_smul α⁻¹)
      have hpre : F' y = (fun x' : X => c y + α⁻¹ • (x' - c y)) ⁻¹' (F y) := by
        ext x'
        simp [F', T', F, hvy]
      rw [hpre]
      exact (hS_fiber_closed y).preimage hcont
    · have hF'_empty : F' y = ∅ := by ext x'; simp [F', T', hvy]
      rw [hF'_empty]
      exact isClosed_empty
  -- Pull back `T'` to `S' ⊆ Fin n → ℝ`.
  let S' : Set (Fin n → ℝ) := e ⁻¹' T'
  have hS'_sub : S' ⊆ S := fun p hp => by
    have hpT : e p ∈ T := hT'_sub hp
    simpa [T] using hpT
  have hS'_meas : MeasurableSet S' := hT'_meas.preimage e.measurable
  have hS'_bdd : Bornology.IsBounded S' := hS_bdd.subset hS'_sub
  have hS'_vol : volume S' = ENNReal.ofReal (α ^ m) * volume S := by
    rw [hmp.measure_preimage hT'_meas.nullMeasurableSet, hvol_T', hvol_T]
  -- Helper: key difference property whenever `p, q ∈ S'` agree on all coordinates `≥ m`.
  have hdiff_m : ∀ p ∈ S', ∀ q ∈ S', (∀ j : Fin n, m ≤ j.1 → p j = q j) →
      p - q ∈ r_prev • K_pi := by
    intro p hp q hq hagree
    have hy_eq : (e p).1 = (e q).1 := by
      ext ⟨j, hj⟩
      exact hagree j hj
    set y : Y := (e p).1
    have hp_in : (y, (e p).2) ∈ T' := hp
    have hq_in : (y, (e q).2) ∈ T' := by
      rw [hy_eq]
      exact hq
    let p₀ : Fin n → ℝ := e.symm (y, c y + α⁻¹ • ((e p).2 - c y))
    let q₀ : Fin n → ℝ := e.symm (y, c y + α⁻¹ • ((e q).2 - c y))
    have hp₀_S : p₀ ∈ S := hp_in.2
    have hq₀_S : q₀ ∈ S := hq_in.2
    have hpq₀_agree : ∀ j : Fin n, m ≤ j.1 → p₀ j = q₀ j := by
      intro j hj
      simp [p₀, q₀, e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
    have hdiff₀ : p₀ - q₀ ∈ r_curr • K_pi := hS_diff p₀ hp₀_S q₀ hq₀_S hpq₀_agree
    have hpq_scale : p - q = α • (p₀ - q₀) := by
      ext j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hj : m ≤ j.1
      · rw [hagree j hj, sub_self, hpq₀_agree j hj, sub_self, mul_zero]
      · have hp₀j : p₀ j = c y ⟨j, hj⟩ + α⁻¹ * (p j - c y ⟨j, hj⟩) := by
          change (if h : m ≤ j.1 then y ⟨j, h⟩ else (c y + α⁻¹ • ((e p).2 - c y)) ⟨j, h⟩) =
            c y ⟨j, hj⟩ + α⁻¹ * (p j - c y ⟨j, hj⟩)
          rw [dif_neg hj]
          rfl
        have hq₀j : q₀ j = c y ⟨j, hj⟩ + α⁻¹ * (q j - c y ⟨j, hj⟩) := by
          change (if h : m ≤ j.1 then y ⟨j, h⟩ else (c y + α⁻¹ • ((e q).2 - c y)) ⟨j, h⟩) =
            c y ⟨j, hj⟩ + α⁻¹ * (q j - c y ⟨j, hj⟩)
          rw [dif_neg hj]
          rfl
        rw [hp₀j, hq₀j]
        field_simp [hα_pos.ne']
        ring
    rw [hpq_scale]
    obtain ⟨z, hzK, hz_eq⟩ := Set.mem_smul_set.mp hdiff₀
    refine ⟨z, hzK, ?_⟩
    rw [← hz_eq]
    change r_prev • z = α • (r_curr • z)
    rw [smul_smul, div_mul_cancel₀ _ hr_curr_pos.ne']
  -- Fiber convexity & closedness at level `m - 1`.
  let Y_prev := {i : Fin n // m - 1 ≤ i.1} → ℝ
  let X_prev := {i : Fin n // ¬ m - 1 ≤ i.1} → ℝ
  let e_prev : (Fin n → ℝ) ≃ᵐ Y_prev × X_prev :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i : Fin n => m - 1 ≤ i.1)
  have hfiber_pre : ∀ y_prev : Y_prev,
      let y_curr : Y := fun i => y_prev ⟨i.1, le_trans (Nat.sub_le m 1) i.2⟩
      let ι_aff : X_prev → X := fun x_prev i =>
        if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else x_prev ⟨i.1, h⟩
      { x_prev : X_prev | e_prev.symm (y_prev, x_prev) ∈ S' } = ι_aff ⁻¹' (F' y_curr) := by
    intro y_prev y_curr ι_aff
    ext x_prev
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S', F']
    have heq : e (e_prev.symm (y_prev, x_prev)) = (y_curr, ι_aff x_prev) := by
      ext i
      · have h1 : m - 1 ≤ i.1.1 := le_trans (Nat.sub_le m 1) i.2
        change (if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else x_prev ⟨i.1, h⟩) =
          y_prev ⟨i.1, h1⟩
        exact dif_pos h1
      · change (if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else x_prev ⟨i.1, h⟩) =
          if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else x_prev ⟨i.1, h⟩
        rfl
    rw [heq]
  refine ⟨S', hS'_sub, hS'_meas, hS'_bdd, hS'_vol, ?_, ?_, ?_, ?_⟩
  · intro y_prev
    rw [hfiber_pre y_prev]
    intro x₁ hx₁ x₂ hx₂ a b ha hb hab
    set y_curr : Y := fun i => y_prev ⟨i.1, le_trans (Nat.sub_le m 1) i.2⟩
    set ι_aff : X_prev → X := fun x_prev i =>
      if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else x_prev ⟨i.1, h⟩
    have haff : ι_aff (a • x₁ + b • x₂) = a • ι_aff x₁ + b • ι_aff x₂ := by
      ext i
      change (if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else a * x₁ ⟨i.1, h⟩ + b * x₂ ⟨i.1, h⟩) =
        a * (if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else x₁ ⟨i.1, h⟩) +
          b * (if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else x₂ ⟨i.1, h⟩)
      split_ifs with h
      · linear_combination -y_prev ⟨i.1, h⟩ * hab
      · rfl
    change ι_aff (a • x₁ + b • x₂) ∈ F' y_curr
    rw [haff]
    exact hF'_conv y_curr hx₁ hx₂ ha hb hab
  · intro y_prev
    rw [hfiber_pre y_prev]
    set y_curr : Y := fun i => y_prev ⟨i.1, le_trans (Nat.sub_le m 1) i.2⟩
    set ι_aff : X_prev → X := fun x_prev i =>
      if h : m - 1 ≤ i.1.1 then y_prev ⟨i.1, h⟩ else x_prev ⟨i.1, h⟩
    have hcont : Continuous ι_aff := by
      rw [continuous_pi_iff]
      intro i
      dsimp only [ι_aff]
      split_ifs with h
      · exact continuous_const
      · exact continuous_apply (⟨i.1, h⟩ : {j : Fin n // ¬ m - 1 ≤ j.1})
    exact (hF'_closed y_curr).preimage hcont
  · intro p hp q hq hagree
    exact hdiff_m p hp q hq (fun j hj => hagree j (le_trans (Nat.sub_le m 1) hj))
  · intro p hp q hq hlat
    have hagree_m : ∀ j : Fin n, m ≤ j.1 → p j = q j :=
      hS_lat p (hS'_sub hp) q (hS'_sub hq) hlat
    have hdiff_prev : p - q ∈ r_prev • K_pi := hdiff_m p hp q hq hagree_m
    intro j hj
    have h0j : (p - q) j = 0 := hflag (p - q) hlat hdiff_prev j hj
    exact sub_eq_zero.mp h0j

/-- **UNCONDITIONAL MINKOWSKI'S SECOND THEOREM ON SUCCESSIVE MINIMA (`minkowski_second_theorem_upper`)**:
For EVERY dimension `n ≥ 1`, every full-rank lattice `Λ ⊂ ℝ^n`, and every compact symmetric convex
body `K ⊆ ℝ^n` with `0 ∈ interior K`:
`(∏ i : Fin n, successiveMinimum K Λ i) * (volume K).toReal ≤ 2 ^ n * ZLattice.covolume Λ volume`. -/
theorem minkowski_second_theorem_upper {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hcpt : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (∏ i : Fin n, successiveMinimum K Λ i) * (volume K).toReal ≤
      (2 : ℝ) ^ n * ZLattice.covolume Λ volume := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨v, hv_mem, hv_li, hv_K⟩ := exists_attaining_basis hconv hcpt h0 Λ
  let lam : Fin n → ℝ := fun i => successiveMinimum K Λ i
  have hlam_pos : ∀ i, 0 < lam i := fun i => successiveMinimum_pos hcpt.isBounded h0 Λ i
  have hlam_mono : ∀ {i j : Fin n}, i ≤ j → lam i ≤ lam j := fun hij =>
    successiveMinimum_mono h0 Λ hij
  -- Coordinate isomorphism `Φ : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ)` sending `v i ↦ e_i`.
  let bv : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    basisOfLinearIndependentOfCardEqFinrank hv_li (by simp)
  let Φ : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := bv.equivFun
  have hΦ_cont : Continuous Φ := Φ.toLinearMap.continuous_of_finiteDimensional
  let Ψ : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.trans Φ
  have hdetΨ_ne : LinearMap.det Ψ.toLinearMap ≠ 0 := by
    have h : ((LinearEquiv.det Ψ : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero (LinearEquiv.det Ψ)
    rwa [LinearEquiv.coe_det] at h
  have hdetΨ_pos : 0 < |LinearMap.det Ψ.toLinearMap| := abs_pos.mpr hdetΨ_ne
  let K_pi : Set (Fin n → ℝ) := Φ '' K
  have hK_pi_conv : Convex ℝ K_pi := hconv.linear_image Φ.toLinearMap
  have hK_pi_symm : ∀ x ∈ K_pi, -x ∈ K_pi := by
    rintro _ ⟨y, hyK, rfl⟩
    exact ⟨-y, hsymm y hyK, map_neg Φ y⟩
  have hK_pi_cpt : IsCompact K_pi := hcpt.image hΦ_cont
  have hvol_K_pi : volume K_pi = ENNReal.ofReal |LinearMap.det Ψ.toLinearMap| * volume K := by
    have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
        volume volume := PiLp.volume_preserving_toLp (Fin n)
    have hpre : K_pi =
        Ψ.toLinearMap '' ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' K) := by
      ext y
      simp only [K_pi, Set.mem_image, Set.mem_preimage, LinearEquiv.coe_toLinearMap, Ψ,
        LinearEquiv.trans_apply]
      constructor
      · rintro ⟨x, hxK, rfl⟩
        exact ⟨WithLp.ofLp x, by simpa using hxK, rfl⟩
      · rintro ⟨x, hxK, rfl⟩
        exact ⟨WithLp.toLp 2 x, hxK, rfl⟩
    rw [hpre, Measure.addHaar_image_linearMap volume Ψ.toLinearMap _,
      hmp.measure_preimage hcpt.measurableSet.nullMeasurableSet]
  -- Transport `Λ` and its fundamental domain to `Fin n → ℝ`.
  let bΛ := basisOfZLattice Λ
  let bΛ_pi : Basis (Fin n) ℝ (Fin n → ℝ) := (bΛ.ofZLatticeBasis ℝ).map Φ
  let Λ_pi : Submodule ℤ (Fin n → ℝ) := Submodule.span ℤ (Set.range bΛ_pi)
  have hmem_Λ_pi : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Λ ↔ Φ x ∈ Λ_pi := by
    intro x
    have hspan : Submodule.span ℤ (Set.range (bΛ.ofZLatticeBasis ℝ)) = Λ :=
      Basis.ofZLatticeBasis_span ℝ Λ bΛ
    have hmap : Submodule.map (Φ.toLinearMap.restrictScalars ℤ) Λ = Λ_pi := by
      rw [← hspan, Submodule.map_span]
      congr 1
      ext y
      simp [bΛ_pi]
    rw [← hmap]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Φ.injective hyx
      rwa [← this]
  have hfund_pi : IsAddFundamentalDomain Λ_pi.toAddSubgroup
      (ZSpan.fundamentalDomain bΛ_pi) volume :=
    ZSpan.isAddFundamentalDomain bΛ_pi volume
  have hvol_fund_pi :
      volume (ZSpan.fundamentalDomain bΛ_pi) =
        ENNReal.ofReal |LinearMap.det Ψ.toLinearMap| *
          ENNReal.ofReal (ZLattice.covolume Λ volume) := by
    have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
        volume volume := PiLp.volume_preserving_toLp (Fin n)
    have hfd_eq : ZSpan.fundamentalDomain bΛ_pi =
        Ψ.toLinearMap '' ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹'
          ZSpan.fundamentalDomain (bΛ.ofZLatticeBasis ℝ)) := by
      have h1 : ZSpan.fundamentalDomain bΛ_pi =
          Φ '' ZSpan.fundamentalDomain (bΛ.ofZLatticeBasis ℝ) := by
        simpa [bΛ_pi] using (ZSpan.map_fundamentalDomain (bΛ.ofZLatticeBasis ℝ) Φ).symm
      rw [h1]
      ext y
      simp only [Set.mem_image, Set.mem_preimage, LinearEquiv.coe_toLinearMap, Ψ,
        LinearEquiv.trans_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨WithLp.ofLp x, by simpa using hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨WithLp.toLp 2 x, hx, rfl⟩
    have hfund_Λ : IsAddFundamentalDomain Λ.toAddSubgroup
        (ZSpan.fundamentalDomain (bΛ.ofZLatticeBasis ℝ)) volume :=
      ZLattice.isAddFundamentalDomain bΛ volume
    have hne_top : volume (ZSpan.fundamentalDomain (bΛ.ofZLatticeBasis ℝ)) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded (bΛ.ofZLatticeBasis ℝ)).measure_lt_top.ne
    have hcov_eq : ENNReal.ofReal (ZLattice.covolume Λ volume) =
        volume (ZSpan.fundamentalDomain (bΛ.ofZLatticeBasis ℝ)) := by
      rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hfund_Λ,
        Measure.real, ENNReal.ofReal_toReal hne_top]
    rw [hfd_eq, Measure.addHaar_image_linearMap volume Ψ.toLinearMap _,
      hmp.measure_preimage (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet, hcov_eq]
  have hΛ_pi_countable : Countable Λ_pi.toAddSubgroup := by
    refine Function.Injective.countable
      (f := fun x : Λ_pi.toAddSubgroup => fun i : Fin n => ⌊bΛ_pi.repr x.1 i⌋) ?_
    intro x y hxy
    apply Subtype.ext
    have hfx : (ZSpan.floor bΛ_pi x.1 : Fin n → ℝ) = x.1 :=
      ZSpan.floor_eq_self_of_mem bΛ_pi x.1 x.2
    have hfy : (ZSpan.floor bΛ_pi y.1 : Fin n → ℝ) = y.1 :=
      ZSpan.floor_eq_self_of_mem bΛ_pi y.1 y.2
    rw [← hfx, ← hfy]
    apply bΛ_pi.repr.injective
    ext i
    rw [ZSpan.repr_floor_apply, ZSpan.repr_floor_apply]
    exact congrArg (Int.cast (R := ℝ)) (congrFun hxy i)
  -- Coordinate form of Flag Containment in `Fin n → ℝ`.
  have hflag_pi : ∀ (k : Fin n) (t : ℝ), 0 < t → t < lam k →
      ∀ x ∈ Λ_pi, x ∈ t • K_pi → ∀ j : Fin n, k.1 ≤ j.1 → x j = 0 := by
    intro k t ht_pos ht_lt x hxΛ hxK j hkj
    have hsymm_Λ : Φ.symm x ∈ Λ := (hmem_Λ_pi (Φ.symm x)).mpr (by simpa using hxΛ)
    have hsymm_K : Φ.symm x ∈ t • K := by
      obtain ⟨y, ⟨z, hzK, rfl⟩, hyx⟩ := Set.mem_smul_set.mp hxK
      refine ⟨z, hzK, ?_⟩
      have : Φ (t • z) = x := by rw [map_smul]; exact hyx
      exact (Φ.symm_apply_eq.mpr this.symm).symm
    have hspan := flag_containment hconv h0 Λ hv_mem hv_li hv_K ht_pos ht_lt hsymm_Λ hsymm_K
    have hsub : Submodule.span ℝ (v '' {l : Fin n | l < k}) ≤
        LinearMap.ker ((LinearMap.proj j).comp Φ.toLinearMap) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, hlk, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearEquiv.coe_toLinearMap, Φ]
      have hbv_l : v l = bv l := by simp [bv]
      rw [hbv_l, Basis.equivFun_self]
      have hne : l ≠ j := fun h => by
        have hlt : l.1 < k.1 := hlk
        have : j.1 < k.1 := h ▸ hlt
        omega
      exact if_neg hne
    have hker := hsub hspan
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at hker
    exact hker
  -- Prove the bound for every contraction factor `θ ∈ (0, 1)`, then pass to `θ → 1⁻`.
  have hbound_theta : ∀ θ : ℝ, 0 < θ → θ < 1 →
      θ ^ n * ((∏ i : Fin n, lam i) * (volume K).toReal) ≤
        (2 : ℝ) ^ n * ZLattice.covolume Λ volume := by
    intro θ hθ_pos hθ_lt
    let r : Fin n → ℝ := fun i => θ * lam i
    have hr_pos : ∀ i, 0 < r i := fun i => mul_pos hθ_pos (hlam_pos i)
    have hr_lt : ∀ i, r i < lam i := fun i => by
      dsimp only [r]
      nlinarith [hlam_pos i]
    have hr_mono : ∀ {i j : Fin n}, i ≤ j → r i ≤ r j := fun hij =>
      mul_le_mul_of_nonneg_left (hlam_mono hij) hθ_pos.le
    -- Telescoping partial product `prodTail m = r(m)^(m+1) * ∏_{j > m} r(j)`.
    let prodTail : (m : ℕ) → m < n → ℝ := fun m hm =>
      (r ⟨m, hm⟩) ^ (m + 1) * ∏ j ∈ Finset.univ.filter (fun j : Fin n => m < j.1), r j
    -- Downward induction over `d = 0, ..., n - 1`, setting `m = (n - 1) - d`.
    have hind : ∀ d : ℕ, (hd : d ≤ n - 1) →
        let m : ℕ := (n - 1) - d
        have hm : m < n := by omega
        ∃ S : Set (Fin n → ℝ),
          MeasurableSet S ∧
          Bornology.IsBounded S ∧
          volume S = ENNReal.ofReal (prodTail m hm / (2 : ℝ) ^ n) * volume K_pi ∧
          (∀ y : {i : Fin n // m ≤ i.1} → ℝ,
            Convex ℝ { x : {i : Fin n // ¬ m ≤ i.1} → ℝ |
              (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
                (fun i : Fin n => m ≤ i.1)).symm (y, x) ∈ S }) ∧
          (∀ y : {i : Fin n // m ≤ i.1} → ℝ,
            IsClosed { x : {i : Fin n // ¬ m ≤ i.1} → ℝ |
              (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
                (fun i : Fin n => m ≤ i.1)).symm (y, x) ∈ S }) ∧
          (∀ p ∈ S, ∀ q ∈ S, (∀ j : Fin n, m ≤ j.1 → p j = q j) → p - q ∈ r ⟨m, hm⟩ • K_pi) ∧
          (∀ p ∈ S, ∀ q ∈ S, p - q ∈ Λ_pi → ∀ j : Fin n, m ≤ j.1 → p j = q j) := by
      intro d
      induction d with
      | zero =>
        intro _
        dsimp only [Nat.sub_zero]
        have hm : n - 1 < n := Nat.sub_lt hn (by decide)
        let S_top : Set (Fin n → ℝ) := (r ⟨n - 1, hm⟩ / 2) • K_pi
        have hscale_pos : 0 < r ⟨n - 1, hm⟩ / 2 := half_pos (hr_pos ⟨n - 1, hm⟩)
        have hS_top_cpt : IsCompact S_top :=
          hK_pi_cpt.image (continuous_const_smul (r ⟨n - 1, hm⟩ / 2))
        have hS_top_conv : Convex ℝ S_top := hK_pi_conv.smul _
        have hS_top_vol : volume S_top =
            ENNReal.ofReal (prodTail (n - 1) hm / (2 : ℝ) ^ n) * volume K_pi := by
          rw [Measure.addHaar_smul_of_nonneg volume hscale_pos.le K_pi, Module.finrank_pi,
            Fintype.card_fin]
          congr 1
          have hfilt : Finset.univ.filter (fun j : Fin n => n - 1 < j.1) = ∅ := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, not_lt]
            omega
          simp only [prodTail, hfilt, Finset.prod_empty, mul_one,
            show n - 1 + 1 = n by omega, div_pow]
        have hS_top_diff : ∀ p ∈ S_top, ∀ q ∈ S_top, p - q ∈ r ⟨n - 1, hm⟩ • K_pi := by
          rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          have hmid : (2⁻¹ : ℝ) • a + (2⁻¹ : ℝ) • (-b) ∈ K_pi :=
            hK_pi_conv ha (hK_pi_symm b hb) (by positivity) (by positivity) (by norm_num)
          refine ⟨(2⁻¹ : ℝ) • a + (2⁻¹ : ℝ) • (-b), hmid, ?_⟩
          change r ⟨n - 1, hm⟩ • ((2⁻¹ : ℝ) • a + (2⁻¹ : ℝ) • (-b)) =
            (r ⟨n - 1, hm⟩ / 2) • a - (r ⟨n - 1, hm⟩ / 2) • b
          rw [smul_add, smul_smul, smul_smul, smul_neg, ← sub_eq_add_neg,
            show r ⟨n - 1, hm⟩ * 2⁻¹ = r ⟨n - 1, hm⟩ / 2 by ring]
        refine ⟨S_top, hS_top_cpt.measurableSet, hS_top_cpt.isBounded, hS_top_vol, ?_, ?_,
          fun p hp q hq _ => hS_top_diff p hp q hq, ?_⟩
        · intro y x₁ hx₁ x₂ hx₂ a b ha hb hab
          have hlin : (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
                (fun i : Fin n => n - 1 ≤ i.1)).symm (y, a • x₁ + b • x₂) =
              a • (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
                (fun i : Fin n => n - 1 ≤ i.1)).symm (y, x₁) +
              b • (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
                (fun i : Fin n => n - 1 ≤ i.1)).symm (y, x₂) := by
            ext i
            change (if h : n - 1 ≤ i.1 then y ⟨i, h⟩ else a * x₁ ⟨i, h⟩ + b * x₂ ⟨i, h⟩) =
              a * (if h : n - 1 ≤ i.1 then y ⟨i, h⟩ else x₁ ⟨i, h⟩) +
                b * (if h : n - 1 ≤ i.1 then y ⟨i, h⟩ else x₂ ⟨i, h⟩)
            split_ifs with h
            · linear_combination -y ⟨i, h⟩ * hab
            · rfl
          change (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
            (fun i : Fin n => n - 1 ≤ i.1)).symm (y, a • x₁ + b • x₂) ∈ S_top
          rw [hlin]
          exact hS_top_conv hx₁ hx₂ ha hb hab
        · intro y
          have hcont : Continuous (fun x : {i : Fin n // ¬ n - 1 ≤ i.1} → ℝ =>
              (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
                (fun i : Fin n => n - 1 ≤ i.1)).symm (y, x)) := by
            rw [continuous_pi_iff]
            intro i
            change Continuous (fun x : {j : Fin n // ¬ n - 1 ≤ j.1} → ℝ =>
              if h : n - 1 ≤ i.1 then y ⟨i, h⟩ else x ⟨i, h⟩)
            split_ifs with h
            · exact continuous_const
            · exact continuous_apply (⟨i, h⟩ : {j : Fin n // ¬ n - 1 ≤ j.1})
          exact hS_top_cpt.isClosed.preimage hcont
        · intro p hp q hq hlat j hj
          have hdiff := hS_top_diff p hp q hq
          have h0j := hflag_pi ⟨n - 1, hm⟩ (r ⟨n - 1, hm⟩) (hr_pos _) (hr_lt _) (p - q) hlat
            hdiff j hj
          exact sub_eq_zero.mp h0j
      | succ d ih =>
        intro hd
        have hd_prev : d ≤ n - 1 := Nat.le_of_succ_le hd
        obtain ⟨S, hS_meas, hS_bdd, hS_vol, hS_fconv, hS_fclosed, hS_diff, hS_lat⟩ := ih hd_prev
        set m : ℕ := (n - 1) - d
        have hm1 : 1 ≤ m := by omega
        have hmn : m ≤ n := by omega
        have hm_lt : m < n := by omega
        have hm_prev_lt : m - 1 < n := by omega
        have hstep_idx : (n - 1) - (d + 1) = m - 1 := by omega
        have hflag_m : ∀ x ∈ Λ_pi, x ∈ r ⟨m - 1, hm_prev_lt⟩ • K_pi →
            ∀ j : Fin n, m - 1 ≤ j.1 → x j = 0 := fun x hxΛ hxK j hj =>
          hflag_pi ⟨m - 1, hm_prev_lt⟩ (r ⟨m - 1, hm_prev_lt⟩) (hr_pos _) (hr_lt _) x hxΛ hxK j hj
        obtain ⟨S', _, hS'_meas, hS'_bdd, hS'_vol, hS'_fconv, hS'_fclosed, hS'_diff, hS'_lat⟩ :=
          compress_step hmn (hr_pos ⟨m - 1, hm_prev_lt⟩)
            (hr_mono (show (⟨m - 1, hm_prev_lt⟩ : Fin n) ≤ ⟨m, hm_lt⟩ from Nat.sub_le m 1))
            hflag_m hS_meas hS_bdd hS_fconv hS_fclosed hS_diff hS_lat
        have hprod_step :
            ((r ⟨m - 1, hm_prev_lt⟩ / r ⟨m, hm_lt⟩) ^ m) *
              (prodTail m hm_lt / (2 : ℝ) ^ n) =
              prodTail (m - 1) hm_prev_lt / (2 : ℝ) ^ n := by
          have hfilt_eq : Finset.univ.filter (fun j : Fin n => m - 1 < j.1) =
              insert ⟨m, hm_lt⟩ (Finset.univ.filter (fun j : Fin n => m < j.1)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · intro hlt
              by_cases hjm : j.1 = m
              · left; exact Fin.ext hjm
              · right; omega
            · rintro (rfl | hlt)
              · change m - 1 < m; omega
              · omega
          have hnot_mem : (⟨m, hm_lt⟩ : Fin n) ∉
              Finset.univ.filter (fun j : Fin n => m < j.1) := by
            simp
          have hprod_filt :
              ∏ j ∈ Finset.univ.filter (fun j : Fin n => m - 1 < j.1), r j =
                r ⟨m, hm_lt⟩ * ∏ j ∈ Finset.univ.filter (fun j : Fin n => m < j.1), r j := by
            rw [hfilt_eq, Finset.prod_insert hnot_mem]
          dsimp only [prodTail]
          rw [hprod_filt, show m - 1 + 1 = m by omega, div_pow, pow_succ]
          have hrm_ne : r ⟨m, hm_lt⟩ ≠ 0 := (hr_pos ⟨m, hm_lt⟩).ne'
          field_simp [hrm_ne]
        have hvol_final : volume S' =
            ENNReal.ofReal (prodTail (m - 1) hm_prev_lt / (2 : ℝ) ^ n) * volume K_pi := by
          rw [hS'_vol, hS_vol, ← mul_assoc,
            ← ENNReal.ofReal_mul (pow_nonneg (div_nonneg (hr_pos _).le (hr_pos _).le) m),
            hprod_step]
        have hS'_eq : ∀ (p : ℕ), p = m - 1 →
            (hp : p < n) →
            ∃ S₀ : Set (Fin n → ℝ),
              MeasurableSet S₀ ∧
              Bornology.IsBounded S₀ ∧
              volume S₀ = ENNReal.ofReal (prodTail p hp / (2 : ℝ) ^ n) * volume K_pi ∧
              (∀ y : {i : Fin n // p ≤ i.1} → ℝ,
                Convex ℝ { x : {i : Fin n // ¬ p ≤ i.1} → ℝ |
                  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
                    (fun i : Fin n => p ≤ i.1)).symm (y, x) ∈ S₀ }) ∧
              (∀ y : {i : Fin n // p ≤ i.1} → ℝ,
                IsClosed { x : {i : Fin n // ¬ p ≤ i.1} → ℝ |
                  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ)
                    (fun i : Fin n => p ≤ i.1)).symm (y, x) ∈ S₀ }) ∧
              (∀ a ∈ S₀, ∀ b ∈ S₀, (∀ j : Fin n, p ≤ j.1 → a j = b j) → a - b ∈ r ⟨p, hp⟩ • K_pi) ∧
              (∀ a ∈ S₀, ∀ b ∈ S₀, a - b ∈ Λ_pi → ∀ j : Fin n, p ≤ j.1 → a j = b j) := by
          rintro _ rfl _
          exact ⟨S', hS'_meas, hS'_bdd, hvol_final, hS'_fconv, hS'_fclosed, hS'_diff, hS'_lat⟩
        exact hS'_eq ((n - 1) - (d + 1)) hstep_idx (by omega)
    -- Specialize the induction at `d = n - 1` (`m = 0`).
    obtain ⟨S₀, hS₀_meas, _, hS₀_vol, _, _, _, hS₀_lat⟩ := hind (n - 1) le_rfl
    have hprod0 : prodTail 0 hn = ∏ i : Fin n, r i := by
      have hfilt0 : Finset.univ.filter (fun j : Fin n => 0 < j.1) =
          Finset.univ.erase ⟨0, hn⟩ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · intro hpos; exact ⟨fun h => by simp [h] at hpos, trivial⟩
        · rintro ⟨hne, _⟩
          have : j.1 ≠ 0 := fun h0 => hne (Fin.ext h0)
          omega
      dsimp only [prodTail]
      rw [hfilt0, pow_one, Finset.mul_prod_erase Finset.univ r (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
    have hS₀_vol' : volume S₀ =
        ENNReal.ofReal ((∏ i : Fin n, r i) / (2 : ℝ) ^ n) * volume K_pi := by
      have hm0 : (n - 1) - (n - 1) = 0 := Nat.sub_self (n - 1)
      simpa only [hm0, hprod0] using hS₀_vol
    -- By Blichfeldt's Theorem (`k = 1`), `volume S₀ ≤ volume (ZSpan.fundamentalDomain bΛ_pi)`.
    have hS₀_le_fd : volume S₀ ≤ volume (ZSpan.fundamentalDomain bΛ_pi) := by
      by_contra hgt
      push Not at hgt
      have hgt1 : ((1 : ℕ) : ℝ≥0∞) * volume (ZSpan.fundamentalDomain bΛ_pi) < volume S₀ := by
        simpa using hgt
      obtain ⟨x, hx_inj, hx_mem, hx_diff⟩ :=
        blichfeldt_theorem_general (L := Λ_pi.toAddSubgroup) hfund_pi hS₀_meas.nullMeasurableSet
          hgt1
      have hlat01 : x 0 - x 1 ∈ Λ_pi := hx_diff 0 1
      have heq01 : x 0 = x 1 := by
        ext j
        have hm0 : (n - 1) - (n - 1) = 0 := Nat.sub_self (n - 1)
        exact hS₀_lat (x 0) (hx_mem 0) (x 1) (hx_mem 1) hlat01 j (by omega)
      exact (by decide : (0 : Fin 2) ≠ 1) (hx_inj heq01)
    rw [hS₀_vol', hvol_K_pi, hvol_fund_pi] at hS₀_le_fd
    have hcancel : ENNReal.ofReal ((∏ i : Fin n, r i) / (2 : ℝ) ^ n) * volume K ≤
        ENNReal.ofReal (ZLattice.covolume Λ volume) := by
      have hdet_ne0 : ENNReal.ofReal |LinearMap.det Ψ.toLinearMap| ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hdetΨ_pos).ne'
      have hdet_ne_top : ENNReal.ofReal |LinearMap.det Ψ.toLinearMap| ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [← ENNReal.mul_le_mul_iff_right hdet_ne0 hdet_ne_top]
      calc
        ENNReal.ofReal |LinearMap.det Ψ.toLinearMap| *
            (ENNReal.ofReal ((∏ i : Fin n, r i) / (2 : ℝ) ^ n) * volume K)
            = ENNReal.ofReal ((∏ i : Fin n, r i) / (2 : ℝ) ^ n) *
                (ENNReal.ofReal |LinearMap.det Ψ.toLinearMap| * volume K) := by ring
        _ ≤ ENNReal.ofReal |LinearMap.det Ψ.toLinearMap| *
              ENNReal.ofReal (ZLattice.covolume Λ volume) := hS₀_le_fd
    have hreal_le : ((∏ i : Fin n, r i) / (2 : ℝ) ^ n) * (volume K).toReal ≤
        ZLattice.covolume Λ volume := by
      have hK_fin : volume K ≠ ⊤ := hcpt.measure_lt_top.ne
      have hcov_pos : 0 ≤ ZLattice.covolume Λ volume := le_of_lt (ZLattice.covolume_pos Λ volume)
      have hprod_nonneg : 0 ≤ (∏ i : Fin n, r i) / (2 : ℝ) ^ n :=
        div_nonneg (Finset.prod_nonneg fun i _ => (hr_pos i).le) (by positivity)
      have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcancel
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hprod_nonneg,
        ENNReal.toReal_ofReal hcov_pos] at htoReal
      exact htoReal
    have hprod_r : ∏ i : Fin n, r i = θ ^ n * ∏ i : Fin n, lam i := by
      simp only [r, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hprod_r] at hreal_le
    have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ h2n_pos] at hreal_le
    linarith
  -- Pass to the limit `θ_k = 1 - 1 / (k + 2) → 1⁻`.
  have hsub_tend : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) Filter.atTop (nhds 0) := by
    have hshift : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1))
        Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (Filter.tendsto_add_atTop_nat 1)
    convert hshift using 1
    ext k
    push_cast
    ring
  have htend : Filter.Tendsto
      (fun k : ℕ => (1 - 1 / ((k : ℝ) + 2)) ^ n * ((∏ i : Fin n, lam i) * (volume K).toReal))
      Filter.atTop
      (nhds ((1 - 0 : ℝ) ^ n * ((∏ i : Fin n, lam i) * (volume K).toReal))) :=
    ((tendsto_const_nhds.sub hsub_tend).pow n).mul_const ((∏ i : Fin n, lam i) * (volume K).toReal)
  rw [sub_zero, one_pow, one_mul] at htend
  refine le_of_tendsto htend (Filter.Eventually.of_forall fun k => ?_)
  have hk_pos : (0 : ℝ) < 1 - 1 / ((k : ℝ) + 2) := by
    have : 1 / ((k : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hk_lt : 1 - 1 / ((k : ℝ) + 2) < 1 := by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
    linarith
  exact hbound_theta (1 - 1 / ((k : ℝ) + 2)) hk_pos hk_lt

/-- The first successive minimum of the closed unit Euclidean ball `B_n` equals `shortestNorm Λ`. -/
theorem successiveMinimum_closedBall_zero_eq_shortestNorm {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ ⟨0, hn⟩ =
      shortestNorm Λ := by
  obtain ⟨u, hu_mem, hu_ne, hu_min⟩ := exists_shortest_nonzero_vector hn Λ
  rw [shortestNorm_eq_of_min Λ hu_mem hu_ne hu_min]
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  unfold successiveMinimum
  have hmem_u : ‖u‖ ∈ { t : ℝ | 0 < t ∧ ∃ v : Fin (0 + 1) → EuclideanSpace ℝ (Fin n),
      (∀ j, v j ∈ Λ) ∧ LinearIndependent ℝ v ∧
      ∀ j, v j ∈ t • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 } := by
    refine ⟨hu_pos, fun _ => u, fun _ => hu_mem, ?_,
      fun _ => (mem_smul_unitClosedBall_iff hu_pos).mpr le_rfl⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : g 0 • u = 0 := by simpa using hg
    fin_cases i
    exact (smul_eq_zero.mp h0).resolve_right hu_ne
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, by rintro t ⟨ht, _⟩; exact ht.le⟩ hmem_u
  · refine le_csInf ⟨‖u‖, hmem_u⟩ ?_
    rintro t ⟨ht, v, hv_mem, hv_li, hv_ball⟩
    have hge : ‖u‖ ≤ ‖v 0‖ := hu_min (v 0) (hv_mem 0) (hv_li.ne_zero 0)
    have hle : ‖v 0‖ ≤ t := (mem_smul_unitClosedBall_iff ht).mp (hv_ball 0)
    exact le_trans hge hle

/-- Exact real volume of the closed unit Euclidean ball in `ℝ^n`:
`ω_n = √π ^ n / Γ(n / 2 + 1) > 0`. -/
theorem unitBallVolume_eq {n : ℕ} (hn : 0 < n) :
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal =
      √Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal]
  have hG : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-- **UNCONDITIONAL HERMITE–MINKOWSKI BOUND IN EVERY DIMENSION `n ≥ 1`
(`hermite_minkowski_bound_all_dims`)**:
For EVERY `n ≥ 1` and every full-rank lattice `Λ ⊂ ℝ^n`, writing
`ω_n = (volume (Metric.closedBall 0 1)).toReal = √π ^ n / Γ(n / 2 + 1)`:
`λ₁(B_n, Λ)² ≤ (4 / ω_n ^ (2 / n)) * covol(Λ) ^ (2 / n)`. -/
theorem hermite_minkowski_bound_all_dims {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (successiveMinimum (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) Λ ⟨0, hn⟩) ^ 2 ≤
      (4 / (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ^ (2 / (n : ℝ))) *
        (ZLattice.covolume Λ volume) ^ (2 / (n : ℝ)) := by
  set B_n : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1
  set ω_n : ℝ := (volume B_n).toReal
  set lam1 : ℝ := successiveMinimum B_n Λ ⟨0, hn⟩
  have h0B : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior B_n := by
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds 0 zero_lt_one
  have hlam1_pos : 0 < lam1 := successiveMinimum_pos Metric.isBounded_closedBall h0B Λ ⟨0, hn⟩
  have hω_pos : 0 < ω_n := by
    change 0 < (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
    rw [unitBallVolume_eq hn]
    have hG : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have hcov_pos : 0 < ZLattice.covolume Λ volume := ZLattice.covolume_pos Λ volume
  have hpow_le_prod : lam1 ^ n ≤ ∏ i : Fin n, successiveMinimum B_n Λ i := by
    calc
      lam1 ^ n = ∏ _i : Fin n, lam1 := by simp
      _ ≤ ∏ i : Fin n, successiveMinimum B_n Λ i := by
        refine Finset.prod_le_prod (fun _ _ => hlam1_pos.le) fun i _ => ?_
        exact successiveMinimum_mono h0B Λ (show (⟨0, hn⟩ : Fin n) ≤ i from Nat.zero_le i.1)
  have hmink := minkowski_second_theorem_upper hn (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    (isCompact_closedBall 0 1) h0B Λ
  have hpow_mul : lam1 ^ n * ω_n ≤ (2 : ℝ) ^ n * ZLattice.covolume Λ volume :=
    le_trans (mul_le_mul_of_nonneg_right hpow_le_prod hω_pos.le) hmink
  have hpow_div : lam1 ^ n ≤ (2 : ℝ) ^ n * ZLattice.covolume Λ volume / ω_n :=
    (le_div_iff₀ hω_pos).mpr hpow_mul
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hexp_nonneg : 0 ≤ (2 : ℝ) / (n : ℝ) := by positivity
  have hrpow := Real.rpow_le_rpow (pow_nonneg hlam1_pos.le n) hpow_div hexp_nonneg
  have hlhs : (lam1 ^ n) ^ ((2 : ℝ) / (n : ℝ)) = lam1 ^ 2 := by
    rw [← Real.rpow_natCast lam1 n, ← Real.rpow_mul hlam1_pos.le,
      mul_div_cancel₀ 2 hn_pos.ne', Real.rpow_two]
  have hrhs : ((2 : ℝ) ^ n * ZLattice.covolume Λ volume / ω_n) ^ ((2 : ℝ) / (n : ℝ)) =
      (4 / ω_n ^ ((2 : ℝ) / (n : ℝ))) * (ZLattice.covolume Λ volume) ^ ((2 : ℝ) / (n : ℝ)) := by
    rw [Real.div_rpow (by positivity) hω_pos.le,
      Real.mul_rpow (by positivity) hcov_pos.le,
      ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_div_cancel₀ 2 hn_pos.ne', Real.rpow_two]
    norm_num
    ring
  rw [hlhs, hrhs] at hrpow
  exact hrpow

end MinkowskiSecondTheorem

end RHDirect.Stage10GeometryOfNumbers
