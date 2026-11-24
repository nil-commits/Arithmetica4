import RHDirect.Stage2DworkExp
import RHDirect.Stage2HodgeWeights
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Fin

/-!
# RHDirect.Stage3DworkFrobenius

Deep **$p$-adic Dwork `U_p` Operator, Overconvergent Banach Algebra `L(b)`, Dwork Trace Formula,
Fredholm Determinant Newton Polygon Lower Bounds, and Crystalline Hodge–Newton Slope Bridge**,
built directly on `RHDirect.Stage2DworkExp`, `RHDirect.Stage2HodgeWeights`,
`RHDirect.PAdicChainValuation`, and Mathlib `v4.33.1` (0 `sorry`, 0 custom `axiom`s).

## Contents

1. **Overconvergent Power-Series Banach Algebra `L(b)` & Dwork's `U_p` Operator**:
   - Banach space `IsOverconvergent b f` and norm `overconvNorm b f := ⨆ n, ‖coeff n f‖ * b ^ n`
     (`overconvNorm_add_le_max`, `overconvNorm_mul_le`, `overconvNorm_smul`,
     `tendsto_overconv_zero_of_lt`).
   - Direct bridge from `PAdicChainValuation.WtGe` (`isOverconvergent_of_wtGe`,
     `overconvNorm_le_of_wtGe`) and from `Stage2DworkExp.dworkSplitting`
     (`dworkSplitting_isOverconvergent`, `overconvNorm_dworkSplitting_eq_one`).
   - Dwork's Frobenius left-inverse `dworkUp p` (`(U_p f)(X) = ∑ a_{pn} X^n`):
     left-inverse identity `dworkUp_comp_frobPS`, Frobenius projection formula
     `dworkUp_frobPS_mul`, iteration `dworkUp_pow_apply`.
   - **Exact Contraction / Compactness Estimate** (`overconvNorm_dworkUp_le`):
     `‖U_p f‖_{b^p} ≤ ‖f‖_b`, and **Complete Continuity / Nuclear Finite-Rank Approximation**
     (`overconvNorm_dworkUp_sub_truncPS_le`):
     `‖U_p f - truncPS N (U_p f)‖_b ≤ (b ^ (1 - p)) ^ N * ‖f‖_b` for `b > 1`, `p ≥ 2`.
   - **Dwork Operator `ψ_g = U_p ∘ M_g`** (`dworkOp`):
     exact iteration `dworkOp_pow_eq`, exact matrix entry formula `dworkMatrix_eq`,
     general overconvergent matrix decay `norm_dworkMatrix_le`
     (`‖(ψ_g)_{i,j}‖ ≤ ‖p‖ ^ (w + c * (p i - j))`), and concrete specialization to
     Dwork's splitting function `θ(X)` (`norm_dworkMatrix_dworkSplitting_le`).

2. **Exact Finite-Dimensional Dwork Trace Formula (`ZMod` Character Orthogonality)**:
   - Cyclic character orthogonality `zmod_root_sum`:
     `∑ t : ZMod m, ζ ^ (t.val * d) = if m ∣ d then (m : K) else 0`.
   - Exact invariance of degree-`< N` polynomials under `ψ_g` when `g.natDegree ≤ (p - 1) * N`
     (`dworkOp_poly_invariant`) and exact matrix power formula `dworkFinMatrix_pow_apply`.
   - **Exact Dwork Trace Formula (Teichmüller Multiplicative Form)**
     `dwork_trace_formula_teichmuller`:
     `(p^k - 1) * Tr(A_N^k) = ∑_{t : ZMod (p^k - 1)} ∏_{r < k} g((ζ^t)^{p^r})`.
   - **Affine Teichmüller Sum (`x^{p^k} = x`)** `dwork_trace_formula_affine` and
     **Pointwise `p^{-k}` Averaging Formula** `dwork_Up_pow_eval_one`.

3. **$p$-adic Fredholm Determinant & Newton Polygon Coefficient Lower Bounds**:
   - Exact Leibniz–subset expansion `coeff_fredholmDet` of `det(1 - T A)`.
   - Combinatorial lower bound `two_mul_sum_val_ge_card_mul_pred` (`m (m - 1) ≤ 2 ∑_{i ∈ S} i`).
   - **Pure Row-Decay Fredholm Bound** `norm_coeff_fredholmDet_of_row_decay`:
     `‖c_m‖ ≤ pi ^ (α * m (m - 1) / 2)`.
   - **Sharp Off-Diagonal Dwork Fredholm Bound** `norm_coeff_fredholmDet_of_dwork_decay`:
     exact permutation cancellation `∑_{i ∈ S} σ(i) = ∑_{i ∈ S} i` yielding
     `‖c_m‖ ≤ pi ^ (c * (p - 1) * m (m - 1) / 2)`.
   - Concrete **Dwork Splitting Fredholm Bound** `norm_coeff_fredholmDet_dworkSplitting` with
     effective slope `α = (p - 1)^2 / p^2`.

4. **Ultrametric Newton Polygon Theorem & Bridge to `Stage2HodgeWeights` & `PAdicChainValuation`**:
   - Exact ultrametric break-point norm equality `norm_coeff_prod_one_sub_at_break`.
   - **General Ultrametric Newton-Above-Convex Theorem** `convex_le_polygon_of_norm_coeff_le`.
   - **Unconditional Crystalline Frobenius Slope Lower Bounds** (`dworkHodgeSlopes_le_newtonPolygon`,
     `polygonLe_of_fredholmDet_dwork_decay`, `polygonLe_of_fredholmDet_hodge_bound`,
     `wtGe_dworkOp_newton_polygon_bound`, `dworkSplitting_newton_polygon_bound`) directly
     discharging `Stage2HodgeWeights.polygon` and `Stage2HodgeWeights.PolygonLe` from
     `PAdicChainValuation.WtGe` and `Stage2DworkExp.dworkSplitting`.
-/

open Real Finset Filter Topology
open scoped BigOperators
open RHDirect.PAdicChainValuation
open RHDirect.Stage2DworkExp
open RHDirect.Stage2HodgeWeights

namespace RHDirect.Stage3DworkFrobenius

noncomputable section

/-! ## Section 1: Overconvergent Banach Algebra `L(b)` & Dwork's `U_p` Operator -/

section OverconvergentSpace

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- A formal power series `f ∈ K[[X]]` lies in the overconvergent Banach space `L(b)` if
`n ↦ ‖coeff n f‖ * b ^ n` is bounded above. -/
def IsOverconvergent (b : ℝ) (f : PowerSeries K) : Prop :=
  BddAbove (Set.range fun n : ℕ => ‖PowerSeries.coeff n f‖ * b ^ n)

/-- The overconvergent Banach norm `‖f‖_b := sup_{n ≥ 0} ‖coeff n f‖ * b ^ n` on `L(b)`. -/
def overconvNorm (b : ℝ) (f : PowerSeries K) : ℝ :=
  ⨆ n : ℕ, ‖PowerSeries.coeff n f‖ * b ^ n

omit [IsUltrametricDist K] in
theorem overconvNorm_nonneg {b : ℝ} (hb : 0 ≤ b) (f : PowerSeries K) :
    0 ≤ overconvNorm b f :=
  Real.iSup_nonneg fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hb n)

omit [IsUltrametricDist K] in
theorem norm_coeff_mul_pow_le_overconvNorm {b : ℝ} {f : PowerSeries K}
    (hf : IsOverconvergent b f) (n : ℕ) :
    ‖PowerSeries.coeff n f‖ * b ^ n ≤ overconvNorm b f :=
  le_ciSup hf n

omit [IsUltrametricDist K] in
theorem overconvNorm_le_of_forall {b B : ℝ} {f : PowerSeries K}
    (hf : ∀ n : ℕ, ‖PowerSeries.coeff n f‖ * b ^ n ≤ B) :
    overconvNorm b f ≤ B :=
  ciSup_le hf

omit [IsUltrametricDist K] in
theorem isOverconvergent_of_forall {b B : ℝ} {f : PowerSeries K}
    (hf : ∀ n : ℕ, ‖PowerSeries.coeff n f‖ * b ^ n ≤ B) :
    IsOverconvergent b f :=
  ⟨B, by rintro _ ⟨n, rfl⟩; exact hf n⟩

omit [IsUltrametricDist K] in
theorem overconvNorm_le_iff {b B : ℝ} (f : PowerSeries K) :
    (IsOverconvergent b f ∧ overconvNorm b f ≤ B) ↔
      ∀ n : ℕ, ‖PowerSeries.coeff n f‖ * b ^ n ≤ B := by
  constructor
  · rintro ⟨hf, hle⟩ n
    exact (norm_coeff_mul_pow_le_overconvNorm hf n).trans hle
  · intro h
    exact ⟨isOverconvergent_of_forall h, overconvNorm_le_of_forall h⟩

omit [IsUltrametricDist K] in
@[simp] theorem overconvNorm_zero (b : ℝ) : overconvNorm b (0 : PowerSeries K) = 0 := by
  unfold overconvNorm
  simp

omit [IsUltrametricDist K] in
theorem isOverconvergent_zero (b : ℝ) : IsOverconvergent b (0 : PowerSeries K) :=
  isOverconvergent_of_forall (B := 0) fun n => by simp

omit [IsUltrametricDist K] in
theorem isOverconvergent_one (b : ℝ) : IsOverconvergent b (1 : PowerSeries K) := by
  refine isOverconvergent_of_forall (B := 1) fun n => ?_
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

omit [IsUltrametricDist K] in
theorem overconvNorm_one (b : ℝ) : overconvNorm b (1 : PowerSeries K) = 1 := by
  apply le_antisymm
  · refine overconvNorm_le_of_forall fun n => ?_
    rw [PowerSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · simp
  · have h0 := norm_coeff_mul_pow_le_overconvNorm (isOverconvergent_one (K := K) b) 0
    simpa using h0

omit [IsUltrametricDist K] in
theorem isOverconvergent_smul {b : ℝ} (c : K) {f : PowerSeries K} (hf : IsOverconvergent b f) :
    IsOverconvergent b (c • f) := by
  obtain ⟨B, hB⟩ := hf
  refine isOverconvergent_of_forall (B := ‖c‖ * max B 0) fun n => ?_
  have hn : ‖PowerSeries.coeff n f‖ * b ^ n ≤ max B 0 :=
    (hB ⟨n, rfl⟩).trans (le_max_left B 0)
  rw [PowerSeries.coeff_smul, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hn (norm_nonneg c)

omit [IsUltrametricDist K] in
theorem overconvNorm_smul {b : ℝ} (c : K) {f : PowerSeries K}
    (hf : IsOverconvergent b f) :
    overconvNorm b (c • f) = ‖c‖ * overconvNorm b f := by
  apply le_antisymm
  · refine overconvNorm_le_of_forall fun n => ?_
    rw [PowerSeries.coeff_smul, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_coeff_mul_pow_le_overconvNorm hf n) (norm_nonneg c)
  · by_cases hc : c = 0
    · subst hc; simp
    · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
      rw [← le_div_iff₀' hcpos]
      refine overconvNorm_le_of_forall fun n => ?_
      rw [le_div_iff₀' hcpos]
      have h := norm_coeff_mul_pow_le_overconvNorm (isOverconvergent_smul c hf) n
      rwa [PowerSeries.coeff_smul, smul_eq_mul, norm_mul, mul_assoc] at h

/-- **Ultrametric Subadditivity on `L(b)`**: `‖f + g‖_b ≤ max ‖f‖_b ‖g‖_b`. -/
theorem isOverconvergent_add {b : ℝ} (hb : 0 ≤ b) {f g : PowerSeries K}
    (hf : IsOverconvergent b f) (hg : IsOverconvergent b g) :
    IsOverconvergent b (f + g) := by
  refine isOverconvergent_of_forall (B := max (overconvNorm b f) (overconvNorm b g)) fun n => ?_
  rw [map_add]
  calc ‖PowerSeries.coeff n f + PowerSeries.coeff n g‖ * b ^ n
      ≤ max ‖PowerSeries.coeff n f‖ ‖PowerSeries.coeff n g‖ * b ^ n :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (pow_nonneg hb n)
    _ = max (‖PowerSeries.coeff n f‖ * b ^ n) (‖PowerSeries.coeff n g‖ * b ^ n) :=
        max_mul_of_nonneg _ _ (pow_nonneg hb n)
    _ ≤ max (overconvNorm b f) (overconvNorm b g) :=
        max_le_max (norm_coeff_mul_pow_le_overconvNorm hf n)
          (norm_coeff_mul_pow_le_overconvNorm hg n)

theorem overconvNorm_add_le_max {b : ℝ} (hb : 0 ≤ b) {f g : PowerSeries K}
    (hf : IsOverconvergent b f) (hg : IsOverconvergent b g) :
    overconvNorm b (f + g) ≤ max (overconvNorm b f) (overconvNorm b g) := by
  refine overconvNorm_le_of_forall fun n => ?_
  rw [map_add]
  calc ‖PowerSeries.coeff n f + PowerSeries.coeff n g‖ * b ^ n
      ≤ max ‖PowerSeries.coeff n f‖ ‖PowerSeries.coeff n g‖ * b ^ n :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (pow_nonneg hb n)
    _ = max (‖PowerSeries.coeff n f‖ * b ^ n) (‖PowerSeries.coeff n g‖ * b ^ n) :=
        max_mul_of_nonneg _ _ (pow_nonneg hb n)
    _ ≤ max (overconvNorm b f) (overconvNorm b g) :=
        max_le_max (norm_coeff_mul_pow_le_overconvNorm hf n)
          (norm_coeff_mul_pow_le_overconvNorm hg n)

/-- **Ultrametric Banach Algebra Submultiplicativity on `L(b)`**: `‖f * g‖_b ≤ ‖f‖_b * ‖g‖_b`. -/
theorem norm_coeff_mul_pow_le_of_overconv {b : ℝ} (hb : 0 ≤ b) {f g : PowerSeries K}
    (hf : IsOverconvergent b f) (hg : IsOverconvergent b g) (n : ℕ) :
    ‖PowerSeries.coeff n (f * g)‖ * b ^ n ≤ overconvNorm b f * overconvNorm b g := by
  have hB0 : 0 ≤ overconvNorm b f * overconvNorm b g :=
    mul_nonneg (overconvNorm_nonneg hb f) (overconvNorm_nonneg hb g)
  by_cases hb0 : b = 0
  · subst hb0
    rcases n with _ | n
    · rw [pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, norm_mul]
      have h1 := norm_coeff_mul_pow_le_overconvNorm hf 0
      have h2 := norm_coeff_mul_pow_le_overconvNorm hg 0
      simp only [pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff] at h1 h2
      exact mul_le_mul h1 h2 (norm_nonneg _) (overconvNorm_nonneg le_rfl f)
    · rw [zero_pow (Nat.succ_ne_zero n), mul_zero]
      exact hB0
  · rw [PowerSeries.coeff_mul]
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hpowpos : 0 < b ^ n := pow_pos hbpos n
    rw [← le_div_iff₀ hpowpos]
    refine ultrametric_norm_sum_le _ _ (div_nonneg hB0 hpowpos.le) fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [le_div_iff₀ hpowpos, norm_mul, ← hx, pow_add]
    calc ‖PowerSeries.coeff x.1 f‖ * ‖PowerSeries.coeff x.2 g‖ * (b ^ x.1 * b ^ x.2)
        = (‖PowerSeries.coeff x.1 f‖ * b ^ x.1) * (‖PowerSeries.coeff x.2 g‖ * b ^ x.2) := by ring
      _ ≤ overconvNorm b f * overconvNorm b g :=
          mul_le_mul (norm_coeff_mul_pow_le_overconvNorm hf x.1)
            (norm_coeff_mul_pow_le_overconvNorm hg x.2)
            (mul_nonneg (norm_nonneg _) (pow_nonneg hb _))
            (overconvNorm_nonneg hb f)

theorem isOverconvergent_mul {b : ℝ} (hb : 0 ≤ b) {f g : PowerSeries K}
    (hf : IsOverconvergent b f) (hg : IsOverconvergent b g) :
    IsOverconvergent b (f * g) :=
  isOverconvergent_of_forall (norm_coeff_mul_pow_le_of_overconv hb hf hg)

theorem overconvNorm_mul_le {b : ℝ} (hb : 0 ≤ b) {f g : PowerSeries K}
    (hf : IsOverconvergent b f) (hg : IsOverconvergent b g) :
    overconvNorm b (f * g) ≤ overconvNorm b f * overconvNorm b g :=
  overconvNorm_le_of_forall (norm_coeff_mul_pow_le_of_overconv hb hf hg)

omit [IsUltrametricDist K] in
theorem isOverconvergent_mono {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hle : b₁ ≤ b₂) {f : PowerSeries K}
    (hf : IsOverconvergent b₂ f) : IsOverconvergent b₁ f := by
  refine isOverconvergent_of_forall (B := overconvNorm b₂ f) fun n => ?_
  calc ‖PowerSeries.coeff n f‖ * b₁ ^ n
      ≤ ‖PowerSeries.coeff n f‖ * b₂ ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb₁ hle n) (norm_nonneg _)
    _ ≤ overconvNorm b₂ f := norm_coeff_mul_pow_le_overconvNorm hf n

omit [IsUltrametricDist K] in
theorem overconvNorm_mono {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hle : b₁ ≤ b₂) {f : PowerSeries K}
    (hf : IsOverconvergent b₂ f) : overconvNorm b₁ f ≤ overconvNorm b₂ f := by
  refine overconvNorm_le_of_forall fun n => ?_
  calc ‖PowerSeries.coeff n f‖ * b₁ ^ n
      ≤ ‖PowerSeries.coeff n f‖ * b₂ ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb₁ hle n) (norm_nonneg _)
    _ ≤ overconvNorm b₂ f := norm_coeff_mul_pow_le_overconvNorm hf n

omit [IsUltrametricDist K] in
/-- Strict overconvergence (`f ∈ L(b')` with `0 ≤ b < b'`) forces geometric decay
`‖coeff n f‖ * b ^ n → 0`. -/
theorem tendsto_overconv_zero_of_lt {b b' : ℝ} (hb : 0 ≤ b) (hlt : b < b')
    {f : PowerSeries K} (hf : IsOverconvergent b' f) :
    Tendsto (fun n : ℕ => ‖PowerSeries.coeff n f‖ * b ^ n) atTop (nhds 0) := by
  have hb'pos : 0 < b' := lt_of_le_of_lt hb hlt
  have hq0 : 0 ≤ b / b' := div_nonneg hb hb'pos.le
  have hq1 : b / b' < 1 := (div_lt_one hb'pos).mpr hlt
  have hlim : Tendsto (fun n : ℕ => overconvNorm b' f * (b / b') ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (overconvNorm b' f)
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hb n)) (fun n => ?_) hlim
  have hbn : ‖PowerSeries.coeff n f‖ * b' ^ n ≤ overconvNorm b' f :=
    norm_coeff_mul_pow_le_overconvNorm hf n
  have hpow : b ^ n = b' ^ n * (b / b') ^ n := by
    rw [div_pow, mul_div_cancel₀ _ (pow_pos hb'pos n).ne']
  rw [hpow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hbn (pow_nonneg hq0 n)

omit [IsUltrametricDist K] in
/-- **Direct Bridge from `PAdicChainValuation.WtGe` to `L(b)`**:
Any univariate series satisfying `WtGe ‖(p : K)‖ (-α) w` lies in `L(‖p‖^(-α))` with
overconvergent norm `≤ ‖(p : K)‖ ^ w`. -/
theorem wtGe_iff_overconvNorm_le [CharZero K] {p : ℕ} (hp : p.Prime) {α w : ℝ}
    (f : PowerSeries K) :
    WtGe ‖(p : K)‖ (fun _ : Unit => -α) w (f : MvPowerSeries Unit K) ↔
      (IsOverconvergent (‖(p : K)‖ ^ (-α)) f ∧
        overconvNorm (‖(p : K)‖ ^ (-α)) f ≤ ‖(p : K)‖ ^ w) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [overconvNorm_le_iff]
  constructor
  · intro hf n
    have hn := hf (Finsupp.single () n)
    unfold MonoWtGe at hn
    rw [wtDot_unit, Finsupp.single_eq_same] at hn
    change ‖PowerSeries.coeff n f‖ ≤ ‖(p : K)‖ ^ (w - (n : ℝ) * -α) at hn
    have hpow : (‖(p : K)‖ ^ (-α)) ^ n = ‖(p : K)‖ ^ (-(n : ℝ) * α) := by
      rw [← Real.rpow_natCast (‖(p : K)‖ ^ (-α)) n, ← Real.rpow_mul hpi0.le]
      congr 1; ring
    rw [hpow]
    calc ‖PowerSeries.coeff n f‖ * ‖(p : K)‖ ^ (-(n : ℝ) * α)
        ≤ ‖(p : K)‖ ^ (w - (n : ℝ) * -α) * ‖(p : K)‖ ^ (-(n : ℝ) * α) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hpi0.le _)
      _ = ‖(p : K)‖ ^ w := by
          rw [← Real.rpow_add hpi0]
          congr 1; ring
  · intro h m
    have hm_eq : m = Finsupp.single () (m ()) := by ext; simp
    unfold MonoWtGe
    rw [wtDot_unit]
    conv_lhs => rw [hm_eq]
    change ‖PowerSeries.coeff (m ()) f‖ ≤ ‖(p : K)‖ ^ (w - (m () : ℝ) * -α)
    have hn := h (m ())
    have hpow : (‖(p : K)‖ ^ (-α)) ^ (m ()) = ‖(p : K)‖ ^ (-(m () : ℝ) * α) := by
      rw [← Real.rpow_natCast (‖(p : K)‖ ^ (-α)) (m ()), ← Real.rpow_mul hpi0.le]
      congr 1; ring
    rw [hpow] at hn
    calc ‖PowerSeries.coeff (m ()) f‖
        = (‖PowerSeries.coeff (m ()) f‖ * ‖(p : K)‖ ^ (-(m () : ℝ) * α)) *
            ‖(p : K)‖ ^ ((m () : ℝ) * α) := by
          rw [mul_assoc, ← Real.rpow_add hpi0]
          have : -(m () : ℝ) * α + (m () : ℝ) * α = 0 := by ring
          rw [this, Real.rpow_zero, mul_one]
      _ ≤ ‖(p : K)‖ ^ w * ‖(p : K)‖ ^ ((m () : ℝ) * α) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hpi0.le _)
      _ = ‖(p : K)‖ ^ (w - (m () : ℝ) * -α) := by
          rw [← Real.rpow_add hpi0]
          congr 1; ring

/-- **Dwork Splitting Function Lies in `L(R_Dwork)` with Unit Norm**:
`θ(X) = exp(ϖ (X - X^p))` belongs to `L(‖p‖ ^ (-(p - 1) / p^2))` with exact norm `1`. -/
theorem dworkSplitting_isOverconvergent [CharZero K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) :
    IsOverconvergent (dworkOverconvRadius K p) (dworkSplitting ϖ p) ∧
      overconvNorm (dworkOverconvRadius K p) (dworkSplitting ϖ p) = 1 := by
  have hwt := (wtGe_iff_overconvNorm_le hp (dworkSplitting ϖ p)).mp
    (dworkSplitting_wtGe hp hlt hϖ)
  rw [Real.rpow_zero] at hwt
  unfold dworkOverconvRadius
  refine ⟨hwt.1, le_antisymm hwt.2 ?_⟩
  have h0 := norm_coeff_mul_pow_le_overconvNorm hwt.1 0
  have hc0 : PowerSeries.coeff 0 (dworkSplitting ϖ p) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    unfold dworkSplitting
    exact constantCoeff_expPS (by simp [hp.ne_zero])
  simpa [hc0] using h0

/-! ### Dwork's Frobenius Left-Inverse `U_p` & Exact Contraction -/

/-- **Dwork's `U_p` Operator** on formal power series:
`(U_p f)(X) := ∑_{n ≥ 0} a_{p n} X^n`. -/
def dworkUp {R : Type*} [CommSemiring R] (p : ℕ) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun f := PowerSeries.mk fun n => PowerSeries.coeff (p * n) f
  map_add' f g := by
    ext n
    simp
  map_smul' c f := by
    ext n
    simp

@[simp] theorem coeff_dworkUp {R : Type*} [CommSemiring R] (p : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (dworkUp p f) = PowerSeries.coeff (p * n) f := by
  simp [dworkUp]

/-- **Left-Inverse to Frobenius**: `U_p(f(X^p)) = f(X)`. -/
theorem dworkUp_comp_frobPS {R : Type*} [CommSemiring R] {p : ℕ} (hp : 0 < p) (f : PowerSeries R) :
    dworkUp p (frobPS p hp f) = f := by
  ext n
  rw [coeff_dworkUp, coeff_frobPS, if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp]

/-- **Dwork Projection / Frobenius-Linearity Formula**:
`U_p(f(X^p) * g(X)) = f(X) * U_p(g(X))`. -/
theorem dworkUp_frobPS_mul {R : Type*} [CommSemiring R] {p : ℕ} (hp : 0 < p)
    (f g : PowerSeries R) :
    dworkUp p (frobPS p hp f * g) = f * dworkUp p g := by
  ext n
  rw [coeff_dworkUp, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [← Finset.sum_filter_of_ne (p := fun x : ℕ × ℕ => p ∣ x.1)
    (fun x _ hx => by
      by_contra h
      apply hx
      rw [coeff_frobPS, if_neg h, zero_mul])]
  refine Finset.sum_bij (fun x _ => (x.1 / p, x.2 / p)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
    obtain ⟨hsum, a, ha⟩ := hx
    have ha_le : a ≤ n := by nlinarith
    have h2 : x.2 = p * (n - a) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [Finset.mem_antidiagonal, ha, h2, Nat.mul_div_cancel_left a hp,
      Nat.mul_div_cancel_left (n - a) hp]
    omega
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx₁ hx₂
    have h1d : p ∣ x₁.2 := by
      obtain ⟨a, ha⟩ := hx₁.2
      exact ⟨n - a, by rw [Nat.mul_sub_left_distrib]; omega⟩
    have h2d : p ∣ x₂.2 := by
      obtain ⟨a, ha⟩ := hx₂.2
      exact ⟨n - a, by rw [Nat.mul_sub_left_distrib]; omega⟩
    have hfst : x₁.1 / p = x₂.1 / p := congrArg Prod.fst heq
    have hsnd : x₁.2 / p = x₂.2 / p := congrArg Prod.snd heq
    ext
    · rw [← Nat.mul_div_cancel' hx₁.2, hfst, Nat.mul_div_cancel' hx₂.2]
    · rw [← Nat.mul_div_cancel' h1d, hsnd, Nat.mul_div_cancel' h2d]
  · intro y hy
    rw [Finset.mem_antidiagonal] at hy
    refine ⟨(p * y.1, p * y.2), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_antidiagonal]
      exact ⟨by rw [← Nat.mul_add, hy], dvd_mul_right p y.1⟩
    · ext <;> simp [Nat.mul_div_cancel_left _ hp]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
    have h2d : p ∣ x.2 := by
      obtain ⟨a, ha⟩ := hx.2
      exact ⟨n - a, by rw [Nat.mul_sub_left_distrib]; omega⟩
    rw [coeff_frobPS, if_pos hx.2, coeff_dworkUp, Nat.mul_div_cancel' h2d]

theorem dworkUp_comp {R : Type*} [CommSemiring R] (p q : ℕ) (f : PowerSeries R) :
    dworkUp p (dworkUp q f) = dworkUp (q * p) f := by
  ext n
  simp [mul_assoc]

theorem dworkUp_pow_apply {R : Type*} [CommSemiring R] (p k : ℕ) (f : PowerSeries R) :
    ((dworkUp (R := R) p) ^ k) f = dworkUp (p ^ k) f := by
  induction k with
  | zero =>
    ext n
    simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, dworkUp_comp, pow_succ]

omit [IsUltrametricDist K] in
/-- **Exact Contraction / Overconvergence Improvement of `U_p`**:
If `f ∈ L(b)` (`0 ≤ b`), then `U_p f ∈ L(b ^ p)` with `‖U_p f‖_{b^p} ≤ ‖f‖_b`! -/
theorem isOverconvergent_dworkUp {b : ℝ} (p : ℕ) {f : PowerSeries K}
    (hf : IsOverconvergent b f) :
    IsOverconvergent (b ^ p) (dworkUp p f) := by
  refine isOverconvergent_of_forall (B := overconvNorm b f) fun n => ?_
  rw [coeff_dworkUp, ← pow_mul]
  exact norm_coeff_mul_pow_le_overconvNorm hf (p * n)

omit [IsUltrametricDist K] in
theorem overconvNorm_dworkUp_le {b : ℝ} (p : ℕ) {f : PowerSeries K}
    (hf : IsOverconvergent b f) :
    overconvNorm (b ^ p) (dworkUp p f) ≤ overconvNorm b f := by
  refine overconvNorm_le_of_forall fun n => ?_
  rw [coeff_dworkUp, ← pow_mul]
  exact norm_coeff_mul_pow_le_overconvNorm hf (p * n)

omit [IsUltrametricDist K] in
/-- **Complete Continuity / Nuclear Finite-Rank Approximation of `U_p` on `L(b)` (`b > 1`)**:
For `1 < b`, `2 ≤ p`, and every truncation rank `N : ℕ`, the operator-norm error of the
rank-`N` truncation `truncPS N ∘ U_p` decays geometrically at rate `(b ^ (-(p - 1))) ^ N`:
`‖U_p f - truncPS N (U_p f)‖_b ≤ (b ^ (1 - p : ℤ)) ^ N * ‖f‖_b`. -/
theorem overconvNorm_dworkUp_sub_truncPS_le {b : ℝ} (hb : 1 < b) {p : ℕ} (hp : 2 ≤ p)
    (N : ℕ) {f : PowerSeries K} (hf : IsOverconvergent b f) :
    overconvNorm b (dworkUp p f - truncPS N (dworkUp p f)) ≤
      (b ^ (1 - (p : ℤ))) ^ N * overconvNorm b f := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hrpos : 0 < b ^ (1 - (p : ℤ)) := zpow_pos hb0 _
  have hrle : b ^ (1 - (p : ℤ)) ≤ 1 := by
    have hexp : (1 - (p : ℤ)) ≤ 0 := by omega
    calc b ^ (1 - (p : ℤ)) ≤ b ^ (0 : ℤ) := zpow_le_zpow_right₀ hb.le hexp
      _ = 1 := zpow_zero b
  refine overconvNorm_le_of_forall fun n => ?_
  rw [map_sub, coeff_truncPS]
  by_cases hn : n < N
  · rw [if_pos hn, sub_self, norm_zero, zero_mul]
    exact mul_nonneg (pow_nonneg hrpos.le N) (overconvNorm_nonneg hb0.le f)
  · push Not at hn
    rw [if_neg (not_lt.mpr hn), sub_zero, coeff_dworkUp]
    have hbd := norm_coeff_mul_pow_le_overconvNorm hf (p * n)
    have hsplit : b ^ n = (b ^ (1 - (p : ℤ))) ^ n * b ^ (p * n) := by
      rw [← zpow_natCast b n, ← zpow_natCast b (p * n), ← zpow_natCast (b ^ (1 - (p : ℤ))) n,
        ← zpow_mul, ← zpow_add₀ hb0.ne']
      congr 1
      push_cast
      ring
    rw [hsplit]
    calc ‖PowerSeries.coeff (p * n) f‖ * ((b ^ (1 - (p : ℤ))) ^ n * b ^ (p * n))
        = (b ^ (1 - (p : ℤ))) ^ n * (‖PowerSeries.coeff (p * n) f‖ * b ^ (p * n)) := by ring
      _ ≤ (b ^ (1 - (p : ℤ))) ^ N * overconvNorm b f :=
          mul_le_mul (pow_le_pow_of_le_one hrpos.le hrle hn) hbd
            (mul_nonneg (norm_nonneg _) (pow_nonneg hb0.le _))
            (pow_nonneg hrpos.le N)

/-! ### Dwork Operator `ψ_g = U_p ∘ M_g` & Matrix Entry Decay -/

/-- **Dwork's Frobenius Operator** `ψ_g(f) := U_p(g * f)` on `R[[X]]`. -/
def dworkOp {R : Type*} [CommSemiring R] (p : ℕ) (g : PowerSeries R) :
    PowerSeries R →ₗ[R] PowerSeries R where
  toFun f := dworkUp p (g * f)
  map_add' f₁ f₂ := by rw [mul_add, map_add]
  map_smul' c f := by
    change dworkUp p (g * (c • f)) = c • dworkUp p (g * f)
    rw [mul_smul_comm, map_smul]

@[simp] theorem dworkOp_apply {R : Type*} [CommSemiring R] (p : ℕ) (g f : PowerSeries R) :
    dworkOp p g f = dworkUp p (g * f) := rfl

/-- **Exact Overconvergent Contraction for `ψ_g = U_p ∘ M_g`**:
`‖ψ_g f‖_{b^p} ≤ ‖g‖_b * ‖f‖_b`. -/
theorem overconvNorm_dworkOp_le {b : ℝ} (hb : 0 ≤ b) (p : ℕ) {g f : PowerSeries K}
    (hg : IsOverconvergent b g) (hf : IsOverconvergent b f) :
    overconvNorm (b ^ p) (dworkOp p g f) ≤ overconvNorm b g * overconvNorm b f :=
  (overconvNorm_dworkUp_le p (isOverconvergent_mul hb hg hf)).trans
    (overconvNorm_mul_le hb hg hf)

/-- The `k`-fold Frobenius norm series `g^{(k)}(X) := ∏_{r=0}^{k-1} g(X^{p^r})`. -/
def dworkNormSeries {R : Type*} [CommSemiring R] (p : ℕ) (hp : 0 < p) (g : PowerSeries R)
    (k : ℕ) : PowerSeries R :=
  ∏ r ∈ Finset.range k, frobPS (p ^ r) (pow_pos hp r) g

theorem frobPS_comp {R : Type*} [CommSemiring R] {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (f : PowerSeries R) :
    frobPS p hp (frobPS q hq f) = frobPS (p * q) (Nat.mul_pos hp hq) f := by
  ext n
  rw [coeff_frobPS, coeff_frobPS]
  by_cases h1 : p ∣ n
  · rw [if_pos h1, coeff_frobPS]
    by_cases h2 : q ∣ n / p
    · have h3 : p * q ∣ n := by
        obtain ⟨k, hk⟩ := h2
        refine ⟨k, ?_⟩
        rw [← Nat.mul_div_cancel' h1, hk, mul_assoc]
      rw [if_pos h2, if_pos h3, Nat.div_div_eq_div_mul]
    · have h3 : ¬ p * q ∣ n := by
        intro ⟨k, hk⟩
        apply h2
        refine ⟨k, ?_⟩
        rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp]
      rw [if_neg h2, if_neg h3]
  · have h3 : ¬ p * q ∣ n := fun h => h1 (dvd_trans (dvd_mul_right p q) h)
    rw [if_neg h1, coeff_frobPS, if_neg h3]

theorem frobPS_one {R : Type*} [CommSemiring R] (f : PowerSeries R) :
    frobPS 1 Nat.one_pos f = f := by
  ext n
  rw [coeff_frobPS, if_pos (one_dvd n), Nat.div_one]

/-- **Exact Iteration Identity for the Dwork Operator**:
`(ψ_g)^k(f) = U_{p^k}(g^{(k)} * f)` where `g^{(k)}(X) = ∏_{r < k} g(X^{p^r})`. -/
theorem dworkOp_pow_eq {R : Type*} [CommSemiring R] {p : ℕ} (hp : 0 < p) (g : PowerSeries R)
    (k : ℕ) (f : PowerSeries R) :
    ((dworkOp p g) ^ k) f = dworkUp (p ^ k) (dworkNormSeries p hp g k * f) := by
  induction k generalizing f with
  | zero =>
    ext n
    simp [dworkNormSeries]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, dworkOp_apply]
    have hcomm : g * dworkUp (p ^ k) (dworkNormSeries p hp g k * f) =
        dworkUp (p ^ k) (frobPS (p ^ k) (pow_pos hp k) g * (dworkNormSeries p hp g k * f)) :=
      (dworkUp_frobPS_mul (pow_pos hp k) g (dworkNormSeries p hp g k * f)).symm
    rw [hcomm, dworkUp_comp, ← pow_succ]
    congr 1
    unfold dworkNormSeries
    rw [Finset.prod_range_succ]
    ring

/-- Infinite monomial-basis matrix entry `(ψ_g)_{i, j} := coeff_i (ψ_g(X^j))`. -/
def dworkMatrix {R : Type*} [CommSemiring R] (p : ℕ) (g : PowerSeries R) (i j : ℕ) : R :=
  PowerSeries.coeff i (dworkOp p g (PowerSeries.X ^ j))

/-- **Exact Monomial Matrix Entry Formula**:
`(ψ_g)_{i, j} = coeff_{p i - j}(g)` if `j ≤ p i`, else `0`. -/
theorem dworkMatrix_eq {R : Type*} [CommSemiring R] (p : ℕ) (g : PowerSeries R) (i j : ℕ) :
    dworkMatrix p g i j = if j ≤ p * i then PowerSeries.coeff (p * i - j) g else 0 := by
  unfold dworkMatrix
  rw [dworkOp_apply, coeff_dworkUp, PowerSeries.coeff_mul]
  by_cases hj : j ≤ p * i
  · rw [if_pos hj, Finset.sum_eq_single (p * i - j, j)]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
    · intro x hx hne
      rw [Finset.mem_antidiagonal] at hx
      have hx2 : x.2 ≠ j := by
        intro h2
        apply hne
        ext
        · omega
        · exact h2
      rw [PowerSeries.coeff_X_pow, if_neg hx2, mul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_antidiagonal]
      omega
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    have hx2 : x.2 ≠ j := by omega
    rw [PowerSeries.coeff_X_pow, if_neg hx2, mul_zero]

omit [IsUltrametricDist K] in
/-- **General Overconvergent Matrix Entry Decay**:
If `g` has Dwork weight `WtGe ‖(p : K)‖ (-c) w` (equivalently `‖coeff n g‖ ≤ ‖p‖ ^ (w + c * n)`),
then every matrix entry of `ψ_g` satisfies:
`‖(ψ_g)_{i, j}‖ ≤ ‖(p : K)‖ ^ (w + c * (p i - j))`. -/
theorem norm_dworkMatrix_le [CharZero K] {p : ℕ} (hp : p.Prime) {c w : ℝ} {g : PowerSeries K}
    (hg : WtGe ‖(p : K)‖ (fun _ : Unit => -c) w (g : MvPowerSeries Unit K)) (i j : ℕ) :
    ‖dworkMatrix p g i j‖ ≤ ‖(p : K)‖ ^ (w + c * ((p : ℝ) * (i : ℝ) - (j : ℝ))) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [dworkMatrix_eq]
  split_ifs with hj
  · have h := hg (Finsupp.single () (p * i - j))
    unfold MonoWtGe at h
    rw [wtDot_unit, Finsupp.single_eq_same] at h
    change ‖PowerSeries.coeff (p * i - j) g‖ ≤ _ at h
    refine h.trans_eq ?_
    congr 1
    rw [Nat.cast_sub hj, Nat.cast_mul]
    ring
  · rw [norm_zero]
    exact Real.rpow_nonneg hpi0.le _

omit [IsUltrametricDist K] in
/-- **Overconvergent `L(b)` Matrix Entry Decay**:
If `g ∈ L(b)` (`0 < b`), then every matrix entry of `ψ_g` satisfies
`‖(ψ_g)_{i, j}‖ ≤ ‖g‖_b * b ^ ((j : ℤ) - (p * i : ℤ))`. -/
theorem norm_dworkMatrix_le_overconvNorm {b : ℝ} (hb : 0 < b) (p : ℕ) {g : PowerSeries K}
    (hg : IsOverconvergent b g) (i j : ℕ) :
    ‖dworkMatrix p g i j‖ ≤ overconvNorm b g * b ^ ((j : ℤ) - (p * i : ℤ)) := by
  rw [dworkMatrix_eq]
  split_ifs with hj
  · have hbd := norm_coeff_mul_pow_le_overconvNorm hg (p * i - j)
    have hexp : b ^ ((j : ℤ) - (p * i : ℤ)) = (b ^ (p * i - j))⁻¹ := by
      rw [← zpow_natCast b (p * i - j), ← zpow_neg]
      congr 1
      have hsub : ((p * i - j : ℕ) : ℤ) = (p * i : ℤ) - (j : ℤ) := Int.ofNat_sub hj
      omega
    rw [hexp, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hb _)]
    exact hbd
  · rw [norm_zero]
    exact mul_nonneg (overconvNorm_nonneg hb.le g) (zpow_nonneg hb.le _)

/-- **Concrete Dwork Splitting Matrix Entry Decay** (built directly on
`Stage2DworkExp.dworkSplitting_wtGe`):
For `ϖ ^ (p - 1) = -p`,
`‖(ψ_θ)_{i, j}‖ ≤ ‖(p : K)‖ ^ (((p - 1) / p^2) * (p i - j))`. -/
theorem norm_dworkMatrix_dworkSplitting_le [CharZero K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) (i j : ℕ) :
    ‖dworkMatrix p (dworkSplitting ϖ p) i j‖ ≤
      ‖(p : K)‖ ^ ((((p : ℝ) - 1) / (p : ℝ) ^ 2) * ((p : ℝ) * (i : ℝ) - (j : ℝ))) := by
  simpa using norm_dworkMatrix_le hp (dworkSplitting_wtGe hp hlt hϖ) i j

end OverconvergentSpace

/-! ## Section 2: Exact Finite-Dimensional Dwork Trace Formula (`ZMod` Orthogonality) -/

section DworkTraceFormula

/-- **`ZMod` Character Orthogonality for Primitive Roots of Unity**:
If `ζ` is a primitive `m`-th root of unity in a field `K` (`m > 0`), then for every `d : ℕ`:
`∑ t : ZMod m, ζ ^ (t.val * d) = if m ∣ d then (m : K) else 0`. -/
theorem zmod_root_sum {K : Type*} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (d : ℕ) :
    ∑ t : ZMod m, ζ ^ (t.val * d) = if m ∣ d then (m : K) else 0 := by
  have hsum_range : ∑ t : ZMod m, ζ ^ (t.val * d) = ∑ k ∈ Finset.range m, (ζ ^ d) ^ k := by
    refine Finset.sum_bij (fun t _ => t.val) ?_ ?_ ?_ ?_
    · intro t _
      exact Finset.mem_range.mpr (ZMod.val_lt t)
    · intro t₁ _ t₂ _ h
      exact ZMod.val_injective m h
    · intro k hk
      refine ⟨(k : ZMod m), Finset.mem_univ _, ?_⟩
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)
    · intro t _
      rw [mul_comm, pow_mul]
  rw [hsum_range]
  split_ifs with hdvd
  · have h1 : ζ ^ d = 1 := (hζ.pow_eq_one_iff_dvd d).mpr hdvd
    simp [h1]
  · have hne : ζ ^ d ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd d).mp h)
    have hgeom : (ζ ^ d - 1) * ∑ k ∈ Finset.range m, (ζ ^ d) ^ k = (ζ ^ d) ^ m - 1 := by
      have := geom_sum_mul (ζ ^ d) m
      rw [mul_comm] at this
      exact this
    have hzm : (ζ ^ d) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hzm, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hne)

/-- The `k`-fold Frobenius norm polynomial `g^{(k)}(X) := ∏_{r=0}^{k-1} g(X^{p^r})`. -/
def dworkNormPoly {R : Type*} [CommSemiring R] (p : ℕ) (g : Polynomial R) (k : ℕ) :
    Polynomial R :=
  ∏ r ∈ Finset.range k, g.comp (Polynomial.X ^ p ^ r)

theorem eval_dworkNormPoly {R : Type*} [CommSemiring R] (p : ℕ) (g : Polynomial R) (k : ℕ)
    (x : R) :
    (dworkNormPoly p g k).eval x = ∏ r ∈ Finset.range k, g.eval (x ^ p ^ r) := by
  unfold dworkNormPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]

theorem natDegree_dworkNormPoly_le {R : Type*} [CommSemiring R] (p : ℕ) (g : Polynomial R)
    (k : ℕ) :
    (dworkNormPoly p g k).natDegree ≤ g.natDegree * ∑ r ∈ Finset.range k, p ^ r := by
  induction k with
  | zero => simp [dworkNormPoly]
  | succ k ih =>
    unfold dworkNormPoly at ih ⊢
    rw [Finset.prod_range_succ, Finset.sum_range_succ, mul_add]
    calc ((∏ r ∈ Finset.range k, g.comp (Polynomial.X ^ p ^ r)) * g.comp (Polynomial.X ^ p ^ k)).natDegree
        ≤ (∏ r ∈ Finset.range k, g.comp (Polynomial.X ^ p ^ r)).natDegree +
            (g.comp (Polynomial.X ^ p ^ k)).natDegree := Polynomial.natDegree_mul_le
      _ ≤ g.natDegree * ∑ r ∈ Finset.range k, p ^ r + g.natDegree * p ^ k := by
          refine Nat.add_le_add ih ?_
          calc (g.comp (Polynomial.X ^ p ^ k)).natDegree
              ≤ g.natDegree * (Polynomial.X ^ p ^ k : Polynomial R).natDegree :=
                Polynomial.natDegree_comp_le
            _ ≤ g.natDegree * p ^ k :=
                Nat.mul_le_mul_left _ (Polynomial.natDegree_X_pow_le (p ^ k))

theorem sum_geom_mul_sub_one (p k : ℕ) (hp : 1 ≤ p) :
    (p - 1) * ∑ r ∈ Finset.range k, p ^ r = p ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : 1 ≤ p ^ k := Nat.one_le_pow k p (by omega)
    have h2 : (p - 1) * p ^ k = p ^ (k + 1) - p ^ k := by
      rw [Nat.sub_mul, one_mul, pow_succ']
    rw [h2]
    have hle : p ^ k ≤ p ^ (k + 1) := by
      rw [pow_succ']
      exact Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- Finite `N × N` matrix of the polynomial Dwork operator `ψ_g = U_p ∘ M_g` in the monomial
basis `{1, X, ..., X^{N-1}}`. -/
def dworkFinMatrix {R : Type*} [CommSemiring R] (p : ℕ) (g : Polynomial R) (N : ℕ) :
    Matrix (Fin N) (Fin N) R :=
  fun i j => if j.val ≤ p * i.val then g.coeff (p * i.val - j.val) else 0

theorem dworkFinMatrix_eq_dworkMatrix {R : Type*} [CommSemiring R] (p : ℕ) (g : Polynomial R)
    (N : ℕ) (i j : Fin N) :
    dworkFinMatrix p g N i j = dworkMatrix p (g : PowerSeries R) i.val j.val := by
  rw [dworkFinMatrix, dworkMatrix_eq]
  split_ifs <;> simp

/-- **Exact Matrix Power Identity for `dworkFinMatrix`**:
When `2 ≤ p` and `g.natDegree ≤ (p - 1) * N`, the finite subspace `deg < N` is strictly
invariant under `ψ_g`, so the `k`-th matrix power `(A_N)^k` equals the exact matrix of
`U_{p^k} ∘ M_{g^{(k)}}` with ZERO truncation error! -/
theorem dworkFinMatrix_pow_apply {R : Type*} [CommSemiring R] {p : ℕ} (hp : 2 ≤ p)
    {g : Polynomial R} {N : ℕ} (hdeg : g.natDegree ≤ (p - 1) * N) (k : ℕ) (i j : Fin N) :
    ((dworkFinMatrix p g N) ^ k) i j =
      if j.val ≤ p ^ k * i.val then (dworkNormPoly p g k).coeff (p ^ k * i.val - j.val) else 0 := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, one_mul, dworkNormPoly, Finset.prod_range_zero,
      Polynomial.coeff_one]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg hij]
      split_ifs with hle hsub
      · exfalso
        exact hij (Fin.ext (by omega))
      · rfl
      · rfl
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    have hnorm_succ : dworkNormPoly p g (k + 1) =
        dworkNormPoly p g k * g.comp (Polynomial.X ^ p ^ k) := by
      unfold dworkNormPoly
      rw [Finset.prod_range_succ]
    have hcoeff_comp : ∀ m : ℕ, (g.comp (Polynomial.X ^ p ^ k)).coeff m =
        if p ^ k ∣ m then g.coeff (m / p ^ k) else 0 := by
      intro m
      rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
      have hterm : ∀ r ∈ g.support, (Polynomial.C (g.coeff r) * (Polynomial.X ^ p ^ k) ^ r).coeff m =
          if m = p ^ k * r then g.coeff r else 0 := fun r _ => by
        rw [← pow_mul, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_congr rfl hterm]
      have hpkpos : 0 < p ^ k := pow_pos (by omega) k
      split_ifs with hdvd
      · by_cases hmem : m / p ^ k ∈ g.support
        · rw [Finset.sum_eq_single (m / p ^ k)]
          · rw [if_pos (Nat.mul_div_cancel' hdvd).symm]
          · intro r _ hr
            rw [if_neg]
            intro heq
            apply hr
            rw [heq, Nat.mul_div_cancel_left r hpkpos]
          · intro hno; exact (hno hmem).elim
        · rw [Finset.sum_eq_zero]
          · exact (Polynomial.notMem_support_iff.mp hmem).symm
          · intro r hr
            rw [if_neg]
            intro heq
            apply hmem
            have : m / p ^ k = r := by rw [heq, Nat.mul_div_cancel_left r hpkpos]
            rwa [this]
      · refine Finset.sum_eq_zero fun r _ => ?_
        rw [if_neg]
        intro heq
        exact hdvd ⟨r, heq⟩
    have hmul_expand : ∀ M : ℕ,
        (dworkNormPoly p g (k + 1)).coeff M =
          ∑ r ∈ Finset.range (M / p ^ k + 1),
            g.coeff r * (dworkNormPoly p g k).coeff (M - p ^ k * r) := by
      intro M
      rw [hnorm_succ, Polynomial.coeff_mul]
      rw [← Finset.sum_filter_of_ne (p := fun x : ℕ × ℕ => p ^ k ∣ x.2)
        (fun x _ hx => by
          by_contra h
          apply hx
          rw [hcoeff_comp, if_neg h, mul_zero])]
      have hpkpos : 0 < p ^ k := pow_pos (by omega) k
      refine Finset.sum_bij (fun x _ => x.2 / p ^ k) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
        rw [Finset.mem_range]
        have hle : x.2 ≤ M := by omega
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hle)
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx₁ hx₂
        have hx2 : x₁.2 = x₂.2 := by
          rw [← Nat.mul_div_cancel' hx₁.2, heq, Nat.mul_div_cancel' hx₂.2]
        ext
        · omega
        · exact hx2
      · intro r hr
        rw [Finset.mem_range] at hr
        have hle : p ^ k * r ≤ M := by
          have : r ≤ M / p ^ k := Nat.lt_succ_iff.mp hr
          calc p ^ k * r ≤ p ^ k * (M / p ^ k) := Nat.mul_le_mul_left _ this
            _ ≤ M := Nat.mul_div_le M (p ^ k)
        refine ⟨(M - p ^ k * r, p ^ k * r), ?_, Nat.mul_div_cancel_left r hpkpos⟩
        simp only [Finset.mem_filter, Finset.mem_antidiagonal]
        exact ⟨Nat.sub_add_cancel hle, dvd_mul_right _ _⟩
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
        rw [hcoeff_comp, if_pos hx.2, Nat.mul_div_cancel' hx.2, mul_comm]
        congr 2
        omega
    -- Now match LHS sum over l : Fin N with RHS
    have hLHS : ∑ l : Fin N, dworkFinMatrix p g N i l *
          (if j.val ≤ p ^ k * l.val then
            (dworkNormPoly p g k).coeff (p ^ k * l.val - j.val) else 0) =
        ∑ l ∈ Finset.range (p * i.val + 1),
          g.coeff (p * i.val - l) *
            (if j.val ≤ p ^ k * l then (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0) := by
      have hfin : ∑ l : Fin N, dworkFinMatrix p g N i l *
            (if j.val ≤ p ^ k * l.val then
              (dworkNormPoly p g k).coeff (p ^ k * l.val - j.val) else 0) =
          ∑ l ∈ Finset.range N,
            (if l ≤ p * i.val then g.coeff (p * i.val - l) else 0) *
              (if j.val ≤ p ^ k * l then
                (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0) := by
        unfold dworkFinMatrix
        rw [Fin.sum_univ_eq_sum_range (fun l =>
          (if l ≤ p * i.val then g.coeff (p * i.val - l) else 0) *
            (if j.val ≤ p ^ k * l then
              (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0))]
      rw [hfin]
      have hzero_ge : ∀ l, N ≤ l →
          (if j.val ≤ p ^ k * l then (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0) = 0 := by
        intro l hl
        split_ifs with hjl
        · refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
          have hdeg_k := natDegree_dworkNormPoly_le p g k
          have hgeom := sum_geom_mul_sub_one p k (by omega)
          have hpm1 : 0 < p - 1 := by omega
          have hmul_le : (p - 1) * (dworkNormPoly p g k).natDegree ≤ (p - 1) * ((p ^ k - 1) * N) := by
            calc (p - 1) * (dworkNormPoly p g k).natDegree
                ≤ (p - 1) * (g.natDegree * ∑ r ∈ Finset.range k, p ^ r) :=
                  Nat.mul_le_mul_left _ hdeg_k
              _ = g.natDegree * ((p - 1) * ∑ r ∈ Finset.range k, p ^ r) := by ring
              _ = g.natDegree * (p ^ k - 1) := by rw [hgeom]
              _ ≤ ((p - 1) * N) * (p ^ k - 1) := Nat.mul_le_mul_right _ hdeg
              _ = (p - 1) * ((p ^ k - 1) * N) := by ring
          have hdeg_bound : (dworkNormPoly p g k).natDegree ≤ (p ^ k - 1) * N :=
            Nat.le_of_mul_le_mul_left hmul_le hpm1
          have h1 : 1 ≤ p ^ k := Nat.one_le_pow k p (by omega)
          have hlow : (p ^ k - 1) * N < p ^ k * l - j.val := by
            have hjN : j.val < N := j.isLt
            have hleN : N ≤ p ^ k * N := Nat.le_mul_of_pos_left N (by omega)
            have hpkN : p ^ k * N ≤ p ^ k * l := Nat.mul_le_mul_left _ hl
            have hsub : (p ^ k - 1) * N = p ^ k * N - N := by
              rw [Nat.sub_mul, one_mul]
            omega
          exact lt_of_le_of_lt hdeg_bound hlow
        · rfl
      -- Now extend both sums to Finset.range (max N (p * i.val + 1))!
      set M := max N (p * i.val + 1)
      have h1 : ∑ l ∈ Finset.range N,
            (if l ≤ p * i.val then g.coeff (p * i.val - l) else 0) *
              (if j.val ≤ p ^ k * l then
                (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0) =
          ∑ l ∈ Finset.range M,
            (if l ≤ p * i.val then g.coeff (p * i.val - l) else 0) *
              (if j.val ≤ p ^ k * l then
                (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0) := by
        refine Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun l _ hl => ?_
        rw [Finset.mem_range, not_lt] at hl
        rw [hzero_ge l hl, mul_zero]
      have h2 : ∑ l ∈ Finset.range (p * i.val + 1),
            g.coeff (p * i.val - l) *
              (if j.val ≤ p ^ k * l then
                (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0) =
          ∑ l ∈ Finset.range M,
            (if l ≤ p * i.val then g.coeff (p * i.val - l) else 0) *
              (if j.val ≤ p ^ k * l then
                (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0) := by
        rw [← Finset.sum_subset (Finset.range_mono (le_max_right _ _))]
        · refine Finset.sum_congr rfl fun l hl => ?_
          rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))]
        · intro l _ hl
          rw [Finset.mem_range, not_lt] at hl
          rw [if_neg (by omega), zero_mul]
      exact h1.trans h2.symm
    rw [hLHS]
    -- Reindex l ↦ r = p * i - l in the range 0 .. p * i
    have hreindex : ∑ l ∈ Finset.range (p * i.val + 1),
          g.coeff (p * i.val - l) *
            (if j.val ≤ p ^ k * l then (dworkNormPoly p g k).coeff (p ^ k * l - j.val) else 0) =
        ∑ r ∈ Finset.range (p * i.val + 1),
          g.coeff r *
            (if j.val ≤ p ^ k * (p * i.val - r) then
              (dworkNormPoly p g k).coeff (p ^ k * (p * i.val - r) - j.val) else 0) := by
      refine Finset.sum_bij (fun l _ => p * i.val - l) ?_ ?_ ?_ ?_
      · intro l hl
        rw [Finset.mem_range] at hl ⊢
        omega
      · intro l₁ hl₁ l₂ hl₂ h
        rw [Finset.mem_range] at hl₁ hl₂
        omega
      · intro r hr
        rw [Finset.mem_range] at hr
        exact ⟨p * i.val - r, Finset.mem_range.mpr (by omega), by omega⟩
      · intro l hl
        rw [Finset.mem_range] at hl
        have hsub : p * i.val - (p * i.val - l) = l := by omega
        rw [hsub]
    rw [hreindex]
    have hpow_mul : p ^ (k + 1) * i.val = p ^ k * (p * i.val) := by
      rw [pow_succ, mul_assoc]
    split_ifs with hji
    · rw [hmul_expand]
      have hpkpos : 0 < p ^ k := pow_pos (by omega) k
      have hdiv_le : (p ^ (k + 1) * i.val - j.val) / p ^ k ≤ p * i.val := by
        rw [Nat.div_le_iff_le_mul_add_pred hpkpos]
        have : p ^ (k + 1) * i.val - j.val ≤ p ^ k * (p * i.val) := by
          rw [← hpow_mul]; exact Nat.sub_le _ _
        nlinarith
      symm
      rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hdiv_le))]
      · refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        have hr_le : p ^ k * r ≤ p ^ (k + 1) * i.val - j.val := by
          have : r ≤ (p ^ (k + 1) * i.val - j.val) / p ^ k := Nat.lt_succ_iff.mp hr
          calc p ^ k * r ≤ p ^ k * ((p ^ (k + 1) * i.val - j.val) / p ^ k) :=
                Nat.mul_le_mul_left _ this
            _ ≤ p ^ (k + 1) * i.val - j.val := Nat.mul_div_le _ _
        have hcond : j.val ≤ p ^ k * (p * i.val - r) := by
          rw [Nat.mul_sub_left_distrib, ← hpow_mul]
          omega
        rw [if_pos hcond]
        congr 2
        rw [Nat.mul_sub_left_distrib, ← hpow_mul]
        omega
      · intro r hrmem hr
        rw [Finset.mem_range] at hrmem
        rw [Finset.mem_range, not_lt] at hr
        have hgt : p ^ (k + 1) * i.val - j.val < p ^ k * r := by
          have h1 : (p ^ (k + 1) * i.val - j.val) / p ^ k < r := by omega
          have h2 := (Nat.div_lt_iff_lt_mul hpkpos).mp h1
          linarith
        have hnot : ¬ j.val ≤ p ^ k * (p * i.val - r) := by
          rw [Nat.mul_sub_left_distrib, ← hpow_mul]
          have hle_pi : p ^ k * r ≤ p ^ (k + 1) * i.val := by
            rw [hpow_mul]
            exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp hrmem)
          omega
        rw [if_neg hnot, mul_zero]
    · refine Finset.sum_eq_zero fun r _ => ?_
      have hnot : ¬ j.val ≤ p ^ k * (p * i.val - r) := by
        have hle : p ^ k * (p * i.val - r) ≤ p ^ (k + 1) * i.val := by
          rw [hpow_mul]
          exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        omega
      rw [if_neg hnot, mul_zero]

/-- **Exact Diagonal Trace Formula on `Fin N`**:
For `2 ≤ p`, `1 ≤ k`, and `g.natDegree < (p - 1) * N`,
`Tr((A_N)^k) = ∑_{n < N} coeff_{(p^k - 1) n}(g^{(k)})` and all terms with `n ≥ N` vanish. -/
theorem trace_dworkFinMatrix_pow {R : Type*} [CommSemiring R] {p : ℕ} (hp : 2 ≤ p)
    {g : Polynomial R} {N : ℕ} (hdeg : g.natDegree ≤ (p - 1) * N) (k : ℕ) :
    Matrix.trace ((dworkFinMatrix p g N) ^ k) =
      ∑ n ∈ Finset.range N, (dworkNormPoly p g k).coeff ((p ^ k - 1) * n) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro _ _ _ _ h
    exact Fin.val_injective h
  · intro n hn
    exact ⟨⟨n, Finset.mem_range.mp hn⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    rw [dworkFinMatrix_pow_apply hp hdeg k i i]
    have h1 : 1 ≤ p ^ k := Nat.one_le_pow k p (by omega)
    have hle : i.val ≤ p ^ k * i.val := Nat.le_mul_of_pos_left i.val (by omega)
    rw [if_pos hle]
    congr 1
    rw [Nat.sub_mul, one_mul]

/-- **Exact Finite-Dimensional Dwork Trace Formula (Teichmüller Multiplicative Sum)**:
Let `ζ ∈ K` be a primitive `(p^k - 1)`-st root of unity (`2 ≤ p`, `1 ≤ k`), and let
`g ∈ K[X]` have `g.natDegree < (p - 1) * N`. Then:
`(p^k - 1) * Tr((dworkFinMatrix p g N)^k) = ∑_{t : ZMod (p^k - 1)} ∏_{r < k} g((ζ^t)^{p^r})`. -/
theorem dwork_trace_formula_teichmuller {K : Type*} [Field K] {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k)
    [NeZero (p ^ k - 1)] {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ k - 1))
    {g : Polynomial K} {N : ℕ} (hdeg : g.natDegree < (p - 1) * N) :
    ((p ^ k - 1 : ℕ) : K) * Matrix.trace ((dworkFinMatrix p g N) ^ k) =
      ∑ t : ZMod (p ^ k - 1), ∏ r ∈ Finset.range k, g.eval ((ζ ^ t.val) ^ (p ^ r)) := by
  set m := p ^ k - 1 with hmdef
  set H := dworkNormPoly p g k with hHdef
  have hmpos : 0 < m := by
    have : 2 ^ 1 ≤ p ^ k := by
      calc 2 ^ 1 ≤ p ^ 1 := Nat.pow_le_pow_left hp 1
        _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  -- Expand RHS via H.eval (ζ ^ t.val) = ∑ d ∈ range (H.natDegree + 1), H.coeff d * (ζ^t.val)^d
  have hRHS : ∑ t : ZMod m, ∏ r ∈ Finset.range k, g.eval ((ζ ^ t.val) ^ (p ^ r)) =
      ∑ t : ZMod m, H.eval (ζ ^ t.val) := by
    refine Finset.sum_congr rfl fun t _ => (eval_dworkNormPoly p g k (ζ ^ t.val)).symm
  rw [hRHS]
  have heval_sum : ∀ t : ZMod m,
      H.eval (ζ ^ t.val) = ∑ d ∈ Finset.range (m * N), H.coeff d * ζ ^ (t.val * d) := by
    intro t
    have hHdeg : H.natDegree < m * N := by
      have h1 := natDegree_dworkNormPoly_le p g k
      have hgeom := sum_geom_mul_sub_one p k (by omega)
      have hpm1 : 0 < p - 1 := by omega
      have hmul : (p - 1) * H.natDegree < (p - 1) * (m * N) := by
        calc (p - 1) * H.natDegree
            ≤ (p - 1) * (g.natDegree * ∑ r ∈ Finset.range k, p ^ r) :=
              Nat.mul_le_mul_left _ h1
          _ = g.natDegree * ((p - 1) * ∑ r ∈ Finset.range k, p ^ r) := by ring
          _ = g.natDegree * m := by rw [hgeom]
          _ < ((p - 1) * N) * m := Nat.mul_lt_mul_of_pos_right hdeg hmpos
          _ = (p - 1) * (m * N) := by ring
      exact lt_of_mul_lt_mul_left hmul (Nat.zero_le _)
    rw [Polynomial.eval_eq_sum_range' hHdeg]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← pow_mul]
  simp_rw [heval_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ d ∈ Finset.range (m * N),
      ∑ t : ZMod m, H.coeff d * ζ ^ (t.val * d) =
        if m ∣ d then (m : K) * H.coeff d else 0 := fun d _ => by
    rw [← Finset.mul_sum, zmod_root_sum hζ d]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hinner]
  rw [trace_dworkFinMatrix_pow hp hdeg.le k, Finset.mul_sum]
  symm
  rw [← Finset.sum_filter_of_ne (p := fun d => m ∣ d) (fun d _ hd => by
    by_contra h; exact hd (if_neg h))]
  symm
  refine Finset.sum_bij (fun n _ => m * n) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_range] at hn
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mul_lt_mul_of_pos_left hn hmpos, dvd_mul_right m n⟩
  · intro n₁ _ n₂ _ h
    exact Nat.eq_of_mul_eq_mul_left hmpos h
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hlt, n, rfl⟩ := hd
    refine ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    exact lt_of_mul_lt_mul_left hlt (Nat.zero_le m)
  · intro n _
    rw [if_pos (dvd_mul_right m n)]

/-- **Affine Teichmüller Dwork Trace Formula (`x^{p^k} = x`, including `x = 0`)**:
Summing `∏_{r < k} g(x^{p^r})` over ALL `p^k` Teichmüller solutions of `x^{p^k} = x`
(indexed by `Option (ZMod (p^k - 1))` with `none ↦ 0` and `some t ↦ ζ^t.val`) equals
`g(0)^k + (p^k - 1) * Tr(A_N^k)`. -/
theorem dwork_trace_formula_affine {K : Type*} [Field K] {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k)
    [NeZero (p ^ k - 1)] {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ k - 1))
    {g : Polynomial K} {N : ℕ} (hdeg : g.natDegree < (p - 1) * N) :
    let teich : Option (ZMod (p ^ k - 1)) → K := fun o => o.elim 0 (fun t => ζ ^ t.val)
    ∑ o : Option (ZMod (p ^ k - 1)), ∏ r ∈ Finset.range k, g.eval ((teich o) ^ (p ^ r)) =
      (g.eval 0) ^ k + ((p ^ k - 1 : ℕ) : K) * Matrix.trace ((dworkFinMatrix p g N) ^ k) := by
  intro teich
  rw [Fintype.sum_option, dwork_trace_formula_teichmuller hp hk hζ hdeg]
  congr 1
  have hzero : ∀ r ∈ Finset.range k, g.eval ((teich none) ^ (p ^ r)) = g.eval 0 := fun r _ => by
    simp [teich, zero_pow (pow_ne_zero r (by omega : p ≠ 0))]
  rw [Finset.prod_congr rfl hzero, Finset.prod_const, Finset.card_range]

/-- **Pointwise `p^{-k}` Averaging Formula for `U_{p^k} ∘ M_{g^{(k)}}`**:
If `ω` is a primitive `p^k`-th root of unity in `K` with `(p : K) ≠ 0`, then for any `M`
strictly above `(dworkNormPoly p g k).natDegree / p^k`:
`∑_{n < M} coeff_{p^k n}(g^{(k)}) = (p^k)⁻¹ * ∑_{t : ZMod (p^k)} ∏_{r < k} g((ω^t)^{p^r})`. -/
theorem dwork_Up_pow_eval_one {K : Type*} [Field K] {p k : ℕ} (hp : 1 ≤ p)
    [NeZero (p ^ k)] {ω : K} (hω : IsPrimitiveRoot ω (p ^ k)) (hpK : (p : K) ≠ 0)
    {g : Polynomial K} {M : ℕ} (hM : (dworkNormPoly p g k).natDegree < p ^ k * M) :
    ∑ n ∈ Finset.range M, (dworkNormPoly p g k).coeff (p ^ k * n) =
      ((p : K) ^ k)⁻¹ *
        ∑ t : ZMod (p ^ k), ∏ r ∈ Finset.range k, g.eval ((ω ^ t.val) ^ (p ^ r)) := by
  set q := p ^ k with hqdef
  set H := dworkNormPoly p g k with hHdef
  have hqpos : 0 < q := pow_pos (by omega) k
  have hqK : (q : K) ≠ 0 := by
    rw [hqdef, Nat.cast_pow]
    exact pow_ne_zero k hpK
  have hRHS : ∑ t : ZMod q, ∏ r ∈ Finset.range k, g.eval ((ω ^ t.val) ^ (p ^ r)) =
      ∑ t : ZMod q, H.eval (ω ^ t.val) :=
    Finset.sum_congr rfl fun t _ => (eval_dworkNormPoly p g k (ω ^ t.val)).symm
  rw [hRHS]
  have heval_sum : ∀ t : ZMod q,
      H.eval (ω ^ t.val) = ∑ d ∈ Finset.range (q * M), H.coeff d * ω ^ (t.val * d) := fun t => by
    rw [Polynomial.eval_eq_sum_range' hM]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← pow_mul]
  simp_rw [heval_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ d ∈ Finset.range (q * M),
      ∑ t : ZMod q, H.coeff d * ω ^ (t.val * d) =
        if q ∣ d then (q : K) * H.coeff d else 0 := fun d _ => by
    rw [← Finset.mul_sum, zmod_root_sum hω d]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hinner]
  have hsum_eq : ∑ d ∈ Finset.range (q * M), (if q ∣ d then (q : K) * H.coeff d else 0) =
      (q : K) * ∑ n ∈ Finset.range M, H.coeff (q * n) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter_of_ne (p := fun d => q ∣ d) (fun d _ hd => by
      by_contra h; exact hd (if_neg h))]
    symm
    refine Finset.sum_bij (fun n _ => q * n) ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_range] at hn
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mul_lt_mul_of_pos_left hn hqpos, dvd_mul_right q n⟩
    · intro n₁ _ n₂ _ h
      exact Nat.eq_of_mul_eq_mul_left hqpos h
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨hlt, n, rfl⟩ := hd
      exact ⟨n, Finset.mem_range.mpr (lt_of_mul_lt_mul_left hlt (Nat.zero_le q)), rfl⟩
    · intro n _
      rw [if_pos (dvd_mul_right q n)]
  rw [hsum_eq, ← Nat.cast_pow, ← hqdef, inv_mul_cancel_left₀ hqK]

end DworkTraceFormula

/-! ## Section 3: $p$-adic Fredholm Determinant & Newton Polygon Coefficient Bounds -/

section FredholmDeterminant

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The Fredholm determinant (reverse characteristic polynomial) `det(1 - T A) ∈ K[T]`
of an `N × N` matrix `A`. -/
def fredholmDet {R : Type*} [CommRing R] {N : ℕ} (A : Matrix (Fin N) (Fin N) R) : Polynomial R :=
  Matrix.det ((1 : Matrix (Fin N) (Fin N) (Polynomial R)) -
    (Polynomial.X : Polynomial R) • A.map Polynomial.C)

private lemma units_int_smul_coeff {R : Type*} [CommRing R] (u : ℤˣ) (P : Polynomial R) (m : ℕ) :
    (u • P).coeff m = u • P.coeff m := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

omit [IsUltrametricDist K] in
private lemma norm_units_int_smul (u : ℤˣ) (x : K) : ‖u • x‖ = ‖x‖ := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- **Exact Leibniz–Subset Expansion of the `m`-th Fredholm Determinant Coefficient**:
`coeff m (det(1 - T A)) = (-1)^m ∑_σ sign(σ) ∑_{|S|=m, σ fixes Sᶜ} ∏_{i ∈ S} A (σ i) i`. -/
theorem coeff_fredholmDet {R : Type*} [CommRing R] {N : ℕ} (A : Matrix (Fin N) (Fin N) R) (m : ℕ) :
    (fredholmDet A).coeff m =
      (-1 : R) ^ m *
        ∑ σ : Equiv.Perm (Fin N),
          Equiv.Perm.sign σ •
            ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
              if (∀ i ∉ S, σ i = i) then ∏ i ∈ S, A (σ i) i else 0 := by
  unfold fredholmDet
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [units_int_smul_coeff]
  have hsmul_comm : (-1 : R) ^ m * (Equiv.Perm.sign σ •
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
        if (∀ i ∉ S, σ i = i) then ∏ i ∈ S, A (σ i) i else 0) =
      Equiv.Perm.sign σ • ((-1 : R) ^ m *
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
          if (∀ i ∉ S, σ i = i) then ∏ i ∈ S, A (σ i) i else 0) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hsmul_comm]
  congr 1
  have hmat : ∀ i : Fin N,
      ((1 : Matrix (Fin N) (Fin N) (Polynomial R)) -
        (Polynomial.X : Polynomial R) • A.map Polynomial.C) (σ i) i =
        (-(Polynomial.C (A (σ i) i)) * Polynomial.X) + (if σ i = i then (1 : Polynomial R) else 0) := by
    intro i
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    ring
  simp_rw [hmat]
  rw [Finset.prod_add, Polynomial.finsetSum_coeff, Finset.mul_sum]
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      ((∏ i ∈ S, (-(Polynomial.C (A (σ i) i)) * Polynomial.X)) *
        (∏ i ∈ Finset.univ \ S, if σ i = i then (1 : Polynomial R) else 0)).coeff m =
      if S.card = m then
        (-1 : R) ^ m * (if (∀ i ∉ S, σ i = i) then ∏ i ∈ S, A (σ i) i else 0)
      else 0 := by
    intro S _
    have hprod1 : ∏ i ∈ S, (-(Polynomial.C (A (σ i) i)) * Polynomial.X) =
        Polynomial.C ((-1 : R) ^ S.card * ∏ i ∈ S, A (σ i) i) * Polynomial.X ^ S.card := by
      have hfactor : ∀ i ∈ S, -(Polynomial.C (A (σ i) i)) * Polynomial.X =
          (Polynomial.C (-1 : R) * Polynomial.C (A (σ i) i)) * Polynomial.X := fun i _ => by
        simp [neg_mul]
      rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.prod_const, ← map_pow, ← map_prod, ← map_mul]
    have hprod2 : ∏ i ∈ Finset.univ \ S, (if σ i = i then (1 : Polynomial R) else 0) =
        if (∀ i ∉ S, σ i = i) then (1 : Polynomial R) else 0 := by
      split_ifs with hall
      · refine Finset.prod_eq_one fun i hi => ?_
        rw [Finset.mem_sdiff] at hi
        rw [if_pos (hall i hi.2)]
      · push Not at hall
        obtain ⟨i, hiS, hne⟩ := hall
        refine Finset.prod_eq_zero (i := i) ?_ ?_
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiS⟩
        · exact if_neg hne
    rw [hprod1, hprod2]
    by_cases hall : ∀ i ∉ S, σ i = i
    · rw [if_pos hall, mul_one, Polynomial.coeff_C_mul_X_pow]
      by_cases hcard : S.card = m
      · rw [if_pos hcard.symm, if_pos hcard, if_pos hall, hcard]
      · rw [if_neg (Ne.symm hcard), if_neg hcard]
    · rw [if_neg hall, mul_zero, Polynomial.coeff_zero, if_neg hall, mul_zero]
      split_ifs <;> rfl
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_filter_of_ne (p := fun S : Finset (Fin N) => S.card = m)
    (fun S _ hS => by by_contra h; exact hS (if_neg h))]
  have hfilt : (Finset.univ : Finset (Fin N)).powerset.filter (fun S => S.card = m) =
      (Finset.univ : Finset (Fin N)).powersetCard m := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [hfilt]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  rw [if_pos hS.2]

theorem coeff_fredholmDet_zero {R : Type*} [CommRing R] {N : ℕ} (A : Matrix (Fin N) (Fin N) R) :
    (fredholmDet A).coeff 0 = 1 := by
  rw [coeff_fredholmDet, pow_zero, one_mul]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
  · simp [Finset.powersetCard_zero]
  · intro σ _ hσ
    rw [Finset.powersetCard_zero, Finset.sum_singleton]
    have hnot : ¬ ∀ i ∉ (∅ : Finset (Fin N)), σ i = i := by
      intro hall
      apply hσ
      ext i
      simpa using congrArg Fin.val (hall i (Finset.notMem_empty i))
    rw [if_neg hnot, smul_zero]
  · intro h; exact (h (Finset.mem_univ 1)).elim

/-- **Combinatorial Triangular Lower Bound**:
For any finite subset `S` of `ℕ`, `|S| * (|S| - 1) ≤ 2 * ∑_{i ∈ S} i`. -/
theorem card_mul_pred_le_two_mul_sum_nat (S : Finset ℕ) :
    S.card * (S.card - 1) ≤ 2 * ∑ i ∈ S, i := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S.Nonempty
    · set M := S.max' hS
      have hM : M ∈ S := Finset.max'_mem S hS
      set T := S.erase M
      have hTss : T ⊂ S := Finset.erase_ssubset hM
      have hih := ih T hTss
      have hcard : S.card = T.card + 1 := (Finset.card_erase_add_one hM).symm
      have hsum : ∑ i ∈ S, i = M + ∑ i ∈ T, i := (Finset.add_sum_erase S id hM).symm
      have hMge : T.card ≤ M := by
        have hsub : T ⊆ Finset.range M := by
          intro x hx
          rw [Finset.mem_erase] at hx
          rw [Finset.mem_range]
          exact lt_of_le_of_ne (Finset.le_max' S x hx.2) hx.1
        calc T.card ≤ (Finset.range M).card := Finset.card_le_card hsub
          _ = M := Finset.card_range M
      rw [hcard, hsum, Nat.add_sub_cancel]
      have h1 : (T.card + 1) * T.card = T.card * (T.card - 1) + 2 * T.card := by
        rcases T.card with _ | k
        · simp
        · rw [Nat.add_sub_cancel]; ring
      rw [h1]
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp

theorem tri_le_sum_fin_val {N : ℕ} (S : Finset (Fin N)) :
    ((S.card : ℝ) * ((S.card : ℝ) - 1) / 2) ≤ ∑ i ∈ S, (i.val : ℝ) := by
  set T : Finset ℕ := S.image Fin.val
  have hcard : T.card = S.card := Finset.card_image_of_injective S Fin.val_injective
  have hsum : ∑ n ∈ T, n = ∑ i ∈ S, i.val := Finset.sum_image fun _ _ _ _ h => Fin.val_injective h
  have hnat := card_mul_pred_le_two_mul_sum_nat T
  rw [hcard, hsum] at hnat
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, zero_mul, zero_div]
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  · have hR : ((S.card * (S.card - 1) : ℕ) : ℝ) ≤ ((2 * ∑ i ∈ S, i.val : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sum] at hR
    linarith

/-- If `σ : Perm (Fin N)` fixes every element outside `S`, then `σ` restricts to a bijection
on `S`, so `∑_{i ∈ S} f (σ i) = ∑_{i ∈ S} f i`. -/
lemma sum_perm_eq_of_fixes_compl {N : ℕ} {M : Type*} [AddCommMonoid M]
    (σ : Equiv.Perm (Fin N)) (S : Finset (Fin N)) (hfix : ∀ i ∉ S, σ i = i) (f : Fin N → M) :
    ∑ i ∈ S, f (σ i) = ∑ i ∈ S, f i := by
  refine Finset.sum_bij (fun i _ => σ i) ?_ ?_ ?_ ?_
  · intro i hi
    by_contra hnot
    have h1 := hfix (σ i) hnot
    have h2 : σ i = i := σ.injective h1
    exact hnot (h2.symm ▸ hi)
  · intro i₁ _ i₂ _ h
    exact σ.injective h
  · intro j hj
    refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
    by_contra hnot
    have h1 := hfix (σ.symm j) hnot
    rw [σ.apply_symm_apply] at h1
    exact hnot (h1 ▸ hj)
  · intro _ _; rfl

/-- **Pure Row-Decay $p$-adic Fredholm Determinant Newton Polygon Lower Bound**:
If `0 < pi ≤ 1`, `0 ≤ α`, and `∀ i j, ‖A i j‖ ≤ pi ^ (α * i)`, then the `m`-th coefficient
of `det(1 - T A)` satisfies:
`‖(fredholmDet A).coeff m‖ ≤ pi ^ (α * m * (m - 1) / 2)`. -/
theorem norm_coeff_fredholmDet_of_row_decay {N : ℕ} {pi α : ℝ} (hpi0 : 0 < pi) (hpi1 : pi ≤ 1)
    (hα : 0 ≤ α) {A : Matrix (Fin N) (Fin N) K}
    (hA : ∀ i j : Fin N, ‖A i j‖ ≤ pi ^ (α * (i.val : ℝ))) (m : ℕ) :
    ‖(fredholmDet A).coeff m‖ ≤ pi ^ (α * ((m : ℝ) * ((m : ℝ) - 1) / 2)) := by
  rw [coeff_fredholmDet, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine ultrametric_norm_sum_le _ _ (Real.rpow_nonneg hpi0.le _) fun σ _ => ?_
  rw [norm_units_int_smul]
  refine ultrametric_norm_sum_le _ _ (Real.rpow_nonneg hpi0.le _) fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  split_ifs with hfix
  · rw [norm_prod]
    calc ∏ i ∈ S, ‖A (σ i) i‖
        ≤ ∏ i ∈ S, pi ^ (α * ((σ i).val : ℝ)) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hA (σ i) i
      _ = pi ^ (∑ i ∈ S, α * ((σ i).val : ℝ)) := (Real.rpow_sum_of_pos hpi0 _ _).symm
      _ = pi ^ (α * ∑ i ∈ S, (i.val : ℝ)) := by
          rw [← Finset.mul_sum, sum_perm_eq_of_fixes_compl σ S hfix (fun i => (i.val : ℝ))]
      _ ≤ pi ^ (α * ((m : ℝ) * ((m : ℝ) - 1) / 2)) := by
          refine Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1 ?_
          have htri := tri_le_sum_fin_val S
          rw [hS.2] at htri
          exact mul_le_mul_of_nonneg_left htri hα
  · rw [norm_zero]
    exact Real.rpow_nonneg hpi0.le _

/-- **Additive $p$-adic Valuation Form of the Fredholm Determinant Bound**:
Under row decay `‖A i j‖ ≤ ‖(p : K)‖ ^ (α * i)` (`‖(p : K)‖ < 1`, `0 ≤ α`), every nonzero
coefficient `c_m = (fredholmDet A).coeff m` has additive `p`-adic valuation
`v_p(c_m) := log_{‖p‖} ‖c_m‖ ≥ α * m * (m - 1) / 2`. -/
theorem valuation_coeff_fredholmDet_of_row_decay [CharZero K] {p N : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {α : ℝ} (hα : 0 ≤ α) {A : Matrix (Fin N) (Fin N) K}
    (hA : ∀ i j : Fin N, ‖A i j‖ ≤ ‖(p : K)‖ ^ (α * (i.val : ℝ)))
    {m : ℕ} (hm : (fredholmDet A).coeff m ≠ 0) :
    α * ((m : ℝ) * ((m : ℝ) - 1) / 2) ≤
      Real.logb ‖(p : K)‖ ‖(fredholmDet A).coeff m‖ := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hlogneg : Real.log ‖(p : K)‖ < 0 := Real.log_neg hpi0 hlt
  have hbd := norm_coeff_fredholmDet_of_row_decay hpi0 hlt.le hα hA m
  have hpos : 0 < ‖(fredholmDet A).coeff m‖ := norm_pos_iff.mpr hm
  have hlog := Real.log_le_log hpos hbd
  rw [Real.log_rpow hpi0] at hlog
  rw [Real.logb, le_div_iff_of_neg hlogneg]
  exact hlog

/-- **Sharp Off-Diagonal Dwork Fredholm Determinant Bound**:
If `0 < pi ≤ 1`, `0 ≤ c`, `1 ≤ p`, and `∀ i j, ‖A i j‖ ≤ pi ^ (c * (p * i - j))`, then the
exact permutation cancellation `∑_{i ∈ S} σ(i) = ∑_{i ∈ S} i` eliminates `-j` and yields:
`‖(fredholmDet A).coeff m‖ ≤ pi ^ (c * (p - 1) * m * (m - 1) / 2)`. -/
theorem norm_coeff_fredholmDet_of_dwork_decay {N : ℕ} {pi c : ℝ} (hpi0 : 0 < pi) (hpi1 : pi ≤ 1)
    (hc : 0 ≤ c) {p : ℕ} (hp : 1 ≤ p) {A : Matrix (Fin N) (Fin N) K}
    (hA : ∀ i j : Fin N, ‖A i j‖ ≤ pi ^ (c * ((p : ℝ) * (i.val : ℝ) - (j.val : ℝ)))) (m : ℕ) :
    ‖(fredholmDet A).coeff m‖ ≤
      pi ^ (c * ((p : ℝ) - 1) * ((m : ℝ) * ((m : ℝ) - 1) / 2)) := by
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [coeff_fredholmDet, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine ultrametric_norm_sum_le _ _ (Real.rpow_nonneg hpi0.le _) fun σ _ => ?_
  rw [norm_units_int_smul]
  refine ultrametric_norm_sum_le _ _ (Real.rpow_nonneg hpi0.le _) fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  split_ifs with hfix
  · rw [norm_prod]
    calc ∏ i ∈ S, ‖A (σ i) i‖
        ≤ ∏ i ∈ S, pi ^ (c * ((p : ℝ) * ((σ i).val : ℝ) - (i.val : ℝ))) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hA (σ i) i
      _ = pi ^ (∑ i ∈ S, c * ((p : ℝ) * ((σ i).val : ℝ) - (i.val : ℝ))) :=
          (Real.rpow_sum_of_pos hpi0 _ _).symm
      _ = pi ^ (c * ((p : ℝ) - 1) * ∑ i ∈ S, (i.val : ℝ)) := by
          congr 1
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
            sum_perm_eq_of_fixes_compl σ S hfix (fun i => (i.val : ℝ))]
          ring
      _ ≤ pi ^ (c * ((p : ℝ) - 1) * ((m : ℝ) * ((m : ℝ) - 1) / 2)) := by
          refine Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1 ?_
          have htri := tri_le_sum_fin_val S
          rw [hS.2] at htri
          exact mul_le_mul_of_nonneg_left htri (mul_nonneg hc hp1)
  · rw [norm_zero]
    exact Real.rpow_nonneg hpi0.le _

/-- **Concrete Fredholm Determinant Bound for Dwork's Splitting Function `θ(X)`**:
For any `N × N` truncation of the Dwork operator `ψ_θ = U_p ∘ M_{θ}`,
`‖(fredholmDet A_N).coeff m‖ ≤ ‖(p : K)‖ ^ (((p - 1)^2 / p^2) * m (m - 1) / 2)`. -/
theorem norm_coeff_fredholmDet_dworkSplitting [CharZero K] {p : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K)) (N m : ℕ) :
    let A : Matrix (Fin N) (Fin N) K := fun i j => dworkMatrix p (dworkSplitting ϖ p) i.val j.val
    ‖(fredholmDet A).coeff m‖ ≤
      ‖(p : K)‖ ^ ((((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2) * ((m : ℝ) * ((m : ℝ) - 1) / 2)) := by
  intro A
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hc0 : 0 ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  have hbd := norm_coeff_fredholmDet_of_dwork_decay hpi0 hlt.le hc0 hp.one_le
    (A := A) (fun i j => norm_dworkMatrix_dworkSplitting_le hp hlt hϖ i.val j.val) m
  refine hbd.trans_eq ?_
  congr 1
  ring

end FredholmDeterminant

/-! ## Section 4: Ultrametric Newton Polygon Theorem & Bridge to `Stage2HodgeWeights` -/

section NewtonPolygonBridge

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Exact elementary-symmetric expansion of `∏_{i : Fin N} (1 - λ_i T)`. -/
theorem coeff_prod_one_sub_X {R : Type*} [CommRing R] {N : ℕ} (lam : Fin N → R) (k : ℕ) :
    (∏ i : Fin N, ((1 : Polynomial R) - Polynomial.C (lam i) * Polynomial.X)).coeff k =
      (-1 : R) ^ k * ∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard k, ∏ i ∈ I, lam i := by
  have hrew : ∀ i : Fin N, (1 : Polynomial R) - Polynomial.C (lam i) * Polynomial.X =
      (-(Polynomial.C (lam i)) * Polynomial.X) + 1 := fun i => by ring
  simp_rw [hrew]
  rw [Finset.prod_add, Polynomial.finsetSum_coeff, Finset.mul_sum]
  have hterm : ∀ I ∈ (Finset.univ : Finset (Fin N)).powerset,
      ((∏ i ∈ I, (-(Polynomial.C (lam i)) * Polynomial.X)) *
        (∏ _i ∈ Finset.univ \ I, (1 : Polynomial R))).coeff k =
      if I.card = k then (-1 : R) ^ k * ∏ i ∈ I, lam i else 0 := by
    intro I _
    rw [Finset.prod_const_one, mul_one]
    have hprod : ∏ i ∈ I, (-(Polynomial.C (lam i)) * Polynomial.X) =
        Polynomial.C ((-1 : R) ^ I.card * ∏ i ∈ I, lam i) * Polynomial.X ^ I.card := by
      have hf : ∀ i ∈ I, -(Polynomial.C (lam i)) * Polynomial.X =
          (Polynomial.C (-1 : R) * Polynomial.C (lam i)) * Polynomial.X := fun i _ => by
        simp [neg_mul]
      rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.prod_const, ← map_pow, ← map_prod, ← map_mul]
    rw [hprod, Polynomial.coeff_C_mul_X_pow]
    by_cases hcard : I.card = k
    · subst hcard; simp
    · simp [hcard, Ne.symm hcard]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_filter_of_ne (p := fun I : Finset (Fin N) => I.card = k)
    (fun I _ hI => by by_contra h; exact hI (if_neg h))]
  have hfilt : (Finset.univ : Finset (Fin N)).powerset.filter (fun I => I.card = k) =
      (Finset.univ : Finset (Fin N)).powersetCard k := by
    ext I
    simp [Finset.mem_powersetCard]
  rw [hfilt]
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [Finset.mem_powersetCard] at hI
  rw [if_pos hI.2]

/-- The sorted slope list of a monotone function `ν : Fin N → ℚ` is `List.ofFn ν`. -/
lemma sortedSlopes_of_monotone {N : ℕ} (ν : Fin N → ℚ) (hmono : Monotone ν) :
    sortedSlopes ((Finset.univ : Finset (Fin N)).val.map ν) = List.ofFn ν := by
  set S : Multiset ℚ := (Finset.univ : Finset (Fin N)).val.map ν
  have hperm : List.Perm (sortedSlopes S) (List.ofFn ν) := by
    rw [← Multiset.coe_eq_coe, sortedSlopes_coe]
    have hcoe : ((List.ofFn ν : List ℚ) : Multiset ℚ) =
        ((List.finRange N).map ν : Multiset ℚ) := by
      rw [List.ofFn_eq_map]
    rw [hcoe]
    change (Finset.univ : Finset (Fin N)).val.map ν = ((List.finRange N : List (Fin N)) : Multiset (Fin N)).map ν
    congr 1
  have hp1 : (sortedSlopes S).Pairwise (· ≤ ·) := sortedSlopes_pairwise S
  have hp2 : (List.ofFn ν).Pairwise (· ≤ ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn]
    exact hmono (by exact Fin.mk_le_mk.mpr (le_of_lt hij))
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hp1 hp2

/-- For monotone `ν : Fin N → ℚ`, `polygon S k` equals `∑_{i : Fin N, i < k} ν i`. -/
lemma polygon_of_monotone {N : ℕ} (ν : Fin N → ℚ) (hmono : Monotone ν) {k : ℕ} (hk : k ≤ N) :
    polygon ((Finset.univ : Finset (Fin N)).val.map ν) k =
      ∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i.val < k), ν i := by
  unfold polygon
  rw [sortedSlopes_of_monotone ν hmono]
  have h1 : ((List.ofFn ν).take k).sum =
      ∑ j ∈ Finset.range k, if h : j < N then ν ⟨j, h⟩ else 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < N := by omega
      have hlen : k < (List.ofFn ν).length := by simpa using hk'
      rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some, List.sum_append,
        List.sum_singleton, ih (Nat.le_of_succ_le hk), Finset.sum_range_succ,
        List.getElem_ofFn, dif_pos hk']
  rw [h1]
  refine Finset.sum_bij (fun j hj => ⟨j, lt_of_lt_of_le (Finset.mem_range.mp hj) hk⟩) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_range.mp hj
  · intro j₁ _ j₂ _ h
    exact congrArg Fin.val h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨i.val, Finset.mem_range.mpr hi, Fin.eta i _⟩
  · intro j hj
    have hjN : j < N := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
    rw [dif_pos hjN]

/-- **Ultrametric Break-Point Norm Equality**:
If `P(T) = ∏_{i : Fin N} (1 - λ_i T)` has sorted rational slopes `ν : Fin N → ℚ`
(`‖λ i‖ = pi ^ (ν i : ℝ)`, `0 < pi < 1`), then at every break point `k ≤ N`
(either `k = 0`, `k = N`, or `ν (k - 1) < ν k`),
`‖P.coeff k‖ = pi ^ (polygon N_slopes k : ℝ)`. -/
theorem norm_coeff_prod_one_sub_at_break {N : ℕ} {pi : ℝ} (hpi0 : 0 < pi) (hpi1 : pi < 1)
    {lam : Fin N → K} {ν : Fin N → ℚ} (hmono : Monotone ν)
    (hnorm : ∀ i : Fin N, ‖lam i‖ = pi ^ (ν i : ℝ))
    {k : ℕ} (hk : k ≤ N)
    (hbreak : k = 0 ∨ k = N ∨ ∀ (h1 : k - 1 < N) (h2 : k < N), ν ⟨k - 1, h1⟩ < ν ⟨k, h2⟩) :
    ‖(∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X)).coeff k‖ =
      pi ^ (polygon ((Finset.univ : Finset (Fin N)).val.map ν) k : ℝ) := by
  rw [coeff_prod_one_sub_X, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    polygon_of_monotone ν hmono hk]
  set I₀ : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => i.val < k) with hI₀def
  have hI₀card : I₀.card = k := by
    have hbij : I₀.card = (Finset.range k).card := by
      refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
      · intro i hi
        simp only [I₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_range.mpr hi
      · intro _ _ _ _ h; exact Fin.val_injective h
      · intro j hj
        rw [Finset.mem_range] at hj
        exact ⟨⟨j, lt_of_lt_of_le hj hk⟩, by simp [I₀, hj], rfl⟩
    rw [hbij, Finset.card_range]
  have hI₀mem : I₀ ∈ (Finset.univ : Finset (Fin N)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hI₀card⟩
  have hnorm_prod : ∀ I : Finset (Fin N), ‖∏ i ∈ I, lam i‖ = pi ^ ((∑ i ∈ I, ν i : ℚ) : ℝ) := by
    intro I
    rw [norm_prod]
    simp_rw [hnorm]
    rw [← Real.rpow_sum_of_pos hpi0, Rat.cast_sum]
  rcases hbreak with rfl | rfl | hstrict
  · have hI0 : I₀ = ∅ := by ext i; simp [I₀]
    rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty, norm_one, hI0,
      Finset.sum_empty, Rat.cast_zero, Real.rpow_zero]
  · have hI0 : I₀ = Finset.univ := by ext i; simp [I₀]
    have hpcard : (Finset.univ : Finset (Fin k)).powersetCard k = {Finset.univ} := by
      simpa [Fintype.card_fin] using Finset.powersetCard_self (Finset.univ : Finset (Fin k))
    rw [hpcard, Finset.sum_singleton, hI0, hnorm_prod]
  · -- Strict break point `0 < k < N` with `ν (k - 1) < ν k`
    by_cases hk0 : k = 0
    · subst hk0
      have hI0 : I₀ = ∅ := by ext i; simp [I₀]
      rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty, norm_one, hI0,
        Finset.sum_empty, Rat.cast_zero, Real.rpow_zero]
    · by_cases hkN : k = N
      · subst hkN
        have hI0 : I₀ = Finset.univ := by ext i; simp [I₀]
        have hpcard : (Finset.univ : Finset (Fin k)).powersetCard k = {Finset.univ} := by
          simpa [Fintype.card_fin] using Finset.powersetCard_self (Finset.univ : Finset (Fin k))
        rw [hpcard, Finset.sum_singleton, hI0, hnorm_prod]
      · have hk1 : k - 1 < N := by omega
        have hk2 : k < N := by omega
        have hgap : ν ⟨k - 1, hk1⟩ < ν ⟨k, hk2⟩ := hstrict hk1 hk2
        rw [← Finset.add_sum_erase _ _ hI₀mem]
        have hrest : ∀ I ∈ ((Finset.univ : Finset (Fin N)).powersetCard k).erase I₀,
            ‖∏ i ∈ I, lam i‖ < ‖∏ i ∈ I₀, lam i‖ := by
          intro I hI
          rw [Finset.mem_erase, Finset.mem_powersetCard] at hI
          obtain ⟨hIne, _, hIcard⟩ := hI
          rw [hnorm_prod I, hnorm_prod I₀]
          refine Real.rpow_lt_rpow_of_exponent_gt hpi0 hpi1 ?_
          exact_mod_cast (by
            -- Compare ∑_{i ∈ I₀} ν i < ∑_{i ∈ I} ν i via sdiff decomposition
            have hcard_eq : (I \ I₀).card = (I₀ \ I).card := by
              have h1 := Finset.card_sdiff_add_card_inter I I₀
              have h2 := Finset.card_sdiff_add_card_inter I₀ I
              rw [Finset.inter_comm] at h2
              omega
            have hne_sdiff : (I \ I₀).Nonempty := by
              by_contra hemp
              rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
              exact hIne (Finset.eq_of_subset_of_card_le hemp (by omega))
            have hpos_card : (0 : ℚ) < ((I \ I₀).card : ℚ) := by
              exact_mod_cast Finset.card_pos.mpr hne_sdiff
            have hI₀_split : ∑ i ∈ I₀, ν i = ∑ i ∈ I₀ \ I, ν i + ∑ i ∈ I₀ ∩ I, ν i := by
              have := Finset.sum_sdiff (s₁ := I₀ ∩ I) (s₂ := I₀) Finset.inter_subset_left (f := ν)
              rw [Finset.sdiff_inter_self_left] at this
              exact this.symm
            have hI_split : ∑ i ∈ I, ν i = ∑ i ∈ I \ I₀, ν i + ∑ i ∈ I ∩ I₀, ν i := by
              have := Finset.sum_sdiff (s₁ := I ∩ I₀) (s₂ := I) Finset.inter_subset_left (f := ν)
              rw [Finset.sdiff_inter_self_left] at this
              exact this.symm
            have hle_left : ∑ i ∈ I₀ \ I, ν i ≤ ((I₀ \ I).card : ℚ) * ν ⟨k - 1, hk1⟩ := by
              calc ∑ i ∈ I₀ \ I, ν i
                  ≤ ∑ _i ∈ I₀ \ I, ν ⟨k - 1, hk1⟩ := Finset.sum_le_sum fun i hi => by
                    have hiI₀ := (Finset.mem_sdiff.mp hi).1
                    simp only [I₀, Finset.mem_filter, Finset.mem_univ, true_and] at hiI₀
                    exact hmono (Fin.mk_le_mk.mpr (by omega))
                _ = ((I₀ \ I).card : ℚ) * ν ⟨k - 1, hk1⟩ := by simp
            have hge_right : ((I \ I₀).card : ℚ) * ν ⟨k, hk2⟩ ≤ ∑ i ∈ I \ I₀, ν i := by
              calc ((I \ I₀).card : ℚ) * ν ⟨k, hk2⟩
                  = ∑ _i ∈ I \ I₀, ν ⟨k, hk2⟩ := by simp
                _ ≤ ∑ i ∈ I \ I₀, ν i := Finset.sum_le_sum fun i hi => by
                    have hnotI₀ := (Finset.mem_sdiff.mp hi).2
                    simp only [I₀, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnotI₀
                    exact hmono (Fin.mk_le_mk.mpr hnotI₀)
            rw [hI₀_split, hI_split, Finset.inter_comm I I₀]
            have hstrict_mul :
                ((I₀ \ I).card : ℚ) * ν ⟨k - 1, hk1⟩ < ((I \ I₀).card : ℚ) * ν ⟨k, hk2⟩ := by
              rw [← hcard_eq]
              exact mul_lt_mul_of_pos_left hgap hpos_card
            linarith : ∑ i ∈ I₀, ν i < ∑ i ∈ I, ν i)
        -- Ultrametric strict dominance of the unique maximum term `I₀`
        have hlt_sum : ‖∑ I ∈ ((Finset.univ : Finset (Fin N)).powersetCard k).erase I₀,
            ∏ i ∈ I, lam i‖ < ‖∏ i ∈ I₀, lam i‖ := by
          set rest := ((Finset.univ : Finset (Fin N)).powersetCard k).erase I₀
          by_cases hremp : rest.Nonempty
          · obtain ⟨Imax, hImax_mem, hImax_ge⟩ :=
              Finset.exists_max_image rest (fun I => ‖∏ i ∈ I, lam i‖) hremp
            have hbd : ‖∑ I ∈ rest, ∏ i ∈ I, lam i‖ ≤ ‖∏ i ∈ Imax, lam i‖ :=
              ultrametric_norm_sum_le rest _ (norm_nonneg _) hImax_ge
            exact lt_of_le_of_lt hbd (hrest Imax hImax_mem)
          · rw [Finset.not_nonempty_iff_eq_empty.mp hremp, Finset.sum_empty, norm_zero, hnorm_prod]
            exact Real.rpow_pos_of_pos hpi0 _
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt_sum.ne', max_eq_left hlt_sum.le,
          hnorm_prod]

/-- Elementary discrete convexity chord inequality: if `h : ℕ → ℚ` has non-decreasing
first differences on `[0, N]`, then for `a ≤ k ≤ b ≤ N`:
`((b - a : ℕ) : ℚ) * h k ≤ ((b - k : ℕ) : ℚ) * h a + ((k - a : ℕ) : ℚ) * h b`. -/
lemma discrete_convex_chord {N : ℕ} {h : ℕ → ℚ}
    (hconv : ∀ j : ℕ, j + 1 < N → h (j + 1) - h j ≤ h (j + 2) - h (j + 1))
    {a k b : ℕ} (hak : a ≤ k) (hkb : k ≤ b) (hbN : b ≤ N) :
    ((b - a : ℕ) : ℚ) * h k ≤ ((b - k : ℕ) : ℚ) * h a + ((k - a : ℕ) : ℚ) * h b := by
  have hstep_mono : ∀ i j : ℕ, i ≤ j → j < N → h (i + 1) - h i ≤ h (j + 1) - h j := by
    intro i j hij hjN
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 := ih (by omega) (by omega)
      have h2 := hconv (i + d) (by omega)
      have hadd : i + (d + 1) = i + d + 1 := by omega
      rw [hadd]
      linarith
  have htele : ∀ u v : ℕ, u ≤ v → h v - h u = ∑ r ∈ Finset.range (v - u), (h (u + r + 1) - h (u + r)) := by
    intro u v huv
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
    rw [Nat.add_sub_cancel_left]
    clear huv
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ, ← ih]
      have : u + (d + 1) = u + d + 1 := by omega
      rw [this]
      ring
  by_cases hka : k = a
  · subst hka; simp
  by_cases hbk : b = k
  · subst hbk; simp
  have hk_lt_b : k < b := lt_of_le_of_ne hkb (Ne.symm hbk)
  have ha_lt_k : a < k := lt_of_le_of_ne hak (Ne.symm hka)
  have hleft : h k - h a ≤ ((k - a : ℕ) : ℚ) * (h (k + 1) - h k) := by
    rw [htele a k hak]
    calc ∑ r ∈ Finset.range (k - a), (h (a + r + 1) - h (a + r))
        ≤ ∑ _r ∈ Finset.range (k - a), (h (k + 1) - h k) := Finset.sum_le_sum fun r hr => by
          rw [Finset.mem_range] at hr
          exact hstep_mono (a + r) k (by omega) (by omega)
      _ = ((k - a : ℕ) : ℚ) * (h (k + 1) - h k) := by simp; ring
  have hright : ((b - k : ℕ) : ℚ) * (h (k + 1) - h k) ≤ h b - h k := by
    rw [htele k b hkb]
    calc ((b - k : ℕ) : ℚ) * (h (k + 1) - h k)
        = ∑ _r ∈ Finset.range (b - k), (h (k + 1) - h k) := by simp; ring
      _ ≤ ∑ r ∈ Finset.range (b - k), (h (k + r + 1) - h (k + r)) :=
          Finset.sum_le_sum fun r hr => by
            rw [Finset.mem_range] at hr
            exact hstep_mono k (k + r) (by omega) (by omega)
  have h1 : ((b - k : ℕ) : ℚ) * (h k - h a) ≤ ((k - a : ℕ) : ℚ) * (h b - h k) := by
    have hka0 : (0 : ℚ) ≤ ((k - a : ℕ) : ℚ) := Nat.cast_nonneg _
    have hbk0 : (0 : ℚ) ≤ ((b - k : ℕ) : ℚ) := Nat.cast_nonneg _
    calc ((b - k : ℕ) : ℚ) * (h k - h a)
        ≤ ((b - k : ℕ) : ℚ) * (((k - a : ℕ) : ℚ) * (h (k + 1) - h k)) :=
          mul_le_mul_of_nonneg_left hleft hbk0
      _ = ((k - a : ℕ) : ℚ) * (((b - k : ℕ) : ℚ) * (h (k + 1) - h k)) := by ring
      _ ≤ ((k - a : ℕ) : ℚ) * (h b - h k) := mul_le_mul_of_nonneg_left hright hka0
  have hba : ((b - a : ℕ) : ℚ) = ((b - k : ℕ) : ℚ) + ((k - a : ℕ) : ℚ) := by
    have : b - a = (b - k) + (k - a) := by omega
    exact_mod_cast this
  rw [hba]
  linarith

/-- **General Ultrametric Newton-Above-Convex Theorem**:
Let `P(T) = ∏_{i : Fin N} (1 - λ_i T)` over an ultrametric field `K` with `‖λ i‖ = pi ^ (ν i : ℝ)`
(`0 < pi < 1`), and let `N_slopes := {ν i}` be its Newton slope multiset.
For ANY convex sequence `h : ℕ → ℚ`, if `∀ k ≤ N, ‖P.coeff k‖ ≤ pi ^ (h k : ℝ)`,
then **`∀ k ≤ N, h k ≤ Stage2HodgeWeights.polygon N_slopes k`**! -/
theorem convex_le_polygon_of_norm_coeff_le {N : ℕ} {pi : ℝ} (hpi0 : 0 < pi) (hpi1 : pi < 1)
    {lam : Fin N → K} {ν : Fin N → ℚ}
    (hnorm : ∀ i : Fin N, ‖lam i‖ = pi ^ (ν i : ℝ))
    {h : ℕ → ℚ}
    (hconv : ∀ j : ℕ, j + 1 < N → h (j + 1) - h j ≤ h (j + 2) - h (j + 1))
    (hcoeff : ∀ k : ℕ, k ≤ N →
      ‖(∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X)).coeff k‖ ≤
        pi ^ (h k : ℝ)) :
    ∀ k : ℕ, k ≤ N → h k ≤ polygon ((Finset.univ : Finset (Fin N)).val.map ν) k := by
  -- Reindex by a permutation `σ` sorting `ν` in non-decreasing order
  set σ : Equiv.Perm (Fin N) := Tuple.sort ν
  set lam' : Fin N → K := lam ∘ σ
  set ν' : Fin N → ℚ := ν ∘ σ
  have hmono : Monotone ν' := Tuple.monotone_sort ν
  have hnorm' : ∀ i : Fin N, ‖lam' i‖ = pi ^ (ν' i : ℝ) := fun i => hnorm (σ i)
  have hprod_eq : ∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam' i) * Polynomial.X) =
      ∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X) :=
    Equiv.prod_comp σ (fun i => (1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X)
  have hS_eq : ((Finset.univ : Finset (Fin N)).val.map ν') =
      ((Finset.univ : Finset (Fin N)).val.map ν) := by
    have hmap : ((Finset.univ : Finset (Fin N)).val.map ν') =
        (((Finset.univ : Finset (Fin N)).val.map σ).map ν) := by
      rw [Multiset.map_map]
    rw [hmap]
    congr 1
    have hbi : (Finset.univ.map σ.toEmbedding : Finset (Fin N)) = Finset.univ := by
      ext x; simp
    have hval := congrArg Finset.val hbi
    simp only [Finset.map_val, Equiv.coe_toEmbedding] at hval
    exact hval
  rw [← hS_eq]
  -- At any break point `k`, h k ≤ polygon S k directly from norm equality
  have hbreak_le : ∀ k ≤ N,
      (k = 0 ∨ k = N ∨ ∀ (h1 : k - 1 < N) (h2 : k < N), ν' ⟨k - 1, h1⟩ < ν' ⟨k, h2⟩) →
      h k ≤ polygon ((Finset.univ : Finset (Fin N)).val.map ν') k := by
    intro k hk hb
    have heq := norm_coeff_prod_one_sub_at_break hpi0 hpi1 hmono hnorm' hk hb
    rw [hprod_eq] at heq
    have hle := hcoeff k hk
    rw [heq] at hle
    have hexp : (h k : ℝ) ≤ (polygon ((Finset.univ : Finset (Fin N)).val.map ν') k : ℝ) := by
      by_contra hlt
      push Not at hlt
      have := Real.rpow_lt_rpow_of_exponent_gt hpi0 hpi1 hlt
      linarith
    exact_mod_cast hexp
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact hbreak_le 0 (Nat.zero_le N) (Or.inl rfl)
  by_cases hkN : k = N
  · subst hkN; exact hbreak_le k le_rfl (Or.inr (Or.inl rfl))
  -- General interior point `0 < k < N`: bracket by flat-segment break points `a < k ≤ b`
  set s : ℚ := ν' ⟨k - 1, by omega⟩ with hsdef
  set Aset : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => ν' i < s)
  set Bset : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => ν' i ≤ s)
  set a : ℕ := Aset.card
  set b : ℕ := Bset.card
  have ha_lt_k : a < k := by
    have hsub : Aset ⊂ Finset.univ.filter (fun i : Fin N => i.val < k) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun i hi => ?_, fun heq => ?_⟩
      · simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_contra hge
        push Not at hge
        have : s ≤ ν' i := hmono (Fin.mk_le_mk.mpr (by omega))
        linarith
      · have hmem : (⟨k - 1, by omega⟩ : Fin N) ∈ Finset.univ.filter (fun i : Fin N => i.val < k) := by
          simp; omega
        rw [← heq] at hmem
        simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and, hsdef] at hmem
        exact lt_irrefl _ hmem
    have hcard_k : (Finset.univ.filter (fun i : Fin N => i.val < k)).card = k := by
      have hbij : (Finset.univ.filter (fun i : Fin N => i.val < k)).card = (Finset.range k).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; simp at hi; exact Finset.mem_range.mpr hi
        · intro _ _ _ _ h; exact Fin.val_injective h
        · intro j hj
          rw [Finset.mem_range] at hj
          exact ⟨⟨j, lt_of_lt_of_le hj hk⟩, by simp [hj], rfl⟩
      rw [hbij, Finset.card_range]
    calc a < (Finset.univ.filter (fun i : Fin N => i.val < k)).card := Finset.card_lt_card hsub
      _ = k := hcard_k
  have hk_le_b : k ≤ b := by
    have hsub : Finset.univ.filter (fun i : Fin N => i.val < k) ⊆ Bset := by
      intro i hi
      simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hmono (Fin.mk_le_mk.mpr (by omega))
    have hcard_k : (Finset.univ.filter (fun i : Fin N => i.val < k)).card = k := by
      have hbij : (Finset.univ.filter (fun i : Fin N => i.val < k)).card = (Finset.range k).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; simp at hi; exact Finset.mem_range.mpr hi
        · intro _ _ _ _ h; exact Fin.val_injective h
        · intro j hj
          rw [Finset.mem_range] at hj
          exact ⟨⟨j, lt_of_lt_of_le hj hk⟩, by simp [hj], rfl⟩
      rw [hbij, Finset.card_range]
    calc k = (Finset.univ.filter (fun i : Fin N => i.val < k)).card := hcard_k.symm
      _ ≤ b := Finset.card_le_card hsub
  have hb_le_N : b ≤ N := by
    calc b ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
      _ = N := Fintype.card_fin N
  -- Characterize Aset and Bset as initial segments `{i | i.val < a}` and `{i | i.val < b}`
  have hA_eq : Aset = Finset.univ.filter (fun i : Fin N => i.val < a) := by
    -- Since ν' is monotone, Aset is downward-closed; every downward-closed subset of Fin N is {i | i < card}
    have hdown : ∀ i j : Fin N, i ≤ j → j ∈ Aset → i ∈ Aset := fun i j hij hj => by
      simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact lt_of_le_of_lt (hmono hij) hj
    have hsub : Aset ⊆ Finset.univ.filter (fun i : Fin N => i.val < a) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hge
      push Not at hge
      have hle_set : Finset.univ.filter (fun i : Fin N => i.val ≤ j.val) ⊆ Aset := fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hdown i j (Fin.mk_le_mk.mpr hi) hj
      have hcard_j : (Finset.univ.filter (fun i : Fin N => i.val ≤ j.val)).card = j.val + 1 := by
        have hbij : (Finset.univ.filter (fun i : Fin N => i.val ≤ j.val)).card =
            (Finset.range (j.val + 1)).card := by
          refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
          · intro i hi; simp at hi; exact Finset.mem_range.mpr (by omega)
          · intro _ _ _ _ h; exact Fin.val_injective h
          · intro r hr
            rw [Finset.mem_range] at hr
            exact ⟨⟨r, lt_of_lt_of_le hr j.isLt⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩
        rw [hbij, Finset.card_range]
      have := Finset.card_le_card hle_set
      rw [hcard_j] at this
      omega
    have hcard_rhs : (Finset.univ.filter (fun i : Fin N => i.val < a)).card = a := by
      have hbij : (Finset.univ.filter (fun i : Fin N => i.val < a)).card = (Finset.range a).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; simp at hi; exact Finset.mem_range.mpr hi
        · intro _ _ _ _ h; exact Fin.val_injective h
        · intro r hr
          rw [Finset.mem_range] at hr
          exact ⟨⟨r, lt_of_lt_of_le hr (by omega)⟩, by simp [hr], rfl⟩
      rw [hbij, Finset.card_range]
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_rhs])
  have hB_eq : Bset = Finset.univ.filter (fun i : Fin N => i.val < b) := by
    have hdown : ∀ i j : Fin N, i ≤ j → j ∈ Bset → i ∈ Bset := fun i j hij hj => by
      simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact le_trans (hmono hij) hj
    have hsub : Bset ⊆ Finset.univ.filter (fun i : Fin N => i.val < b) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hge
      push Not at hge
      have hle_set : Finset.univ.filter (fun i : Fin N => i.val ≤ j.val) ⊆ Bset := fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hdown i j (Fin.mk_le_mk.mpr hi) hj
      have hcard_j : (Finset.univ.filter (fun i : Fin N => i.val ≤ j.val)).card = j.val + 1 := by
        have hbij : (Finset.univ.filter (fun i : Fin N => i.val ≤ j.val)).card =
            (Finset.range (j.val + 1)).card := by
          refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
          · intro i hi; simp at hi; exact Finset.mem_range.mpr (by omega)
          · intro _ _ _ _ h; exact Fin.val_injective h
          · intro r hr
            rw [Finset.mem_range] at hr
            exact ⟨⟨r, lt_of_lt_of_le hr j.isLt⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩
        rw [hbij, Finset.card_range]
      have := Finset.card_le_card hle_set
      rw [hcard_j] at this
      omega
    have hcard_rhs : (Finset.univ.filter (fun i : Fin N => i.val < b)).card = b := by
      have hbij : (Finset.univ.filter (fun i : Fin N => i.val < b)).card = (Finset.range b).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; simp at hi; exact Finset.mem_range.mpr hi
        · intro _ _ _ _ h; exact Fin.val_injective h
        · intro r hr
          rw [Finset.mem_range] at hr
          exact ⟨⟨r, lt_of_lt_of_le hr hb_le_N⟩, by simp [hr], rfl⟩
      rw [hbij, Finset.card_range]
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_rhs])
  -- Both `a` and `b` are break points!
  have ha_le : h a ≤ polygon ((Finset.univ : Finset (Fin N)).val.map ν') a := by
    refine hbreak_le a (by omega) ?_
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · refine Or.inr (Or.inr fun h1 h2 => ?_)
      have hmem1 : (⟨a - 1, h1⟩ : Fin N) ∈ Aset := by rw [hA_eq]; simp; omega
      have hnot2 : (⟨a, h2⟩ : Fin N) ∉ Aset := by rw [hA_eq]; simp
      simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hmem1 hnot2
      linarith
  have hb_le : h b ≤ polygon ((Finset.univ : Finset (Fin N)).val.map ν') b := by
    refine hbreak_le b hb_le_N ?_
    by_cases hbN : b = N
    · exact Or.inr (Or.inl hbN)
    · refine Or.inr (Or.inr fun h1 h2 => ?_)
      have hmem1 : (⟨b - 1, h1⟩ : Fin N) ∈ Bset := by rw [hB_eq]; simp; omega
      have hnot2 : (⟨b, h2⟩ : Fin N) ∉ Bset := by rw [hB_eq]; simp
      simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hmem1 hnot2
      linarith
  -- On `[a, b)`, every slope `ν' i` equals `s`, so `polygon` is linear on `[a, b]`!
  have hflat : ∀ i : Fin N, a ≤ i.val → i.val < b → ν' i = s := by
    intro i hai hib
    have hnotA : i ∉ Aset := by rw [hA_eq]; simp; omega
    have hmemB : i ∈ Bset := by rw [hB_eq]; simp [hib]
    simp only [Aset, Bset, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnotA hmemB
    linarith
  have hpoly_step : ∀ m : ℕ, a ≤ m → m ≤ b →
      polygon ((Finset.univ : Finset (Fin N)).val.map ν') m =
        polygon ((Finset.univ : Finset (Fin N)).val.map ν') a + ((m - a : ℕ) : ℚ) * s := by
    intro m ham hmb
    rw [polygon_of_monotone ν' hmono (by omega), polygon_of_monotone ν' hmono (by omega)]
    have hsplit : Finset.univ.filter (fun i : Fin N => i.val < m) =
        Finset.univ.filter (fun i : Fin N => i.val < a) ∪
          Finset.univ.filter (fun i : Fin N => a ≤ i.val ∧ i.val < m) := by
      ext i; simp; omega
    have hdisj : Disjoint (Finset.univ.filter (fun i : Fin N => i.val < a))
        (Finset.univ.filter (fun i : Fin N => a ≤ i.val ∧ i.val < m)) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp at h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    congr 1
    have hconst : ∑ i ∈ Finset.univ.filter (fun i : Fin N => a ≤ i.val ∧ i.val < m), ν' i =
        ∑ _i ∈ Finset.univ.filter (fun i : Fin N => a ≤ i.val ∧ i.val < m), s :=
      Finset.sum_congr rfl fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hflat i hi.1 (lt_of_lt_of_le hi.2 hmb)
    rw [hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard_seg : (Finset.univ.filter (fun i : Fin N => a ≤ i.val ∧ i.val < m)).card = m - a := by
      have hbij : (Finset.univ.filter (fun i : Fin N => a ≤ i.val ∧ i.val < m)).card =
          (Finset.range (m - a)).card := by
        refine Finset.card_bij (fun i _ => i.val - a) ?_ ?_ ?_
        · intro i hi; simp at hi; exact Finset.mem_range.mpr (by omega)
        · intro i₁ hi₁ i₂ hi₂ heq
          simp at hi₁ hi₂
          exact Fin.ext (by omega)
        · intro r hr
          rw [Finset.mem_range] at hr
          exact ⟨⟨a + r, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, by dsimp; omega⟩
      rw [hbij, Finset.card_range]
    exact_mod_cast hcard_seg
  have hpoly_k := hpoly_step k ha_lt_k.le hk_le_b
  have hpoly_b := hpoly_step b (by omega) le_rfl
  have hlin : ((b - a : ℕ) : ℚ) * polygon ((Finset.univ : Finset (Fin N)).val.map ν') k =
      ((b - k : ℕ) : ℚ) * polygon ((Finset.univ : Finset (Fin N)).val.map ν') a +
        ((k - a : ℕ) : ℚ) * polygon ((Finset.univ : Finset (Fin N)).val.map ν') b := by
    rw [hpoly_k, hpoly_b]
    have hba : ((b - a : ℕ) : ℚ) = ((b - k : ℕ) : ℚ) + ((k - a : ℕ) : ℚ) := by
      have : b - a = (b - k) + (k - a) := by omega
      exact_mod_cast this
    rw [hba]
    ring
  have hchord := discrete_convex_chord hconv ha_lt_k.le hk_le_b hb_le_N
  have hba_pos : (0 : ℚ) < ((b - a : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < b - a)
  have hmul : ((b - a : ℕ) : ℚ) * h k ≤
      ((b - a : ℕ) : ℚ) * polygon ((Finset.univ : Finset (Fin N)).val.map ν') k := by
    rw [hlin]
    exact hchord.trans (add_le_add
      (mul_le_mul_of_nonneg_left ha_le (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left hb_le (Nat.cast_nonneg _)))
  exact le_of_mul_le_mul_left hmul hba_pos

/-- The canonical Dwork Hodge slope multiset `{0, α, 2α, ..., (N-1)α} : Multiset ℚ`. -/
def dworkHodgeSlopes (α : ℚ) (N : ℕ) : Multiset ℚ :=
  (Finset.univ : Finset (Fin N)).val.map (fun i : Fin N => α * (i.val : ℚ))

theorem dworkHodgeSlopes_card (α : ℚ) (N : ℕ) :
    (dworkHodgeSlopes α N).card = N := by
  simp [dworkHodgeSlopes]

/-- Exact closed form for the Dwork Hodge polygon:
`polygon (dworkHodgeSlopes α N) k = α * k * (k - 1) / 2` for `0 ≤ α` and `k ≤ N`. -/
theorem polygon_dworkHodgeSlopes {α : ℚ} (hα : 0 ≤ α) (N : ℕ) {k : ℕ} (hk : k ≤ N) :
    polygon (dworkHodgeSlopes α N) k = α * ((k : ℚ) * ((k : ℚ) - 1) / 2) := by
  have hmono : Monotone (fun i : Fin N => α * (i.val : ℚ)) := fun i j hij =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hα
  unfold dworkHodgeSlopes
  rw [polygon_of_monotone _ hmono hk, ← Finset.mul_sum]
  congr 1
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i : Fin N => i.val < k),
      (i.val : ℚ) = ∑ r ∈ Finset.range k, (r : ℚ) := by
    refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
    · intro i hi; simp at hi; exact Finset.mem_range.mpr hi
    · intro _ _ _ _ h; exact Fin.val_injective h
    · intro r hr
      rw [Finset.mem_range] at hr
      exact ⟨⟨r, lt_of_lt_of_le hr hk⟩, by simp [hr], rfl⟩
    · intro _ _; rfl
  rw [hsum]
  have htri := Finset.sum_range_id_mul_two k
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp
  · have hQ : ((∑ r ∈ Finset.range k, r : ℕ) : ℚ) * 2 = ((k * (k - 1) : ℕ) : ℚ) := by
      exact_mod_cast htri
    rw [Nat.cast_sum, Nat.cast_mul, Nat.cast_sub hkpos, Nat.cast_one] at hQ
    linarith

/-- **Row-Decay Crystalline Frobenius Slope Lower Bound**:
If `A : Matrix (Fin N) (Fin N) K` satisfies pure row decay `‖A i j‖ ≤ ‖(p : K)‖ ^ (α * i)`
(`0 ≤ α : ℚ`, `‖(p : K)‖ < 1`), and `fredholmDet A` splits with rational Frobenius slopes `ν`,
then `Stage2HodgeWeights.polygon (dworkHodgeSlopes α N) k ≤ Stage2HodgeWeights.polygon N_slopes k`
for all `k ≤ N`. -/
theorem rowDecay_le_newtonPolygon [CharZero K] {p N : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {α : ℚ} (hα : 0 ≤ α) {A : Matrix (Fin N) (Fin N) K}
    (hA : ∀ i j : Fin N, ‖A i j‖ ≤ ‖(p : K)‖ ^ ((α : ℝ) * (i.val : ℝ)))
    {lam : Fin N → K} {ν : Fin N → ℚ}
    (hsplit : fredholmDet A = ∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X))
    (hnorm : ∀ i : Fin N, ‖lam i‖ = ‖(p : K)‖ ^ (ν i : ℝ)) :
    ∀ k : ℕ, k ≤ N →
      polygon (dworkHodgeSlopes α N) k ≤
        polygon ((Finset.univ : Finset (Fin N)).val.map ν) k := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  refine convex_le_polygon_of_norm_coeff_le hpi0 hlt hnorm
    (fun j hj => polygon_convex _ (by rwa [dworkHodgeSlopes_card])) fun k hk => ?_
  rw [← hsplit, polygon_dworkHodgeSlopes hα N hk]
  have hbd := norm_coeff_fredholmDet_of_row_decay hpi0 hlt.le (by exact_mod_cast hα) hA k
  refine hbd.trans_eq ?_
  congr 1
  push_cast
  ring

/-- **Unconditional Crystalline Frobenius Slope Lower Bound (Hodge Polygon Below Newton Polygon)**:
Let `A : Matrix (Fin N) (Fin N) K` satisfy the Dwork off-diagonal decay
`‖A i j‖ ≤ ‖(p : K)‖ ^ (c * (p i - j))` (`0 ≤ c : ℚ`, `1 ≤ p`, `‖(p : K)‖ < 1`).
If `fredholmDet A = ∏_{i : Fin N} (1 - λ_i T)` with rational Frobenius slopes `ν_i : ℚ`
(`‖λ i‖ = ‖(p : K)‖ ^ (ν i : ℝ)`), then for EVERY `k ≤ N`:
`Stage2HodgeWeights.polygon (dworkHodgeSlopes (c * (p - 1)) N) k ≤ Stage2HodgeWeights.polygon N_slopes k`. -/
theorem dworkHodgeSlopes_le_newtonPolygon [CharZero K] {p N : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {c : ℚ} (hc : 0 ≤ c) {A : Matrix (Fin N) (Fin N) K}
    (hA : ∀ i j : Fin N, ‖A i j‖ ≤ ‖(p : K)‖ ^ ((c : ℝ) * ((p : ℝ) * (i.val : ℝ) - (j.val : ℝ))))
    {lam : Fin N → K} {ν : Fin N → ℚ}
    (hsplit : fredholmDet A = ∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X))
    (hnorm : ∀ i : Fin N, ‖lam i‖ = ‖(p : K)‖ ^ (ν i : ℝ)) :
    ∀ k : ℕ, k ≤ N →
      polygon (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N) k ≤
        polygon ((Finset.univ : Finset (Fin N)).val.map ν) k := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hpm1 : (0 : ℚ) ≤ (p : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.one_le
    linarith
  have hα : 0 ≤ c * ((p : ℚ) - 1) := mul_nonneg hc hpm1
  have hconv : ∀ j : ℕ, j + 1 < N →
      polygon (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N) (j + 1) -
        polygon (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N) j ≤
      polygon (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N) (j + 2) -
        polygon (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N) (j + 1) := fun j hj => by
    have hj' : j + 1 < (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N).card := by
      rwa [dworkHodgeSlopes_card]
    exact polygon_convex _ hj'
  refine convex_le_polygon_of_norm_coeff_le hpi0 hlt hnorm hconv fun k hk => ?_
  rw [← hsplit, polygon_dworkHodgeSlopes hα N hk]
  have hbd := norm_coeff_fredholmDet_of_dwork_decay hpi0 hlt.le (by exact_mod_cast hc) hp.one_le hA k
  refine hbd.trans_eq ?_
  congr 1
  push_cast
  ring

/-- **Direct Bridge to `Stage2HodgeWeights.PolygonLe` (Arbitrary Hodge Multiset `H`)**:
For ANY Hodge slope multiset `H : Multiset ℚ` of cardinality `N`, if the Fredholm determinant
of `A` splits with Newton slopes `N_slopes`, satisfies the Hodge coefficient bound
`‖(fredholmDet A).coeff k‖ ≤ ‖(p : K)‖ ^ (polygon H k : ℝ)` for all `k ≤ N`, and shares the
determinant endpoint `H.sum = N_slopes.sum`, then **`Stage2HodgeWeights.PolygonLe H N_slopes`**! -/
theorem polygonLe_of_fredholmDet_hodge_bound [CharZero K] {p N : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {H : Multiset ℚ} (hHcard : H.card = N)
    {A : Matrix (Fin N) (Fin N) K}
    {lam : Fin N → K} {ν : Fin N → ℚ}
    (hsplit : fredholmDet A = ∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X))
    (hnorm : ∀ i : Fin N, ‖lam i‖ = ‖(p : K)‖ ^ (ν i : ℝ))
    (hcoeff : ∀ k : ℕ, k ≤ N → ‖(fredholmDet A).coeff k‖ ≤ ‖(p : K)‖ ^ (polygon H k : ℝ))
    (hend : H.sum = ((Finset.univ : Finset (Fin N)).val.map ν).sum) :
    PolygonLe H ((Finset.univ : Finset (Fin N)).val.map ν) := by
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  refine ⟨by simp [hHcard], ?_, hend⟩
  intro k hk
  rw [hHcard] at hk
  refine convex_le_polygon_of_norm_coeff_le hpi0 hlt hnorm
    (fun j hj => polygon_convex H (by rwa [hHcard]))
    (fun m hm => by rw [← hsplit]; exact hcoeff m hm) k hk

/-- **Direct Bridge to `Stage2HodgeWeights.PolygonLe` (Dwork Matrix Decay)**:
When a Dwork-decay matrix `A` has determinant slope matching `dworkHodgeSlopes (c * (p - 1)) N`,
its Newton polygon dominates its Hodge polygon in the exact sense of
`Stage2HodgeWeights.PolygonLe`. -/
theorem polygonLe_of_fredholmDet_dwork_decay [CharZero K] {p N : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {c : ℚ} (hc : 0 ≤ c) {A : Matrix (Fin N) (Fin N) K}
    (hA : ∀ i j : Fin N, ‖A i j‖ ≤ ‖(p : K)‖ ^ ((c : ℝ) * ((p : ℝ) * (i.val : ℝ) - (j.val : ℝ))))
    {lam : Fin N → K} {ν : Fin N → ℚ}
    (hsplit : fredholmDet A = ∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X))
    (hnorm : ∀ i : Fin N, ‖lam i‖ = ‖(p : K)‖ ^ (ν i : ℝ))
    (hend : (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N).sum =
      ((Finset.univ : Finset (Fin N)).val.map ν).sum) :
    PolygonLe (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N) ((Finset.univ : Finset (Fin N)).val.map ν) :=
  ⟨by simp [dworkHodgeSlopes_card],
    fun k hk => dworkHodgeSlopes_le_newtonPolygon hp hlt hc hA hsplit hnorm k
      (by rwa [dworkHodgeSlopes_card] at hk),
    hend⟩

/-- **End-to-End Pipeline from `PAdicChainValuation.WtGe` to `Stage2HodgeWeights.polygon`**:
Given ANY power series `g` satisfying `PAdicChainValuation.WtGe ‖(p : K)‖ (-c) 0` (`0 ≤ c : ℚ`),
its Dwork operator `ψ_g = U_p ∘ M_g` simultaneously satisfies:
1. Overconvergent contraction `‖ψ_g f‖_{b^p} ≤ ‖f‖_b` at `b = ‖(p : K)‖ ^ (-c)`;
2. Fredholm determinant decay `‖(fredholmDet A_N).coeff m‖ ≤ ‖p‖ ^ (c (p - 1) m (m - 1) / 2)`;
3. Unconditional Newton-above-Hodge crystalline Frobenius slope lower bound
   `Stage2HodgeWeights.polygon (dworkHodgeSlopes (c * (p - 1)) N) k ≤ Stage2HodgeWeights.polygon N_slopes k`. -/
theorem wtGe_dworkOp_newton_polygon_bound [CharZero K] {p N : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {c : ℚ} (hc : 0 ≤ c) {g : PowerSeries K}
    (hg : WtGe ‖(p : K)‖ (fun _ : Unit => -(c : ℝ)) 0 (g : MvPowerSeries Unit K)) :
    let b := ‖(p : K)‖ ^ (-(c : ℝ))
    let A : Matrix (Fin N) (Fin N) K := fun i j => dworkMatrix p g i.val j.val
    (∀ f : PowerSeries K, IsOverconvergent b f →
      overconvNorm (b ^ p) (dworkOp p g f) ≤ overconvNorm b f) ∧
    (∀ m : ℕ, ‖(fredholmDet A).coeff m‖ ≤
      ‖(p : K)‖ ^ ((c : ℝ) * ((p : ℝ) - 1) * ((m : ℝ) * ((m : ℝ) - 1) / 2))) ∧
    (∀ (lam : Fin N → K) (ν : Fin N → ℚ),
      fredholmDet A = ∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X) →
      (∀ i : Fin N, ‖lam i‖ = ‖(p : K)‖ ^ (ν i : ℝ)) →
      ∀ k : ℕ, k ≤ N →
        polygon (dworkHodgeSlopes (c * ((p : ℚ) - 1)) N) k ≤
          polygon ((Finset.univ : Finset (Fin N)).val.map ν) k) := by
  intro b A
  have hpi0 : 0 < ‖(p : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hb0 : 0 ≤ b := Real.rpow_nonneg hpi0.le _
  have hgov := (wtGe_iff_overconvNorm_le hp g).mp hg
  rw [Real.rpow_zero] at hgov
  have hA : ∀ i j : Fin N,
      ‖A i j‖ ≤ ‖(p : K)‖ ^ ((c : ℝ) * ((p : ℝ) * (i.val : ℝ) - (j.val : ℝ))) := fun i j => by
    simpa using norm_dworkMatrix_le hp hg i.val j.val
  refine ⟨fun f hf => ?_, fun m => ?_, fun lam ν hsplit hnorm => ?_⟩
  · calc overconvNorm (b ^ p) (dworkOp p g f)
        ≤ overconvNorm b g * overconvNorm b f := overconvNorm_dworkOp_le hb0 p hgov.1 hf
      _ ≤ 1 * overconvNorm b f :=
          mul_le_mul_of_nonneg_right hgov.2 (overconvNorm_nonneg hb0 f)
      _ = overconvNorm b f := one_mul _
  · exact norm_coeff_fredholmDet_of_dwork_decay hpi0 hlt.le (by exact_mod_cast hc) hp.one_le hA m
  · exact dworkHodgeSlopes_le_newtonPolygon hp hlt hc hA hsplit hnorm

/-- **End-to-End Crystalline Frobenius Slope Lower Bound for Dwork's Splitting Function `θ(X)`**:
Directly chaining `Stage2DworkExp.dworkSplitting_wtGe` into `wtGe_dworkOp_newton_polygon_bound`,
every `N × N` truncation of `ψ_θ = U_p ∘ M_θ` satisfies the explicit Dwork Newton polygon
lower bound with slope quantum `α_p = (p - 1)^2 / p^2`:
`polygon (dworkHodgeSlopes (((p - 1)^2 : ℚ) / p^2) N) k ≤ polygon N_slopes k` for all `k ≤ N`! -/
theorem dworkSplitting_newton_polygon_bound [CharZero K] {p N : ℕ} (hp : p.Prime)
    (hlt : ‖(p : K)‖ < 1) {ϖ : K} (hϖ : ϖ ^ (p - 1) = -(p : K))
    {lam : Fin N → K} {ν : Fin N → ℚ}
    (hsplit : fredholmDet (fun i j : Fin N => dworkMatrix p (dworkSplitting ϖ p) i.val j.val) =
      ∏ i : Fin N, ((1 : Polynomial K) - Polynomial.C (lam i) * Polynomial.X))
    (hnorm : ∀ i : Fin N, ‖lam i‖ = ‖(p : K)‖ ^ (ν i : ℝ)) :
    ∀ k : ℕ, k ≤ N →
      polygon (dworkHodgeSlopes (((p : ℚ) - 1) ^ 2 / (p : ℚ) ^ 2) N) k ≤
        polygon ((Finset.univ : Finset (Fin N)).val.map ν) k := by
  set c : ℚ := ((p : ℚ) - 1) / (p : ℚ) ^ 2 with hcdef
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (sq_nonneg _)
  have hg : WtGe ‖(p : K)‖ (fun _ : Unit => -(c : ℝ)) 0
      (dworkSplitting ϖ p : MvPowerSeries Unit K) := by
    have h := dworkSplitting_wtGe hp hlt hϖ
    have hcast : (c : ℝ) = ((p : ℝ) - 1) / (p : ℝ) ^ 2 := by
      rw [hcdef]; push_cast; rfl
    rwa [hcast]
  have hmain := (wtGe_dworkOp_newton_polygon_bound (N := N) hp hlt hc0 hg).2.2 lam ν hsplit hnorm
  have hslope_eq : c * ((p : ℚ) - 1) = ((p : ℚ) - 1) ^ 2 / (p : ℚ) ^ 2 := by
    rw [hcdef]; ring
  rwa [hslope_eq] at hmain

end NewtonPolygonBridge

end

end RHDirect.Stage3DworkFrobenius
