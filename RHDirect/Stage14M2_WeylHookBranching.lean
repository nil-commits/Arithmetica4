import RHDirect.Stage12SchurWeylLattices
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# RHDirect.Stage14M2_WeylHookBranching

Field-2 Package M2 Wave 1 (4 of 6) — unconditional, zero-`sorry`, zero-custom-`axiom`,
zero-`native_decide` Lean 4 formalization of:

1. **Dominant Weights (`DomWeight`), Interlacing (`Interlace`), Capelli Capacity (`cCap`),
   and Weyl Dimension (`dimV`)**:
   - Integer dominant weights `DomWeight N`, determinant shift `detShift`, normalized partition
     `toPartition : Partition N`, weight shifting `shiftW`, spread `spread`,
   - Interlacing identities (`interlace_identities`, `interlace_telescope`, `constituent_range`),
     Capelli eigenvalue polynomial `capEig`, capacity constant `cCap`, vanishing off-diagonal
     (`cap_kills`), truncated defect bound (`truncated_defect_bound`), and exact non-vanishing
     & polynomial-power bound (`capacity_constant_bound`),
   - Exact shift-invariance `cCap_shift`, `dimV_shift`, exact bridge `dimV_eq_weylDim` to
     `Stage12SchurWeylLattices.Partition.weylDim`, and `branching_constant_bound`.

2. **Exact Hook–Vandermonde Identity & Explicit Stirling Bounds (`hook_length_stirling_bound`)**:
   - Exact global hook–Vandermonde–factorial identity
     `lam.hookProd * ∏_{i < j} (ℓ_i - ℓ_j) = ∏_i (ℓ_i)!`,
   - Exact factorial-Vandermonde sandwich (`HookLengthFactorialBound` / `hook_length_factorial_bound`),
   - Unconditional explicit Stirling bounds on `log (n!)` proved from first principles:
     `n log n - n + 1 ≤ log (n!) ≤ (n + 1) log (n + 1) - n` and
     `log (n!) ≤ (n + 1) log n - n + 1` (`n ≥ 1`),
   - **`hook_length_stirling_bound`**: explicit Stirling upper & lower bounds on `log (hookProd lam)`
     and the sharp polynomial-degree upper bound `weylDim lam ≤ (lam_0 + r)^(r*(r-1)/2)`
     (plus exact shifted-factorial denominator improvement).

3. **Concrete `SchurFunctorColumnLat` & Column-Tensor Branching Slopes**:
   - Concrete bundled Schur-functor column lattice `SchurFunctorColumnLat` over any
     `ConcreteEuclideanLat`, with canonical instantiations on `columnTensorLat`, arbitrary-rank
     `CMHermLattice d r`, and general totally-complex `NumberFieldHLat K`,
   - Exact column rank, exact column slope, and Stirling-sharpened `muMin` / `slope` lower bounds
     ready for M2 Wave 2 `ColumnExactSlope` and Wave 3 `AutomorphicLatM`.

4. **Multivariable Polynomial Fock Space, Weighted Cauchy–Binet & `standard_slope_lower`**:
   - Rational and complex multivariable Fock inner products `fockQ` / `fockC` with full
     sesquilinearity, positivity, and Cauchy–Schwarz inequality,
   - Unconditional multinomial factorization lower bound (`monomial_factorization_lower`),
   - Weighted Cauchy–Binet Gram determinant identity (`factorial_mul_det_sq`) and integer-matrix
     weighted Gram determinant lower bound (`det_gram_weighted_ge_pow_of_int`),
   - Concrete leading principal minors `lpMinor` and highest-weight polynomials `hwPoly` with
     `hwPoly_ne_zero` and `0 < fockQ (hwPoly ℚ N ν) (hwPoly ℚ N ν)`,
   - **`nabla_gram_lower_bound`** and **`standard_slope_lower`** (`PI.StdSlopeLow`) giving
     `-((∑ s, ν s) * log N + log (cNu ν)) ≤ μ` unconditionally!

5. **Fock Adjoint Existence, `branching_normalised_of_adjoint` & `branching_link_family_normalised`**:
   - Unconditional Gram–Schmidt construction of Fock-space adjoints (`fock_adjoint_exists`) on
     any finite-dimensional subspace `V ≤ MvPolynomial σ ℂ`,
   - **`branching_normalised_of_adjoint`**: rescales the Fock adjoint by `h_sg / h_lt`, proving
     non-vanishing, integrality, `GL_n`-equivariance, and the sharp normalized Fock-norm estimate,
   - **`branching_integral_shift`** & **`branching_integral_of_normalised`**: removes the
     `lt.w (Fin.last n) = 0` normalization via `shiftW`,
   - **`branching_link_family_normalised`** & **`branching_family_of_adjoint`**: lifts the
     normalized adjoint branching theorem to arbitrary parameter families with the exponential
     capacity-spread + `log (dimV)` bound.
-/

noncomputable section

open Module Submodule Finset Real Matrix MvPolynomial
open RHDirect.ArakelovCovolume (rk covol degAr slope muMax)
open RHDirect.Stage4ArakelovBost (muMin muMin_le_slope_le_muMax)
open RHDirect.Stage11MoriwakiCovolume (arithDeg scaleLat scaleLat_invariants slope_scaleLat)
open RHDirect.Stage12SchurWeylLattices
open scoped BigOperators Matrix ComplexOrder

namespace RHDirect.Stage14M2_WeylHookBranching

/-! ## Section 1: Dominant Weights, Interlacing, Capelli Capacity & Weyl Dimension -/

section DominantWeightsAndCapacity

/-- Dominant integer weight `w_0 ≥ w_1 ≥ ⋯ ≥ w_{N-1}` for `GL_N` / `U(N)`. -/
structure DomWeight (N : ℕ) where
  w : Fin N → ℤ
  anti : Antitone w

namespace DomWeight

/-- Determinant twist `detShift = w_{N-1}` (or `0` when `N = 0`). -/
def detShift {N : ℕ} (lam : DomWeight N) : ℤ :=
  if h : 0 < N then lam.w ⟨N - 1, by omega⟩ else 0

/-- Shifted non-negative coordinates `natW i = (w_i - detShift).toNat`. -/
def natW {N : ℕ} (lam : DomWeight N) (i : Fin N) : ℕ :=
  (lam.w i - lam.detShift).toNat

theorem detShift_le {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    lam.detShift ≤ lam.w i := by
  unfold detShift
  rw [dif_pos (Fin.pos i)]
  exact lam.anti (by rw [Fin.le_def]; exact Nat.le_sub_one_of_lt i.2)

theorem natW_cast {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    (lam.natW i : ℤ) = lam.w i - lam.detShift := by
  unfold natW
  have h := lam.detShift_le i
  omega

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have h1 := lam.anti hij
  unfold natW
  omega

/-- Associated `Partition N` (normalized by subtracting `detShift`). -/
def toPartition {N : ℕ} (lam : DomWeight N) : Partition N where
  parts := lam.natW
  anti := lam.natW_anti

/-- Constant-shift weight `(shiftW lam c).w i = lam.w i + c`. -/
def shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => lam.w i + c
  anti := fun _ _ h => by dsimp only; linarith [lam.anti h]

@[simp] theorem shiftW_w {N : ℕ} (lam : DomWeight N) (c : ℤ) :
    (lam.shiftW c).w = fun i => lam.w i + c := rfl

theorem shiftW_shiftW_neg {N : ℕ} (lam : DomWeight N) (c : ℤ) :
    (lam.shiftW (-c)).shiftW c = lam := by
  cases lam with
  | mk w anti =>
    simp only [shiftW, mk.injEq]
    funext i
    ring

theorem detShift_shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) (hN : 0 < N) :
    (lam.shiftW c).detShift = lam.detShift + c := by
  unfold detShift
  rw [dif_pos hN, dif_pos hN]
  rfl

theorem natW_shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) :
    (lam.shiftW c).natW = lam.natW := by
  funext i
  unfold natW
  rw [detShift_shiftW lam c (Fin.pos i), shiftW_w]
  congr 1
  ring

theorem toPartition_shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) :
    (lam.shiftW c).toPartition = lam.toPartition := by
  cases lam with
  | mk w anti =>
    unfold toPartition
    congr 1
    exact natW_shiftW ⟨w, anti⟩ c

theorem detShift_last {n : ℕ} (lt : DomWeight (n + 1)) (h0 : lt.w (Fin.last n) = 0) :
    lt.detShift = 0 := by
  unfold detShift
  rw [dif_pos (Nat.succ_pos n)]
  have hlast : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [hlast, h0]

theorem nonneg_of_last_zero {n : ℕ} (lt : DomWeight (n + 1)) (h0 : lt.w (Fin.last n) = 0)
    (i : Fin (n + 1)) : 0 ≤ lt.w i := by
  have := lt.anti (Fin.le_last i)
  omega

/-- Dominant weight spread `w_0 - w_{N-1} + N` (or `1` when `N = 0`). -/
def spread {N : ℕ} (lam : DomWeight N) : ℤ :=
  if h : 0 < N then lam.w ⟨0, h⟩ - lam.w ⟨N - 1, by omega⟩ + (N : ℤ) else 1

theorem spread_eq_succ {n : ℕ} (lt : DomWeight (n + 1)) :
    lt.spread = lt.w 0 - lt.w (Fin.last n) + ((n : ℤ) + 1) := by
  unfold spread
  rw [dif_pos (Nat.succ_pos n)]
  have hlast : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [hlast]
  push_cast
  rfl

theorem spread_pos {N : ℕ} (lam : DomWeight N) : 0 < lam.spread := by
  unfold spread
  split_ifs with h
  · have hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w ⟨0, h⟩ :=
      lam.anti (by rw [Fin.le_def]; exact Nat.zero_le _)
    omega
  · norm_num

theorem spread_shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) :
    (lam.shiftW c).spread = lam.spread := by
  unfold spread
  split_ifs with h
  · simp only [shiftW_w]; ring
  · rfl

end DomWeight

/-- Branching interlacing condition `lt_{i+1} ≤ sg_i ≤ lt_i` for `U(n+1) ↓ U(n)`. -/
def Interlace {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, lt.w i.succ ≤ sg.w i ∧ sg.w i ≤ lt.w i.castSucc

theorem interlace_shift {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (c : ℤ)
    (hI : Interlace lt sg) : Interlace (lt.shiftW c) (sg.shiftW c) := by
  intro i
  obtain ⟨h1, h2⟩ := hI i
  simp only [DomWeight.shiftW_w]
  exact ⟨by omega, by omega⟩

/-- Non-negative coordinates `sgNat sg i = (sg.w i).toNat` when `lt_{last} = 0`. -/
def sgNat {n : ℕ} (sg : DomWeight n) : Fin n → ℕ :=
  fun i => (sg.w i).toNat

/-- Restricted non-negative top coordinates `lamNat lt i = lt.natW i.castSucc`. -/
def lamNat {n : ℕ} (lt : DomWeight (n + 1)) : Fin n → ℕ :=
  fun i => lt.natW i.castSucc

theorem sg_nonneg_of_interlace {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (h0 : lt.w (Fin.last n) = 0) (hI : Interlace lt sg) (i : Fin n) : 0 ≤ sg.w i := by
  have h1 := (hI i).1
  have h2 := lt.nonneg_of_last_zero h0 i.succ
  omega

theorem sgNat_cast_of_interlace {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (h0 : lt.w (Fin.last n) = 0) (hI : Interlace lt sg) :
    (fun i => (sgNat sg i : ℤ)) = sg.w := by
  funext i
  unfold sgNat
  have := sg_nonneg_of_interlace lt sg h0 hI i
  omega

theorem detShift_nonneg_of_interlace {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (h0 : lt.w (Fin.last n) = 0) (hI : Interlace lt sg) : 0 ≤ sg.detShift := by
  unfold DomWeight.detShift
  split_ifs with h
  · exact sg_nonneg_of_interlace lt sg h0 hI _
  · exact le_rfl

theorem sgNat_eq_natW_add_detShift {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (h0 : lt.w (Fin.last n) = 0) (hI : Interlace lt sg) :
    sgNat sg = fun i => sg.natW i + sg.detShift.toNat := by
  funext i
  have h1 := sg_nonneg_of_interlace lt sg h0 hI i
  have h2 := detShift_nonneg_of_interlace lt sg h0 hI
  have h3 := sg.detShift_le i
  unfold sgNat DomWeight.natW
  omega

/-- Interlacing base weight difference `d0(lam, sg) = ∑_{i < n} (sg_i - lam_{i+1})`. -/
def d0 {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, (sg i - lam i.succ)

/-- Truncated interlacing length sum `d1(lam, sg) = ∑_{i < n} min (lam_i - lam_{i+1}) (d0 lam sg)`. -/
def d1 {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, min (lam i.castSucc - lam i.succ) (d0 lam sg)

/-- Branching degree `degP lt sg = ∑ lt - ∑ sg`. -/
def degP {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) : ℤ :=
  (∑ i : Fin (n + 1), lt.w i) - ∑ i : Fin n, sg.w i

/-- Adjacent step `lenP lt i = lt_i - lt_{i+1}`. -/
def lenP {n : ℕ} (lt : DomWeight (n + 1)) (i : Fin n) : ℤ :=
  lt.w i.castSucc - lt.w i.succ

/-- Permitted constituent interval `rset lam sg i = [lam_{i+1}, min (lam_i, lam_{i+1} + d0)]`. -/
def rset {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam i.succ) (min (lam i.castSucc) (lam i.succ + d0 lam sg))

/-- Capelli-Lagrange eigenvalue product `capEig lam sg mu`. -/
def capEig {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg mu : Fin n → ℤ) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (rset lam sg i).erase (sg i), ∏ j : Fin n, ((v - (i : ℤ)) - (mu j - (j : ℤ)))

/-- Diagonal Capelli capacity constant `cCap lam sg = capEig lam sg sg`. -/
def cCap {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ :=
  capEig lam sg sg

theorem d0_shift {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (c : ℤ) :
    d0 (fun i => lam i + c) (fun i => sg i + c) = d0 lam sg := by
  unfold d0
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem d1_shift {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (c : ℤ) :
    d1 (fun i => lam i + c) (fun i => sg i + c) = d1 lam sg := by
  unfold d1
  rw [d0_shift]
  refine Finset.sum_congr rfl fun _ _ => ?_
  congr 1; ring

theorem degP_shiftW {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (c : ℤ) :
    degP (lt.shiftW c) (sg.shiftW c) = degP lt sg + c := by
  unfold degP
  simp only [DomWeight.shiftW_w, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  ring

theorem degP_eq_sum_sub_of_last_zero {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (h0 : lt.w (Fin.last n) = 0) (hI : Interlace lt sg) :
    degP lt sg = ((∑ i : Fin n, (lamNat lt i - sgNat sg i) : ℕ) : ℤ) := by
  unfold degP
  rw [Fin.sum_univ_castSucc, h0, add_zero, ← Finset.sum_sub_distrib, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (lamNat lt i : ℤ) = lt.w i.castSucc := by
    unfold lamNat
    rw [lt.natW_cast i.castSucc, lt.detShift_last h0, sub_zero]
  have h2 : (sgNat sg i : ℤ) = sg.w i := congrFun (sgNat_cast_of_interlace lt sg h0 hI) i
  have hle : sgNat sg i ≤ lamNat lt i := by
    have := (hI i).2
    omega
  rw [Nat.cast_sub hle, h1, h2]

theorem cCap_shift {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (c : ℤ) :
    cCap (fun i => lam i + c) (fun i => sg i + c) = cCap lam sg := by
  unfold cCap capEig
  refine Finset.prod_congr rfl fun i _ => ?_
  refine Finset.prod_nbij' (fun v => v - c) (fun v => v + c) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [rset, d0_shift, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢
    omega
  · intro v hv
    simp only [rset, d0_shift, Finset.mem_erase, Finset.mem_Icc, le_min_iff] at hv ⊢
    omega
  · intro v _; ring
  · intro v _; ring
  · intro v _
    exact Finset.prod_congr rfl fun j _ => by ring

/-- Exact interlacing identities (`InterlaceIdent`). -/
theorem interlace_identities {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (hI : Interlace lt sg) :
    degP lt sg = lt.w 0 - d0 lt.w sg.w ∧
    (∑ i : Fin n, (lt.w i.castSucc - sg.w i)) = lt.w 0 - lt.w (Fin.last n) - d0 lt.w sg.w ∧
    0 ≤ d0 lt.w sg.w ∧
    0 ≤ d1 lt.w sg.w ∧
    (∀ i : Fin n, sg.w i ∈ rset lt.w sg.w i) ∧
    (∀ i : Fin n, (((rset lt.w sg.w i).erase (sg.w i)).card : ℤ) =
      min (lenP lt i) (d0 lt.w sg.w)) := by
  have hd0_nonneg : 0 ≤ d0 lt.w sg.w :=
    Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hI i).1
  have hsingle : ∀ i : Fin n, sg.w i - lt.w i.succ ≤ d0 lt.w sg.w := fun i =>
    Finset.single_le_sum (fun k _ => sub_nonneg.mpr (hI k).1) (Finset.mem_univ i)
  have hsum_succ : (∑ i : Fin (n + 1), lt.w i) = lt.w 0 + ∑ i : Fin n, lt.w i.succ :=
    Fin.sum_univ_succ lt.w
  have hsum_cast : (∑ i : Fin (n + 1), lt.w i) = (∑ i : Fin n, lt.w i.castSucc) + lt.w (Fin.last n) :=
    Fin.sum_univ_castSucc lt.w
  have hdeg : degP lt sg = lt.w 0 - d0 lt.w sg.w := by
    unfold degP d0
    rw [hsum_succ, Finset.sum_sub_distrib]
    ring
  have hdiff : (∑ i : Fin n, (lt.w i.castSucc - sg.w i)) =
      lt.w 0 - lt.w (Fin.last n) - d0 lt.w sg.w := by
    unfold d0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linarith
  have hd1_nonneg : 0 ≤ d1 lt.w sg.w :=
    Finset.sum_nonneg fun i _ => le_min (by linarith [(hI i).1, (hI i).2]) hd0_nonneg
  have hmem : ∀ i : Fin n, sg.w i ∈ rset lt.w sg.w i := fun i => by
    unfold rset
    rw [Finset.mem_Icc]
    exact ⟨(hI i).1, le_min (hI i).2 (by linarith [hsingle i])⟩
  have hcard : ∀ i : Fin n, (((rset lt.w sg.w i).erase (sg.w i)).card : ℤ) =
      min (lenP lt i) (d0 lt.w sg.w) := fun i => by
    rw [Finset.card_erase_of_mem (hmem i)]
    unfold rset lenP
    rw [Int.card_Icc]
    have h1 := (hI i).1
    have h2 := (hI i).2
    have h3 := hsingle i
    omega
  exact ⟨hdeg, hdiff, hd0_nonneg, hd1_nonneg, hmem, hcard⟩

/-- Off-diagonal Capelli vanishing (`CapKills`): `mu ≠ sg` in `rset` implies `capEig lt sg mu = 0`. -/
theorem cap_kills {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg mu : Fin n → ℤ)
    (hmu : ∀ i : Fin n, mu i ∈ rset lam sg i) (hne : mu ≠ sg) :
    capEig lam sg mu = 0 := by
  have hex : ∃ i : Fin n, mu i ≠ sg i := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨i, hi⟩ := hex
  unfold capEig
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmu i⟩) ?_
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  ring

/-- Truncated defect bound (`TruncatedDefectBound`): for any `I ⊆ Fin n` with `|I| ≤ 3`,
`d1 lt sg ≤ 3 * d0 lt sg + ∑_{i ∉ I} lenP lt i`. -/
theorem truncated_defect_bound {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (hI : Interlace lt sg) (I : Finset (Fin n)) (hcard : I.card ≤ 3) :
    d1 lt.w sg.w ≤ 3 * d0 lt.w sg.w + ∑ i ∈ Iᶜ, lenP lt i := by
  have hd0 : 0 ≤ d0 lt.w sg.w := (interlace_identities lt sg hI).2.2.1
  unfold d1 lenP
  rw [← Finset.sum_add_sum_compl I]
  have h1 : ∑ i ∈ I, min (lt.w i.castSucc - lt.w i.succ) (d0 lt.w sg.w) ≤ 3 * d0 lt.w sg.w := by
    calc ∑ i ∈ I, min (lt.w i.castSucc - lt.w i.succ) (d0 lt.w sg.w)
        ≤ ∑ _i ∈ I, d0 lt.w sg.w := Finset.sum_le_sum fun _ _ => min_le_right _ _
      _ = (I.card : ℤ) * d0 lt.w sg.w := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * d0 lt.w sg.w := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hd0
  have h2 : ∑ i ∈ Iᶜ, min (lt.w i.castSucc - lt.w i.succ) (d0 lt.w sg.w) ≤
      ∑ i ∈ Iᶜ, (lt.w i.castSucc - lt.w i.succ) :=
    Finset.sum_le_sum fun _ _ => min_le_left _ _
  linarith

private lemma cap_factor_ne_and_abs_le {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (hI : Interlace lt sg) (i j : Fin n) {v : ℤ} (hv : v ∈ (rset lt.w sg.w i).erase (sg.w i)) :
    ((v - (i : ℤ)) - (sg.w j - (j : ℤ))) ≠ 0 ∧
    |((v - (i : ℤ)) - (sg.w j - (j : ℤ)))| ≤ lt.w 0 - lt.w (Fin.last n) + (n : ℤ) - 1 := by
  have hne : v ≠ sg.w i := (Finset.mem_erase.mp hv).1
  have hv_icc : lt.w i.succ ≤ v ∧ v ≤ min (lt.w i.castSucc) (lt.w i.succ + d0 lt.w sg.w) :=
    Finset.mem_Icc.mp (Finset.mem_erase.mp hv).2
  have hv_lo : lt.w i.succ ≤ v := hv_icc.1
  have hv_hi : v ≤ lt.w i.castSucc := hv_icc.2.trans (min_le_left _ _)
  have h0_ge_i : lt.w i.castSucc ≤ lt.w 0 := lt.anti (Fin.zero_le _)
  have h0_ge_j : lt.w j.castSucc ≤ lt.w 0 := lt.anti (Fin.zero_le _)
  have hlast_le_i : lt.w (Fin.last n) ≤ lt.w i.succ := lt.anti (Fin.le_last _)
  have hlast_le_j : lt.w (Fin.last n) ≤ lt.w j.succ := lt.anti (Fin.le_last _)
  have hsj_lo : lt.w j.succ ≤ sg.w j := (hI j).1
  have hsj_hi : sg.w j ≤ lt.w j.castSucc := (hI j).2
  have hi_lt : (i : ℕ) < n := i.2
  have hj_lt : (j : ℕ) < n := j.2
  constructor
  · intro heq
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with hji | hji | hji
    · have h3 : lt.w i.castSucc ≤ lt.w j.succ :=
        lt.anti (Fin.le_def.mpr (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
      omega
    · have hij : j = i := Fin.ext hji
      subst hij
      exact hne (by omega)
    · have h3 : lt.w j.castSucc ≤ lt.w i.succ :=
        lt.anti (Fin.le_def.mpr (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
      omega
  · rw [abs_le]
    constructor <;> omega

/-- **Unconditional Capelli Capacity Constant Bound (`capacity_constant_bound`)**:
for any interlacing pair `(lt, sg)`:
1. `cCap lt.w sg.w ≠ 0`,
2. `|cCap lt.w sg.w| ≤ (lt.w 0 - lt.w (Fin.last n) + n - 1) ^ (n * (d1 lt.w sg.w).toNat)`. -/
theorem capacity_constant_bound {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (hI : Interlace lt sg) :
    cCap lt.w sg.w ≠ 0 ∧
    |cCap lt.w sg.w| ≤
      (lt.w 0 - lt.w (Fin.last n) + (n : ℤ) - 1) ^ (n * (d1 lt.w sg.w).toNat) := by
  obtain ⟨_, _, hd0nn, hd1nn, _, hcard⟩ := interlace_identities lt sg hI
  have hsum : ∑ i : Fin n, ((rset lt.w sg.w i).erase (sg.w i)).card = (d1 lt.w sg.w).toNat := by
    have hZ : ((∑ i : Fin n, ((rset lt.w sg.w i).erase (sg.w i)).card : ℕ) : ℤ) =
        (((d1 lt.w sg.w).toNat : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Int.toNat_of_nonneg hd1nn]
      unfold d1
      exact Finset.sum_congr rfl fun i _ => hcard i
    exact Nat.cast_injective hZ
  constructor
  · unfold cCap capEig
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro v hv
    rw [Finset.prod_ne_zero_iff]; intro j _
    exact (cap_factor_ne_and_abs_le lt sg hI i j hv).1
  · unfold cCap capEig
    simp only [Finset.abs_prod]
    set B : ℤ := lt.w 0 - lt.w (Fin.last n) + (n : ℤ) - 1
    calc ∏ i : Fin n, ∏ v ∈ (rset lt.w sg.w i).erase (sg.w i), ∏ j : Fin n,
            |((v - (i : ℤ)) - (sg.w j - (j : ℤ)))|
        ≤ ∏ i : Fin n, ∏ v ∈ (rset lt.w sg.w i).erase (sg.w i), ∏ _j : Fin n, B := by
          refine Finset.prod_le_prod
            (fun _ _ => Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
            fun i _ => Finset.prod_le_prod
              (fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
              fun v hv => Finset.prod_le_prod
                (fun _ _ => abs_nonneg _)
                fun j _ => (cap_factor_ne_and_abs_le lt sg hI i j hv).2
      _ = ∏ i : Fin n, (B ^ n) ^ ((rset lt.w sg.w i).erase (sg.w i)).card := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (B ^ n) ^ (∑ i : Fin n, ((rset lt.w sg.w i).erase (sg.w i)).card) := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = B ^ (n * (d1 lt.w sg.w).toNat) := by
          rw [hsum, ← pow_mul]

/-- Weyl dimension formula `dimV w` for an integer dominant weight `w : Fin N → ℤ`. -/
def dimV {N : ℕ} (w : Fin N → ℤ) : ℝ :=
  ∏ p ∈ Partition.pairsLt N,
    ((w p.1 - w p.2 + (p.2.1 : ℤ) - (p.1.1 : ℤ) : ℤ) : ℝ) / ((p.2.1 - p.1.1 : ℕ) : ℝ)

theorem dimV_shift {N : ℕ} (w : Fin N → ℤ) (c : ℤ) :
    dimV (fun i => w i + c) = dimV w := by
  unfold dimV
  refine Finset.prod_congr rfl fun p _ => ?_
  congr 2
  ring

/-- Exact identification `dimV lam.w = lam.toPartition.weylDim` bridging to `Stage12SchurWeylLattices`. -/
theorem dimV_eq_weylDim {N : ℕ} (lam : DomWeight N) :
    dimV lam.w = lam.toPartition.weylDim := by
  unfold dimV Partition.weylDim
  refine Finset.prod_congr rfl fun p hp => ?_
  congr 1
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hlt_val : p.1.1 < p.2.1 := hlt
  have h1 : lam.toPartition.shiftedPart p.1 = lam.natW p.1 + (N - 1 - p.1.1) := rfl
  have h2 : lam.toPartition.shiftedPart p.2 = lam.natW p.2 + (N - 1 - p.2.1) := rfl
  have hanti : lam.natW p.2 ≤ lam.natW p.1 := lam.natW_anti hlt.le
  have hge : lam.toPartition.shiftedPart p.2 ≤ lam.toPartition.shiftedPart p.1 :=
    (lam.toPartition.shiftedPart_strictAnti hlt).le
  have hc1 := lam.natW_cast p.1
  have hc2 := lam.natW_cast p.2
  have hp1 : p.1.1 < N := p.1.2
  have hp2 : p.2.1 < N := p.2.2
  have hZ : ((lam.toPartition.shiftedPart p.1 - lam.toPartition.shiftedPart p.2 : ℕ) : ℤ) =
      lam.w p.1 - lam.w p.2 + (p.2.1 : ℤ) - (p.1.1 : ℤ) := by
    rw [Nat.cast_sub hge, h1, h2]
    omega
  exact_mod_cast hZ.symm

theorem dimV_pos {N : ℕ} (lam : DomWeight N) : 0 < dimV lam.w := by
  rw [dimV_eq_weylDim]
  exact lam.toPartition.weylDim_pos

/-- **Exponential Branching Constant Bound (`branching_constant_bound`)**:
`(cCap lt sg)^2 * dimV lt ≤ exp(2 n * log(spread lt) * d1(lt, sg) + log(dimV lt))`. -/
theorem branching_constant_bound {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (hI : Interlace lt sg) :
    (((cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * dimV lt.w ≤
      Real.exp (2 * (n : ℝ) * Real.log (lt.spread : ℝ) *
          (∑ i : Fin n, (min (lenP lt i) (d0 lt.w sg.w) : ℝ)) +
        Real.log (dimV lt.w)) := by
  obtain ⟨_, hc⟩ := capacity_constant_bound lt sg hI
  have hd1nn : 0 ≤ d1 lt.w sg.w := (interlace_identities lt sg hI).2.2.2.1
  have hsum : (∑ i : Fin n, (min (lenP lt i) (d0 lt.w sg.w) : ℝ)) = ((d1 lt.w sg.w : ℤ) : ℝ) := by
    unfold d1 lenP
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Int.cast_min]
  have hdim_pos : 0 < dimV lt.w := dimV_pos lt
  rw [Real.exp_add, Real.exp_log hdim_pos]
  refine mul_le_mul_of_nonneg_right ?_ hdim_pos.le
  set c := cCap lt.w sg.w
  set k := n * (d1 lt.w sg.w).toNat
  set W : ℤ := lt.w 0 - lt.w (Fin.last n) + ((n : ℤ) + 1)
  have hanti : lt.w (Fin.last n) ≤ lt.w 0 := lt.anti (Fin.zero_le _)
  have hWpos : 0 < W := by omega
  have hBW : (lt.w 0 - lt.w (Fin.last n) + (n : ℤ) - 1) ^ k ≤ W ^ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero, pow_zero]
    · have hn : 0 < n := Nat.pos_of_ne_zero (left_ne_zero_of_mul (Nat.pos_iff_ne_zero.mp h0))
      exact pow_le_pow_left₀ (by omega) (by omega) k
  have hcZ : c ^ 2 ≤ W ^ (2 * k) := by
    rw [pow_mul', ← sq_abs c]
    exact pow_le_pow_left₀ (abs_nonneg c) (hc.trans hBW) 2
  have hcR : ((c : ℝ)) ^ 2 ≤ (W : ℝ) ^ (2 * k) := by exact_mod_cast hcZ
  refine hcR.trans (le_of_eq ?_)
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hWR, hsum, lt.spread_eq_succ]
  change Real.exp (Real.log (W : ℝ) * ((2 * k : ℕ) : ℝ)) =
    Real.exp (2 * (n : ℝ) * Real.log ((W : ℤ) : ℝ) * ((d1 lt.w sg.w : ℤ) : ℝ))
  congr 1
  have hkR : ((k : ℕ) : ℝ) = (n : ℝ) * ((d1 lt.w sg.w : ℤ) : ℝ) := by
    change ((n * (d1 lt.w sg.w).toNat : ℕ) : ℝ) = _
    rw [Nat.cast_mul]
    congr 1
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hd1nn)
    rw [← h2, Int.cast_natCast]
  push_cast
  rw [hkR]
  ring

end DominantWeightsAndCapacity

/-! ## Section 2: Exact Hook–Vandermonde Identity & Explicit Stirling Bounds (`hook_length_stirling_bound`) -/

section HookLengthStirlingBounds

/-- Exact cardinality of strictly ordered pairs: `|(Partition.pairsLt r)| = r * (r - 1) / 2`. -/
theorem card_pairsLt (r : ℕ) : (Partition.pairsLt r).card = r * (r - 1) / 2 := by
  induction r with
  | zero => simp [Partition.pairsLt]
  | succ n ih =>
    have hsplit : (Partition.pairsLt (n + 1)).card =
        (Partition.pairsLt n).card + n := by
      let S₁ := (Partition.pairsLt (n + 1)).filter fun p => p.2.1 < n
      let S₂ := (Partition.pairsLt (n + 1)).filter fun p => ¬ (p.2.1 < n)
      have hpart : (Partition.pairsLt (n + 1)).card = S₁.card + S₂.card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _)]
        congr 1
        ext p
        simp only [Finset.mem_union, Finset.mem_filter]
        tauto
      have hS₁ : S₁.card = (Partition.pairsLt n).card := by
        refine Finset.card_bij
          (fun p hp => (⟨p.1.1, lt_trans (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            (Finset.mem_filter.mp hp).2⟩, ⟨p.2.1, (Finset.mem_filter.mp hp).2⟩))
          (fun p hp => by
            rw [Partition.pairsLt, Finset.mem_filter]
            exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
              (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2⟩)
          (fun p₁ _ p₂ _ h => by
            rcases Prod.mk.inj h with ⟨h1, h2⟩
            exact Prod.ext (Fin.ext (Fin.mk.inj h1)) (Fin.ext (Fin.mk.inj h2)))
          (fun q hq => by
            refine ⟨(q.1.castSucc, q.2.castSucc), ?_, by ext <;> rfl⟩
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
              (Finset.mem_filter.mp hq).2⟩, q.2.2⟩)
      have hS₂ : S₂.card = n := by
        have hbij : S₂.card = (Finset.range n).card := by
          refine Finset.card_bij (fun p _ => p.1.1)
            (fun p hp => by
              have hlt : p.1.1 < p.2.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
              have h2 : p.2.1 < n + 1 := p.2.2
              have hge : ¬ (p.2.1 < n) := (Finset.mem_filter.mp hp).2
              exact Finset.mem_range.mpr (by omega))
            (fun p₁ hp₁ p₂ hp₂ h => by
              have h12 : p₁.2.1 = n := by
                have := p₁.2.2; have := (Finset.mem_filter.mp hp₁).2; omega
              have h22 : p₂.2.1 = n := by
                have := p₂.2.2; have := (Finset.mem_filter.mp hp₂).2; omega
              exact Prod.ext (Fin.ext h) (Fin.ext (h12.trans h22.symm)))
            (fun k hk => by
              have hk' : k < n := Finset.mem_range.mp hk
              refine ⟨(⟨k, by omega⟩, Fin.last n), ?_, rfl⟩
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
                show k < n from hk'⟩, by simp⟩)
        rw [hbij, Finset.card_range]
      rw [hpart, hS₁, hS₂]
    rw [hsplit, ih]
    cases n with
    | zero => simp
    | succ m =>
      have heven : 2 ∣ (m + 1) * m := by
        rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact ⟨(2 * k + 1) * k, by ring⟩
        · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
      have h1 : (m + 1) * m / 2 + (m + 1) = ((m + 1) * m + 2 * (m + 1)) / 2 := by
        rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
      rw [show m + 1 + 1 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega, h1]
      congr 1
      ring

/-- **Exact Global Hook–Vandermonde–Factorial Identity (`hookProd_mul_vandermonde_eq_prod_factorial`)**:
for every `r : ℕ` and every partition `lam : Partition r`,
`lam.hookProd * ∏_{0 ≤ i < j < r} (ℓ_i - ℓ_j) = ∏_{i < r} (ℓ_i)!`. -/
theorem hookProd_mul_vandermonde_eq_prod_factorial {r : ℕ} (lam : Partition r) :
    lam.hookProd *
      (∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2)) =
    ∏ i : Fin r, (lam.shiftedPart i).factorial := by
  have hhook_rows : lam.hookProd =
      ∏ i : Fin r, ∏ j ∈ Finset.range (lam.parts i), lam.hookLength i j := by
    unfold Partition.hookProd Partition.cells
    rw [Finset.prod_biUnion]
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact Finset.prod_image (fun _ _ _ _ h => (Prod.mk.inj h).2)
    · intro i _ j _ hij
      exact Finset.disjoint_left.mpr fun p hp1 hp2 => by
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp1
        obtain ⟨_, _, h⟩ := Finset.mem_image.mp hp2
        exact hij (Prod.mk.inj h).1.symm
  have hvand_rows :
      (∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2)) =
      ∏ i : Fin r, ∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m),
        (lam.shiftedPart i - lam.shiftedPart m) := by
    unfold Partition.pairsLt
    rw [Finset.prod_filter, Finset.product_eq_sprod, Finset.prod_product]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
  rw [hhook_rows, hvand_rows, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => lam.row_hook_prod_mul_diff_eq_factorial i

/-- Exact factorial upper bound on hook products: `H_lam ≤ ∏_i (ℓ_i)!`. -/
theorem hookProd_le_prod_shifted_factorial {r : ℕ} (lam : Partition r) :
    lam.hookProd ≤ ∏ i : Fin r, (lam.shiftedPart i).factorial := by
  have hpos : 1 ≤ ∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2) := by
    refine Finset.one_le_prod' fun p hp => ?_
    exact Nat.sub_pos_of_lt (lam.shiftedPart_strictAnti (Finset.mem_filter.mp hp).2)
  calc lam.hookProd = lam.hookProd * 1 := (mul_one _).symm
    _ ≤ lam.hookProd * (∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2)) :=
        Nat.mul_le_mul_left _ hpos
    _ = ∏ i : Fin r, (lam.shiftedPart i).factorial :=
        hookProd_mul_vandermonde_eq_prod_factorial lam

/-- Explicit upper bound on the Vandermonde product of shifted parts:
`∏_{i < j} (ℓ_i - ℓ_j) ≤ (lam_0 + r)^(r*(r-1)/2)`. -/
theorem vandermonde_le_pow {r : ℕ} (lam : Partition r) :
    (∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2)) ≤
      (lam.maxPart + r) ^ (r * (r - 1) / 2) := by
  calc ∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2)
      ≤ ∏ _p ∈ Partition.pairsLt r, (lam.maxPart + r) := by
        refine Finset.prod_le_prod' fun p _ => ?_
        have h1 : lam.parts p.1 ≤ lam.maxPart := lam.parts_le_maxPart p.1
        have h2 : p.1.1 < r := p.1.2
        unfold Partition.shiftedPart
        omega
    _ = (lam.maxPart + r) ^ (Partition.pairsLt r).card := Finset.prod_const _
    _ = (lam.maxPart + r) ^ (r * (r - 1) / 2) := by rw [card_pairsLt]

/-- Exact logarithmic factorial-Vandermonde lower bound on `log (hookProd lam)`:
`∑_i log (ℓ_i!) - (r*(r-1)/2) * log (lam_0 + r) ≤ log (hookProd lam)`. -/
theorem log_prod_shifted_factorial_sub_le_log_hookProd {r : ℕ} (_hr : 0 < r) (lam : Partition r) :
    (∑ i : Fin r, Real.log ((lam.shiftedPart i).factorial : ℝ)) -
      ((r * (r - 1) / 2 : ℕ) : ℝ) * Real.log ((lam.maxPart + r : ℕ) : ℝ) ≤
    Real.log (lam.hookProd : ℝ) := by
  have hid : ((lam.hookProd : ℝ)) *
      ((∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2) : ℕ) : ℝ) =
      ((∏ i : Fin r, (lam.shiftedPart i).factorial : ℕ) : ℝ) := by
    exact_mod_cast hookProd_mul_vandermonde_eq_prod_factorial lam
  have hHpos : (0 : ℝ) < (lam.hookProd : ℝ) := Nat.cast_pos.mpr lam.hookProd_pos
  have hVpos : (0 : ℝ) < ((∏ p ∈ Partition.pairsLt r,
      (lam.shiftedPart p.1 - lam.shiftedPart p.2) : ℕ) : ℝ) := by
    refine Nat.cast_pos.mpr (Finset.prod_pos fun p hp => ?_)
    exact Nat.sub_pos_of_lt (lam.shiftedPart_strictAnti (Finset.mem_filter.mp hp).2)
  have hlog_id : Real.log (lam.hookProd : ℝ) +
      Real.log ((∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2) : ℕ) : ℝ) =
      ∑ i : Fin r, Real.log ((lam.shiftedPart i).factorial : ℝ) := by
    rw [← Real.log_mul hHpos.ne' hVpos.ne', hid, Nat.cast_prod,
      Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
  have hVle : ((∏ p ∈ Partition.pairsLt r,
      (lam.shiftedPart p.1 - lam.shiftedPart p.2) : ℕ) : ℝ) ≤
      ((lam.maxPart + r : ℕ) : ℝ) ^ (r * (r - 1) / 2) := by
    exact_mod_cast vandermonde_le_pow lam
  have hlogV : Real.log ((∏ p ∈ Partition.pairsLt r,
      (lam.shiftedPart p.1 - lam.shiftedPart p.2) : ℕ) : ℝ) ≤
      ((r * (r - 1) / 2 : ℕ) : ℝ) * Real.log ((lam.maxPart + r : ℕ) : ℝ) := by
    have h := Real.log_le_log hVpos hVle
    rwa [Real.log_pow] at h
  linarith

/-- **Unconditional `HookLengthFactorialBound` (Alpöge `FlipTwoThree:308`)**:
for any `N : ℕ` and antitone `nu : Fin N → ℚ` taking natural-number values, letting `lam` be the
corresponding partition:
1. `lam.hookProd ≤ ∏ i : Fin N, (⌊nu i⌋.toNat + N - 1 - i)!`,
2. for `0 < N`, `∑ i, log ((⌊nu i⌋.toNat + N - 1 - i)!) - N^2 * log (nu 0 + N) ≤ log (lam.hookProd)`. -/
theorem hook_length_factorial_bound (N : ℕ) (nu : Fin N → ℚ)
    (hint : ∀ i, ∃ z : ℕ, nu i = z) (hanti : Antitone nu) :
    let lam : Partition N :=
      { parts := fun i => ⌊nu i⌋.toNat
        anti := fun a b hab => by
          obtain ⟨za, hza⟩ := hint a
          obtain ⟨zb, hzb⟩ := hint b
          have hle := hanti hab
          rw [hza, hzb] at hle
          have hzn : zb ≤ za := by exact_mod_cast hle
          simp only [hza, hzb, Int.floor_natCast, Int.toNat_natCast]
          exact hzn }
    (lam.hookProd : ℝ) ≤ ∏ i : Fin N, (((⌊nu i⌋.toNat + N - 1 - i.1 : ℕ).factorial : ℕ) : ℝ) ∧
    ∀ h : 0 < N, (∑ i : Fin N, Real.log (((⌊nu i⌋.toNat + N - 1 - i.1 : ℕ).factorial : ℕ) : ℝ)) -
      (N : ℝ) ^ 2 * Real.log ((nu ⟨0, h⟩ : ℝ) + (N : ℝ)) ≤ Real.log (lam.hookProd : ℝ) := by
  intro lam
  have hshift_eq : ∀ i : Fin N, lam.shiftedPart i = ⌊nu i⌋.toNat + N - 1 - i.1 := fun i => by
    unfold Partition.shiftedPart
    have hi : i.1 < N := i.2
    change ⌊nu i⌋.toNat + (N - 1 - i.1) = _
    omega
  constructor
  · have h1 : (lam.hookProd : ℝ) ≤ ((∏ i : Fin N, (lam.shiftedPart i).factorial : ℕ) : ℝ) := by
      exact_mod_cast hookProd_le_prod_shifted_factorial lam
    rw [Nat.cast_prod] at h1
    simpa only [hshift_eq] using h1
  · intro hN
    have hlow := log_prod_shifted_factorial_sub_le_log_hookProd hN lam
    simp only [hshift_eq] at hlow
    have hmax_eq : ((lam.maxPart + N : ℕ) : ℝ) = (nu ⟨0, hN⟩ : ℝ) + (N : ℝ) := by
      unfold Partition.maxPart
      rw [dif_pos hN]
      obtain ⟨z0, hz0⟩ := hint ⟨0, hN⟩
      change ((⌊nu ⟨0, hN⟩⌋.toNat + N : ℕ) : ℝ) = _
      rw [hz0, Int.floor_natCast, Int.toNat_natCast]
      push_cast
      rfl
    rw [hmax_eq] at hlow
    have hlog_nn : 0 ≤ Real.log ((nu ⟨0, hN⟩ : ℝ) + (N : ℝ)) := by
      apply Real.log_nonneg
      obtain ⟨z0, hz0⟩ := hint ⟨0, hN⟩
      rw [hz0]
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hz0nn : (0 : ℝ) ≤ (z0 : ℝ) := Nat.cast_nonneg z0
      push_cast
      linarith
    have hhalf_le : ((N * (N - 1) / 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have hnat : N * (N - 1) / 2 ≤ N * N :=
        (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left N (Nat.sub_le N 1))
      have : ((N * (N - 1) / 2 : ℕ) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast hnat
      simpa [sq] using this
    have hmul := mul_le_mul_of_nonneg_right hhalf_le hlog_nn
    linarith

/-! ### Explicit Elementary Stirling Bounds on `log (n!)` -/

/-- **Explicit Stirling Lower Bound (`stirling_log_factorial_lower`)**:
for every `n ≥ 1`, `n * log n - n + 1 ≤ log (n!)`. -/
theorem stirling_log_factorial_lower :
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 ≤ Real.log (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have ihk := ih hk
      have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hk1R : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hstep : Real.log ((k + 1).factorial : ℝ) =
          Real.log (k.factorial : ℝ) + Real.log ((k + 1 : ℕ) : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity)
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), add_comm]
      have hlog_ratio : Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 / (k : ℝ) := by
        have h1 := Real.log_le_sub_one_of_pos (div_pos hk1R hkR)
        have hsub : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
          push_cast; field_simp [hkR.ne']; ring
        linarith
      have hmul_log : (k : ℝ) * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) ≤ 1 := by
        rw [← Real.log_div hk1R.ne' hkR.ne']
        have := mul_le_mul_of_nonneg_left hlog_ratio hkR.le
        have hcancel : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp [hkR.ne']
        linarith
      rw [hstep]
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hmul_log ⊢
      nlinarith

/-- **Explicit Stirling Upper Bound (`stirling_log_factorial_upper`)**:
for every `n : ℕ` (including `n = 0`), `log (n!) ≤ (n + 1) * log (n + 1) - n`. -/
theorem stirling_log_factorial_upper :
    ∀ n : ℕ, Real.log (n.factorial : ℝ) ≤ ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - (n : ℝ) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hstep : Real.log ((k + 1).factorial : ℝ) =
        Real.log (k.factorial : ℝ) + Real.log ((k : ℝ) + 1) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity)
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), add_comm]
      push_cast; ring
    have hlog_inv : Real.log (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ -(1 / ((k : ℝ) + 2)) := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hk1 hk2)
      have hsub : ((k : ℝ) + 1) / ((k : ℝ) + 2) - 1 = -(1 / ((k : ℝ) + 2)) := by
        field_simp [hk2.ne']; ring
      linarith
    have hlog_ge : 1 / ((k : ℝ) + 2) ≤ Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) := by
      have hdiv : Real.log (((k : ℝ) + 1) / ((k : ℝ) + 2)) =
          Real.log ((k : ℝ) + 1) - Real.log ((k : ℝ) + 2) :=
        Real.log_div hk1.ne' hk2.ne'
      linarith
    have hmul_ge : 1 ≤ ((k : ℝ) + 2) * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) := by
      have := mul_le_mul_of_nonneg_left hlog_ge hk2.le
      have hcancel : ((k : ℝ) + 2) * (1 / ((k : ℝ) + 2)) = 1 := by field_simp [hk2.ne']
      linarith
    rw [hstep]
    have h2 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    have h1' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [h2, h1']
    nlinarith

/-- **Sharp Explicit Stirling Upper Bound for `n ≥ 1` (`stirling_log_factorial_upper_sharp`)**:
`log (n!) ≤ (n + 1) * log n - n + 1`. -/
theorem stirling_log_factorial_upper_sharp :
    ∀ n : ℕ, 1 ≤ n → Real.log (n.factorial : ℝ) ≤ ((n : ℝ) + 1) * Real.log (n : ℝ) - (n : ℝ) + 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have ihk := ih hk
      have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hstep : Real.log ((k + 1).factorial : ℝ) =
          Real.log (k.factorial : ℝ) + Real.log ((k : ℝ) + 1) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity)
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), add_comm]
        push_cast; ring
      have hlog_inv : Real.log ((k : ℝ) / ((k : ℝ) + 1)) ≤ -(1 / ((k : ℝ) + 1)) := by
        have h1 := Real.log_le_sub_one_of_pos (div_pos hkR hk1)
        have hsub : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by
          field_simp [hk1.ne']; ring
        linarith
      have hlog_ge : 1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
        have hdiv : Real.log ((k : ℝ) / ((k : ℝ) + 1)) = Real.log (k : ℝ) - Real.log ((k : ℝ) + 1) :=
          Real.log_div hkR.ne' hk1.ne'
        linarith
      have hmul_ge : 1 ≤ ((k : ℝ) + 1) * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hlog_ge hk1.le
        have hcancel : ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) = 1 := by field_simp [hk1.ne']
        linarith
      rw [hstep]
      have h1' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [h1']
      nlinarith

/-- Helper: lower bound `n * log n - n ≤ log (n!)` valid for ALL `n : ℕ` (including `n = 0`). -/
theorem stirling_log_factorial_lower_all (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · linarith [stirling_log_factorial_lower n hn]

/-- Exact denominator identity in the Weyl dimension formula:
`∏_{0 ≤ i < j < r} (j - i) = ∏_{i < r} (r - 1 - i)!`. -/
theorem prod_pairsLt_sub_eq_prod_factorial (r : ℕ) :
    (∏ p ∈ Partition.pairsLt r, (p.2.1 - p.1.1)) =
      ∏ i : Fin r, (r - 1 - i.1).factorial := by
  unfold Partition.pairsLt
  rw [Finset.prod_filter, Finset.product_eq_sprod, Finset.prod_product]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  have hbij : ∏ m ∈ Finset.univ.filter (fun m : Fin r => i < m), (m.1 - i.1) =
      ∏ n ∈ Finset.Icc 1 (r - 1 - i.1), n := by
    refine Finset.prod_bij (fun m _ => m.1 - i.1)
      (fun m hm => Finset.mem_Icc.mpr (by
        have h1 : i.1 < m.1 := (Finset.mem_filter.mp hm).2
        have h2 : m.1 < r := m.2; omega))
      (fun m₁ hm₁ m₂ hm₂ h => Fin.ext (by
        have h1 : i.1 < m₁.1 := (Finset.mem_filter.mp hm₁).2
        have h2 : i.1 < m₂.1 := (Finset.mem_filter.mp hm₂).2; omega))
      (fun n hn => ⟨⟨n + i.1, by
        have h1 := (Finset.mem_Icc.mp hn).1; have h2 := (Finset.mem_Icc.mp hn).2
        have hi := i.2; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, show i.1 < n + i.1 by
          have := (Finset.mem_Icc.mp hn).1; omega⟩,
        by dsimp only; omega⟩)
      (fun _ _ => rfl)
  rw [hbij]
  set L := r - 1 - i.1
  clear * -
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), ih, Nat.factorial_succ,
      mul_comm]

/-- **MAIN EXPORT #2 — Explicit Stirling & Factorial Hook-Length Bound (`hook_length_stirling_bound`)**:
For every `r : ℕ` and every partition `lam : Partition r`:
1. Exact factorial ceiling: `lam.hookProd ≤ ∏ i : Fin r, (lam.shiftedPart i).factorial`,
2. Explicit Stirling upper bound on `log (hookProd lam)`:
   `log (hookProd lam) ≤ ∑ i : Fin r, ((ℓ_i + 1) * log (ℓ_i + 1) - ℓ_i)`,
3. Explicit Stirling lower bound on `log (hookProd lam)` (when `0 < r`):
   `(∑ i : Fin r, (ℓ_i * log ℓ_i - ℓ_i)) - (r*(r-1)/2) * log (lam_0 + r) ≤ log (hookProd lam)`,
4. Sharp Weyl dimension upper bound (polynomial in `lam_0 + r` of degree `r*(r-1)/2`!):
   `lam.weylDim ≤ (lam_0 + r) ^ (r * (r - 1) / 2)` AND
   `log (lam.weylDim) ≤ (r*(r-1)/2) * log (lam_0 + r) - ∑ i : Fin r, log ((r - 1 - i)!)`. -/
theorem hook_length_stirling_bound {r : ℕ} (lam : Partition r) :
    lam.hookProd ≤ ∏ i : Fin r, (lam.shiftedPart i).factorial ∧
    Real.log (lam.hookProd : ℝ) ≤
      ∑ i : Fin r,
        (((lam.shiftedPart i : ℝ) + 1) * Real.log ((lam.shiftedPart i : ℝ) + 1) -
          (lam.shiftedPart i : ℝ)) ∧
    (0 < r →
      (∑ i : Fin r,
        ((lam.shiftedPart i : ℝ) * Real.log (lam.shiftedPart i : ℝ) - (lam.shiftedPart i : ℝ))) -
        ((r * (r - 1) / 2 : ℕ) : ℝ) * Real.log ((lam.maxPart + r : ℕ) : ℝ) ≤
      Real.log (lam.hookProd : ℝ)) ∧
    lam.weylDim ≤ ((lam.maxPart + r : ℕ) : ℝ) ^ (r * (r - 1) / 2) ∧
    (0 < r →
      Real.log lam.weylDim ≤
        ((r * (r - 1) / 2 : ℕ) : ℝ) * Real.log ((lam.maxPart + r : ℕ) : ℝ) -
          ∑ i : Fin r, Real.log ((r - 1 - i.1).factorial : ℝ)) := by
  have h1 := hookProd_le_prod_shifted_factorial lam
  have h2 : Real.log (lam.hookProd : ℝ) ≤
      ∑ i : Fin r,
        (((lam.shiftedPart i : ℝ) + 1) * Real.log ((lam.shiftedPart i : ℝ) + 1) -
          (lam.shiftedPart i : ℝ)) := by
    have hR : (lam.hookProd : ℝ) ≤ ((∏ i : Fin r, (lam.shiftedPart i).factorial : ℕ) : ℝ) := by
      exact_mod_cast h1
    have hlog := Real.log_le_log (Nat.cast_pos.mpr lam.hookProd_pos) hR
    rw [Nat.cast_prod, Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))] at hlog
    exact hlog.trans (Finset.sum_le_sum fun i _ => stirling_log_factorial_upper (lam.shiftedPart i))
  have h3 : 0 < r →
      (∑ i : Fin r,
        ((lam.shiftedPart i : ℝ) * Real.log (lam.shiftedPart i : ℝ) - (lam.shiftedPart i : ℝ))) -
        ((r * (r - 1) / 2 : ℕ) : ℝ) * Real.log ((lam.maxPart + r : ℕ) : ℝ) ≤
      Real.log (lam.hookProd : ℝ) := by
    intro hr
    have hlow := log_prod_shifted_factorial_sub_le_log_hookProd hr lam
    have hsum_le :
        (∑ i : Fin r,
          ((lam.shiftedPart i : ℝ) * Real.log (lam.shiftedPart i : ℝ) - (lam.shiftedPart i : ℝ))) ≤
        ∑ i : Fin r, Real.log ((lam.shiftedPart i).factorial : ℝ) :=
      Finset.sum_le_sum fun i _ => stirling_log_factorial_lower_all (lam.shiftedPart i)
    linarith
  have hweyl_div : lam.weylDim =
      ((∏ p ∈ Partition.pairsLt r, (lam.shiftedPart p.1 - lam.shiftedPart p.2) : ℕ) : ℝ) /
      ((∏ i : Fin r, (r - 1 - i.1).factorial : ℕ) : ℝ) := by
    unfold Partition.weylDim
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
      prod_pairsLt_sub_eq_prod_factorial]
  have hden_ge_one : (1 : ℝ) ≤ ((∏ i : Fin r, (r - 1 - i.1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.one_le_prod' fun i _ => Nat.factorial_pos _
  have hnum_le : ((∏ p ∈ Partition.pairsLt r,
      (lam.shiftedPart p.1 - lam.shiftedPart p.2) : ℕ) : ℝ) ≤
      ((lam.maxPart + r : ℕ) : ℝ) ^ (r * (r - 1) / 2) := by
    exact_mod_cast vandermonde_le_pow lam
  have h4 : lam.weylDim ≤ ((lam.maxPart + r : ℕ) : ℝ) ^ (r * (r - 1) / 2) := by
    rw [hweyl_div]
    exact (div_le_self (Nat.cast_nonneg _) hden_ge_one).trans hnum_le
  have h5 : 0 < r →
      Real.log lam.weylDim ≤
        ((r * (r - 1) / 2 : ℕ) : ℝ) * Real.log ((lam.maxPart + r : ℕ) : ℝ) -
          ∑ i : Fin r, Real.log ((r - 1 - i.1).factorial : ℝ) := by
    intro _
    have hVpos : (0 : ℝ) < ((∏ p ∈ Partition.pairsLt r,
        (lam.shiftedPart p.1 - lam.shiftedPart p.2) : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Finset.prod_pos fun p hp =>
        Nat.sub_pos_of_lt (lam.shiftedPart_strictAnti (Finset.mem_filter.mp hp).2))
    have hDpos : (0 : ℝ) < ((∏ i : Fin r, (r - 1 - i.1).factorial : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Finset.prod_pos fun i _ => Nat.factorial_pos _)
    have hDlog : Real.log ((∏ i : Fin r, (r - 1 - i.1).factorial : ℕ) : ℝ) =
        ∑ i : Fin r, Real.log ((r - 1 - i.1).factorial : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    rw [hweyl_div, Real.log_div hVpos.ne' hDpos.ne', hDlog]
    have hlogV := Real.log_le_log hVpos hnum_le
    rw [Real.log_pow] at hlogV
    linarith
  exact ⟨h1, h2, h3, h4, h5⟩

end HookLengthStirlingBounds

/-! ## Section 3: Concrete `SchurFunctorColumnLat` & Column-Tensor Branching Slopes -/

section SchurFunctorColumnLattice

/-- **MAIN EXPORT #1 — Concrete Schur-Functor Column Lattice `SchurFunctorColumnLat`**:
bundles:
- a base nonzero Euclidean lattice `base : ConcreteEuclideanLat`,
- a partition `lam : Partition (rk base.L)`,
- the target Schur-functor lattice `schurLat : ConcreteEuclideanLat` realizing `𝕊_lam(base)`,
- the concrete full-real-span branching projection `proj : (columnTensorLat base lam).L →ₗ[ℤ] schurLat.L`
  with explicit hook-product / branching distortion bound `‖proj x‖ ≤ H_lam * branchConst * ‖x‖`.

Ready for direct consumption in M2 Wave 2 (`ColumnExactSlope`) and Wave 3 (`AutomorphicLatM`). -/
structure SchurFunctorColumnLat where
  base : ConcreteEuclideanLat
  lam : Partition (rk base.L)
  schurLat : ConcreteEuclideanLat
  proj : (columnTensorLat base lam).L →ₗ[ℤ] schurLat.L
  branchConst : ℝ
  branchConst_pos : 0 < branchConst
  proj_norm_le : ∀ x : (columnTensorLat base lam).L,
    ‖((proj x : schurLat.L) : schurLat.E)‖ ≤
      (lam.hookProd : ℝ) * branchConst * ‖(x : (columnTensorLat base lam).E)‖
  proj_full_span :
    Submodule.span ℝ (Set.range fun x : (columnTensorLat base lam).L =>
      ((proj x : schurLat.L) : schurLat.E)) =
    Submodule.span ℝ (schurLat.L : Set schurLat.E)

namespace SchurFunctorColumnLat

/-- Underlying column-tensor lattice `⨂_{j < lam_0} (⋀^{lam'_j} base)`. -/
def colLat (S : SchurFunctorColumnLat) : ConcreteEuclideanLat :=
  columnTensorLat S.base S.lam

/-- Exact rank of the column-tensor lattice: `∏_{j < lam_0} choose (rk base) (lam'_j)`. -/
theorem colLat_rk_eq (S : SchurFunctorColumnLat) :
    rk S.colLat.L =
      ∏ j ∈ Finset.range S.lam.maxPart, Nat.choose (rk S.base.L) (S.lam.colLen j) :=
  (column_lattice_exact_slope S.base S.lam).1

/-- Exact column-tensor slope: `slope (colLat) = |lam| * slope (base)`. -/
theorem colLat_slope_eq (S : SchurFunctorColumnLat) :
    ArakelovCovolume.slope S.colLat.L =
      (S.lam.weight : ℝ) * ArakelovCovolume.slope S.base.L :=
  (column_lattice_exact_slope S.base S.lam).2

/-- Canonical self-realized `SchurFunctorColumnLat` with `schurLat = columnTensorLat base lam`,
`proj = id`, and `branchConst = 1`. -/
def ofColumnTensor (base : ConcreteEuclideanLat) (lam : Partition (rk base.L)) :
    SchurFunctorColumnLat where
  base := base
  lam := lam
  schurLat := columnTensorLat base lam
  proj := LinearMap.id
  branchConst := 1
  branchConst_pos := one_pos
  proj_norm_le := fun x => by
    have hH : (1 : ℝ) ≤ (lam.hookProd : ℝ) := by exact_mod_cast lam.hookProd_pos
    have hnn : 0 ≤ ‖(x : (columnTensorLat base lam).E)‖ := norm_nonneg _
    simp only [LinearMap.id_coe, id_eq, mul_one]
    nlinarith
  proj_full_span := by
    congr 1
    ext y
    simp only [LinearMap.id_coe, id_eq, Set.mem_range, SetLike.mem_coe]
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩

/-- Concrete `ConcreteEuclideanLat` attached to any arbitrary-rank `CMHermLattice d r`. -/
def concreteLatOfCMHerm {d r : ℕ} (Λ : CMHermLattice d r) : ConcreteEuclideanLat where
  E := EuclideanSpace ℝ (Fin (2 * r))
  L := Λ.euclLat
  discL := Λ.discreteTopology_euclLat
  ne_bot := Λ.euclLat_ne_bot

/-- Concrete `SchurFunctorColumnLat` built directly on any arbitrary-rank `CMHermLattice d r`
and dominant partition `lam : Partition (2 * r)`. -/
def ofCMHermLattice {d r : ℕ} (Λ : CMHermLattice d r) (lam : Partition (2 * r)) :
    SchurFunctorColumnLat :=
  let A := concreteLatOfCMHerm Λ
  let lamA : Partition (rk A.L) :=
    { parts := fun i => lam.parts (i.cast Λ.rk_euclLat)
      anti := fun _ _ h => lam.anti h }
  ofColumnTensor A lamA

/-- Concrete `ConcreteEuclideanLat` attached to any nonzero `NumberFieldHLat K`. -/
def concreteLatOfNumberFieldHLat {K : Type} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] [StarRing K] (A : NumberFieldHLat K)
    (hne : A.zRealize ≠ ⊥) : ConcreteEuclideanLat where
  E := EuclideanSpace ℝ (NumberField.InfinitePlace K × A.ι × Fin 2)
  L := A.zRealize
  discL := A.discReal
  ne_bot := hne

/-- Concrete `SchurFunctorColumnLat` built directly on any nonzero `NumberFieldHLat K`. -/
def ofNumberFieldHLat {K : Type} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    [StarRing K] (A : NumberFieldHLat K) (hne : A.zRealize ≠ ⊥)
    (lam : Partition (rk A.zRealize)) : SchurFunctorColumnLat :=
  ofColumnTensor (concreteLatOfNumberFieldHLat A hne) lam

/-- **Stirling-Sharpened `muMin` & `slope` Lower Bound on `SchurFunctorColumnLat`**:
combines `muMin_sub_log_le_muMin_of_fullRank` with `hook_length_stirling_bound` to bound
`muMin S.schurLat.L` and `slope S.schurLat.L` using the exact Stirling hook-length ceiling
`∑ i, ((ℓ_i + 1) log (ℓ_i + 1) - ℓ_i)` (strictly sharper than `|lam| * log (lam_0 + r)`!). -/
theorem muMin_lower_stirling (S : SchurFunctorColumnLat) :
    muMin S.colLat.L -
      (∑ i : Fin (rk S.base.L),
        (((S.lam.shiftedPart i : ℝ) + 1) * Real.log ((S.lam.shiftedPart i : ℝ) + 1) -
          (S.lam.shiftedPart i : ℝ))) -
      Real.log S.branchConst ≤ muMin S.schurLat.L ∧
    muMin S.schurLat.L ≤ ArakelovCovolume.slope S.schurLat.L := by
  have hHpos : (0 : ℝ) < (S.lam.hookProd : ℝ) := Nat.cast_pos.mpr S.lam.hookProd_pos
  have hHC : 0 < (S.lam.hookProd : ℝ) * S.branchConst := mul_pos hHpos S.branchConst_pos
  obtain ⟨hmu, _⟩ := muMin_sub_log_le_muMin_of_fullRank
    S.colLat.L S.schurLat.L S.schurLat.ne_bot S.proj hHC S.proj_norm_le S.proj_full_span
  have hst := (hook_length_stirling_bound S.lam).2.1
  have hlog_mul : Real.log ((S.lam.hookProd : ℝ) * S.branchConst) =
      Real.log (S.lam.hookProd : ℝ) + Real.log S.branchConst :=
    Real.log_mul hHpos.ne' S.branchConst_pos.ne'
  refine ⟨by linarith, (muMin_le_slope_le_muMax S.schurLat.L S.schurLat.ne_bot).1⟩

/-- **Slope Lower Bound under Semistability Defect `Δ`** (`slope colLat - muMin colLat ≤ Δ`):
`|lam| * slope base - Δ - ∑ i, ((ℓ_i + 1) log (ℓ_i + 1) - ℓ_i) - log branchConst ≤ muMin S ≤ slope S`. -/
theorem slope_lower_stirling (S : SchurFunctorColumnLat) {Δ : ℝ}
    (hΔ : ArakelovCovolume.slope S.colLat.L - muMin S.colLat.L ≤ Δ) :
    (S.lam.weight : ℝ) * ArakelovCovolume.slope S.base.L - Δ -
      (∑ i : Fin (rk S.base.L),
        (((S.lam.shiftedPart i : ℝ) + 1) * Real.log ((S.lam.shiftedPart i : ℝ) + 1) -
          (S.lam.shiftedPart i : ℝ))) -
      Real.log S.branchConst ≤ muMin S.schurLat.L ∧
    muMin S.schurLat.L ≤ ArakelovCovolume.slope S.schurLat.L := by
  obtain ⟨h1, h2⟩ := S.muMin_lower_stirling
  have hcol := S.colLat_slope_eq
  exact ⟨by linarith, h2⟩

/-- Exact column-tensor slope for `ofCMHermLattice Λ lam`:
`slope (ofCMHermLattice Λ lam).colLat.L = |lam| * (-(1/4) log d - log (det H) / (2r))`. -/
theorem colLat_slope_ofCMHermLattice {d r : ℕ} (Λ : CMHermLattice d r) (lam : Partition (2 * r)) :
    ArakelovCovolume.slope (ofCMHermLattice Λ lam).colLat.L =
      (lam.weight : ℝ) * (-(1 / 4) * Real.log d - Real.log Λ.H.det.re / (2 * (r : ℝ))) := by
  have h := (ofCMHermLattice Λ lam).colLat_slope_eq
  have hw : (ofCMHermLattice Λ lam).lam.weight = lam.weight := by
    unfold ofCMHermLattice ofColumnTensor Partition.weight
    exact Fintype.sum_equiv (finCongr Λ.rk_euclLat) _ _ fun _ => rfl
  rw [h, hw]
  change _ * ArakelovCovolume.slope Λ.euclLat = _
  rw [Λ.slope_eq]

end SchurFunctorColumnLat

end SchurFunctorColumnLattice

/-! ## Section 4: Multivariable Polynomial Fock Space, Weighted Cauchy–Binet & `standard_slope_lower` -/

section FockSpaceAndStandardSlopeLower

/-- Rational Bargmann–Fock inner product on `MvPolynomial σ ℚ`:
`fockQ P Q = ∑_{m ∈ supp P} P_m * Q_m * ∏_{k ∈ supp m} (m k)!`. -/
def fockQ {σ : Type*} (P Q : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ P.support, P.coeff m * Q.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ)

/-- Complex Hermitian Bargmann–Fock inner product on `MvPolynomial σ ℂ`:
`fockC P Q = ∑_{m ∈ supp P} P_m * conj(Q_m) * ∏_{k ∈ supp m} (m k)!`. -/
def fockC {σ : Type*} (P Q : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ P.support, P.coeff m * star (Q.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)

theorem fockQ_eq_sum {σ : Type*} (P Q : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    fockQ P Q = ∑ m ∈ S, P.coeff m * Q.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]; ring

theorem fockQ_comm {σ : Type*} (P Q : MvPolynomial σ ℚ) : fockQ P Q = fockQ Q P := by
  classical
  rw [fockQ_eq_sum P Q (P.support ∪ Q.support) Finset.subset_union_left,
    fockQ_eq_sum Q P (P.support ∪ Q.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem fockQ_self_nonneg {σ : Type*} (P : MvPolynomial σ ℚ) : 0 ≤ fockQ P P := by
  unfold fockQ
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (mul_self_nonneg (P.coeff m)) (Nat.cast_nonneg _)

theorem fockQ_self_pos_of_ne_zero {σ : Type*} {P : MvPolynomial σ ℚ} (hP : P ≠ 0) :
    0 < fockQ P P := by
  have hne : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨m, hm⟩ := hne
  have hcm : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hterm_pos : 0 < P.coeff m * P.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) :=
    mul_pos (mul_self_pos.mpr hcm) (Nat.cast_pos.mpr (Finset.prod_pos fun _ _ => Nat.factorial_pos _))
  unfold fockQ
  exact lt_of_lt_of_le hterm_pos
    (Finset.single_le_sum
      (f := fun m' => P.coeff m' * P.coeff m' * ((∏ k ∈ m'.support, (m' k).factorial : ℕ) : ℚ))
      (fun m' _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)) hm)

theorem fockC_eq_sum {σ : Type*} (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    fockC P Q = ∑ m ∈ S, P.coeff m * star (Q.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockC
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]; ring

theorem fockC_conj_symm {σ : Type*} (P Q : MvPolynomial σ ℂ) :
    star (fockC P Q) = fockC Q P := by
  classical
  rw [fockC_eq_sum P Q (P.support ∪ Q.support) Finset.subset_union_left,
    fockC_eq_sum Q P (P.support ∪ Q.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_natCast, starRingEnd_self_apply]
  ring

theorem fockC_add_left {σ : Type*} (P₁ P₂ Q : MvPolynomial σ ℂ) :
    fockC (P₁ + P₂) Q = fockC P₁ Q + fockC P₂ Q := by
  classical
  let S := P₁.support ∪ P₂.support
  have hsub : (P₁ + P₂).support ⊆ S := MvPolynomial.support_add
  rw [fockC_eq_sum _ Q S hsub, fockC_eq_sum P₁ Q S Finset.subset_union_left,
    fockC_eq_sum P₂ Q S Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fockC_add_right {σ : Type*} (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    fockC P (Q₁ + Q₂) = fockC P Q₁ + fockC P Q₂ := by
  have h := congrArg star (fockC_add_left Q₁ Q₂ P)
  rw [star_add, fockC_conj_symm, fockC_conj_symm, fockC_conj_symm] at h
  exact h

theorem fockC_smul_left {σ : Type*} (a : ℂ) (P Q : MvPolynomial σ ℂ) :
    fockC (a • P) Q = a * fockC P Q := by
  rw [fockC_eq_sum (a • P) Q P.support MvPolynomial.support_smul, fockC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

theorem fockC_smul_right {σ : Type*} (a : ℂ) (P Q : MvPolynomial σ ℂ) :
    fockC P (a • Q) = star a * fockC P Q := by
  have h := congrArg star (fockC_smul_left a Q P)
  rw [star_mul', fockC_conj_symm, fockC_conj_symm] at h
  rw [h, mul_comm]

theorem fockC_zero_left {σ : Type*} (Q : MvPolynomial σ ℂ) : fockC 0 Q = 0 := by
  simp [fockC]

theorem fockC_zero_right {σ : Type*} (P : MvPolynomial σ ℂ) : fockC P 0 = 0 := by
  simp [fockC]

theorem fockC_self_eq_real {σ : Type*} (P : MvPolynomial σ ℂ) :
    fockC P P = ((∑ m ∈ P.support, Complex.normSq (P.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold fockC
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.star_def, Complex.mul_conj]

theorem fockC_self_re_eq {σ : Type*} (P : MvPolynomial σ ℂ) :
    (fockC P P).re = ∑ m ∈ P.support, Complex.normSq (P.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) := by
  rw [fockC_self_eq_real, Complex.ofReal_re]

theorem fockC_self_im_zero {σ : Type*} (P : MvPolynomial σ ℂ) : (fockC P P).im = 0 := by
  rw [fockC_self_eq_real, Complex.ofReal_im]

theorem fockC_self_eq_ofReal_re {σ : Type*} (P : MvPolynomial σ ℂ) :
    fockC P P = ((fockC P P).re : ℂ) :=
  Complex.ext rfl (fockC_self_im_zero P)

theorem fockC_self_re_nonneg {σ : Type*} (P : MvPolynomial σ ℂ) : 0 ≤ (fockC P P).re := by
  rw [fockC_self_re_eq]
  exact Finset.sum_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fockC_self_re_pos_of_ne_zero {σ : Type*} {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    0 < (fockC P P).re := by
  rw [fockC_self_re_eq]
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hP
  have hcm : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hterm : 0 < Complex.normSq (P.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) :=
    mul_pos (Complex.normSq_pos.mpr hcm)
      (Nat.cast_pos.mpr (Finset.prod_pos fun _ _ => Nat.factorial_pos _))
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum
      (f := fun m' => Complex.normSq (P.coeff m') * ((∏ k ∈ m'.support, (m' k).factorial : ℕ) : ℝ))
      (fun _ _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)) hm)

/-- **Cauchy–Schwarz Inequality in Multivariable Fock Space (`fockC_cauchy_schwarz`)**:
`Complex.normSq (fockC P Q) ≤ (fockC P P).re * (fockC Q Q).re`. -/
theorem fockC_cauchy_schwarz {σ : Type*} (P Q : MvPolynomial σ ℂ) :
    Complex.normSq (fockC P Q) ≤ (fockC P P).re * (fockC Q Q).re := by
  by_cases hQ : Q = 0
  · subst hQ; simp [fockC_zero_right]
  · have hQQ : 0 < (fockC Q Q).re := fockC_self_re_pos_of_ne_zero hQ
    let α : ℂ := -(fockC P Q) / ((fockC Q Q).re : ℂ)
    have hnn : 0 ≤ (fockC (P + α • Q) (P + α • Q)).re := fockC_self_re_nonneg _
    have hexp : fockC (P + α • Q) (P + α • Q) =
        fockC P P + star α * fockC P Q + α * fockC Q P + α * star α * fockC Q Q := by
      rw [fockC_add_left, fockC_add_right, fockC_add_right, fockC_smul_left, fockC_smul_right,
        fockC_smul_left, fockC_smul_right]
      ring
    have hQQC : fockC Q Q = ((fockC Q Q).re : ℂ) := fockC_self_eq_ofReal_re Q
    have hQP : fockC Q P = star (fockC P Q) := (fockC_conj_symm P Q).symm
    have hQQne : ((fockC Q Q).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQQ.ne'
    have hsimp : fockC (P + α • Q) (P + α • Q) =
        fockC P P - ((Complex.normSq (fockC P Q) / (fockC Q Q).re : ℝ) : ℂ) := by
      rw [hexp, hQQC, hQP]
      have hαstar : star α = -star (fockC P Q) / ((fockC Q Q).re : ℂ) := by
        simp [α]
      rw [hαstar]
      simp only [α]
      have hns : fockC P Q * star (fockC P Q) = (Complex.normSq (fockC P Q) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj]
      rw [Complex.ofReal_div]
      field_simp [hQQne]
      linear_combination -(fockC Q Q).re * hns
    rw [hsimp, Complex.sub_re, Complex.ofReal_re] at hnn
    have := mul_le_mul_of_nonneg_right hnn hQQ.le
    rw [sub_mul, div_mul_cancel₀ _ hQQ.ne'] at this
    linarith

/-! ### Multinomial Factorization Lower Bound & Weighted Cauchy–Binet -/

/-- Elementary multinomial factorial bound:
for any `n : ℕ` and `f : Fin n → ℕ`, `(∑ i, f i)! ≤ n ^ (∑ i, f i) * ∏ i, (f i)!`. -/
theorem multinomial_factorial_le_pow :
    ∀ (n : ℕ) (f : Fin n → ℕ),
      (∑ i : Fin n, f i).factorial ≤ n ^ (∑ i : Fin n, f i) * ∏ i : Fin n, (f i).factorial := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ k ih =>
    intro f
    rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]
    set S := ∑ i : Fin k, f i.castSucc
    set a := f (Fin.last k)
    have hbin : (S + a).choose S * k ^ S ≤ (k + 1) ^ (S + a) := by
      have h1 := add_pow (k : ℕ) 1 (S + a)
      have hterm : (S + a).choose S * k ^ S * 1 ^ (S + a - S) ≤
          ∑ m ∈ Finset.range (S + a + 1), k ^ m * 1 ^ (S + a - m) * (S + a).choose m := by
        have hmem : S ∈ Finset.range (S + a + 1) := Finset.mem_range.mpr (by omega)
        have hle := Finset.single_le_sum (f := fun m => k ^ m * 1 ^ (S + a - m) * (S + a).choose m)
          (fun _ _ => Nat.zero_le _) hmem
        calc (S + a).choose S * k ^ S * 1 ^ (S + a - S)
            = k ^ S * 1 ^ (S + a - S) * (S + a).choose S := by ring
          _ ≤ _ := hle
      rw [one_pow, mul_one] at hterm
      exact hterm.trans h1.symm.le
    have hch : (S + a).choose S * S.factorial * a.factorial = (S + a).factorial := by
      have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right S a)
      rwa [Nat.add_sub_cancel_left] at h
    have hih := ih (fun i : Fin k => f i.castSucc)
    calc (S + a).factorial
        = (S + a).choose S * S.factorial * a.factorial := hch.symm
      _ ≤ (S + a).choose S * (k ^ S * ∏ i : Fin k, (f i.castSucc).factorial) * a.factorial :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hih)
      _ = ((S + a).choose S * k ^ S) * ((∏ i : Fin k, (f i.castSucc).factorial) * a.factorial) := by
          ring
      _ ≤ (k + 1) ^ (S + a) * ((∏ i : Fin k, (f i.castSucc).factorial) * a.factorial) :=
          Nat.mul_le_mul_right _ hbin

/-- **Multinomial Factorization Lower Bound (`monomial_factorization_lower`)**
(Alpöge `PI.SlopeSteps.MonoFactLow`):
for any monomial `m : Fin N × Fin N →₀ ℕ` with column sums `∑ a, m (a, s) = ν s`,
`∏ s, (ν s)! ≤ N ^ (∑ s, ν s) * ∏ k ∈ m.support, (m k)!`. -/
theorem monomial_factorization_lower (N : ℕ) (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ)
    (hcol : ∀ s : Fin N, ∑ a : Fin N, m (a, s) = ν s) :
    ∏ s : Fin N, (ν s).factorial ≤
      N ^ (∑ s : Fin N, ν s) * ∏ k ∈ m.support, (m k).factorial := by
  have hprod_supp : ∏ k ∈ m.support, (m k).factorial =
      ∏ s : Fin N, ∏ a : Fin N, (m (a, s)).factorial := by
    have hall : ∏ k ∈ m.support, (m k).factorial = ∏ k : Fin N × Fin N, (m k).factorial := by
      refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
      have h0 : m k = 0 := Finsupp.notMem_support_iff.mp hk
      simp [h0]
    rw [hall, Fintype.prod_prod_type_right]
  rw [hprod_supp, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  rw [← hcol s]
  exact multinomial_factorial_le_pow N (fun a => m (a, s))

/-- Rectangular Cauchy–Binet expansion over any commutative ring `R`. -/
theorem det_mul_rect' {R : Type*} [CommRing R] {k : ℕ} {n : Type*} [Fintype n]
    (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) :
    (A * B).det = ∑ f : Fin k → n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply, Matrix.mul_apply, Fintype.prod_sum, Finset.smul_sum,
    Matrix.submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]
  ring

private lemma sum_comp_perm' {M : Type*} [AddCommMonoid M] {k : ℕ} {n : Type*} [Fintype n]
    [DecidableEq n] (F : (Fin k → n) → M) (τ : Equiv.Perm (Fin k)) :
    ∑ f : Fin k → n, F (fun i => f (τ i)) = ∑ f, F f :=
  Equiv.sum_comp (Equiv.arrowCongr τ.symm (Equiv.refl n)) F

/-- **Weighted Cauchy–Binet Determinant Identity (`factorial_mul_det_gram_cauchy_binet`)**:
`(k!) * det (Vᵀ * diagonal q * V) = ∑_{f : Fin k → n} (∏_i q (f i)) * det (V.submatrix f id) * det (Vᵀ.submatrix id f)`. -/
theorem factorial_mul_det_gram_cauchy_binet {R : Type*} [CommRing R] (k : ℕ) {n : Type*} [Fintype n]
    [DecidableEq n] (q : n → R) (V : Matrix n (Fin k) R) :
    (k.factorial : R) * (Vᵀ * Matrix.diagonal q * V).det =
      ∑ f : Fin k → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (Vᵀ.submatrix id f).det) := by
  have hexp : (Vᵀ * Matrix.diagonal q * V).det = ∑ f : Fin k → n, (∏ i, q (f i)) *
      ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det) := by
    rw [Matrix.mul_assoc, det_mul_rect']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [Matrix.diagonal_mul, Finset.prod_mul_distrib, mul_assoc]
  have hk : (k.factorial : R) = ∑ _τ : Equiv.Perm (Fin k), (1 : R) := by
    simp [Fintype.card_perm]
  have step : ∀ τ : Equiv.Perm (Fin k),
      (1 : R) * ∑ f : Fin k → n, (∏ i, q (f i)) * ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det) =
      ∑ f : Fin k → n, (∏ i, q (f i)) *
        ((∏ i, V (f (τ i)) i) * ((Vᵀ.submatrix id f).submatrix id τ).det) := by
    intro τ
    rw [one_mul, ← sum_comp_perm' _ τ]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Equiv.prod_comp τ (fun i => q (f i))]
    rfl
  rw [hexp, hk, Finset.sum_mul, Finset.sum_congr rfl fun τ _ => step τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Matrix.det_apply (V.submatrix f id), Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Matrix.det_permute']
  simp only [Matrix.submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
  ring

/-- **Weighted Cauchy–Binet Determinant Square Identity (`factorial_mul_det_sq`)**:
for any commutative ring `R`, diagonal weight `q : n → R`, and `V : Matrix n (Fin k) R`:
`k! * det (Vᵀ * diagonal q * V) = ∑_{f : Fin k → n} (∏_i q (f i)) * (det (V.submatrix f id))^2`. -/
theorem factorial_mul_det_sq {R : Type*} [CommRing R] (k : ℕ) {n : Type*} [Fintype n]
    [DecidableEq n] (q : n → R) (V : Matrix n (Fin k) R) :
    (k.factorial : R) * (Vᵀ * Matrix.diagonal q * V).det =
      ∑ f : Fin k → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (V.submatrix f id).det) := by
  rw [factorial_mul_det_gram_cauchy_binet]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]

/-- **Integer-Matrix Weighted Gram Determinant Lower Bound (`det_gram_weighted_ge_pow_of_int`)**:
if `Vz : Matrix n (Fin r) ℤ` has linearly independent columns over `ℚ` (via `V := Vz.map (Int.castRingHom ℚ)`)
and `0 ≤ A ≤ q m` for all `m : n`, then `A ^ r ≤ (Vᵀ * diagonal q * V).det`. -/
theorem det_gram_weighted_ge_pow_of_int {r : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (Vz : Matrix n (Fin r) ℤ) (q : n → ℚ) {A : ℚ} (hA0 : 0 ≤ A) (hqA : ∀ m : n, A ≤ q m)
    (hli : LinearIndependent ℚ (fun j : Fin r => fun m : n => (Vz m j : ℚ))) :
    A ^ r ≤ ((Vz.map (Int.castRingHom ℚ))ᵀ * Matrix.diagonal q * (Vz.map (Int.castRingHom ℚ))).det := by
  let V : Matrix n (Fin r) ℚ := Vz.map (Int.castRingHom ℚ)
  have hfac : (0 : ℚ) < (r.factorial : ℚ) := Nat.cast_pos.mpr (Nat.factorial_pos r)
  have hidq := factorial_mul_det_sq r q V
  have hid1 := factorial_mul_det_sq r (fun _ => (1 : ℚ)) V
  rw [Matrix.diagonal_one, Matrix.mul_one] at hid1
  simp only [Finset.prod_const_one, one_mul] at hid1
  have hVV_pos : 0 < (Vᵀ * V).det := by
    have hne : ∃ f : Fin r → n, (V.submatrix f id).det ≠ 0 := by
      by_contra hall
      push Not at hall
      -- If all r×r minors vanish, Vᵀ * V has det 0, contradicting hli!
      have hdet0 : (Vᵀ * V).det = 0 := by
        have hsum0 : ∑ f : Fin r → n, (V.submatrix f id).det * (V.submatrix f id).det = 0 :=
          Finset.sum_eq_zero fun f _ => by rw [hall f, mul_zero]
        rw [hsum0] at hid1
        exact (mul_eq_zero.mp hid1).resolve_left hfac.ne'
      obtain ⟨v, hv0, hVv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      have hVmul : V.mulVec v = 0 := by
        have hdot : dotProduct (V.mulVec v) (V.mulVec v) = 0 := by
          have hstep1 : dotProduct (V.mulVec v) (V.mulVec v) =
              dotProduct v (Vᵀ.mulVec (V.mulVec v)) := by
            simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
              Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun i _ =>
                Finset.sum_congr rfl fun k _ => by ring
          calc dotProduct (V.mulVec v) (V.mulVec v)
              = dotProduct v (Vᵀ.mulVec (V.mulVec v)) := hstep1
            _ = dotProduct v ((Vᵀ * V).mulVec v) := by rw [Matrix.mulVec_mulVec]
            _ = dotProduct v 0 := by rw [hVv]
            _ = 0 := dotProduct_zero v
        funext m
        have hsum : ∑ i : n, (V.mulVec v i) ^ 2 = 0 := by
          simpa [dotProduct, sq] using hdot
        have hm0 : (V.mulVec v m) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum m (Finset.mem_univ m)
        exact sq_eq_zero_iff.mp hm0
      have hcomb : ∑ j : Fin r, v j • (fun m : n => (Vz m j : ℚ)) = 0 := by
        funext m
        have := congrFun hVmul m
        simpa [Matrix.mulVec, dotProduct, V, mul_comm] using this
      have hvzero : v = 0 := funext fun j =>
        Fintype.linearIndependent_iff.mp hli v hcomb j
      exact hv0 hvzero
    obtain ⟨f, hf⟩ := hne
    have hsum_pos : 0 < ∑ g : Fin r → n, (V.submatrix g id).det * (V.submatrix g id).det :=
      lt_of_lt_of_le (mul_self_pos.mpr hf)
        (Finset.single_le_sum (f := fun g : Fin r → n => (V.submatrix g id).det * (V.submatrix g id).det)
          (fun g _ => mul_self_nonneg _) (Finset.mem_univ f))
    nlinarith
  have hVV_int : (Vᵀ * V).det = (((Vzᵀ * Vz).det : ℤ) : ℚ) := by
    have hmap : Vᵀ * V = (Int.castRingHom ℚ).mapMatrix (Vzᵀ * Vz) := by
      ext i j
      simp [V, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hmap, ← RingHom.map_det]
    rfl
  have hVV_ge_one : (1 : ℚ) ≤ (Vᵀ * V).det := by
    rw [hVV_int] at hVV_pos ⊢
    have hz : (0 : ℤ) < (Vzᵀ * Vz).det := by exact_mod_cast hVV_pos
    exact_mod_cast (show (1 : ℤ) ≤ (Vzᵀ * Vz).det by omega)
  have hsum_ge : A ^ r * (∑ f : Fin r → n, (V.submatrix f id).det * (V.submatrix f id).det) ≤
      ∑ f : Fin r → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (V.submatrix f id).det) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (mul_self_nonneg _)
    calc A ^ r = ∏ _i : Fin r, A := by simp
      _ ≤ ∏ i : Fin r, q (f i) := Finset.prod_le_prod (fun _ _ => hA0) (fun i _ => hqA (f i))
  rw [← hidq, ← hid1] at hsum_ge
  have hmul : (r.factorial : ℚ) * (A ^ r * (Vᵀ * V).det) ≤
      (r.factorial : ℚ) * (Vᵀ * Matrix.diagonal q * V).det := by linarith
  have h1 : A ^ r * (Vᵀ * V).det ≤ (Vᵀ * Matrix.diagonal q * V).det :=
    le_of_mul_le_mul_left hmul hfac
  calc A ^ r = A ^ r * 1 := (mul_one _).symm
    _ ≤ A ^ r * (Vᵀ * V).det := mul_le_mul_of_nonneg_left hVV_ge_one (pow_nonneg hA0 r)
    _ ≤ (Vᵀ * Matrix.diagonal q * V).det := h1

/-! ### Concrete Leading Principal Minors, Highest-Weight Vectors & `standard_slope_lower` -/

/-- Concrete `k × k` leading principal minor of the generic `N × N` variable matrix `X_{i,j}`
in `MvPolynomial (Fin N × Fin N) R`. -/
def lpMinor (R : Type*) [CommRing R] (N k : ℕ) (hk : k ≤ N) :
    MvPolynomial (Fin N × Fin N) R :=
  (Matrix.of fun (i j : Fin k) =>
    MvPolynomial.X (R := R) (⟨i.1, lt_of_lt_of_le i.2 hk⟩, ⟨j.1, lt_of_lt_of_le j.2 hk⟩)).det

/-- Evaluating `lpMinor R N k` on the identity matrix `δ_{i,j}` equals `1`. -/
theorem eval_id_lpMinor (R : Type*) [CommRing R] (N k : ℕ) (hk : k ≤ N) :
    MvPolynomial.eval (fun p : Fin N × Fin N => if p.1 = p.2 then (1 : R) else 0)
      (lpMinor R N k hk) = 1 := by
  unfold lpMinor
  rw [RingHom.map_det]
  have hM : (MvPolynomial.eval (fun p : Fin N × Fin N => if p.1 = p.2 then (1 : R) else 0)).mapMatrix
      (Matrix.of fun (i j : Fin k) =>
        MvPolynomial.X (R := R) (⟨i.1, lt_of_lt_of_le i.2 hk⟩, ⟨j.1, lt_of_lt_of_le j.2 hk⟩)) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : (⟨i.1, lt_of_lt_of_le i.2 hk⟩ : Fin N) ≠ ⟨j.1, lt_of_lt_of_le j.2 hk⟩ :=
        fun heq => h (Fin.ext (Fin.mk.inj heq))
      simp [h, h']
  rw [hM, Matrix.det_one]

/-- Concrete highest-weight polynomial `hwPoly R N ν = ∏_{k=1}^N (det_{k×k})^{ν_{k-1} - ν_k}`
for a partition `ν : Fin N → ℕ`. -/
def hwPoly (R : Type*) [CommRing R] (N : ℕ) (ν : Fin N → ℕ) :
    MvPolynomial (Fin N × Fin N) R :=
  ∏ i : Fin N,
    lpMinor R N (i.1 + 1) i.2 ^
      (if h : i.1 + 1 < N then ν i - ν ⟨i.1 + 1, h⟩ else ν i)

theorem eval_id_hwPoly (R : Type*) [CommRing R] (N : ℕ) (ν : Fin N → ℕ) :
    MvPolynomial.eval (fun p : Fin N × Fin N => if p.1 = p.2 then (1 : R) else 0)
      (hwPoly R N ν) = 1 := by
  unfold hwPoly
  rw [map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [map_pow, eval_id_lpMinor, one_pow]

theorem hwPoly_ne_zero (R : Type*) [CommRing R] [Nontrivial R] (N : ℕ) (ν : Fin N → ℕ) :
    hwPoly R N ν ≠ 0 := by
  intro h0
  have h := eval_id_hwPoly R N ν
  rw [h0, map_zero] at h
  exact zero_ne_one h

theorem fockQ_hwPoly_pos (N : ℕ) (ν : Fin N → ℕ) :
    0 < fockQ (hwPoly ℚ N ν) (hwPoly ℚ N ν) :=
  fockQ_self_pos_of_ne_zero (hwPoly_ne_zero ℚ N ν)

/-- Normalized Fock Gram matrix of an integral polynomial basis `e : Fin r → MvPolynomial (Fin N × Fin N) ℤ`,
normalized by `hNorm : ℚ` (matching `PI.stdGram` / `PI.SlopeSteps.gramOf`). -/
def stdFockGram (N : ℕ) (hNorm : ℚ) {r : ℕ}
    (e : Fin r → MvPolynomial (Fin N × Fin N) ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    fockQ (MvPolynomial.map (Int.castRingHom ℚ) (e i))
      (MvPolynomial.map (Int.castRingHom ℚ) (e j)) / hNorm

/-- Normalized highest-weight Fock constant `cNu N ν hNorm = hNorm / ∏_s (ν s)!`
(matching `PI.cNu`). -/
def cNu (N : ℕ) (ν : Fin N → ℕ) (hNorm : ℚ) : ℝ :=
  (hNorm : ℝ) / ∏ s : Fin N, ((ν s).factorial : ℝ)

/-- Column-weight-`ν` support condition for integral polynomials in `MvPolynomial (Fin N × Fin N) ℤ`. -/
def HasColWeight (N : ℕ) (ν : Fin N → ℕ) (P : MvPolynomial (Fin N × Fin N) ℤ) : Prop :=
  ∀ m ∈ P.support, ∀ s : Fin N, ∑ a : Fin N, m (a, s) = ν s

/-- **Unconditional Dual-Weyl Gram Determinant Lower Bound (`nabla_gram_lower_bound`)**:
for ANY `ℤ`-linearly-independent family `e : Fin r → MvPolynomial (Fin N × Fin N) ℤ` supported on
column-weight-`ν` monomials and any `hNorm > 0`:
`((∏ s, (ν s)!) / (N^(∑ s, ν s) * hNorm))^r ≤ (stdFockGram N hNorm e).det`! -/
theorem nabla_gram_lower_bound (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hNorm : ℚ) (hh : 0 < hNorm)
    {r : ℕ} (e : Fin r → MvPolynomial (Fin N × Fin N) ℤ)
    (hcol : ∀ i : Fin r, HasColWeight N ν (e i))
    (hli : LinearIndependent ℤ e) :
    (((∏ s : Fin N, (ν s).factorial : ℕ) : ℚ) /
      ((N : ℚ) ^ (∑ s : Fin N, ν s) * hNorm)) ^ r ≤
    (stdFockGram N hNorm e).det := by
  classical
  have hNpow : (0 : ℚ) < (N : ℚ) ^ (∑ s : Fin N, ν s) :=
    pow_pos (Nat.cast_pos.mpr hN) _
  set A : ℚ := ((∏ s : Fin N, (ν s).factorial : ℕ) : ℚ) /
    ((N : ℚ) ^ (∑ s : Fin N, ν s) * hNorm)
  have hA0 : 0 ≤ A := div_nonneg (Nat.cast_nonneg _) (mul_pos hNpow hh).le
  set S : Finset (Fin N × Fin N →₀ ℕ) := Finset.univ.biUnion fun i => (e i).support
  set Vz : Matrix S (Fin r) ℤ := Matrix.of fun m i => (e i).coeff m.1
  set V : Matrix S (Fin r) ℚ := Vz.map (Int.castRingHom ℚ)
  set q : S → ℚ := fun m => ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) / hNorm
  have hG : stdFockGram N hNorm e = Vᵀ * Matrix.diagonal q * V := by
    ext i j
    have hsub : (MvPolynomial.map (Int.castRingHom ℚ) (e i)).support ⊆ S :=
      (MvPolynomial.support_map_subset _ _).trans
        (Finset.subset_biUnion_of_mem (fun k => (e k).support) (Finset.mem_univ i))
    simp only [stdFockGram, Matrix.of_apply]
    rw [fockQ_eq_sum _ _ S hsub, Finset.sum_div, ← Finset.sum_coe_sort S, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, V, Vz, Matrix.map_apply,
      Matrix.of_apply, q, MvPolynomial.coeff_map, eq_intCast]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hqA : ∀ m : S, A ≤ q m := by
    intro m
    obtain ⟨i, -, hm⟩ := Finset.mem_biUnion.mp m.2
    have hT1 := monomial_factorization_lower N ν m.1 (hcol i m.1 hm)
    have hT1q : ((∏ s : Fin N, (ν s).factorial : ℕ) : ℚ) ≤
        (N : ℚ) ^ (∑ s : Fin N, ν s) * ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) := by
      exact_mod_cast hT1
    rw [div_le_div_iff₀ (mul_pos hNpow hh) hh]
    calc ((∏ s : Fin N, (ν s).factorial : ℕ) : ℚ) * hNorm
        ≤ (N : ℚ) ^ (∑ s : Fin N, ν s) *
            ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) * hNorm :=
          mul_le_mul_of_nonneg_right hT1q hh.le
      _ = ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) *
            ((N : ℚ) ^ (∑ s : Fin N, ν s) * hNorm) := by ring
  have hliQ : LinearIndependent ℚ (fun j : Fin r => fun m : S => (Vz m j : ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    let D : ℕ := ∏ i : Fin r, (c i).den
    have hDpos : 0 < D := Finset.prod_pos fun i _ => (c i).pos
    have hDR : (0 : ℚ) < (D : ℚ) := Nat.cast_pos.mpr hDpos
    have hmul_int : ∀ i : Fin r, ∃ z : ℤ, (D : ℚ) * c i = (z : ℚ) := fun i => by
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun a : Fin r => (c a).den) (Finset.mem_univ i)
      refine ⟨(c i).num * (k : ℤ), ?_⟩
      have hci : c i = ((c i).num : ℚ) / ((c i).den : ℚ) := (Rat.num_div_den (c i)).symm
      have hDk : (D : ℚ) = ((c i).den : ℚ) * (k : ℚ) := by
        change ((∏ a : Fin r, (c a).den : ℕ) : ℚ) = _
        rw [hk, Nat.cast_mul]
      have hd0 : ((c i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (c i).pos.ne'
      have hcd : c i * ((c i).den : ℚ) = ((c i).num : ℚ) := by
        calc c i * ((c i).den : ℚ)
            = (((c i).num : ℚ) / ((c i).den : ℚ)) * ((c i).den : ℚ) :=
                congrArg (· * ((c i).den : ℚ)) hci
          _ = ((c i).num : ℚ) := div_mul_cancel₀ _ hd0
      calc (D : ℚ) * c i
          = ((c i).den : ℚ) * (k : ℚ) * c i := by rw [hDk]
        _ = (c i * ((c i).den : ℚ)) * (k : ℚ) := by ring
        _ = ((c i).num : ℚ) * (k : ℚ) := by rw [hcd]
        _ = (((c i).num * (k : ℤ) : ℤ) : ℚ) := by push_cast; ring
    choose z hz using hmul_int
    have hcombZ : ∑ i : Fin r, z i • e i = 0 := by
      ext m
      rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum]
      by_cases hm : m ∈ S
      · have hmQ := congrFun hc ⟨m, hm⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Vz,
          Matrix.of_apply] at hmQ
        have hmulQ : (D : ℚ) * (∑ i : Fin r, c i * (((e i).coeff m : ℤ) : ℚ)) = 0 := by
          rw [hmQ, mul_zero]
        rw [Finset.mul_sum] at hmulQ
        have hsumZ : ((∑ i : Fin r, z i * (e i).coeff m : ℤ) : ℚ) = 0 := by
          rw [Int.cast_sum]
          refine (Finset.sum_congr rfl fun i _ => ?_).trans hmulQ
          rw [Int.cast_mul, ← hz i]; ring
        have h0 : ∑ i : Fin r, z i * (e i).coeff m = 0 := by exact_mod_cast hsumZ
        simp only [MvPolynomial.coeff_smul, smul_eq_mul]
        exact h0
      · refine Finset.sum_eq_zero fun i _ => ?_
        have hnot : m ∉ (e i).support := fun hi =>
          hm (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
        rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.mp hnot, smul_zero]
    have hzj : z j = 0 := Fintype.linearIndependent_iff.mp hli z hcombZ j
    have hcj : (D : ℚ) * c j = 0 := by rw [hz j, hzj, Int.cast_zero]
    exact (mul_eq_zero.mp hcj).resolve_left hDR.ne'
  rw [hG]
  exact det_gram_weighted_ge_pow_of_int Vz q hA0 hqA hliQ

/-- **MAIN EXPORT #5 — Unconditional Standard Weyl-Lattice Slope Lower Bound (`standard_slope_lower`)**
(Alpöge `PI.StdSlopeLow`):
for any `N > 0`, partition `ν : Fin N → ℕ`, positive Fock normalization `hNorm : ℚ`, rank `r > 0`,
Weyl basis `eWeyl` and dual-Weyl basis `eDual` (supported on column-weight-`ν` monomials) satisfying
Gram duality `(stdFockGram N hNorm eWeyl).det * (stdFockGram N hNorm eDual).det = 1`,
with standard slope `μ = -Real.log ((stdFockGram N hNorm eWeyl).det : ℝ) / r`:
**`-((∑ s : Fin N, (ν s : ℝ)) * Real.log (N : ℝ) + Real.log (cNu N ν hNorm)) ≤ μ`**! -/
theorem standard_slope_lower (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ) (hNorm : ℚ) (hh : 0 < hNorm)
    {r : ℕ} (hr : 0 < r)
    (eWeyl eDual : Fin r → MvPolynomial (Fin N × Fin N) ℤ)
    (hcol : ∀ i : Fin r, HasColWeight N ν (eDual i))
    (hliDual : LinearIndependent ℤ eDual)
    (hdual : (stdFockGram N hNorm eWeyl).det * (stdFockGram N hNorm eDual).det = 1)
    {μ : ℝ} (hμ : μ = -Real.log ((stdFockGram N hNorm eWeyl).det : ℝ) / (r : ℝ)) :
    -((∑ s : Fin N, (ν s : ℝ)) * Real.log (N : ℝ) + Real.log (cNu N ν hNorm)) ≤ μ := by
  have hlow := nabla_gram_lower_bound N hN ν hNorm hh eDual hcol hliDual
  have hprod_pos : (0 : ℝ) < ∏ s : Fin N, ((ν s).factorial : ℝ) :=
    Finset.prod_pos fun s _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hhR : (0 : ℝ) < (hNorm : ℝ) := Rat.cast_pos.mpr hh
  have hcNu_pos : 0 < cNu N ν hNorm := div_pos hhR hprod_pos
  have hA_pos : (0 : ℝ) < ((∏ s : Fin N, (ν s).factorial : ℕ) : ℝ) /
      ((N : ℝ) ^ (∑ s : Fin N, ν s) * (hNorm : ℝ)) :=
    div_pos (Nat.cast_pos.mpr (Finset.prod_pos fun _ _ => Nat.factorial_pos _))
      (mul_pos (pow_pos hNpos _) hhR)
  have hlowR : (((∏ s : Fin N, (ν s).factorial : ℕ) : ℝ) /
      ((N : ℝ) ^ (∑ s : Fin N, ν s) * (hNorm : ℝ))) ^ r ≤
      ((stdFockGram N hNorm eDual).det : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hlow
    simpa [Rat.cast_pow, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast] using h
  have hdetDual_pos : (0 : ℝ) < ((stdFockGram N hNorm eDual).det : ℝ) :=
    lt_of_lt_of_le (pow_pos hA_pos r) hlowR
  have hdualR : ((stdFockGram N hNorm eWeyl).det : ℝ) *
      ((stdFockGram N hNorm eDual).det : ℝ) = 1 := by
    exact_mod_cast hdual
  have hdetWeyl_pos : (0 : ℝ) < ((stdFockGram N hNorm eWeyl).det : ℝ) := by
    by_contra hle
    push Not at hle
    have : ((stdFockGram N hNorm eWeyl).det : ℝ) *
        ((stdFockGram N hNorm eDual).det : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hdetDual_pos.le
    linarith
  have hlog_dual : Real.log ((stdFockGram N hNorm eWeyl).det : ℝ) +
      Real.log ((stdFockGram N hNorm eDual).det : ℝ) = 0 := by
    rw [← Real.log_mul hdetWeyl_pos.ne' hdetDual_pos.ne', hdualR, Real.log_one]
  have hlog_low : (r : ℝ) * Real.log (((∏ s : Fin N, (ν s).factorial : ℕ) : ℝ) /
      ((N : ℝ) ^ (∑ s : Fin N, ν s) * (hNorm : ℝ))) ≤
      Real.log ((stdFockGram N hNorm eDual).det : ℝ) := by
    have h := Real.log_le_log (pow_pos hA_pos r) hlowR
    rwa [Real.log_pow] at h
  have hlog_A : Real.log (((∏ s : Fin N, (ν s).factorial : ℕ) : ℝ) /
      ((N : ℝ) ^ (∑ s : Fin N, ν s) * (hNorm : ℝ))) =
      -((∑ s : Fin N, (ν s : ℝ)) * Real.log (N : ℝ) + Real.log (cNu N ν hNorm)) := by
    unfold cNu
    rw [Nat.cast_prod, Real.log_div hprod_pos.ne' (mul_pos (pow_pos hNpos _) hhR).ne',
      Real.log_mul (pow_pos hNpos _).ne' hhR.ne', Real.log_pow, Nat.cast_sum,
      Real.log_div hhR.ne' hprod_pos.ne']
    ring
  rw [hlog_A] at hlog_low
  have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  rw [hμ]
  have hneg : -Real.log ((stdFockGram N hNorm eWeyl).det : ℝ) =
      Real.log ((stdFockGram N hNorm eDual).det : ℝ) := by linarith
  rw [hneg, le_div_iff₀ hrR]
  linarith

/-- Explicit corollary combining `standard_slope_lower` with the hook bound
`cNu N ν hNorm ≤ (ν 0 + N)^(N*(N-1)/2)` (Alpöge `PI.HookBound`). -/
theorem standard_slope_lower_of_hook_bound (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ)
    (hNorm : ℚ) (hh : 0 < hNorm) {r : ℕ} (hr : 0 < r)
    (eWeyl eDual : Fin r → MvPolynomial (Fin N × Fin N) ℤ)
    (hcol : ∀ i : Fin r, HasColWeight N ν (eDual i))
    (hliDual : LinearIndependent ℤ eDual)
    (hdual : (stdFockGram N hNorm eWeyl).det * (stdFockGram N hNorm eDual).det = 1)
    {μ : ℝ} (hμ : μ = -Real.log ((stdFockGram N hNorm eWeyl).det : ℝ) / (r : ℝ))
    (hcNu_le : cNu N ν hNorm ≤ ((ν ⟨0, hN⟩ : ℝ) + (N : ℝ)) ^ (N * (N - 1) / 2)) :
    -((∑ s : Fin N, (ν s : ℝ)) * Real.log (N : ℝ) +
        ((N * (N - 1) / 2 : ℕ) : ℝ) * Real.log ((ν ⟨0, hN⟩ : ℝ) + (N : ℝ))) ≤ μ := by
  have hstd := standard_slope_lower N hN ν hNorm hh hr eWeyl eDual hcol hliDual hdual hμ
  have hprod_pos : (0 : ℝ) < ∏ s : Fin N, ((ν s).factorial : ℝ) :=
    Finset.prod_pos fun s _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hcNu_pos : 0 < cNu N ν hNorm := div_pos (Rat.cast_pos.mpr hh) hprod_pos
  have hlog_cNu : Real.log (cNu N ν hNorm) ≤
      ((N * (N - 1) / 2 : ℕ) : ℝ) * Real.log ((ν ⟨0, hN⟩ : ℝ) + (N : ℝ)) := by
    have h := Real.log_le_log hcNu_pos hcNu_le
    rwa [Real.log_pow] at h
  linarith

end FockSpaceAndStandardSlopeLower

/-! ## Section 5: Fock Adjoint Existence, `branching_normalised_of_adjoint` & `branching_link_family_normalised` -/

section BranchingAdjointAndFamilyLink

/-! ### Unconditional Fock-Space Adjoint Construction (`fock_adjoint_exists`) -/

private lemma fockC_orthog_basis_exists {σ : Type*}
    (V : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V] :
    ∃ (d : ℕ) (b : Fin d → V),
      (∀ i j : Fin d, fockC (b i : MvPolynomial σ ℂ) (b j : MvPolynomial σ ℂ) =
        if i = j then 1 else 0) ∧
      (∀ v : V, (v : MvPolynomial σ ℂ) =
        ∑ i : Fin d, fockC (v : MvPolynomial σ ℂ) (b i : MvPolynomial σ ℂ) • (b i : MvPolynomial σ ℂ)) := by
  classical
  let d := Module.finrank ℂ V
  let e : Module.Basis (Fin d) ℂ V := Module.finBasis ℂ V
  -- Construct orthogonal Gram–Schmidt vectors in V by strong recursion on index k ≤ d.
  suffices hGS : ∀ k : ℕ, ∀ hk : k ≤ d,
      ∃ u : Fin k → V,
        (∀ i j : Fin k, fockC (u i : MvPolynomial σ ℂ) (u j : MvPolynomial σ ℂ) =
          if i = j then 1 else 0) ∧
        (∀ i : Fin k, (e ⟨i.1, lt_of_lt_of_le i.2 hk⟩ : V) ∈
          Submodule.span ℂ (Set.range u)) by
    obtain ⟨u, horth, hspan⟩ := hGS d le_rfl
    refine ⟨d, u, horth, fun v => ?_⟩
    have hv_span : v ∈ Submodule.span ℂ (Set.range u) := by
      have hrep := (e.sum_repr v).symm
      rw [hrep]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact hspan i
    rw [Submodule.mem_span_range_iff_exists_fun] at hv_span
    obtain ⟨c, hc⟩ := hv_span
    have hval : (v : MvPolynomial σ ℂ) = ∑ i : Fin d, c i • (u i : MvPolynomial σ ℂ) := by
      have h := congrArg Subtype.val hc.symm
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
    have hcoeff : ∀ j : Fin d, c j = fockC (v : MvPolynomial σ ℂ) (u j : MvPolynomial σ ℂ) := by
      intro j
      rw [hval]
      have hlin : ∀ (s : Finset (Fin d)) (g : Fin d → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ),
          fockC (∑ i ∈ s, g i) q = ∑ i ∈ s, fockC (g i) q := by
        intro s g q
        induction s using Finset.induction_on with
        | empty => simp [fockC_zero_left]
        | insert a s ha ih => rw [Finset.sum_insert ha, fockC_add_left, ih, Finset.sum_insert ha]
      rw [hlin]
      have hterms : ∑ i : Fin d, fockC (c i • (u i : MvPolynomial σ ℂ)) (u j : MvPolynomial σ ℂ) =
          ∑ i : Fin d, c i * (if i = j then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl fun i _ => by rw [fockC_smul_left, horth i j]
      rw [hterms]
      simp
    conv_lhs => rw [hval]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoeff i]
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hmd
    obtain ⟨u, horth, hspan⟩ := ih (Nat.le_of_succ_le hmd)
    let em : V := e ⟨m, hmd⟩
    let w : V := em - ∑ i : Fin m, fockC (em : MvPolynomial σ ℂ) (u i : MvPolynomial σ ℂ) • u i
    have hw_ne : (w : MvPolynomial σ ℂ) ≠ 0 := by
      intro hw0
      have hwV : w = 0 := Subtype.ext hw0
      have hem_mem : em ∈ Submodule.span ℂ (Set.range u) := by
        have heq : em = ∑ i : Fin m, fockC (em : MvPolynomial σ ℂ) (u i : MvPolynomial σ ℂ) • u i :=
          sub_eq_zero.mp hwV
        rw [heq]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      -- Every u i lies in span of {e 0, ..., e (m-1)}? Not needed: prove em ∈ span (e 0..m-1) or use finrank!
      have hcard_lt : Module.finrank ℂ (Submodule.span ℂ (Set.range u)) ≤ m := by
        have hle := finrank_span_le_card (R := ℂ) (Set.range u)
        exact hle.trans (by
          calc (Set.range u).toFinset.card ≤ Fintype.card (Fin m) := by
                have h1 : (Set.range u).toFinset = Finset.univ.image u := by ext x; simp
                rw [h1]
                exact Finset.card_image_le
            _ = m := Fintype.card_fin m)
      have hspan_em : ∀ j : Fin (m + 1), e ⟨j.1, lt_of_lt_of_le j.2 hmd⟩ ∈
          Submodule.span ℂ (Set.range u) := fun j => by
        rcases Fin.lastCases (motive := fun j => e ⟨j.1, lt_of_lt_of_le j.2 hmd⟩ ∈
            Submodule.span ℂ (Set.range u)) hem_mem (fun i => hspan i) j with h
        exact h
      have hli_m1 : LinearIndependent ℂ (fun j : Fin (m + 1) =>
          (⟨e ⟨j.1, lt_of_lt_of_le j.2 hmd⟩, hspan_em j⟩ : Submodule.span ℂ (Set.range u))) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc j
        have hval : ∑ i : Fin (m + 1), c i • e ⟨i.1, lt_of_lt_of_le i.2 hmd⟩ = 0 := by
          have := congrArg Subtype.val hc
          simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using this
        have hinj : Function.Injective (fun i : Fin (m + 1) => (⟨i.1, lt_of_lt_of_le i.2 hmd⟩ : Fin d)) :=
          fun a b hab => Fin.ext (Fin.mk.inj hab)
        exact Fintype.linearIndependent_iff.mp (e.linearIndependent.comp _ hinj) c hval j
      have hfr_ge : m + 1 ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range u)) := by
        simpa [Fintype.card_fin] using hli_m1.fintype_card_le_finrank
      omega
    have hw_pos : 0 < (fockC (w : MvPolynomial σ ℂ) (w : MvPolynomial σ ℂ)).re :=
      fockC_self_re_pos_of_ne_zero hw_ne
    let nrm : ℝ := Real.sqrt (fockC (w : MvPolynomial σ ℂ) (w : MvPolynomial σ ℂ)).re
    have hnrm_pos : 0 < nrm := Real.sqrt_pos.mpr hw_pos
    let um : V := ((nrm⁻¹ : ℝ) : ℂ) • w
    have hsum_left : ∀ (s : Finset (Fin m)) (g : Fin m → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ),
        fockC (∑ i ∈ s, g i) q = ∑ i ∈ s, fockC (g i) q := by
      intro s g q
      induction s using Finset.induction_on with
      | empty => simp [fockC_zero_left]
      | insert a s ha ih => rw [Finset.sum_insert ha, fockC_add_left, ih, Finset.sum_insert ha]
    have hw_orth : ∀ i : Fin m, fockC (w : MvPolynomial σ ℂ) (u i : MvPolynomial σ ℂ) = 0 := by
      intro i
      have hw_coe : (w : MvPolynomial σ ℂ) = (em : MvPolynomial σ ℂ) +
          (-1 : ℂ) • ∑ j : Fin m, fockC (em : MvPolynomial σ ℂ) (u j : MvPolynomial σ ℂ) •
            (u j : MvPolynomial σ ℂ) := by
        simp only [w, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, neg_one_smul]
        abel
      rw [hw_coe, fockC_add_left, fockC_smul_left, hsum_left]
      have hterms : ∑ j : Fin m, fockC (fockC (em : MvPolynomial σ ℂ) (u j : MvPolynomial σ ℂ) •
          (u j : MvPolynomial σ ℂ)) (u i : MvPolynomial σ ℂ) =
          fockC (em : MvPolynomial σ ℂ) (u i : MvPolynomial σ ℂ) := by
        have h1 : ∀ j : Fin m, fockC (fockC (em : MvPolynomial σ ℂ) (u j : MvPolynomial σ ℂ) •
            (u j : MvPolynomial σ ℂ)) (u i : MvPolynomial σ ℂ) =
            fockC (em : MvPolynomial σ ℂ) (u j : MvPolynomial σ ℂ) * (if j = i then 1 else 0) :=
          fun j => by rw [fockC_smul_left, horth j i]
        simp_rw [h1]; simp
      rw [hterms]; ring
    have hum_unit : fockC (um : MvPolynomial σ ℂ) (um : MvPolynomial σ ℂ) = 1 := by
      change fockC (((nrm⁻¹ : ℝ) : ℂ) • (w : MvPolynomial σ ℂ))
        (((nrm⁻¹ : ℝ) : ℂ) • (w : MvPolynomial σ ℂ)) = 1
      rw [fockC_smul_left, fockC_smul_right, Complex.star_def, Complex.conj_ofReal,
        fockC_self_eq_ofReal_re, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      have hsq : nrm * nrm = (fockC (w : MvPolynomial σ ℂ) (w : MvPolynomial σ ℂ)).re :=
        Real.mul_self_sqrt hw_pos.le
      have hcalc : nrm⁻¹ * (nrm⁻¹ * (fockC (w : MvPolynomial σ ℂ) (w : MvPolynomial σ ℂ)).re) = 1 := by
        rw [← hsq]; field_simp [hnrm_pos.ne']
      rw [hcalc, Complex.ofReal_one]
    let u' : Fin (m + 1) → V := Fin.snoc u um
    refine ⟨u', ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · simp [u', hum_unit]
        · have hne : Fin.last m ≠ j'.castSucc := (Fin.castSucc_ne_last j').symm
          simp only [u', Fin.snoc_last, Fin.snoc_castSucc, hne, ↓reduceIte]
          change fockC (((nrm⁻¹ : ℝ) : ℂ) • (w : MvPolynomial σ ℂ)) (u j' : MvPolynomial σ ℂ) = 0
          rw [fockC_smul_left, hw_orth j', mul_zero]
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · simp only [u', Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last, ↓reduceIte]
          have h := congrArg star (show fockC (((nrm⁻¹ : ℝ) : ℂ) • (w : MvPolynomial σ ℂ))
            (u i' : MvPolynomial σ ℂ) = 0 by rw [fockC_smul_left, hw_orth i', mul_zero])
          rw [fockC_conj_symm, star_zero] at h
          exact h
        · simp only [u', Fin.snoc_castSucc, Fin.castSucc_inj]
          exact horth i' j'
    · intro j
      have hsub_span : Submodule.span ℂ (Set.range u) ≤ Submodule.span ℂ (Set.range u') := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i.castSucc, by simp [u']⟩
      refine Fin.lastCases ?_ (fun i => hsub_span (hspan i)) j
      have hw_eq : em = ((nrm : ℝ) : ℂ) • um +
          ∑ i : Fin m, fockC (em : MvPolynomial σ ℂ) (u i : MvPolynomial σ ℂ) • u i := by
        have hum_w : ((nrm : ℝ) : ℂ) • um = w := by
          simp only [um, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnrm_pos.ne',
            Complex.ofReal_one, one_smul]
        rw [hum_w]
        simp only [w, sub_add_cancel]
      change em ∈ Submodule.span ℂ (Set.range u')
      rw [hw_eq]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last m, by simp [u']⟩))
        (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (hsub_span (Submodule.subset_span ⟨i, rfl⟩)))

/-- **Unconditional Fock-Space Adjoint Existence (`fock_adjoint_exists`)**:
for any finite-dimensional `ℂ`-subspace `V ≤ MvPolynomial σ ℂ` and any `ℂ`-linear map
`jl : V →ₗ[ℂ] MvPolynomial τ ℂ`, there exists a `ℂ`-linear map
`P0 : MvPolynomial τ ℂ →ₗ[ℂ] MvPolynomial σ ℂ` landing in `V` such that
`fockC (P0 F) v = fockC F (jl v)` for all `F` and all `v : V`. -/
theorem fock_adjoint_exists {σ τ : Type*}
    (V : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V]
    (jl : V →ₗ[ℂ] MvPolynomial τ ℂ) :
    ∃ P0 : MvPolynomial τ ℂ →ₗ[ℂ] MvPolynomial σ ℂ,
      (∀ F, P0 F ∈ V) ∧
      (∀ F (v : V), fockC (P0 F) (v : MvPolynomial σ ℂ) = fockC F (jl v)) := by
  obtain ⟨d, b, horth, hrep⟩ := fockC_orthog_basis_exists V
  let P0 : MvPolynomial τ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
    { toFun := fun F => ∑ i : Fin d, fockC F (jl (b i)) • (b i : MvPolynomial σ ℂ)
      map_add' := fun F₁ F₂ => by
        simp_rw [fockC_add_left, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a F => by
        simp only [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [fockC_smul_left, smul_smul] }
  have hsum_left : ∀ (s : Finset (Fin d)) (g : Fin d → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ),
      fockC (∑ i ∈ s, g i) q = ∑ i ∈ s, fockC (g i) q := by
    intro s g q
    induction s using Finset.induction_on with
    | empty => simp [fockC_zero_left]
    | insert a s ha ih => rw [Finset.sum_insert ha, fockC_add_left, ih, Finset.sum_insert ha]
  have hsum_right : ∀ (s : Finset (Fin d)) (g : Fin d → MvPolynomial τ ℂ) (p : MvPolynomial τ ℂ),
      fockC p (∑ i ∈ s, g i) = ∑ i ∈ s, fockC p (g i) := by
    intro s g p
    induction s using Finset.induction_on with
    | empty => simp [fockC_zero_right]
    | insert a s ha ih => rw [Finset.sum_insert ha, fockC_add_right, ih, Finset.sum_insert ha]
  refine ⟨P0, fun F => ?_, fun F v => ?_⟩
  · change (∑ i : Fin d, fockC F (jl (b i)) • (b i : MvPolynomial σ ℂ)) ∈ V
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
  have hv_V : v = ∑ i : Fin d, fockC (v : MvPolynomial σ ℂ) (b i : MvPolynomial σ ℂ) • b i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hrep v
  have hP0_bi : ∀ j : Fin d, fockC (P0 F) (b j : MvPolynomial σ ℂ) = fockC F (jl (b j)) := by
    intro j
    change fockC (∑ i : Fin d, fockC F (jl (b i)) • (b i : MvPolynomial σ ℂ))
      (b j : MvPolynomial σ ℂ) = _
    rw [hsum_left]
    have h1 : ∀ i : Fin d, fockC (fockC F (jl (b i)) • (b i : MvPolynomial σ ℂ))
        (b j : MvPolynomial σ ℂ) = fockC F (jl (b i)) * (if i = j then 1 else 0) :=
      fun i => by rw [fockC_smul_left, horth i j]
    simp_rw [h1]; simp
  conv_lhs => rw [hv_V, Submodule.coe_sum]
  conv_rhs => rw [hv_V, map_sum]
  have hsum_right_σ : ∀ (s : Finset (Fin d)) (g : Fin d → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ),
      fockC p (∑ i ∈ s, g i) = ∑ i ∈ s, fockC p (g i) := by
    intro s g p
    induction s using Finset.induction_on with
    | empty => simp [fockC_zero_right]
    | insert a s ha ih => rw [Finset.sum_insert ha, fockC_add_right, ih, Finset.sum_insert ha]
  rw [hsum_right_σ, hsum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, map_smul, fockC_smul_right, fockC_smul_right, hP0_bi i]

/-! ### Diagonal Scaling, Block Matrices, Normalized Fock Metrics & Adjoint Branching -/

/-- Scaling matrix `scaleMat n T = diag(1, ..., 1, √T) ∈ M_{n+1}(ℂ)`. -/
def scaleMat (n T : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal fun i => if i = Fin.last n then ((Real.sqrt T : ℝ) : ℂ) else 1

/-- Block-diagonal embedding `blockMat g = diag(g, 1) ∈ M_{n+1}(ℂ)`. -/
def blockMat {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j =>
    if hi : i.1 < n then
      if hj : j.1 < n then g ⟨i.1, hi⟩ ⟨j.1, hj⟩ else 0
    else
      if j = Fin.last n then 1 else 0

theorem det_scaleMat (n T : ℕ) : (scaleMat n T).det = ((Real.sqrt T : ℝ) : ℂ) := by
  unfold scaleMat
  rw [Matrix.det_diagonal]
  rw [Fin.prod_univ_castSucc]
  have h1 : ∏ i : Fin n, (if (i.castSucc : Fin (n + 1)) = Fin.last n then
      ((Real.sqrt T : ℝ) : ℂ) else 1) = 1 :=
    Finset.prod_eq_one fun i _ => by simp [Fin.castSucc_ne_last]
  rw [h1, one_mul, if_pos rfl]

theorem det_blockMat {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : (blockMat g).det = g.det := by
  let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  have hM : (blockMat g).submatrix e e = Matrix.fromBlocks g 0 0 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [blockMat, e, finSumFinEquiv_apply_left, i.2, j.2]
      | inr j =>
        fin_cases j
        simp [blockMat, e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, i.2]
    | inr i =>
      fin_cases i
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply, blockMat, Matrix.of_apply, Matrix.fromBlocks_apply₂₁,
          Matrix.zero_apply, e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.val_natAdd, add_zero, lt_self_iff_false, ↓reduceDIte]
        have hne : Fin.castAdd 1 j ≠ Fin.last n := by
          intro heq
          have hv := congrArg Fin.val heq
          simp at hv
          omega
        exact if_neg hne
      | inr j =>
        fin_cases j
        simp only [Matrix.submatrix_apply, blockMat, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
          Matrix.one_apply_eq, e, finSumFinEquiv_apply_right, Fin.val_natAdd,
          add_zero, lt_self_iff_false, ↓reduceDIte]
        have heq : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext (by simp)
        exact if_pos heq
  rw [← Matrix.det_submatrix_equiv_self e (blockMat g), hM, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

/-- Integer power of the determinant of `g : GL (Fin N) ℂ`. -/
def detPow {N : ℕ} (g : GL (Fin N) ℂ) (c : ℤ) : ℂ :=
  ((Matrix.GeneralLinearGroup.det g ^ c : ℂˣ) : ℂ)

theorem detPow_add {N : ℕ} (g : GL (Fin N) ℂ) (a b : ℤ) :
    detPow g (a + b) = detPow g a * detPow g b := by
  unfold detPow
  rw [_root_.zpow_add, Units.val_mul]

theorem detPow_zero_dim (g : GL (Fin 0) ℂ) (c : ℤ) : detPow g c = 1 := by
  have h : Matrix.GeneralLinearGroup.det g = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp
  unfold detPow
  rw [h, _root_.one_zpow, Units.val_one]

theorem detPow_blockMat {n : ℕ} (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ)
    (hH : (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ))
    (c : ℤ) : detPow H c = detPow g c := by
  have h : Matrix.GeneralLinearGroup.det H = Matrix.GeneralLinearGroup.det g := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      hH, det_blockMat]
  unfold detPow
  rw [h]

/-- **Concrete Polynomial Weyl-Representation Package (`WeylRepSystem`)**:
encapsulates the polynomial Weyl modules `delSq ℂ N lam` & integral lattices `delSqZ N lam`,
extremal highest-weight vectors `extremal N lam` (normalized via `lam.natW`), and the
`GL_N(ℂ)`-action `sqAct N lam` with determinant-shift covariance `sqAct (shiftW lam c) g f =
detPow g c • sqAct lam g f`. -/
structure WeylRepSystem where
  delSqC : ∀ (N : ℕ), DomWeight N → Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)
  [delSqC_fd : ∀ N lam, FiniteDimensional ℂ (delSqC N lam)]
  delSqZ : ∀ (N : ℕ), DomWeight N → Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)
  extremal : ∀ (N : ℕ), DomWeight N → MvPolynomial (Fin N × Fin N) ℂ
  extremal_ne_zero : ∀ N lam, extremal N lam ≠ 0
  delSqC_shiftW : ∀ N lam (c : ℤ), delSqC N (lam.shiftW c) = delSqC N lam
  delSqZ_shiftW : ∀ N lam (c : ℤ), delSqZ N (lam.shiftW c) = delSqZ N lam
  extremal_shiftW : ∀ N lam (c : ℤ), extremal N (lam.shiftW c) = extremal N lam
  sqAct : ∀ (N : ℕ), DomWeight N → GL (Fin N) ℂ →
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ
  sqAct_shiftW : ∀ N (lam : DomWeight N) (c : ℤ) (g : GL (Fin N) ℂ) f,
    sqAct N (lam.shiftW c) g f = detPow g c • sqAct N lam g f

attribute [instance] WeylRepSystem.delSqC_fd

namespace WeylRepSystem

/-- Normalized Fock Hermitian form `normFock lam f g = fockC f g / fockC (extremal lam) (extremal lam)`. -/
def normFock (W : WeylRepSystem) {N : ℕ} (lam : DomWeight N)
    (f g : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  fockC f g / fockC (W.extremal N lam) (W.extremal N lam)

/-- Twisted Fock squared norm `normTil lt G f = (normFock lt (sqAct lt G f) (sqAct lt G f)).re`. -/
def normTil (W : WeylRepSystem) {n : ℕ} (lt : DomWeight (n + 1)) (G : GL (Fin (n + 1)) ℂ)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) : ℝ :=
  (W.normFock lt (W.sqAct (n + 1) lt G f) (W.sqAct (n + 1) lt G f)).re

theorem fock_extremal_pos (W : WeylRepSystem) {N : ℕ} (lam : DomWeight N) :
    0 < (fockC (W.extremal N lam) (W.extremal N lam)).re :=
  fockC_self_re_pos_of_ne_zero (W.extremal_ne_zero N lam)

theorem normFock_self_re_eq (W : WeylRepSystem) {N : ℕ} (lam : DomWeight N)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    (W.normFock lam f f).re =
      (fockC f f).re / (fockC (W.extremal N lam) (W.extremal N lam)).re := by
  unfold normFock
  conv_lhs => rw [fockC_self_eq_ofReal_re f, fockC_self_eq_ofReal_re (W.extremal N lam),
    ← Complex.ofReal_div, Complex.ofReal_re]

theorem normFock_self_re_nonneg (W : WeylRepSystem) {N : ℕ} (lam : DomWeight N)
    (f : MvPolynomial (Fin N × Fin N) ℂ) : 0 ≤ (W.normFock lam f f).re := by
  rw [W.normFock_self_re_eq]
  exact div_nonneg (fockC_self_re_nonneg f) (W.fock_extremal_pos lam).le

theorem normTil_nonneg (W : WeylRepSystem) {n : ℕ} (lt : DomWeight (n + 1))
    (G : GL (Fin (n + 1)) ℂ) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :
    0 ≤ W.normTil lt G f :=
  W.normFock_self_re_nonneg lt _

theorem normFock_shiftW (W : WeylRepSystem) {N : ℕ} (lam : DomWeight N) (c : ℤ) :
    W.normFock (lam.shiftW c) = W.normFock lam := by
  funext f g
  unfold normFock
  rw [W.extremal_shiftW]

theorem normTil_shiftW (W : WeylRepSystem) {n : ℕ} (lt : DomWeight (n + 1)) (c : ℤ)
    (T : ℕ) (G : GL (Fin (n + 1)) ℂ)
    (hG : (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :
    W.normTil (lt.shiftW c) G f = (T : ℝ) ^ c * W.normTil lt G f := by
  have hdet : ((Matrix.GeneralLinearGroup.det G : ℂˣ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hG, det_scaleMat]
  have hd : detPow G c * star (detPow G c) = (((T : ℝ) ^ c : ℝ) : ℂ) := by
    unfold detPow
    rw [Units.val_zpow_eq_zpow_val, hdet, ← Complex.ofReal_zpow, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_zpow,
      Real.mul_self_sqrt (Nat.cast_nonneg T)]
  unfold normTil
  rw [W.normFock_shiftW, W.sqAct_shiftW]
  unfold normFock
  rw [fockC_smul_left, fockC_smul_right]
  have hrew : detPow G c * (star (detPow G c) *
      fockC (W.sqAct (n + 1) lt G f) (W.sqAct (n + 1) lt G f)) =
      (detPow G c * star (detPow G c)) *
        fockC (W.sqAct (n + 1) lt G f) (W.sqAct (n + 1) lt G f) := by ring
  rw [hrew, hd, mul_div_assoc, Complex.re_ofReal_mul]

/-- **Branching Integral Existence at `(n, lt, sg, T, G)` (`BranchingIntegralAt`)**
(exact counterpart of Alpöge `BranchingLinkFamilyNormalised.BranchingIntegralAt`). -/
def BranchingIntegralAt (W : WeylRepSystem) (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (T : ℕ) (G : GL (Fin (n + 1)) ℂ) : Prop :=
  ∃ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
    (∀ f ∈ W.delSqC (n + 1) lt, P f ∈ W.delSqC n sg) ∧
    (∃ f ∈ W.delSqC (n + 1) lt, P f ≠ 0) ∧
    (∀ f ∈ W.delSqZ (n + 1) lt, ∃ g ∈ W.delSqZ n sg,
      P (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
    (∀ (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ),
      (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ) →
      ∀ f ∈ W.delSqC (n + 1) lt, P (W.sqAct (n + 1) lt H f) = W.sqAct n sg g (P f)) ∧
    (∀ f ∈ W.delSqC (n + 1) lt,
      (W.normFock sg (P f) (P f)).re ≤
        Real.exp (-(degP lt sg : ℝ) * Real.log (T : ℝ)) *
          ((((cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * dimV lt.w) * W.normTil lt G f)

/-- Normalized branching integral property (`lt.w (Fin.last n) = 0`). -/
def BranchingIntegralNormalised (W : WeylRepSystem) : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n),
    lt.w (Fin.last n) = 0 → Interlace lt sg →
    ∀ (T : ℕ), 0 < T →
    ∀ (G : GL (Fin (n + 1)) ℂ),
      (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T →
      W.BranchingIntegralAt n lt sg T G

/-- Unnormalized branching integral property (arbitrary dominant `lt`, `sg`). -/
def BranchingIntegral (W : WeylRepSystem) : Prop :=
  ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n), Interlace lt sg →
    ∀ (T : ℕ), 0 < T →
    ∀ (G : GL (Fin (n + 1)) ℂ),
      (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T →
      W.BranchingIntegralAt n lt sg T G

/-- **Adjoint Branching Lift Data (`AdjointBranchingData`)** for normalized `lt` (`lt_{last} = 0`),
interlacing `sg`, and scaling `G = scaleMat n T`: bundles the concrete branching lift `jl`,
equivariance of `jl`, non-vanishing witness, integral preservation of the normalized adjoint
`P = (h_sg / h_lt) • P0`, and the scaled Fock norm-trace bound (`xi_norm_bound`). -/
structure AdjointBranchingData (W : WeylRepSystem) (n : ℕ)
    (lt : DomWeight (n + 1)) (sg : DomWeight n) (T : ℕ) (G : GL (Fin (n + 1)) ℂ) where
  jl : W.delSqC n sg →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ
  jl_scaled : W.delSqC n sg →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ
  xiNorm : ℝ
  xiNorm_nonneg : 0 ≤ xiNorm
  xiNorm_le_dimV : xiNorm ≤ dimV lt.w * (fockC (W.extremal (n + 1) lt) (W.extremal (n + 1) lt)).re
  nonvanishing_witness : ∃ (F : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) (v : W.delSqC n sg),
    F ∈ W.delSqC (n + 1) lt ∧ fockC F (jl v) ≠ 0
  jl_equiv : ∀ (g : GL (Fin n) ℂ) (H : GL (Fin (n + 1)) ℂ),
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = blockMat (g : Matrix (Fin n) (Fin n) ℂ) →
    ∀ (F : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) (v : W.delSqC n sg),
      ∃ v' : W.delSqC n sg,
        fockC (W.sqAct (n + 1) lt H F) (jl v) = fockC F (jl v') ∧
        ∀ u ∈ W.delSqC n sg, fockC (W.sqAct n sg g u) (v : MvPolynomial (Fin n × Fin n) ℂ) =
          fockC u (v' : MvPolynomial (Fin n × Fin n) ℂ)
  sqAct_preserves : ∀ (g : GL (Fin n) ℂ), ∀ u ∈ W.delSqC n sg, W.sqAct n sg g u ∈ W.delSqC n sg
  scaling_pairing : ∀ (F : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) (v : W.delSqC n sg),
    fockC F (jl v) = fockC (W.sqAct (n + 1) lt G F) (jl_scaled v)
  norm_trace_eq : ∀ (v : W.delSqC n sg),
    (fockC (jl_scaled v) (jl_scaled v)).re *
      (fockC (W.extremal n sg) (W.extremal n sg)).re =
    (1 / Real.sqrt T) ^ (2 * ∑ i : Fin n, (lamNat lt i - sgNat sg i)) *
      (((cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * xiNorm *
      (fockC (v : MvPolynomial (Fin n × Fin n) ℂ) (v : MvPolynomial (Fin n × Fin n) ℂ)).re
  adjoint_integral :
    ∀ P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
      (∀ F, P F ∈ W.delSqC n sg) →
      (∀ F (v : W.delSqC n sg), W.normFock sg (P F) (v : MvPolynomial (Fin n × Fin n) ℂ) =
        W.normFock lt F (jl v)) →
      ∀ f ∈ W.delSqZ (n + 1) lt, ∃ g ∈ W.delSqZ n sg,
        P (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g

private lemma exp_neg_deg_eq_inv_sqrt_pow {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (h0 : lt.w (Fin.last n) = 0) (hI : Interlace lt sg) (T : ℕ) (hT : 0 < T) :
    Real.exp (-(degP lt sg : ℝ) * Real.log (T : ℝ)) =
      (1 / Real.sqrt T) ^ (2 * ∑ i : Fin n, (lamNat lt i - sgNat sg i)) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hsq : (1 / Real.sqrt T) ^ 2 = (T : ℝ)⁻¹ := by
    rw [one_div, inv_pow, Real.sq_sqrt hTpos.le]
  rw [pow_mul, hsq, degP_eq_sum_sub_of_last_zero lt sg h0 hI]
  set d := ∑ i : Fin n, (lamNat lt i - sgNat sg i)
  have h1 : Real.exp (-((d : ℕ) : ℝ) * Real.log (T : ℝ)) = ((T : ℝ) ^ d)⁻¹ := by
    rw [neg_mul, Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hTpos d)]
  push_cast
  rw [h1, inv_pow]

/-- **MAIN EXPORT #3 — Adjoint Branching Normalisation Theorem (`branching_normalised_of_adjoint`)**
(exact counterpart of Alpöge `BranchingNormalisedOfAdjoint.lean`):
constructs the Fock adjoint `P0` unconditionally via `fock_adjoint_exists`, rescales by
`α = h_sg / h_lt`, and proves non-vanishing, integrality, `GL_n`-equivariance, and the
exact normalized Fock-norm inequality via Cauchy–Schwarz + `norm_trace_eq` + `xiNorm_le_dimV`! -/
theorem branching_normalised_of_adjoint (W : WeylRepSystem)
    (hdata : ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n),
      lt.w (Fin.last n) = 0 → Interlace lt sg →
      ∀ (T : ℕ), 0 < T →
      ∀ (G : GL (Fin (n + 1)) ℂ),
        (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T →
        Nonempty (W.AdjointBranchingData n lt sg T G)) :
    W.BranchingIntegralNormalised := by
  intro n lt sg h0 hI T hT G hG
  obtain ⟨D⟩ := hdata n lt sg h0 hI T hT G hG
  obtain ⟨P0, hP0V, hP0⟩ := fock_adjoint_exists (W.delSqC n sg) D.jl
  set hsr : ℝ := (fockC (W.extremal n sg) (W.extremal n sg)).re
  set hlr : ℝ := (fockC (W.extremal (n + 1) lt) (W.extremal (n + 1) lt)).re
  have hs0 : 0 < hsr := W.fock_extremal_pos sg
  have hl0 : 0 < hlr := W.fock_extremal_pos lt
  set α : ℂ := ((hsr / hlr : ℝ) : ℂ)
  have hsC : fockC (W.extremal n sg) (W.extremal n sg) = (hsr : ℂ) := fockC_self_eq_ofReal_re _
  have hlC : fockC (W.extremal (n + 1) lt) (W.extremal (n + 1) lt) = (hlr : ℂ) :=
    fockC_self_eq_ofReal_re _
  have hadjN : ∀ F (v : W.delSqC n sg),
      W.normFock sg ((α • P0) F) (v : MvPolynomial (Fin n × Fin n) ℂ) =
      W.normFock lt F (D.jl v) := by
    intro F v
    unfold normFock
    rw [LinearMap.smul_apply, fockC_smul_left, hP0 F v, hsC, hlC]
    simp only [α, Complex.ofReal_div]
    have hsne : (hsr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
    have hlne : (hlr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl0.ne'
    field_simp [hsne, hlne]
  refine ⟨α • P0, fun f _ => Submodule.smul_mem _ _ (hP0V f), ?_, ?_, ?_, ?_⟩
  · -- Non-vanishing
    obtain ⟨F, v, hF, hne⟩ := D.nonvanishing_witness
    refine ⟨F, hF, ?_⟩
    rw [LinearMap.smul_apply]
    refine smul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hs0 hl0).ne') ?_
    intro h0P
    have h := hP0 F v
    rw [h0P, fockC_zero_left] at h
    exact hne h.symm
  · -- Integrality via adjoint_integral
    exact D.adjoint_integral (α • P0) (fun F => Submodule.smul_mem _ _ (hP0V F)) hadjN
  · -- GL_n-equivariance
    intro g H hH f _
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    congr 1
    have hdiff_mem : P0 (W.sqAct (n + 1) lt H f) - W.sqAct n sg g (P0 f) ∈ W.delSqC n sg :=
      Submodule.sub_mem _ (hP0V _) (D.sqAct_preserves g _ (hP0V f))
    by_contra hne
    have hpos : 0 < (fockC (P0 (W.sqAct (n + 1) lt H f) - W.sqAct n sg g (P0 f))
        (P0 (W.sqAct (n + 1) lt H f) - W.sqAct n sg g (P0 f))).re :=
      fockC_self_re_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hzero : ∀ v : W.delSqC n sg,
        fockC (P0 (W.sqAct (n + 1) lt H f) - W.sqAct n sg g (P0 f))
          (v : MvPolynomial (Fin n × Fin n) ℂ) = 0 := by
      intro v
      obtain ⟨v', hv1, hv2⟩ := D.jl_equiv g H hH f v
      have hsub_eq : P0 (W.sqAct (n + 1) lt H f) - W.sqAct n sg g (P0 f) =
          P0 (W.sqAct (n + 1) lt H f) + (-1 : ℂ) • W.sqAct n sg g (P0 f) := by
        rw [neg_one_smul]; abel
      rw [hsub_eq, fockC_add_left, fockC_smul_left, hP0 _ v, hv1,
        hv2 (P0 f) (hP0V f), hP0 f v']
      ring
    have := hzero ⟨P0 (W.sqAct (n + 1) lt H f) - W.sqAct n sg g (P0 f), hdiff_mem⟩
    rw [this, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  · -- Sharp normalized Fock-norm estimate via Cauchy–Schwarz + norm_trace_eq
    intro f _
    set p : ℝ := (fockC (P0 f) (P0 f)).re
    set s : ℝ := (fockC (W.sqAct (n + 1) lt G f) (W.sqAct (n + 1) lt G f)).re
    set t2 : ℝ := (1 / Real.sqrt T) ^ (2 * ∑ i : Fin n, (lamNat lt i - sgNat sg i))
    set cc : ℝ := (((cCap lt.w sg.w : ℤ) : ℝ) ^ 2)
    have hp0 : 0 ≤ p := fockC_self_re_nonneg _
    have hs0' : 0 ≤ s := fockC_self_re_nonneg _
    have ht0 : 0 ≤ t2 := by positivity
    have hcc0 : 0 ≤ cc := by positivity
    -- Cauchy–Schwarz on `p = fockC (P0 f) (P0 f) = fockC (sqAct G f) (jl_scaled (P0 f))`
    have hP0_bound : p ≤ (t2 * cc * D.xiNorm / hsr) * s := by
      rcases eq_or_lt_of_le hp0 with hp_eq | hp_pos
      · rw [← hp_eq]; exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ht0 hcc0) D.xiNorm_nonneg) hs0.le) hs0'
      · let vP : W.delSqC n sg := ⟨P0 f, hP0V f⟩
        have hpair : fockC (P0 f) (P0 f) = fockC (W.sqAct (n + 1) lt G f) (D.jl_scaled vP) := by
          rw [hP0 f vP, D.scaling_pairing f vP]
        have hcs := fockC_cauchy_schwarz (W.sqAct (n + 1) lt G f) (D.jl_scaled vP)
        rw [← hpair, fockC_self_eq_ofReal_re, Complex.normSq_ofReal] at hcs
        have htr := D.norm_trace_eq vP
        have ha_eq : (fockC (D.jl_scaled vP) (D.jl_scaled vP)).re =
            (t2 * cc * D.xiNorm / hsr) * p := by
          field_simp [hs0.ne']
          linarith
        rw [ha_eq] at hcs
        have hsq : p * p ≤ ((t2 * cc * D.xiNorm / hsr) * s) * p := by linarith
        exact le_of_mul_le_mul_right hsq hp_pos
    have hL : (W.normFock sg ((α • P0) f) ((α • P0) f)).re = (hsr / hlr) ^ 2 * p / hsr := by
      rw [W.normFock_self_re_eq, LinearMap.smul_apply, fockC_smul_left, fockC_smul_right,
        Complex.star_def, Complex.conj_ofReal, fockC_self_eq_ofReal_re,
        ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    have hR : W.normTil lt G f = s / hlr := W.normFock_self_re_eq lt _
    rw [hL, hR, exp_neg_deg_eq_inv_sqrt_pow lt sg h0 hI T hT]
    have h1 : (hsr / hlr) ^ 2 * p / hsr ≤ t2 * cc * D.xiNorm * s / hlr ^ 2 := by
      rw [div_le_div_iff₀ hs0 (pow_pos hl0 2)]
      calc (hsr / hlr) ^ 2 * p * hlr ^ 2
          = hsr ^ 2 * p := by field_simp [hl0.ne']
        _ ≤ hsr ^ 2 * ((t2 * cc * D.xiNorm / hsr) * s) :=
            mul_le_mul_of_nonneg_left hP0_bound (sq_nonneg hsr)
        _ = t2 * cc * D.xiNorm * s * hsr := by field_simp [hs0.ne']
    have h2 : t2 * cc * D.xiNorm * s / hlr ^ 2 ≤ t2 * (cc * dimV lt.w) * (s / hlr) := by
      rw [div_le_iff₀ (pow_pos hl0 2)]
      have hmul : t2 * cc * D.xiNorm * s ≤ t2 * cc * (dimV lt.w * hlr) * s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left D.xiNorm_le_dimV (mul_nonneg ht0 hcc0)) hs0'
      calc t2 * cc * D.xiNorm * s
          ≤ t2 * cc * (dimV lt.w * hlr) * s := hmul
        _ = t2 * (cc * dimV lt.w) * (s / hlr) * hlr ^ 2 := by field_simp [hl0.ne']
    exact h1.trans h2

/-- **Weight-Shift Transfer (`branching_integral_shift`)**:
shifting both weights `(lt, sg)` by any integer `c : ℤ` preserves `BranchingIntegralAt`,
absorbing `T^c` into `exp(-(degP + c) log T) * T^c = exp(-degP log T)`! -/
theorem branching_integral_shift (W : WeylRepSystem) {n : ℕ}
    (lt : DomWeight (n + 1)) (sg : DomWeight n) (c : ℤ)
    (T : ℕ) (hT : 0 < T) (G : GL (Fin (n + 1)) ℂ)
    (hG : (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T)
    (h : W.BranchingIntegralAt n lt sg T G) :
    W.BranchingIntegralAt n (lt.shiftW c) (sg.shiftW c) T G := by
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := h
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rw [W.delSqC_shiftW, W.delSqC_shiftW]; exact h1
  · rw [W.delSqC_shiftW]; exact h2
  · rw [W.delSqZ_shiftW, W.delSqZ_shiftW]; exact h3
  · intro g H hH f hf
    rw [W.delSqC_shiftW] at hf
    rw [W.sqAct_shiftW, W.sqAct_shiftW, map_smul, h4 g H hH f hf, detPow_blockMat g H hH]
  · intro f hf
    rw [W.delSqC_shiftW] at hf
    have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
    have hz : (T : ℝ) ^ c = Real.exp (Real.log (T : ℝ) * (c : ℝ)) := by
      rw [← Real.rpow_intCast, Real.rpow_def_of_pos hTpos]
    rw [W.normFock_shiftW, W.normTil_shiftW lt c T G hG f, DomWeight.shiftW_w, DomWeight.shiftW_w,
      cCap_shift, dimV_shift, degP_shiftW, hz]
    have he : Real.exp (-((degP lt sg + c : ℤ) : ℝ) * Real.log (T : ℝ)) *
        Real.exp (Real.log (T : ℝ) * (c : ℝ)) =
        Real.exp (-(degP lt sg : ℝ) * Real.log (T : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc (W.normFock sg (P f) (P f)).re
        ≤ Real.exp (-(degP lt sg : ℝ) * Real.log (T : ℝ)) *
            ((((cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * dimV lt.w) * W.normTil lt G f := h5 f hf
      _ = Real.exp (-((degP lt sg + c : ℤ) : ℝ) * Real.log (T : ℝ)) *
            ((((cCap lt.w sg.w : ℤ) : ℝ) ^ 2) * dimV lt.w) *
            (Real.exp (Real.log (T : ℝ) * (c : ℝ)) * W.normTil lt G f) := by
          rw [← he]; ring

/-- **Elimination of `lt.w (Fin.last n) = 0` Normalization (`branching_integral_of_normalised`)**:
`BranchingIntegralNormalised → BranchingIntegral`. -/
theorem branching_integral_of_normalised (W : WeylRepSystem)
    (h : W.BranchingIntegralNormalised) : W.BranchingIntegral := by
  intro n lt sg hI T hT G hG
  have e1 := lt.shiftW_shiftW_neg (lt.w (Fin.last n))
  have e2 := sg.shiftW_shiftW_neg (lt.w (Fin.last n))
  have h0 := h n (lt.shiftW (-lt.w (Fin.last n))) (sg.shiftW (-lt.w (Fin.last n)))
    (by simp only [DomWeight.shiftW_w]; ring) (interlace_shift lt sg _ hI) T hT G hG
  have h1 := W.branching_integral_shift _ _ (lt.w (Fin.last n)) T hT G hG h0
  rwa [e1, e2] at h1

/-- Family branching link statement (`BranchingLinkFamily`) over an arbitrary parameter family
`ι` (covering `FamP`, words `u`, and infinite places `τ`): produces integral `GL_n`-equivariant
nonzero branching projections with the full exponential spread-capacity + `log (dimV)` norm bound. -/
def BranchingLinkFamily (W : WeylRepSystem) {ι : Type*}
    (dimIdx : ι → ℕ)
    (ltFam : ∀ a : ι, DomWeight (dimIdx a + 1))
    (sgFam : ∀ a : ι, DomWeight (dimIdx a))
    (TFam : ι → ℕ)
    (GFam : ∀ a : ι, GL (Fin (dimIdx a + 1)) ℂ) : Prop :=
  ∀ a : ι,
    ∃ P : MvPolynomial (Fin (dimIdx a + 1) × Fin (dimIdx a + 1)) ℂ →ₗ[ℂ]
        MvPolynomial (Fin (dimIdx a) × Fin (dimIdx a)) ℂ,
      (∀ f ∈ W.delSqC (dimIdx a + 1) (ltFam a), P f ∈ W.delSqC (dimIdx a) (sgFam a)) ∧
      (∃ f ∈ W.delSqC (dimIdx a + 1) (ltFam a), P f ≠ 0) ∧
      (∀ f ∈ W.delSqZ (dimIdx a + 1) (ltFam a), ∃ g ∈ W.delSqZ (dimIdx a) (sgFam a),
        P (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
      (∀ (g : GL (Fin (dimIdx a)) ℂ) (H : GL (Fin (dimIdx a + 1)) ℂ),
        (H : Matrix (Fin (dimIdx a + 1)) (Fin (dimIdx a + 1)) ℂ) =
          blockMat (g : Matrix (Fin (dimIdx a)) (Fin (dimIdx a)) ℂ) →
        ∀ f ∈ W.delSqC (dimIdx a + 1) (ltFam a),
          P (W.sqAct (dimIdx a + 1) (ltFam a) H f) = W.sqAct (dimIdx a) (sgFam a) g (P f)) ∧
      (∀ f ∈ W.delSqC (dimIdx a + 1) (ltFam a),
        (W.normFock (sgFam a) (P f) (P f)).re ≤
          Real.exp (-(degP (ltFam a) (sgFam a) : ℝ) * Real.log (TFam a : ℝ) +
            2 * (dimIdx a : ℝ) * Real.log ((ltFam a).spread : ℝ) *
              (∑ i : Fin (dimIdx a), (min (lenP (ltFam a) i) (d0 (ltFam a).w (sgFam a).w) : ℝ)) +
            Real.log (dimV (ltFam a).w)) *
          W.normTil (ltFam a) (GFam a) f)

/-- **MAIN EXPORT #4 — Family Branching Link from Normalized Branching (`branching_link_family_normalised`)**
(exact counterpart of Alpöge `BranchingLinkFamilyNormalised.lean`):
lifts `BranchingIntegralNormalised` to ANY interlacing parameter family `(dimIdx, ltFam, sgFam, TFam, GFam)`
with invertible `scaleMat` (`GFam a = scaleMat (dimIdx a) (TFam a)`), automatically proving
`0 < TFam a` from invertibility of `GFam a` and applying `branching_constant_bound`! -/
theorem branching_link_family_normalised (W : WeylRepSystem)
    (hNorm : W.BranchingIntegralNormalised)
    {ι : Type*}
    (dimIdx : ι → ℕ)
    (ltFam : ∀ a : ι, DomWeight (dimIdx a + 1))
    (sgFam : ∀ a : ι, DomWeight (dimIdx a))
    (TFam : ι → ℕ)
    (GFam : ∀ a : ι, GL (Fin (dimIdx a + 1)) ℂ)
    (hInter : ∀ a : ι, Interlace (ltFam a) (sgFam a))
    (hG : ∀ a : ι, (GFam a : Matrix (Fin (dimIdx a + 1)) (Fin (dimIdx a + 1)) ℂ) =
      scaleMat (dimIdx a) (TFam a)) :
    W.BranchingLinkFamily dimIdx ltFam sgFam TFam GFam := by
  have hAll := W.branching_integral_of_normalised hNorm
  intro a
  have hTpos : 0 < TFam a := by
    by_contra h0
    have hTeq : TFam a = 0 := by omega
    have hdet : (GFam a : Matrix (Fin (dimIdx a + 1)) (Fin (dimIdx a + 1)) ℂ).det = 0 := by
      rw [hG a, det_scaleMat, hTeq]; simp
    have h1 := congrArg Matrix.det
      (show ((GFam a * (GFam a)⁻¹ : GL (Fin (dimIdx a + 1)) ℂ) :
        Matrix (Fin (dimIdx a + 1)) (Fin (dimIdx a + 1)) ℂ) = 1 by simp)
    rw [Units.val_mul, Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := hAll (dimIdx a) (ltFam a) (sgFam a) (hInter a) (TFam a) hTpos (GFam a) (hG a)
  refine ⟨P, h1, h2, h3, h4, fun f hf => (h5 f hf).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (W.normTil_nonneg (ltFam a) (GFam a) f)
  rw [add_assoc, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (branching_constant_bound (ltFam a) (sgFam a) (hInter a))
    (Real.exp_pos _).le

/-- End-to-end composition: `AdjointBranchingData` → `BranchingLinkFamily`. -/
theorem branching_family_of_adjoint (W : WeylRepSystem)
    (hdata : ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n),
      lt.w (Fin.last n) = 0 → Interlace lt sg →
      ∀ (T : ℕ), 0 < T →
      ∀ (G : GL (Fin (n + 1)) ℂ),
        (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T →
        Nonempty (W.AdjointBranchingData n lt sg T G))
    {ι : Type*}
    (dimIdx : ι → ℕ)
    (ltFam : ∀ a : ι, DomWeight (dimIdx a + 1))
    (sgFam : ∀ a : ι, DomWeight (dimIdx a))
    (TFam : ι → ℕ)
    (GFam : ∀ a : ι, GL (Fin (dimIdx a + 1)) ℂ)
    (hInter : ∀ a : ι, Interlace (ltFam a) (sgFam a))
    (hG : ∀ a : ι, (GFam a : Matrix (Fin (dimIdx a + 1)) (Fin (dimIdx a + 1)) ℂ) =
      scaleMat (dimIdx a) (TFam a)) :
    W.BranchingLinkFamily dimIdx ltFam sgFam TFam GFam :=
  W.branching_link_family_normalised (W.branching_normalised_of_adjoint hdata)
    dimIdx ltFam sgFam TFam GFam hInter hG

end WeylRepSystem

/-- Top-level export alias for `WeylRepSystem.branching_normalised_of_adjoint`. -/
theorem branching_normalised_of_adjoint (W : WeylRepSystem)
    (hdata : ∀ (n : ℕ) (lt : DomWeight (n + 1)) (sg : DomWeight n),
      lt.w (Fin.last n) = 0 → Interlace lt sg →
      ∀ (T : ℕ), 0 < T →
      ∀ (G : GL (Fin (n + 1)) ℂ),
        (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scaleMat n T →
        Nonempty (W.AdjointBranchingData n lt sg T G)) :
    W.BranchingIntegralNormalised :=
  W.branching_normalised_of_adjoint hdata

/-- Top-level export alias for `WeylRepSystem.branching_link_family_normalised`. -/
theorem branching_link_family_normalised (W : WeylRepSystem)
    (hNorm : W.BranchingIntegralNormalised)
    {ι : Type*}
    (dimIdx : ι → ℕ)
    (ltFam : ∀ a : ι, DomWeight (dimIdx a + 1))
    (sgFam : ∀ a : ι, DomWeight (dimIdx a))
    (TFam : ι → ℕ)
    (GFam : ∀ a : ι, GL (Fin (dimIdx a + 1)) ℂ)
    (hInter : ∀ a : ι, Interlace (ltFam a) (sgFam a))
    (hG : ∀ a : ι, (GFam a : Matrix (Fin (dimIdx a + 1)) (Fin (dimIdx a + 1)) ℂ) =
      scaleMat (dimIdx a) (TFam a)) :
    W.BranchingLinkFamily dimIdx ltFam sgFam TFam GFam :=
  W.branching_link_family_normalised hNorm dimIdx ltFam sgFam TFam GFam hInter hG

end BranchingAdjointAndFamilyLink

end RHDirect.Stage14M2_WeylHookBranching
