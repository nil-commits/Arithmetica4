/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign: Kronecker's criterion at s = 0 (elementary, no rank/finrank)

If the Hankel determinants `N_{0,m} = det (a_{i+j})_{0 ≤ i,j ≤ m}` vanish for all large `m`,
then `(a_n)` satisfies a linear recurrence from `n = 0`. The proof is entirely elementary:
minimize the vanishing threshold `M₀`, extract a recurrence from the last column of
`adjugate (H_{0,M₀})` (using `A · adj A = det A · 1 = 0`), and propagate it by a strong
induction that right-multiplies `H_{0,n}` by a unipotent upper-triangular matrix and reads
off a block-triangular determinant. No rank, finrank, or Desnanot–Jacobi is used.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open Matrix Finset BigOperators

namespace RHDirect.DworkRat

variable {K : Type*} [Field K]

/-! ### Hankel matrices at s = 0 over a field -/

/-- The `(m+1)×(m+1)` Hankel matrix `(a_{i+j})` at `s = 0`. -/
def hankel0 (a : ℕ → K) (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => a (i.val + j.val)

omit [Field K] in
@[simp] theorem hankel0_apply (a : ℕ → K) (m : ℕ) (i j : Fin (m + 1)) :
    hankel0 a m i j = a (i.val + j.val) := rfl

/-! ### Column reversal and the anti-triangular determinant -/

/-- The order-reversing equivalence on `Fin n`. -/
def finRevEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := fun i => Fin.rev_rev i
  right_inv := fun i => Fin.rev_rev i

/-- The cast of a permutation sign is nonzero. -/
private theorem sign_cast_ne_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((σ.sign : ℤˣ) : K) ≠ 0 :=
  (IsUnit.map (Int.castRingHom K) (Units.isUnit σ.sign)).ne_zero

/-- **Anti-triangular determinant.** If `M` is zero above the anti-diagonal (`i+j < r`) and
has constant anti-diagonal `d`, then `det M = ± d^{r+1}`. -/
theorem det_antiTriangular {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (d : K)
    (hzero : ∀ i j : Fin (r + 1), i.val + j.val < r → M i j = 0)
    (hdiag : ∀ i : Fin (r + 1), M i (Fin.rev i) = d) :
    M.det = ((Equiv.Perm.sign (finRevEquiv (r + 1)) : ℤˣ) : K)⁻¹ * d ^ (r + 1) := by
  set s := ((Equiv.Perm.sign (finRevEquiv (r + 1)) : ℤˣ) : K) with hs_def
  let M' := Matrix.reindex (Equiv.refl (Fin (r + 1))) (finRevEquiv (r + 1)) M
  have hM' : ∀ i j, M' i j = M i (Fin.rev j) := fun _ _ => rfl
  have hlower : M'.IsLowerTriangular := by
    intro i j hij
    rw [hM']
    apply hzero
    have hij' : i.val < j.val := by
      have : i < j := by simpa [OrderDual.toDual_lt_toDual] using hij
      exact_mod_cast this
    have hrev : (Fin.rev j).val = r - j.val := by simp [Fin.rev]
    rw [hrev]
    have hjr : j.val ≤ r := Nat.le_of_lt_succ j.isLt
    omega
  have hdiag' : ∀ i, M' i i = d := fun i => by rw [hM']; exact hdiag i
  have hdetM' : M'.det = d ^ (r + 1) := by
    rw [Matrix.det_of_isLowerTriangular M' hlower]
    simp_rw [hdiag']
    rw [Finset.prod_const]
    simp [Fintype.card_fin]
  have hreindex : M'.det = s * M.det := by
    have := Matrix.det_reindex (Equiv.refl (Fin (r + 1))) (finRevEquiv (r + 1)) M
    simpa [M', s, hs_def] using this
  have hsign : s ≠ 0 := by
    simpa [s, hs_def] using sign_cast_ne_zero (finRevEquiv (r + 1))
  rw [hdetM'] at hreindex
  calc M.det = (s⁻¹ * s) * M.det := by field_simp [hsign]
    _ = s⁻¹ * (s * M.det) := by rw [mul_assoc]
    _ = s⁻¹ * d ^ (r + 1) := by rw [← hreindex]

/-- A nonzero anti-diagonal makes an anti-triangular matrix have nonzero determinant. -/
theorem det_antiTriangular_ne_zero {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (d : K)
    (hzero : ∀ i j : Fin (r + 1), i.val + j.val < r → M i j = 0)
    (hdiag : ∀ i : Fin (r + 1), M i (Fin.rev i) = d) (hd : d ≠ 0) : M.det ≠ 0 := by
  rw [det_antiTriangular M d hzero hdiag]
  exact mul_ne_zero (inv_ne_zero (sign_cast_ne_zero _)) (pow_ne_zero _ hd)

/-- Size-parameterized anti-triangular determinant (anti-diagonal at `i+j = s-1`). -/
theorem det_antiTriangular_size {s : ℕ} (M : Matrix (Fin s) (Fin s) K) (d : K)
    (hzero : ∀ i j : Fin s, i.val + j.val < s - 1 → M i j = 0)
    (hdiag : ∀ i : Fin s, M i (Fin.rev i) = d) :
    M.det = ((Equiv.Perm.sign (finRevEquiv s) : ℤˣ) : K)⁻¹ * d ^ s := by
  set sg := ((Equiv.Perm.sign (finRevEquiv s) : ℤˣ) : K) with hsg_def
  let M' := Matrix.reindex (Equiv.refl (Fin s)) (finRevEquiv s) M
  have hM' : ∀ i j, M' i j = M i (Fin.rev j) := fun _ _ => rfl
  have hlower : M'.IsLowerTriangular := by
    intro i j hij
    rw [hM']
    apply hzero
    have hij' : i.val < j.val := by
      have : i < j := by simpa [OrderDual.toDual_lt_toDual] using hij
      exact_mod_cast this
    have hrev : (Fin.rev j).val = s - 1 - j.val := by simp [Fin.rev]; omega
    rw [hrev]
    have hjr : j.val ≤ s - 1 := by
      have := j.isLt
      omega
    omega
  have hdiag' : ∀ i, M' i i = d := fun i => by rw [hM']; exact hdiag i
  have hdetM' : M'.det = d ^ s := by
    rw [Matrix.det_of_isLowerTriangular M' hlower]
    simp_rw [hdiag']
    rw [Finset.prod_const]
    simp [Fintype.card_fin]
  have hreindex : M'.det = sg * M.det := by
    have := Matrix.det_reindex (Equiv.refl (Fin s)) (finRevEquiv s) M
    simpa [M', sg, hsg_def] using this
  have hsg : sg ≠ 0 := by
    simpa [sg, hsg_def] using sign_cast_ne_zero (finRevEquiv s)
  rw [hdetM'] at hreindex
  calc M.det = (sg⁻¹ * sg) * M.det := by field_simp [hsg]
    _ = sg⁻¹ * (sg * M.det) := by rw [mul_assoc]
    _ = sg⁻¹ * d ^ s := by rw [← hreindex]

/-! ### The last cofactor of a Hankel matrix -/

/-- The bottom-right cofactor of `H_{0,r+1}` is `N_{0,r}`. -/
theorem hankel0_adj_last {a : ℕ → K} (r : ℕ) :
    (hankel0 a (r + 1)).adjugate (Fin.last (r + 1)) (Fin.last (r + 1)) = (hankel0 a r).det := by
  rw [Matrix.adjugate_apply]
  set A' := (hankel0 a (r + 1)).updateRow (Fin.last (r + 1)) (Pi.single (Fin.last (r + 1)) 1) with hA'
  have hrow : ∀ j : Fin (r + 2), A' (Fin.last (r + 1)) j = if j = Fin.last (r + 1) then 1 else 0 := by
    intro j
    simp [hA', Matrix.updateRow_apply, Pi.single_apply]
  have hdet := Matrix.det_succ_row A' (Fin.last (r + 1))
  have hsum : A'.det = (A'.submatrix (Fin.last (r + 1)).succAbove (Fin.last (r + 1)).succAbove).det := by
    rw [hdet]
    rw [Finset.sum_eq_single (Fin.last (r + 1))]
    · simp [hrow]
    · intro j _ hj
      simp [hrow, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum]
  have hminor : A'.submatrix (Fin.last (r + 1)).succAbove (Fin.last (r + 1)).succAbove = hankel0 a r := by
    ext i j
    simp only [hA', Matrix.submatrix_apply, Matrix.updateRow_apply, hankel0_apply]
    have hi : (Fin.last (r + 1)).succAbove i ≠ Fin.last (r + 1) := Fin.succAbove_ne _ _
    simp only [hi, ite_false]
    have hv1 : ((Fin.last (r + 1)).succAbove i).val = i.val := by simp [Fin.succAbove_last]
    have hv2 : ((Fin.last (r + 1)).succAbove j).val = j.val := by simp [Fin.succAbove_last]
    simp only [hv1, hv2]
  rw [hminor]

/-! ### The induction step: block determinant after a unipotent column operation -/

/-- Reindex a `range (r+2)` sum of the zero-extended `c` as a `Fin (r+2)` sum. -/
lemma sum_cExt_range {r : ℕ} (c : Fin (r + 2) → K) (a : ℕ → K) (i : ℕ) :
    ∑ t ∈ range (r + 2), (if ht : t < r + 2 then c ⟨t, ht⟩ else 0) * a (i + t) =
    ∑ j : Fin (r + 2), c j * a (i + j.val) := by
  apply Eq.symm
  apply Finset.sum_bij (fun (j : Fin (r + 2)) _ => j.val)
  · intro j _
    simp only [mem_range]
    exact j.isLt
  · intro j₁ _ j₂ _ h
    exact Fin.ext h
  · intro k hk
    refine ⟨⟨k, by simpa using hk⟩, ?_, rfl⟩
    exact Finset.mem_univ _
  · intro j _
    simp [j.isLt]

/-- Casting a `Fin` along a type equality preserves its value. -/
lemma cast_fin_val {m n : ℕ} (h : m = n) (i : Fin m) :
    (cast (congrArg Fin h) i).val = i.val := by
  subst h
  rfl

/-- The induction step: if `e_0 = … = e_{n-1} = 0`, then `e_n = 0`, via a block determinant. -/
lemma kronecker_step (a : ℕ → K) (r : ℕ) (c : Fin (r + 2) → K)
    (clast : c (Fin.last (r + 1)) = 1)
    (hprev : (hankel0 a r).det ≠ 0)
    (hM0 : ∀ m ≥ r + 1, (hankel0 a m).det = 0)
    (n : ℕ) (hn' : r + 1 ≤ n)
    (e : ℕ → K) (he_def : ∀ i, e i = ∑ j : Fin (r + 2), c j * a (i + j.val))
    (ih : ∀ k < n, e k = 0) : e n = 0 := by
  classical
  set M0 := r + 1 with hM0def
  let cExt : ℕ → K := fun t => if ht : t < r + 2 then c ⟨t, ht⟩ else 0
  -- unipotent upper-triangular column-operation matrix
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) K := fun k j =>
    if j.val < M0 then (if k = j then 1 else 0)
    else if j.val - M0 ≤ k.val ∧ k.val ≤ j.val then cExt (k.val - (j.val - M0)) else 0
  have hU_upper : U.IsUpperTriangular := by
    intro i j hij
    simp only [U]
    split_ifs <;> (simp_all; try omega)
  have hU_diag : ∀ j, U j j = 1 := by
    intro j
    by_cases hj : j.val < M0
    · show (if j.val < M0 then (if j = j then (1 : K) else 0) else
        (if j.val - M0 ≤ j.val ∧ j.val ≤ j.val then cExt (j.val - (j.val - M0)) else 0)) = 1
      rw [if_pos hj]
      exact if_pos (by rfl : j = j)
    · show (if j.val < M0 then (if j = j then (1 : K) else 0) else
        (if j.val - M0 ≤ j.val ∧ j.val ≤ j.val then cExt (j.val - (j.val - M0)) else 0)) = 1
      rw [if_neg hj]
      have hcond : j.val - M0 ≤ j.val ∧ j.val ≤ j.val := by omega
      rw [if_pos hcond]
      have hjm : j.val - (j.val - M0) = M0 := by omega
      rw [hjm]
      simp only [cExt]
      rw [dif_pos (show M0 < r + 2 by omega)]
      have heq : (⟨M0, by omega⟩ : Fin (r + 2)) = Fin.last (r + 1) := by
        apply Fin.ext
        simp [Fin.last, M0]
      rw [heq]
      exact clast
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU_upper]
    simp_rw [hU_diag]
    simp
  let M := hankel0 a n * U
  have hdetM : M.det = 0 := by
    simp only [M, Matrix.det_mul, hM0 n hn', zero_mul]
  -- entries of M left of the split
  have hM_left : ∀ i j, j.val < M0 → M i j = a (i.val + j.val) := by
    intro i j hj
    simp only [M, Matrix.mul_apply]
    simp_rw [hankel0_apply, U]
    simp_rw [if_pos hj]
    rw [Finset.sum_eq_single j]
    · rw [if_pos (show j = j by rfl)]
      ring
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- entries of M right of the split are the recurrence error e
  have hM_right : ∀ i j, M0 ≤ j.val → M i j = e (i.val + j.val - M0) := by
    intro i j hj
    simp only [M, Matrix.mul_apply]
    simp_rw [hankel0_apply, U]
    simp_rw [if_neg (by omega : ¬(j.val < M0))]
    have hbij : ∑ k : Fin (n + 1), a (i.val + k.val) *
        (if j.val - M0 ≤ k.val ∧ k.val ≤ j.val then cExt (k.val - (j.val - M0)) else 0) =
        ∑ t ∈ range (M0 + 1), cExt t * a (i.val + j.val - M0 + t) := by
      have hfilter : ∑ k : Fin (n + 1), a (i.val + k.val) *
          (if j.val - M0 ≤ k.val ∧ k.val ≤ j.val then cExt (k.val - (j.val - M0)) else 0) =
          ∑ k ∈ (univ : Finset (Fin (n + 1))).filter
            (fun k => j.val - M0 ≤ k.val ∧ k.val ≤ j.val),
            a (i.val + k.val) * cExt (k.val - (j.val - M0)) := by
        simp_rw [mul_ite, mul_zero]
        rw [← Finset.sum_filter]
      rw [hfilter]
      apply Finset.sum_bij (fun (k : Fin (n + 1)) _ => k.val - (j.val - M0))
      · intro k hk
        simp only [mem_filter, mem_univ, true_and] at hk
        simp only [mem_range]
        omega
      · intro k₁ _ k₂ _ h
        apply Fin.ext
        simp only [mem_filter, mem_univ, true_and] at *
        omega
      · intro t ht
        simp only [mem_range] at ht
        refine ⟨⟨j.val - M0 + t, by omega⟩, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]
          omega
        · simp
      · intro k hk
        simp only [mem_filter, mem_univ, true_and] at hk
        have hidx : i.val + k.val = i.val + j.val - M0 + (k.val - (j.val - M0)) := by omega
        rw [hidx]
        ring
    rw [hbij]
    have hM0r : M0 + 1 = r + 2 := by omega
    rw [hM0r]
    rw [sum_cExt_range]
    rw [he_def]
  -- split the index set Fin (n+1) ≃ Fin (r+1) ⊕ Fin (n-r)
  have hnn : n + 1 = (r + 1) + (n - r) := by omega
  let se : Fin (n + 1) ≃ Fin (r + 1) ⊕ Fin (n - r) :=
    (Equiv.cast (congrArg Fin hnn)).trans finSumFinEquiv.symm
  have hse_l : ∀ i : Fin (r + 1), (se.symm (Sum.inl i)).val = i.val := by
    intro i
    simp [se, finSumFinEquiv, Equiv.cast]
    rw [show (congrArg Fin hnn).symm = congrArg Fin hnn.symm from proof_irrel _ _,
      cast_fin_val (by omega : r + 1 + (n - r) = n + 1), Fin.val_castAdd]
  have hse_r : ∀ j : Fin (n - r), (se.symm (Sum.inr j)).val = r + 1 + j.val := by
    intro j
    simp [se, finSumFinEquiv, Equiv.cast]
    rw [show (congrArg Fin hnn).symm = congrArg Fin hnn.symm from proof_irrel _ _,
      cast_fin_val (by omega : r + 1 + (n - r) = n + 1), Fin.val_natAdd]
  let MB := Matrix.reindex se se M
  have hdetMB : MB.det = M.det := by
    have h := Matrix.det_reindex se se M
    change MB.det = ↑↑(Equiv.Perm.sign (se.trans se.symm)) * M.det at h
    have hsign : Equiv.Perm.sign (se.trans se.symm) = 1 := by simp
    simp only [hsign] at h
    norm_num at h
    exact h
  let C : Matrix (Fin (n - r)) (Fin (r + 1)) K := fun i j => a (r + 1 + i.val + j.val)
  let D : Matrix (Fin (n - r)) (Fin (n - r)) K := fun i j => e (r + 1 + i.val + j.val)
  have hMB : MB = Matrix.fromBlocks (hankel0 a r) 0 C D := by
    ext x y
    cases x <;> cases y <;>
      simp only [MB, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks, C, D]
    · -- top-left
      rename_i i j
      rw [hM_left]
      · congr 1; simp [hse_l]
      · simp [hse_l]; omega
    · -- top-right = 0
      rename_i i j
      rw [hM_right]
      · have hlt : (se.symm (Sum.inl i)).val + (se.symm (Sum.inr j)).val - M0 < n := by
          simp [hse_l, hse_r, M0]; omega
        exact ih _ hlt
      · simp [hse_r, M0]; try omega
    · -- bottom-left
      rename_i i j
      rw [hM_left]
      · congr 1; simp [hse_l, hse_r]
      · simp [hse_l]; omega
    · -- bottom-right
      rename_i i j
      rw [hM_right]
      · congr 1
        simp [hse_r, M0]
        omega
      · simp [hse_r, M0]; try omega
  have hdetMB' : MB.det = (hankel0 a r).det * D.det := by
    rw [hMB]
    exact Matrix.det_fromBlocks_zero₁₂ (hankel0 a r) C D
  have hDdet : D.det = 0 := by
    have := hdetMB'.symm.trans (hdetMB.trans hdetM)
    -- (hankel0 a r).det * D.det = 0, and (hankel0 a r).det ≠ 0
    exact mul_eq_zero.mp this |>.resolve_left hprev
  -- D is anti-triangular with anti-diagonal e n
  have hDzero : ∀ i j : Fin (n - r), i.val + j.val < n - r - 1 → D i j = 0 := by
    intro i j hij
    simp only [D]
    have hidx : r + 1 + i.val + j.val < n := by omega
    exact ih _ hidx
  have hDdiag : ∀ i : Fin (n - r), D i (Fin.rev i) = e n := by
    intro i
    simp only [D]
    have : r + 1 + i.val + (Fin.rev i).val = n := by
      simp [Fin.rev]; omega
    rw [this]
  have hDanti : D.det = ((Equiv.Perm.sign (finRevEquiv (n - r)) : ℤˣ) : K)⁻¹ *
      (e n) ^ (n - r) :=
    det_antiTriangular_size D (e n) hDzero hDdiag
  rw [hDanti] at hDdet
  have hsign : ((Equiv.Perm.sign (finRevEquiv (n - r)) : ℤˣ) : K)⁻¹ ≠ 0 :=
    inv_ne_zero (sign_cast_ne_zero _)
  have hpow : (e n) ^ (n - r) = 0 := by
    exact mul_eq_zero.mp hDdet |>.resolve_left hsign
  by_contra h
  exact absurd hpow (pow_ne_zero (n - r) h)

/-! ### Kronecker's criterion at s = 0 -/

/-- **Kronecker's criterion (s = 0, elementary).** If the Hankel determinants `N_{0,m}`
vanish for all large `m`, then `(a_n)` satisfies a monic linear recurrence from `n = 0`. -/
theorem kronecker_recurrence (a : ℕ → K) (h : ∃ M, ∀ m ≥ M, (hankel0 a m).det = 0) :
    ∃ (d : ℕ) (c : ℕ → K), c d = 1 ∧ (∀ j > d, c j = 0) ∧
      ∀ n, ∑ j ∈ range (d + 1), c j * a (n + j) = 0 := by
  classical
  set M0 := Nat.find h with hM0def
  have hM0 : ∀ m ≥ M0, (hankel0 a m).det = 0 := Nat.find_spec h
  by_cases hM0z : M0 = 0
  · -- Case M0 = 0: all coefficients vanish
    have hall : ∀ n, a n = 0 := by
      by_contra hne
      push Not at hne
      set k0 := Nat.find hne with hk0def
      have hk0 : a k0 ≠ 0 := Nat.find_spec hne
      have hmin : ∀ j < k0, a j = 0 := by
        intro j hj
        by_contra hjne
        exact Nat.find_min hne hj hjne
      have hanti : (hankel0 a k0).det ≠ 0 := by
        apply det_antiTriangular_ne_zero (hankel0 a k0) (a k0)
        · intro i j hij
          exact hmin (i.val + j.val) hij
        · intro i
          simp only [hankel0_apply]
          have : i.val + (Fin.rev i).val = k0 := by simp [Fin.rev]; omega
          rw [this]
        · exact hk0
      exact hanti (hM0 k0 (by omega))
    refine ⟨0, fun j => if j = 0 then 1 else 0, ?_, ?_, ?_⟩
    · simp
    · intro j hj
      simp [show j ≠ 0 by omega]
    · intro n
      simp [hall n]
  · -- Case M0 > 0
    have hM0pos : 0 < M0 := Nat.pos_of_ne_zero hM0z
    set r := M0 - 1 with hrdef
    have hr : M0 = r + 1 := by omega
    -- minimality gives N_{0,r} ≠ 0
    have hprev : (hankel0 a r).det ≠ 0 := by
      by_contra hz
      have hsmall : ∀ m ≥ r, (hankel0 a m).det = 0 := by
        intro m hm
        by_cases hmr : m = r
        · subst hmr; exact hz
        · exact hM0 m (by omega)
      have : M0 ≤ r := Nat.find_min' h hsmall
      omega
    have hM0' : ∀ m ≥ r + 1, (hankel0 a m).det = 0 := fun m hm => hM0 m (by omega)
    -- extract the recurrence from the last column of adjugate (H_{0,r+1})
    let A := hankel0 a (r + 1)
    have hdetA : A.det = 0 := hM0' (r + 1) (by omega)
    have hadj : A * A.adjugate = 0 := by rw [Matrix.mul_adjugate, hdetA]; simp
    let v : Fin (r + 2) → K := fun j => A.adjugate j (Fin.last (r + 1))
    have hv : ∀ i : Fin (r + 2), ∑ j : Fin (r + 2), a (i.val + j.val) * v j = 0 := by
      intro i
      have := congrArg (fun M => M i (Fin.last (r + 1))) hadj
      simp only [Matrix.mul_apply, Matrix.zero_apply] at this
      simpa [A, v, hankel0_apply] using this
    have vlast : v (Fin.last (r + 1)) = (hankel0 a r).det := by
      simpa [v, A] using hankel0_adj_last (a := a) r
    have vlastne : v (Fin.last (r + 1)) ≠ 0 := by rw [vlast]; exact hprev
    let c : Fin (r + 2) → K := fun j => v j / v (Fin.last (r + 1))
    have clast : c (Fin.last (r + 1)) = 1 := by
      simp only [c]; field_simp [vlastne]
    -- define the recurrence error e (over Fin (r+2))
    let e : ℕ → K := fun i => ∑ j : Fin (r + 2), c j * a (i + j.val)
    have he0 : ∀ i ≤ r + 1, e i = 0 := by
      intro i hi
      simp only [e, c]
      have hterm : ∀ j : Fin (r + 2), (v j / v (Fin.last (r + 1))) * a (i + j.val) =
          (v j * a (i + j.val)) * (v (Fin.last (r + 1)))⁻¹ := by
        intro j; simp only [div_eq_mul_inv]; ring
      simp_rw [hterm]
      rw [← Finset.sum_mul]
      have hnum : ∑ j : Fin (r + 2), v j * a (i + j.val) = 0 := by
        have := hv ⟨i, by omega⟩
        convert this using 1
        apply Finset.sum_congr rfl; intro j _; ring
      rw [hnum]
      simp
    -- strong induction: e n = 0 for all n
    have heall : ∀ n, e n = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases hn : n ≤ r + 1
        · exact he0 n hn
        · exact kronecker_step a r c clast hprev hM0' n (by omega) e (fun i => rfl)
            (fun k hk => ih k hk)
    -- package: extend c to ℕ and convert the Fin-sum to a range-sum
    let cExt : ℕ → K := fun j => if hj : j < r + 2 then c ⟨j, hj⟩ else 0
    have hconv : ∀ n, ∑ j ∈ range (r + 2), cExt j * a (n + j) = e n := by
      intro n
      simp only [e, cExt]
      exact sum_cExt_range c a n
    refine ⟨r + 1, cExt, ?_, ?_, ?_⟩
    · simp only [cExt]
      have hlt : r + 1 < r + 2 := by omega
      simp [hlt]
      have heq : (⟨r + 1, hlt⟩ : Fin (r + 2)) = Fin.last (r + 1) := by
        apply Fin.ext
        simp [Fin.last]
      rw [heq]
      exact clast
    · intro j hj
      simp only [cExt]
      simp [show ¬(j < r + 2) by omega]
    · intro n
      rw [hconv]
      exact heall n

end RHDirect.DworkRat