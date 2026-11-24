import RHDirect.Stage11LocalLanglandsGL2
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# RHDirect.Stage11GL2SmoothRep

**GENUINE `GL₂(ℚ_p)` SMOOTH ADMISSIBLE REPRESENTATIONS DIRECTLY ON MATHLIB'S
`Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]`**:
1. **Concrete Subgroups & Ultrametric Decompositions of `GL (Fin 2) ℚ_[p]`**:
   - Maximal compact open subgroup `K0 p` (`GL₂(ℤ_p)`: entries in `ℤ_[p]` and `det ∈ ℤ_[p]ˣ`),
   - Principal congruence subgroups `principalCongruence p n` (`K_n`, normal in `K0 p` and open
     under arbitrary `GL₂(ℚ_p)` conjugation),
   - Iwahori subgroup `Iwahori p` (upper-triangular mod `p` inside `K0 p`),
   - Upper-triangular Borel subgroup `Borel p` with exact modular character
     `δ_B(diag(a, d)) = ‖a‖_p / ‖d‖_p` and half-power `δ_B^{1/2}`,
   - Explicit **Iwasawa Decomposition** `GL₂(ℚ_p) = B(ℚ_p) · K₀` proved via ultrametric comparison
     of `‖g 1 0‖` vs `‖g 1 1‖`,
   - Explicit **Bruhat Decomposition** `K₀ = I ⊔ I w I` and `GL₂(ℚ_p) = B · I ⊔ B · w · I`.
2. **Genuine Smooth Principal Series `SmoothInd p χ₁ χ₂` & Exact Satake Eigenvalue (`T_p`)**:
   - Smooth right-regular `GL₂(ℚ_p)`-representation `SmoothInd p χ₁ χ₂ ⊆ (GL (Fin 2) ℚ_[p] → ℂ)`,
   - **Exact Spherical Vector Uniqueness**: `dim_ℂ (SmoothInd p χ₁ χ₂)^{K₀} = 1` for unramified
     `χ₁, χ₂`, spanned by the normalized Iwasawa spherical vector `f₀` (`f₀(1) = 1`),
   - **Concrete `p + 1` Coset Decomposition** of `K₀ diag(p, 1) K₀`:
     `K₀ diag(p, 1) K₀ = (⨆_{j=0}^{p-1} !![p, j; 0, 1] · K₀) ⊔ !![1, 0; 0, p] · K₀`,
   - **Exact Satake Eigenvalue Theorem**:
     `(T_p f₀)(g) = p^{1/2} * (χ₁(p) + χ₂(p)) * f₀(g)` for ALL `g ∈ GL (Fin 2) ℚ_[p]`.
3. **Genuine Smooth Steinberg Quotient `SmoothSteinberg p χ` & Satake Eigenform Grounding**:
   - Genuine 1-dimensional `GL₂(ℚ_p)`-subrepresentation
     `ℂ · (χ ∘ det) ↪ SmoothInd p (χ · |·|^{-1/2}) (χ · |·|^{1/2})` and genuine quotient
     `SmoothSteinberg p χ` with induced `GL₂(ℚ_p)`-action,
   - **Vanishing of `K₀`-invariants**: `(SmoothSteinberg p χ)^{K₀} = 0` (`finrank = 0`),
   - **Exact 1D Iwahori-fixed Space**: `dim_ℂ (SmoothSteinberg p χ)^{I} = 1`,
   - **Concrete Atkin–Lehner `w_p` & `U_p` Eigenvalues**:
     `R(w_p) v = -χ(p) • v` and `U_p v = χ(p) • v` (normalized `p^{-1/2} U_p` eigenvalue
     `χ(p) p^{-1/2}` matching `Stage11LocalLanglandsGL2.localLFactor_steinberg_unram`),
   - **Direct Functorial Grounding into `Stage11LocalLanglandsGL2.satakeGL2OfEigenform`** for all
     seven classical Hecke eigenforms (`Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂, S₂₄⁺, S₂₄⁻`) at every prime `p`.

Zero `sorry`, zero custom `axiom`s, zero `native_decide`.
-/

noncomputable section

open Complex Matrix
open scoped BigOperators
open RHDirect.Stage11LocalLanglandsGL2

namespace RHDirect
namespace Stage11GL2SmoothRep

/-! ## Section 1: Concrete Subgroups of Mathlib's `GL (Fin 2) ℚ_[p]` & Decompositions -/

section ConcreteSubgroups

variable (p : ℕ) [hp : Fact p.Prime]

/-- Mathlib's `p`-adic general linear group `GL₂(ℚ_p)`. -/
abbrev GL2Qp (p : ℕ) [Fact p.Prime] := Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]

/-! ### Ultrametric & `2 × 2` Matrix Helper Lemmas -/

lemma norm_le_inv_p_of_lt_one {x : ℚ_[p]} (hx : ‖x‖ < 1) : ‖x‖ ≤ (p : ℝ)⁻¹ := by
  by_cases h0 : x = 0
  · rw [h0, norm_zero]
    exact inv_nonneg.mpr (prime_pos_R p).le
  · rw [Padic.norm_eq_zpow_neg_valuation h0] at hx ⊢
    have hv : 0 < Padic.valuation x := by
      by_contra hle
      have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (-Padic.valuation x) :=
        one_le_zpow₀ (prime_one_lt_R p).le (by omega)
      linarith
    rw [← _root_.zpow_neg_one]
    exact zpow_le_zpow_right₀ (prime_one_lt_R p).le (by omega)

lemma norm_add_eq_right_of_lt {x y : ℚ_[p]} (h : ‖x‖ < ‖y‖) : ‖x + y‖ = ‖y‖ := by
  apply le_antisymm
  · exact (Padic.nonarchimedean x y).trans (max_le h.le le_rfl)
  · have h1 : ‖y‖ ≤ max ‖x + y‖ ‖x‖ := by
      have hy : y = (x + y) + (-x) := by ring
      conv_lhs => rw [hy]
      simpa [norm_neg] using Padic.nonarchimedean (x + y) (-x)
    rcases le_max_iff.mp h1 with hle | hle
    · exact hle
    · linarith

lemma norm_sub_eq_one_of_lt {x : ℚ_[p]} (hx : ‖x‖ < 1) : ‖1 + x‖ = 1 := by
  have h := norm_add_eq_right_of_lt p (x := x) (y := 1) (by simpa using hx)
  simpa [add_comm] using h

lemma norm_mat_mul_le {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]} {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hA : ∀ i j, ‖A i j‖ ≤ C₁) (hB : ∀ i j, ‖B i j‖ ≤ C₂) :
    ∀ i j, ‖(A * B) i j‖ ≤ C₁ * C₂ := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (hA i 0) (hB 0 j) (norm_nonneg _) hC₁
  · rw [norm_mul]
    exact mul_le_mul (hA i 1) (hB 1 j) (norm_nonneg _) hC₁

lemma norm_mat_add_le {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]} {C : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ C) (hB : ∀ i j, ‖B i j‖ ≤ C) :
    ∀ i j, ‖(A + B) i j‖ ≤ C := by
  intro i j
  exact (Padic.nonarchimedean (A i j) (B i j)).trans (max_le (hA i j) (hB i j))

lemma norm_mat_sub_le {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]} {C : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ C) (hB : ∀ i j, ‖B i j‖ ≤ C) :
    ∀ i j, ‖(A - B) i j‖ ≤ C := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (Padic.nonarchimedean (A i j) (-B i j)).trans (max_le (hA i j) (by simpa using hB i j))

lemma norm_one_entry_le_one (i j : Fin 2) :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp

lemma exists_norm_le_zpow (x : ℚ_[p]) : ∃ M : ℕ, ‖x‖ ≤ (p : ℝ) ^ (M : ℤ) := by
  by_cases h0 : x = 0
  · refine ⟨0, ?_⟩
    simp [h0]
  · rw [Padic.norm_eq_zpow_neg_valuation h0]
    refine ⟨(-Padic.valuation x).toNat, ?_⟩
    exact zpow_le_zpow_right₀ (prime_one_lt_R p).le (Int.self_le_toNat _)

lemma exists_mat_norm_bound (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    ∃ M : ℕ, ∀ i j : Fin 2, ‖A i j‖ ≤ (p : ℝ) ^ (M : ℤ) := by
  obtain ⟨M00, h00⟩ := exists_norm_le_zpow p (A 0 0)
  obtain ⟨M01, h01⟩ := exists_norm_le_zpow p (A 0 1)
  obtain ⟨M10, h10⟩ := exists_norm_le_zpow p (A 1 0)
  obtain ⟨M11, h11⟩ := exists_norm_le_zpow p (A 1 1)
  refine ⟨max (max M00 M01) (max M10 M11), fun i j => ?_⟩
  have hmono : ∀ {m n : ℕ}, m ≤ n → (p : ℝ) ^ (m : ℤ) ≤ (p : ℝ) ^ (n : ℤ) := fun h =>
    zpow_le_zpow_right₀ (prime_one_lt_R p).le (Int.ofNat_le.mpr h)
  fin_cases i <;> fin_cases j
  · exact h00.trans (hmono (le_trans (le_max_left _ _) (le_max_left _ _)))
  · exact h01.trans (hmono (le_trans (le_max_right _ _) (le_max_left _ _)))
  · exact h10.trans (hmono (le_trans (le_max_left _ _) (le_max_right _ _)))
  · exact h11.trans (hmono (le_trans (le_max_right _ _) (le_max_right _ _)))

lemma gl2_det_ne_zero (g : GL2Qp p) : Matrix.det g.1 ≠ 0 :=
  (Matrix.GeneralLinearGroup.det g).ne_zero

/-- Explicit `2 × 2` inverse matrix formula for `g⁻¹` in `GL (Fin 2) ℚ_[p]`. -/
theorem gl2_inv_val (g : GL2Qp p) :
    (g⁻¹ : GL2Qp p).1 =
      (Matrix.det g.1)⁻¹ • !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0] := by
  set invM : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
    (Matrix.det g.1)⁻¹ • !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0]
  have hdet : Matrix.det g.1 ≠ 0 := gl2_det_ne_zero p g
  rw [Matrix.det_fin_two] at hdet
  have hmul : g.1 * invM = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [invM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    · field_simp [hdet]; ring
    · ring
    · ring
    · calc -(g.1 1 0 * ((g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0)⁻¹ * g.1 0 1)) +
            g.1 1 1 * ((g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0)⁻¹ * g.1 0 0)
          = (g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0) *
              (g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ hdet
  calc (g⁻¹ : GL2Qp p).1
      = (g⁻¹ : GL2Qp p).1 * 1 := (Matrix.mul_one _).symm
    _ = (g⁻¹ : GL2Qp p).1 * (g.1 * invM) := by rw [hmul]
    _ = ((g⁻¹ : GL2Qp p).1 * g.1) * invM := (Matrix.mul_assoc _ _ _).symm
    _ = ((g⁻¹ * g : GL2Qp p).1) * invM := rfl
    _ = (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) * invM := by rw [inv_mul_cancel]; rfl
    _ = invM := Matrix.one_mul _

lemma gl2_inv_entry_00 (g : GL2Qp p) :
    (g⁻¹ : GL2Qp p).1 0 0 = (Matrix.det g.1)⁻¹ * g.1 1 1 := by
  rw [gl2_inv_val]; simp

lemma gl2_inv_entry_01 (g : GL2Qp p) :
    (g⁻¹ : GL2Qp p).1 0 1 = (Matrix.det g.1)⁻¹ * (-g.1 0 1) := by
  rw [gl2_inv_val]; simp

lemma gl2_inv_entry_10 (g : GL2Qp p) :
    (g⁻¹ : GL2Qp p).1 1 0 = (Matrix.det g.1)⁻¹ * (-g.1 1 0) := by
  rw [gl2_inv_val]; simp

lemma gl2_inv_entry_11 (g : GL2Qp p) :
    (g⁻¹ : GL2Qp p).1 1 1 = (Matrix.det g.1)⁻¹ * g.1 0 0 := by
  rw [gl2_inv_val]; simp

/-- Constructor for elements of `GL (Fin 2) ℚ_[p]` from 4 entries and nonzero determinant. -/
def mkGL2 {a b c d : ℚ_[p]} (hdet : a * d - b * c ≠ 0) : GL2Qp p :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by simpa [Matrix.det_fin_two] using hdet)

@[simp]
lemma mkGL2_val {a b c d : ℚ_[p]} (hdet : a * d - b * c ≠ 0) :
    (mkGL2 p hdet).1 = !![a, b; c, d] := rfl

@[simp]
lemma mkGL2_det {a b c d : ℚ_[p]} (hdet : a * d - b * c ≠ 0) :
    Matrix.det (mkGL2 p hdet).1 = a * d - b * c := by
  simp [mkGL2, Matrix.det_fin_two]

/-- Diagonal element `diag(a, d) ∈ GL₂(ℚ_p)`. -/
def diagGL2 (a d : ℚ_[p]ˣ) : GL2Qp p :=
  mkGL2 p (a := (a : ℚ_[p])) (b := 0) (c := 0) (d := (d : ℚ_[p]))
    (by simp [a.ne_zero, d.ne_zero])

@[simp]
lemma diagGL2_val (a d : ℚ_[p]ˣ) :
    (diagGL2 p a d).1 = !![(a : ℚ_[p]), 0; 0, (d : ℚ_[p])] := rfl

/-- Upper unipotent element `!![1, x; 0, 1] ∈ GL₂(ℚ_p)`. -/
def unipGL2 (x : ℚ_[p]) : GL2Qp p :=
  mkGL2 p (a := 1) (b := x) (c := 0) (d := 1) (by simp)

/-- Weyl element `w = !![0, 1; 1, 0] ∈ GL₂(ℚ_p)` (involutive: `w * w = 1`, `det w = -1`). -/
def weylGL2 : GL2Qp p :=
  mkGL2 p (a := 0) (b := 1) (c := 1) (d := 0) (by norm_num)

@[simp]
lemma weylGL2_val : (weylGL2 p).1 = !![(0 : ℚ_[p]), 1; 1, 0] := rfl

@[simp]
lemma weylGL2_mul_self : weylGL2 p * weylGL2 p = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylGL2, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma weylGL2_inv : (weylGL2 p)⁻¹ = weylGL2 p := by
  exact inv_eq_of_mul_eq_one_right (weylGL2_mul_self p)

/-! ### 1. Maximal Compact Open Subgroup `K0 p = GL₂(ℤ_p)` -/

/-- **Maximal Compact Open Subgroup `K₀ = GL₂(ℤ_p)`** as a concrete subgroup of Mathlib's
`Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]`: matrices with entries in `ℤ_[p]` (`‖g i j‖ ≤ 1`)
and unit determinant (`‖det g‖ = 1`, i.e. `det g ∈ ℤ_[p]ˣ`). -/
def K0 : Subgroup (GL2Qp p) where
  carrier := { g : GL2Qp p | (∀ i j : Fin 2, ‖g.1 i j‖ ≤ 1) ∧ ‖Matrix.det g.1‖ = 1 }
  one_mem' := ⟨fun i j => norm_one_entry_le_one p i j, by simp⟩
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · have hmul := norm_mat_mul_le p zero_le_one zero_le_one hg.1 hh.1
      simpa using hmul
    · change ‖Matrix.det (g.1 * h.1)‖ = 1
      rw [Matrix.det_mul, norm_mul, hg.2, hh.2, mul_one]
  inv_mem' {g} hg := by
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · change ‖(g⁻¹ : GL2Qp p).1 0 0‖ ≤ 1
        rw [gl2_inv_entry_00, norm_mul, norm_inv, hg.2, inv_one, one_mul]; exact hg.1 1 1
      · change ‖(g⁻¹ : GL2Qp p).1 0 1‖ ≤ 1
        rw [gl2_inv_entry_01, norm_mul, norm_inv, hg.2, inv_one, one_mul, norm_neg]; exact hg.1 0 1
      · change ‖(g⁻¹ : GL2Qp p).1 1 0‖ ≤ 1
        rw [gl2_inv_entry_10, norm_mul, norm_inv, hg.2, inv_one, one_mul, norm_neg]; exact hg.1 1 0
      · change ‖(g⁻¹ : GL2Qp p).1 1 1‖ ≤ 1
        rw [gl2_inv_entry_11, norm_mul, norm_inv, hg.2, inv_one, one_mul]; exact hg.1 0 0
    · have hdet_mul : Matrix.det (g⁻¹ : GL2Qp p).1 * Matrix.det g.1 = 1 := by
        rw [← Matrix.det_mul]
        change Matrix.det ((g⁻¹ * g : GL2Qp p).1) = 1
        rw [inv_mul_cancel]; simp
      have hnorm := congrArg norm hdet_mul
      rw [norm_mul, hg.2, mul_one, norm_one] at hnorm
      exact hnorm

lemma mem_K0_iff (g : GL2Qp p) :
    g ∈ K0 p ↔ (∀ i j : Fin 2, ‖g.1 i j‖ ≤ 1) ∧ ‖Matrix.det g.1‖ = 1 := Iff.rfl

/-- Equivalence between `g ∈ K0 p` and literally having entries in `ℤ_[p]` with `det ∈ ℤ_[p]ˣ`. -/
theorem mem_K0_iff_padicInt (g : GL2Qp p) :
    g ∈ K0 p ↔
      (∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
        (∀ i j, (M i j : ℚ_[p]) = g.1 i j) ∧ IsUnit (Matrix.det M)) := by
  constructor
  · intro hg
    let M : Matrix (Fin 2) (Fin 2) ℤ_[p] := Matrix.of fun i j => mkPadicInt (hg.1 i j)
    refine ⟨M, fun i j => rfl, ?_⟩
    rw [PadicInt.isUnit_iff]
    have hdet_coe : ((Matrix.det M : ℤ_[p]) : ℚ_[p]) = Matrix.det g.1 := by
      simp [M, Matrix.det_fin_two]
    change ‖((Matrix.det M : ℤ_[p]) : ℚ_[p])‖ = 1
    rw [hdet_coe]
    exact hg.2
  · rintro ⟨M, hM, hunit⟩
    refine ⟨fun i j => ?_, ?_⟩
    · rw [← hM i j]; exact (M i j).2
    · have hdet_coe : ((Matrix.det M : ℤ_[p]) : ℚ_[p]) = Matrix.det g.1 := by
        simp [Matrix.det_fin_two, hM]
      rw [← hdet_coe]
      exact PadicInt.isUnit_iff.mp hunit

lemma weylGL2_mem_K0 : weylGL2 p ∈ K0 p := by
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [weylGL2]
  · simp [weylGL2, Matrix.det_fin_two]

/-! ### 2. Principal Congruence Subgroups `K_n` & Conjugation Openness -/

/-- **Principal Congruence Subgroup `K_n = principalCongruence p n ≤ K0 p`**:
- `n = 0`: `K_0 = K0 p = GL₂(ℤ_p)`,
- `n ≥ 1`: `{ g ∈ K₀ | ∀ i j, ‖g i j - δ_{ij}‖ ≤ p^{-n} }`. -/
def principalCongruence (n : ℕ) : Subgroup (GL2Qp p) where
  carrier := { g : GL2Qp p | g ∈ K0 p ∧
    (n = 0 ∨ ∀ i j : Fin 2, ‖g.1 i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) }
  one_mem' := ⟨(K0 p).one_mem, Or.inr fun i j => by
    change ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ _
    rw [sub_self, norm_zero]
    exact (zpow_pos (prime_pos_R p) _).le⟩
  mul_mem' {g h} hg hh := by
    refine ⟨(K0 p).mul_mem hg.1 hh.1, ?_⟩
    rcases hg.2 with rfl | hg2
    · exact Or.inl rfl
    · rcases hh.2 with rfl | hh2
      · exact Or.inl rfl
      · right
        intro i j
        have hsplit : (g * h : GL2Qp p).1 - 1 = g.1 * (h.1 - 1) + (g.1 - 1) := by
          change g.1 * h.1 - 1 = _; noncomm_ring
        have hh2' : ∀ a b, ‖(h.1 - 1) a b‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := hh2
        have hg2' : ∀ a b, ‖(g.1 - 1) a b‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := hg2
        have h1 : ∀ a b, ‖(g.1 * (h.1 - 1)) a b‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
          have := norm_mat_mul_le p zero_le_one (zpow_pos (prime_pos_R p) _).le hg.1.1 hh2'
          simpa using this
        have h2 := norm_mat_add_le p h1 hg2' i j
        change ‖((g * h : GL2Qp p).1 - 1) i j‖ ≤ _
        rw [hsplit]
        exact h2
  inv_mem' {g} hg := by
    refine ⟨(K0 p).inv_mem hg.1, ?_⟩
    rcases hg.2 with rfl | hg2
    · exact Or.inl rfl
    · right
      intro i j
      have hsplit : (g⁻¹ : GL2Qp p).1 - 1 = -((g⁻¹ : GL2Qp p).1 * (g.1 - 1)) := by
        have hmul : (g⁻¹ : GL2Qp p).1 * g.1 = 1 := by
          change (g⁻¹ * g : GL2Qp p).1 = 1; rw [inv_mul_cancel]; rfl
        rw [Matrix.mul_sub, Matrix.mul_one, hmul]; abel
      have hinvK0 := (K0 p).inv_mem hg.1
      have hg2' : ∀ a b, ‖(g.1 - 1) a b‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := hg2
      have h1 : ∀ a b, ‖((g⁻¹ : GL2Qp p).1 * (g.1 - 1)) a b‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
        have := norm_mat_mul_le p zero_le_one (zpow_pos (prime_pos_R p) _).le hinvK0.1 hg2'
        simpa using this
      have h2 := h1 i j
      change ‖((g⁻¹ : GL2Qp p).1 - 1) i j‖ ≤ _
      rw [hsplit, Matrix.neg_apply, norm_neg]
      exact h2

lemma principalCongruence_zero : principalCongruence p 0 = K0 p := by
  ext g
  simp [principalCongruence]

lemma principalCongruence_le_K0 (n : ℕ) : principalCongruence p n ≤ K0 p :=
  fun _ hg => hg.1

lemma principalCongruence_anti {m n : ℕ} (hmn : m ≤ n) :
    principalCongruence p n ≤ principalCongruence p m := by
  intro g hg
  refine ⟨hg.1, ?_⟩
  by_cases hm : m = 0
  · exact Or.inl hm
  · right
    rcases hg.2 with rfl | hg2
    · omega
    · intro i j
      exact (hg2 i j).trans (zpow_le_zpow_right₀ (prime_one_lt_R p).le (by omega))

/-- Any matrix `g : GL₂(ℚ_p)` satisfying `‖g i j - δ_{ij}‖ ≤ p^{-n}` with `n ≥ 1` automatically
lies in `K0 p` (and hence in `principalCongruence p n`). -/
lemma mem_principalCongruence_of_sub_one_le {g : GL2Qp p} {n : ℕ} (hn : 1 ≤ n)
    (hsub : ∀ i j : Fin 2, ‖g.1 i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    g ∈ principalCongruence p n := by
  have hp_lt1 : (p : ℝ) ^ (-(n : ℤ)) < 1 := zpow_lt_one_of_neg₀ (prime_one_lt_R p) (by omega)
  have hK0_entry : ∀ i j : Fin 2, ‖g.1 i j‖ ≤ 1 := by
    intro i j
    have hsplit : g.1 i j = (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j +
        (g.1 i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) := by ring
    rw [hsplit]
    exact (Padic.nonarchimedean _ _).trans
      (max_le (norm_one_entry_le_one p i j) ((hsub i j).trans hp_lt1.le))
  have hdet_sub : ‖Matrix.det g.1 - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    set e00 := g.1 0 0 - 1
    set e11 := g.1 1 1 - 1
    set e01 := g.1 0 1
    set e10 := g.1 1 0
    have he00 : ‖e00‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by simpa [e00] using hsub 0 0
    have he11 : ‖e11‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by simpa [e11] using hsub 1 1
    have he01 : ‖e01‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by simpa [e01] using hsub 0 1
    have he10 : ‖e10‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by simpa [e10] using hsub 1 0
    have hdet_eq : Matrix.det g.1 - 1 = e00 + e11 + e00 * e11 - e01 * e10 := by
      rw [Matrix.det_fin_two]; simp only [e00, e11, e01, e10]; ring
    rw [hdet_eq, sub_eq_add_neg]
    have hmul1 : ‖e00 * e11‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      rw [norm_mul]
      calc ‖e00‖ * ‖e11‖ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 :=
            mul_le_mul he00 (he11.trans hp_lt1.le) (norm_nonneg _) (zpow_pos (prime_pos_R p) _).le
        _ = (p : ℝ) ^ (-(n : ℤ)) := mul_one _
    have hmul2 : ‖-(e01 * e10)‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      rw [norm_neg, norm_mul]
      calc ‖e01‖ * ‖e10‖ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 :=
            mul_le_mul he01 (he10.trans hp_lt1.le) (norm_nonneg _) (zpow_pos (prime_pos_R p) _).le
        _ = (p : ℝ) ^ (-(n : ℤ)) := mul_one _
    exact (Padic.nonarchimedean _ _).trans (max_le
      ((Padic.nonarchimedean _ _).trans (max_le
        ((Padic.nonarchimedean _ _).trans (max_le he00 he11)) hmul1)) hmul2)
  have hdet_norm : ‖Matrix.det g.1‖ = 1 := by
    have hsplit : Matrix.det g.1 = 1 + (Matrix.det g.1 - 1) := by ring
    rw [hsplit]
    exact norm_sub_eq_one_of_lt p (lt_of_le_of_lt hdet_sub hp_lt1)
  exact ⟨⟨hK0_entry, hdet_norm⟩, Or.inr hsub⟩

/-- **Conjugation Openness of `principalCongruence`**: for every `x ∈ GL₂(ℚ_p)` and every `n : ℕ`,
there exists `m : ℕ` such that `x * K_m * x⁻¹ ≤ K_n`! This guarantees smoothness is preserved by
the full right-regular action of `GL (Fin 2) ℚ_[p]`. -/
theorem exists_conj_principalCongruence (x : GL2Qp p) (n : ℕ) :
    ∃ m : ℕ, ∀ k ∈ principalCongruence p m, x * k * x⁻¹ ∈ principalCongruence p n := by
  obtain ⟨M₁, hM₁⟩ := exists_mat_norm_bound p x.1
  obtain ⟨M₂, hM₂⟩ := exists_mat_norm_bound p (x⁻¹ : GL2Qp p).1
  set M := max M₁ M₂
  set n' := max n 1
  set m := n' + 2 * M
  have hmono : ∀ {a b : ℕ}, a ≤ b → (p : ℝ) ^ (a : ℤ) ≤ (p : ℝ) ^ (b : ℤ) := fun h =>
    zpow_le_zpow_right₀ (prime_one_lt_R p).le (Int.ofNat_le.mpr h)
  have hx_bd : ∀ i j, ‖x.1 i j‖ ≤ (p : ℝ) ^ (M : ℤ) := fun i j =>
    (hM₁ i j).trans (hmono (le_max_left _ _))
  have hxinv_bd : ∀ i j, ‖(x⁻¹ : GL2Qp p).1 i j‖ ≤ (p : ℝ) ^ (M : ℤ) := fun i j =>
    (hM₂ i j).trans (hmono (le_max_right _ _))
  refine ⟨m, fun k hk => ?_⟩
  have hm_ge1 : 1 ≤ m := by omega
  have hk_sub : ∀ i j, ‖k.1 i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    rcases hk.2 with h0 | hle
    · omega
    · exact hle
  have hconj_sub : ∀ i j, ‖(x * k * x⁻¹ : GL2Qp p).1 i j -
      (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(n' : ℤ)) := by
    have hsplit : (x * k * x⁻¹ : GL2Qp p).1 - 1 = x.1 * (k.1 - 1) * (x⁻¹ : GL2Qp p).1 := by
      have hxx : x.1 * (x⁻¹ : GL2Qp p).1 = 1 := by
        change (x * x⁻¹ : GL2Qp p).1 = 1; rw [mul_inv_cancel]; rfl
      change x.1 * k.1 * (x⁻¹ : GL2Qp p).1 - 1 = _
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hxx]
    have h1 := norm_mat_mul_le p (zpow_pos (prime_pos_R p) _).le (zpow_pos (prime_pos_R p) _).le
      hx_bd hk_sub
    have h2 := norm_mat_mul_le p (mul_nonneg (zpow_pos (prime_pos_R p) _).le
      (zpow_pos (prime_pos_R p) _).le) (zpow_pos (prime_pos_R p) _).le h1 hxinv_bd
    intro i j
    change ‖((x * k * x⁻¹ : GL2Qp p).1 - 1) i j‖ ≤ _
    rw [hsplit]
    refine (h2 i j).trans ?_
    have hexp : (p : ℝ) ^ (M : ℤ) * (p : ℝ) ^ (-(m : ℤ)) * (p : ℝ) ^ (M : ℤ) =
        (p : ℝ) ^ (-(n' : ℤ)) := by
      rw [← zpow_add₀ (prime_ne_zero_R p), ← zpow_add₀ (prime_ne_zero_R p)]
      congr 1; simp only [m]; push_cast; ring
    rw [hexp]
  have hmem_n' : x * k * x⁻¹ ∈ principalCongruence p n' :=
    mem_principalCongruence_of_sub_one_le p (le_max_right n 1) hconj_sub
  exact principalCongruence_anti p (le_max_left n 1) hmem_n'

/-- Every element `k ∈ K0 p` has finite order modulo `principalCongruence p n` for every `n : ℕ`.
(Crucial for proving vanishing of `K₀`-invariants and exactness of `I`-invariants on the Steinberg
quotient!) -/
theorem exists_pow_mem_principalCongruence {k : GL2Qp p} (hk : k ∈ K0 p) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ k ^ m ∈ principalCongruence p n := by
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨1, Nat.one_pos, by simpa [principalCongruence_zero] using hk⟩
  · have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
    have hpowK0 : ∀ r : ℕ, k ^ r ∈ K0 p := fun r => (K0 p).pow_mem hk r
    let φ : ℕ → (Fin 2 → Fin 2 → ZMod (p ^ n)) := fun r i j =>
      PadicInt.toZModPow n (mkPadicInt ((hpowK0 r).1 i j))
    obtain ⟨a, b, hab, hφ⟩ := Finite.exists_ne_map_eq_of_infinite φ
    wlog hlt : a < b generalizing a b
    · exact this b a hab.symm hφ.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have hdiff_le : ∀ i j : Fin 2, ‖(k ^ b : GL2Qp p).1 i j - (k ^ a : GL2Qp p).1 i j‖ ≤
        (p : ℝ) ^ (-(n : ℤ)) := by
      intro i j
      have hker : mkPadicInt ((hpowK0 b).1 i j) - mkPadicInt ((hpowK0 a).1 i j) ∈
          RingHom.ker (PadicInt.toZModPow n) := by
        rw [RingHom.mem_ker, map_sub]
        have hij := congrFun (congrFun hφ i) j
        exact sub_eq_zero.mpr hij.symm
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
      rcases hker with ⟨q, hq⟩
      have hcoe : (k ^ b : GL2Qp p).1 i j - (k ^ a : GL2Qp p).1 i j =
          ((p : ℚ_[p]) ^ n) * (q : ℚ_[p]) := by
        have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hq
        simpa [mkPadicInt_coe] using this
      rw [hcoe, norm_mul, norm_pow, Padic.norm_p, inv_pow, ← zpow_neg_coe_of_pos _ (Nat.pos_of_ne_zero hn0)]
      calc (p : ℝ) ^ (-(n : ℤ)) * ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 :=
            mul_le_mul_of_nonneg_left q.2 (zpow_pos (prime_pos_R p) _).le
        _ = (p : ℝ) ^ (-(n : ℤ)) := mul_one _
    have hpow_eq : k ^ (b - a) = (k ^ a)⁻¹ * k ^ b := by
      have hba : a + (b - a) = b := Nat.add_sub_of_le hlt.le
      rw [eq_inv_mul_iff_mul_eq, ← pow_add, hba]
    have hsplit : (k ^ (b - a) : GL2Qp p).1 - 1 =
        ((k ^ a)⁻¹ : GL2Qp p).1 * ((k ^ b : GL2Qp p).1 - (k ^ a : GL2Qp p).1) := by
      have hmul : ((k ^ a)⁻¹ : GL2Qp p).1 * (k ^ a : GL2Qp p).1 = 1 := by
        change ((k ^ a)⁻¹ * k ^ a : GL2Qp p).1 = 1; rw [inv_mul_cancel]; rfl
      rw [Matrix.mul_sub, hmul, hpow_eq]; rfl
    have hinvK0 : (k ^ a)⁻¹ ∈ K0 p := (K0 p).inv_mem (hpowK0 a)
    have hdiff_le' : ∀ i j : Fin 2, ‖((k ^ b : GL2Qp p).1 - (k ^ a : GL2Qp p).1) i j‖ ≤
        (p : ℝ) ^ (-(n : ℤ)) := hdiff_le
    have hsub : ∀ i j, ‖(k ^ (b - a) : GL2Qp p).1 i j -
        (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      have h1 := norm_mat_mul_le p zero_le_one (zpow_pos (prime_pos_R p) _).le hinvK0.1 hdiff_le'
      intro i j
      change ‖((k ^ (b - a) : GL2Qp p).1 - 1) i j‖ ≤ _
      rw [hsplit]
      simpa using h1 i j
    exact mem_principalCongruence_of_sub_one_le p (Nat.pos_of_ne_zero hn0) hsub

/-! ### 3. Iwahori Subgroup `Iwahori p ≤ K0 p` -/

/-- **Iwahori Subgroup `I = Iwahori p ≤ K0 p`**: matrices in `GL₂(ℤ_p)` that are upper-triangular
modulo `p` (`‖g 1 0‖ < 1`, equivalently `toZMod (g 1 0) = 0`). -/
def Iwahori : Subgroup (GL2Qp p) where
  carrier := { g : GL2Qp p | g ∈ K0 p ∧ ‖g.1 1 0‖ < 1 }
  one_mem' := ⟨(K0 p).one_mem, by simp⟩
  mul_mem' {g h} hg hh := by
    refine ⟨(K0 p).mul_mem hg.1 hh.1, ?_⟩
    change ‖(g.1 * h.1) 1 0‖ < 1
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖g.1 1 0‖ * ‖h.1 0 0‖ ≤ ‖g.1 1 0‖ * 1 :=
            mul_le_mul_of_nonneg_left (hh.1.1 0 0) (norm_nonneg _)
        _ < 1 := by simpa using hg.2
    · rw [norm_mul]
      calc ‖g.1 1 1‖ * ‖h.1 1 0‖ ≤ 1 * ‖h.1 1 0‖ :=
            mul_le_mul_of_nonneg_right (hg.1.1 1 1) (norm_nonneg _)
        _ < 1 := by simpa using hh.2
  inv_mem' {g} hg := by
    refine ⟨(K0 p).inv_mem hg.1, ?_⟩
    rw [gl2_inv_entry_10, norm_mul, norm_inv, hg.1.2, inv_one, one_mul, norm_neg]
    exact hg.2

lemma mem_Iwahori_iff (g : GL2Qp p) :
    g ∈ Iwahori p ↔ g ∈ K0 p ∧ ‖g.1 1 0‖ < 1 := Iff.rfl

lemma Iwahori_le_K0 : Iwahori p ≤ K0 p := fun _ hg => hg.1

lemma principalCongruence_one_le_Iwahori : principalCongruence p 1 ≤ Iwahori p := by
  intro g hg
  refine ⟨hg.1, ?_⟩
  rcases hg.2 with h0 | hle
  · omega
  · have h10 := hle 1 0
    simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at h10
    exact lt_of_le_of_lt h10 (zpow_lt_one_of_neg₀ (prime_one_lt_R p) (by norm_num))

lemma mem_Iwahori_iff_toZMod_zero {g : GL2Qp p} (hg : g ∈ K0 p) :
    g ∈ Iwahori p ↔ PadicInt.toZMod (mkPadicInt (hg.1 1 0)) = 0 := by
  rw [mem_Iwahori_iff, padicInt_toZMod_eq_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

lemma iwahori_diag_norm_eq_one {g : GL2Qp p} (hg : g ∈ Iwahori p) :
    ‖g.1 0 0‖ = 1 ∧ ‖g.1 1 1‖ = 1 := by
  have hdet := hg.1.2
  rw [Matrix.det_fin_two] at hdet
  have hbc : ‖-(g.1 0 1 * g.1 1 0)‖ < 1 := by
    rw [norm_neg, norm_mul]
    calc ‖g.1 0 1‖ * ‖g.1 1 0‖ ≤ 1 * ‖g.1 1 0‖ :=
          mul_le_mul_of_nonneg_right (hg.1.1 0 1) (norm_nonneg _)
      _ < 1 := by simpa using hg.2
  have had_le : ‖g.1 0 0 * g.1 1 1‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖g.1 0 0‖ * ‖g.1 1 1‖ ≤ 1 * 1 :=
          mul_le_mul (hg.1.1 0 0) (hg.1.1 1 1) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have had_eq : ‖g.1 0 0 * g.1 1 1‖ = 1 := by
    apply le_antisymm had_le
    have htri : ‖g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0‖ ≤
        max ‖g.1 0 0 * g.1 1 1‖ ‖-(g.1 0 1 * g.1 1 0)‖ := by
      rw [sub_eq_add_neg]; exact Padic.nonarchimedean _ _
    rw [hdet] at htri
    rcases le_max_iff.mp htri with h1 | h2
    · exact h1
    · linarith
  rw [norm_mul] at had_eq
  constructor
  · apply le_antisymm (hg.1.1 0 0)
    by_contra hlt; push Not at hlt
    nlinarith [norm_nonneg (g.1 0 0), norm_nonneg (g.1 1 1), hg.1.1 1 1]
  · apply le_antisymm (hg.1.1 1 1)
    by_contra hlt; push Not at hlt
    nlinarith [norm_nonneg (g.1 0 0), norm_nonneg (g.1 1 1), hg.1.1 0 0]

lemma weylGL2_not_mem_Iwahori : weylGL2 p ∉ Iwahori p := by
  intro hw
  have h10 := hw.2
  simp [weylGL2] at h10

/-! ### 4. Upper-Triangular Borel Subgroup `Borel p` & Modular Character `δ_B` -/

/-- **Upper-Triangular Borel Subgroup `B(ℚ_p)`** inside `GL (Fin 2) ℚ_[p]`. -/
def Borel : Subgroup (GL2Qp p) where
  carrier := { g : GL2Qp p | g.1 1 0 = 0 }
  one_mem' := rfl
  mul_mem' {g h} hg hh := by
    change (g.1 * h.1) 1 0 = 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hg, hh, zero_mul, mul_zero, add_zero]
  inv_mem' {g} hg := by
    change (g⁻¹ : GL2Qp p).1 1 0 = 0
    rw [gl2_inv_entry_10, hg, neg_zero, mul_zero]

lemma mem_Borel_iff (g : GL2Qp p) : g ∈ Borel p ↔ g.1 1 0 = 0 := Iff.rfl

lemma borel_diag_ne_zero (b : Borel p) : b.1.1 0 0 ≠ 0 ∧ b.1.1 1 1 ≠ 0 := by
  have hdet := gl2_det_ne_zero p b.1
  rw [Matrix.det_fin_two, b.2, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

/-- Top-left diagonal homomorphism `B(ℚ_p) →* ℚ_pˣ`. -/
def borelDiag0 : Borel p →* ℚ_[p]ˣ where
  toFun b := Units.mk0 (b.1.1 0 0) (borel_diag_ne_zero p b).1
  map_one' := by ext; rfl
  map_mul' b₁ b₂ := by
    ext
    change (b₁.1.1 * b₂.1.1) 0 0 = b₁.1.1 0 0 * b₂.1.1 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, b₂.2, mul_zero, add_zero]

/-- Bottom-right diagonal homomorphism `B(ℚ_p) →* ℚ_pˣ`. -/
def borelDiag1 : Borel p →* ℚ_[p]ˣ where
  toFun b := Units.mk0 (b.1.1 1 1) (borel_diag_ne_zero p b).2
  map_one' := by ext; rfl
  map_mul' b₁ b₂ := by
    ext
    change (b₁.1.1 * b₂.1.1) 1 1 = b₁.1.1 1 1 * b₂.1.1 1 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, b₁.2, zero_mul, zero_add]

@[simp] lemma borelDiag0_val (b : Borel p) : ((borelDiag0 p b : ℚ_[p]ˣ) : ℚ_[p]) = b.1.1 0 0 := rfl
@[simp] lemma borelDiag1_val (b : Borel p) : ((borelDiag1 p b : ℚ_[p]ˣ) : ℚ_[p]) = b.1.1 1 1 := rfl

lemma borel_det_eq_mul (b : Borel p) :
    Matrix.GeneralLinearGroup.det b.1 = borelDiag0 p b * borelDiag1 p b := by
  ext
  change Matrix.det b.1.1 = b.1.1 0 0 * b.1.1 1 1
  rw [Matrix.det_fin_two, b.2, mul_zero, sub_zero]

lemma diagGL2_mem_Borel (a d : ℚ_[p]ˣ) : diagGL2 p a d ∈ Borel p := rfl

/-- Exact characterization of `B(ℚ_p) ∩ K₀`: diagonal entries have `p`-adic norm `1`! -/
lemma borel_inter_K0_diag_norm {b : Borel p} (hb : b.1 ∈ K0 p) :
    ‖b.1.1 0 0‖ = 1 ∧ ‖b.1.1 1 1‖ = 1 := by
  have hI : b.1 ∈ Iwahori p := ⟨hb, by rw [b.2, norm_zero]; exact zero_lt_one⟩
  exact iwahori_diag_norm_eq_one p hI

/-- Exact modular character `δ_B : B(ℚ_p) →* ℝ`: `δ_B(b) = ‖b₀₀‖_p / ‖b₁₁‖_p`. -/
def deltaB : Borel p →* ℝ where
  toFun b := ‖b.1.1 0 0‖ / ‖b.1.1 1 1‖
  map_one' := by change ‖(1 : ℚ_[p])‖ / ‖(1 : ℚ_[p])‖ = 1; simp
  map_mul' b₁ b₂ := by
    have h0 : (b₁ * b₂).1.1 0 0 = b₁.1.1 0 0 * b₂.1.1 0 0 := by
      change (b₁.1.1 * b₂.1.1) 0 0 = _
      rw [Matrix.mul_apply, Fin.sum_univ_two, b₂.2, mul_zero, add_zero]
    have h1 : (b₁ * b₂).1.1 1 1 = b₁.1.1 1 1 * b₂.1.1 1 1 := by
      change (b₁.1.1 * b₂.1.1) 1 1 = _
      rw [Matrix.mul_apply, Fin.sum_univ_two, b₁.2, zero_mul, zero_add]
    simp only [h0, h1, norm_mul, mul_div_mul_comm]

lemma deltaB_pos (b : Borel p) : 0 < deltaB p b :=
  div_pos (norm_pos_iff.mpr (borel_diag_ne_zero p b).1)
    (norm_pos_iff.mpr (borel_diag_ne_zero p b).2)

/-- Exact diagonal modulus formula: `δ_B(diag(a, d)) = ‖a‖_p / ‖d‖_p`. -/
theorem deltaB_diag (a d : ℚ_[p]ˣ) :
    deltaB p ⟨diagGL2 p a d, diagGL2_mem_Borel p a d⟩ = ‖(a : ℚ_[p])‖ / ‖(d : ℚ_[p])‖ := rfl

/-- Exact real-power evaluation of `Stage11LocalLanglandsGL2.LocalChar.normPowChar p s`:
`(normPowChar p s)(x) = ‖x‖_p^s` for all `x ∈ ℚ_[p]ˣ` and `s : ℝ`! -/
theorem normPowChar_toHom_val (s : ℝ) (x : ℚ_[p]ˣ) :
    ((LocalChar.normPowChar p s).toHom x : ℂ) = (((‖(x : ℚ_[p])‖ ^ s : ℝ) : ℂ)) := by
  simp only [LocalChar.normPowChar, LocalChar.unramChar_apply, Units.val_zpow_eq_zpow_val,
    Units.val_mk0, ← Complex.ofReal_zpow]
  congr 1
  rw [Padic.norm_eq_zpow_neg_valuation x.ne_zero, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (prime_pos_R p).le, ← Real.rpow_mul (prime_pos_R p).le]
  congr 1
  push_cast
  ring

/-- Square root of the Borel modular character `δ_B^{1/2} : B(ℚ_p) →* ℂˣ`, defined algebraically
via `normPowChar p (1 / 2)` so it composes seamlessly with `LocalChar p`. -/
def deltaBHalf : Borel p →* ℂˣ where
  toFun b :=
    (LocalChar.normPowChar p (1 / 2)).toHom (borelDiag0 p b) *
      ((LocalChar.normPowChar p (1 / 2)).toHom (borelDiag1 p b))⁻¹
  map_one' := by simp
  map_mul' b₁ b₂ := by
    simp only [map_mul, mul_inv]
    ac_rfl

/-- Exact analytic formula `δ_B^{1/2}(b) = (‖b₀₀‖_p / ‖b₁₁‖_p)^{1/2}`! -/
theorem deltaBHalf_val (b : Borel p) :
    (deltaBHalf p b : ℂ) = (((deltaB p b) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  simp only [deltaBHalf, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul,
    Units.val_inv_eq_inv_val, normPowChar_toHom_val, borelDiag0_val, borelDiag1_val]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  change ‖b.1.1 0 0‖ ^ (1 / 2 : ℝ) * (‖b.1.1 1 1‖ ^ (1 / 2 : ℝ))⁻¹ =
    (‖b.1.1 0 0‖ / ‖b.1.1 1 1‖) ^ (1 / 2 : ℝ)
  rw [Real.div_rpow (norm_nonneg _) (norm_nonneg _), ← div_eq_mul_inv]

lemma deltaBHalf_eq_one_of_mem_K0 {b : Borel p} (hb : b.1 ∈ K0 p) :
    deltaBHalf p b = 1 := by
  have ⟨h0, h1⟩ := borel_inter_K0_diag_norm p hb
  have hunr := LocalChar.normPowChar_isUnramified p (1 / 2)
  simp only [deltaBHalf, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [hunr (borelDiag0 p b) h0, hunr (borelDiag1 p b) h1, inv_one, mul_one]

/-! ### 5. Explicit Iwasawa Decomposition `GL₂(ℚ_p) = B(ℚ_p) · K₀` -/

/-- **EXACT IWASAWA DECOMPOSITION `GL₂(ℚ_p) = B(ℚ_p) · K₀`** (Unconditional, via ultrametric
comparison of `‖g 1 0‖` vs `‖g 1 1‖` in `ℚ_[p]`):
every `g ∈ GL (Fin 2) ℚ_[p]` factors as `g = b * k` with `b ∈ Borel p` and `k ∈ K0 p`! -/
theorem iwasawa_decomp (g : GL2Qp p) :
    ∃ (b : Borel p) (k : K0 p), g = b.1 * k.1 := by
  set a := g.1 0 0
  set b₀ := g.1 0 1
  set c := g.1 1 0
  set d := g.1 1 1
  have hdet : a * d - b₀ * c ≠ 0 := by
    simpa [a, b₀, c, d, Matrix.det_fin_two] using gl2_det_ne_zero p g
  rcases le_total ‖c‖ ‖d‖ with hcd | hdc
  · -- Case 1: ‖c‖ ≤ ‖d‖, so d ≠ 0 and t = c / d ∈ ℤ_[p]; take k = !![1, 0; t, 1] ∈ K₀
    have hd : d ≠ 0 := by
      intro hd0
      rw [hd0, norm_zero] at hcd
      have hc0 : c = 0 := norm_eq_zero.mp (le_antisymm hcd (norm_nonneg _))
      exact hdet (by simp [hd0, hc0])
    set t : ℚ_[p] := c / d
    have ht : ‖t‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.mpr hd)]
      exact hcd
    let k : GL2Qp p := mkGL2 p (a := 1) (b := 0) (c := t) (d := 1) (by simp)
    have hk : k ∈ K0 p := by
      refine ⟨fun i j => ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [k, ht]
      · simp [k]
    let B : GL2Qp p := g * k⁻¹
    have hB : B ∈ Borel p := by
      change (g.1 * (k⁻¹ : GL2Qp p).1) 1 0 = 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_10]
      simp [k, Matrix.det_fin_two]
      change c + -(d * t) = 0
      simp only [t, mul_div_cancel₀ _ hd, add_neg_cancel]
    exact ⟨⟨B, hB⟩, ⟨k, hk⟩, by simp [B]⟩
  · -- Case 2: ‖d‖ ≤ ‖c‖, so c ≠ 0 and s = d / c ∈ ℤ_[p]; take k = !![0, 1; 1, s] ∈ K₀
    have hc : c ≠ 0 := by
      intro hc0
      rw [hc0, norm_zero] at hdc
      have hd0 : d = 0 := norm_eq_zero.mp (le_antisymm hdc (norm_nonneg _))
      exact hdet (by simp [hd0, hc0])
    set s : ℚ_[p] := d / c
    have hs : ‖s‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.mpr hc)]
      exact hdc
    let k : GL2Qp p := mkGL2 p (a := 0) (b := 1) (c := 1) (d := s) (by simp)
    have hk : k ∈ K0 p := by
      refine ⟨fun i j => ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [k, hs]
      · simp [k]
    let B : GL2Qp p := g * k⁻¹
    have hB : B ∈ Borel p := by
      change (g.1 * (k⁻¹ : GL2Qp p).1) 1 0 = 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_10]
      simp [k, Matrix.det_fin_two]
      change -(c * s) + d = 0
      simp only [s, mul_div_cancel₀ _ hc, neg_add_cancel]
    exact ⟨⟨B, hB⟩, ⟨k, hk⟩, by simp [B]⟩

/-! ### 6. Bruhat Decomposition `K₀ = I ⊔ I w I` and `GL₂(ℚ_p) = B · I ⊔ B · w · I` -/

/-- **EXACT BRUHAT DECOMPOSITION OF `K₀ = GL₂(ℤ_p)` WITH RESPECT TO THE IWAHORI SUBGROUP `I`**:
every `k ∈ K₀` lies either in `I` or in `(B ∩ K₀) · w · (B ∩ K₀) ⊆ I · w · I`, and the two
double cosets `I` and `I w I` are disjoint! -/
theorem K0_bruhat_decomp {k : GL2Qp p} (hk : k ∈ K0 p) :
    k ∈ Iwahori p ∨
      ∃ (b₁ : Borel p) (i₂ : Iwahori p), b₁.1 ∈ K0 p ∧ k = b₁.1 * weylGL2 p * i₂.1 := by
  by_cases hc : ‖k.1 1 0‖ < 1
  · exact Or.inl ⟨hk, hc⟩
  · right
    have hc1 : ‖k.1 1 0‖ = 1 := le_antisymm (hk.1 1 0) (not_lt.mp hc)
    have hc_ne : k.1 1 0 ≠ 0 := by intro h0; rw [h0, norm_zero] at hc1; norm_num at hc1
    set a := k.1 0 0
    set b := k.1 0 1
    set c := k.1 1 0
    set d := k.1 1 1
    set t : ℚ_[p] := a * c⁻¹
    have ht : ‖t‖ ≤ 1 := by
      rw [norm_mul, norm_inv, hc1, inv_one, mul_one]; exact hk.1 0 0
    let b₁ : GL2Qp p := mkGL2 p (a := 1) (b := t) (c := 0) (d := 1) (by simp)
    have hb₁_B : b₁ ∈ Borel p := rfl
    have hb₁_K0 : b₁ ∈ K0 p := by
      refine ⟨fun i j => ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [b₁, ht]
      · simp [b₁]
    let i₂ : GL2Qp p := weylGL2 p * (b₁⁻¹ * k)
    have hi₂_K0 : i₂ ∈ K0 p :=
      (K0 p).mul_mem (weylGL2_mem_K0 p) ((K0 p).mul_mem ((K0 p).inv_mem hb₁_K0) hk)
    have hi₂_10 : i₂.1 1 0 = 0 := by
      change ((weylGL2 p).1 * ((b₁⁻¹ : GL2Qp p).1 * k.1)) 1 0 = 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, weylGL2_val]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
      rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_01]
      simp [b₁, Matrix.det_fin_two]
      change a + -(t * c) = 0
      simp only [t, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one, add_neg_cancel]
    have hi₂_I : i₂ ∈ Iwahori p := ⟨hi₂_K0, by rw [hi₂_10, norm_zero]; exact zero_lt_one⟩
    refine ⟨⟨b₁, hb₁_B⟩, ⟨i₂, hi₂_I⟩, hb₁_K0, ?_⟩
    simp only [i₂]
    calc k = b₁ * (b₁⁻¹ * k) := by group
      _ = b₁ * ((weylGL2 p * weylGL2 p) * (b₁⁻¹ * k)) := by rw [weylGL2_mul_self, one_mul]
      _ = b₁ * weylGL2 p * (weylGL2 p * (b₁⁻¹ * k)) := by group

/-- Standard double-coset form `K₀ = I ⊔ I w I`: disjointness of `I` and `I w I`. -/
theorem K0_bruhat_disjoint {i₁ i₂ : Iwahori p} :
    i₁.1 * weylGL2 p * i₂.1 ∉ Iwahori p := by
  intro hmem
  have hw : weylGL2 p ∈ Iwahori p := by
    have h := (Iwahori p).mul_mem ((Iwahori p).mul_mem ((Iwahori p).inv_mem i₁.2) hmem)
      ((Iwahori p).inv_mem i₂.2)
    simpa [mul_assoc] using h
  exact weylGL2_not_mem_Iwahori p hw

/-- **EXACT IWAHORI–BRUHAT DECOMPOSITION `GL₂(ℚ_p) = B · I ⊔ B · w · I`**:
every `g ∈ GL (Fin 2) ℚ_[p]` lies in `B · I` or `B · w · I`! -/
theorem gl2_iwahori_bruhat (g : GL2Qp p) :
    (∃ (b : Borel p) (i : Iwahori p), g = b.1 * i.1) ∨
    (∃ (b : Borel p) (i : Iwahori p), g = b.1 * weylGL2 p * i.1) := by
  obtain ⟨b, k, rfl⟩ := iwasawa_decomp p g
  rcases K0_bruhat_decomp p k.2 with hkI | ⟨b₁, i₂, _, hk_eq⟩
  · exact Or.inl ⟨b, ⟨k.1, hkI⟩, rfl⟩
  · refine Or.inr ⟨b * b₁, i₂, ?_⟩
    change b.1 * k.1 = (b.1 * b₁.1) * weylGL2 p * i₂.1
    rw [hk_eq]; group

/-- Disjointness of `B · I` and `B · w · I` in `GL (Fin 2) ℚ_[p]`! -/
theorem gl2_iwahori_bruhat_disjoint (b₁ b₂ : Borel p) (i₁ i₂ : Iwahori p) :
    b₁.1 * i₁.1 ≠ b₂.1 * weylGL2 p * i₂.1 := by
  intro heq
  have hrel : (b₂⁻¹ * b₁ : Borel p).1 = weylGL2 p * (i₂ * i₁⁻¹ : Iwahori p).1 := by
    change b₂.1⁻¹ * b₁.1 = weylGL2 p * (i₂.1 * i₁.1⁻¹)
    calc b₂.1⁻¹ * b₁.1 = b₂.1⁻¹ * (b₁.1 * i₁.1) * i₁.1⁻¹ := by group
      _ = b₂.1⁻¹ * (b₂.1 * weylGL2 p * i₂.1) * i₁.1⁻¹ := by rw [heq]
      _ = weylGL2 p * (i₂.1 * i₁.1⁻¹) := by group
  have h10_lhs : ((b₂⁻¹ * b₁ : Borel p).1).1 1 0 = 0 := (b₂⁻¹ * b₁).2
  have h10_rhs : (weylGL2 p * (i₂ * i₁⁻¹ : Iwahori p).1).1 1 0 =
      ((i₂ * i₁⁻¹ : Iwahori p).1).1 0 0 := by
    change ((weylGL2 p).1 * ((i₂ * i₁⁻¹ : Iwahori p).1).1) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two, weylGL2_val]
    simp
  have h00_zero : ((i₂ * i₁⁻¹ : Iwahori p).1).1 0 0 = 0 := by
    rw [← h10_rhs, ← hrel, h10_lhs]
  have h00_norm : ‖((i₂ * i₁⁻¹ : Iwahori p).1).1 0 0‖ = 1 :=
    (iwahori_diag_norm_eq_one p (i₂ * i₁⁻¹).2).1
  rw [h00_zero, norm_zero] at h00_norm
  norm_num at h00_norm

end ConcreteSubgroups

/-! ## Section 2: Genuine Smooth Principal Series `SmoothInd p χ₁ χ₂` & Exact `T_p` Eigenvalue -/

section SmoothPrincipalSeries

variable (p : ℕ) [hp : Fact p.Prime]

/-- Combined Borel inducing character `b ↦ δ_B^{1/2}(b) · χ₁(b₀₀) · χ₂(b₁₁)` (`B(ℚ_p) →* ℂˣ`). -/
def borelChar (χ₁ χ₂ : LocalChar p) : Borel p →* ℂˣ where
  toFun b := deltaBHalf p b * χ₁.toHom (borelDiag0 p b) * χ₂.toHom (borelDiag1 p b)
  map_one' := by simp
  map_mul' b₁ b₂ := by
    simp only [map_mul]
    ac_rfl

lemma borelChar_val (χ₁ χ₂ : LocalChar p) (b : Borel p) :
    (borelChar p χ₁ χ₂ b : ℂ) =
      (((deltaB p b) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        (χ₁.toHom (borelDiag0 p b) : ℂ) * (χ₂.toHom (borelDiag1 p b) : ℂ) := by
  simp only [borelChar, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, deltaBHalf_val]

lemma borelChar_eq_one_of_mem_K0 {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) {b : Borel p} (hb : b.1 ∈ K0 p) :
    borelChar p χ₁ χ₂ b = 1 := by
  have ⟨h0, h1⟩ := borel_inter_K0_diag_norm p hb
  simp only [borelChar, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [deltaBHalf_eq_one_of_mem_K0 p hb, h₁ (borelDiag0 p b) h0, h₂ (borelDiag1 p b) h1,
    mul_one, mul_one]

/-- **Genuine Smooth Normalized Principal Series `SmoothInd p χ₁ χ₂ = Ind_B^{GL₂}(χ₁ ⊗ χ₂)`**:
the `ℂ`-subspace of functions `f : GL (Fin 2) ℚ_[p] → ℂ` satisfying:
1. **Left Borel equivariance**: `f (b * g) = (‖b₀₀‖ / ‖b₁₁‖)^{1/2} * χ₁(b₀₀) * χ₂(b₁₁) * f g`,
2. **Right smoothness**: invariant under right translation by some principal congruence subgroup
   `K_n = principalCongruence p n`. -/
def SmoothInd (χ₁ χ₂ : LocalChar p) : Submodule ℂ (GL2Qp p → ℂ) where
  carrier := { f : GL2Qp p → ℂ |
    (∀ (b : Borel p) (g : GL2Qp p), f (b.1 * g) = (borelChar p χ₁ χ₂ b : ℂ) * f g) ∧
    (∃ n : ℕ, ∀ (g : GL2Qp p) (k : GL2Qp p), k ∈ principalCongruence p n → f (g * k) = f g) }
  zero_mem' := ⟨fun _ _ => by simp, ⟨0, fun _ _ _ => rfl⟩⟩
  add_mem' {f₁ f₂} hf₁ hf₂ := by
    refine ⟨fun b g => ?_, ?_⟩
    · simp only [Pi.add_apply, hf₁.1 b g, hf₂.1 b g, mul_add]
    · rcases hf₁.2 with ⟨n₁, hn₁⟩
      rcases hf₂.2 with ⟨n₂, hn₂⟩
      refine ⟨max n₁ n₂, fun g k hk => ?_⟩
      simp only [Pi.add_apply,
        hn₁ g k (principalCongruence_anti p (le_max_left n₁ n₂) hk),
        hn₂ g k (principalCongruence_anti p (le_max_right n₁ n₂) hk)]
  smul_mem' c {f} hf := by
    refine ⟨fun b g => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.1 b g]; ring
    · rcases hf.2 with ⟨n, hn⟩
      refine ⟨n, fun g k hk => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, hn g k hk]

lemma smoothInd_left_borel {χ₁ χ₂ : LocalChar p} (f : SmoothInd p χ₁ χ₂)
    (b : Borel p) (g : GL2Qp p) :
    f.1 (b.1 * g) = (borelChar p χ₁ χ₂ b : ℂ) * f.1 g :=
  f.2.1 b g

lemma smoothInd_left_borel_explicit {χ₁ χ₂ : LocalChar p} (f : SmoothInd p χ₁ χ₂)
    (b : Borel p) (g : GL2Qp p) :
    f.1 (b.1 * g) =
      (((‖b.1.1 0 0‖ / ‖b.1.1 1 1‖) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        (χ₁.toHom (borelDiag0 p b) : ℂ) * (χ₂.toHom (borelDiag1 p b) : ℂ) * f.1 g := by
  rw [smoothInd_left_borel, borelChar_val]; rfl

/-- **Genuine Right-Regular `GL (Fin 2) ℚ_[p]`-Action** on `SmoothInd p χ₁ χ₂`:
`(rightAction p χ₁ χ₂ h f)(g) = f(g * h)`. -/
def rightAction (χ₁ χ₂ : LocalChar p) (h : GL2Qp p) :
    SmoothInd p χ₁ χ₂ →ₗ[ℂ] SmoothInd p χ₁ χ₂ where
  toFun f :=
    ⟨fun g => f.1 (g * h),
      ⟨fun b g => by dsimp only; rw [mul_assoc, f.2.1 b (g * h)],
       by
         rcases f.2.2 with ⟨n, hn⟩
         obtain ⟨m, hm⟩ := exists_conj_principalCongruence p h⁻¹ n
         refine ⟨m, fun g k hk => ?_⟩
         dsimp only
         have hconj : h⁻¹ * k * h ∈ principalCongruence p n := by
           simpa [inv_inv] using hm k hk
         have hrew : g * k * h = (g * h) * (h⁻¹ * k * h) := by group
         rw [hrew, hn (g * h) (h⁻¹ * k * h) hconj]⟩⟩
  map_add' _ _ := by ext g; rfl
  map_smul' _ _ := by ext g; rfl

@[simp]
lemma rightAction_apply (χ₁ χ₂ : LocalChar p) (h : GL2Qp p) (f : SmoothInd p χ₁ χ₂) (g : GL2Qp p) :
    (rightAction p χ₁ χ₂ h f).1 g = f.1 (g * h) := rfl

lemma rightAction_one (χ₁ χ₂ : LocalChar p) (f : SmoothInd p χ₁ χ₂) :
    rightAction p χ₁ χ₂ 1 f = f := by
  ext g; simp

lemma rightAction_mul (χ₁ χ₂ : LocalChar p) (h₁ h₂ : GL2Qp p) (f : SmoothInd p χ₁ χ₂) :
    rightAction p χ₁ χ₂ (h₁ * h₂) f = rightAction p χ₁ χ₂ h₁ (rightAction p χ₁ χ₂ h₂ f) := by
  ext g; simp [mul_assoc]

/-- The `H`-invariant submodule `(SmoothInd p χ₁ χ₂)^H` for any subgroup `H ≤ GL₂(ℚ_p)`. -/
def fixedSubmodule (χ₁ χ₂ : LocalChar p) (H : Subgroup (GL2Qp p)) :
    Submodule ℂ (SmoothInd p χ₁ χ₂) where
  carrier := { f : SmoothInd p χ₁ χ₂ | ∀ h ∈ H, rightAction p χ₁ χ₂ h f = f }
  zero_mem' h _ := by ext g; simp
  add_mem' {f₁ f₂} hf₁ hf₂ h hh := by
    rw [map_add, hf₁ h hh, hf₂ h hh]
  smul_mem' c {f} hf h hh := by
    rw [map_smul, hf h hh]

lemma mem_fixedSubmodule_iff {χ₁ χ₂ : LocalChar p} {H : Subgroup (GL2Qp p)}
    {f : SmoothInd p χ₁ χ₂} :
    f ∈ fixedSubmodule p χ₁ χ₂ H ↔ ∀ (g : GL2Qp p) (h : GL2Qp p), h ∈ H → f.1 (g * h) = f.1 g := by
  constructor
  · intro hf g h hh
    exact congrFun (congrArg Subtype.val (hf h hh)) g
  · intro hf h hh
    ext g
    exact hf g h hh

/-! ### Exact Spherical Vector Uniqueness: `dim_ℂ (SmoothInd p χ₁ χ₂)^{K₀} = 1` -/

/-- Well-definedness of `borelChar p χ₁ χ₂` across any two Iwasawa decompositions `b₁ k₁ = b₂ k₂`
for unramified `χ₁, χ₂`. -/
lemma borelChar_iwasawa_unique {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    {b₁ b₂ : Borel p} {k₁ k₂ : K0 p} (heq : b₁.1 * k₁.1 = b₂.1 * k₂.1) :
    borelChar p χ₁ χ₂ b₁ = borelChar p χ₁ χ₂ b₂ := by
  have hrel : (b₂⁻¹ * b₁ : Borel p).1 ∈ K0 p := by
    have h1 : b₂.1⁻¹ * b₁.1 = k₂.1 * k₁.1⁻¹ := by
      calc b₂.1⁻¹ * b₁.1 = b₂.1⁻¹ * (b₁.1 * k₁.1) * k₁.1⁻¹ := by group
        _ = b₂.1⁻¹ * (b₂.1 * k₂.1) * k₁.1⁻¹ := by rw [heq]
        _ = k₂.1 * k₁.1⁻¹ := by group
    change b₂.1⁻¹ * b₁.1 ∈ K0 p
    rw [h1]
    exact (K0 p).mul_mem k₂.2 ((K0 p).inv_mem k₁.2)
  have h1 := borelChar_eq_one_of_mem_K0 p h₁ h₂ hrel
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

/-- The canonical normalized spherical vector `f₀ ∈ SmoothInd p χ₁ χ₂` (`f₀(b * k) = δ_B^{1/2}(b) χ₁(b₀₀) χ₂(b₁₁)`),
constructed via the Iwasawa decomposition `GL₂(ℚ_p) = B · K₀`. -/
def sphericalVec {χ₁ χ₂ : LocalChar p} (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    SmoothInd p χ₁ χ₂ :=
  let toFun : GL2Qp p → ℂ := fun g =>
    (borelChar p χ₁ χ₂ (Classical.choose (iwasawa_decomp p g)) : ℂ)
  have hval : ∀ (b : Borel p) (k : K0 p), toFun (b.1 * k.1) = (borelChar p χ₁ χ₂ b : ℂ) := by
    intro b k
    dsimp only [toFun]
    set b' := Classical.choose (iwasawa_decomp p (b.1 * k.1))
    obtain ⟨k', hk'⟩ := Classical.choose_spec (iwasawa_decomp p (b.1 * k.1))
    exact congrArg Units.val (borelChar_iwasawa_unique p h₁ h₂ hk'.symm)
  ⟨toFun,
    ⟨fun b g => by
      obtain ⟨b', k', rfl⟩ := iwasawa_decomp p g
      have hmul : b.1 * (b'.1 * k'.1) = (b * b').1 * k'.1 := by
        simp only [Subgroup.coe_mul, mul_assoc]
      rw [hmul, hval (b * b') k', hval b' k', map_mul, Units.val_mul],
     ⟨0, fun g k hk => by
       rw [principalCongruence_zero] at hk
       obtain ⟨b', k', rfl⟩ := iwasawa_decomp p g
       have hmul : b'.1 * k'.1 * k = b'.1 * (k' * ⟨k, hk⟩).1 := by
         simp only [Subgroup.coe_mul, mul_assoc]
       rw [hmul, hval b' (k' * ⟨k, hk⟩), hval b' k']⟩⟩⟩

theorem sphericalVec_apply_iwasawa {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) (b : Borel p) (k : K0 p) :
    (sphericalVec p h₁ h₂).1 (b.1 * k.1) = (borelChar p χ₁ χ₂ b : ℂ) := by
  dsimp only [sphericalVec]
  set b' := Classical.choose (iwasawa_decomp p (b.1 * k.1))
  obtain ⟨k', hk'⟩ := Classical.choose_spec (iwasawa_decomp p (b.1 * k.1))
  exact congrArg Units.val (borelChar_iwasawa_unique p h₁ h₂ hk'.symm)

@[simp]
theorem sphericalVec_apply_one {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    (sphericalVec p h₁ h₂).1 1 = 1 := by
  have h := sphericalVec_apply_iwasawa p h₁ h₂ 1 1
  simpa using h

theorem sphericalVec_apply_borel {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) (b : Borel p) :
    (sphericalVec p h₁ h₂).1 b.1 = (borelChar p χ₁ χ₂ b : ℂ) := by
  have h := sphericalVec_apply_iwasawa p h₁ h₂ b 1
  simpa using h

theorem sphericalVec_mem_fixedK0 {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    sphericalVec p h₁ h₂ ∈ fixedSubmodule p χ₁ χ₂ (K0 p) := by
  rw [mem_fixedSubmodule_iff]
  intro g k hk
  obtain ⟨b', k', rfl⟩ := iwasawa_decomp p g
  have hmul : b'.1 * k'.1 * k = b'.1 * (k' * ⟨k, hk⟩).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [hmul, sphericalVec_apply_iwasawa, sphericalVec_apply_iwasawa]

/-- **Spherical Vector Uniqueness**: every `K₀`-fixed vector `f ∈ (SmoothInd p χ₁ χ₂)^{K₀}` is
a unique scalar multiple `f(1) • f₀`! -/
theorem eq_smul_sphericalVec_of_mem_fixedK0 {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    {f : SmoothInd p χ₁ χ₂} (hf : f ∈ fixedSubmodule p χ₁ χ₂ (K0 p)) :
    f = (f.1 1) • sphericalVec p h₁ h₂ := by
  ext g
  obtain ⟨b, k, rfl⟩ := iwasawa_decomp p g
  have hfk : f.1 k.1 = f.1 1 := by
    simpa using (mem_fixedSubmodule_iff p).mp hf 1 k.1 k.2
  rw [f.2.1 b k.1, hfk, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
    sphericalVec_apply_iwasawa]
  ring

/-- Explicit linear isomorphism `(SmoothInd p χ₁ χ₂)^{K₀} ≃ₗ[ℂ] ℂ` (`f ↦ f(1)`). -/
def sphericalFixedEquiv {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    fixedSubmodule p χ₁ χ₂ (K0 p) ≃ₗ[ℂ] ℂ where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ⟨c • sphericalVec p h₁ h₂, (fixedSubmodule p χ₁ χ₂ (K0 p)).smul_mem c
    (sphericalVec_mem_fixedK0 p h₁ h₂)⟩
  left_inv f := by
    ext g
    have h := eq_smul_sphericalVec_of_mem_fixedK0 p h₁ h₂ f.2
    exact congrFun (congrArg Subtype.val h.symm) g
  right_inv c := by
    simp

/-- **EXACT SPHERICAL DIMENSION THEOREM**: `dim_ℂ (SmoothInd p χ₁ χ₂)^{K₀} = 1` for all unramified
`χ₁, χ₂ : LocalChar p`! -/
theorem finrank_sphericalFixed {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    Module.finrank ℂ (fixedSubmodule p χ₁ χ₂ (K0 p)) = 1 := by
  rw [(sphericalFixedEquiv p h₁ h₂).finrank_eq, Module.finrank_self]

/-! ### Concrete `p + 1` Coset Decomposition of `K₀ diag(p, 1) K₀` -/

/-- The diagonal Hecke generator `diag(p, 1) ∈ GL₂(ℚ_p)`. -/
def diagP1 : GL2Qp p := diagGL2 p (padicPrimeUnit p) 1

/-- Upper-triangular Hecke coset representatives `!![p, j; 0, 1]` for `j : Fin p`. -/
def heckeRepUpper (j : Fin p) : GL2Qp p :=
  mkGL2 p (a := (p : ℚ_[p])) (b := (j.val : ℚ_[p])) (c := 0) (d := 1)
    (by simpa using prime_ne_zero_padic p)

/-- Lower diagonal Hecke coset representative `!![1, 0; 0, p]`. -/
def heckeRepLower : GL2Qp p :=
  mkGL2 p (a := 1) (b := 0) (c := 0) (d := (p : ℚ_[p]))
    (by simpa using prime_ne_zero_padic p)

/-- All `p + 1` coset representatives of `K₀ diag(p, 1) K₀ / K₀` indexed by `Option (Fin p)`. -/
def heckeRep : Option (Fin p) → GL2Qp p
  | some j => heckeRepUpper p j
  | none => heckeRepLower p

lemma heckeRepUpper_mem_Borel (j : Fin p) : heckeRepUpper p j ∈ Borel p := rfl
lemma heckeRepLower_mem_Borel : heckeRepLower p ∈ Borel p := rfl

/-- The spherical Hecke double coset `K₀ · diag(p, 1) · K₀ ⊆ GL (Fin 2) ℚ_[p]`. -/
def heckeDoubleCoset : Set (GL2Qp p) :=
  { g : GL2Qp p | ∃ (k₁ : K0 p) (k₂ : K0 p), g = k₁.1 * diagP1 p * k₂.1 }

/-- Left `K₀`-coset `g · K₀ ⊆ GL (Fin 2) ℚ_[p]`. -/
def leftCoset (g : GL2Qp p) (H : Subgroup (GL2Qp p)) : Set (GL2Qp p) :=
  { x : GL2Qp p | ∃ h ∈ H, x = g * h }

lemma heckeRepUpper_mem_doubleCoset (j : Fin p) :
    heckeRepUpper p j ∈ heckeDoubleCoset p := by
  let u : GL2Qp p := mkGL2 p (a := 1) (b := (j.val : ℚ_[p])) (c := 0) (d := 1) (by simp)
  have hu : u ∈ K0 p := by
    refine ⟨fun a b => ?_, ?_⟩
    · fin_cases a <;> fin_cases b <;> simp [u]
      simpa using Padic.norm_int_le_one (p := p) (j.val : ℤ)
    · simp [u]
  refine ⟨⟨u, hu⟩, 1, ?_⟩
  apply Units.ext; ext a b
  fin_cases a <;> fin_cases b <;>
    simp [heckeRepUpper, u, diagP1, diagGL2, Matrix.mul_apply, Fin.sum_univ_two]

lemma heckeRepLower_mem_doubleCoset :
    heckeRepLower p ∈ heckeDoubleCoset p := by
  refine ⟨⟨weylGL2 p, weylGL2_mem_K0 p⟩, ⟨weylGL2 p, weylGL2_mem_K0 p⟩, ?_⟩
  apply Units.ext; ext a b
  fin_cases a <;> fin_cases b <;>
    simp [heckeRepLower, weylGL2, diagP1, diagGL2, Matrix.mul_apply, Fin.sum_univ_two]

lemma heckeRep_mem_doubleCoset (r : Option (Fin p)) :
    heckeRep p r ∈ heckeDoubleCoset p := by
  cases r with
  | some j => exact heckeRepUpper_mem_doubleCoset p j
  | none => exact heckeRepLower_mem_doubleCoset p

/-- Residue lift helper: for any `x ∈ ℚ_[p]` with `‖x‖ ≤ 1`, there exists `j : Fin p` such that
`‖x - (j.val : ℚ_[p])‖ ≤ p⁻¹`. -/
lemma exists_fin_sub_norm_le_inv_p {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    ∃ j : Fin p, ‖x - (j.val : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set z : ZMod p := PadicInt.toZMod (mkPadicInt hx)
  refine ⟨⟨z.val, z.val_lt⟩, ?_⟩
  have hsub_le : ‖x - (z.val : ℚ_[p])‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (Padic.nonarchimedean _ _).trans (max_le hx ?_)
    rw [norm_neg]
    simpa using Padic.norm_int_le_one (p := p) (z.val : ℤ)
  have hz0 : PadicInt.toZMod (mkPadicInt hsub_le) = 0 := by
    have heq : mkPadicInt hsub_le = mkPadicInt hx - ((z.val : ℕ) : ℤ_[p]) :=
      padicInt_ext (by simp only [mkPadicInt_coe, PadicInt.coe_sub, PadicInt.coe_natCast])
    rw [heq, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  exact norm_le_inv_p_of_lt_one p ((padicInt_toZMod_eq_zero_iff p _).mp hz0)

/-- Every `g ∈ GL (Fin 2) ℚ_[p]` with `ℤ_[p]` entries and `‖det g‖ = p⁻¹` lies in one of the
`p + 1` explicit left `K₀`-cosets `(heckeRep p r) · K₀`! -/
lemma exists_heckeRep_of_entries_le_one_det_inv_p {g : GL2Qp p}
    (hent : ∀ i j : Fin 2, ‖g.1 i j‖ ≤ 1) (hdet : ‖Matrix.det g.1‖ = (p : ℝ)⁻¹) :
    ∃ r : Option (Fin p), g ∈ leftCoset p (heckeRep p r) (K0 p) := by
  set a := g.1 0 0
  set b := g.1 0 1
  set c := g.1 1 0
  set d := g.1 1 1
  have hp_pos : (0 : ℝ) < (p : ℝ) := prime_pos_R p
  have hp_ne : (p : ℚ_[p]) ≠ 0 := prime_ne_zero_padic p
  have hpinv_norm : ‖(p : ℚ_[p])⁻¹‖ = (p : ℝ) := by rw [norm_inv, Padic.norm_p, inv_inv]
  by_cases hcd : ‖c‖ < 1 ∧ ‖d‖ < 1
  · -- Case 1: both c, d ∈ p ℤ_[p] ⇒ g ∈ !![1, 0; 0, p] * K₀
    refine ⟨none, (heckeRepLower p)⁻¹ * g, ?_, by simp [heckeRep]⟩
    have hc_le : ‖c‖ ≤ (p : ℝ)⁻¹ := norm_le_inv_p_of_lt_one p hcd.1
    have hd_le : ‖d‖ ≤ (p : ℝ)⁻¹ := norm_le_inv_p_of_lt_one p hcd.2
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · change ‖(((heckeRepLower p)⁻¹ : GL2Qp p).1 * g.1) 0 0‖ ≤ 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_01]
        simp [heckeRepLower, hp_ne, hent 0 0]
      · change ‖(((heckeRepLower p)⁻¹ : GL2Qp p).1 * g.1) 0 1‖ ≤ 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_01]
        simp [heckeRepLower, hp_ne, hent 0 1]
      · change ‖(((heckeRepLower p)⁻¹ : GL2Qp p).1 * g.1) 1 0‖ ≤ 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_10, gl2_inv_entry_11]
        simp only [heckeRepLower, mkGL2_val, Matrix.det_fin_two, one_mul, zero_mul, sub_zero,
          neg_zero, mul_zero, zero_add, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one]
        rw [norm_mul, hpinv_norm]
        calc (p : ℝ) * ‖c‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hc_le hp_pos.le
          _ = 1 := mul_inv_cancel₀ hp_pos.ne'
      · change ‖(((heckeRepLower p)⁻¹ : GL2Qp p).1 * g.1) 1 1‖ ≤ 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_10, gl2_inv_entry_11]
        simp only [heckeRepLower, mkGL2_val, Matrix.det_fin_two, one_mul, zero_mul, sub_zero,
          neg_zero, mul_zero, zero_add, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one]
        rw [norm_mul, hpinv_norm]
        calc (p : ℝ) * ‖d‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hd_le hp_pos.le
          _ = 1 := mul_inv_cancel₀ hp_pos.ne'
    · change ‖Matrix.det (((heckeRepLower p)⁻¹ : GL2Qp p).1 * g.1)‖ = 1
      rw [Matrix.det_mul, norm_mul, hdet]
      have hdet_inv : Matrix.det ((heckeRepLower p)⁻¹ : GL2Qp p).1 = (p : ℚ_[p])⁻¹ := by
        have hm : Matrix.det ((heckeRepLower p)⁻¹ : GL2Qp p).1 * Matrix.det (heckeRepLower p).1 = 1 := by
          rw [← Matrix.det_mul]; change Matrix.det (((heckeRepLower p)⁻¹ * heckeRepLower p : GL2Qp p).1) = 1
          rw [inv_mul_cancel]; simp
        simp only [heckeRepLower, mkGL2_det, one_mul, zero_mul, sub_zero] at hm
        exact eq_inv_of_mul_eq_one_left hm
      rw [hdet_inv, hpinv_norm, mul_inv_cancel₀ hp_pos.ne']
  · -- Case 2: ‖c‖ = 1 or ‖d‖ = 1 ⇒ g ∈ !![p, j; 0, 1] * K₀
    have hor : ‖c‖ = 1 ∨ ‖d‖ = 1 := by
      rcases not_and_or.mp hcd with hc | hd
      · exact Or.inl (le_antisymm (hent 1 0) (not_lt.mp hc))
      · exact Or.inr (le_antisymm (hent 1 1) (not_lt.mp hd))
    obtain ⟨j, hrow0, hrow1⟩ : ∃ j : Fin p,
        ‖a - (j.val : ℚ_[p]) * c‖ ≤ (p : ℝ)⁻¹ ∧ ‖b - (j.val : ℚ_[p]) * d‖ ≤ (p : ℝ)⁻¹ := by
      rcases hor with hc1 | hd1
      · have hc_ne : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc1; norm_num at hc1
        have hac : ‖a * c⁻¹‖ ≤ 1 := by
          rw [norm_mul, norm_inv, hc1, inv_one, mul_one]; exact hent 0 0
        obtain ⟨j, hj⟩ := exists_fin_sub_norm_le_inv_p p hac
        have ha_sub : ‖a - (j.val : ℚ_[p]) * c‖ ≤ (p : ℝ)⁻¹ := by
          have h1 : a - (j.val : ℚ_[p]) * c = (a * c⁻¹ - (j.val : ℚ_[p])) * c := by
            field_simp [hc_ne]
          rw [h1, norm_mul, hc1, mul_one]; exact hj
        have hb_sub : ‖b - (j.val : ℚ_[p]) * d‖ ≤ (p : ℝ)⁻¹ := by
          have h1 : (b - (j.val : ℚ_[p]) * d) * c =
              -(Matrix.det g.1) + d * (a - (j.val : ℚ_[p]) * c) := by
            rw [Matrix.det_fin_two]; simp only [a, b, c, d]; ring
          have hnorm := congrArg norm h1
          rw [norm_mul, hc1, mul_one] at hnorm
          rw [hnorm]
          refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
          · rw [norm_neg, hdet]
          · rw [norm_mul]
            calc ‖d‖ * ‖a - (j.val : ℚ_[p]) * c‖ ≤ 1 * (p : ℝ)⁻¹ :=
                  mul_le_mul (hent 1 1) ha_sub (norm_nonneg _) zero_le_one
              _ = (p : ℝ)⁻¹ := one_mul _
        exact ⟨j, ha_sub, hb_sub⟩
      · have hd_ne : d ≠ 0 := by intro h0; rw [h0, norm_zero] at hd1; norm_num at hd1
        have hbd : ‖b * d⁻¹‖ ≤ 1 := by
          rw [norm_mul, norm_inv, hd1, inv_one, mul_one]; exact hent 0 1
        obtain ⟨j, hj⟩ := exists_fin_sub_norm_le_inv_p p hbd
        have hb_sub : ‖b - (j.val : ℚ_[p]) * d‖ ≤ (p : ℝ)⁻¹ := by
          have h1 : b - (j.val : ℚ_[p]) * d = (b * d⁻¹ - (j.val : ℚ_[p])) * d := by
            field_simp [hd_ne]
          rw [h1, norm_mul, hd1, mul_one]; exact hj
        have ha_sub : ‖a - (j.val : ℚ_[p]) * c‖ ≤ (p : ℝ)⁻¹ := by
          have h1 : (a - (j.val : ℚ_[p]) * c) * d =
              Matrix.det g.1 + c * (b - (j.val : ℚ_[p]) * d) := by
            rw [Matrix.det_fin_two]; simp only [a, b, c, d]; ring
          have hnorm := congrArg norm h1
          rw [norm_mul, hd1, mul_one] at hnorm
          rw [hnorm]
          refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
          · rw [hdet]
          · rw [norm_mul]
            calc ‖c‖ * ‖b - (j.val : ℚ_[p]) * d‖ ≤ 1 * (p : ℝ)⁻¹ :=
                  mul_le_mul (hent 1 0) hb_sub (norm_nonneg _) zero_le_one
              _ = (p : ℝ)⁻¹ := one_mul _
        exact ⟨j, ha_sub, hb_sub⟩
    refine ⟨some j, (heckeRepUpper p j)⁻¹ * g, ?_, by simp [heckeRep]⟩
    refine ⟨fun r s => ?_, ?_⟩
    · fin_cases r <;> fin_cases s
      · change ‖(((heckeRepUpper p j)⁻¹ : GL2Qp p).1 * g.1) 0 0‖ ≤ 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_01]
        simp only [heckeRepUpper, mkGL2_val, Matrix.det_fin_two, mul_one, mul_zero, sub_zero,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        have hrew : (p : ℚ_[p])⁻¹ * a + (p : ℚ_[p])⁻¹ * -(j.val : ℚ_[p]) * c =
            (p : ℚ_[p])⁻¹ * (a - (j.val : ℚ_[p]) * c) := by ring
        change ‖(p : ℚ_[p])⁻¹ * a + (p : ℚ_[p])⁻¹ * -(j.val : ℚ_[p]) * c‖ ≤ 1
        rw [hrew, norm_mul, hpinv_norm]
        calc (p : ℝ) * ‖a - (j.val : ℚ_[p]) * c‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left hrow0 hp_pos.le
          _ = 1 := mul_inv_cancel₀ hp_pos.ne'
      · change ‖(((heckeRepUpper p j)⁻¹ : GL2Qp p).1 * g.1) 0 1‖ ≤ 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_01]
        simp only [heckeRepUpper, mkGL2_val, Matrix.det_fin_two, mul_one, mul_zero, sub_zero,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        have hrew : (p : ℚ_[p])⁻¹ * b + (p : ℚ_[p])⁻¹ * -(j.val : ℚ_[p]) * d =
            (p : ℚ_[p])⁻¹ * (b - (j.val : ℚ_[p]) * d) := by ring
        change ‖(p : ℚ_[p])⁻¹ * b + (p : ℚ_[p])⁻¹ * -(j.val : ℚ_[p]) * d‖ ≤ 1
        rw [hrew, norm_mul, hpinv_norm]
        calc (p : ℝ) * ‖b - (j.val : ℚ_[p]) * d‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left hrow1 hp_pos.le
          _ = 1 := mul_inv_cancel₀ hp_pos.ne'
      · change ‖(((heckeRepUpper p j)⁻¹ : GL2Qp p).1 * g.1) 1 0‖ ≤ 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_10, gl2_inv_entry_11]
        simp [heckeRepUpper, hp_ne, hent 1 0]
      · change ‖(((heckeRepUpper p j)⁻¹ : GL2Qp p).1 * g.1) 1 1‖ ≤ 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_10, gl2_inv_entry_11]
        simp [heckeRepUpper, hp_ne, hent 1 1]
    · change ‖Matrix.det (((heckeRepUpper p j)⁻¹ : GL2Qp p).1 * g.1)‖ = 1
      rw [Matrix.det_mul, norm_mul, hdet]
      have hdet_inv : Matrix.det ((heckeRepUpper p j)⁻¹ : GL2Qp p).1 = (p : ℚ_[p])⁻¹ := by
        have hm : Matrix.det ((heckeRepUpper p j)⁻¹ : GL2Qp p).1 * Matrix.det (heckeRepUpper p j).1 = 1 := by
          rw [← Matrix.det_mul]
          change Matrix.det (((heckeRepUpper p j)⁻¹ * heckeRepUpper p j : GL2Qp p).1) = 1
          rw [inv_mul_cancel]; simp
        simp only [heckeRepUpper, mkGL2_det, mul_one, mul_zero, sub_zero] at hm
        exact eq_inv_of_mul_eq_one_left hm
      rw [hdet_inv, hpinv_norm, mul_inv_cancel₀ hp_pos.ne']

/-- Exact characterization of the double coset `K₀ diag(p, 1) K₀`:
`g ∈ K₀ diag(p, 1) K₀ ↔ (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖det g‖ = p⁻¹`! -/
theorem mem_heckeDoubleCoset_iff (g : GL2Qp p) :
    g ∈ heckeDoubleCoset p ↔ (∀ i j : Fin 2, ‖g.1 i j‖ ≤ 1) ∧ ‖Matrix.det g.1‖ = (p : ℝ)⁻¹ := by
  constructor
  · rintro ⟨k₁, k₂, rfl⟩
    have hdiag_le : ∀ i j : Fin 2, ‖(diagP1 p).1 i j‖ ≤ 1 := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [diagP1, diagGL2, Padic.norm_p]
      exact inv_le_one_of_one_le₀ (prime_one_lt_R p).le
    refine ⟨?_, ?_⟩
    · have h1 := norm_mat_mul_le p zero_le_one zero_le_one k₁.2.1 hdiag_le
      simp only [mul_one] at h1
      have h2 := norm_mat_mul_le p zero_le_one zero_le_one h1 k₂.2.1
      simpa using h2
    · change ‖Matrix.det (k₁.1.1 * (diagP1 p).1 * k₂.1.1)‖ = (p : ℝ)⁻¹
      rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, k₁.2.2, k₂.2.2, one_mul, mul_one]
      simp [diagP1, diagGL2, Padic.norm_p]
  · rintro ⟨hent, hdet⟩
    obtain ⟨r, k, hk, rfl⟩ := exists_heckeRep_of_entries_le_one_det_inv_p p hent hdet
    obtain ⟨k₁, k₂, hr⟩ := heckeRep_mem_doubleCoset p r
    refine ⟨k₁, k₂ * ⟨k, hk⟩, ?_⟩
    rw [hr]; simp only [Subgroup.coe_mul, mul_assoc]

/-- **EXACT `p + 1` COSET DECOMPOSITION OF `K₀ diag(p, 1) K₀`** in `GL (Fin 2) ℚ_[p]`:
`K₀ diag(p, 1) K₀ = (⋃ j : Fin p, !![p, j; 0, 1] · K₀) ∪ !![1, 0; 0, p] · K₀`. -/
theorem heckeDoubleCoset_eq_iUnion :
    heckeDoubleCoset p = ⋃ r : Option (Fin p), leftCoset p (heckeRep p r) (K0 p) := by
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · intro hg
    obtain ⟨hent, hdet⟩ := (mem_heckeDoubleCoset_iff p g).mp hg
    exact exists_heckeRep_of_entries_le_one_det_inv_p p hent hdet
  · rintro ⟨r, k, hk, rfl⟩
    obtain ⟨k₁, k₂, hr⟩ := heckeRep_mem_doubleCoset p r
    refine ⟨k₁, k₂ * ⟨k, hk⟩, ?_⟩
    rw [hr]; simp only [Subgroup.coe_mul, mul_assoc]

/-- **EXACT PAIRWISE DISJOINTNESS OF ALL `p + 1` LEFT `K₀`-COSETS** of `K₀ diag(p, 1) K₀`! -/
theorem heckeCosets_pairwiseDisjoint :
    Pairwise (fun r₁ r₂ : Option (Fin p) =>
      Disjoint (leftCoset p (heckeRep p r₁) (K0 p)) (leftCoset p (heckeRep p r₂) (K0 p))) := by
  intro r₁ r₂ hne
  rw [Set.disjoint_left]
  rintro x ⟨k₁, hk₁, rfl⟩ ⟨k₂, hk₂, hxeq⟩
  have hrel : (heckeRep p r₁)⁻¹ * heckeRep p r₂ ∈ K0 p := by
    have h1 : (heckeRep p r₁)⁻¹ * heckeRep p r₂ = k₁ * k₂⁻¹ := by
      calc (heckeRep p r₁)⁻¹ * heckeRep p r₂
          = (heckeRep p r₁)⁻¹ * (heckeRep p r₂ * k₂) * k₂⁻¹ := by group
        _ = (heckeRep p r₁)⁻¹ * (heckeRep p r₁ * k₁) * k₂⁻¹ := by rw [← hxeq]
        _ = k₁ * k₂⁻¹ := by group
    rw [h1]
    exact (K0 p).mul_mem hk₁ ((K0 p).inv_mem hk₂)
  have hp_ne : (p : ℚ_[p]) ≠ 0 := prime_ne_zero_padic p
  have hpinv_norm : ‖(p : ℚ_[p])⁻¹‖ = (p : ℝ) := by rw [norm_inv, Padic.norm_p, inv_inv]
  cases r₁ with
  | none =>
    cases r₂ with
    | none => exact hne rfl
    | some j =>
      have h11 := hrel.1 1 1
      change ‖(((heckeRepLower p)⁻¹ : GL2Qp p).1 * (heckeRepUpper p j).1) 1 1‖ ≤ 1 at h11
      rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_10, gl2_inv_entry_11] at h11
      simp only [heckeRepLower, heckeRepUpper, mkGL2_val, Matrix.det_fin_two, one_mul, zero_mul,
        sub_zero, neg_zero, mul_zero, zero_add, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one,
        hpinv_norm] at h11
      linarith [prime_one_lt_R p]
  | some j₁ =>
    cases r₂ with
    | none =>
      have h00 := hrel.1 0 0
      change ‖(((heckeRepUpper p j₁)⁻¹ : GL2Qp p).1 * (heckeRepLower p).1) 0 0‖ ≤ 1 at h00
      rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_01] at h00
      simp only [heckeRepLower, heckeRepUpper, mkGL2_val, Matrix.det_fin_two, mul_one, mul_zero,
        sub_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, add_zero, hpinv_norm] at h00
      linarith [prime_one_lt_R p]
    | some j₂ =>
      have h01 := hrel.1 0 1
      change ‖(((heckeRepUpper p j₁)⁻¹ : GL2Qp p).1 * (heckeRepUpper p j₂).1) 0 1‖ ≤ 1 at h01
      rw [Matrix.mul_apply, Fin.sum_univ_two, gl2_inv_entry_00, gl2_inv_entry_01] at h01
      simp only [heckeRepUpper, mkGL2_val, Matrix.det_fin_two, mul_one, mul_zero, sub_zero,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at h01
      have hrew : (p : ℚ_[p])⁻¹ * (j₂.val : ℚ_[p]) + (p : ℚ_[p])⁻¹ * -(j₁.val : ℚ_[p]) =
          (p : ℚ_[p])⁻¹ * ((j₂.val : ℚ_[p]) - (j₁.val : ℚ_[p])) := by ring
      rw [hrew, norm_mul, hpinv_norm] at h01
      have hsub_le : ‖(j₂.val : ℚ_[p]) - (j₁.val : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
        calc ‖(j₂.val : ℚ_[p]) - (j₁.val : ℚ_[p])‖
            = (p : ℝ)⁻¹ * ((p : ℝ) * ‖(j₂.val : ℚ_[p]) - (j₁.val : ℚ_[p])‖) := by
                field_simp [(prime_pos_R p).ne']
          _ ≤ (p : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left h01 (inv_nonneg.mpr (prime_pos_R p).le)
          _ = (p : ℝ)⁻¹ := mul_one _
      have hsub_lt : ‖(j₂.val : ℚ_[p]) - (j₁.val : ℚ_[p])‖ < 1 :=
        lt_of_le_of_lt hsub_le (inv_lt_one_of_one_lt₀ (prime_one_lt_R p))
      have hz0 : PadicInt.toZMod (mkPadicInt hsub_lt.le) = 0 :=
        (padicInt_toZMod_eq_zero_iff p _).mpr hsub_lt
      have heq_zmod : ((j₂.val : ℕ) : ZMod p) = ((j₁.val : ℕ) : ZMod p) := by
        have h1 : mkPadicInt hsub_lt.le = ((j₂.val : ℕ) : ℤ_[p]) - ((j₁.val : ℕ) : ℤ_[p]) :=
          padicInt_ext (by simp)
        rw [h1, map_sub, map_natCast, map_natCast, sub_eq_zero] at hz0
        exact hz0
      have : NeZero p := ⟨hp.out.ne_zero⟩
      have hval_eq : j₂.val = j₁.val := by
        have h2 := congrArg ZMod.val heq_zmod
        rw [ZMod.val_natCast_of_lt j₂.isLt, ZMod.val_natCast_of_lt j₁.isLt] at h2
        exact h2
      exact hne (congrArg some (Fin.ext hval_eq.symm))

omit hp in
/-- Exact cardinality of the `p + 1` Hecke cosets (`Fintype.card (Option (Fin p)) = p + 1`). -/
theorem heckeCosets_card : Fintype.card (Option (Fin p)) = p + 1 := by
  simp

/-- Left multiplication by `k ∈ K₀` permutes the `p + 1` left `K₀`-cosets of `K₀ diag(p, 1) K₀`! -/
lemma K0_mul_heckeRep_perm (k : K0 p) :
    ∃ (σ : Equiv.Perm (Option (Fin p))), ∀ r : Option (Fin p),
      ∃ k' : K0 p, k.1 * heckeRep p r = heckeRep p (σ r) * k'.1 := by
  have hex : ∀ r : Option (Fin p), ∃ r' : Option (Fin p), ∃ k' : K0 p,
      k.1 * heckeRep p r = heckeRep p r' * k'.1 := by
    intro r
    have hmem : k.1 * heckeRep p r ∈ heckeDoubleCoset p := by
      obtain ⟨k₁, k₂, hr⟩ := heckeRep_mem_doubleCoset p r
      refine ⟨k * k₁, k₂, ?_⟩
      rw [hr]; simp only [Subgroup.coe_mul, mul_assoc]
    rw [heckeDoubleCoset_eq_iUnion, Set.mem_iUnion] at hmem
    rcases hmem with ⟨r', k', hk', heq⟩
    exact ⟨r', ⟨k', hk'⟩, heq⟩
  let f : Option (Fin p) → Option (Fin p) := fun r => Classical.choose (hex r)
  have hf_spec : ∀ r, ∃ k' : K0 p, k.1 * heckeRep p r = heckeRep p (f r) * k'.1 :=
    fun r => Classical.choose_spec (hex r)
  have hinj : Function.Injective f := by
    intro r₁ r₂ hfr
    obtain ⟨k₁', hk₁'⟩ := hf_spec r₁
    obtain ⟨k₂', hk₂'⟩ := hf_spec r₂
    by_contra hne
    have hdisj := heckeCosets_pairwiseDisjoint p hne
    dsimp only at hdisj
    rw [Set.disjoint_left] at hdisj
    have hx : heckeRep p r₁ * k₁'.1⁻¹ = heckeRep p r₂ * k₂'.1⁻¹ := by
      have h1 : k.1 * (heckeRep p r₁ * k₁'.1⁻¹) = heckeRep p (f r₁) := by
        calc k.1 * (heckeRep p r₁ * k₁'.1⁻¹)
            = (k.1 * heckeRep p r₁) * k₁'.1⁻¹ := by group
          _ = (heckeRep p (f r₁) * k₁'.1) * k₁'.1⁻¹ := by rw [hk₁']
          _ = heckeRep p (f r₁) := by group
      have h2 : k.1 * (heckeRep p r₂ * k₂'.1⁻¹) = heckeRep p (f r₂) := by
        calc k.1 * (heckeRep p r₂ * k₂'.1⁻¹)
            = (k.1 * heckeRep p r₂) * k₂'.1⁻¹ := by group
          _ = (heckeRep p (f r₂) * k₂'.1) * k₂'.1⁻¹ := by rw [hk₂']
          _ = heckeRep p (f r₂) := by group
      rw [hfr] at h1
      exact mul_left_cancel (h1.trans h2.symm)
    exact hdisj ⟨k₁'.1⁻¹, (K0 p).inv_mem k₁'.2, rfl⟩ ⟨k₂'.1⁻¹, (K0 p).inv_mem k₂'.2, hx⟩
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun r => hf_spec r⟩

/-! ### Concrete Spherical Hecke Operator `T_p` & Exact Satake Eigenvalue Theorem -/

/-- **Concrete Spherical Hecke Operator `T_p`** acting on `GL (Fin 2) ℚ_[p] → ℂ` via summation
over the `p + 1` disjoint left `K₀`-cosets of `K₀ diag(p, 1) K₀`:
`(heckeTp p f)(g) = ∑_{j=0}^{p-1} f(g · !![p, j; 0, 1]) + f(g · !![1, 0; 0, p])`. -/
def heckeTp : (GL2Qp p → ℂ) →ₗ[ℂ] (GL2Qp p → ℂ) where
  toFun f g := ∑ r : Option (Fin p), f (g * heckeRep p r)
  map_add' f₁ f₂ := by ext g; simp [Finset.sum_add_distrib]
  map_smul' c f := by
    ext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]

lemma heckeTp_apply (f : GL2Qp p → ℂ) (g : GL2Qp p) :
    heckeTp p f g = (∑ j : Fin p, f (g * heckeRepUpper p j)) + f (g * heckeRepLower p) := by
  simp [heckeTp, Fintype.sum_option, heckeRep, add_comm]

/-- Normalized spherical Hecke operator `T_p^{norm} = p^{-1/2} · T_p` (whose eigenvalue on the
spherical vector of `Ind_B^G(χ₁ ⊗ χ₂)` is literally `χ₁(p) + χ₂(p)`). -/
def heckeTpNorm : (GL2Qp p → ℂ) →ₗ[ℂ] (GL2Qp p → ℂ) :=
  ((((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • heckeTp p

/-- `heckeTp p` preserves `(SmoothInd p χ₁ χ₂)^{K₀}`! -/
theorem heckeTp_mem_fixedK0 {χ₁ χ₂ : LocalChar p}
    {f : SmoothInd p χ₁ χ₂} (hf : f ∈ fixedSubmodule p χ₁ χ₂ (K0 p)) :
    ∃ Tf : SmoothInd p χ₁ χ₂, Tf.1 = heckeTp p f.1 ∧ Tf ∈ fixedSubmodule p χ₁ χ₂ (K0 p) := by
  have hB : ∀ (b : Borel p) (g : GL2Qp p),
      heckeTp p f.1 (b.1 * g) = (borelChar p χ₁ χ₂ b : ℂ) * heckeTp p f.1 g := by
    intro b g
    simp only [heckeTp, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc, f.2.1 b, Finset.mul_sum]
  have hK0 : ∀ (g : GL2Qp p) (k : GL2Qp p), k ∈ K0 p → heckeTp p f.1 (g * k) = heckeTp p f.1 g := by
    intro g k hk
    obtain ⟨σ, hσ⟩ := K0_mul_heckeRep_perm p ⟨k, hk⟩
    simp only [heckeTp, LinearMap.coe_mk, AddHom.coe_mk]
    calc ∑ r : Option (Fin p), f.1 (g * k * heckeRep p r)
        = ∑ r : Option (Fin p), f.1 (g * heckeRep p (σ r)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          obtain ⟨k', hk'⟩ := hσ r
          rw [mul_assoc, hk', ← mul_assoc]
          exact (mem_fixedSubmodule_iff p).mp hf (g * heckeRep p (σ r)) k'.1 k'.2
      _ = ∑ r : Option (Fin p), f.1 (g * heckeRep p r) := Equiv.sum_comp σ (fun r => f.1 (g * heckeRep p r))
  refine ⟨⟨heckeTp p f.1, ⟨hB, ⟨0, fun g k hk => by rw [principalCongruence_zero] at hk; exact hK0 g k hk⟩⟩⟩,
    rfl, (mem_fixedSubmodule_iff p).mpr hK0⟩

/-- **EXACT SATAKE EIGENVALUE THEOREM (`T_p f₀ = p^{1/2} (χ₁(p) + χ₂(p)) · f₀`)**
for ALL unramified `χ₁, χ₂ : LocalChar p` and ALL `g ∈ GL (Fin 2) ℚ_[p]`! -/
theorem heckeTp_sphericalVec {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) (g : GL2Qp p) :
    heckeTp p (sphericalVec p h₁ h₂).1 g =
      (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((χ₁.evalP : ℂ) + (χ₂.evalP : ℂ)) *
        (sphericalVec p h₁ h₂).1 g := by
  obtain ⟨Tf, hTf_val, hTf_K0⟩ := heckeTp_mem_fixedK0 p (sphericalVec_mem_fixedK0 p h₁ h₂)
  have huniq := eq_smul_sphericalVec_of_mem_fixedK0 p h₁ h₂ hTf_K0
  have hval_g : heckeTp p (sphericalVec p h₁ h₂).1 g =
      heckeTp p (sphericalVec p h₁ h₂).1 1 * (sphericalVec p h₁ h₂).1 g := by
    rw [← hTf_val]
    simpa [Submodule.coe_smul_of_tower] using congrFun (congrArg Subtype.val huniq) g
  rw [hval_g]
  congr 1
  rw [heckeTp_apply]
  have hupper : ∀ j : Fin p, (sphericalVec p h₁ h₂).1 (1 * heckeRepUpper p j) =
      (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (χ₁.evalP : ℂ) := by
    intro j
    rw [one_mul]
    have h := sphericalVec_apply_borel p h₁ h₂ ⟨heckeRepUpper p j, heckeRepUpper_mem_Borel p j⟩
    rw [h]
    have hd0 : borelDiag0 p ⟨heckeRepUpper p j, heckeRepUpper_mem_Borel p j⟩ = padicPrimeUnit p := by
      ext; rfl
    have hd1 : borelDiag1 p ⟨heckeRepUpper p j, heckeRepUpper_mem_Borel p j⟩ = 1 := by
      ext; rfl
    simp only [borelChar, deltaBHalf, MonoidHom.coe_mk, OneHom.coe_mk, hd0, hd1, map_one,
      inv_one, mul_one, Units.val_mul]
    change ((LocalChar.normPowChar p (1 / 2)).evalP : ℂ) * (χ₁.evalP : ℂ) = _
    rw [LocalChar.normPowChar_evalP_val]
  have hlower : (sphericalVec p h₁ h₂).1 (1 * heckeRepLower p) =
      (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (χ₂.evalP : ℂ) := by
    rw [one_mul]
    have h := sphericalVec_apply_borel p h₁ h₂ ⟨heckeRepLower p, heckeRepLower_mem_Borel p⟩
    rw [h]
    have hd0 : borelDiag0 p ⟨heckeRepLower p, heckeRepLower_mem_Borel p⟩ = 1 := by
      ext; rfl
    have hd1 : borelDiag1 p ⟨heckeRepLower p, heckeRepLower_mem_Borel p⟩ = padicPrimeUnit p := by
      ext; rfl
    simp only [borelChar, deltaBHalf, MonoidHom.coe_mk, OneHom.coe_mk, hd0, hd1, map_one,
      one_mul, mul_one, Units.val_mul, Units.val_inv_eq_inv_val]
    change (((LocalChar.normPowChar p (1 / 2)).evalP : ℂ)⁻¹) * (χ₂.evalP : ℂ) = _
    rw [LocalChar.normPowChar_evalP_val]
    congr 1
    rw [← Complex.ofReal_inv, ← Real.rpow_neg (prime_pos_R p).le, neg_neg]
  simp only [hupper, hlower, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpmul : (p : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [show (p : ℂ) = (((p : ℝ) ^ (1 : ℝ) : ℝ) : ℂ) by simp,
      ← Complex.ofReal_mul, ← Real.rpow_add (prime_pos_R p)]
    norm_num
  calc (p : ℂ) * ((((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (χ₁.evalP : ℂ)) +
        (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (χ₂.evalP : ℂ)
      = ((p : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (χ₁.evalP : ℂ) +
        (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (χ₂.evalP : ℂ) := by ring
    _ = (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((χ₁.evalP : ℂ) + (χ₂.evalP : ℂ)) := by
          rw [hpmul]; ring

/-- Normalized Satake eigenvalue theorem: `(T_p^{norm} f₀)(g) = (χ₁(p) + χ₂(p)) * f₀(g)`! -/
theorem heckeTpNorm_sphericalVec {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) (g : GL2Qp p) :
    heckeTpNorm p (sphericalVec p h₁ h₂).1 g =
      ((χ₁.evalP : ℂ) + (χ₂.evalP : ℂ)) * (sphericalVec p h₁ h₂).1 g := by
  change ((((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * heckeTp p (sphericalVec p h₁ h₂).1 g = _
  rw [heckeTp_sphericalVec]
  have hcancel : (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (prime_pos_R p)]; norm_num
  calc (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((χ₁.evalP : ℂ) + (χ₂.evalP : ℂ)) *
          (sphericalVec p h₁ h₂).1 g)
      = ((((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ((χ₁.evalP : ℂ) + (χ₂.evalP : ℂ)) * (sphericalVec p h₁ h₂).1 g := by ring
    _ = ((χ₁.evalP : ℂ) + (χ₂.evalP : ℂ)) * (sphericalVec p h₁ h₂).1 g := by rw [hcancel, one_mul]

end SmoothPrincipalSeries

/-! ## Section 3: Genuine Smooth Steinberg Quotient `SmoothSteinberg p χ`, Iwahori Invariants,
Atkin–Lehner `w_p`, & `U_p` Eigenvalue -/

section SmoothSteinbergRep

variable (p : ℕ) [hp : Fact p.Prime]

/-- The reducible principal series `SmoothInd p (χ · |·|^{-1/2}) (χ · |·|^{1/2})` containing the
1-dimensional character `χ ∘ det` as its unique irreducible subrepresentation and `SmoothSteinberg p χ`
as its unique irreducible quotient. -/
abbrev SteinbergAmbient (χ : LocalChar p) :=
  SmoothInd p (χ * LocalChar.normPowChar p (-(1 / 2))) (χ * LocalChar.normPowChar p (1 / 2))

/-- Exact cancellation of the modular half-power on `SteinbergAmbient p χ`:
`borelChar (χ |·|^{-1/2}) (χ |·|^{1/2}) b = χ(det b)`! -/
theorem borelChar_steinbergAmbient (χ : LocalChar p) (b : Borel p) :
    borelChar p (χ * LocalChar.normPowChar p (-(1 / 2))) (χ * LocalChar.normPowChar p (1 / 2)) b =
      χ.toHom (Matrix.GeneralLinearGroup.det b.1) := by
  rw [borel_det_eq_mul, map_mul]
  simp only [borelChar, deltaBHalf, MonoidHom.coe_mk, OneHom.coe_mk, LocalChar.mul_toHom,
    MonoidHom.mul_apply]
  have hneg : LocalChar.normPowChar p (-(1 / 2)) = (LocalChar.normPowChar p (1 / 2))⁻¹ :=
    LocalChar.normPowChar_neg p (1 / 2)
  rw [hneg, LocalChar.inv_toHom, MonoidHom.inv_apply]
  set u0 := (LocalChar.normPowChar p (1 / 2)).toHom (borelDiag0 p b)
  set u1 := (LocalChar.normPowChar p (1 / 2)).toHom (borelDiag1 p b)
  set c0 := χ.toHom (borelDiag0 p b)
  set c1 := χ.toHom (borelDiag1 p b)
  calc u0 * u1⁻¹ * (c0 * u0⁻¹) * (c1 * u1)
      = (c0 * c1) * (u0 * u0⁻¹) * (u1⁻¹ * u1) := by ac_rfl
    _ = c0 * c1 := by rw [mul_inv_cancel, inv_mul_cancel, mul_one, mul_one]

/-- The 1-dimensional vector `g ↦ χ(det g)` inside `SteinbergAmbient p χ` (for ANY smooth `χ`!). -/
def detCharVec (χ : LocalChar p) : SteinbergAmbient p χ :=
  ⟨fun g => (χ.toHom (Matrix.GeneralLinearGroup.det g) : ℂ),
    ⟨fun b g => by
      dsimp only
      rw [borelChar_steinbergAmbient, map_mul, map_mul, Units.val_mul],
     ⟨χ.condExp, fun g k hk => by
       dsimp only
       have hdet_filt : IsInUnitFilt p χ.condExp (Matrix.GeneralLinearGroup.det k) := by
         refine ⟨hk.1.2, ?_⟩
         by_cases h0 : χ.condExp = 0
         · exact Or.inl h0
         · right
           rcases hk.2 with h0' | hle
           · exact absurd h0' h0
           · have hn : 1 ≤ χ.condExp := Nat.pos_of_ne_zero h0
             have hp_lt1 : (p : ℝ) ^ (-(χ.condExp : ℤ)) < 1 :=
               zpow_lt_one_of_neg₀ (prime_one_lt_R p) (by omega)
             set e00 := k.1 0 0 - 1
             set e11 := k.1 1 1 - 1
             set e01 := k.1 0 1
             set e10 := k.1 1 0
             have he00 : ‖e00‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) := by simpa [e00] using hle 0 0
             have he11 : ‖e11‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) := by simpa [e11] using hle 1 1
             have he01 : ‖e01‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) := by simpa [e01] using hle 0 1
             have he10 : ‖e10‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) := by simpa [e10] using hle 1 0
             have hdet_eq : Matrix.det k.1 - 1 = e00 + e11 + e00 * e11 - e01 * e10 := by
               rw [Matrix.det_fin_two]; simp only [e00, e11, e01, e10]; ring
             change ‖Matrix.det k.1 - 1‖ ≤ _
             rw [hdet_eq, sub_eq_add_neg]
             have hmul1 : ‖e00 * e11‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) := by
               rw [norm_mul]
               calc ‖e00‖ * ‖e11‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) * 1 :=
                     mul_le_mul he00 (he11.trans hp_lt1.le) (norm_nonneg _) (zpow_pos (prime_pos_R p) _).le
                 _ = (p : ℝ) ^ (-(χ.condExp : ℤ)) := mul_one _
             have hmul2 : ‖-(e01 * e10)‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) := by
               rw [norm_neg, norm_mul]
               calc ‖e01‖ * ‖e10‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) * 1 :=
                     mul_le_mul he01 (he10.trans hp_lt1.le) (norm_nonneg _) (zpow_pos (prime_pos_R p) _).le
                 _ = (p : ℝ) ^ (-(χ.condExp : ℤ)) := mul_one _
             exact (Padic.nonarchimedean _ _).trans (max_le
               ((Padic.nonarchimedean _ _).trans (max_le
                 ((Padic.nonarchimedean _ _).trans (max_le he00 he11)) hmul1)) hmul2)
       rw [map_mul, map_mul, χ.condExp_spec _ hdet_filt, mul_one]⟩⟩⟩

@[simp]
lemma detCharVec_apply (χ : LocalChar p) (g : GL2Qp p) :
    (detCharVec p χ).1 g = (χ.toHom (Matrix.GeneralLinearGroup.det g) : ℂ) := rfl

lemma rightAction_detCharVec (χ : LocalChar p) (h : GL2Qp p) :
    rightAction p _ _ h (detCharVec p χ) =
      ((χ.toHom (Matrix.GeneralLinearGroup.det h) : ℂ)) • detCharVec p χ := by
  ext g
  simp [map_mul, mul_comm]

/-- **Genuine 1-Dimensional `GL₂(ℚ_p)`-Subrepresentation `ℂ · (χ ∘ det) ↪ SteinbergAmbient p χ`**. -/
def oneDimSubrep (χ : LocalChar p) : Submodule ℂ (SteinbergAmbient p χ) :=
  Submodule.span ℂ {detCharVec p χ}

lemma mem_oneDimSubrep_iff (χ : LocalChar p) (f : SteinbergAmbient p χ) :
    f ∈ oneDimSubrep p χ ↔ ∃ c : ℂ, f = c • detCharVec p χ := by
  rw [oneDimSubrep, Submodule.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

lemma oneDimSubrep_invariant (χ : LocalChar p) (h : GL2Qp p) :
    Submodule.map (rightAction p _ _ h) (oneDimSubrep p χ) ≤ oneDimSubrep p χ := by
  rintro _ ⟨f, hf, rfl⟩
  change f ∈ oneDimSubrep p χ at hf
  rw [mem_oneDimSubrep_iff] at hf ⊢
  rcases hf with ⟨c, rfl⟩
  refine ⟨c * (χ.toHom (Matrix.GeneralLinearGroup.det h) : ℂ), ?_⟩
  rw [map_smul, rightAction_detCharVec, smul_smul]

theorem finrank_oneDimSubrep (χ : LocalChar p) :
    Module.finrank ℂ (oneDimSubrep p χ) = 1 := by
  have hne : detCharVec p χ ≠ 0 := by
    intro h0
    have h1 := congrFun (congrArg Subtype.val h0) 1
    simp at h1
  exact finrank_span_singleton hne

/-- **GENUINE SMOOTH STEINBERG QUOTIENT `SmoothSteinberg p χ`**:
`SmoothInd p (χ · |·|^{-1/2}) (χ · |·|^{1/2}) / (ℂ · (χ ∘ det))`! -/
abbrev SmoothSteinberg (χ : LocalChar p) :=
  (SteinbergAmbient p χ) ⧸ (oneDimSubrep p χ)

/-- Quotient projection `SteinbergAmbient p χ →ₗ[ℂ] SmoothSteinberg p χ`. -/
abbrev steinbergMk (χ : LocalChar p) : SteinbergAmbient p χ →ₗ[ℂ] SmoothSteinberg p χ :=
  Submodule.mkQ (oneDimSubrep p χ)

/-- **Genuine Induced `GL (Fin 2) ℚ_[p]`-Action** on the Steinberg quotient `SmoothSteinberg p χ`. -/
def steinbergAction (χ : LocalChar p) (h : GL2Qp p) :
    SmoothSteinberg p χ →ₗ[ℂ] SmoothSteinberg p χ :=
  Submodule.mapQ (oneDimSubrep p χ) (oneDimSubrep p χ) (rightAction p _ _ h)
    (by
      intro f hf
      exact oneDimSubrep_invariant p χ h ⟨f, hf, rfl⟩)

@[simp]
lemma steinbergAction_mk (χ : LocalChar p) (h : GL2Qp p) (f : SteinbergAmbient p χ) :
    steinbergAction p χ h (steinbergMk p χ f) = steinbergMk p χ (rightAction p _ _ h f) := rfl

lemma steinbergAction_one (χ : LocalChar p) (v : SmoothSteinberg p χ) :
    steinbergAction p χ 1 v = v := by
  induction v using Submodule.Quotient.induction_on with
  | _ f => exact congrArg (steinbergMk p χ) (rightAction_one p _ _ f)

lemma steinbergAction_mul (χ : LocalChar p) (h₁ h₂ : GL2Qp p) (v : SmoothSteinberg p χ) :
    steinbergAction p χ (h₁ * h₂) v =
      steinbergAction p χ h₁ (steinbergAction p χ h₂ v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ f => exact congrArg (steinbergMk p χ) (rightAction_mul p _ _ h₁ h₂ f)

/-- The `H`-invariant submodule `(SmoothSteinberg p χ)^H` for any subgroup `H ≤ GL₂(ℚ_p)`. -/
def steinbergFixed (χ : LocalChar p) (H : Subgroup (GL2Qp p)) :
    Submodule ℂ (SmoothSteinberg p χ) where
  carrier := { v : SmoothSteinberg p χ | ∀ h ∈ H, steinbergAction p χ h v = v }
  zero_mem' h _ := map_zero _
  add_mem' {v₁ v₂} hv₁ hv₂ h hh := by rw [map_add, hv₁ h hh, hv₂ h hh]
  smul_mem' c {v} hv h hh := by rw [map_smul, hv h hh]

/-! ### Exact Lifting of `H`-Invariants from `SmoothSteinberg p χ` to `SteinbergAmbient p χ` (for `H ≤ K₀`) -/

/-- **Crucial Exactness Lemma**: for unramified `χ` and ANY subgroup `H ≤ K₀`, every `H`-invariant
vector `[f] ∈ (SmoothSteinberg p χ)^H` lifts to an actual `H`-invariant function
`f ∈ (SteinbergAmbient p χ)^H` (because `H / (H ∩ K_n)` is torsion, so every additive cocycle
`H →+ ℂ` vanishes identically!). -/
theorem lift_steinbergFixed_of_le_K0 {χ : LocalChar p} (hχ : χ.IsUnramified)
    {H : Subgroup (GL2Qp p)} (hHK0 : H ≤ K0 p) {f : SteinbergAmbient p χ}
    (hf : steinbergMk p χ f ∈ steinbergFixed p χ H) :
    f ∈ fixedSubmodule p _ _ H := by
  have hdet_triv : ∀ k ∈ K0 p, rightAction p _ _ k (detCharVec p χ) = detCharVec p χ := by
    intro k hk
    rw [rightAction_detCharVec, hχ (Matrix.GeneralLinearGroup.det k) hk.2, Units.val_one, one_smul]
  have hdiff : ∀ h ∈ H, ∃ c : ℂ, rightAction p _ _ h f - f = c • detCharVec p χ := by
    intro h hh
    have hq := hf h hh
    rw [steinbergAction_mk, ← sub_eq_zero, ← map_sub] at hq
    exact (mem_oneDimSubrep_iff p χ _).mp ((Submodule.Quotient.mk_eq_zero _).mp hq)
  intro h hh
  obtain ⟨c, hc⟩ := hdiff h hh
  have hpow_all : ∀ r : ℕ, rightAction p _ _ (h ^ r) f - f = ((r : ℕ) : ℂ) • (c • detCharVec p χ) := by
    intro r
    induction r with
    | zero => simp [rightAction_one]
    | succ r ih =>
      rw [pow_succ, rightAction_mul]
      have hstep : rightAction p _ _ (h ^ r) (rightAction p _ _ h f) - f =
          rightAction p _ _ (h ^ r) (rightAction p _ _ h f - f) +
            (rightAction p _ _ (h ^ r) f - f) := by
        rw [map_sub]; abel
      rw [hstep, hc, map_smul, hdet_triv (h ^ r) ((K0 p).pow_mem (hHK0 hh) r), ih]
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1
      push_cast
      ring
  rcases f.2.2 with ⟨n, hn⟩
  obtain ⟨m, hm_pos, hkm⟩ := exists_pow_mem_principalCongruence p (hHK0 hh) n
  have hpow_eq := hpow_all m
  have hzero : rightAction p _ _ (h ^ m) f - f = 0 := by
    rw [sub_eq_zero]
    ext g
    exact hn g (h ^ m) hkm
  rw [hzero] at hpow_eq
  have heval1 := congrFun (congrArg Subtype.val hpow_eq) 1
  simp only [Submodule.coe_zero, Pi.zero_apply, Submodule.coe_smul_of_tower, Pi.smul_apply,
    smul_eq_mul, detCharVec_apply, map_one, Units.val_one, mul_one] at heval1
  have hm_ne : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
  have hc0 : c = 0 := (mul_eq_zero.mp heval1.symm).resolve_left hm_ne
  rw [hc0, zero_smul] at hc
  exact sub_eq_zero.mp hc

/-- **VANISHING OF `K₀`-INVARIANTS OF THE SMOOTH STEINBERG REPRESENTATION**:
`(SmoothSteinberg p χ)^{K₀} = 0` for every unramified `χ : LocalChar p`! -/
theorem steinbergFixed_K0_eq_bot {χ : LocalChar p} (hχ : χ.IsUnramified) :
    steinbergFixed p χ (K0 p) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  induction v using Submodule.Quotient.induction_on with
  | _ f =>
    have hfK0 : f ∈ fixedSubmodule p _ _ (K0 p) :=
      lift_steinbergFixed_of_le_K0 p hχ le_rfl hv
    have h₁ : (χ * LocalChar.normPowChar p (-(1 / 2))).IsUnramified :=
      LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
    have h₂ : (χ * LocalChar.normPowChar p (1 / 2)).IsUnramified :=
      LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
    have hdet_eq_sph : detCharVec p χ = sphericalVec p h₁ h₂ := by
      ext g
      obtain ⟨b, k, rfl⟩ := iwasawa_decomp p g
      rw [detCharVec_apply, map_mul, map_mul, hχ (Matrix.GeneralLinearGroup.det k.1) k.2.2,
        mul_one, sphericalVec_apply_iwasawa, borelChar_steinbergAmbient]
    have huniq := eq_smul_sphericalVec_of_mem_fixedK0 p h₁ h₂ hfK0
    rw [← hdet_eq_sph] at huniq
    change Submodule.Quotient.mk f = (0 : SmoothSteinberg p χ)
    rw [Submodule.Quotient.mk_eq_zero, mem_oneDimSubrep_iff]
    exact ⟨f.1 1, huniq⟩

theorem finrank_steinbergFixed_K0 {χ : LocalChar p} (hχ : χ.IsUnramified) :
    Module.finrank ℂ (steinbergFixed p χ (K0 p)) = 0 := by
  rw [steinbergFixed_K0_eq_bot p hχ, finrank_bot]

/-! ### Exact 2D Iwahori-Fixed Space of `SmoothInd` & Exact 1D Iwahori-Fixed Space of `SmoothSteinberg` -/

lemma borelChar_iwahori_unique {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    {b₁ b₂ : Borel p} {i₁ i₂ : Iwahori p} (heq : b₁.1 * i₁.1 = b₂.1 * i₂.1) :
    borelChar p χ₁ χ₂ b₁ = borelChar p χ₁ χ₂ b₂ :=
  borelChar_iwasawa_unique p h₁ h₂ (k₁ := ⟨i₁.1, Iwahori_le_K0 p i₁.2⟩)
    (k₂ := ⟨i₂.1, Iwahori_le_K0 p i₂.2⟩) heq

lemma borelChar_iwahori_weyl_unique {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    {b₁ b₂ : Borel p} {i₁ i₂ : Iwahori p}
    (heq : b₁.1 * weylGL2 p * i₁.1 = b₂.1 * weylGL2 p * i₂.1) :
    borelChar p χ₁ χ₂ b₁ = borelChar p χ₁ χ₂ b₂ := by
  have hk₁ : weylGL2 p * i₁.1 ∈ K0 p := (K0 p).mul_mem (weylGL2_mem_K0 p) (Iwahori_le_K0 p i₁.2)
  have hk₂ : weylGL2 p * i₂.1 ∈ K0 p := (K0 p).mul_mem (weylGL2_mem_K0 p) (Iwahori_le_K0 p i₂.2)
  have heq' : b₁.1 * (weylGL2 p * i₁.1) = b₂.1 * (weylGL2 p * i₂.1) := by
    simpa [mul_assoc] using heq
  exact borelChar_iwasawa_unique p h₁ h₂ (k₁ := ⟨_, hk₁⟩) (k₂ := ⟨_, hk₂⟩) heq'

/-- The first Iwahori-fixed basis vector `φ₁ ∈ (SmoothInd p χ₁ χ₂)^I`: supported on `B · I`,
with `φ₁(1) = 1` and `φ₁(w) = 0`. -/
def iwahoriVec1 {χ₁ χ₂ : LocalChar p} (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    SmoothInd p χ₁ χ₂ :=
  letI := Classical.decPred (fun g : GL2Qp p => ∃ (b : Borel p) (i : Iwahori p), g = b.1 * i.1)
  let toFun : GL2Qp p → ℂ := fun g =>
    if h : ∃ (b : Borel p) (i : Iwahori p), g = b.1 * i.1 then
      (borelChar p χ₁ χ₂ (Classical.choose h) : ℂ)
    else 0
  have hval_BI : ∀ (b : Borel p) (i : Iwahori p),
      toFun (b.1 * i.1) = (borelChar p χ₁ χ₂ b : ℂ) := by
    intro b i
    have hex : ∃ (b' : Borel p) (i' : Iwahori p), b.1 * i.1 = b'.1 * i'.1 := ⟨b, i, rfl⟩
    simp only [toFun, dif_pos hex]
    obtain ⟨i', hi'⟩ := Classical.choose_spec hex
    exact congrArg Units.val (borelChar_iwahori_unique p h₁ h₂ hi'.symm)
  have hval_BwI : ∀ (b : Borel p) (i : Iwahori p),
      toFun (b.1 * weylGL2 p * i.1) = 0 := by
    intro b i
    have hnot : ¬∃ (b' : Borel p) (i' : Iwahori p), b.1 * weylGL2 p * i.1 = b'.1 * i'.1 := by
      rintro ⟨b', i', heq⟩
      exact gl2_iwahori_bruhat_disjoint p b' b i' i heq.symm
    simp only [toFun, dif_neg hnot]
  ⟨toFun,
    ⟨fun b g => by
      rcases gl2_iwahori_bruhat p g with ⟨b', i', rfl⟩ | ⟨b', i', rfl⟩
      · have hmul : b.1 * (b'.1 * i'.1) = (b * b').1 * i'.1 := by
          simp only [Subgroup.coe_mul, mul_assoc]
        rw [hmul, hval_BI (b * b') i', hval_BI b' i', map_mul, Units.val_mul]
      · have hmul : b.1 * (b'.1 * weylGL2 p * i'.1) = (b * b').1 * weylGL2 p * i'.1 := by
          simp only [Subgroup.coe_mul, mul_assoc]
        rw [hmul, hval_BwI (b * b') i', hval_BwI b' i', mul_zero],
     ⟨1, fun g k hk => by
       have hkI : k ∈ Iwahori p := principalCongruence_one_le_Iwahori p hk
       rcases gl2_iwahori_bruhat p g with ⟨b', i', rfl⟩ | ⟨b', i', rfl⟩
       · have hmul : b'.1 * i'.1 * k = b'.1 * (i' * ⟨k, hkI⟩).1 := by
           simp only [Subgroup.coe_mul, mul_assoc]
         rw [hmul, hval_BI b' (i' * ⟨k, hkI⟩), hval_BI b' i']
       · have hmul : b'.1 * weylGL2 p * i'.1 * k = b'.1 * weylGL2 p * (i' * ⟨k, hkI⟩).1 := by
           simp only [Subgroup.coe_mul, mul_assoc]
         rw [hmul, hval_BwI b' (i' * ⟨k, hkI⟩), hval_BwI b' i']⟩⟩⟩

/-- The second Iwahori-fixed basis vector `φ_w ∈ (SmoothInd p χ₁ χ₂)^I`: supported on `B · w · I`,
with `φ_w(1) = 0` and `φ_w(w) = 1`. -/
def iwahoriVecW {χ₁ χ₂ : LocalChar p} (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    SmoothInd p χ₁ χ₂ :=
  sphericalVec p h₁ h₂ - iwahoriVec1 p h₁ h₂

theorem iwahoriVec1_apply_BI {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) (b : Borel p) (i : Iwahori p) :
    (iwahoriVec1 p h₁ h₂).1 (b.1 * i.1) = (borelChar p χ₁ χ₂ b : ℂ) := by
  classical
  have hex : ∃ (b' : Borel p) (i' : Iwahori p), b.1 * i.1 = b'.1 * i'.1 := ⟨b, i, rfl⟩
  dsimp only [iwahoriVec1]
  rw [dif_pos hex]
  obtain ⟨i', hi'⟩ := Classical.choose_spec hex
  exact congrArg Units.val (borelChar_iwahori_unique p h₁ h₂ hi'.symm)

theorem iwahoriVec1_apply_BwI {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) (b : Borel p) (i : Iwahori p) :
    (iwahoriVec1 p h₁ h₂).1 (b.1 * weylGL2 p * i.1) = 0 := by
  classical
  have hnot : ¬∃ (b' : Borel p) (i' : Iwahori p), b.1 * weylGL2 p * i.1 = b'.1 * i'.1 := by
    rintro ⟨b', i', heq⟩
    exact gl2_iwahori_bruhat_disjoint p b' b i' i heq.symm
  dsimp only [iwahoriVec1]
  rw [dif_neg hnot]

@[simp]
theorem iwahoriVec1_apply_one {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    (iwahoriVec1 p h₁ h₂).1 1 = 1 := by
  simpa using iwahoriVec1_apply_BI p h₁ h₂ 1 1

@[simp]
theorem iwahoriVec1_apply_weyl {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    (iwahoriVec1 p h₁ h₂).1 (weylGL2 p) = 0 := by
  simpa using iwahoriVec1_apply_BwI p h₁ h₂ 1 1

@[simp]
theorem iwahoriVecW_apply_one {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    (iwahoriVecW p h₁ h₂).1 1 = 0 := by
  simp [iwahoriVecW]

@[simp]
theorem iwahoriVecW_apply_weyl {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    (iwahoriVecW p h₁ h₂).1 (weylGL2 p) = 1 := by
  have hs : (sphericalVec p h₁ h₂).1 (weylGL2 p) = 1 := by
    have h := sphericalVec_apply_iwasawa p h₁ h₂ 1 ⟨weylGL2 p, weylGL2_mem_K0 p⟩
    simpa using h
  simp [iwahoriVecW, hs]

theorem iwahoriVec1_mem_fixedI {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    iwahoriVec1 p h₁ h₂ ∈ fixedSubmodule p χ₁ χ₂ (Iwahori p) := by
  rw [mem_fixedSubmodule_iff]
  intro g k hk
  rcases gl2_iwahori_bruhat p g with ⟨b', i', rfl⟩ | ⟨b', i', rfl⟩
  · have hmul : b'.1 * i'.1 * k = b'.1 * (i' * ⟨k, hk⟩).1 := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [hmul, iwahoriVec1_apply_BI, iwahoriVec1_apply_BI]
  · have hmul : b'.1 * weylGL2 p * i'.1 * k = b'.1 * weylGL2 p * (i' * ⟨k, hk⟩).1 := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [hmul, iwahoriVec1_apply_BwI, iwahoriVec1_apply_BwI]

theorem iwahoriVecW_mem_fixedI {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    iwahoriVecW p h₁ h₂ ∈ fixedSubmodule p χ₁ χ₂ (Iwahori p) := by
  have hsI : sphericalVec p h₁ h₂ ∈ fixedSubmodule p χ₁ χ₂ (Iwahori p) :=
    fun h hh => sphericalVec_mem_fixedK0 p h₁ h₂ h (Iwahori_le_K0 p hh)
  exact (fixedSubmodule p χ₁ χ₂ (Iwahori p)).sub_mem hsI (iwahoriVec1_mem_fixedI p h₁ h₂)

/-- Every Iwahori-fixed function `f ∈ (SmoothInd p χ₁ χ₂)^I` is uniquely determined by
`(f(1), f(w))`: `f = f(1) • φ₁ + f(w) • φ_w`! -/
theorem eq_lincomb_iwahoriVec_of_mem_fixedI {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified)
    {f : SmoothInd p χ₁ χ₂} (hf : f ∈ fixedSubmodule p χ₁ χ₂ (Iwahori p)) :
    f = (f.1 1) • iwahoriVec1 p h₁ h₂ + (f.1 (weylGL2 p)) • iwahoriVecW p h₁ h₂ := by
  ext g
  rcases gl2_iwahori_bruhat p g with ⟨b, i, rfl⟩ | ⟨b, i, rfl⟩
  · have hfi : f.1 i.1 = f.1 1 := by
      simpa using (mem_fixedSubmodule_iff p).mp hf 1 i.1 i.2
    have hW : (iwahoriVecW p h₁ h₂).1 (b.1 * i.1) = 0 := by
      change (sphericalVec p h₁ h₂).1 (b.1 * i.1) - (iwahoriVec1 p h₁ h₂).1 (b.1 * i.1) = 0
      rw [sphericalVec_apply_iwasawa p h₁ h₂ b ⟨i.1, Iwahori_le_K0 p i.2⟩,
        iwahoriVec1_apply_BI, sub_self]
    rw [f.2.1 b i.1, hfi]
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, iwahoriVec1_apply_BI, hW, mul_zero, add_zero]
    ring
  · have hfwi : f.1 (weylGL2 p * i.1) = f.1 (weylGL2 p) :=
      (mem_fixedSubmodule_iff p).mp hf (weylGL2 p) i.1 i.2
    have hW : (iwahoriVecW p h₁ h₂).1 (b.1 * weylGL2 p * i.1) = (borelChar p χ₁ χ₂ b : ℂ) := by
      change (sphericalVec p h₁ h₂).1 (b.1 * weylGL2 p * i.1) -
        (iwahoriVec1 p h₁ h₂).1 (b.1 * weylGL2 p * i.1) = _
      have hmul : b.1 * weylGL2 p * i.1 = b.1 * (weylGL2 p * i.1) := mul_assoc _ _ _
      have hwk : weylGL2 p * i.1 ∈ K0 p := (K0 p).mul_mem (weylGL2_mem_K0 p) (Iwahori_le_K0 p i.2)
      rw [iwahoriVec1_apply_BwI, sub_zero, hmul,
        sphericalVec_apply_iwasawa p h₁ h₂ b ⟨weylGL2 p * i.1, hwk⟩]
    rw [mul_assoc, f.2.1 b (weylGL2 p * i.1), hfwi, ← mul_assoc]
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, iwahoriVec1_apply_BwI, mul_zero, zero_add, hW]
    ring

/-- Explicit linear isomorphism `(SmoothInd p χ₁ χ₂)^I ≃ₗ[ℂ] ℂ × ℂ` (`f ↦ (f(1), f(w))`). -/
def iwahoriFixedEquiv {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    fixedSubmodule p χ₁ χ₂ (Iwahori p) ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun f := (f.1.1 1, f.1.1 (weylGL2 p))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v :=
    ⟨v.1 • iwahoriVec1 p h₁ h₂ + v.2 • iwahoriVecW p h₁ h₂,
      (fixedSubmodule p χ₁ χ₂ (Iwahori p)).add_mem
        ((fixedSubmodule p χ₁ χ₂ (Iwahori p)).smul_mem v.1 (iwahoriVec1_mem_fixedI p h₁ h₂))
        ((fixedSubmodule p χ₁ χ₂ (Iwahori p)).smul_mem v.2 (iwahoriVecW_mem_fixedI p h₁ h₂))⟩
  left_inv f := by
    ext g
    exact congrFun (congrArg Subtype.val (eq_lincomb_iwahoriVec_of_mem_fixedI p h₁ h₂ f.2).symm) g
  right_inv v := by
    ext <;> simp

/-- **EXACT 2D IWAHORI-FIXED SPACE OF PRINCIPAL SERIES**: `dim_ℂ (SmoothInd p χ₁ χ₂)^I = 2`! -/
theorem finrank_iwahoriFixed {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    Module.finrank ℂ (fixedSubmodule p χ₁ χ₂ (Iwahori p)) = 2 := by
  rw [(iwahoriFixedEquiv p h₁ h₂).finrank_eq, Module.finrank_prod, Module.finrank_self]

/-- The canonical nonzero Iwahori-fixed generator `v_St = [φ₁] ∈ (SmoothSteinberg p χ)^I`. -/
def steinbergIwahoriGen {χ : LocalChar p} (hχ : χ.IsUnramified) : SmoothSteinberg p χ :=
  steinbergMk p χ (iwahoriVec1 p
    (LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _))
    (LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)))

theorem steinbergIwahoriGen_mem_fixedI {χ : LocalChar p} (hχ : χ.IsUnramified) :
    steinbergIwahoriGen p hχ ∈ steinbergFixed p χ (Iwahori p) := by
  intro h hh
  rw [steinbergIwahoriGen, steinbergAction_mk]
  congr 1
  exact iwahoriVec1_mem_fixedI p _ _ h hh

/-- Explicit linear isomorphism `(SmoothSteinberg p χ)^I ≃ₗ[ℂ] ℂ` (`[f] ↦ f(1) - f(w)`),
proving `dim_ℂ (SmoothSteinberg p χ)^I = 1` unconditionally! -/
def steinbergIwahoriFixedEquiv {χ : LocalChar p} (hχ : χ.IsUnramified) :
    steinbergFixed p χ (Iwahori p) ≃ₗ[ℂ] ℂ :=
  let h₁ : (χ * LocalChar.normPowChar p (-(1 / 2))).IsUnramified :=
    LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
  let h₂ : (χ * LocalChar.normPowChar p (1 / 2)).IsUnramified :=
    LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
  let evalDiff : SteinbergAmbient p χ →ₗ[ℂ] ℂ :=
    { toFun := fun f => f.1 1 - f.1 (weylGL2 p)
      map_add' := fun f₁ f₂ => by simp; ring
      map_smul' := fun c f => by simp; ring }
  have hker : oneDimSubrep p χ ≤ LinearMap.ker evalDiff := by
    intro f hf
    rw [mem_oneDimSubrep_iff] at hf
    rcases hf with ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    change c * (detCharVec p χ).1 1 - c * (detCharVec p χ).1 (weylGL2 p) = 0
    have hw_det : ‖((Matrix.GeneralLinearGroup.det (weylGL2 p) : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 :=
      (weylGL2_mem_K0 p).2
    simp only [detCharVec_apply, map_one, hχ _ hw_det, Units.val_one, sub_self]
  let descEval : SmoothSteinberg p χ →ₗ[ℂ] ℂ := Submodule.liftQ (oneDimSubrep p χ) evalDiff hker
  { toFun := fun v => descEval v.1
    map_add' := fun v₁ v₂ => map_add descEval v₁.1 v₂.1
    map_smul' := fun c v => map_smul descEval c v.1
    invFun := fun c => ⟨c • steinbergIwahoriGen p hχ,
      (steinbergFixed p χ (Iwahori p)).smul_mem c (steinbergIwahoriGen_mem_fixedI p hχ)⟩
    left_inv := fun v => by
      rcases v with ⟨v, hv⟩
      ext
      induction v using Submodule.Quotient.induction_on with
      | _ f =>
        have hfI : f ∈ fixedSubmodule p _ _ (Iwahori p) :=
          lift_steinbergFixed_of_le_K0 p hχ (Iwahori_le_K0 p) hv
        have hdecomp := eq_lincomb_iwahoriVec_of_mem_fixedI p h₁ h₂ hfI
        have hdet_eq_sph : detCharVec p χ = sphericalVec p h₁ h₂ := by
          ext g
          obtain ⟨b, k, rfl⟩ := iwasawa_decomp p g
          rw [detCharVec_apply, map_mul, map_mul, hχ (Matrix.GeneralLinearGroup.det k.1) k.2.2,
            mul_one, sphericalVec_apply_iwasawa, borelChar_steinbergAmbient]
        have hdiff_sub : f - (f.1 1 - f.1 (weylGL2 p)) • iwahoriVec1 p h₁ h₂ =
            (f.1 (weylGL2 p)) • detCharVec p χ := by
          rw [hdet_eq_sph]
          calc f - (f.1 1 - f.1 (weylGL2 p)) • iwahoriVec1 p h₁ h₂
              = ((f.1 1) • iwahoriVec1 p h₁ h₂ +
                  (f.1 (weylGL2 p)) • (sphericalVec p h₁ h₂ - iwahoriVec1 p h₁ h₂)) -
                  (f.1 1 - f.1 (weylGL2 p)) • iwahoriVec1 p h₁ h₂ := by
                congr 1
            _ = (f.1 (weylGL2 p)) • sphericalVec p h₁ h₂ := by module
        change (f.1 1 - f.1 (weylGL2 p)) • steinbergMk p χ (iwahoriVec1 p h₁ h₂) = steinbergMk p χ f
        rw [← map_smul, eq_comm, ← sub_eq_zero, ← map_sub]
        change Submodule.Quotient.mk (f - (f.1 1 - f.1 (weylGL2 p)) • iwahoriVec1 p h₁ h₂) =
          (0 : SmoothSteinberg p χ)
        rw [Submodule.Quotient.mk_eq_zero, mem_oneDimSubrep_iff]
        exact ⟨f.1 (weylGL2 p), hdiff_sub⟩
    right_inv := fun c => by
      change descEval (c • steinbergMk p χ (iwahoriVec1 p h₁ h₂)) = c
      rw [map_smul]
      change c * ((iwahoriVec1 p h₁ h₂).1 1 - (iwahoriVec1 p h₁ h₂).1 (weylGL2 p)) = c
      simp }

/-- **EXACT 1D IWAHORI-FIXED SPACE OF THE SMOOTH STEINBERG REPRESENTATION**:
`dim_ℂ (SmoothSteinberg p χ)^I = 1` for every unramified `χ : LocalChar p`! -/
theorem finrank_steinbergFixed_iwahori {χ : LocalChar p} (hχ : χ.IsUnramified) :
    Module.finrank ℂ (steinbergFixed p χ (Iwahori p)) = 1 := by
  rw [(steinbergIwahoriFixedEquiv p hχ).finrank_eq, Module.finrank_self]

theorem eq_smul_steinbergIwahoriGen {χ : LocalChar p} (hχ : χ.IsUnramified)
    {v : SmoothSteinberg p χ} (hv : v ∈ steinbergFixed p χ (Iwahori p)) :
    ∃ c : ℂ, v = c • steinbergIwahoriGen p hχ := by
  refine ⟨steinbergIwahoriFixedEquiv p hχ ⟨v, hv⟩, ?_⟩
  have h := (steinbergIwahoriFixedEquiv p hχ).left_inv ⟨v, hv⟩
  exact (congrArg Subtype.val h).symm

/-! ### Concrete Atkin–Lehner Involution `w_p = !![0, 1; p, 0]` & Exact Eigenvalue `-χ(p)` -/

/-- The concrete Atkin–Lehner matrix `w_p = !![0, 1; p, 0] ∈ GL (Fin 2) ℚ_[p]`. -/
def atkinLehnerGL2 : GL2Qp p :=
  mkGL2 p (a := 0) (b := 1) (c := (p : ℚ_[p])) (d := 0)
    (by simpa using neg_ne_zero.mpr (prime_ne_zero_padic p))

lemma atkinLehnerGL2_eq_diag_mul_weyl :
    atkinLehnerGL2 p = diagGL2 p 1 (padicPrimeUnit p) * weylGL2 p := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehnerGL2, diagGL2, weylGL2, Matrix.mul_apply, Fin.sum_univ_two]

lemma weylGL2_mul_atkinLehnerGL2 :
    weylGL2 p * atkinLehnerGL2 p = diagGL2 p (padicPrimeUnit p) 1 := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinLehnerGL2, diagGL2, weylGL2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `w_p = !![0, 1; p, 0]` normalizes the Iwahori subgroup `Iwahori p`! -/
theorem atkinLehner_normalizes_iwahori {i : GL2Qp p} (hi : i ∈ Iwahori p) :
    atkinLehnerGL2 p * i * (atkinLehnerGL2 p)⁻¹ ∈ Iwahori p := by
  have hp_ne : (p : ℚ_[p]) ≠ 0 := prime_ne_zero_padic p
  have hp_pos : (0 : ℝ) < (p : ℝ) := prime_pos_R p
  have hpinv_norm : ‖(p : ℚ_[p])⁻¹‖ = (p : ℝ) := by rw [norm_inv, Padic.norm_p, inv_inv]
  have hc_le : ‖i.1 1 0‖ ≤ (p : ℝ)⁻¹ := norm_le_inv_p_of_lt_one p hi.2
  have hconj_val : (atkinLehnerGL2 p * i * (atkinLehnerGL2 p)⁻¹ : GL2Qp p).1 =
      !![i.1 1 1, (p : ℚ_[p])⁻¹ * i.1 1 0; (p : ℚ_[p]) * i.1 0 1, i.1 0 0] := by
    ext r s
    change (((atkinLehnerGL2 p).1 * i.1) * ((atkinLehnerGL2 p)⁻¹ : GL2Qp p).1) r s = _
    rw [gl2_inv_val]
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, atkinLehnerGL2,
        Matrix.det_fin_two, hp_ne]
    · ring
    · field_simp [hp_ne]
  refine ⟨⟨fun r s => ?_, ?_⟩, ?_⟩
  · rw [hconj_val]
    fin_cases r <;> fin_cases s
    · simpa using hi.1.1 1 1
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_mul, hpinv_norm]
      calc (p : ℝ) * ‖i.1 1 0‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hc_le hp_pos.le
        _ = 1 := mul_inv_cancel₀ hp_pos.ne'
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_mul, Padic.norm_p]
      calc (p : ℝ)⁻¹ * ‖i.1 0 1‖ ≤ (p : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (hi.1.1 0 1) (inv_nonneg.mpr hp_pos.le)
        _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ (prime_one_lt_R p).le
    · simpa using hi.1.1 0 0
  · change ‖Matrix.det ((atkinLehnerGL2 p).1 * i.1 * ((atkinLehnerGL2 p)⁻¹ : GL2Qp p).1)‖ = 1
    rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hi.1.2, mul_one]
    have hmul : Matrix.det (atkinLehnerGL2 p).1 * Matrix.det ((atkinLehnerGL2 p)⁻¹ : GL2Qp p).1 = 1 := by
      rw [← Matrix.det_mul]
      change Matrix.det ((atkinLehnerGL2 p * (atkinLehnerGL2 p)⁻¹ : GL2Qp p).1) = 1
      rw [mul_inv_cancel]; simp
    rw [← norm_mul, hmul, norm_one]
  · rw [hconj_val]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, norm_mul, Padic.norm_p]
    calc (p : ℝ)⁻¹ * ‖i.1 0 1‖ ≤ (p : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hi.1.1 0 1) (inv_nonneg.mpr hp_pos.le)
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ (prime_one_lt_R p)

/-- **EXACT ATKIN–LEHNER EIGENVALUE ON `(SmoothSteinberg p χ)^I`**:
`R(w_p) v = -χ(p) • v` for EVERY Iwahori-fixed vector `v ∈ (SmoothSteinberg p χ)^I`! -/
theorem steinbergAction_atkinLehner_eigenvalue {χ : LocalChar p} (hχ : χ.IsUnramified)
    {v : SmoothSteinberg p χ} (hv : v ∈ steinbergFixed p χ (Iwahori p)) :
    steinbergAction p χ (atkinLehnerGL2 p) v = -((χ.evalP : ℂ)) • v := by
  obtain ⟨c, rfl⟩ := eq_smul_steinbergIwahoriGen p hχ hv
  rw [map_smul, smul_comm]
  congr 1
  set h₁ : (χ * LocalChar.normPowChar p (-(1 / 2))).IsUnramified :=
    LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
  set h₂ : (χ * LocalChar.normPowChar p (1 / 2)).IsUnramified :=
    LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
  set φ₁ := iwahoriVec1 p h₁ h₂
  set φw := iwahoriVecW p h₁ h₂
  have hwp_I : rightAction p _ _ (atkinLehnerGL2 p) φ₁ ∈ fixedSubmodule p _ _ (Iwahori p) := by
    intro i hi
    rw [← rightAction_mul]
    have hconj : atkinLehnerGL2 p * i * (atkinLehnerGL2 p)⁻¹ ∈ Iwahori p :=
      atkinLehner_normalizes_iwahori p hi
    have hrew : i * atkinLehnerGL2 p = atkinLehnerGL2 p * ((atkinLehnerGL2 p)⁻¹ * i * atkinLehnerGL2 p) := by
      group
    -- Actually rightAction_mul: R(i) (R(w_p) φ₁) = R(i * w_p) φ₁; need w_p⁻¹ * i * w_p ∈ I!
    have hwp2 : atkinLehnerGL2 p * atkinLehnerGL2 p = diagGL2 p (padicPrimeUnit p) (padicPrimeUnit p) := by
      apply Units.ext; ext r s
      fin_cases r <;> fin_cases s <;>
        simp [atkinLehnerGL2, diagGL2, Matrix.mul_apply, Fin.sum_univ_two]
    have hconj' : (atkinLehnerGL2 p)⁻¹ * i * atkinLehnerGL2 p ∈ Iwahori p := by
      -- Since w_p² = p · I₂ is central, w_p⁻¹ * i * w_p = w_p * i * w_p⁻¹!
      have heq_conj : (atkinLehnerGL2 p)⁻¹ * i * atkinLehnerGL2 p =
          atkinLehnerGL2 p * i * (atkinLehnerGL2 p)⁻¹ := by
        have hcent : ∀ x : GL2Qp p,
            diagGL2 p (padicPrimeUnit p) (padicPrimeUnit p) * x =
              x * diagGL2 p (padicPrimeUnit p) (padicPrimeUnit p) := by
          intro x; apply Units.ext; ext r s
          fin_cases r <;> fin_cases s <;>
            simp [diagGL2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
        have hcomm : (atkinLehnerGL2 p * atkinLehnerGL2 p) * i =
            i * (atkinLehnerGL2 p * atkinLehnerGL2 p) := by
          rw [hwp2]; exact hcent i
        calc (atkinLehnerGL2 p)⁻¹ * i * atkinLehnerGL2 p
            = (atkinLehnerGL2 p)⁻¹ * (i * (atkinLehnerGL2 p * atkinLehnerGL2 p)) *
                (atkinLehnerGL2 p)⁻¹ := by group
          _ = (atkinLehnerGL2 p)⁻¹ * ((atkinLehnerGL2 p * atkinLehnerGL2 p) * i) *
                (atkinLehnerGL2 p)⁻¹ := by rw [← hcomm]
          _ = atkinLehnerGL2 p * i * (atkinLehnerGL2 p)⁻¹ := by group
      rw [heq_conj]
      exact hconj
    rw [hrew, rightAction_mul, iwahoriVec1_mem_fixedI p h₁ h₂ _ hconj']
  have hval1 : (rightAction p _ _ (atkinLehnerGL2 p) φ₁).1 1 = 0 := by
    rw [rightAction_apply, one_mul, atkinLehnerGL2_eq_diag_mul_weyl]
    have h := iwahoriVec1_apply_BwI p h₁ h₂
      ⟨diagGL2 p 1 (padicPrimeUnit p), diagGL2_mem_Borel p _ _⟩ 1
    simpa using h
  have hvalw : (rightAction p _ _ (atkinLehnerGL2 p) φ₁).1 (weylGL2 p) = (χ.evalP : ℂ) := by
    rw [rightAction_apply, weylGL2_mul_atkinLehnerGL2]
    have h := iwahoriVec1_apply_BI p h₁ h₂
      ⟨diagGL2 p (padicPrimeUnit p) 1, diagGL2_mem_Borel p _ _⟩ 1
    simp only [OneMemClass.coe_one, mul_one] at h
    rw [h, borelChar_steinbergAmbient]
    have hdet : Matrix.GeneralLinearGroup.det (diagGL2 p (padicPrimeUnit p) 1) = padicPrimeUnit p := by
      ext; simp [diagGL2, Matrix.det_fin_two]
    rw [hdet]; rfl
  have hlin : rightAction p _ _ (atkinLehnerGL2 p) φ₁ = (χ.evalP : ℂ) • φw := by
    have h := eq_lincomb_iwahoriVec_of_mem_fixedI p h₁ h₂ hwp_I
    rw [hval1, hvalw, zero_smul, zero_add] at h
    exact h
  have hdet_eq_sph : detCharVec p χ = sphericalVec p h₁ h₂ := by
    ext g
    obtain ⟨b, k, rfl⟩ := iwasawa_decomp p g
    rw [detCharVec_apply, map_mul, map_mul, hχ (Matrix.GeneralLinearGroup.det k.1) k.2.2,
      mul_one, sphericalVec_apply_iwasawa, borelChar_steinbergAmbient]
  have hq_sum : steinbergMk p χ φw = -steinbergMk p χ φ₁ := by
    rw [eq_neg_iff_add_eq_zero, ← map_add]
    change Submodule.Quotient.mk (φw + φ₁) = (0 : SmoothSteinberg p χ)
    rw [Submodule.Quotient.mk_eq_zero, mem_oneDimSubrep_iff]
    refine ⟨1, ?_⟩
    rw [one_smul, hdet_eq_sph]
    simp [φw, φ₁, iwahoriVecW]
  rw [steinbergIwahoriGen, steinbergAction_mk, hlin, map_smul, hq_sum, smul_neg, neg_smul]

/-! ### Concrete Iwahori `U_p` Operator (`I diag(p, 1) I = ⨆_{j=0}^{p-1} !![p, j; 0, 1] · I`) & Eigenvalue -/

/-- Exact `p`-coset decomposition of the Iwahori double coset `I · diag(p, 1) · I`:
for every `i ∈ I` and `j : Fin p`, `i * !![p, j; 0, 1]` lies in `!![p, j'; 0, 1] · I` for a
bijective permutation `j' = σ_i(j)` of `Fin p`! -/
theorem iwahori_mul_heckeRepUpper_perm (i : Iwahori p) :
    ∃ σ : Equiv.Perm (Fin p), ∀ j : Fin p,
      ∃ i' : Iwahori p, i.1 * heckeRepUpper p j = heckeRepUpper p (σ j) * i'.1 := by
  have hp_ne : (p : ℚ_[p]) ≠ 0 := prime_ne_zero_padic p
  have hp_pos : (0 : ℝ) < (p : ℝ) := prime_pos_R p
  have hpinv_norm : ‖(p : ℚ_[p])⁻¹‖ = (p : ℝ) := by rw [norm_inv, Padic.norm_p, inv_inv]
  have hex : ∀ j : Fin p, ∃ j' : Fin p, ∃ i' : Iwahori p,
      i.1 * heckeRepUpper p j = heckeRepUpper p j' * i'.1 := by
    intro j
    have ⟨ha1, hd1⟩ := iwahori_diag_norm_eq_one p i.2
    have hd_ne : i.1.1 1 1 ≠ 0 := by intro h0; rw [h0, norm_zero] at hd1; norm_num at hd1
    have hnum_le : ‖(i.1.1 0 0 * (j.val : ℚ_[p]) + i.1.1 0 1) * (i.1.1 1 1)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, hd1, inv_one, mul_one]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ (i.2.1.1 0 1))
      rw [norm_mul, ha1, one_mul]
      simpa using Padic.norm_int_le_one (p := p) (j.val : ℤ)
    obtain ⟨j', hj'⟩ := exists_fin_sub_norm_le_inv_p p hnum_le
    refine ⟨j', ⟨(heckeRepUpper p j')⁻¹ * (i.1 * heckeRepUpper p j), ?_⟩, by group⟩
    have hprod_le : ‖(i.1.1 0 0 * (j.val : ℚ_[p]) + i.1.1 0 1) - (j'.val : ℚ_[p]) * i.1.1 1 1‖ ≤
        (p : ℝ)⁻¹ := by
      have h1 : (i.1.1 0 0 * (j.val : ℚ_[p]) + i.1.1 0 1) - (j'.val : ℚ_[p]) * i.1.1 1 1 =
          ((i.1.1 0 0 * (j.val : ℚ_[p]) + i.1.1 0 1) * (i.1.1 1 1)⁻¹ - (j'.val : ℚ_[p])) * i.1.1 1 1 := by
        field_simp [hd_ne]
      rw [h1, norm_mul, hd1, mul_one]; exact hj'
    have hc_le : ‖i.1.1 1 0‖ ≤ (p : ℝ)⁻¹ := norm_le_inv_p_of_lt_one p i.2.2
    have hM_val : (((heckeRepUpper p j')⁻¹ * (i.1 * heckeRepUpper p j) : GL2Qp p).1) =
        !![i.1.1 0 0 - (j'.val : ℚ_[p]) * i.1.1 1 0,
           (p : ℚ_[p])⁻¹ * ((i.1.1 0 0 * (j.val : ℚ_[p]) + i.1.1 0 1) -
             (j'.val : ℚ_[p]) * (i.1.1 1 0 * (j.val : ℚ_[p]) + i.1.1 1 1));
           (p : ℚ_[p]) * i.1.1 1 0,
           i.1.1 1 0 * (j.val : ℚ_[p]) + i.1.1 1 1] := by
      ext r s
      change (((heckeRepUpper p j')⁻¹ : GL2Qp p).1 * (i.1.1 * (heckeRepUpper p j).1)) r s = _
      rw [gl2_inv_val]
      fin_cases r <;> fin_cases s <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, heckeRepUpper, Matrix.det_fin_two] <;>
        field_simp [hp_ne] <;> ring
    have hj_le : ‖(j.val : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (j.val : ℤ)
    have hj'_le : ‖(j'.val : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (j'.val : ℤ)
    refine ⟨⟨fun r s => ?_, ?_⟩, ?_⟩
    · rw [hM_val]
      fin_cases r <;> fin_cases s
      · simp only [Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_fin_one, sub_eq_add_neg]
        refine (Padic.nonarchimedean _ _).trans (max_le (i.2.1.1 0 0) ?_)
        rw [norm_neg, norm_mul]
        calc ‖(j'.val : ℚ_[p])‖ * ‖i.1.1 1 0‖ ≤ 1 * 1 :=
              mul_le_mul hj'_le (i.2.1.1 1 0) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_mul, hpinv_norm]
        have hterm : ‖(i.1.1 0 0 * (j.val : ℚ_[p]) + i.1.1 0 1) -
            (j'.val : ℚ_[p]) * (i.1.1 1 0 * (j.val : ℚ_[p]) + i.1.1 1 1)‖ ≤ (p : ℝ)⁻¹ := by
          have hsplit : (i.1.1 0 0 * (j.val : ℚ_[p]) + i.1.1 0 1) -
              (j'.val : ℚ_[p]) * (i.1.1 1 0 * (j.val : ℚ_[p]) + i.1.1 1 1) =
              ((i.1.1 0 0 * (j.val : ℚ_[p]) + i.1.1 0 1) - (j'.val : ℚ_[p]) * i.1.1 1 1) +
                (-((j'.val : ℚ_[p]) * (i.1.1 1 0 * (j.val : ℚ_[p])))) := by ring
          rw [hsplit]
          refine (Padic.nonarchimedean _ _).trans (max_le hprod_le ?_)
          rw [norm_neg, norm_mul, norm_mul]
          have hcj : ‖i.1.1 1 0‖ * ‖(j.val : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
            calc ‖i.1.1 1 0‖ * ‖(j.val : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ * 1 :=
                  mul_le_mul hc_le hj_le (norm_nonneg _) (inv_nonneg.mpr hp_pos.le)
              _ = (p : ℝ)⁻¹ := mul_one _
          calc ‖(j'.val : ℚ_[p])‖ * (‖i.1.1 1 0‖ * ‖(j.val : ℚ_[p])‖) ≤ 1 * (p : ℝ)⁻¹ :=
                mul_le_mul hj'_le hcj (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
            _ = (p : ℝ)⁻¹ := one_mul _
        calc (p : ℝ) * _ ≤ (p : ℝ) * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hterm hp_pos.le
          _ = 1 := mul_inv_cancel₀ hp_pos.ne'
      · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_mul, Padic.norm_p]
        calc (p : ℝ)⁻¹ * ‖i.1.1 1 0‖ ≤ (p : ℝ)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left (i.2.1.1 1 0) (inv_nonneg.mpr hp_pos.le)
          _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ (prime_one_lt_R p).le
      · simp only [Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        refine (Padic.nonarchimedean _ _).trans (max_le ?_ (i.2.1.1 1 1))
        rw [norm_mul]
        calc ‖i.1.1 1 0‖ * ‖(j.val : ℚ_[p])‖ ≤ 1 * 1 :=
              mul_le_mul (i.2.1.1 1 0) hj_le (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    · change ‖Matrix.det (((heckeRepUpper p j')⁻¹ : GL2Qp p).1 * (i.1.1 * (heckeRepUpper p j).1))‖ = 1
      rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, i.2.1.2, one_mul]
      have hdet_inv : Matrix.det ((heckeRepUpper p j')⁻¹ : GL2Qp p).1 = (p : ℚ_[p])⁻¹ := by
        have hm : Matrix.det ((heckeRepUpper p j')⁻¹ : GL2Qp p).1 * Matrix.det (heckeRepUpper p j').1 = 1 := by
          rw [← Matrix.det_mul]
          change Matrix.det (((heckeRepUpper p j')⁻¹ * heckeRepUpper p j' : GL2Qp p).1) = 1
          rw [inv_mul_cancel]; simp
        simp only [heckeRepUpper, mkGL2_det, mul_one, mul_zero, sub_zero] at hm
        exact eq_inv_of_mul_eq_one_left hm
      rw [hdet_inv]
      simp [heckeRepUpper, hpinv_norm, Padic.norm_p, mul_inv_cancel₀ hp_pos.ne']
    · rw [hM_val]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, norm_mul, Padic.norm_p]
      calc (p : ℝ)⁻¹ * ‖i.1.1 1 0‖ ≤ (p : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (i.2.1.1 1 0) (inv_nonneg.mpr hp_pos.le)
        _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ (prime_one_lt_R p)
  let f : Fin p → Fin p := fun j => Classical.choose (hex j)
  have hf_spec : ∀ j, ∃ i' : Iwahori p, i.1 * heckeRepUpper p j = heckeRepUpper p (f j) * i'.1 :=
    fun j => Classical.choose_spec (hex j)
  have hinj : Function.Injective f := by
    intro j₁ j₂ hfj
    obtain ⟨i₁', hi₁'⟩ := hf_spec j₁
    obtain ⟨i₂', hi₂'⟩ := hf_spec j₂
    by_contra hne
    have hdisj := heckeCosets_pairwiseDisjoint p (show (some j₁ : Option (Fin p)) ≠ some j₂ by
      exact fun h => hne (Option.some.inj h))
    dsimp only at hdisj
    rw [Set.disjoint_left] at hdisj
    have hx : heckeRepUpper p j₁ * i₁'.1⁻¹ = heckeRepUpper p j₂ * i₂'.1⁻¹ := by
      have h1 : i.1 * (heckeRepUpper p j₁ * i₁'.1⁻¹) = heckeRepUpper p (f j₁) := by
        calc i.1 * (heckeRepUpper p j₁ * i₁'.1⁻¹)
            = (i.1 * heckeRepUpper p j₁) * i₁'.1⁻¹ := by group
          _ = (heckeRepUpper p (f j₁) * i₁'.1) * i₁'.1⁻¹ := by rw [hi₁']
          _ = heckeRepUpper p (f j₁) := by group
      have h2 : i.1 * (heckeRepUpper p j₂ * i₂'.1⁻¹) = heckeRepUpper p (f j₂) := by
        calc i.1 * (heckeRepUpper p j₂ * i₂'.1⁻¹)
            = (i.1 * heckeRepUpper p j₂) * i₂'.1⁻¹ := by group
          _ = (heckeRepUpper p (f j₂) * i₂'.1) * i₂'.1⁻¹ := by rw [hi₂']
          _ = heckeRepUpper p (f j₂) := by group
      rw [hfj] at h1
      exact mul_left_cancel (h1.trans h2.symm)
    exact hdisj ⟨i₁'.1⁻¹, (K0 p).inv_mem (Iwahori_le_K0 p i₁'.2), rfl⟩
      ⟨i₂'.1⁻¹, (K0 p).inv_mem (Iwahori_le_K0 p i₂'.2), hx⟩
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun j => hf_spec j⟩

/-- **Concrete Iwahori `U_p` Operator** on `SmoothInd p χ₁ χ₂`:
`heckeUp p χ₁ χ₂ f = ∑ j : Fin p, rightAction (!![p, j; 0, 1]) f`. -/
def heckeUp (χ₁ χ₂ : LocalChar p) :
    SmoothInd p χ₁ χ₂ →ₗ[ℂ] SmoothInd p χ₁ χ₂ :=
  ∑ j : Fin p, rightAction p χ₁ χ₂ (heckeRepUpper p j)

lemma heckeUp_apply (χ₁ χ₂ : LocalChar p) (f : SmoothInd p χ₁ χ₂) (g : GL2Qp p) :
    (heckeUp p χ₁ χ₂ f).1 g = ∑ j : Fin p, f.1 (g * heckeRepUpper p j) := by
  simp only [heckeUp, LinearMap.coe_sum, Finset.sum_apply, Submodule.coe_sum]
  simp

/-- `heckeUp` preserves `oneDimSubrep p χ` and therefore descends canonically to the
Steinberg quotient `SmoothSteinberg p χ`! -/
def steinbergHeckeUp (χ : LocalChar p) :
    SmoothSteinberg p χ →ₗ[ℂ] SmoothSteinberg p χ :=
  ∑ j : Fin p, steinbergAction p χ (heckeRepUpper p j)

@[simp]
lemma steinbergHeckeUp_mk (χ : LocalChar p) (f : SteinbergAmbient p χ) :
    steinbergHeckeUp p χ (steinbergMk p χ f) = steinbergMk p χ (heckeUp p _ _ f) := by
  simp only [steinbergHeckeUp, heckeUp, LinearMap.sum_apply, map_sum, steinbergAction_mk]

/-- Normalized `U_p` operator `p^{-1/2} · U_p` on `SmoothSteinberg p χ`. -/
def steinbergHeckeUpNorm (χ : LocalChar p) :
    SmoothSteinberg p χ →ₗ[ℂ] SmoothSteinberg p χ :=
  ((((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • steinbergHeckeUp p χ

/-- **EXACT `U_p` EIGENVALUE ON `(SmoothSteinberg p χ)^I`**:
`U_p v = χ(p) • v` for EVERY Iwahori-fixed vector `v ∈ (SmoothSteinberg p χ)^I`! -/
theorem steinbergHeckeUp_eigenvalue {χ : LocalChar p} (hχ : χ.IsUnramified)
    {v : SmoothSteinberg p χ} (hv : v ∈ steinbergFixed p χ (Iwahori p)) :
    steinbergHeckeUp p χ v = (χ.evalP : ℂ) • v := by
  obtain ⟨c, rfl⟩ := eq_smul_steinbergIwahoriGen p hχ hv
  rw [map_smul, smul_comm]
  congr 1
  set h₁ : (χ * LocalChar.normPowChar p (-(1 / 2))).IsUnramified :=
    LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
  set h₂ : (χ * LocalChar.normPowChar p (1 / 2)).IsUnramified :=
    LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
  set φ₁ := iwahoriVec1 p h₁ h₂
  set φw := iwahoriVecW p h₁ h₂
  have hUp_I : heckeUp p _ _ φ₁ ∈ fixedSubmodule p _ _ (Iwahori p) := by
    rw [mem_fixedSubmodule_iff]
    intro g i hi
    obtain ⟨σ, hσ⟩ := iwahori_mul_heckeRepUpper_perm p ⟨i, hi⟩
    rw [heckeUp_apply, heckeUp_apply]
    calc ∑ j : Fin p, φ₁.1 (g * i * heckeRepUpper p j)
        = ∑ j : Fin p, φ₁.1 (g * heckeRepUpper p (σ j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          obtain ⟨i', hi'⟩ := hσ j
          rw [mul_assoc, hi', ← mul_assoc]
          exact (mem_fixedSubmodule_iff p).mp (iwahoriVec1_mem_fixedI p h₁ h₂) _ i'.1 i'.2
      _ = ∑ j : Fin p, φ₁.1 (g * heckeRepUpper p j) :=
          Equiv.sum_comp σ (fun j => φ₁.1 (g * heckeRepUpper p j))
  have hval1 : (heckeUp p _ _ φ₁).1 1 = (p : ℂ) * (χ.evalP : ℂ) := by
    rw [heckeUp_apply]
    have hterm : ∀ j : Fin p, φ₁.1 (heckeRepUpper p j) = (χ.evalP : ℂ) := by
      intro j
      have h := iwahoriVec1_apply_BI p h₁ h₂ ⟨heckeRepUpper p j, heckeRepUpper_mem_Borel p j⟩ 1
      simp only [OneMemClass.coe_one, mul_one] at h
      rw [h, borelChar_steinbergAmbient]
      have hdet : Matrix.GeneralLinearGroup.det (heckeRepUpper p j) = padicPrimeUnit p := by
        ext; simp [heckeRepUpper]
      rw [hdet]; rfl
    simp [hterm]
  have hvalw : (heckeUp p _ _ φ₁).1 (weylGL2 p) = ((p - 1 : ℕ) : ℂ) * (χ.evalP : ℂ) := by
    rw [heckeUp_apply]
    have hp_ne : (p : ℚ_[p]) ≠ 0 := prime_ne_zero_padic p
    have hterm0 : φ₁.1 (weylGL2 p * heckeRepUpper p ⟨0, hp.out.pos⟩) = 0 := by
      have heq : weylGL2 p * heckeRepUpper p ⟨0, hp.out.pos⟩ =
          diagGL2 p 1 (padicPrimeUnit p) * weylGL2 p * 1 := by
        apply Units.ext; ext r s
        fin_cases r <;> fin_cases s <;>
          simp [weylGL2, heckeRepUpper, diagGL2, Matrix.mul_apply, Fin.sum_univ_two]
      rw [heq]
      exact iwahoriVec1_apply_BwI p h₁ h₂ ⟨diagGL2 p 1 (padicPrimeUnit p), diagGL2_mem_Borel p _ _⟩ 1
    have hterm_nz : ∀ j : Fin p, j.val ≠ 0 → φ₁.1 (weylGL2 p * heckeRepUpper p j) = (χ.evalP : ℂ) := by
      intro j hj0
      have hj_cop : Nat.Coprime p j.val :=
        hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj0) j.isLt)
      have hj_norm : ‖(j.val : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hj_cop
      have hj_ne : (j.val : ℚ_[p]) ≠ 0 := by intro h0; rw [h0, norm_zero] at hj_norm; norm_num at hj_norm
      let bj : GL2Qp p := mkGL2 p (a := -(p : ℚ_[p]) * (j.val : ℚ_[p])⁻¹) (b := 1)
        (c := 0) (d := (j.val : ℚ_[p])) (by simp [hp_ne, hj_ne])
      let ij : GL2Qp p := mkGL2 p (a := 1) (b := 0)
        (c := (p : ℚ_[p]) * (j.val : ℚ_[p])⁻¹) (d := 1) (by simp)
      have hbj_B : bj ∈ Borel p := rfl
      have hij_I : ij ∈ Iwahori p := by
        have h10_norm : ‖(p : ℚ_[p]) * (j.val : ℚ_[p])⁻¹‖ = (p : ℝ)⁻¹ := by
          rw [norm_mul, Padic.norm_p, norm_inv, hj_norm, inv_one, mul_one]
        have h10_lt : ‖(p : ℚ_[p]) * (j.val : ℚ_[p])⁻¹‖ < 1 := by
          rw [h10_norm]; exact inv_lt_one_of_one_lt₀ (prime_one_lt_R p)
        refine ⟨⟨fun r s => ?_, ?_⟩, ?_⟩
        · fin_cases r <;> fin_cases s <;>
            simp [ij, hj_norm, inv_le_one_of_one_le₀ (prime_one_lt_R p).le]
        · simp [ij]
        · simpa [ij] using h10_lt
      have hfac : weylGL2 p * heckeRepUpper p j = bj * ij := by
        apply Units.ext; ext r s
        change ((weylGL2 p).1 * (heckeRepUpper p j).1) r s = (bj.1 * ij.1) r s
        fin_cases r <;> fin_cases s <;>
          simp [weylGL2, heckeRepUpper, bj, ij, Matrix.mul_apply, Fin.sum_univ_two]
        field_simp [hj_ne]
      rw [hfac, iwahoriVec1_apply_BI p h₁ h₂ ⟨bj, hbj_B⟩ ⟨ij, hij_I⟩, borelChar_steinbergAmbient]
      have hdet : Matrix.GeneralLinearGroup.det bj = (-1 : ℚ_[p]ˣ) * padicPrimeUnit p := by
        ext
        change Matrix.det bj.1 = (-1 : ℚ_[p]) * (p : ℚ_[p])
        simp only [bj, mkGL2_det, mul_zero, sub_zero]
        field_simp [hj_ne]
      rw [hdet, map_mul, hχ (-1) (by simp), one_mul]; rfl
    have hsplit_sum : ∑ j : Fin p, φ₁.1 (weylGL2 p * heckeRepUpper p j) =
        φ₁.1 (weylGL2 p * heckeRepUpper p ⟨0, hp.out.pos⟩) +
          ∑ j ∈ Finset.univ.erase ⟨0, hp.out.pos⟩, φ₁.1 (weylGL2 p * heckeRepUpper p j) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    rw [hsplit_sum, hterm0, zero_add]
    have hcongr : ∑ j ∈ Finset.univ.erase (⟨0, hp.out.pos⟩ : Fin p),
        φ₁.1 (weylGL2 p * heckeRepUpper p j) =
        ∑ _j ∈ Finset.univ.erase (⟨0, hp.out.pos⟩ : Fin p), (χ.evalP : ℂ) := by
      refine Finset.sum_congr rfl fun j hj => hterm_nz j ?_
      intro h0
      exact (Finset.mem_erase.mp hj).1 (Fin.ext h0)
    rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hlin : heckeUp p _ _ φ₁ =
      ((p : ℂ) * (χ.evalP : ℂ)) • φ₁ + (((p - 1 : ℕ) : ℂ) * (χ.evalP : ℂ)) • φw := by
    have h := eq_lincomb_iwahoriVec_of_mem_fixedI p h₁ h₂ hUp_I
    rw [hval1, hvalw] at h
    exact h
  have hdet_eq_sph : detCharVec p χ = sphericalVec p h₁ h₂ := by
    ext g
    obtain ⟨b, k, rfl⟩ := iwasawa_decomp p g
    rw [detCharVec_apply, map_mul, map_mul, hχ (Matrix.GeneralLinearGroup.det k.1) k.2.2,
      mul_one, sphericalVec_apply_iwasawa, borelChar_steinbergAmbient]
  have hq_sum : steinbergMk p χ φw = -steinbergMk p χ φ₁ := by
    rw [eq_neg_iff_add_eq_zero, ← map_add]
    change Submodule.Quotient.mk (φw + φ₁) = (0 : SmoothSteinberg p χ)
    rw [Submodule.Quotient.mk_eq_zero, mem_oneDimSubrep_iff]
    refine ⟨1, ?_⟩
    rw [one_smul, hdet_eq_sph]
    simp [φw, φ₁, iwahoriVecW]
  rw [steinbergIwahoriGen, steinbergHeckeUp_mk, hlin, map_add, map_smul, map_smul, hq_sum,
    smul_neg, ← sub_eq_add_neg, ← sub_smul]
  congr 1
  have hp1 : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by
    rw [Nat.cast_sub hp.out.pos, Nat.cast_one]
  rw [hp1]; ring

/-- **EXACT NORMALIZED `U_p` EIGENVALUE & STEINBERG LOCAL `L`-FACTOR MATCH**:
for every unramified `χ`, `(p^{-1/2} U_p) v = (χ(p) p^{-1/2}) • v` on `(SmoothSteinberg p χ)^I`,
whose eigenvalue `λ_{U_p} = χ(p) p^{-1/2}` gives the EXACT local `L`-factor
`(1 - λ_{U_p} T)⁻¹ = (GL2LocalRep.steinberg χ).localLFactor T` of `Stage11LocalLanglandsGL2`! -/
theorem steinbergHeckeUpNorm_eigenvalue_and_LFactor {χ : LocalChar p} (hχ : χ.IsUnramified)
    {v : SmoothSteinberg p χ} (hv : v ∈ steinbergFixed p χ (Iwahori p)) (T : ℂ) :
    steinbergHeckeUpNorm p χ v =
      ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • v ∧
    (GL2LocalRep.steinberg χ).localLFactor T =
      (1 - ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * T)⁻¹ := by
  constructor
  · change (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • steinbergHeckeUp p χ v = _
    rw [steinbergHeckeUp_eigenvalue p hχ hv, smul_smul, mul_comm]
  · exact GL2LocalRep.localLFactor_steinberg_unram hχ T

end SmoothSteinbergRep

/-! ## Section 4: Direct Functorial Grounding into `Stage11LocalLanglandsGL2.satakeGL2OfEigenform`
for All Classical Hecke Eigenforms (`Δ₁₂..Δ₂₂, S₂₄±`) -/

section SatakeEigenformGrounding

open RHDirect.Stage10PeterssonHecke

variable (p : ℕ) [hp : Fact p.Prime]

/-- The genuine smooth `GL (Fin 2) ℚ_[p]`-representation attached to a weight-`k` normalized
Hecke eigenform with eigenvalue `a_p` at prime `p` (unramified Satake characters
`χ₁ = unramChar p α_p`, `χ₂ = unramChar p β_p`). -/
abbrev smoothPrincipalSeriesOfEigenform (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :=
  SmoothInd p
    (LocalChar.unramChar p (satakeRoots a_p p k).1)
    (LocalChar.unramChar p (satakeRoots a_p p k).2)

/-- The canonical normalized `K₀`-spherical vector `f₀` in `smoothPrincipalSeriesOfEigenform a_p p k`. -/
def eigenformSphericalVec (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    smoothPrincipalSeriesOfEigenform a_p p k :=
  sphericalVec p
    (LocalChar.unramChar_isUnramified p (satakeRoots a_p p k).1)
    (LocalChar.unramChar_isUnramified p (satakeRoots a_p p k).2)

/-- Classically twisted principal series `SmoothInd p (χ₁ · |·|^{1/2}) (χ₂ · |·|^{1/2})` on which
the UNNORMALIZED spherical Hecke operator `T_p` has eigenvalue literally `a_p`! -/
abbrev smoothPrincipalSeriesClassical (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :=
  SmoothInd p
    (LocalChar.unramChar p (satakeRoots a_p p k).1 * LocalChar.normPowChar p (1 / 2))
    (LocalChar.unramChar p (satakeRoots a_p p k).2 * LocalChar.normPowChar p (1 / 2))

/-- Canonical normalized `K₀`-spherical vector in `smoothPrincipalSeriesClassical a_p p k`. -/
def eigenformSphericalVecClassical (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    smoothPrincipalSeriesClassical a_p p k :=
  sphericalVec p
    (LocalChar.isUnramified_mul (LocalChar.unramChar_isUnramified p _)
      (LocalChar.normPowChar_isUnramified p _))
    (LocalChar.isUnramified_mul (LocalChar.unramChar_isUnramified p _)
      (LocalChar.normPowChar_isUnramified p _))

/-- **MASTER FUNCTORIAL SATAKE GROUNDING THEOREM**:
for EVERY prime `p`, weight `k`, Hecke eigenvalue `a_p : ℂ`, every `g ∈ GL (Fin 2) ℚ_[p]`, and
every `T : ℂ`:
1. The genuine spherical Hecke operator `T_p` on `smoothPrincipalSeriesOfEigenform a_p p k` acts on
   its unique spherical vector `f₀` with exact eigenvalue `p^{1/2} * Tr(φ(Frob_p)) = p^{1/2} * a_p`,
2. The normalized spherical Hecke operator `T_p^{norm} = p^{-1/2} T_p` acts with exact eigenvalue
   `Tr(φ(Frob_p)) = a_p`,
3. On the classical normalization `smoothPrincipalSeriesClassical a_p p k`, the raw `p + 1`-coset
   Hecke operator `T_p` itself acts with exact eigenvalue `a_p = Tr(φ(Frob_p))`,
4. The exact `Stage11LocalLanglandsGL2` local `L`-factor of `satakeGL2OfEigenform a_p p k` equals
   `(1 - Tr(φ(Frob_p)) T + det(φ(Frob_p)) T²)⁻¹ = (1 - a_p T + p^{k - 1} T²)⁻¹`,
5. The spherical fixed subspace has exact dimension `1`! -/
theorem satakeGL2OfEigenform_smooth_hecke_grounding (a_p : ℂ) (k : ℕ) :
    Module.finrank ℂ (fixedSubmodule p
      (LocalChar.unramChar p (satakeRoots a_p p k).1)
      (LocalChar.unramChar p (satakeRoots a_p p k).2) (K0 p)) = 1 ∧
    (∀ g : GL2Qp p,
      heckeTp p (eigenformSphericalVec a_p p k).1 g =
        (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          Matrix.trace (llcGL2 p (satakeGL2OfEigenform a_p p k)).frobMatrix *
          (eigenformSphericalVec a_p p k).1 g) ∧
    (∀ g : GL2Qp p,
      heckeTpNorm p (eigenformSphericalVec a_p p k).1 g =
        Matrix.trace (llcGL2 p (satakeGL2OfEigenform a_p p k)).frobMatrix *
          (eigenformSphericalVec a_p p k).1 g) ∧
    (∀ g : GL2Qp p,
      heckeTp p (eigenformSphericalVecClassical a_p p k).1 g =
        Matrix.trace (llcGL2 p (satakeGL2OfEigenform a_p p k)).frobMatrix *
          (eigenformSphericalVecClassical a_p p k).1 g) ∧
    (∀ T : ℂ,
      (satakeGL2OfEigenform a_p p k).localLFactor T =
        (1 - Matrix.trace (llcGL2 p (satakeGL2OfEigenform a_p p k)).frobMatrix * T +
          Matrix.det (llcGL2 p (satakeGL2OfEigenform a_p p k)).frobMatrix * T ^ 2)⁻¹) := by
  have ⟨htr, hdet⟩ := satakeGL2OfEigenform_frob_trace_det a_p p k
  refine ⟨finrank_sphericalFixed p (LocalChar.unramChar_isUnramified p _)
    (LocalChar.unramChar_isUnramified p _), ?_, ?_, ?_, ?_⟩
  · intro g
    rw [eigenformSphericalVec, heckeTp_sphericalVec, LocalChar.unramChar_evalP,
      LocalChar.unramChar_evalP, satakeRoots_add, htr]
  · intro g
    rw [eigenformSphericalVec, heckeTpNorm_sphericalVec, LocalChar.unramChar_evalP,
      LocalChar.unramChar_evalP, satakeRoots_add, htr]
  · intro g
    rw [eigenformSphericalVecClassical, heckeTp_sphericalVec]
    simp only [LocalChar.evalP_mul, LocalChar.unramChar_evalP, LocalChar.normPowChar_evalP_val,
      Units.val_mul]
    have hcancel : (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add (prime_pos_R p)]; norm_num
    have hsum : (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        (((satakeRoots a_p p k).1 : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
         ((satakeRoots a_p p k).2 : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = a_p := by
      calc (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            (((satakeRoots a_p p k).1 : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
             ((satakeRoots a_p p k).2 : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          = ((((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
              (((satakeRoots a_p p k).1 : ℂ) + ((satakeRoots a_p p k).2 : ℂ)) := by ring
        _ = a_p := by rw [hcancel, one_mul, satakeRoots_add]
    rw [hsum, htr]
  · intro T
    rw [satakeGL2OfEigenform_localLFactor_T, htr, hdet]

/-- **ALL SEVEN CLASSICAL HECKE EIGENFORMS (`Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂, S₂₄⁺, S₂₄⁻`) AT EVERY
PRIME `p`**: concrete `GL (Fin 2) ℚ_[p]` spherical Hecke operator `T_p` eigenvalue = `a_p(f)`
= `Tr(φ(Frob_p))` matching `Stage11LocalLanglandsGL2.localLFactor`! -/
theorem classical_eigenforms_gl2_smooth_hecke_match (g : GL2Qp p) (T : ℂ) :
    (heckeTp p (eigenformSphericalVecClassical (coeffDelta12Z p : ℂ) p 12).1 g =
      (coeffDelta12Z p : ℂ) * (eigenformSphericalVecClassical (coeffDelta12Z p : ℂ) p 12).1 g ∧
     (satakeGL2OfEigenform (coeffDelta12Z p : ℂ) p 12).localLFactor T =
      (1 - (coeffDelta12Z p : ℂ) * T + (p : ℂ) ^ 11 * T ^ 2)⁻¹) ∧
    (heckeTp p (eigenformSphericalVecClassical (coeffDelta16Z p : ℂ) p 16).1 g =
      (coeffDelta16Z p : ℂ) * (eigenformSphericalVecClassical (coeffDelta16Z p : ℂ) p 16).1 g ∧
     (satakeGL2OfEigenform (coeffDelta16Z p : ℂ) p 16).localLFactor T =
      (1 - (coeffDelta16Z p : ℂ) * T + (p : ℂ) ^ 15 * T ^ 2)⁻¹) ∧
    (heckeTp p (eigenformSphericalVecClassical (coeffDelta18Z p : ℂ) p 18).1 g =
      (coeffDelta18Z p : ℂ) * (eigenformSphericalVecClassical (coeffDelta18Z p : ℂ) p 18).1 g ∧
     (satakeGL2OfEigenform (coeffDelta18Z p : ℂ) p 18).localLFactor T =
      (1 - (coeffDelta18Z p : ℂ) * T + (p : ℂ) ^ 17 * T ^ 2)⁻¹) ∧
    (heckeTp p (eigenformSphericalVecClassical (coeffDelta20Z p : ℂ) p 20).1 g =
      (coeffDelta20Z p : ℂ) * (eigenformSphericalVecClassical (coeffDelta20Z p : ℂ) p 20).1 g ∧
     (satakeGL2OfEigenform (coeffDelta20Z p : ℂ) p 20).localLFactor T =
      (1 - (coeffDelta20Z p : ℂ) * T + (p : ℂ) ^ 19 * T ^ 2)⁻¹) ∧
    (heckeTp p (eigenformSphericalVecClassical (coeffDelta22Z p : ℂ) p 22).1 g =
      (coeffDelta22Z p : ℂ) * (eigenformSphericalVecClassical (coeffDelta22Z p : ℂ) p 22).1 g ∧
     (satakeGL2OfEigenform (coeffDelta22Z p : ℂ) p 22).localLFactor T =
      (1 - (coeffDelta22Z p : ℂ) * T + (p : ℂ) ^ 21 * T ^ 2)⁻¹) ∧
    (heckeTp p (eigenformSphericalVecClassical
        (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenPlus p) p 24).1 g =
      (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenPlus p) *
        (eigenformSphericalVecClassical
          (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenPlus p) p 24).1 g ∧
     (satakeGL2OfEigenform
        (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenPlus p) p 24).localLFactor T =
      (1 - (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenPlus p) * T +
        (p : ℂ) ^ 23 * T ^ 2)⁻¹) ∧
    (heckeTp p (eigenformSphericalVecClassical
        (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenMinus p) p 24).1 g =
      (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenMinus p) *
        (eigenformSphericalVecClassical
          (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenMinus p) p 24).1 g ∧
     (satakeGL2OfEigenform
        (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenMinus p) p 24).localLFactor T =
      (1 - (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenMinus p) * T +
        (p : ℂ) ^ 23 * T ^ 2)⁻¹) := by
  have hgen : ∀ (a_p : ℂ) (k : ℕ),
      heckeTp p (eigenformSphericalVecClassical a_p p k).1 g =
        a_p * (eigenformSphericalVecClassical a_p p k).1 g ∧
      (satakeGL2OfEigenform a_p p k).localLFactor T =
        (1 - a_p * T + (p : ℂ) ^ (k - 1) * T ^ 2)⁻¹ := by
    intro a_p k
    have h := satakeGL2OfEigenform_smooth_hecke_grounding p a_p k
    have ⟨htr, _⟩ := satakeGL2OfEigenform_frob_trace_det a_p p k
    refine ⟨?_, satakeGL2OfEigenform_localLFactor_T a_p p k T⟩
    rw [h.2.2.2.1 g, htr]
  exact ⟨hgen _ 12, hgen _ 16, hgen _ 18, hgen _ 20, hgen _ 22, hgen _ 24, hgen _ 24⟩

end SatakeEigenformGrounding

end Stage11GL2SmoothRep
end RHDirect
