import RHDirect.Interfaces
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# RHDirect.CosetWeights

Compact, direct, 0-`sorry`, 0-`axiom` rebuild of the **Totient / Primitive Coset Weight &
Fourier Clearing Engine** against `RHDirect.Interfaces` and Mathlib `v4.33.1`.

This module replaces the sprawling `toE`/`chr`/`ArithData` wrapper layers in
`PrimitiveCosets/` and `TotientGaloisClasses/` with five clean components:

1. **Weight Positivity & `(3 * o + 1)⁻¹` Clearing Identities** for `Level.wt`,
   `Level.fullWt`, and `CosetFrame.lam`, including the probability-measure normalization
   `∑ γ : φ.A, φ.lam γ = |φ.A0|`.
2. **Finite Abelian Character Orthogonality & Exact Fourier Transform of `CosetFrame.lam`**:
   annihilator duality (`|φ.annihilator| = φ.o`), coset-indicator sums, and exact
   `(1, (3o+1)⁻¹)` Fourier coefficients of `φ.lam`.
3. **Coset-Share Discrepancy & Fourier Clearing Bounds (`CosetFrame.Shares`)**:
   direct proofs of `CosetFrame.tops_sum`, the exact character-isolation lower bound
   `CosetFrame.keptSum_sub_offKeptNorm_le`, its perturbed form `fourier_clear_perturbed_le`,
   and the direct `keptSum → Level.Gm` bridge.
4. **Dirichlet Subgroup Orthogonality & Non-Negative Dirichlet-Series Coefficients**:
   injectivity of `PChar.of`, unconditional subgroup character orthogonality over
   `Ξ : Subgroup (DirichletCharacter ℂ M)`, reality and strict positivity of
   `Level.rampCoeff`, exact `(4o, 3o)/(3o+1)` evaluation on coprime integers for
   `Level.ofSub Ξ` and `Level.cyc ψ`, and the explicit non-negative ramp expansion of `Level.Gm`.
5. **Clean `Level → CharFamily` Bridge & Analytic Bridge Reduction**:
   `Level.toCharFamily` preserving `Gm` and `ZeroFree`, together with the direct
   deduction of `AnalyticBridgeContract` from any `CharFamily` multiplicative-window criterion.
-/

noncomputable section

open Complex Finset
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect

/-! ## 1. Positivity & Exact `(3 * o + 1)⁻¹` Clearing Identities -/

namespace PChar

theorem eq_one_of_chi_eq_one (ψ : PChar) (h : ψ.χ = 1) : ψ = PChar.one := by
  have hN : ψ.N = 1 := by
    have hp : ψ.χ.conductor = ψ.N := ψ.prim
    rw [h, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  cases ψ with
  | mk N χ prim =>
    dsimp only at hN h
    subst hN
    obtain rfl : χ = 1 := h
    rfl

theorem chi_ne_one_of_ne_one {ψ : PChar} (h : ψ ≠ PChar.one) : ψ.χ ≠ 1 :=
  fun h1 => h (ψ.eq_one_of_chi_eq_one h1)

theorem N_eq_one_or_chi_ne_one (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
  by_cases h : ψ.χ = 1
  · left
    have hp : ψ.χ.conductor = ψ.N := ψ.prim
    rw [h, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  · exact Or.inr h

theorem inv_eq_one_iff (ψ : PChar) : ψ.inv = PChar.one ↔ ψ = PChar.one := by
  constructor
  · intro h
    have h' := congrArg PChar.inv h
    rw [PChar.inv_inv] at h'
    exact h'.trans (eq_one_of_chi_eq_one PChar.one.inv (inv_one))
  · rintro rfl
    exact eq_one_of_chi_eq_one PChar.one.inv inv_one

theorem val_one (n : ℕ) : PChar.one.val n = 1 := by
  change (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1
  have h : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [h, map_one]

theorem norm_val_le_one (ψ : PChar) (n : ℕ) : ‖ψ.val n‖ ≤ 1 :=
  ψ.χ.norm_le_one _

theorem neg_one_le_val_re (ψ : PChar) (n : ℕ) : -1 ≤ (ψ.val n).re := by
  have h1 : |(ψ.val n).re| ≤ ‖ψ.val n‖ := Complex.abs_re_le_norm _
  have h2 : ‖ψ.val n‖ ≤ 1 := ψ.norm_val_le_one n
  exact (abs_le.mp (h1.trans h2)).1

theorem val_re_le_one (ψ : PChar) (n : ℕ) : (ψ.val n).re ≤ 1 := by
  have h1 : |(ψ.val n).re| ≤ ‖ψ.val n‖ := Complex.abs_re_le_norm _
  have h2 : ‖ψ.val n‖ ≤ 1 := ψ.norm_val_le_one n
  exact (abs_le.mp (h1.trans h2)).2

theorem val_inv_eq_star (ψ : PChar) (n : ℕ) : ψ.inv.val n = star (ψ.val n) := by
  change ψ.χ⁻¹ (n : ZMod ψ.N) = star (ψ.χ (n : ZMod ψ.N))
  by_cases hu : IsUnit (n : ZMod ψ.N)
  · have hinv : ψ.χ⁻¹ (n : ZMod ψ.N) * ψ.χ (n : ZMod ψ.N) = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu]
    have hnorm : ‖ψ.χ (n : ZMod ψ.N)‖ = 1 := by
      have hp : ψ.χ (n : ZMod ψ.N) ^ Fintype.card (ZMod ψ.N)ˣ = 1 := by
        obtain ⟨u, hu'⟩ := hu
        rw [← hu', ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
      have hq : ‖ψ.χ (n : ZMod ψ.N)‖ ^ Fintype.card (ZMod ψ.N)ˣ = 1 := by
        rw [← norm_pow, hp, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).mp hq
    have hmul : star (ψ.χ (n : ZMod ψ.N)) * ψ.χ (n : ZMod ψ.N) = 1 := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        hnorm, one_pow, Complex.ofReal_one]
    have hne : ψ.χ (n : ZMod ψ.N) ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hnorm
      exact zero_ne_one hnorm
    exact mul_right_cancel₀ hne (hinv.trans hmul.symm)
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, star_zero]

theorem val_inv_im (ψ : PChar) (n : ℕ) : (ψ.inv.val n).im = -(ψ.val n).im := by
  rw [val_inv_eq_star]
  simp

theorem val_inv_re (ψ : PChar) (n : ℕ) : (ψ.inv.val n).re = (ψ.val n).re := by
  rw [val_inv_eq_star]
  simp

private theorem changeLevel_eq_of_mk_eq {M d₁ d₂ : ℕ} [NeZero M] [NeZero d₁] [NeZero d₂]
    (ψ₁ : DirichletCharacter ℂ d₁) (ψ₂ : DirichletCharacter ℂ d₂)
    (hd₁ : d₁ ∣ M) (hd₂ : d₂ ∣ M) (p₁ : ψ₁.IsPrimitive) (p₂ : ψ₂.IsPrimitive)
    (h : PChar.mk d₁ ψ₁ p₁ = PChar.mk d₂ ψ₂ p₂) :
    DirichletCharacter.changeLevel hd₁ ψ₁ = DirichletCharacter.changeLevel hd₂ ψ₂ := by
  cases h
  rfl

theorem of_injective {M : ℕ} [NeZero M] :
    Function.Injective (PChar.of : DirichletCharacter ℂ M → PChar) := by
  intro χ₁ χ₂ h
  have : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  have hchange := changeLevel_eq_of_mk_eq χ₁.primitiveCharacter χ₂.primitiveCharacter
    χ₁.conductor_dvd_level χ₂.conductor_dvd_level
    χ₁.primitiveCharacter_isPrimitive χ₂.primitiveCharacter_isPrimitive h
  rw [χ₁.changeLevel_primitiveCharacter, χ₂.changeLevel_primitiveCharacter] at hchange
  exact hchange

theorem of_val_of_coprime {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {n : ℕ}
    (hn : n.Coprime M) : (PChar.of χ).val n = χ (n : ZMod M) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter
    χ.conductor_dvd_level (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime, χ.changeLevel_primitiveCharacter,
    ZMod.cast_natCast χ.conductor_dvd_level] at h
  exact h.symm

end PChar

namespace Level

variable (L : Level)

theorem three_o_add_one_pos : (0 : ℝ) < 3 * (L.o : ℝ) + 1 := by
  have : (0 : ℝ) < L.o := Nat.cast_pos.mpr L.o_pos
  linarith

theorem four_le_three_o_add_one : (4 : ℝ) ≤ 3 * (L.o : ℝ) + 1 := by
  have : (1 : ℝ) ≤ L.o := by exact_mod_cast L.o_pos
  linarith

theorem wt_pos (ψ : PChar) : 0 < L.wt ψ :=
  inv_pos.mpr L.three_o_add_one_pos

theorem wt_nonneg (ψ : PChar) : 0 ≤ L.wt ψ :=
  (L.wt_pos ψ).le

theorem wt_le_quarter (ψ : PChar) : L.wt ψ ≤ 1 / 4 := by
  rw [Level.wt, one_div]
  exact inv_anti₀ (by norm_num) L.four_le_three_o_add_one

theorem wt_le_one (ψ : PChar) : L.wt ψ ≤ 1 :=
  (L.wt_le_quarter ψ).trans (by norm_num)

/-- Exact `(3 * o + 1)` weight clearing identity for `Level.wt`. -/
theorem wt_clear (ψ : PChar) : (3 * (L.o : ℝ) + 1) * L.wt ψ = 1 :=
  mul_inv_cancel₀ L.three_o_add_one_pos.ne'

theorem wt_inv (ψ : PChar) : L.wt ψ.inv = L.wt ψ := rfl

open Classical in
/-- Unified weight on `L.KEPT`: `1` at `PChar.one` and `(3 * L.o + 1)⁻¹` on `L.Nt`. -/
def fullWt (ψ : PChar) : ℝ := if ψ = PChar.one then 1 else L.wt ψ

theorem fullWt_one : L.fullWt PChar.one = 1 := by
  classical simp [fullWt]

theorem fullWt_of_ne_one {ψ : PChar} (h : ψ ≠ PChar.one) : L.fullWt ψ = L.wt ψ := by
  classical simp [fullWt, h]

theorem fullWt_pos (ψ : PChar) : 0 < L.fullWt ψ := by
  classical
  unfold fullWt
  split_ifs
  · exact one_pos
  · exact L.wt_pos ψ

theorem fullWt_inv (ψ : PChar) : L.fullWt ψ.inv = L.fullWt ψ := by
  classical
  simp only [fullWt, PChar.inv_eq_one_iff, wt_inv]

theorem fullWt_clear {ψ : PChar} (h : ψ ≠ PChar.one) :
    (3 * (L.o : ℝ) + 1) * L.fullWt ψ = 1 := by
  rw [L.fullWt_of_ne_one h, L.wt_clear]

theorem Nt_inv_mem {ψ : PChar} (h : ψ ∈ L.Nt) : ψ.inv ∈ L.Nt := by
  classical
  simp only [Nt, Finset.mem_erase] at h ⊢
  exact ⟨fun h1 => h.1 ((PChar.inv_eq_one_iff ψ).mp h1), L.inv_mem ψ h.2⟩

theorem card_Nt_add_one : L.Nt.card + 1 = L.KEPT.card := by
  classical
  exact Finset.card_erase_add_one L.one_mem

end Level

namespace CosetFrame

variable (φ : CosetFrame)

theorem three_o_add_one_pos : (0 : ℝ) < 3 * (φ.o : ℝ) + 1 := by
  have : (0 : ℝ) < φ.o := Nat.cast_pos.mpr φ.o_pos
  linarith

theorem four_le_three_o_add_one : (4 : ℝ) ≤ 3 * (φ.o : ℝ) + 1 := by
  have : (1 : ℝ) ≤ φ.o := by exact_mod_cast φ.o_pos
  linarith

theorem lam_mem {γ : φ.A} (hγ : γ ∈ φ.A0) : φ.lam γ = 4 / (3 * (φ.o : ℝ) + 1) := by
  simp [lam, hγ]

theorem lam_not_mem {γ : φ.A} (hγ : γ ∉ φ.A0) : φ.lam γ = 3 / (3 * (φ.o : ℝ) + 1) := by
  simp [lam, hγ]

/-- Exact splitting of `CosetFrame.lam` into uniform background `3/(3o+1)` plus
an `A0`-supported bump `(3o+1)⁻¹`. -/
theorem lam_decomp (γ : φ.A) :
    φ.lam γ = 3 * (3 * (φ.o : ℝ) + 1)⁻¹ + if γ ∈ φ.A0 then (3 * (φ.o : ℝ) + 1)⁻¹ else 0 := by
  have hpos := φ.three_o_add_one_pos
  unfold lam
  split_ifs <;> field_simp [hpos.ne'] <;> ring

theorem lam_pos (γ : φ.A) : 0 < φ.lam γ := by
  have hpos := φ.three_o_add_one_pos
  unfold lam
  split_ifs <;> positivity

theorem lam_le_one (γ : φ.A) : φ.lam γ ≤ 1 := by
  have hpos := φ.three_o_add_one_pos
  have h4 := φ.four_le_three_o_add_one
  unfold lam
  rw [div_le_one hpos]
  split_ifs <;> linarith

/-- Exact `(3 * o + 1)` clearing identity for `CosetFrame.lam`. -/
theorem lam_clear (γ : φ.A) :
    (3 * (φ.o : ℝ) + 1) * φ.lam γ = if γ ∈ φ.A0 then 4 else 3 := by
  unfold lam
  exact mul_div_cancel₀ _ φ.three_o_add_one_pos.ne'

theorem lam_eq_of_sub_mem {γ₁ γ₂ : φ.A} (h : γ₁ - γ₂ ∈ φ.A0) : φ.lam γ₁ = φ.lam γ₂ := by
  have hiff : γ₁ ∈ φ.A0 ↔ γ₂ ∈ φ.A0 := by
    constructor
    · intro h1
      have : γ₂ = γ₁ - (γ₁ - γ₂) := by abel
      rw [this]
      exact φ.A0.sub_mem h1 h
    · intro h2
      have : γ₁ = (γ₁ - γ₂) + γ₂ := by abel
      rw [this]
      exact φ.A0.add_mem h h2
  simp [lam, hiff]

theorem lam_neg (γ : φ.A) : φ.lam (-γ) = φ.lam γ := by
  simp [lam, neg_mem_iff]

theorem card_A0_pos : 0 < Fintype.card φ.A0 :=
  Fintype.card_pos_iff.mpr ⟨⟨0, φ.A0.zero_mem⟩⟩

theorem card_A_pos : 0 < Fintype.card φ.A :=
  Fintype.card_pos_iff.mpr ⟨0⟩

theorem index_A0_eq_o : φ.A0.index = φ.o := by
  have hlag := AddSubgroup.index_mul_card φ.A0
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← φ.index_eq] at hlag
  exact Nat.eq_of_mul_eq_mul_right φ.card_A0_pos hlag

/-- `φ.lam` defines a probability measure on the `φ.o` cosets of `φ.A0` in `φ.A`,
so summing `φ.lam γ` over all `γ ∈ φ.A` equals `|φ.A0|`. -/
theorem sum_lam_eq_card_A0 : ∑ γ : φ.A, φ.lam γ = (Fintype.card φ.A0 : ℝ) := by
  have hpos := φ.three_o_add_one_pos
  have hcard : (Finset.univ.filter fun γ : φ.A => γ ∈ φ.A0).card = Fintype.card φ.A0 :=
    (Fintype.card_subtype (· ∈ φ.A0)).symm
  calc
    ∑ γ : φ.A, φ.lam γ
        = ∑ γ : φ.A, (3 * (3 * (φ.o : ℝ) + 1)⁻¹ +
            if γ ∈ φ.A0 then (3 * (φ.o : ℝ) + 1)⁻¹ else 0) :=
          Finset.sum_congr rfl fun γ _ => φ.lam_decomp γ
    _ = (Fintype.card φ.A : ℝ) * (3 * (3 * (φ.o : ℝ) + 1)⁻¹) +
          (Fintype.card φ.A0 : ℝ) * (3 * (φ.o : ℝ) + 1)⁻¹ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
    _ = (Fintype.card φ.A0 : ℝ) := by
          have hidx : (Fintype.card φ.A : ℝ) = (φ.o : ℝ) * (Fintype.card φ.A0 : ℝ) := by
            exact_mod_cast φ.index_eq.symm
          rw [hidx]
          field_simp [hpos.ne']

end CosetFrame

/-! ## 2. Finite Abelian Character Orthogonality & Exact Fourier Transform of `lam` -/

/-- Every additive character on a finite abelian group takes values on the unit circle. -/
theorem addChar_norm_eq_one {H : Type*} [AddCommGroup H] [Fintype H]
    (θ : AddChar H ℂ) (g : H) : ‖θ g‖ = 1 := by
  have hp : θ g ^ Fintype.card H = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  have hq : ‖θ g‖ ^ Fintype.card H = 1 := by
    rw [← norm_pow, hp, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).mp hq

/-- Summing a character trivial on `A0` over the coset `t + A0` gives `|A0| * θ t`. -/
theorem addChar_sum_coset {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A0 : AddSubgroup H) [DecidablePred (· ∈ A0)]
    (θ : AddChar H ℂ) (h0 : ∀ s ∈ A0, θ s = 1) (t : H) :
    ∑ g : H, (if t - g ∈ A0 then θ g else 0) = (Fintype.card A0 : ℂ) * θ t := by
  have step : ∀ g : H, (if t - g ∈ A0 then θ g else 0) = if t - g ∈ A0 then θ t else 0 := by
    intro g
    split_ifs with hg
    · have e : g = t + -(t - g) := by abel
      rw [e, AddChar.map_add_eq_mul, h0 _ (A0.neg_mem hg), mul_one]
    · rfl
  have eqv : A0 ≃ {g : H // t - g ∈ A0} :=
    { toFun := fun s => ⟨t - s, by simp [s.2]⟩
      invFun := fun g => ⟨t - g, g.2⟩
      left_inv := fun s => by ext; simp
      right_inv := fun g => by ext; simp }
  have hc : (Finset.univ.filter fun g : H => t - g ∈ A0).card = Fintype.card A0 := by
    rw [← Fintype.card_subtype, Fintype.card_congr eqv.symm]
  rw [Finset.sum_congr rfl fun g _ => step g, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, hc]

open Classical in
/-- Subgroup orthogonality for additive characters on a finite abelian group. -/
theorem addChar_sum_subgroup_orthog {H : Type*} [AddCommGroup H] [Fintype H]
    (A0 : AddSubgroup H) [Fintype A0] (θ : AddChar H ℂ) :
    ∑ u : A0, θ (u : H) =
      if ∀ s ∈ A0, θ s = 1 then (Fintype.card A0 : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [Finset.sum_congr rfl fun u _ => h u.1 u.2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  · let φ : AddChar A0 ℂ := θ.compAddMonoidHom A0.subtype
    have hne : φ ≠ 0 := by
      intro h0
      apply h
      intro s hs
      have := DFunLike.congr_fun h0 ⟨s, hs⟩
      simpa [φ] using this
    exact AddChar.sum_eq_zero_iff_ne_zero.mpr hne

private theorem exists_addChar_factor_quotient {G Q M : Type*}
    [AddCommGroup G] [AddCommGroup Q] [CommGroupWithZero M]
    (π : G →+ Q) (hπ : Function.Surjective π) (θ : AddChar G M)
    (hker : ∀ x, π x = 0 → θ x = 1) :
    ∃ χ : AddChar Q M, χ.compAddMonoidHom π = θ := by
  have wd : ∀ x y, π x = π y → θ x = θ y := by
    intro x y hxy
    have h0 : π (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    calc
      θ x = θ (y + (x - y)) := by rw [add_sub_cancel]
      _ = θ y * θ (x - y) := AddChar.map_add_eq_mul θ _ _
      _ = θ y := by rw [hker _ h0, mul_one]
  let s := Function.surjInv hπ
  have hs : ∀ q, π (s q) = q := Function.surjInv_eq hπ
  refine ⟨{ toFun := fun q => θ (s q), map_zero_eq_one' := ?_, map_add_eq_mul' := ?_ }, ?_⟩
  · rw [wd (s 0) 0 (by rw [hs, map_zero]), AddChar.map_zero_eq_one]
  · intro a b
    rw [← AddChar.map_add_eq_mul, wd (s (a + b)) (s a + s b) (by rw [hs, map_add, hs, hs])]
  · ext x
    exact wd _ _ (hs _)

namespace CosetFrame

variable (φ : CosetFrame)

open Classical in
/-- The annihilator `A0⊥ ⊆ AddChar φ.A ℂ` of characters trivial on `φ.A0`. -/
def annihilator : Finset (AddChar φ.A ℂ) :=
  Finset.univ.filter fun θ => ∀ s ∈ φ.A0, θ s = 1

theorem mem_annihilator {θ : AddChar φ.A ℂ} :
    θ ∈ φ.annihilator ↔ ∀ s ∈ φ.A0, θ s = 1 := by
  classical
  simp [annihilator]

theorem zero_mem_annihilator : (0 : AddChar φ.A ℂ) ∈ φ.annihilator := by
  rw [mem_annihilator]
  intro _ _
  exact AddChar.zero_apply _

/-- By Pontryagin duality on `φ.A ⧸ φ.A0`, the annihilator of `φ.A0` has cardinality `φ.o`. -/
theorem card_annihilator : φ.annihilator.card = φ.o := by
  classical
  let π : φ.A →+ φ.A ⧸ φ.A0 := QuotientAddGroup.mk' φ.A0
  have hπ : Function.Surjective π := QuotientAddGroup.mk'_surjective φ.A0
  have hinj : Function.Injective (fun χ : AddChar (φ.A ⧸ φ.A0) ℂ => χ.compAddMonoidHom π) := by
    intro χ₁ χ₂ h
    ext q
    obtain ⟨x, rfl⟩ := hπ q
    exact DFunLike.congr_fun h x
  have himg : φ.annihilator =
      Finset.univ.image (fun χ : AddChar (φ.A ⧸ φ.A0) ℂ => χ.compAddMonoidHom π) := by
    ext θ
    simp only [annihilator, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine exists_addChar_factor_quotient π hπ θ fun x hx => ?_
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hx
      exact h x hx
    · rintro ⟨χ, rfl⟩ s hs
      show χ (π s) = 1
      have : π s = 0 := (QuotientAddGroup.eq_zero_iff s).mpr hs
      rw [this, AddChar.map_zero_eq_one]
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, AddChar.card_eq,
    ← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, φ.index_A0_eq_o]

/-- Exact finite-abelian Fourier transform of `φ.lam` on the annihilator `φ.annihilator`:
it isolates the trivial character with weight `1` and every nontrivial character with
exact uniform weight `(3 * φ.o + 1)⁻¹`. -/
theorem fourier_lam (θ : AddChar φ.A ℂ) (h0 : ∀ s ∈ φ.A0, θ s = 1) :
    ∑ γ : φ.A, θ γ * (φ.lam γ : ℂ) =
      (Fintype.card φ.A0 : ℂ) *
        if θ = 0 then (1 : ℂ) else ((3 * (φ.o : ℝ) + 1)⁻¹ : ℂ) := by
  classical
  by_cases hθ : θ = 0
  · subst hθ
    simp only [AddChar.zero_apply, one_mul, ↓reduceIte, mul_one]
    rw [← Complex.ofReal_sum, φ.sum_lam_eq_card_A0]
    simp
  · rw [if_neg hθ]
    have hsum0 : ∑ γ : φ.A, θ γ = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hθ
    have hcos : ∑ γ : φ.A, (if γ ∈ φ.A0 then θ γ else 0) = (Fintype.card φ.A0 : ℂ) := by
      have hz := addChar_sum_coset φ.A0 θ h0 0
      simp only [zero_sub, neg_mem_iff, AddChar.map_zero_eq_one, mul_one] at hz
      exact hz
    have hsplit : ∀ γ : φ.A,
        θ γ * (φ.lam γ : ℂ) =
          (3 * ((3 * (φ.o : ℝ) + 1)⁻¹ : ℂ)) * θ γ +
          ((3 * (φ.o : ℝ) + 1)⁻¹ : ℂ) * (if γ ∈ φ.A0 then θ γ else 0) := by
      intro γ
      rw [φ.lam_decomp γ]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl fun γ _ => hsplit γ, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hsum0, hcos]
    ring

/-! ## 3. Coset-Share Discrepancy & Fourier Clearing Bounds (`CosetFrame.Shares`) -/

/-- General finite-abelian character discrepancy bound from coset-share regularity. -/
theorem character_sum_sub_coset_avg (θ : AddChar φ.A ℂ)
    (h0 : ∀ s ∈ φ.A0, θ s = 1) (h1 : θ ≠ 0) (TT : Finset φ.A) (b c η : ℝ)
    (hs : ∀ γ : φ.A,
      |((TT.filter fun t => t - γ ∈ φ.A0).card : ℝ) - (b + if γ ∈ φ.A0 then c else 0)| ≤ η) :
    ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤ (φ.o : ℝ) * η := by
  have hiff : ∀ γ : φ.A, 0 - γ ∈ φ.A0 ↔ γ ∈ φ.A0 := fun γ => by rw [zero_sub, neg_mem_iff]
  have hz := addChar_sum_coset φ.A0 θ h0 0
  simp only [hiff, AddChar.map_zero_eq_one, mul_one] at hz
  have hB : ∑ γ : φ.A, θ γ = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr h1
  have hC : ∑ γ : φ.A, θ γ * (if γ ∈ φ.A0 then (c : ℂ) else 0) =
      (Fintype.card φ.A0 : ℂ) * c := by
    rw [← hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    split_ifs <;> ring
  have hA : ∑ γ : φ.A, θ γ * ((TT.filter fun t => t - γ ∈ φ.A0).card : ℂ) =
      (Fintype.card φ.A0 : ℂ) * ∑ t ∈ TT, θ t := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun t _ => (addChar_sum_coset φ.A0 θ h0 t).symm,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  let e : φ.A → ℝ := fun γ =>
    ((TT.filter fun t => t - γ ∈ φ.A0).card : ℝ) - (b + if γ ∈ φ.A0 then c else 0)
  have key : (Fintype.card φ.A0 : ℂ) * ((∑ t ∈ TT, θ t) - c) =
      ∑ γ : φ.A, θ γ * (e γ : ℂ) := by
    have hsplit : ∀ γ : φ.A, θ γ * (e γ : ℂ) =
        θ γ * ((TT.filter fun t => t - γ ∈ φ.A0).card : ℂ) -
        (b : ℂ) * θ γ - θ γ * (if γ ∈ φ.A0 then (c : ℂ) else 0) := by
      intro γ
      simp only [e]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl fun γ _ => hsplit γ, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, hA, ← Finset.mul_sum, hB, hC]
    ring
  have hbound : ‖∑ γ : φ.A, θ γ * (e γ : ℂ)‖ ≤ (Fintype.card φ.A : ℝ) * η := by
    calc
      ‖∑ γ : φ.A, θ γ * (e γ : ℂ)‖
          ≤ ∑ γ : φ.A, ‖θ γ * (e γ : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _γ : φ.A, η := Finset.sum_le_sum fun γ _ => by
            rw [norm_mul, addChar_norm_eq_one, one_mul, Complex.norm_real, Real.norm_eq_abs]
            exact hs γ
      _ = (Fintype.card φ.A : ℝ) * η := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Fintype.card φ.A0 := Nat.cast_pos.mpr φ.card_A0_pos
  have h3 : (Fintype.card φ.A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤
      (Fintype.card φ.A0 : ℝ) * ((φ.o : ℝ) * η) := by
    calc
      (Fintype.card φ.A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖
          = ‖(Fintype.card φ.A0 : ℂ) * ((∑ t ∈ TT, θ t) - c)‖ := by
              rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ γ : φ.A, θ γ * (e γ : ℂ)‖ := by rw [key]
      _ ≤ (Fintype.card φ.A : ℝ) * η := hbound
      _ = (Fintype.card φ.A0 : ℝ) * ((φ.o : ℝ) * η) := by
            have hidx : (Fintype.card φ.A : ℝ) = (φ.o : ℝ) * (Fintype.card φ.A0 : ℝ) := by
              exact_mod_cast φ.index_eq.symm
            rw [hidx]
            ring
  exact le_of_mul_le_mul_left h3 hn

/-- **Direct `TopsSum` Theorem for `CosetFrame.Shares`**:
coset-share regularity `φ.Shares TT δ` forces every nontrivial character `θ ∈ φ.annihilator`
to sum over `TT` to `(3 * φ.o + 1)⁻¹ * |TT|` up to error `φ.o * δ * |TT|`. -/
theorem tops_sum {TT : Finset φ.A} {δ : ℝ} (hsh : φ.Shares TT δ)
    {θ : AddChar φ.A ℂ} (h0 : ∀ s ∈ φ.A0, θ s = 1) (h1 : θ ≠ 0) :
    ‖(∑ t ∈ TT, θ t) - (((3 * (φ.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤
      (φ.o : ℝ) * δ * (TT.card : ℝ) := by
  have hs : ∀ γ : φ.A,
      |((TT.filter fun t => t - γ ∈ φ.A0).card : ℝ) -
        (3 * (3 * (φ.o : ℝ) + 1)⁻¹ * (TT.card : ℝ) +
          if γ ∈ φ.A0 then (3 * (φ.o : ℝ) + 1)⁻¹ * (TT.card : ℝ) else 0)| ≤
        δ * (TT.card : ℝ) := by
    intro γ
    have hg := hsh γ
    convert hg using 3
    rw [φ.lam_decomp γ]
    split_ifs <;> ring
  have hfin := φ.character_sum_sub_coset_avg θ h0 h1 TT _ _ _ hs
  push_cast at hfin ⊢
  exact le_of_le_of_eq hfin (by ring)

open Classical in
/-- Exact `(1, (3o + 1)⁻¹)` character weight induced by `CosetFrame.lam`. -/
def charWt (θ : AddChar φ.A ℂ) : ℝ :=
  if θ = 0 then 1 else (3 * (φ.o : ℝ) + 1)⁻¹

theorem charWt_zero : φ.charWt 0 = 1 := by
  classical simp [charWt]

theorem charWt_of_ne_zero {θ : AddChar φ.A ℂ} (h : θ ≠ 0) :
    φ.charWt θ = (3 * (φ.o : ℝ) + 1)⁻¹ := by
  classical simp [charWt, h]

theorem charWt_pos (θ : AddChar φ.A ℂ) : 0 < φ.charWt θ := by
  classical
  unfold charWt
  split_ifs
  · exact one_pos
  · exact inv_pos.mpr φ.three_o_add_one_pos

/-- Unified `tops_sum` over all `θ ∈ φ.annihilator` (both `θ = 0` and `θ ≠ 0`). -/
theorem tops_sum_all {TT : Finset φ.A} {δ : ℝ} (hδ : 0 ≤ δ) (hsh : φ.Shares TT δ)
    {θ : AddChar φ.A ℂ} (hθ : θ ∈ φ.annihilator) :
    ‖(∑ t ∈ TT, θ t) - ((φ.charWt θ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤
      (φ.o : ℝ) * δ * (TT.card : ℝ) := by
  by_cases h0 : θ = 0
  · subst h0
    rw [φ.charWt_zero]
    simp only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one,
      Complex.ofReal_one, one_mul, sub_self, norm_zero]
    positivity
  · rw [φ.charWt_of_ne_zero h0]
    exact φ.tops_sum hsh ((φ.mem_annihilator).mp hθ) h0

/-- Weighted sum over a kept character set `Kp` with weights `φ.charWt`. -/
def keptSum (Kp : Finset (AddChar φ.A ℂ)) (G : AddChar φ.A ℂ → ℂ) : ℝ :=
  ∑ θ ∈ Kp, φ.charWt θ * (G θ).re

open Classical in
/-- Total `L¹` error norm over off-kept characters in `φ.annihilator \ Kp`. -/
def offKeptNorm (Kp : Finset (AddChar φ.A ℂ)) (G : AddChar φ.A ℂ → ℂ) : ℝ :=
  ∑ θ ∈ φ.annihilator \ Kp, ‖G θ‖

/-- Uniform bound on off-kept characters (compact replacement for `SigALe`). -/
theorem offKeptNorm_le (Kp : Finset (AddChar φ.A ℂ)) (G : AddChar φ.A ℂ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ θ ∈ φ.annihilator \ Kp, ‖G θ‖ ≤ B) :
    φ.offKeptNorm Kp G ≤ (φ.o : ℝ) * B := by
  classical
  calc
    φ.offKeptNorm Kp G
        ≤ ∑ _θ ∈ φ.annihilator \ Kp, B := Finset.sum_le_sum hb
    _ = ((φ.annihilator \ Kp).card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (φ.annihilator.card : ℝ) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    _ = (φ.o : ℝ) * B := by rw [φ.card_annihilator]

/-- **Core Fourier Clearing & Character-Isolation Lower Bound**:
summing `Re(∑_{θ ∈ A0⊥} θ(t) G(θ))` over a coset-regular set `TT` isolates the positively
weighted sum `φ.keptSum Kp G` up to the off-kept norm and the coset-share discrepancy. -/
theorem keptSum_sub_offKeptNorm_le {TT : Finset φ.A} {δ : ℝ} (hsh : φ.Shares TT δ)
    {Kp : Finset (AddChar φ.A ℂ)} (hKp : Kp ⊆ φ.annihilator) (G : AddChar φ.A ℂ → ℂ) :
    (TT.card : ℝ) *
        (φ.keptSum Kp G - φ.offKeptNorm Kp G -
          (φ.o : ℝ) * δ * ∑ θ ∈ Kp.erase 0, ‖G θ‖) ≤
      ∑ t ∈ TT, (∑ θ ∈ φ.annihilator, θ t * G θ).re := by
  classical
  have hswap :
      ∑ t ∈ TT, (∑ θ ∈ φ.annihilator, θ t * G θ).re =
        ∑ θ ∈ φ.annihilator, ((∑ t ∈ TT, θ t) * G θ).re := by
    simp_rw [Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [Finset.sum_mul, Complex.re_sum]
  rw [hswap]
  have hpart : φ.annihilator = Kp ∪ (φ.annihilator \ Kp) :=
    (Finset.union_sdiff_of_subset hKp).symm
  rw [hpart, Finset.sum_union Finset.disjoint_sdiff]
  have hkept :
      (TT.card : ℝ) * (φ.keptSum Kp G - (φ.o : ℝ) * δ * ∑ θ ∈ Kp.erase 0, ‖G θ‖) ≤
        ∑ θ ∈ Kp, ((∑ t ∈ TT, θ t) * G θ).re := by
    have hterm : ∀ θ ∈ Kp,
        (TT.card : ℝ) *
            (φ.charWt θ * (G θ).re - if θ = 0 then 0 else (φ.o : ℝ) * δ * ‖G θ‖) ≤
          ((∑ t ∈ TT, θ t) * G θ).re := by
      intro θ hθ
      by_cases h0 : θ = 0
      · subst h0
        rw [if_pos rfl, sub_zero, φ.charWt_zero, one_mul]
        simp only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
        have : ((TT.card : ℂ) * G 0).re = (TT.card : ℝ) * (G 0).re := by
          rw [show (TT.card : ℂ) = ((TT.card : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]
        rw [this]
      · rw [if_neg h0, φ.charWt_of_ne_zero h0]
        set c : ℝ := (3 * (φ.o : ℝ) + 1)⁻¹
        have hts := φ.tops_sum hsh ((φ.mem_annihilator).mp (hKp hθ)) h0
        have hdiff :
            (∑ t ∈ TT, θ t) * G θ - (c : ℂ) * (TT.card : ℂ) * G θ =
              ((∑ t ∈ TT, θ t) - (c : ℂ) * (TT.card : ℂ)) * G θ := by ring
        have hnorm :
            ‖(∑ t ∈ TT, θ t) * G θ - (c : ℂ) * (TT.card : ℂ) * G θ‖ ≤
              (φ.o : ℝ) * δ * (TT.card : ℝ) * ‖G θ‖ := by
          rw [hdiff, norm_mul]
          exact mul_le_mul_of_nonneg_right hts (norm_nonneg _)
        have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
        have hmain : ((c : ℂ) * (TT.card : ℂ) * G θ).re = (TT.card : ℝ) * (c * (G θ).re) := by
          have : (c : ℂ) * (TT.card : ℂ) = ((c * (TT.card : ℝ) : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.re_ofReal_mul]
          ring
        rw [Complex.sub_re, hmain] at hre
        linarith
    calc
      (TT.card : ℝ) * (φ.keptSum Kp G - (φ.o : ℝ) * δ * ∑ θ ∈ Kp.erase 0, ‖G θ‖)
          = ∑ θ ∈ Kp, (TT.card : ℝ) *
              (φ.charWt θ * (G θ).re - if θ = 0 then 0 else (φ.o : ℝ) * δ * ‖G θ‖) := by
            unfold keptSum
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
            congr 1
            have hite :
                ∑ θ ∈ Kp, (TT.card : ℝ) * (if θ = 0 then (0 : ℝ) else (φ.o : ℝ) * δ * ‖G θ‖) =
                  ∑ θ ∈ Kp.erase 0, (TT.card : ℝ) * ((φ.o : ℝ) * δ * ‖G θ‖) := by
              have hstep : ∀ θ : AddChar φ.A ℂ,
                  (TT.card : ℝ) * (if θ = 0 then (0 : ℝ) else (φ.o : ℝ) * δ * ‖G θ‖) =
                    if θ ≠ 0 then (TT.card : ℝ) * ((φ.o : ℝ) * δ * ‖G θ‖) else 0 := by
                intro θ
                by_cases hθ : θ = 0 <;> simp [hθ]
              rw [Finset.sum_congr rfl fun θ _ => hstep θ, ← Finset.sum_filter]
              refine Finset.sum_congr ?_ fun _ _ => rfl
              ext θ
              simp [and_comm]
            rw [hite, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ θ ∈ Kp, ((∑ t ∈ TT, θ t) * G θ).re := Finset.sum_le_sum hterm
  have hoff :
      -((TT.card : ℝ) * φ.offKeptNorm Kp G) ≤
        ∑ θ ∈ φ.annihilator \ Kp, ((∑ t ∈ TT, θ t) * G θ).re := by
    unfold offKeptNorm
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun θ _ => ?_
    have hts : ‖∑ t ∈ TT, θ t‖ ≤ (TT.card : ℝ) := by
      calc
        ‖∑ t ∈ TT, θ t‖ ≤ ∑ t ∈ TT, ‖θ t‖ := norm_sum_le _ _
        _ = (TT.card : ℝ) := by
            simp only [addChar_norm_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hnorm : ‖(∑ t ∈ TT, θ t) * G θ‖ ≤ (TT.card : ℝ) * ‖G θ‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hts (norm_nonneg _)
    exact (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
  linarith

/-- Perturbed Fourier clearing bound allowing `t`-dependent evaluations `Gt t θ`
close to `G θ` (compact replacement for `ChCore.one_char` + `sum_vv`). -/
theorem fourier_clear_perturbed_le {TT : Finset φ.A} {δ : ℝ} (hsh : φ.Shares TT δ)
    {Kp : Finset (AddChar φ.A ℂ)} (hKp : Kp ⊆ φ.annihilator)
    (G : AddChar φ.A ℂ → ℂ) (Gt : φ.A → AddChar φ.A ℂ → ℂ) (Err : AddChar φ.A ℂ → ℝ)
    (hpert : ∀ t ∈ TT, ∀ θ ∈ φ.annihilator, ‖Gt t θ - G θ‖ ≤ Err θ) :
    (TT.card : ℝ) *
        (φ.keptSum Kp G - φ.offKeptNorm Kp G -
          (φ.o : ℝ) * δ * ∑ θ ∈ Kp.erase 0, ‖G θ‖ -
          ∑ θ ∈ φ.annihilator, Err θ) ≤
      ∑ t ∈ TT, (∑ θ ∈ φ.annihilator, θ t * Gt t θ).re := by
  have hbase := φ.keptSum_sub_offKeptNorm_le hsh hKp G
  have hdiff :
      ∑ t ∈ TT, (∑ θ ∈ φ.annihilator, θ t * G θ).re -
        ∑ t ∈ TT, (∑ θ ∈ φ.annihilator, θ t * Gt t θ).re ≤
      (TT.card : ℝ) * ∑ θ ∈ φ.annihilator, Err θ := by
    rw [← Finset.sum_sub_distrib, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    simp_rw [Complex.re_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun θ hθ => ?_
    have hnorm : ‖θ t * (G θ - Gt t θ)‖ ≤ Err θ := by
      rw [norm_mul, addChar_norm_eq_one, one_mul, norm_sub_rev]
      exact hpert t ht θ hθ
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).2
    have heq : (θ t * G θ).re - (θ t * Gt t θ).re = (θ t * (G θ - Gt t θ)).re := by
      rw [← Complex.sub_re, ← mul_sub]
    rwa [heq]
  linarith

end CosetFrame

/-! ## 4. Dirichlet Subgroup Orthogonality & Non-Negative Dirichlet-Series Coefficients -/

open Classical in
/-- Unconditional subgroup character orthogonality for `Ξ : Subgroup (DirichletCharacter ℂ M)`. -/
theorem dirichlet_subgroup_orthog {M : ℕ} [NeZero M]
    (Ξ : Subgroup (DirichletCharacter ℂ M)) (a : ZMod M) :
    ∑ χ : Ξ, (χ : DirichletCharacter ℂ M) a =
      if ∀ χ ∈ Ξ, χ a = 1 then (Nat.card Ξ : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [Finset.sum_congr rfl fun χ _ => h χ.1 χ.2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  · push Not at h
    obtain ⟨χ₀, hχ₀, hne⟩ := h
    let S : ℂ := ∑ χ : Ξ, (χ : DirichletCharacter ℂ M) a
    have hshift : χ₀ a * S = S := by
      change χ₀ a * ∑ χ : Ξ, (χ : DirichletCharacter ℂ M) a =
        ∑ χ : Ξ, (χ : DirichletCharacter ℂ M) a
      rw [Finset.mul_sum]
      have hterm : ∀ χ : Ξ,
          χ₀ a * (χ : DirichletCharacter ℂ M) a =
            (((⟨χ₀, hχ₀⟩ * χ : Ξ) : DirichletCharacter ℂ M) a) := fun χ => by
        change χ₀ a * χ.1 a = (χ₀ * χ.1) a
        rw [MulChar.mul_apply]
      rw [Finset.sum_congr rfl fun χ _ => hterm χ]
      exact Equiv.sum_comp (Equiv.mulLeft (⟨χ₀, hχ₀⟩ : Ξ))
        (fun χ : Ξ => (χ : DirichletCharacter ℂ M) a)
    have hmul0 : (χ₀ a - 1) * S = 0 := by linear_combination hshift
    exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hne)

namespace Level

variable (L : Level)

/-- The Dirichlet-series coefficient of `L.Gm` at `n : ℕ`:
`1 + (3 * L.o + 1)⁻¹ * ∑_{ψ ∈ L.Nt} Re(ψ(n))`. -/
def rampCoeff (n : ℕ) : ℝ :=
  1 + ∑ ψ ∈ L.Nt, L.wt ψ * (ψ.val n).re

theorem rampCoeff_eq_sum_fullWt (n : ℕ) :
    L.rampCoeff n = ∑ ψ ∈ L.KEPT, L.fullWt ψ * (ψ.val n).re := by
  classical
  rw [← Finset.add_sum_erase _ _ L.one_mem]
  unfold rampCoeff Nt
  congr 1
  · rw [L.fullWt_one, one_mul, PChar.val_one, Complex.one_re]
  · refine Finset.sum_congr rfl fun ψ hψ => ?_
    rw [L.fullWt_of_ne_one (Finset.ne_of_mem_erase hψ)]

/-- Inverse-closure of `L.KEPT` forces the imaginary parts of the character sum to vanish. -/
theorem sum_Nt_im_eq_zero (n : ℕ) : ∑ ψ ∈ L.Nt, (ψ.val n).im = 0 := by
  have hneg : ∑ ψ ∈ L.Nt, (ψ.val n).im = -(∑ ψ ∈ L.Nt, (ψ.val n).im) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij PChar.inv (fun ψ hψ => L.Nt_inv_mem hψ)
      (fun a _ b _ h => by
        have := congrArg PChar.inv h
        simpa [PChar.inv_inv] using this)
      (fun ψ hψ => ⟨ψ.inv, L.Nt_inv_mem hψ, PChar.inv_inv ψ⟩)
      (fun ψ _ => by rw [PChar.val_inv_im, neg_neg])
  linarith

/-- Consequently, the complex `(3 * L.o + 1)⁻¹`-weighted character sum is purely real
and equals `L.rampCoeff n`. -/
theorem rampCoeff_eq_complex (n : ℕ) :
    (L.rampCoeff n : ℂ) = 1 + ∑ ψ ∈ L.Nt, (L.wt ψ : ℂ) * ψ.val n := by
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.add_re, Complex.one_re, Complex.re_sum,
      Complex.re_ofReal_mul, rampCoeff]
  · simp only [Complex.ofReal_im, Complex.add_im, Complex.one_im, zero_add, Complex.im_sum,
      Complex.im_ofReal_mul, Level.wt, ← Finset.mul_sum, L.sum_Nt_im_eq_zero n, mul_zero]

/-- Explicit lower bound on `L.rampCoeff n` from `L.KEPT.card`. -/
theorem rampCoeff_ge_of_card (n : ℕ) :
    (3 * (L.o : ℝ) + 2 - (L.KEPT.card : ℝ)) / (3 * (L.o : ℝ) + 1) ≤ L.rampCoeff n := by
  have hpos := L.three_o_add_one_pos
  have hsum : -(L.Nt.card : ℝ) * (3 * (L.o : ℝ) + 1)⁻¹ ≤
      ∑ ψ ∈ L.Nt, L.wt ψ * (ψ.val n).re := by
    calc
      -(L.Nt.card : ℝ) * (3 * (L.o : ℝ) + 1)⁻¹
          = ∑ _ψ ∈ L.Nt, (3 * (L.o : ℝ) + 1)⁻¹ * (-1) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ ψ ∈ L.Nt, L.wt ψ * (ψ.val n).re :=
            Finset.sum_le_sum fun ψ _ =>
              mul_le_mul_of_nonneg_left (ψ.neg_one_le_val_re n) (L.wt_nonneg ψ)
  have hcard : (L.Nt.card : ℝ) + 1 = (L.KEPT.card : ℝ) := by
    exact_mod_cast L.card_Nt_add_one
  unfold rampCoeff
  have heq : (3 * (L.o : ℝ) + 2 - (L.KEPT.card : ℝ)) / (3 * (L.o : ℝ) + 1) =
      1 - (L.Nt.card : ℝ) * (3 * (L.o : ℝ) + 1)⁻¹ := by
    rw [← hcard]
    field_simp [hpos.ne']
    ring
  rw [heq]
  linarith

/-- Strict positivity of `L.rampCoeff n` whenever `L.KEPT.card ≤ 3 * L.o + 1`. -/
theorem rampCoeff_pos_of_card_le (hcard : L.KEPT.card ≤ 3 * L.o + 1) (n : ℕ) :
    0 < L.rampCoeff n := by
  have hpos := L.three_o_add_one_pos
  have hnum : (0 : ℝ) < 3 * (L.o : ℝ) + 2 - (L.KEPT.card : ℝ) := by
    have : (L.KEPT.card : ℝ) ≤ 3 * (L.o : ℝ) + 1 := by exact_mod_cast hcard
    linarith
  exact lt_of_lt_of_le (div_pos hnum hpos) (L.rampCoeff_ge_of_card n)

/-- When `L.KEPT.card ≤ L.o` (e.g. `Level.ofSub` and `Level.cyc`), every Dirichlet-series
coefficient satisfies `2 / 3 < L.rampCoeff n`. -/
theorem two_thirds_lt_rampCoeff_of_card_le (hcard : L.KEPT.card ≤ L.o) (n : ℕ) :
    (2 : ℝ) / 3 < L.rampCoeff n := by
  have hpos := L.three_o_add_one_pos
  have hc : (L.KEPT.card : ℝ) ≤ (L.o : ℝ) := by exact_mod_cast hcard
  have h1 : (2 : ℝ) / 3 < (3 * (L.o : ℝ) + 2 - (L.KEPT.card : ℝ)) / (3 * (L.o : ℝ) + 1) := by
    rw [div_lt_div_iff₀ (by norm_num) hpos]
    linarith
  exact lt_of_lt_of_le h1 (L.rampCoeff_ge_of_card n)

/-- Exact card equality `(Level.ofSub Ξ).KEPT.card = (Level.ofSub Ξ).o` via injectivity of
`PChar.of`. -/
theorem card_KEPT_ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) :
    (Level.ofSub Ξ).KEPT.card = (Level.ofSub Ξ).o := by
  classical
  unfold Level.ofSub
  dsimp only
  rw [Finset.card_image_of_injective _ PChar.of_injective, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem card_KEPT_cyc (ψ : PChar) : (Level.cyc ψ).KEPT.card = (Level.cyc ψ).o :=
  card_KEPT_ofSub (Subgroup.zpowers ψ.χ)

theorem rampCoeff_ofSub_pos {M : ℕ} [NeZero M]
    (Ξ : Subgroup (DirichletCharacter ℂ M)) (n : ℕ) :
    0 < (Level.ofSub Ξ).rampCoeff n := by
  have h : (2 : ℝ) / 3 < (Level.ofSub Ξ).rampCoeff n :=
    (Level.ofSub Ξ).two_thirds_lt_rampCoeff_of_card_le (card_KEPT_ofSub Ξ).le n
  linarith

theorem rampCoeff_cyc_pos (ψ : PChar) (n : ℕ) : 0 < (Level.cyc ψ).rampCoeff n :=
  rampCoeff_ofSub_pos (Subgroup.zpowers ψ.χ) n

open Classical in
/-- **Exact `(4o, 3o)/(3o + 1)` Coset Evaluation for `Level.ofSub Ξ`**:
on integers coprime to `M`, `rampCoeff` takes the exact dual coset weight of `CosetFrame.lam`,
isolating the kernel `ker(Ξ) = {n | ∀ χ ∈ Ξ, χ(n) = 1}` with weight `4o/(3o+1)` and
non-kernel cosets with weight `3o/(3o+1)`. -/
theorem rampCoeff_ofSub_of_coprime {M : ℕ} [NeZero M]
    (Ξ : Subgroup (DirichletCharacter ℂ M)) {n : ℕ} (hn : n.Coprime M) :
    (Level.ofSub Ξ).rampCoeff n =
      (if ∀ χ ∈ Ξ, χ (n : ZMod M) = 1 then 4 * ((Level.ofSub Ξ).o : ℝ)
       else 3 * ((Level.ofSub Ξ).o : ℝ)) / (3 * ((Level.ofSub Ξ).o : ℝ) + 1) := by
  classical
  set L := Level.ofSub Ξ
  have hpos : (0 : ℝ) < 3 * (L.o : ℝ) + 1 := L.three_o_add_one_pos
  have hsum_all :
      ∑ ψ ∈ L.KEPT, ψ.val n = ∑ χ : Ξ, (χ : DirichletCharacter ℂ M) (n : ZMod M) := by
    change ∑ ψ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ M => χ ∈ Ξ).image PChar.of,
        ψ.val n = ∑ χ : Ξ, (χ : DirichletCharacter ℂ M) (n : ZMod M)
    rw [Finset.sum_image (fun a _ b _ h => PChar.of_injective h)]
    have hval :
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ M => χ ∈ Ξ),
          (PChar.of χ).val n =
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ M => χ ∈ Ξ),
          χ (n : ZMod M) :=
      Finset.sum_congr rfl fun χ _ => PChar.of_val_of_coprime χ hn
    rw [hval]
    exact Finset.sum_subtype (Finset.univ.filter fun χ : DirichletCharacter ℂ M => χ ∈ Ξ)
      (p := (· ∈ Ξ)) (fun χ => by simp) (fun χ => χ (n : ZMod M))
  have hsum_Nt :
      ∑ ψ ∈ L.Nt, ψ.val n =
        (∑ χ : Ξ, (χ : DirichletCharacter ℂ M) (n : ZMod M)) - 1 := by
    have h1 := Finset.add_sum_erase L.KEPT (fun ψ => ψ.val n) L.one_mem
    rw [PChar.val_one] at h1
    exact eq_sub_of_add_eq' (h1.trans hsum_all)
  have hC := L.rampCoeff_eq_complex n
  rw [show ∑ ψ ∈ L.Nt, (L.wt ψ : ℂ) * ψ.val n =
      ((3 * (L.o : ℝ) + 1)⁻¹ : ℂ) * ∑ ψ ∈ L.Nt, ψ.val n by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    unfold Level.wt
    push_cast
    rfl] at hC
  rw [hsum_Nt, dirichlet_subgroup_orthog Ξ (n : ZMod M)] at hC
  have ho : (Nat.card Ξ : ℂ) = (L.o : ℂ) := rfl
  rw [ho] at hC
  have hre := congrArg Complex.re hC
  rw [Complex.ofReal_re] at hre
  rw [hre]
  split_ifs
  · have : (1 + ((3 * (L.o : ℝ) + 1)⁻¹ : ℂ) * ((L.o : ℂ) - 1)).re =
        1 + (3 * (L.o : ℝ) + 1)⁻¹ * ((L.o : ℝ) - 1) := by
      rw [Complex.add_re, Complex.one_re,
        show ((3 * (L.o : ℝ) + 1)⁻¹ : ℂ) = (((3 * (L.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_ofReal_mul]
      simp
    rw [this]
    field_simp [hpos.ne']
    ring
  · have : (1 + ((3 * (L.o : ℝ) + 1)⁻¹ : ℂ) * ((0 : ℂ) - 1)).re =
        1 - (3 * (L.o : ℝ) + 1)⁻¹ := by
      rw [Complex.add_re, Complex.one_re,
        show ((3 * (L.o : ℝ) + 1)⁻¹ : ℂ) = (((3 * (L.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_ofReal_mul]
      simp
      ring
    rw [this]
    field_simp [hpos.ne']
    ring

/-- **Target-Character Isolation for `Level.cyc ψ`**:
on integers coprime to `ψ.N`, `(Level.cyc ψ).rampCoeff n` is `4o/(3o+1)` when `ψ(n) = 1`
and `3o/(3o+1)` when `ψ(n) ≠ 1`. -/
theorem rampCoeff_cyc_of_coprime (ψ : PChar) {n : ℕ} (hn : n.Coprime ψ.N) :
    (Level.cyc ψ).rampCoeff n =
      (if ψ.val n = 1 then 4 * ((Level.cyc ψ).o : ℝ)
       else 3 * ((Level.cyc ψ).o : ℝ)) / (3 * ((Level.cyc ψ).o : ℝ) + 1) := by
  have hiff : (∀ χ ∈ Subgroup.zpowers ψ.χ, χ (n : ZMod ψ.N) = 1) ↔ ψ.val n = 1 := by
    constructor
    · intro h
      exact h ψ.χ (Subgroup.mem_zpowers ψ.χ)
    · intro h χ hχ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hχ
      have hu : IsUnit (n : ZMod ψ.N) := (ZMod.isUnit_iff_coprime n ψ.N).mpr hn
      change (ψ.χ ^ k) (n : ZMod ψ.N) = 1
      have hval : ψ.χ (n : ZMod ψ.N) = 1 := h
      have hpow_nat : ∀ m : ℕ, (ψ.χ ^ m) (n : ZMod ψ.N) = 1 := by
        intro m
        induction m with
        | zero => rw [pow_zero, MulChar.one_apply hu]
        | succ m ih => rw [pow_succ, MulChar.mul_apply, ih, hval, mul_one]
      cases k with
      | ofNat m =>
        rw [Int.ofNat_eq_natCast, zpow_natCast]
        exact hpow_nat m
      | negSucc m =>
        rw [zpow_negSucc]
        have hmul : (ψ.χ ^ (m + 1))⁻¹ (n : ZMod ψ.N) * (ψ.χ ^ (m + 1)) (n : ZMod ψ.N) = 1 := by
          rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu]
        rwa [hpow_nat (m + 1), mul_one] at hmul
  simpa only [Level.cyc, hiff] using rampCoeff_ofSub_of_coprime (Subgroup.zpowers ψ.χ) hn

/-- Explicit Dirichlet-series ramp decomposition of `L.Gm y` displaying `L.rampCoeff n`
as the coefficient of `Λ(n) * max (y / n - 1) 0`. -/
theorem Gm_eq_rampCoeff_sum (y : ℝ) :
    L.Gm y =
      (∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * L.rampCoeff n * max (y / n - 1) 0) -
        y * Real.log y + (1 + Real.eulerMascheroniConstant) * y +
        y * ∑ ψ ∈ L.Nt, L.wt ψ *
          (deriv (DirichletCharacter.LFunction ψ.χ) 1 / DirichletCharacter.LFunction ψ.χ 1).re := by
  classical
  have hGchi_Nt : ∀ ψ ∈ L.Nt,
      (Gchi ψ.χ y).re =
        (∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * (ψ.val n).re * max (y / n - 1) 0) +
          y * (deriv (DirichletCharacter.LFunction ψ.χ) 1 /
            DirichletCharacter.LFunction ψ.χ 1).re := by
    intro ψ hψ
    have hne : ψ.χ ≠ 1 := PChar.chi_ne_one_of_ne_one (Finset.ne_of_mem_erase hψ)
    unfold Gchi
    rw [if_neg hne, Complex.add_re, Complex.re_ofReal_mul]
    congr 1
    unfold ramp
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have : ((Λ n : ℂ) * ψ.val n * ((max (y / n - 1) 0 : ℝ) : ℂ)) =
        (((Λ n * max (y / n - 1) 0 : ℝ) : ℂ) * ψ.val n) := by push_cast; ring
    change ((Λ n : ℂ) * ψ.val n * ((max (y / n - 1) 0 : ℝ) : ℂ)).re = _
    rw [this, Complex.re_ofReal_mul]
    ring
  have hGz_ramp :
      (ramp (fun _ => 1) y).re =
        ∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * max (y / n - 1) 0 := by
    unfold ramp
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_one, show (Λ n : ℂ) * ((max (y / n - 1) 0 : ℝ) : ℂ) =
      ((Λ n * max (y / n - 1) 0 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hsum_Nt :
      ∑ ψ ∈ L.Nt, L.wt ψ * (Gchi ψ.χ y).re =
        (∑ ψ ∈ L.Nt, L.wt ψ *
          ∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * (ψ.val n).re * max (y / n - 1) 0) +
        y * ∑ ψ ∈ L.Nt, L.wt ψ * (deriv (DirichletCharacter.LFunction ψ.χ) 1 /
          DirichletCharacter.LFunction ψ.χ 1).re := by
    rw [Finset.sum_congr rfl fun ψ hψ => by rw [hGchi_Nt ψ hψ, mul_add], Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => by ring
  have hramp :
      (∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * max (y / n - 1) 0) +
        ∑ ψ ∈ L.Nt, L.wt ψ *
          (∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * (ψ.val n).re * max (y / n - 1) 0) =
      ∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * L.rampCoeff n * max (y / n - 1) 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold rampCoeff
    rw [mul_add, add_mul, mul_one]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ψ _ => by ring
  unfold Gm Gz
  rw [hGz_ramp, hsum_Nt]
  linarith [hramp]

/-- Every term in the von Mangoldt ramp sum of `L.Gm` is non-negative whenever
`L.KEPT.card ≤ 3 * L.o + 1` (in particular for every `Level.ofSub` and `Level.cyc`). -/
theorem rampTerm_nonneg_of_card_le (hcard : L.KEPT.card ≤ 3 * L.o + 1) (y : ℝ) (n : ℕ) :
    0 ≤ Λ n * L.rampCoeff n * max (y / n - 1) 0 := by
  have h1 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ L.rampCoeff n := (L.rampCoeff_pos_of_card_le hcard n).le
  have h3 : 0 ≤ max (y / n - 1) 0 := le_max_right _ _
  positivity

/-- The entire von Mangoldt ramp sum of `L.Gm` is non-negative whenever
`L.KEPT.card ≤ 3 * L.o + 1`. -/
theorem rampSum_nonneg_of_card_le (hcard : L.KEPT.card ≤ 3 * L.o + 1) (y : ℝ) :
    0 ≤ ∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * L.rampCoeff n * max (y / n - 1) 0 :=
  Finset.sum_nonneg fun n _ => L.rampTerm_nonneg_of_card_le hcard y n

end Level

/-! ## 5. Direct `CosetFrame → Level.Gm` and `Level → CharFamily` Bridges -/

theorem Gchi_one_re (y : ℝ) : (Gchi PChar.one.χ y).re = Gz y := by
  classical
  have h1 : PChar.one.χ = 1 := rfl
  unfold Gchi Gz
  rw [if_pos h1]
  have hr : ramp (fun n => PChar.one.χ (n : ZMod PChar.one.N)) y = ramp (fun _ => 1) y := by
    unfold ramp
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    have hval : PChar.one.χ (n : ZMod PChar.one.N) = 1 := PChar.val_one n
    rw [hval]
  rw [hr]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]

/-- Direct bridge from `CosetFrame.keptSum` to `Level.Gm` for any character embedding
`ι : PChar → AddChar φ.A ℂ` sending `PChar.one` to `0` (replacing `GmAEq.lean`). -/
theorem CosetFrame.keptSum_eq_level_Gm (φ : CosetFrame) (L : Level)
    (ho : φ.o = L.o) (ι : PChar → AddChar φ.A ℂ)
    (hinj : Set.InjOn ι (L.KEPT : Set PChar)) (h1 : ι PChar.one = 0)
    (G : AddChar φ.A ℂ → ℂ) (y : ℝ)
    (hG : ∀ ψ ∈ L.KEPT, (G (ι ψ)).re = (Gchi ψ.χ y).re) :
    φ.keptSum (L.KEPT.image ι) G = L.Gm y := by
  classical
  unfold CosetFrame.keptSum Level.Gm Level.Nt
  rw [Finset.sum_image hinj, ← Finset.add_sum_erase _ _ L.one_mem]
  congr 1
  · rw [hG PChar.one L.one_mem, h1, φ.charWt_zero, one_mul, Gchi_one_re]
  · refine Finset.sum_congr rfl fun ψ hψ => ?_
    have hne_p : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
    have hmem : ψ ∈ L.KEPT := Finset.mem_of_mem_erase hψ
    have hne : ι ψ ≠ 0 := by
      intro h0
      exact hne_p (hinj hmem L.one_mem (h0.trans h1.symm))
    rw [φ.charWt_of_ne_zero hne, ho, hG ψ hmem]
    rfl

namespace Level

/-- Canonical positively-weighted `CharFamily` associated to a `Level` (replacing `LevelFamily.lean`). -/
def toCharFamily (L : Level) : CharFamily where
  ι := L.KEPT
  N := fun i => i.1.N
  nz := fun i => i.1.ne
  χ := fun i => i.1.χ
  a := fun i => L.fullWt i.1
  a_pos := fun i => L.fullWt_pos i.1
  adm := fun i => i.1.N_eq_one_or_chi_ne_one

theorem toCharFamily_Gm (L : Level) (y : ℝ) : L.toCharFamily.Gm y = L.Gm y := by
  classical
  change ∑ i : L.KEPT, L.fullWt i.1 * (Gchi i.1.χ y).re = L.Gm y
  rw [Finset.sum_coe_sort L.KEPT (fun ψ => L.fullWt ψ * (Gchi ψ.χ y).re),
    ← Finset.add_sum_erase _ _ L.one_mem]
  unfold Level.Gm Level.Nt
  congr 1
  · rw [L.fullWt_one, one_mul, Gchi_one_re]
  · refine Finset.sum_congr rfl fun ψ hψ => ?_
    rw [L.fullWt_of_ne_one (Finset.ne_of_mem_erase hψ)]

theorem toCharFamily_zeroFree_iff (L : Level) (θ : ℝ) :
    L.toCharFamily.ZeroFree θ ↔ L.ZeroFreeAbove θ := by
  simp only [CharFamily.ZeroFree, Level.ZeroFreeAbove, PChar.ZeroFreeAbove, toCharFamily]
  constructor
  · intro h ψ hψ s hs
    exact h ⟨ψ, hψ⟩ s hs
  · intro h i s hs
    exact h i.1 i.2 s hs

theorem toCharFamily_hasRpowWindow_iff (L : Level) (θ δ C : ℝ) :
    HasRpowWindow L.toCharFamily.Gm θ δ C ↔ HasRpowWindow L.Gm θ δ C := by
  simp only [HasRpowWindow, L.toCharFamily_Gm]

/-- `ZeroFreeAll` reduces to `ZeroFreeLevel` on every cyclic character level `Level.cyc ψ`. -/
theorem zeroFreeAll_of_cyc (h : ∀ ψ : PChar, (Level.cyc ψ).ZeroFreeLevel) : ZeroFreeAll :=
  fun ψ => h ψ ψ (Level.mem_cyc ψ)

/-- Direct reduction from `LevelWindowBound L la` to `L.ZeroFreeLevel` given any
`CharFamily` multiplicative-window nonvanishing theorem (such as `zeroFree_of_rpow_window`). -/
theorem zeroFreeLevel_of_windowBound (L : Level) {la : ℝ} (hla : 1 < la)
    (hW : LevelWindowBound L la)
    (hLandau : ∀ (F : CharFamily) {θ δ C : ℝ},
      0 < θ → θ < 1 → 0 < δ → HasRpowWindow F.Gm θ δ C → F.ZeroFree θ) :
    L.ZeroFreeLevel := by
  intro ψ hψ s hs
  set θ : ℝ := min ((1 / 2 + s.re) / 2) (3 / 4)
  have hθ_half : (1 : ℝ) / 2 < θ := lt_min (by linarith) (by norm_num)
  have hθ_pos : 0 < θ := lt_trans (by norm_num) hθ_half
  have hθ_lt1 : θ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθ_s : θ < s.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hF : L.toCharFamily.ZeroFree θ :=
    hLandau L.toCharFamily hθ_pos hθ_lt1 (sub_pos.mpr hla)
      ((L.toCharFamily_hasRpowWindow_iff θ (la - 1) 1).mpr (hW θ hθ_half hθ_lt1))
  exact (L.toCharFamily_zeroFree_iff θ).mp hF ψ hψ s hθ_s

end Level

/-- One-line construction of `AnalyticBridgeContract` from any `CharFamily`
multiplicative-window nonvanishing theorem (`RHDirect.zeroFree_of_rpow_window`). -/
theorem analyticBridgeContract_of_charFamily_window
    (hLandau : ∀ (F : CharFamily) {θ δ C : ℝ},
      0 < θ → θ < 1 → 0 < δ → HasRpowWindow F.Gm θ δ C → F.ZeroFree θ) :
    AnalyticBridgeContract where
  zeroFreeAll_of_windows := fun _la hla hAll =>
    Level.zeroFreeAll_of_cyc fun ψ =>
      (Level.cyc ψ).zeroFreeLevel_of_windowBound hla (hAll ψ) hLandau

end RHDirect

end
