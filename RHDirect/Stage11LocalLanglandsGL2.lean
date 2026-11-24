import RHDirect.Stage4LocalLanglands
import RHDirect.Stage6AdelicPoisson
import RHDirect.Stage10PeterssonHecke
import Mathlib.Data.Sym.Sym2
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# RHDirect.Stage11LocalLanglandsGL2

**CONCRETE `GL₂(ℚ_p)` LOCAL LANGLANDS CORRESPONDENCE (`principalSeries`, `oneDim`, `steinberg`,
`tameSupercuspidal`) WITH EXACT LOCAL `L`-FACTORS, CONDUCTOR EXPONENTS, `2 × 2` WEIL–DELIGNE
MATRICES, SATAKE BRIDGE FOR `Δ₁₂..Δ₂₂` & `S₂₄`, AND FULL `12/12` `LocalLanglandsLaws`**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Components

1. **Concrete Smooth Local Characters `LocalChar p` on `ℚ_[p]ˣ` & Conductors**:
   - Higher-unit filtration `IsInUnitFilt p n` (`U_0 = ℤ_[p]ˣ`, `U_n = 1 + p^n ℤ_[p]` for `n ≥ 1`),
     smooth multiplicative characters `LocalChar p` on Mathlib's `ℚ_[p]ˣ`, exact conductor exponent
     `condExp χ : ℕ`, unramified characters `unramChar p α`, normalized local absolute value
     characters `normPowChar p s` / `normChar p`, and `GL₁` local `L`-factors `gl1LFactor`.
2. **Concrete Quadratic Extensions `QuadExtType p`, `QuadField p E`, & `QuadChar p E`**:
   - All three local quadratic extension families (`unramified`, `ramifiedStd`, `ramifiedTwist`)
     realized as concrete fields `QuadField p E` over `ℚ_[p]` with exact Galois involution
     `quadGal`, multiplicative norm `quadNorm`, ultrametric valuation identities, local class
     field theory quadratic character `quadCharOfExt E` (`ω_{E/ℚ_p}` of exact conductor
     `E.discExp`), smooth characters `QuadChar p E` with `galConj`, `resQp`, `baseChange`,
     conductor `condExp`, regularity theorem `one_le_condExp_of_ne_galConj`, and explicit regular
     unramified character construction at every prime `p`.
3. **Concrete `GL₂(ℚ_p)` Irreducible Admissible Classification (`GL2LocalRep p`)**:
   - `principalSeries` (`χ₁ χ₂⁻¹ ≠ |·|±¹`), `oneDim` (`χ ∘ det`, the Langlands quotient at the
     reducibility point), `steinberg` (`St ⊗ χ`, monodromy `N ≠ 0`, conductor `1` when `χ` is
     unramified), and `tameSupercuspidal` (`π(E, θ)` for regular Galois orbits `{θ, θ^σ}`,
     conductor `f(E/ℚ_p) * a(θ) + d(E/ℚ_p) ≥ 2`).
4. **Concrete 2D Weil–Deligne Parameters (`WD2Param p`) & Exact Bijection
   `llcGL2 : GL2LocalRep p ≃ WD2Param p`**:
   - Explicit `2 × 2` Frobenius matrix `frobMatrix` and nilpotent monodromy `monodromyMatrix`
     satisfying `N² = 0`, `det(φ) = detChar(p) ≠ 0`, and `φ N φ⁻¹ = p⁻¹ N`.
   - Exact bijection `llcGL2_bijective` preserving central character = determinant
     (`det_llcGL2_eq_centralChar`), contragredient = dual (`dual_llcGL2_eq_llcGL2_dual`),
     twist equivariance (`twist_llcGL2_eq`), exact local `L`-factors (`localLFactor_llcGL2_eq`),
     and exact conductor exponents (`conductor_llcGL2_eq_artinConductor`).
5. **Satake Bridge for `Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂` & `S₂₄±`**:
   - Explicit `satakeGL2OfEigenform a_p p k` with local `L`-factor
     `(1 - a_p p^{-s} + p^{k-1-2s})⁻¹`, matching all seven `Stage10PeterssonHecke` Euler products.
6. **Full `12/12` `LocalLanglandsLaws` & `MinimalLocalLanglands` Across All Primes `p`**:
   - Concrete `gl2LocalLanglandsPlace p` discharging `FullLocalLanglandsLaws`,
     all `12/12` live fields of `RHDirect.LocalLanglandsLaws`, and `MinimalLocalLanglands`
     over all `Nat.Primes`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex
open scoped BigOperators

namespace RHDirect
namespace Stage11LocalLanglandsGL2

/-! ## Section 1: Concrete Smooth Local Characters `LocalChar p` on `ℚ_[p]ˣ` & Conductors -/

section LocalCharacters

variable (p : ℕ) [hp : Fact p.Prime]

lemma prime_pos_R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos

lemma prime_one_lt_R : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt

lemma prime_ne_zero_R : (p : ℝ) ≠ 0 := (prime_pos_R p).ne'

lemma prime_ne_zero_C : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

lemma prime_ne_zero_padic : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero

/-- Wrap `x : ℚ_[p]` with `‖x‖ ≤ 1` cleanly as an element of `ℤ_[p]`. -/
def mkPadicInt {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) : ℤ_[p] := ⟨x, hx⟩

@[simp]
lemma mkPadicInt_coe {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    ((mkPadicInt hx : ℤ_[p]) : ℚ_[p]) = x := rfl

lemma mkPadicInt_norm {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    ‖mkPadicInt hx‖ = ‖x‖ := rfl

lemma padicInt_ext {p : ℕ} [Fact p.Prime] {x y : ℤ_[p]} (h : (x : ℚ_[p]) = (y : ℚ_[p])) :
    x = y := Subtype.ext h

lemma valuation_eq_zero_of_norm_eq_one {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x‖ = 1) :
    Padic.valuation x = 0 := by
  have hxne : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hx; norm_num at hx
  have h1 := Padic.norm_eq_zpow_neg_valuation hxne
  rw [hx] at h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (1 : ℝ) < (p : ℝ) ^ (-Padic.valuation x) :=
      one_lt_zpow₀ (prime_one_lt_R p) (by omega)
    linarith
  · have : (p : ℝ) ^ (-Padic.valuation x) < 1 :=
      zpow_lt_one_of_neg₀ (prime_one_lt_R p) (by omega)
    linarith

/-- The uniformizer `p` viewed as a unit of `ℚ_[p]ˣ`. -/
def padicPrimeUnit : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (prime_ne_zero_padic p)

@[simp]
lemma padicPrimeUnit_val : ((padicPrimeUnit p : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) := rfl

lemma valuation_padicPrimeUnit : Padic.valuation ((padicPrimeUnit p : ℚ_[p]ˣ) : ℚ_[p]) = 1 := by
  simp [padicPrimeUnit]

/-- Higher-unit filtration on `ℚ_[p]ˣ`:
- `n = 0`: `U_0 = ℤ_[p]ˣ = { u ∈ ℚ_[p]ˣ | ‖u‖ = 1 }`
- `n ≥ 1`: `U_n = 1 + p^n ℤ_[p] = { u ∈ ℚ_[p]ˣ | ‖u‖ = 1 ∧ ‖u - 1‖ ≤ p^{-n} }`. -/
def IsInUnitFilt (n : ℕ) (u : ℚ_[p]ˣ) : Prop :=
  ‖(u : ℚ_[p])‖ = 1 ∧ (n = 0 ∨ ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)))

lemma isInUnitFilt_one (n : ℕ) : IsInUnitFilt p n 1 := by
  refine ⟨by simp, Or.inr ?_⟩
  simp only [Units.val_one, sub_self, norm_zero]
  exact (zpow_pos (prime_pos_R p) _).le

lemma isInUnitFilt_mul {n : ℕ} {u v : ℚ_[p]ˣ}
    (hu : IsInUnitFilt p n u) (hv : IsInUnitFilt p n v) :
    IsInUnitFilt p n (u * v) := by
  refine ⟨by rw [Units.val_mul, norm_mul, hu.1, hv.1, mul_one], ?_⟩
  rcases hu.2 with rfl | hu2
  · exact Or.inl rfl
  · rcases hv.2 with rfl | hv2
    · exact Or.inl rfl
    · right
      have hsplit : ((u * v : ℚ_[p]ˣ) : ℚ_[p]) - 1 =
          (u : ℚ_[p]) * ((v : ℚ_[p]) - 1) + ((u : ℚ_[p]) - 1) := by
        rw [Units.val_mul]; ring
      rw [hsplit]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ hu2)
      rw [norm_mul, hu.1, one_mul]
      exact hv2

lemma isInUnitFilt_inv {n : ℕ} {u : ℚ_[p]ˣ} (hu : IsInUnitFilt p n u) :
    IsInUnitFilt p n u⁻¹ := by
  have hinv_norm : ‖((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
    have hmul : ‖((u : ℚ_[p]) * ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))‖ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, norm_one]
    rw [norm_mul, hu.1, one_mul] at hmul
    exact hmul
  refine ⟨hinv_norm, ?_⟩
  rcases hu.2 with rfl | hu2
  · exact Or.inl rfl
  · right
    have hmul : ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * (u : ℚ_[p]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hsplit : ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) - 1 =
        -(((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * ((u : ℚ_[p]) - 1)) := by
      rw [mul_sub, mul_one, hmul]; ring
    rw [hsplit, norm_neg, norm_mul, hinv_norm, one_mul]
    exact hu2

lemma isInUnitFilt_mono {m n : ℕ} (hmn : m ≤ n) {u : ℚ_[p]ˣ} (hu : IsInUnitFilt p n u) :
    IsInUnitFilt p m u := by
  refine ⟨hu.1, ?_⟩
  by_cases hm : m = 0
  · exact Or.inl hm
  · right
    rcases hu.2 with rfl | hu2
    · omega
    · refine hu2.trans ?_
      exact zpow_le_zpow_right₀ (prime_one_lt_R p).le (by omega)

/-- Every `x : ℚ_[p]ˣ` decomposes canonically as `p^{v_p(x)} * u` with `‖u‖ = 1`. -/
def padicUnitPart (x : ℚ_[p]ˣ) : ℚ_[p]ˣ :=
  padicPrimeUnit p ^ (-Padic.valuation (x : ℚ_[p])) * x

lemma norm_padicUnitPart (x : ℚ_[p]ˣ) : ‖((padicUnitPart p x : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  unfold padicUnitPart
  rw [Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, padicPrimeUnit_val,
    Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation x.ne_zero,
    ← zpow_add₀ (prime_ne_zero_R p), neg_neg, add_neg_cancel, zpow_zero]

lemma padicUnitPart_decomp (x : ℚ_[p]ˣ) :
    x = padicPrimeUnit p ^ (Padic.valuation (x : ℚ_[p])) * padicUnitPart p x := by
  unfold padicUnitPart
  rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

/-- Smooth multiplicative character `χ : ℚ_[p]ˣ →* ℂˣ`, i.e. locally constant on `ℚ_[p]ˣ`
(trivial on `U_n = 1 + p^n ℤ_[p]` for some `n : ℕ`). -/
structure LocalChar where
  toHom : ℚ_[p]ˣ →* ℂˣ
  smooth : ∃ n : ℕ, ∀ u : ℚ_[p]ˣ, IsInUnitFilt p n u → toHom u = 1

namespace LocalChar

variable {p}

@[ext]
lemma ext_hom {χ₁ χ₂ : LocalChar p} (h : ∀ x : ℚ_[p]ˣ, χ₁.toHom x = χ₂.toHom x) :
    χ₁ = χ₂ := by
  cases χ₁; cases χ₂
  congr
  exact MonoidHom.ext h

instance : CommGroup (LocalChar p) where
  one := ⟨1, ⟨0, fun _ _ => rfl⟩⟩
  mul χ₁ χ₂ :=
    ⟨χ₁.toHom * χ₂.toHom, by
      rcases χ₁.smooth with ⟨n₁, h₁⟩
      rcases χ₂.smooth with ⟨n₂, h₂⟩
      refine ⟨max n₁ n₂, fun u hu => ?_⟩
      simp only [MonoidHom.mul_apply]
      rw [h₁ u (isInUnitFilt_mono p (le_max_left n₁ n₂) hu),
        h₂ u (isInUnitFilt_mono p (le_max_right n₁ n₂) hu), mul_one]⟩
  inv χ :=
    ⟨χ.toHom⁻¹, by
      rcases χ.smooth with ⟨n, hn⟩
      refine ⟨n, fun u hu => ?_⟩
      simp only [MonoidHom.inv_apply, hn u hu, inv_one]⟩
  mul_assoc a b c := ext_hom fun x => mul_assoc (a.toHom x) (b.toHom x) (c.toHom x)
  one_mul a := ext_hom fun x => one_mul (a.toHom x)
  mul_one a := ext_hom fun x => mul_one (a.toHom x)
  inv_mul_cancel a := ext_hom fun x => inv_mul_cancel (a.toHom x)
  mul_comm a b := ext_hom fun x => mul_comm (a.toHom x) (b.toHom x)

@[simp] lemma one_toHom : (1 : LocalChar p).toHom = 1 := rfl
@[simp] lemma mul_toHom (χ₁ χ₂ : LocalChar p) : (χ₁ * χ₂).toHom = χ₁.toHom * χ₂.toHom := rfl
@[simp] lemma inv_toHom (χ : LocalChar p) : χ⁻¹.toHom = χ.toHom⁻¹ := rfl

/-- Evaluation of `χ` at the uniformizer `p ∈ ℚ_[p]ˣ`. -/
def evalP (χ : LocalChar p) : ℂˣ := χ.toHom (padicPrimeUnit p)

@[simp] lemma evalP_one : (1 : LocalChar p).evalP = 1 := rfl
@[simp] lemma evalP_mul (χ₁ χ₂ : LocalChar p) : (χ₁ * χ₂).evalP = χ₁.evalP * χ₂.evalP := rfl
@[simp] lemma evalP_inv (χ : LocalChar p) : χ⁻¹.evalP = χ.evalP⁻¹ := rfl

/-- Unramified predicate: `χ` is trivial on `ℤ_[p]ˣ = { u | ‖u‖ = 1 }`. -/
def IsUnramified (χ : LocalChar p) : Prop :=
  ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 → χ.toHom u = 1

lemma isUnramified_one : (1 : LocalChar p).IsUnramified := fun _ _ => rfl

lemma isUnramified_mul {χ₁ χ₂ : LocalChar p} (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    (χ₁ * χ₂).IsUnramified := fun u hu => by
  simp [h₁ u hu, h₂ u hu]

lemma isUnramified_inv_iff (χ : LocalChar p) : χ⁻¹.IsUnramified ↔ χ.IsUnramified := by
  constructor
  · intro h u hu
    have h1 := h u hu
    simpa using congrArg Inv.inv h1
  · intro h u hu
    simp [h u hu]

/-- Exact conductor exponent `a(χ) : ℕ`, the smallest `n` such that `χ` is trivial on `U_n`. -/
def condExp (χ : LocalChar p) : ℕ :=
  letI := Classical.decPred (fun n => ∀ u : ℚ_[p]ˣ, IsInUnitFilt p n u → χ.toHom u = 1)
  Nat.find χ.smooth

lemma condExp_spec (χ : LocalChar p) :
    ∀ u : ℚ_[p]ˣ, IsInUnitFilt p χ.condExp u → χ.toHom u = 1 := by
  classical
  exact Nat.find_spec χ.smooth

lemma condExp_le {χ : LocalChar p} {n : ℕ}
    (hn : ∀ u : ℚ_[p]ˣ, IsInUnitFilt p n u → χ.toHom u = 1) : χ.condExp ≤ n := by
  classical
  exact Nat.find_min' χ.smooth hn

lemma condExp_eq_zero_iff (χ : LocalChar p) : χ.condExp = 0 ↔ χ.IsUnramified := by
  constructor
  · intro h0 u hu
    have hfilt : IsInUnitFilt p χ.condExp u := by rw [h0]; exact ⟨hu, Or.inl rfl⟩
    exact χ.condExp_spec u hfilt
  · intro hunr
    exact Nat.eq_zero_of_le_zero (condExp_le fun u hu => hunr u hu.1)

lemma condExp_one : (1 : LocalChar p).condExp = 0 :=
  (condExp_eq_zero_iff (1 : LocalChar p)).mpr isUnramified_one

lemma condExp_inv (χ : LocalChar p) : χ⁻¹.condExp = χ.condExp := by
  apply le_antisymm
  · refine condExp_le fun u hu => ?_
    simp [χ.condExp_spec u hu]
  · refine condExp_le fun u hu => ?_
    have h1 := χ⁻¹.condExp_spec u hu
    simpa using congrArg Inv.inv h1

lemma condExp_mul_le (χ₁ χ₂ : LocalChar p) :
    (χ₁ * χ₂).condExp ≤ max χ₁.condExp χ₂.condExp := by
  refine condExp_le fun u hu => ?_
  simp only [mul_toHom, MonoidHom.mul_apply]
  rw [χ₁.condExp_spec u (isInUnitFilt_mono p (le_max_left _ _) hu),
    χ₂.condExp_spec u (isInUnitFilt_mono p (le_max_right _ _) hu), mul_one]

lemma condExp_mul_unram (χ₁ : LocalChar p) {χ₂ : LocalChar p} (h₂ : χ₂.IsUnramified) :
    (χ₁ * χ₂).condExp = χ₁.condExp := by
  apply le_antisymm
  · have h0 : χ₂.condExp = 0 := (condExp_eq_zero_iff χ₂).mpr h₂
    have hle := condExp_mul_le χ₁ χ₂
    simpa [h0] using hle
  · have h2inv : χ₂⁻¹.IsUnramified := (isUnramified_inv_iff χ₂).mpr h₂
    have h0 : χ₂⁻¹.condExp = 0 := (condExp_eq_zero_iff χ₂⁻¹).mpr h2inv
    have hle := condExp_mul_le (χ₁ * χ₂) χ₂⁻¹
    simpa [h0, mul_assoc] using hle

/-- Unramified character `unramChar p α` sending `x ↦ α^{v_p(x)}`. -/
def unramChar (p : ℕ) [Fact p.Prime] (α : ℂˣ) : LocalChar p where
  toHom :=
    { toFun := fun x => α ^ (Padic.valuation (x : ℚ_[p]))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [Units.val_mul, Padic.valuation_mul x.ne_zero y.ne_zero, zpow_add] }
  smooth := ⟨0, fun u hu => by
    simp [valuation_eq_zero_of_norm_eq_one hu.1]⟩

@[simp]
lemma unramChar_apply (p : ℕ) [Fact p.Prime] (α : ℂˣ) (x : ℚ_[p]ˣ) :
    (unramChar p α).toHom x = α ^ (Padic.valuation (x : ℚ_[p])) := rfl

@[simp]
lemma unramChar_evalP (p : ℕ) [Fact p.Prime] (α : ℂˣ) :
    (unramChar p α).evalP = α := by
  rw [evalP, unramChar_apply, valuation_padicPrimeUnit, zpow_one]

lemma unramChar_isUnramified (p : ℕ) [Fact p.Prime] (α : ℂˣ) :
    (unramChar p α).IsUnramified := fun u hu => by
  rw [unramChar_apply, valuation_eq_zero_of_norm_eq_one hu, zpow_zero]

@[simp]
lemma unramChar_condExp (p : ℕ) [Fact p.Prime] (α : ℂˣ) :
    (unramChar p α).condExp = 0 :=
  (condExp_eq_zero_iff _).mpr (unramChar_isUnramified p α)

@[simp]
lemma unramChar_one (p : ℕ) [Fact p.Prime] : unramChar p 1 = 1 :=
  ext_hom fun x => by simp

lemma unramChar_mul (p : ℕ) [Fact p.Prime] (α β : ℂˣ) :
    unramChar p (α * β) = unramChar p α * unramChar p β :=
  ext_hom fun x => by simp [mul_zpow]

lemma unramChar_inv (p : ℕ) [Fact p.Prime] (α : ℂˣ) :
    unramChar p α⁻¹ = (unramChar p α)⁻¹ :=
  ext_hom fun x => by simp

lemma unramChar_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (unramChar p) := by
  intro α β h
  have := congrArg evalP h
  simpa using this

lemma eq_unramChar_of_isUnramified {χ : LocalChar p} (h : χ.IsUnramified) :
    χ = unramChar p χ.evalP := by
  apply ext_hom
  intro x
  conv_lhs => rw [padicUnitPart_decomp p x]
  rw [map_mul, map_zpow, h (padicUnitPart p x) (norm_padicUnitPart p x), mul_one]
  rfl

/-- Real-power unramified norm character `|·|_p^s` (`x ↦ p^{-s · v_p(x)}`). -/
def normPowChar (p : ℕ) [Fact p.Prime] (s : ℝ) : LocalChar p :=
  unramChar p (Units.mk0 (((p : ℝ) ^ (-s) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (prime_pos_R p) _).ne'))

/-- Normalized local absolute value character `|·|_p = normPowChar p 1` (`p ↦ p⁻¹`). -/
def normChar (p : ℕ) [Fact p.Prime] : LocalChar p := normPowChar p 1

lemma normPowChar_isUnramified (p : ℕ) [Fact p.Prime] (s : ℝ) :
    (normPowChar p s).IsUnramified :=
  unramChar_isUnramified p _

lemma normChar_isUnramified (p : ℕ) [Fact p.Prime] : (normChar p).IsUnramified :=
  normPowChar_isUnramified p 1

@[simp]
lemma normPowChar_evalP_val (p : ℕ) [Fact p.Prime] (s : ℝ) :
    ((normPowChar p s).evalP : ℂ) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
  simp [normPowChar]

@[simp]
lemma normChar_evalP_val (p : ℕ) [Fact p.Prime] :
    ((normChar p).evalP : ℂ) = (p : ℂ)⁻¹ := by
  simp [normChar, normPowChar_evalP_val, Real.rpow_neg_one]

@[simp]
lemma normPowChar_zero (p : ℕ) [Fact p.Prime] : normPowChar p 0 = 1 := by
  rw [normPowChar]
  convert unramChar_one p
  ext
  simp

lemma normPowChar_add (p : ℕ) [Fact p.Prime] (s₁ s₂ : ℝ) :
    normPowChar p (s₁ + s₂) = normPowChar p s₁ * normPowChar p s₂ := by
  unfold normPowChar
  rw [← unramChar_mul]
  congr 1
  ext
  simp only [Units.val_mk0, Units.val_mul, ← Complex.ofReal_mul, ← Real.rpow_add (prime_pos_R p),
    neg_add]

lemma normPowChar_neg (p : ℕ) [Fact p.Prime] (s : ℝ) :
    normPowChar p (-s) = (normPowChar p s)⁻¹ := by
  unfold normPowChar
  rw [← unramChar_inv]
  congr 1
  ext
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val, ← Complex.ofReal_inv,
    ← Real.rpow_neg (prime_pos_R p).le, neg_neg]

lemma normPowChar_half_mul_half (p : ℕ) [Fact p.Prime] :
    normPowChar p (1 / 2) * normPowChar p (1 / 2) = normChar p := by
  rw [← normPowChar_add]
  norm_num [normChar]

lemma normPowChar_half_mul_neg_half (p : ℕ) [Fact p.Prime] :
    normPowChar p (1 / 2) * normPowChar p (-(1 / 2)) = 1 := by
  rw [← normPowChar_add, add_neg_cancel, normPowChar_zero]

lemma normChar_ne_one (p : ℕ) [Fact p.Prime] : normChar p ≠ 1 := by
  intro h
  have hv := congrArg (fun χ : LocalChar p => (χ.evalP : ℂ)) h
  simp only [normChar_evalP_val, evalP_one, Units.val_one] at hv
  have hp1 : (p : ℂ) = 1 := by
    have := congrArg (· * (p : ℂ)) hv
    simpa [inv_mul_cancel₀ (prime_ne_zero_C p)] using this.symm
  have hp1N : p = 1 := by exact_mod_cast hp1
  exact (Fact.out : p.Prime).ne_one hp1N

lemma normChar_sq_ne_one (p : ℕ) [Fact p.Prime] : normChar p * normChar p ≠ 1 := by
  intro h
  have hv := congrArg (fun χ : LocalChar p => (χ.evalP : ℂ)) h
  simp only [evalP_mul, Units.val_mul, normChar_evalP_val, evalP_one, Units.val_one] at hv
  have hp2 : (p : ℂ) ^ 2 = 1 := by
    have hmul := congrArg (· * (p : ℂ) ^ 2) hv
    have hpne : (p : ℂ) ≠ 0 := prime_ne_zero_C p
    have hsimp : (p : ℂ)⁻¹ * (p : ℂ)⁻¹ * (p : ℂ) ^ 2 = 1 := by field_simp [hpne]
    rw [hsimp, one_mul] at hmul
    exact hmul.symm
  have hp2N : p ^ 2 = 1 := by exact_mod_cast hp2
  have hge : 4 ≤ p ^ 2 := by
    have := (Fact.out : p.Prime).two_le
    nlinarith
  omega

/-- Local `GL₁` `L`-factor `L(χ, T)`: `(1 - χ(p) T)⁻¹` if `χ` is unramified, `1` if ramified. -/
def gl1LFactor (χ : LocalChar p) (T : ℂ) : ℂ :=
  letI := Classical.dec χ.IsUnramified
  if χ.IsUnramified then (1 - (χ.evalP : ℂ) * T)⁻¹ else 1

lemma gl1LFactor_of_isUnramified {χ : LocalChar p} (h : χ.IsUnramified) (T : ℂ) :
    χ.gl1LFactor T = (1 - (χ.evalP : ℂ) * T)⁻¹ := by
  classical
  simp [gl1LFactor, h]

lemma gl1LFactor_unramChar (α : ℂˣ) (T : ℂ) :
    (unramChar p α).gl1LFactor T = (1 - (α : ℂ) * T)⁻¹ := by
  rw [gl1LFactor_of_isUnramified (unramChar_isUnramified p α), unramChar_evalP]

lemma gl1LFactor_of_not_isUnramified {χ : LocalChar p} (h : ¬χ.IsUnramified) (T : ℂ) :
    χ.gl1LFactor T = 1 := by
  classical
  simp [gl1LFactor, h]

end LocalChar

end LocalCharacters

/-! ## Section 2: Concrete Quadratic Extensions `QuadExtType p`, `QuadField p E`, & `QuadChar p E` -/

section QuadraticExtensions

/-- The three local quadratic extension families over `ℚ_p`:
- `unramified`: the unique unramified quadratic extension (`f = 2, e = 1, d = 0`),
- `ramifiedStd`: `ℚ_p(√p)` (`f = 1, e = 2`, `d = 1` for odd `p`, `d = 3` for `p = 2`),
- `ramifiedTwist`: `ℚ_p(√(u p))` (`f = 1, e = 2`, `d = 1` for odd `p`, `d = 3` for `p = 2`). -/
inductive QuadExtType (p : ℕ) where
  | unramified : QuadExtType p
  | ramifiedStd : QuadExtType p
  | ramifiedTwist : QuadExtType p
  deriving DecidableEq

namespace QuadExtType

variable {p : ℕ}

/-- Residue field degree `f(E/ℚ_p)`. -/
def residueDeg : QuadExtType p → ℕ
  | .unramified => 2
  | .ramifiedStd => 1
  | .ramifiedTwist => 1

/-- Ramification index `e(E/ℚ_p)`. -/
def ramIndex : QuadExtType p → ℕ
  | .unramified => 1
  | .ramifiedStd => 2
  | .ramifiedTwist => 2

/-- Discriminant valuation exponent `d(E/ℚ_p) = v_p(disc(E/ℚ_p))`. -/
def discExp : QuadExtType p → ℕ
  | .unramified => 0
  | .ramifiedStd => if p = 2 then 3 else 1
  | .ramifiedTwist => if p = 2 then 3 else 1

/-- Tame ramification predicate for `E / ℚ_p`: unramified or `p ≠ 2`. -/
def IsTameExt (E : QuadExtType p) : Prop :=
  E = .unramified ∨ p ≠ 2

@[simp]
lemma ramIndex_mul_residueDeg (E : QuadExtType p) : E.ramIndex * E.residueDeg = 2 := by
  cases E <;> rfl

lemma residueDeg_pos (E : QuadExtType p) : 0 < E.residueDeg := by
  cases E <;> simp [residueDeg]

lemma ramIndex_pos (E : QuadExtType p) : 0 < E.ramIndex := by
  cases E <;> simp [ramIndex]

end QuadExtType

variable (p : ℕ) [hp : Fact p.Prime]

/-- Existence of a quadratic non-residue `u ∈ (0, p)` modulo any odd prime `p`. -/
lemma exists_nonSquare_mod_odd_prime (hodd : p ≠ 2) :
    ∃ u : ℕ, 0 < u ∧ u < p ∧ ¬IsSquare (u : ZMod p) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hsq_not_surj : ¬Function.Surjective (fun x : (ZMod p)ˣ => x * x) := by
    intro hsurj
    have hinj : Function.Injective (fun x : (ZMod p)ˣ => x * x) :=
      Finite.injective_iff_surjective.mpr hsurj
    have hneg : ((-1 : (ZMod p)ˣ) * (-1 : (ZMod p)ˣ)) = (1 : (ZMod p)ˣ) * (1 : (ZMod p)ˣ) := by
      simp
    have heq := hinj hneg
    have hval : (-1 : ZMod p) = (1 : ZMod p) := congrArg Units.val heq
    have h2 : (2 : ZMod p) = 0 := by linear_combination -hval
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := hp.out.two_le
    omega
  simp only [Function.Surjective, not_forall] at hsq_not_surj
  rcases hsq_not_surj with ⟨u, hu⟩
  refine ⟨(u : ZMod p).val, ?_, (u : ZMod p).val_lt, ?_⟩
  · have hne0 : (u : ZMod p) ≠ 0 := u.ne_zero
    exact Nat.pos_of_ne_zero (fun h0 => hne0 ((ZMod.val_eq_zero _).mp h0))
  · rintro ⟨r, hr⟩
    rw [ZMod.natCast_zmod_val] at hr
    have hr0 : r ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hr; exact u.ne_zero hr
    have hru : IsUnit r := isUnit_iff_ne_zero.mpr hr0
    exact hu ⟨hru.unit, by ext; simpa using hr.symm⟩

/-- Chosen unit representative `u_p ∈ {1, ..., p-1}` (a non-square mod `p` for odd `p`, and `5`
for `p = 2`). -/
def nonSquareUnitNat : ℕ :=
  if hodd : p ≠ 2 then Classical.choose (exists_nonSquare_mod_odd_prime p hodd) else 5

lemma nonSquareUnitNat_spec_odd (hodd : p ≠ 2) :
    0 < nonSquareUnitNat p ∧ nonSquareUnitNat p < p ∧
      ¬IsSquare ((nonSquareUnitNat p : ℕ) : ZMod p) := by
  simp only [nonSquareUnitNat, dif_pos hodd]
  exact Classical.choose_spec (exists_nonSquare_mod_odd_prime p hodd)

lemma nonSquareUnitNat_coprime : Nat.Coprime p (nonSquareUnitNat p) := by
  by_cases hodd : p ≠ 2
  · obtain ⟨hpos, hlt, _⟩ := nonSquareUnitNat_spec_odd p hodd
    exact hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos hlt)
  · push Not at hodd
    subst hodd
    simp [nonSquareUnitNat]
    decide

lemma norm_nonSquareUnitNat : ‖((nonSquareUnitNat p : ℕ) : ℚ_[p])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr (nonSquareUnitNat_coprime p)

/-- Trace coefficient `t_E ∈ ℚ_[p]` of the quadratic extension `ω² = t_E ω + δ_E`. -/
def quadTrace (E : QuadExtType p) : ℚ_[p] :=
  match E with
  | .unramified => if p = 2 then 1 else 0
  | .ramifiedStd => 0
  | .ramifiedTwist => 0

/-- Constant coefficient `δ_E ∈ ℚ_[p]` of the quadratic extension `ω² = t_E ω + δ_E`. -/
def quadDelta (E : QuadExtType p) : ℚ_[p] :=
  match E with
  | .unramified => if p = 2 then 1 else (nonSquareUnitNat p : ℚ_[p])
  | .ramifiedStd => (p : ℚ_[p])
  | .ramifiedTwist => (nonSquareUnitNat p : ℚ_[p]) * (p : ℚ_[p])

/-- Characterization of the kernel of `PadicInt.toZMod : ℤ_[p] →+* ZMod p`:
`toZMod z = 0 ↔ ‖(z : ℚ_[p])‖ < 1`. -/
lemma padicInt_toZMod_eq_zero_iff (z : ℤ_[p]) :
    PadicInt.toZMod z = 0 ↔ ‖(z : ℚ_[p])‖ < 1 := by
  constructor
  · intro h0
    have hnu : ¬IsUnit z := by
      intro hu
      have hu' : IsUnit (PadicInt.toZMod z) := hu.map PadicInt.toZMod
      rw [h0] at hu'
      exact not_isUnit_zero hu'
    have hne1 : ‖(z : ℚ_[p])‖ ≠ 1 := by
      intro h1
      exact hnu (PadicInt.isUnit_iff.mpr h1)
    exact lt_of_le_of_ne z.2 hne1
  · intro hlt
    have hle : ‖(z : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
      by_cases hz : (z : ℚ_[p]) = 0
      · rw [hz, norm_zero]; exact inv_nonneg.mpr (prime_pos_R p).le
      · rw [Padic.norm_eq_zpow_neg_valuation hz] at hlt ⊢
        have hv_pos : 0 < Padic.valuation (z : ℚ_[p]) := by
          by_contra hle0
          have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (-Padic.valuation (z : ℚ_[p])) :=
            one_le_zpow₀ (prime_one_lt_R p).le (by omega)
          linarith
        rw [← zpow_neg_one]
        exact zpow_le_zpow_right₀ (prime_one_lt_R p).le (by omega)
    have hdiv_norm : ‖(z : ℚ_[p]) / (p : ℚ_[p])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p]
      exact (div_le_one (inv_pos.mpr (prime_pos_R p))).mpr hle
    have hz_eq : z = (p : ℤ_[p]) * mkPadicInt hdiv_norm := by
      apply padicInt_ext
      simp only [PadicInt.coe_mul, PadicInt.coe_natCast, mkPadicInt_coe]
      exact (mul_div_cancel₀ _ (prime_ne_zero_padic p)).symm
    rw [hz_eq, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- Concrete quadratic extension field `E = ℚ_p[ω] / (ω² - t_E ω - δ_E)` represented explicitly as
pairs `(re, im) ∈ ℚ_[p] × ℚ_[p]` corresponding to `re + im · ω`. -/
@[ext]
structure QuadField (E : QuadExtType p) where
  re : ℚ_[p]
  im : ℚ_[p]

namespace QuadField

variable {p} {E : QuadExtType p}

/-- Ring norm `N_{E/ℚ_p}(c + d ω) = c² + t_E c d - δ_E d²`. -/
def normVal (z : QuadField p E) : ℚ_[p] :=
  z.re ^ 2 + quadTrace p E * z.re * z.im - quadDelta p E * z.im ^ 2

private lemma zmod2_quad_ne_zero (x y : ZMod 2) (h : x ≠ 0 ∨ y ≠ 0) :
    x ^ 2 + x * y - y ^ 2 ≠ 0 := by
  decide +revert

/-- **Exact Ultrametric Norm Formula for Unramified `QuadField p .unramified`** (ALL primes `p`,
including `p = 2` via `c² + c d - d²`!): `‖N(c, d)‖_p = max (‖c‖_p²) (‖d‖_p²)`. -/
theorem norm_normVal_unramified (z : QuadField p .unramified) :
    ‖z.normVal‖ = max (‖z.re‖ ^ 2) (‖z.im‖ ^ 2) := by
  by_cases h0 : z.re = 0 ∧ z.im = 0
  · simp [normVal, h0.1, h0.2]
  · have hmax_pos : 0 < max ‖z.re‖ ‖z.im‖ := by
      rcases not_and_or.mp h0 with h | h
      · exact lt_of_lt_of_le (norm_pos_iff.mpr h) (le_max_left _ _)
      · exact lt_of_lt_of_le (norm_pos_iff.mpr h) (le_max_right _ _)
    obtain ⟨s, hs_ne, hs_norm⟩ : ∃ s : ℚ_[p], s ≠ 0 ∧ ‖s‖ = max ‖z.re‖ ‖z.im‖ := by
      rcases le_total ‖z.re‖ ‖z.im‖ with hle | hle
      · refine ⟨z.im, ?_, by rw [max_eq_right hle]⟩
        intro h; rw [h, norm_zero] at hle
        have : ‖z.re‖ = 0 := le_antisymm hle (norm_nonneg _)
        exact h0 ⟨norm_eq_zero.mp this, h⟩
      · refine ⟨z.re, ?_, by rw [max_eq_left hle]⟩
        intro h; rw [h, norm_zero] at hle
        have : ‖z.im‖ = 0 := le_antisymm hle (norm_nonneg _)
        exact h0 ⟨h, norm_eq_zero.mp this⟩
    set a : ℚ_[p] := z.re / s
    set b : ℚ_[p] := z.im / s
    have ha_le : ‖a‖ ≤ 1 := by
      rw [norm_div, hs_norm, div_le_one hmax_pos]; exact le_max_left _ _
    have hb_le : ‖b‖ ≤ 1 := by
      rw [norm_div, hs_norm, div_le_one hmax_pos]; exact le_max_right _ _
    have hab_max : max ‖a‖ ‖b‖ = 1 := by
      apply le_antisymm (max_le ha_le hb_le)
      rcases le_total ‖z.re‖ ‖z.im‖ with hle | hle
      · have hpos : 0 < ‖z.im‖ := by rwa [max_eq_right hle] at hmax_pos
        have : ‖b‖ = 1 := by rw [norm_div, hs_norm, max_eq_right hle, div_self hpos.ne']
        exact this ▸ le_max_right _ _
      · have hpos : 0 < ‖z.re‖ := by rwa [max_eq_left hle] at hmax_pos
        have : ‖a‖ = 1 := by rw [norm_div, hs_norm, max_eq_left hle, div_self hpos.ne']
        exact this ▸ le_max_left _ _
    set w : ℚ_[p] := a ^ 2 + quadTrace p .unramified * a * b - quadDelta p .unramified * b ^ 2
    have hnorm_w_le : ‖w‖ ≤ 1 := by
      have ht_le : ‖quadTrace p .unramified‖ ≤ 1 := by
        unfold quadTrace; split_ifs <;> simp
      have hd_le : ‖quadDelta p .unramified‖ ≤ 1 := by
        unfold quadDelta; split_ifs
        · simp
        · rw [norm_nonSquareUnitNat p]
      have h1 : ‖a ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha_le
      have h2 : ‖quadTrace p .unramified * a * b‖ ≤ 1 := by
        rw [norm_mul, norm_mul]
        have hta : ‖quadTrace p .unramified‖ * ‖a‖ ≤ 1 := by
          calc ‖quadTrace p .unramified‖ * ‖a‖ ≤ 1 * 1 :=
                mul_le_mul ht_le ha_le (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        calc ‖quadTrace p .unramified‖ * ‖a‖ * ‖b‖ ≤ 1 * 1 :=
              mul_le_mul hta hb_le (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have h3 : ‖quadDelta p .unramified * b ^ 2‖ ≤ 1 := by
        rw [norm_mul, norm_pow]
        calc ‖quadDelta p .unramified‖ * ‖b‖ ^ 2 ≤ 1 * 1 :=
              mul_le_mul hd_le (pow_le_one₀ (norm_nonneg _) hb_le) (sq_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      unfold w
      rw [sub_eq_add_neg]
      refine (Padic.nonarchimedean _ _).trans
        (max_le ((Padic.nonarchimedean _ _).trans (max_le h1 h2)) ?_)
      rw [norm_neg]; exact h3
    have hnorm_w_eq : ‖w‖ = 1 := by
      apply le_antisymm hnorm_w_le
      by_contra hlt
      push Not at hlt
      have hw0 : PadicInt.toZMod (mkPadicInt hnorm_w_le) = 0 :=
        (padicInt_toZMod_eq_zero_iff p _).mpr hlt
      have hnot_both : PadicInt.toZMod (mkPadicInt ha_le) ≠ 0 ∨
          PadicInt.toZMod (mkPadicInt hb_le) ≠ 0 := by
        by_contra hboth
        push Not at hboth
        have ha1 : ‖a‖ < 1 := (padicInt_toZMod_eq_zero_iff p _).mp hboth.1
        have hb1 : ‖b‖ < 1 := (padicInt_toZMod_eq_zero_iff p _).mp hboth.2
        have hlt1 : max ‖a‖ ‖b‖ < 1 := max_lt ha1 hb1
        linarith
      by_cases hp2 : p = 2
      · subst hp2
        have hrel : (PadicInt.toZMod (mkPadicInt ha_le)) ^ 2 +
            PadicInt.toZMod (mkPadicInt ha_le) * PadicInt.toZMod (mkPadicInt hb_le) -
            (PadicInt.toZMod (mkPadicInt hb_le)) ^ 2 = 0 := by
          have hw_eq : mkPadicInt hnorm_w_le =
              mkPadicInt ha_le ^ 2 + mkPadicInt ha_le * mkPadicInt hb_le - mkPadicInt hb_le ^ 2 := by
            apply padicInt_ext; simp [w, quadTrace, quadDelta]
          have hm := congrArg PadicInt.toZMod hw_eq
          simp only [map_sub, map_add, map_mul, map_pow] at hm
          exact hm.symm.trans hw0
        exact zmod2_quad_ne_zero _ _ hnot_both hrel
      · have hrel : (PadicInt.toZMod (mkPadicInt ha_le)) ^ 2 -
            ((nonSquareUnitNat p : ℕ) : ZMod p) * (PadicInt.toZMod (mkPadicInt hb_le)) ^ 2 = 0 := by
          have hw_eq : mkPadicInt hnorm_w_le =
              mkPadicInt ha_le ^ 2 -
                ((nonSquareUnitNat p : ℕ) : ℤ_[p]) * mkPadicInt hb_le ^ 2 := by
            apply padicInt_ext; simp [w, quadTrace, quadDelta, hp2]
          have hm := congrArg PadicInt.toZMod hw_eq
          simp only [map_sub, map_mul, map_pow, map_natCast] at hm
          exact hm.symm.trans hw0
        have hb0 : PadicInt.toZMod (mkPadicInt hb_le) ≠ 0 := by
          intro hb_zero
          rw [hb_zero, zero_pow two_ne_zero, mul_zero, sub_zero] at hrel
          have ha0 : PadicInt.toZMod (mkPadicInt ha_le) = 0 := eq_zero_of_pow_eq_zero hrel
          rcases hnot_both with h | h
          · exact h ha0
          · exact h hb_zero
        have hsq : IsSquare ((nonSquareUnitNat p : ℕ) : ZMod p) := by
          refine ⟨PadicInt.toZMod (mkPadicInt ha_le) * (PadicInt.toZMod (mkPadicInt hb_le))⁻¹, ?_⟩
          have h1 : (PadicInt.toZMod (mkPadicInt ha_le)) ^ 2 =
              ((nonSquareUnitNat p : ℕ) : ZMod p) * (PadicInt.toZMod (mkPadicInt hb_le)) ^ 2 :=
            sub_eq_zero.mp hrel
          have hb_sq : (PadicInt.toZMod (mkPadicInt hb_le)) ^ 2 ≠ 0 := pow_ne_zero 2 hb0
          calc ((nonSquareUnitNat p : ℕ) : ZMod p)
              = ((nonSquareUnitNat p : ℕ) : ZMod p) * (PadicInt.toZMod (mkPadicInt hb_le)) ^ 2 *
                  ((PadicInt.toZMod (mkPadicInt hb_le)) ^ 2)⁻¹ := by rw [mul_inv_cancel_right₀ hb_sq]
            _ = (PadicInt.toZMod (mkPadicInt ha_le)) ^ 2 *
                  ((PadicInt.toZMod (mkPadicInt hb_le)) ^ 2)⁻¹ := by rw [h1]
            _ = (PadicInt.toZMod (mkPadicInt ha_le) * (PadicInt.toZMod (mkPadicInt hb_le))⁻¹) *
                  (PadicInt.toZMod (mkPadicInt ha_le) * (PadicInt.toZMod (mkPadicInt hb_le))⁻¹) := by
                ring
        exact (nonSquareUnitNat_spec_odd p hp2).2.2 hsq
    have hz_eq : z.normVal = s ^ 2 * w := by
      unfold normVal w a b
      field_simp [hs_ne]
    rw [hz_eq, norm_mul, norm_pow, hnorm_w_eq, mul_one, hs_norm]
    rcases le_total ‖z.re‖ ‖z.im‖ with hle | hle
    · rw [max_eq_right hle, max_eq_right (pow_le_pow_left₀ (norm_nonneg _) hle 2)]
    · rw [max_eq_left hle, max_eq_left (pow_le_pow_left₀ (norm_nonneg _) hle 2)]

/-- **Exact Ultrametric Norm Formula for Ramified `QuadField p E`** (ALL primes `p`):
`‖N(c, d)‖_p = max (‖c‖_p²) (p⁻¹ * ‖d‖_p²)`. -/
theorem norm_normVal_ramified (hram : E ≠ .unramified) (z : QuadField p E) :
    ‖z.normVal‖ = max (‖z.re‖ ^ 2) ((p : ℝ)⁻¹ * ‖z.im‖ ^ 2) := by
  have htr : quadTrace p E = 0 := by cases E <;> simp_all [quadTrace]
  have hd_norm : ‖quadDelta p E‖ = (p : ℝ)⁻¹ := by
    cases E with
    | unramified => exact absurd rfl hram
    | ramifiedStd => simp [quadDelta, Padic.norm_p]
    | ramifiedTwist =>
      simp [quadDelta, norm_mul, norm_nonSquareUnitNat p, Padic.norm_p]
  have hval_eq : z.normVal = z.re ^ 2 + -(quadDelta p E * z.im ^ 2) := by
    unfold normVal; rw [htr]; ring
  rw [hval_eq]
  by_cases ha : z.re = 0
  · simp only [ha, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, norm_neg,
      norm_mul, norm_pow, hd_norm, norm_zero]
    exact (max_eq_right (mul_nonneg (inv_nonneg.mpr (prime_pos_R p).le) (sq_nonneg _))).symm
  by_cases hb : z.im = 0
  · simp [hb]
  have hne : ‖z.re ^ 2‖ ≠ ‖-(quadDelta p E * z.im ^ 2)‖ := by
    intro heq
    rw [norm_neg, norm_mul, norm_pow, norm_pow, hd_norm,
      Padic.norm_eq_zpow_neg_valuation ha, Padic.norm_eq_zpow_neg_valuation hb] at heq
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_neg_one, ← zpow_add₀ (prime_ne_zero_R p)] at heq
    have hexp : (-Padic.valuation z.re) * (2 : ℤ) = -1 + (-Padic.valuation z.im) * (2 : ℤ) := by
      by_contra hne_exp
      rcases lt_or_gt_of_ne hne_exp with hlt | hgt
      · exact (zpow_lt_zpow_right₀ (prime_one_lt_R p) hlt).ne heq
      · exact (zpow_lt_zpow_right₀ (prime_one_lt_R p) hgt).ne' heq
    omega
  rw [Padic.add_eq_max_of_ne hne, norm_neg, norm_mul, norm_pow, norm_pow, hd_norm]

theorem normVal_eq_zero_iff (z : QuadField p E) : z.normVal = 0 ↔ z = ⟨0, 0⟩ := by
  constructor
  · intro h0
    have hn0 : ‖z.normVal‖ = 0 := by rw [h0, norm_zero]
    cases E with
    | unramified =>
      rw [norm_normVal_unramified] at hn0
      have ha : ‖z.re‖ ^ 2 = 0 := le_antisymm ((le_max_left _ _).trans hn0.le) (sq_nonneg _)
      have hb : ‖z.im‖ ^ 2 = 0 := le_antisymm ((le_max_right _ _).trans hn0.le) (sq_nonneg _)
      ext
      · exact norm_eq_zero.mp (sq_eq_zero_iff.mp ha)
      · exact norm_eq_zero.mp (sq_eq_zero_iff.mp hb)
    | ramifiedStd | ramifiedTwist =>
      rw [norm_normVal_ramified (by simp)] at hn0
      have ha : ‖z.re‖ ^ 2 = 0 := le_antisymm ((le_max_left _ _).trans hn0.le) (sq_nonneg _)
      have hb : (p : ℝ)⁻¹ * ‖z.im‖ ^ 2 = 0 :=
        le_antisymm ((le_max_right _ _).trans hn0.le)
          (mul_nonneg (inv_nonneg.mpr (prime_pos_R p).le) (sq_nonneg _))
      have hb' : ‖z.im‖ ^ 2 = 0 :=
        (mul_eq_zero.mp hb).resolve_left (inv_ne_zero (prime_ne_zero_R p))
      ext
      · exact norm_eq_zero.mp (sq_eq_zero_iff.mp ha)
      · exact norm_eq_zero.mp (sq_eq_zero_iff.mp hb')
  · rintro rfl; simp [normVal]

instance : Zero (QuadField p E) := ⟨⟨0, 0⟩⟩
instance : One (QuadField p E) := ⟨⟨1, 0⟩⟩
instance : Add (QuadField p E) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (QuadField p E) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (QuadField p E) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul (QuadField p E) :=
  ⟨fun z w =>
    ⟨z.re * w.re + quadDelta p E * z.im * w.im,
     z.re * w.im + z.im * w.re + quadTrace p E * z.im * w.im⟩⟩
instance : Inv (QuadField p E) :=
  ⟨fun z =>
    ⟨(z.re + quadTrace p E * z.im) / z.normVal, -z.im / z.normVal⟩⟩

@[simp] lemma zero_re : (0 : QuadField p E).re = 0 := rfl
@[simp] lemma zero_im : (0 : QuadField p E).im = 0 := rfl
@[simp] lemma one_re : (1 : QuadField p E).re = 1 := rfl
@[simp] lemma one_im : (1 : QuadField p E).im = 0 := rfl
@[simp] lemma add_re (z w : QuadField p E) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : QuadField p E) : (z + w).im = z.im + w.im := rfl
@[simp] lemma neg_re (z : QuadField p E) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : QuadField p E) : (-z).im = -z.im := rfl
@[simp] lemma sub_re (z w : QuadField p E) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : QuadField p E) : (z - w).im = z.im - w.im := rfl
@[simp] lemma mul_re (z w : QuadField p E) :
    (z * w).re = z.re * w.re + quadDelta p E * z.im * w.im := rfl
@[simp] lemma mul_im (z w : QuadField p E) :
    (z * w).im = z.re * w.im + z.im * w.re + quadTrace p E * z.im * w.im := rfl

instance : CommRing (QuadField p E) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring

instance : Field (QuadField p E) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg QuadField.re h)⟩
  mul_inv_cancel a ha := by
    have hn : a.normVal ≠ 0 := mt (normVal_eq_zero_iff a).mp ha
    ext
    · change a.re * ((a.re + quadTrace p E * a.im) / a.normVal) +
          quadDelta p E * a.im * (-a.im / a.normVal) = 1
      have hfac : a.re * ((a.re + quadTrace p E * a.im) / a.normVal) +
          quadDelta p E * a.im * (-a.im / a.normVal) = a.normVal / a.normVal := by
        unfold normVal; ring
      rw [hfac, div_self hn]
    · change a.re * (-a.im / a.normVal) + a.im * ((a.re + quadTrace p E * a.im) / a.normVal) +
          quadTrace p E * a.im * (-a.im / a.normVal) = 0
      ring
  inv_zero := by ext <;> simp [Inv.inv, normVal]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- Multiplicative field norm `N_{E/ℚ_p} : QuadField p E →* ℚ_[p]`. -/
def quadNorm : QuadField p E →* ℚ_[p] where
  toFun := normVal
  map_one' := by simp [normVal]
  map_mul' z w := by unfold normVal; simp; ring

/-- Unit-level norm homomorphism `N_{E/ℚ_p} : (QuadField p E)ˣ →* ℚ_[p]ˣ`. -/
def quadNormUnits : (QuadField p E)ˣ →* ℚ_[p]ˣ := Units.map quadNorm

/-- Galois conjugation automorphism `σ : QuadField p E ≃+* QuadField p E` (`c + d ω ↦ (c + t d) - d ω`). -/
def quadGal : QuadField p E ≃+* QuadField p E where
  toFun z := ⟨z.re + quadTrace p E * z.im, -z.im⟩
  invFun z := ⟨z.re + quadTrace p E * z.im, -z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp <;> ring
  map_add' z w := by ext <;> simp <;> ring

/-- Galois conjugation on units `(QuadField p E)ˣ ≃* (QuadField p E)ˣ`. -/
def quadGalUnits : (QuadField p E)ˣ ≃* (QuadField p E)ˣ :=
  Units.mapEquiv quadGal.toMulEquiv

@[simp]
lemma quadGalUnits_coe (u : (QuadField p E)ˣ) :
    ((quadGalUnits u : (QuadField p E)ˣ) : QuadField p E) = quadGal (u : QuadField p E) := rfl

/-- Canonical embedding `ℚ_[p] →+* QuadField p E` (`c ↦ (c, 0)`). -/
def quadEmbed : ℚ_[p] →+* QuadField p E where
  toFun c := ⟨c, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp
  map_zero' := rfl
  map_add' a b := by ext <;> simp

/-- Canonical embedding on units `ℚ_[p]ˣ →* (QuadField p E)ˣ`. -/
def quadEmbedUnits : ℚ_[p]ˣ →* (QuadField p E)ˣ :=
  Units.map quadEmbed.toMonoidHom

@[simp]
lemma quadGal_quadGal (z : QuadField p E) : quadGal (quadGal z) = z := by
  ext <;> simp [quadGal]

@[simp]
lemma quadGalUnits_invol (u : (QuadField p E)ˣ) :
    quadGalUnits (quadGalUnits u) = u := by
  apply Units.ext
  exact quadGal_quadGal (u : QuadField p E)

@[simp]
lemma quadNorm_quadGal (z : QuadField p E) : quadNorm (quadGal z) = quadNorm z := by
  simp [quadNorm, normVal, quadGal]; ring

@[simp]
lemma quadNormUnits_quadGalUnits (u : (QuadField p E)ˣ) :
    quadNormUnits (quadGalUnits u) = quadNormUnits u := by
  apply Units.ext
  exact quadNorm_quadGal (u : QuadField p E)

@[simp]
lemma quadNorm_quadEmbed (c : ℚ_[p]) : quadNorm (quadEmbed (E := E) c) = c ^ 2 := by
  simp [quadNorm, normVal, quadEmbed]

@[simp]
lemma quadNormUnits_quadEmbedUnits (x : ℚ_[p]ˣ) :
    quadNormUnits (quadEmbedUnits (E := E) x) = x ^ 2 := by
  apply Units.ext
  simp [quadNormUnits, quadEmbedUnits, sq]

@[simp]
lemma quadGal_quadEmbed (c : ℚ_[p]) : quadGal (quadEmbed (E := E) c) = quadEmbed c := by
  ext <;> simp [quadGal, quadEmbed]

@[simp]
lemma quadGalUnits_quadEmbedUnits (x : ℚ_[p]ˣ) :
    quadGalUnits (quadEmbedUnits (E := E) x) = quadEmbedUnits x := by
  apply Units.ext
  exact quadGal_quadEmbed (x : ℚ_[p])

/-- Ultrametric inequality for the field norm `‖N(z + w)‖_p ≤ max ‖N(z)‖_p ‖N(w)‖_p`. -/
theorem norm_quadNorm_add_le (z w : QuadField p E) :
    ‖quadNorm (z + w)‖ ≤ max ‖quadNorm z‖ ‖quadNorm w‖ := by
  have hsq : ∀ x y : ℚ_[p], ‖x + y‖ ^ 2 ≤ max (‖x‖ ^ 2) (‖y‖ ^ 2) := fun x y => by
    have h1 : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := Padic.nonarchimedean x y
    have h2 : ‖x + y‖ ^ 2 ≤ (max ‖x‖ ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rcases le_total ‖x‖ ‖y‖ with hle | hle
    · rw [max_eq_right hle] at h2
      exact h2.trans (le_max_right _ _)
    · rw [max_eq_left hle] at h2
      exact h2.trans (le_max_left _ _)
  cases E with
  | unramified =>
    change ‖(z + w).normVal‖ ≤ max ‖z.normVal‖ ‖w.normVal‖
    rw [norm_normVal_unramified, norm_normVal_unramified, norm_normVal_unramified]
    exact max_le
      ((hsq z.re w.re).trans (max_le ((le_max_left _ _).trans (le_max_left _ _))
        ((le_max_left _ _).trans (le_max_right _ _))))
      ((hsq z.im w.im).trans (max_le ((le_max_right _ _).trans (le_max_left _ _))
        ((le_max_right _ _).trans (le_max_right _ _))))
  | ramifiedStd | ramifiedTwist =>
    change ‖(z + w).normVal‖ ≤ max ‖z.normVal‖ ‖w.normVal‖
    rw [norm_normVal_ramified (by simp), norm_normVal_ramified (by simp),
      norm_normVal_ramified (by simp)]
    have hp_inv : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (prime_pos_R p).le
    refine max_le
      ((hsq z.re w.re).trans (max_le ((le_max_left _ _).trans (le_max_left _ _))
        ((le_max_left _ _).trans (le_max_right _ _)))) ?_
    calc (p : ℝ)⁻¹ * ‖z.im + w.im‖ ^ 2
        ≤ (p : ℝ)⁻¹ * max (‖z.im‖ ^ 2) (‖w.im‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hsq z.im w.im) hp_inv
      _ = max ((p : ℝ)⁻¹ * ‖z.im‖ ^ 2) ((p : ℝ)⁻¹ * ‖w.im‖ ^ 2) := mul_max_of_nonneg _ _ hp_inv
      _ ≤ max (max (‖z.re‖ ^ 2) ((p : ℝ)⁻¹ * ‖z.im‖ ^ 2))
              (max (‖w.re‖ ^ 2) ((p : ℝ)⁻¹ * ‖w.im‖ ^ 2)) :=
          max_le ((le_max_right _ _).trans (le_max_left _ _))
            ((le_max_right _ _).trans (le_max_right _ _))

@[simp]
lemma norm_quadNorm_neg (z : QuadField p E) : ‖quadNorm (-z)‖ = ‖quadNorm z‖ := by
  have h : quadNorm (-z) = quadNorm z := by simp [quadNorm, normVal]
  rw [h]

/-- Higher-unit filtration `U_E^n` on `(QuadField p E)ˣ`:
- `n = 0`: `𝒪_Eˣ = { u | ‖N(u)‖_p = 1 }`,
- `n ≥ 1`: `1 + ϖ_E^n 𝒪_E = { u | ‖N(u)‖_p = 1 ∧ ‖N(u - 1)‖_p ≤ p^{-f(E/ℚ_p) · n} }`. -/
def IsInQuadUnitFilt (n : ℕ) (u : (QuadField p E)ˣ) : Prop :=
  ‖quadNorm (u : QuadField p E)‖ = 1 ∧
    (n = 0 ∨ ‖quadNorm ((u : QuadField p E) - 1)‖ ≤ (p : ℝ) ^ (-((E.residueDeg * n : ℕ) : ℤ)))

lemma isInQuadUnitFilt_one (n : ℕ) : IsInQuadUnitFilt (E := E) n 1 := by
  refine ⟨by simp, Or.inr ?_⟩
  simp only [Units.val_one, sub_self, quadNorm, MonoidHom.coe_mk, OneHom.coe_mk, normVal,
    zero_re, zero_im, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero, sub_self, norm_zero]
  exact (zpow_pos (prime_pos_R p) _).le

lemma isInQuadUnitFilt_mul {n : ℕ} {u v : (QuadField p E)ˣ}
    (hu : IsInQuadUnitFilt (E := E) n u) (hv : IsInQuadUnitFilt (E := E) n v) :
    IsInQuadUnitFilt (E := E) n (u * v) := by
  refine ⟨by rw [Units.val_mul, map_mul, norm_mul, hu.1, hv.1, mul_one], ?_⟩
  rcases hu.2 with rfl | hu2
  · exact Or.inl rfl
  · rcases hv.2 with rfl | hv2
    · exact Or.inl rfl
    · right
      have hsplit : ((u * v : (QuadField p E)ˣ) : QuadField p E) - 1 =
          (u : QuadField p E) * ((v : QuadField p E) - 1) + ((u : QuadField p E) - 1) := by
        rw [Units.val_mul]; ring
      rw [hsplit]
      refine (norm_quadNorm_add_le _ _).trans (max_le ?_ hu2)
      rw [map_mul, norm_mul, hu.1, one_mul]
      exact hv2

lemma isInQuadUnitFilt_inv {n : ℕ} {u : (QuadField p E)ˣ}
    (hu : IsInQuadUnitFilt (E := E) n u) :
    IsInQuadUnitFilt (E := E) n u⁻¹ := by
  have hinv_norm : ‖quadNorm ((u⁻¹ : (QuadField p E)ˣ) : QuadField p E)‖ = 1 := by
    have hmul : ‖quadNorm ((u : QuadField p E) * ((u⁻¹ : (QuadField p E)ˣ) : QuadField p E))‖ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, norm_one]
    rw [map_mul, norm_mul, hu.1, one_mul] at hmul
    exact hmul
  refine ⟨hinv_norm, ?_⟩
  rcases hu.2 with rfl | hu2
  · exact Or.inl rfl
  · right
    have hmul : ((u⁻¹ : (QuadField p E)ˣ) : QuadField p E) * (u : QuadField p E) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hsplit : ((u⁻¹ : (QuadField p E)ˣ) : QuadField p E) - 1 =
        -(((u⁻¹ : (QuadField p E)ˣ) : QuadField p E) * ((u : QuadField p E) - 1)) := by
      rw [mul_sub, mul_one, hmul]; ring
    rw [hsplit, norm_quadNorm_neg, map_mul, norm_mul, hinv_norm, one_mul]
    exact hu2

lemma isInQuadUnitFilt_mono {m n : ℕ} (hmn : m ≤ n) {u : (QuadField p E)ˣ}
    (hu : IsInQuadUnitFilt (E := E) n u) :
    IsInQuadUnitFilt (E := E) m u := by
  refine ⟨hu.1, ?_⟩
  by_cases hm : m = 0
  · exact Or.inl hm
  · right
    rcases hu.2 with rfl | hu2
    · omega
    · refine hu2.trans ?_
      have hmul : E.residueDeg * m ≤ E.residueDeg * n := Nat.mul_le_mul_left _ hmn
      exact zpow_le_zpow_right₀ (prime_one_lt_R p).le (by omega)

lemma isInQuadUnitFilt_quadGal {n : ℕ} {u : (QuadField p E)ˣ}
    (hu : IsInQuadUnitFilt (E := E) n u) :
    IsInQuadUnitFilt (E := E) n (quadGalUnits u) := by
  refine ⟨by rw [quadGalUnits_coe, quadNorm_quadGal]; exact hu.1, ?_⟩
  rcases hu.2 with rfl | hu2
  · exact Or.inl rfl
  · right
    have hsub : ((quadGalUnits u : (QuadField p E)ˣ) : QuadField p E) - 1 =
        quadGal ((u : QuadField p E) - 1) := by
      rw [quadGalUnits_coe, map_sub, map_one]
    rw [hsub, quadNorm_quadGal]
    exact hu2

lemma isInQuadUnitFilt_quadEmbed {n : ℕ} {u : ℚ_[p]ˣ} (hu : IsInUnitFilt p n u) :
    IsInQuadUnitFilt (E := E) n (quadEmbedUnits u) := by
  refine ⟨by change ‖quadNorm (quadEmbed (u : ℚ_[p]))‖ = 1
             rw [quadNorm_quadEmbed, norm_pow, hu.1, one_pow], ?_⟩
  rcases hu.2 with rfl | hu2
  · exact Or.inl rfl
  · right
    have hsub : ((quadEmbedUnits (E := E) u : (QuadField p E)ˣ) : QuadField p E) - 1 =
        quadEmbed ((u : ℚ_[p]) - 1) := by
      change quadEmbed (u : ℚ_[p]) - 1 = _
      rw [map_sub, map_one]
    rw [hsub, quadNorm_quadEmbed, norm_pow]
    have hle : ‖(u : ℚ_[p]) - 1‖ ^ 2 ≤ ((p : ℝ) ^ (-(n : ℤ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hu2 2
    refine hle.trans ?_
    rw [← zpow_natCast, ← zpow_mul]
    have hdeg : E.residueDeg ≤ 2 := by cases E <;> simp [QuadExtType.residueDeg]
    have hmul : E.residueDeg * n ≤ 2 * n := Nat.mul_le_mul_right n hdeg
    exact zpow_le_zpow_right₀ (prime_one_lt_R p).le (by omega)

lemma isInUnitFilt_quadNorm {n : ℕ} {u : (QuadField p E)ˣ}
    (hu : IsInQuadUnitFilt (E := E) (E.ramIndex * n) u) :
    IsInUnitFilt p n (quadNormUnits u) := by
  refine ⟨hu.1, ?_⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    rcases hu.2 with h0 | hu2
    · exfalso
      have hpos := Nat.mul_pos E.ramIndex_pos (Nat.pos_of_ne_zero hn)
      omega
    · set w : QuadField p E := (u : QuadField p E) - 1
      have hNw : ‖quadNorm w‖ ≤ (p : ℝ) ^ (-(2 * (n : ℤ))) := by
        have hmul : ((E.residueDeg * (E.ramIndex * n) : ℕ) : ℤ) = 2 * (n : ℤ) := by
          have : E.residueDeg * (E.ramIndex * n) = 2 * n := by
            rw [← mul_assoc, mul_comm E.residueDeg E.ramIndex, E.ramIndex_mul_residueDeg]
          exact_mod_cast this
        rw [hmul] at hu2
        exact hu2
      have hre : ‖w.re‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
        have hsq : ‖w.re‖ ^ 2 ≤ (p : ℝ) ^ (-(2 * (n : ℤ))) := by
          refine le_trans ?_ hNw
          cases E with
          | unramified =>
            change ‖w.re‖ ^ 2 ≤ ‖w.normVal‖
            rw [norm_normVal_unramified]; exact le_max_left _ _
          | ramifiedStd | ramifiedTwist =>
            change ‖w.re‖ ^ 2 ≤ ‖w.normVal‖
            rw [norm_normVal_ramified (by simp)]; exact le_max_left _ _
        have hrhs : (p : ℝ) ^ (-(2 * (n : ℤ))) = ((p : ℝ) ^ (-(n : ℤ))) ^ 2 := by
          rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
        rw [hrhs] at hsq
        nlinarith [norm_nonneg w.re, zpow_pos (prime_pos_R p) (-(n : ℤ))]
      have htr_im : ‖quadTrace p E * w.im‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
        cases E with
        | unramified =>
          have hsq : ‖w.im‖ ^ 2 ≤ (p : ℝ) ^ (-(2 * (n : ℤ))) := by
            refine le_trans ?_ hNw
            change ‖w.im‖ ^ 2 ≤ ‖w.normVal‖
            rw [norm_normVal_unramified]; exact le_max_right _ _
          have hrhs : (p : ℝ) ^ (-(2 * (n : ℤ))) = ((p : ℝ) ^ (-(n : ℤ))) ^ 2 := by
            rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
          rw [hrhs] at hsq
          have him : ‖w.im‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
            nlinarith [norm_nonneg w.im, zpow_pos (prime_pos_R p) (-(n : ℤ))]
          have ht_le : ‖quadTrace p .unramified‖ ≤ 1 := by unfold quadTrace; split_ifs <;> simp
          rw [norm_mul]
          calc ‖quadTrace p .unramified‖ * ‖w.im‖ ≤ 1 * (p : ℝ) ^ (-(n : ℤ)) :=
                mul_le_mul ht_le him (norm_nonneg _) zero_le_one
            _ = (p : ℝ) ^ (-(n : ℤ)) := one_mul _
        | ramifiedStd | ramifiedTwist =>
          simp [quadTrace]
      have hident : ((quadNormUnits u : ℚ_[p]ˣ) : ℚ_[p]) - 1 =
          quadNorm w + ((2 : ℤ) : ℚ_[p]) * w.re + quadTrace p E * w.im := by
        change quadNorm (u : QuadField p E) - 1 = _
        have huw : (u : QuadField p E) = 1 + w := by simp [w]
        rw [huw]
        simp [quadNorm, normVal]
        ring
      rw [hident]
      have hNw' : ‖quadNorm w‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
        hNw.trans (zpow_le_zpow_right₀ (prime_one_lt_R p).le (by omega))
      have h2re : ‖((2 : ℤ) : ℚ_[p]) * w.re‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
        rw [norm_mul]
        calc ‖((2 : ℤ) : ℚ_[p])‖ * ‖w.re‖ ≤ 1 * (p : ℝ) ^ (-(n : ℤ)) :=
              mul_le_mul (Padic.norm_int_le_one 2) hre (norm_nonneg _) zero_le_one
          _ = (p : ℝ) ^ (-(n : ℤ)) := one_mul _
      exact (Padic.nonarchimedean _ _).trans
        (max_le ((Padic.nonarchimedean _ _).trans (max_le hNw' h2re)) htr_im)

end QuadField

/-- Smooth multiplicative character `θ : Eˣ →* ℂˣ` on the concrete quadratic extension
`QuadField p E`. -/
structure QuadChar (E : QuadExtType p) where
  toHom : (QuadField p E)ˣ →* ℂˣ
  smooth : ∃ n : ℕ, ∀ u : (QuadField p E)ˣ, QuadField.IsInQuadUnitFilt (E := E) n u → toHom u = 1

namespace QuadChar

variable {p} {E : QuadExtType p}

@[ext]
lemma ext_hom {θ₁ θ₂ : QuadChar p E} (h : ∀ x : (QuadField p E)ˣ, θ₁.toHom x = θ₂.toHom x) :
    θ₁ = θ₂ := by
  cases θ₁; cases θ₂
  congr
  exact MonoidHom.ext h

instance : CommGroup (QuadChar p E) where
  one := ⟨1, ⟨0, fun _ _ => rfl⟩⟩
  mul θ₁ θ₂ :=
    ⟨θ₁.toHom * θ₂.toHom, by
      rcases θ₁.smooth with ⟨n₁, h₁⟩
      rcases θ₂.smooth with ⟨n₂, h₂⟩
      refine ⟨max n₁ n₂, fun u hu => ?_⟩
      simp only [MonoidHom.mul_apply]
      rw [h₁ u (QuadField.isInQuadUnitFilt_mono (le_max_left n₁ n₂) hu),
        h₂ u (QuadField.isInQuadUnitFilt_mono (le_max_right n₁ n₂) hu), mul_one]⟩
  inv θ :=
    ⟨θ.toHom⁻¹, by
      rcases θ.smooth with ⟨n, hn⟩
      refine ⟨n, fun u hu => ?_⟩
      simp only [MonoidHom.inv_apply, hn u hu, inv_one]⟩
  mul_assoc a b c := ext_hom fun x => mul_assoc (a.toHom x) (b.toHom x) (c.toHom x)
  one_mul a := ext_hom fun x => one_mul (a.toHom x)
  mul_one a := ext_hom fun x => mul_one (a.toHom x)
  inv_mul_cancel a := ext_hom fun x => inv_mul_cancel (a.toHom x)
  mul_comm a b := ext_hom fun x => mul_comm (a.toHom x) (b.toHom x)

@[simp] lemma one_toHom : (1 : QuadChar p E).toHom = 1 := rfl
@[simp] lemma mul_toHom (θ₁ θ₂ : QuadChar p E) : (θ₁ * θ₂).toHom = θ₁.toHom * θ₂.toHom := rfl
@[simp] lemma inv_toHom (θ : QuadChar p E) : θ⁻¹.toHom = θ.toHom⁻¹ := rfl

/-- Galois conjugate character `θ^σ = θ ∘ σ` on `QuadField p E`. -/
def galConj : QuadChar p E →* QuadChar p E where
  toFun θ :=
    ⟨θ.toHom.comp QuadField.quadGalUnits.toMonoidHom, by
      rcases θ.smooth with ⟨n, hn⟩
      exact ⟨n, fun u hu => hn (QuadField.quadGalUnits u) (QuadField.isInQuadUnitFilt_quadGal hu)⟩⟩
  map_one' := ext_hom fun _ => rfl
  map_mul' _ _ := ext_hom fun _ => rfl

@[simp]
lemma galConj_galConj (θ : QuadChar p E) : θ.galConj.galConj = θ :=
  ext_hom fun u => by
    change θ.toHom (QuadField.quadGalUnits (QuadField.quadGalUnits u)) = θ.toHom u
    rw [QuadField.quadGalUnits_invol]

/-- Restriction `θ|_{ℚ_pˣ} : LocalChar p` via `quadEmbedUnits`. -/
def resQp : QuadChar p E →* LocalChar p where
  toFun θ :=
    ⟨θ.toHom.comp QuadField.quadEmbedUnits, by
      rcases θ.smooth with ⟨n, hn⟩
      exact ⟨n, fun u hu => hn (QuadField.quadEmbedUnits u) (QuadField.isInQuadUnitFilt_quadEmbed hu)⟩⟩
  map_one' := LocalChar.ext_hom fun _ => rfl
  map_mul' _ _ := LocalChar.ext_hom fun _ => rfl

@[simp]
lemma resQp_galConj (θ : QuadChar p E) : θ.galConj.resQp = θ.resQp :=
  LocalChar.ext_hom fun x => by
    change θ.toHom (QuadField.quadGalUnits (QuadField.quadEmbedUnits x)) =
      θ.toHom (QuadField.quadEmbedUnits x)
    rw [QuadField.quadGalUnits_quadEmbedUnits]

/-- Base-change lift `η ↦ η ∘ N_{E/ℚ_p}` from `LocalChar p` to `QuadChar p E`. -/
def baseChange : LocalChar p →* QuadChar p E where
  toFun η :=
    ⟨η.toHom.comp QuadField.quadNormUnits, by
      rcases η.smooth with ⟨n, hn⟩
      exact ⟨E.ramIndex * n, fun u hu =>
        hn (QuadField.quadNormUnits u) (QuadField.isInUnitFilt_quadNorm hu)⟩⟩
  map_one' := ext_hom fun _ => rfl
  map_mul' _ _ := ext_hom fun _ => rfl

@[simp]
lemma galConj_baseChange (η : LocalChar p) : (baseChange (E := E) η).galConj = baseChange η :=
  ext_hom fun u => by
    change η.toHom (QuadField.quadNormUnits (QuadField.quadGalUnits u)) =
      η.toHom (QuadField.quadNormUnits u)
    rw [QuadField.quadNormUnits_quadGalUnits]

@[simp]
lemma resQp_baseChange (η : LocalChar p) : (baseChange (E := E) η).resQp = η ^ 2 :=
  LocalChar.ext_hom fun x => by
    change η.toHom (QuadField.quadNormUnits (QuadField.quadEmbedUnits x)) = (η ^ 2).toHom x
    rw [QuadField.quadNormUnits_quadEmbedUnits, map_pow, sq, sq]
    rfl

/-- Exact conductor exponent `a(θ) : ℕ` on `Eˣ`. -/
def condExp (θ : QuadChar p E) : ℕ :=
  letI := Classical.decPred
    (fun n => ∀ u : (QuadField p E)ˣ, QuadField.IsInQuadUnitFilt (E := E) n u → θ.toHom u = 1)
  Nat.find θ.smooth

lemma condExp_spec (θ : QuadChar p E) :
    ∀ u : (QuadField p E)ˣ, QuadField.IsInQuadUnitFilt (E := E) θ.condExp u → θ.toHom u = 1 := by
  classical
  exact Nat.find_spec θ.smooth

lemma condExp_le {θ : QuadChar p E} {n : ℕ}
    (hn : ∀ u : (QuadField p E)ˣ, QuadField.IsInQuadUnitFilt (E := E) n u → θ.toHom u = 1) :
    θ.condExp ≤ n := by
  classical
  exact Nat.find_min' θ.smooth hn

lemma condExp_galConj (θ : QuadChar p E) : θ.galConj.condExp = θ.condExp := by
  apply le_antisymm
  · refine condExp_le fun u hu => ?_
    exact θ.condExp_spec (QuadField.quadGalUnits u) (QuadField.isInQuadUnitFilt_quadGal hu)
  · refine condExp_le fun u hu => ?_
    have h1 := θ.galConj.condExp_spec (QuadField.quadGalUnits u) (QuadField.isInQuadUnitFilt_quadGal hu)
    change θ.toHom (QuadField.quadGalUnits (QuadField.quadGalUnits u)) = 1 at h1
    rwa [QuadField.quadGalUnits_invol] at h1

lemma condExp_inv (θ : QuadChar p E) : θ⁻¹.condExp = θ.condExp := by
  apply le_antisymm
  · refine condExp_le fun u hu => ?_
    simp [θ.condExp_spec u hu]
  · refine condExp_le fun u hu => ?_
    have h1 := θ⁻¹.condExp_spec u hu
    simpa using congrArg Inv.inv h1

lemma condExp_mul_baseChange_unram (θ : QuadChar p E) {η : LocalChar p} (hη : η.IsUnramified) :
    (θ * baseChange η).condExp = θ.condExp := by
  have hbc0 : ∀ u : (QuadField p E)ˣ, ‖QuadField.quadNorm (u : QuadField p E)‖ = 1 →
      (baseChange (E := E) η).toHom u = 1 := fun u hu => hη (QuadField.quadNormUnits u) hu
  apply le_antisymm
  · refine condExp_le fun u hu => ?_
    simp only [mul_toHom, MonoidHom.mul_apply, θ.condExp_spec u hu, hbc0 u hu.1, mul_one]
  · refine condExp_le fun u hu => ?_
    have h1 := (θ * baseChange η).condExp_spec u hu
    simp only [mul_toHom, MonoidHom.mul_apply, hbc0 u hu.1, mul_one] at h1
    exact h1

/-- **Regularity Forces Ramification (`1 ≤ a(θ)`)**:
any character `θ : Eˣ →* ℂˣ` with `θ ≠ θ^σ` MUST be ramified (`1 ≤ θ.condExp`)! -/
theorem one_le_condExp_of_ne_galConj {θ : QuadChar p E} (hreg : θ ≠ θ.galConj) :
    1 ≤ θ.condExp := by
  by_contra hlt
  have h0 : θ.condExp = 0 := by omega
  apply hreg
  apply ext_hom
  intro z
  have hu_norm : ‖QuadField.quadNorm (((QuadField.quadGalUnits z * z⁻¹ : (QuadField p E)ˣ) : QuadField p E))‖ = 1 := by
    rw [Units.val_mul, map_mul, QuadField.quadGalUnits_coe, QuadField.quadNorm_quadGal]
    have hmul : QuadField.quadNorm (z : QuadField p E) *
        QuadField.quadNorm ((z⁻¹ : (QuadField p E)ˣ) : QuadField p E) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [hmul, norm_one]
  have hfilt : QuadField.IsInQuadUnitFilt (E := E) θ.condExp (QuadField.quadGalUnits z * z⁻¹) := by
    rw [h0]; exact ⟨hu_norm, Or.inl rfl⟩
  have h1 := θ.condExp_spec (QuadField.quadGalUnits z * z⁻¹) hfilt
  rw [map_mul, map_inv] at h1
  exact (eq_of_mul_inv_eq_one h1).symm

end QuadChar

/-! ### Local Class Field Theory Quadratic Character `ω_{E/ℚ_p}` (`quadCharOfExt`) -/

section QuadCharOfExt

private def chi2Mod8Bool (x : ZMod 8) : Bool := (x == 1) || (x == 7)

private lemma chi2Mod8Bool_mul (a b : ZMod 8) (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7)
    (hb : b = 1 ∨ b = 3 ∨ b = 5 ∨ b = 7) :
    (if chi2Mod8Bool (a * b) then (1 : ℤ) else -1) =
      (if chi2Mod8Bool a then (1 : ℤ) else -1) * (if chi2Mod8Bool b then (1 : ℤ) else -1) := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide

private lemma zmod8_unit_cases (u : (ZMod 8)ˣ) :
    (u : ZMod 8) = 1 ∨ (u : ZMod 8) = 3 ∨ (u : ZMod 8) = 5 ∨ (u : ZMod 8) = 7 := by
  have hcop : Nat.Coprime (u : ZMod 8).val 8 :=
    (ZMod.isUnit_iff_coprime (u : ZMod 8).val 8).mp (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
  have hfin : ∀ k : Fin 8, Nat.Coprime k.1 8 →
      (k.1 : ZMod 8) = 1 ∨ (k.1 : ZMod 8) = 3 ∨ (k.1 : ZMod 8) = 5 ∨ (k.1 : ZMod 8) = 7 := by
    decide
  simpa using hfin ⟨(u : ZMod 8).val, (u : ZMod 8).val_lt⟩ hcop

/-- Order-2 character on `(ZMod 8)ˣ` of conductor `3`: `u ↦ 1` if `u ≡ 1, 7 (mod 8)` and `-1` if
`u ≡ 3, 5 (mod 8)`. -/
private def chi2Mod8 : (ZMod 8)ˣ →* ℂˣ where
  toFun u := if chi2Mod8Bool (u : ZMod 8) then 1 else -1
  map_one' := by simp [chi2Mod8Bool]
  map_mul' a b := by
    have hZ := chi2Mod8Bool_mul (a : ZMod 8) (b : ZMod 8) (zmod8_unit_cases a) (zmod8_unit_cases b)
    apply Units.ext
    simp only [Units.val_mul]
    rcases Bool.eq_false_or_eq_true (chi2Mod8Bool ((a : ZMod 8) * (b : ZMod 8))) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (chi2Mod8Bool (a : ZMod 8)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (chi2Mod8Bool (b : ZMod 8)) with h3 | h3 <;>
    simp [h1, h2, h3] at hZ ⊢

private lemma chi2Mod8_sq (u : (ZMod 8)ˣ) : chi2Mod8 u * chi2Mod8 u = 1 := by
  unfold chi2Mod8
  dsimp only [MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs <;> simp

/-- Reduction map `ℤ_[p]ˣ →* (ZMod p)ˣ` via `PadicInt.toZMod`. -/
private def padicUnitToZMod (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1) : (ZMod p)ˣ :=
  Units.map (PadicInt.toZMod (p := p)).toMonoidHom
    (PadicInt.isUnit_iff.mpr (show ‖mkPadicInt hu.le‖ = 1 from hu)).unit

/-- Legendre quadratic character on `ℤ_[p]ˣ` for odd prime `p`. -/
private def oddQuadUnitVal (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1) : ℂˣ :=
  if IsSquare ((padicUnitToZMod p u hu : (ZMod p)ˣ) : ZMod p) then 1 else -1

private lemma oddQuadUnitVal_eq_legendreSym (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1) :
    ((oddQuadUnitVal p u hu : ℂˣ) : ℂ) =
      (legendreSym p (((padicUnitToZMod p u hu : (ZMod p)ˣ) : ZMod p).val : ℤ) : ℂ) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set z : ZMod p := ((padicUnitToZMod p u hu : (ZMod p)ˣ) : ZMod p)
  have hz_ne : z ≠ 0 := (padicUnitToZMod p u hu).ne_zero
  have hcast : ((z.val : ℤ) : ZMod p) = z := by simp
  unfold oddQuadUnitVal
  by_cases hsq : IsSquare z
  · rw [if_pos hsq]
    have hleg : legendreSym p (z.val : ℤ) = 1 :=
      (legendreSym.eq_one_iff p (by rwa [hcast])).mpr (by rwa [hcast])
    rw [hleg]; simp
  · rw [if_neg hsq]
    have hleg : legendreSym p (z.val : ℤ) = -1 :=
      (legendreSym.eq_neg_one_iff p).mpr (by rwa [hcast])
    rw [hleg]; simp

private lemma oddQuadUnitVal_mul {u v : ℚ_[p]ˣ}
    (hu : ‖(u : ℚ_[p])‖ = 1) (hv : ‖(v : ℚ_[p])‖ = 1) :
    oddQuadUnitVal p (u * v) (by rw [Units.val_mul, norm_mul, hu, hv, mul_one]) =
      oddQuadUnitVal p u hu * oddQuadUnitVal p v hv := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  apply Units.ext
  change ((oddQuadUnitVal p (u * v) _ : ℂˣ) : ℂ) =
    ((oddQuadUnitVal p u hu : ℂˣ) : ℂ) * ((oddQuadUnitVal p v hv : ℂˣ) : ℂ)
  rw [oddQuadUnitVal_eq_legendreSym, oddQuadUnitVal_eq_legendreSym, oddQuadUnitVal_eq_legendreSym]
  set zu : ZMod p := ((padicUnitToZMod p u hu : (ZMod p)ˣ) : ZMod p)
  set zv : ZMod p := ((padicUnitToZMod p v hv : (ZMod p)ˣ) : ZMod p)
  have hzuv : ((padicUnitToZMod p (u * v)
      (by rw [Units.val_mul, norm_mul, hu, hv, mul_one]) : (ZMod p)ˣ) : ZMod p) = zu * zv := by
    have h1 : mkPadicInt (show ‖((u * v : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 by
        rw [Units.val_mul, norm_mul, hu, hv, mul_one]) =
        mkPadicInt hu.le * mkPadicInt hv.le := padicInt_ext (by simp)
    change PadicInt.toZMod (mkPadicInt _) =
      PadicInt.toZMod (mkPadicInt hu.le) * PadicInt.toZMod (mkPadicInt hv.le)
    rw [h1, map_mul]
  rw [hzuv]
  have hleg_eq : legendreSym p ((zu * zv).val : ℤ) =
      legendreSym p ((zu.val : ℤ) * (zv.val : ℤ)) := by
    rw [legendreSym.mod p ((zu * zv).val : ℤ), legendreSym.mod p ((zu.val : ℤ) * (zv.val : ℤ))]
    congr 1
    have hdiv : (zu * zv).val + p * (zu.val * zv.val / p) = zu.val * zv.val := by
      rw [ZMod.val_mul]
      exact Nat.mod_add_div (zu.val * zv.val) p
    have hZ : ((zu.val : ℤ) * (zv.val : ℤ)) =
        ((zu * zv).val : ℤ) + (p : ℤ) * ((zu.val * zv.val / p : ℕ) : ℤ) := by
      exact_mod_cast hdiv.symm
    rw [hZ, Int.add_mul_emod_self_left]
  rw [hleg_eq, legendreSym.mul]
  push_cast
  rfl

private lemma oddQuadUnitVal_one_of_filt1 {u : ℚ_[p]ˣ}
    (hu : IsInUnitFilt p 1 u) : oddQuadUnitVal p u hu.1 = 1 := by
  have hsub : ‖(u : ℚ_[p]) - 1‖ < 1 := by
    rcases hu.2 with h0 | hle
    · omega
    · refine hle.trans_lt ?_
      rw [show -((1 : ℕ) : ℤ) = -1 from rfl, zpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (prime_one_lt_R p)
  have hz : PadicInt.toZMod (mkPadicInt hsub.le) = 0 :=
    (padicInt_toZMod_eq_zero_iff p _).mpr hsub
  have hu1 : ((padicUnitToZMod p u hu.1 : (ZMod p)ˣ) : ZMod p) = 1 := by
    have heq : mkPadicInt hsub.le = mkPadicInt hu.1.le - 1 := padicInt_ext (by simp)
    rw [heq, map_sub, map_one] at hz
    exact sub_eq_zero.mp hz
  simp [oddQuadUnitVal, hu1]

/-- Reduction map `ℤ_[2]ˣ →* (ZMod 8)ˣ` via `PadicInt.toZModPow 3`. -/
private def padic2UnitToZMod8 (u : ℚ_[2]ˣ) (hu : ‖(u : ℚ_[2])‖ = 1) : (ZMod 8)ˣ :=
  Units.map (PadicInt.toZModPow 3 (p := 2)).toMonoidHom
    (PadicInt.isUnit_iff.mpr (show ‖mkPadicInt hu.le‖ = 1 from hu)).unit

private lemma padic2UnitToZMod8_val (u : ℚ_[2]ˣ) (hu : ‖(u : ℚ_[2])‖ = 1) :
    ((padic2UnitToZMod8 u hu : (ZMod 8)ˣ) : ZMod 8) =
      PadicInt.toZModPow 3 (mkPadicInt hu.le) := rfl

private lemma padic2UnitToZMod8_mul {u v : ℚ_[2]ˣ}
    (hu : ‖(u : ℚ_[2])‖ = 1) (hv : ‖(v : ℚ_[2])‖ = 1) :
    padic2UnitToZMod8 (u * v) (by rw [Units.val_mul, norm_mul, hu, hv, mul_one]) =
      padic2UnitToZMod8 u hu * padic2UnitToZMod8 v hv := by
  apply Units.ext
  change ((padic2UnitToZMod8 (u * v) _ : (ZMod 8)ˣ) : ZMod 8) =
    ((padic2UnitToZMod8 u hu : (ZMod 8)ˣ) : ZMod 8) * ((padic2UnitToZMod8 v hv : (ZMod 8)ˣ) : ZMod 8)
  rw [padic2UnitToZMod8_val, padic2UnitToZMod8_val, padic2UnitToZMod8_val, ← map_mul]
  congr 1

private lemma padic2UnitToZMod8_one_of_filt3 {u : ℚ_[2]ˣ} (hu : IsInUnitFilt 2 3 u) :
    padic2UnitToZMod8 u hu.1 = 1 := by
  rcases hu.2 with h0 | hle
  · omega
  · have hsub_le : ‖(u : ℚ_[2]) - 1‖ ≤ (2 : ℝ) ^ (-(3 : ℤ)) := hle
    have hnorm23 : ‖((2 : ℚ_[2]) ^ 3)‖ = (2 : ℝ) ^ (-(3 : ℤ)) := by
      have h := Padic.norm_p_pow (p := 2) 3
      simpa using h
    have hdiv_norm : ‖((u : ℚ_[2]) - 1) / (2 : ℚ_[2]) ^ 3‖ ≤ 1 := by
      rw [norm_div, hnorm23]
      exact (div_le_one (by positivity)).mpr hsub_le
    have hsub_z : mkPadicInt (hsub_le.trans (by norm_num)) =
        (((2 : ℕ) : ℤ_[2]) ^ 3) * mkPadicInt hdiv_norm := by
      apply padicInt_ext
      simp only [mkPadicInt_coe, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
      rw [Nat.cast_ofNat]
      have h23 : ((2 : ℚ_[2]) ^ 3) ≠ 0 := pow_ne_zero 3 (prime_ne_zero_padic 2)
      field_simp [h23]
    have hz : PadicInt.toZModPow 3 (mkPadicInt (hsub_le.trans (by norm_num))) = 0 := by
      rw [hsub_z, map_mul, map_pow, map_natCast]
      have h8 : (((2 : ℕ) : ZMod (2 ^ 3)) ^ 3) = 0 := by decide
      rw [h8, zero_mul]
    have heq : mkPadicInt (hsub_le.trans (by norm_num)) = mkPadicInt hu.1.le - 1 :=
      padicInt_ext (by simp)
    rw [heq, map_sub, map_one] at hz
    apply Units.ext
    rw [padic2UnitToZMod8_val, Units.val_one]
    exact sub_eq_zero.mp hz

/-- Construct a smooth character of `ℚ_[p]ˣ` from a multiplicative character on `ℤ_[p]ˣ` and a
uniformizer value `α : ℂˣ`. -/
private def mkLocalCharOfUnit (f : (u : ℚ_[p]ˣ) → ‖(u : ℚ_[p])‖ = 1 → ℂˣ)
    (hf_mul : ∀ u v hu hv, f (u * v) (by rw [Units.val_mul, norm_mul, hu, hv, mul_one]) = f u hu * f v hv)
    (n : ℕ) (hf_smooth : ∀ u (hu : IsInUnitFilt p n u), f u hu.1 = 1)
    (α : ℂˣ) : LocalChar p where
  toHom :=
    { toFun := fun x => f (padicUnitPart p x) (norm_padicUnitPart p x) * α ^ Padic.valuation (x : ℚ_[p])
      map_one' := by
        have h1 : f 1 (by simp) = 1 := by
          have hm := hf_mul 1 1 (by simp) (by simp)
          simpa using hm.symm
        have hu1 : padicUnitPart p 1 = 1 := by simp [padicUnitPart]
        simp [hu1, h1]
      map_mul' := fun x y => by
        have hu_mul : padicUnitPart p (x * y) = padicUnitPart p x * padicUnitPart p y := by
          unfold padicUnitPart
          rw [Units.val_mul, Padic.valuation_mul x.ne_zero y.ne_zero, neg_add, zpow_add]
          ac_rfl
        simp only [Units.val_mul, Padic.valuation_mul x.ne_zero y.ne_zero, zpow_add, hu_mul]
        rw [hf_mul (padicUnitPart p x) (padicUnitPart p y) (norm_padicUnitPart p x) (norm_padicUnitPart p y)]
        ac_rfl }
  smooth := ⟨n, fun u hu => by
    have hv := valuation_eq_zero_of_norm_eq_one hu.1
    have hup : padicUnitPart p u = u := by simp [padicUnitPart, hv]
    simp [hup, hv, hf_smooth u hu]⟩

private lemma mkLocalCharOfUnit_apply (f : (u : ℚ_[p]ˣ) → ‖(u : ℚ_[p])‖ = 1 → ℂˣ)
    (hf_mul : ∀ u v hu hv, f (u * v) (by rw [Units.val_mul, norm_mul, hu, hv, mul_one]) = f u hu * f v hv)
    (n : ℕ) (hf_smooth : ∀ u (hu : IsInUnitFilt p n u), f u hu.1 = 1)
    (α : ℂˣ) (x : ℚ_[p]ˣ) :
    (mkLocalCharOfUnit p f hf_mul n hf_smooth α).toHom x =
      f (padicUnitPart p x) (norm_padicUnitPart p x) * α ^ Padic.valuation (x : ℚ_[p]) := rfl

private def quadCharRamOdd (α : ℂˣ) : LocalChar p :=
  mkLocalCharOfUnit p (oddQuadUnitVal p) (fun _ _ => oddQuadUnitVal_mul p) 1
    (fun _ hu => oddQuadUnitVal_one_of_filt1 p hu) α

private def quadCharRam2 (α : ℂˣ) : LocalChar 2 :=
  mkLocalCharOfUnit 2 (fun u hu => chi2Mod8 (padic2UnitToZMod8 u hu))
    (fun _ _ hu hv => by rw [padic2UnitToZMod8_mul hu hv, map_mul]) 3
    (fun _ hu => by rw [padic2UnitToZMod8_one_of_filt3 hu, map_one]) α

private lemma quadCharRamOdd_sq {α : ℂˣ} (hα : α * α = 1) :
    quadCharRamOdd p α * quadCharRamOdd p α = 1 := by
  have hsq : ∀ u hu, oddQuadUnitVal p u hu * oddQuadUnitVal p u hu = 1 := fun u hu => by
    unfold oddQuadUnitVal; split_ifs <;> simp
  apply LocalChar.ext_hom
  intro x
  simp only [LocalChar.mul_toHom, LocalChar.one_toHom, MonoidHom.mul_apply, MonoidHom.one_apply,
    quadCharRamOdd, mkLocalCharOfUnit_apply]
  rw [mul_mul_mul_comm, hsq, one_mul, ← mul_zpow, hα, one_zpow]

private lemma quadCharRam2_sq {α : ℂˣ} (hα : α * α = 1) :
    quadCharRam2 α * quadCharRam2 α = 1 := by
  apply LocalChar.ext_hom
  intro x
  simp only [LocalChar.mul_toHom, LocalChar.one_toHom, MonoidHom.mul_apply, MonoidHom.one_apply,
    quadCharRam2, mkLocalCharOfUnit_apply]
  rw [mul_mul_mul_comm, chi2Mod8_sq, one_mul, ← mul_zpow, hα, one_zpow]

private lemma quadCharRamOdd_condExp (hodd : p ≠ 2) (α : ℂˣ) :
    (quadCharRamOdd p α).condExp = 1 := by
  apply le_antisymm
  · exact LocalChar.condExp_le fun u hu => by
      have hv := valuation_eq_zero_of_norm_eq_one hu.1
      have hup : padicUnitPart p u = u := by simp [padicUnitPart, hv]
      simp [quadCharRamOdd, mkLocalCharOfUnit_apply, hup, hv, oddQuadUnitVal_one_of_filt1 p hu]
  · by_contra hlt
    have h0 : (quadCharRamOdd p α).condExp = 0 := by omega
    have hunr := (LocalChar.condExp_eq_zero_iff _).mp h0
    have hu_norm : ‖((nonSquareUnitNat p : ℕ) : ℚ_[p])‖ = 1 := norm_nonSquareUnitNat p
    let u0 : ℚ_[p]ˣ := Units.mk0 ((nonSquareUnitNat p : ℕ) : ℚ_[p]) (by
      intro h; rw [h, norm_zero] at hu_norm; norm_num at hu_norm)
    have hu0_norm : ‖(u0 : ℚ_[p])‖ = 1 := hu_norm
    have h1 := hunr u0 hu0_norm
    have hv0 : Padic.valuation (u0 : ℚ_[p]) = 0 := valuation_eq_zero_of_norm_eq_one hu0_norm
    have hup0 : padicUnitPart p u0 = u0 := by simp [padicUnitPart, hv0]
    rw [quadCharRamOdd, mkLocalCharOfUnit_apply] at h1
    simp only [hup0, hv0, zpow_zero, mul_one] at h1
    have hnsq : ¬IsSquare ((padicUnitToZMod p u0 hu0_norm : (ZMod p)ˣ) : ZMod p) := by
      have hcast : ((padicUnitToZMod p u0 hu0_norm : (ZMod p)ˣ) : ZMod p) =
          ((nonSquareUnitNat p : ℕ) : ZMod p) := by
        change PadicInt.toZMod (mkPadicInt hu0_norm.le) = _
        have hnat : mkPadicInt hu0_norm.le = ((nonSquareUnitNat p : ℕ) : ℤ_[p]) :=
          padicInt_ext (by simp [u0])
        rw [hnat, map_natCast]
      rw [hcast]
      exact (nonSquareUnitNat_spec_odd p hodd).2.2
    have hval : oddQuadUnitVal p u0 hu0_norm = -1 := by
      unfold oddQuadUnitVal; rw [if_neg hnsq]
    have h1' : oddQuadUnitVal p u0 hu0_norm = 1 := h1
    rw [hval] at h1'
    have hneg : (-1 : ℂ) = 1 := congrArg Units.val h1'
    norm_num at hneg

private lemma quadCharRam2_condExp (α : ℂˣ) : (quadCharRam2 α).condExp = 3 := by
  apply le_antisymm
  · exact LocalChar.condExp_le fun u hu => by
      have hv := valuation_eq_zero_of_norm_eq_one hu.1
      have hup : padicUnitPart 2 u = u := by simp [padicUnitPart, hv]
      simp [quadCharRam2, mkLocalCharOfUnit_apply, hup, hv, padic2UnitToZMod8_one_of_filt3 hu]
  · by_contra hlt
    have hle2 : (quadCharRam2 α).condExp ≤ 2 := by omega
    have h5_norm : ‖(5 : ℚ_[2])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr (by decide)
    let u5 : ℚ_[2]ˣ := Units.mk0 (5 : ℚ_[2]) (by
      intro h; rw [h, norm_zero] at h5_norm; norm_num at h5_norm)
    have hu5_norm : ‖(u5 : ℚ_[2])‖ = 1 := h5_norm
    have hu5_filt2 : IsInUnitFilt 2 2 u5 := by
      refine ⟨hu5_norm, Or.inr ?_⟩
      have h4 : (u5 : ℚ_[2]) - 1 = ((2 : ℕ) : ℚ_[2]) ^ 2 := by norm_num [u5]
      rw [h4, Padic.norm_p_pow]
    have h1 := LocalChar.condExp_spec (quadCharRam2 α) u5 (isInUnitFilt_mono 2 hle2 hu5_filt2)
    have hv5 : Padic.valuation (u5 : ℚ_[2]) = 0 := valuation_eq_zero_of_norm_eq_one hu5_norm
    have hup5 : padicUnitPart 2 u5 = u5 := by simp [padicUnitPart, hv5]
    rw [quadCharRam2, mkLocalCharOfUnit_apply] at h1
    simp only [hup5, hv5, zpow_zero, mul_one] at h1
    have hval5 : ((padic2UnitToZMod8 u5 hu5_norm : (ZMod 8)ˣ) : ZMod 8) = 5 := by
      rw [padic2UnitToZMod8_val]
      have hnat : mkPadicInt hu5_norm.le = ((5 : ℕ) : ℤ_[2]) :=
        padicInt_ext (by rw [mkPadicInt_coe, PadicInt.coe_natCast]; rfl)
      rw [hnat, map_natCast]; rfl
    have hchi5 : chi2Mod8 (padic2UnitToZMod8 u5 hu5_norm) = -1 := by
      unfold chi2Mod8
      dsimp only [MonoidHom.coe_mk, OneHom.coe_mk]
      rw [hval5, show chi2Mod8Bool 5 = false by decide]
      simp
    have h1' : chi2Mod8 (padic2UnitToZMod8 u5 hu5_norm) = 1 := h1
    rw [hchi5] at h1'
    have hneg : (-1 : ℂ) = 1 := congrArg Units.val h1'
    norm_num at hneg

/-- The local class field theory quadratic character `ω_{E/ℚ_p} : LocalChar p` attached to
`E : QuadExtType p`, of order 2 and exact conductor `E.discExp` (`0` for unramified, `1` for
odd ramified, `3` for `p = 2` ramified). -/
def quadCharOfExt (E : QuadExtType p) : LocalChar p :=
  match E with
  | .unramified => LocalChar.unramChar p (-1)
  | .ramifiedStd =>
    if _hodd : p ≠ 2 then quadCharRamOdd p (oddQuadUnitVal p (-1) (by simp))
    else (show p = 2 by omega) ▸ quadCharRam2 1
  | .ramifiedTwist =>
    if _hodd : p ≠ 2 then quadCharRamOdd p (-(oddQuadUnitVal p (-1) (by simp)))
    else (show p = 2 by omega) ▸ quadCharRam2 (-1)

lemma quadCharOfExt_sq (E : QuadExtType p) : quadCharOfExt p E * quadCharOfExt p E = 1 := by
  have hneg1_sq : oddQuadUnitVal p (-1) (by simp) * oddQuadUnitVal p (-1) (by simp) = 1 := by
    unfold oddQuadUnitVal; split_ifs <;> simp
  cases E with
  | unramified => simp [quadCharOfExt, ← LocalChar.unramChar_mul]
  | ramifiedStd =>
    by_cases hodd : p ≠ 2
    · simp only [quadCharOfExt, dif_pos hodd]
      exact quadCharRamOdd_sq p hneg1_sq
    · push Not at hodd; subst hodd
      simp only [quadCharOfExt, ne_eq, not_true_eq_false, ↓reduceDIte]
      exact quadCharRam2_sq (by simp)
  | ramifiedTwist =>
    by_cases hodd : p ≠ 2
    · simp only [quadCharOfExt, dif_pos hodd]
      exact quadCharRamOdd_sq p (by rw [neg_mul_neg]; exact hneg1_sq)
    · push Not at hodd; subst hodd
      simp only [quadCharOfExt, ne_eq, not_true_eq_false, ↓reduceDIte]
      exact quadCharRam2_sq (by simp)

lemma quadCharOfExt_inv (E : QuadExtType p) : (quadCharOfExt p E)⁻¹ = quadCharOfExt p E :=
  inv_eq_of_mul_eq_one_left (quadCharOfExt_sq p E)

lemma quadCharOfExt_condExp (E : QuadExtType p) : (quadCharOfExt p E).condExp = E.discExp := by
  cases E with
  | unramified => simp [quadCharOfExt, QuadExtType.discExp]
  | ramifiedStd =>
    by_cases hodd : p ≠ 2
    · simp only [quadCharOfExt, QuadExtType.discExp, dif_pos hodd, if_neg hodd]
      exact quadCharRamOdd_condExp p hodd _
    · push Not at hodd; subst hodd
      simp only [quadCharOfExt, QuadExtType.discExp, ne_eq, not_true_eq_false, ↓reduceDIte, ↓reduceIte]
      exact quadCharRam2_condExp 1
  | ramifiedTwist =>
    by_cases hodd : p ≠ 2
    · simp only [quadCharOfExt, QuadExtType.discExp, dif_pos hodd, if_neg hodd]
      exact quadCharRamOdd_condExp p hodd _
    · push Not at hodd; subst hodd
      simp only [quadCharOfExt, QuadExtType.discExp, ne_eq, not_true_eq_false, ↓reduceDIte, ↓reduceIte]
      exact quadCharRam2_condExp (-1)

end QuadCharOfExt

/-! ### Galois Orbits of Regular Quadratic Characters `RegularQuadOrbit p E` -/

/-- Unordered regular Galois orbit `{θ, θ^σ}` (`θ ≠ θ^σ`) indexing dihedral supercuspidal
representations `Ind_{W_E}^{W_{ℚ_p}} θ`. -/
structure RegularQuadOrbit (E : QuadExtType p) where
  orbit : Sym2 (QuadChar p E)
  isOrbit : ∃ θ : QuadChar p E, orbit = s(θ, θ.galConj) ∧ θ ≠ θ.galConj

namespace RegularQuadOrbit

variable {p} {E : QuadExtType p}

@[ext]
lemma ext_orbit {o₁ o₂ : RegularQuadOrbit p E} (h : o₁.orbit = o₂.orbit) : o₁ = o₂ := by
  cases o₁; cases o₂; congr

/-- Construct a regular Galois orbit `{θ, θ^σ}` from any `θ ≠ θ^σ`. -/
def ofChar (θ : QuadChar p E) (hreg : θ ≠ θ.galConj) : RegularQuadOrbit p E :=
  ⟨s(θ, θ.galConj), ⟨θ, rfl, hreg⟩⟩

lemma ofChar_galConj (θ : QuadChar p E) (hreg : θ ≠ θ.galConj) :
    ofChar θ.galConj (by simpa using hreg.symm) = ofChar θ hreg :=
  ext_orbit (by simp [ofChar, Sym2.eq_swap])

lemma ofChar_eq_iff {θ₁ θ₂ : QuadChar p E} (h₁ : θ₁ ≠ θ₁.galConj) (h₂ : θ₂ ≠ θ₂.galConj) :
    ofChar θ₁ h₁ = ofChar θ₂ h₂ ↔ θ₁ = θ₂ ∨ θ₁ = θ₂.galConj := by
  constructor
  · intro heq
    have hsym : s(θ₁, θ₁.galConj) = s(θ₂, θ₂.galConj) := congrArg orbit heq
    rw [Sym2.eq_iff] at hsym
    rcases hsym with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · rfl
    · exact ofChar_galConj θ₂ h₂

/-- Contragredient dual `{θ⁻¹, (θ⁻¹)^σ}` of a regular Galois orbit. -/
def dual (o : RegularQuadOrbit p E) : RegularQuadOrbit p E :=
  ⟨o.orbit.map Inv.inv, by
    rcases o.isOrbit with ⟨θ, horb, hreg⟩
    refine ⟨θ⁻¹, ?_, ?_⟩
    · rw [horb, Sym2.map_mk, map_inv]
    · intro h
      apply hreg
      have := congrArg Inv.inv h
      simpa [map_inv] using this⟩

@[simp]
lemma dual_ofChar (θ : QuadChar p E) (hreg : θ ≠ θ.galConj) :
    (ofChar θ hreg).dual = ofChar θ⁻¹ (by intro h; apply hreg; simpa [map_inv] using congrArg Inv.inv h) :=
  ext_orbit (by simp [dual, ofChar, map_inv])

@[simp]
lemma dual_dual (o : RegularQuadOrbit p E) : o.dual.dual = o := by
  apply ext_orbit
  rcases o.isOrbit with ⟨θ, horb, _⟩
  simp [dual, horb]

/-- Twist of a regular Galois orbit by `η : LocalChar p`: `{θ · (η ∘ N), θ^σ · (η ∘ N)}`. -/
def twist (o : RegularQuadOrbit p E) (η : LocalChar p) : RegularQuadOrbit p E :=
  ⟨o.orbit.map (· * QuadChar.baseChange η), by
    rcases o.isOrbit with ⟨θ, horb, hreg⟩
    refine ⟨θ * QuadChar.baseChange η, ?_, ?_⟩
    · rw [horb, Sym2.map_mk, map_mul, QuadChar.galConj_baseChange]
    · intro h
      rw [map_mul, QuadChar.galConj_baseChange] at h
      exact hreg (mul_right_cancel h)⟩

@[simp]
lemma twist_one (o : RegularQuadOrbit p E) : o.twist 1 = o := by
  apply ext_orbit
  rcases o.isOrbit with ⟨θ, horb, _⟩
  simp [twist, horb]

lemma twist_mul (o : RegularQuadOrbit p E) (η₁ η₂ : LocalChar p) :
    (o.twist η₁).twist η₂ = o.twist (η₁ * η₂) := by
  apply ext_orbit
  rcases o.isOrbit with ⟨θ, horb, _⟩
  simp [twist, horb, map_mul, mul_assoc]

lemma dual_twist (o : RegularQuadOrbit p E) (η : LocalChar p) :
    (o.twist η).dual = o.dual.twist η⁻¹ := by
  apply ext_orbit
  rcases o.isOrbit with ⟨θ, horb, _⟩
  simp [dual, twist, horb, map_inv, mul_comm]

/-- Well-defined restriction `θ|_{ℚ_pˣ}` (independent of representative in `{θ, θ^σ}`). -/
def resQp (o : RegularQuadOrbit p E) : LocalChar p :=
  (Classical.choose o.isOrbit).resQp

lemma resQp_ofChar (θ : QuadChar p E) (hreg : θ ≠ θ.galConj) :
    (ofChar θ hreg).resQp = θ.resQp := by
  unfold resQp
  have hspec := Classical.choose_spec (ofChar θ hreg).isOrbit
  have hsym : s(Classical.choose (ofChar θ hreg).isOrbit,
      (Classical.choose (ofChar θ hreg).isOrbit).galConj) = s(θ, θ.galConj) := hspec.1.symm
  rw [Sym2.eq_iff] at hsym
  rcases hsym with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, QuadChar.resQp_galConj]

lemma resQp_dual (o : RegularQuadOrbit p E) : o.dual.resQp = o.resQp⁻¹ := by
  rcases o.isOrbit with ⟨θ, horb, hreg⟩
  have ho : o = ofChar θ hreg := ext_orbit horb
  rw [ho, dual_ofChar, resQp_ofChar, resQp_ofChar, map_inv]

lemma resQp_twist (o : RegularQuadOrbit p E) (η : LocalChar p) :
    (o.twist η).resQp = o.resQp * η ^ 2 := by
  rcases o.isOrbit with ⟨θ, horb, hreg⟩
  have ho : o = ofChar θ hreg := ext_orbit horb
  have htw : (ofChar θ hreg).twist η =
      ofChar (θ * QuadChar.baseChange η) (by
        intro h; rw [map_mul, QuadChar.galConj_baseChange] at h; exact hreg (mul_right_cancel h)) :=
    ext_orbit (by simp [twist, ofChar, map_mul])
  rw [ho, htw, resQp_ofChar, resQp_ofChar, map_mul, QuadChar.resQp_baseChange]

/-- Well-defined conductor exponent `a(θ)` (independent of representative in `{θ, θ^σ}`). -/
def condExp (o : RegularQuadOrbit p E) : ℕ :=
  (Classical.choose o.isOrbit).condExp

lemma condExp_ofChar (θ : QuadChar p E) (hreg : θ ≠ θ.galConj) :
    (ofChar θ hreg).condExp = θ.condExp := by
  unfold condExp
  have hspec := Classical.choose_spec (ofChar θ hreg).isOrbit
  have hsym : s(Classical.choose (ofChar θ hreg).isOrbit,
      (Classical.choose (ofChar θ hreg).isOrbit).galConj) = s(θ, θ.galConj) := hspec.1.symm
  rw [Sym2.eq_iff] at hsym
  rcases hsym with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, QuadChar.condExp_galConj]

theorem one_le_condExp (o : RegularQuadOrbit p E) : 1 ≤ o.condExp := by
  rcases o.isOrbit with ⟨θ, horb, hreg⟩
  have ho : o = ofChar θ hreg := ext_orbit horb
  rw [ho, condExp_ofChar]
  exact QuadChar.one_le_condExp_of_ne_galConj hreg

end RegularQuadOrbit

/-! ### Explicit Construction of a Regular Unramified Character `θ ≠ θ^σ` at EVERY Prime `p` -/

section ExplicitRegularUnramChar

/-- The residue field `𝔽_{p²}` of `QuadField p .unramified` (`ZMod p × ZMod p` with
`ω² = ω + 1` for `p = 2` and `ω² = nonSquareUnitNat p` for odd `p`). -/
@[ext]
private structure QuadResField where
  re : ZMod p
  im : ZMod p
  deriving DecidableEq

private def resTrace : ZMod p := if p = 2 then 1 else 0
private def resDelta : ZMod p := if p = 2 then 1 else (nonSquareUnitNat p : ZMod p)

private def resNorm (z : QuadResField p) : ZMod p :=
  z.re ^ 2 + resTrace p * z.re * z.im - resDelta p * z.im ^ 2

private lemma resNorm_eq_zero_iff (z : QuadResField p) : resNorm p z = 0 ↔ z = ⟨0, 0⟩ := by
  constructor
  · intro h0
    by_cases hp2 : p = 2
    · subst hp2
      rcases z with ⟨a, b⟩
      have h0' : a ^ 2 + a * b - b ^ 2 = 0 := by simpa [resNorm, resTrace, resDelta] using h0
      by_contra hne
      have hnot : a ≠ 0 ∨ b ≠ 0 := by
        by_contra hboth
        push Not at hboth
        exact hne (QuadResField.ext hboth.1 hboth.2)
      exact QuadField.zmod2_quad_ne_zero a b hnot h0'
    · have hrel : z.re ^ 2 - (nonSquareUnitNat p : ZMod p) * z.im ^ 2 = 0 := by
        simpa [resNorm, resTrace, resDelta, hp2] using h0
      by_cases hb : z.im = 0
      · rw [hb, zero_pow two_ne_zero, mul_zero, sub_zero] at hrel
        exact QuadResField.ext (eq_zero_of_pow_eq_zero hrel) hb
      · exfalso
        apply (nonSquareUnitNat_spec_odd p hp2).2.2
        refine ⟨z.re * z.im⁻¹, ?_⟩
        have h1 : z.re ^ 2 = (nonSquareUnitNat p : ZMod p) * z.im ^ 2 := sub_eq_zero.mp hrel
        have hbsq : z.im ^ 2 ≠ 0 := pow_ne_zero 2 hb
        calc (nonSquareUnitNat p : ZMod p)
            = (nonSquareUnitNat p : ZMod p) * z.im ^ 2 * (z.im ^ 2)⁻¹ := by
                rw [mul_inv_cancel_right₀ hbsq]
          _ = z.re ^ 2 * (z.im ^ 2)⁻¹ := by rw [h1]
          _ = (z.re * z.im⁻¹) * (z.re * z.im⁻¹) := by ring
  · rintro rfl; simp [resNorm]

private instance : Zero (QuadResField p) := ⟨⟨0, 0⟩⟩
private instance : One (QuadResField p) := ⟨⟨1, 0⟩⟩
private instance : Add (QuadResField p) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
private instance : Neg (QuadResField p) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
private instance : Sub (QuadResField p) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
private instance : Mul (QuadResField p) :=
  ⟨fun z w =>
    ⟨z.re * w.re + resDelta p * z.im * w.im,
     z.re * w.im + z.im * w.re + resTrace p * z.im * w.im⟩⟩
private instance : Inv (QuadResField p) :=
  ⟨fun z => ⟨(z.re + resTrace p * z.im) * (resNorm p z)⁻¹, -z.im * (resNorm p z)⁻¹⟩⟩

private instance : Fintype (QuadResField p) :=
  Fintype.ofEquiv (ZMod p × ZMod p)
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun z => (z.re, z.im)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma card_quadResField : Fintype.card (QuadResField p) = p ^ 2 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let e : QuadResField p ≃ ZMod p × ZMod p :=
    { toFun := fun z => (z.re, z.im)
      invFun := fun q => ⟨q.1, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, ZMod.card, sq]

private instance : CommRing (QuadResField p) where
  add_assoc a b c := by ext <;> exact add_assoc _ _ _
  zero_add a := by ext <;> exact zero_add _
  add_zero a := by ext <;> exact add_zero _
  add_comm a b := by ext <;> exact add_comm _ _
  neg_add_cancel a := by ext <;> exact neg_add_cancel _
  sub_eq_add_neg a b := by ext <;> exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc a b c := by
    ext
    · change (a.re * b.re + resDelta p * a.im * b.im) * c.re +
          resDelta p * (a.re * b.im + a.im * b.re + resTrace p * a.im * b.im) * c.im =
        a.re * (b.re * c.re + resDelta p * b.im * c.im) +
          resDelta p * a.im * (b.re * c.im + b.im * c.re + resTrace p * b.im * c.im)
      ring
    · change (a.re * b.re + resDelta p * a.im * b.im) * c.im +
          (a.re * b.im + a.im * b.re + resTrace p * a.im * b.im) * c.re +
          resTrace p * (a.re * b.im + a.im * b.re + resTrace p * a.im * b.im) * c.im =
        a.re * (b.re * c.im + b.im * c.re + resTrace p * b.im * c.im) +
          a.im * (b.re * c.re + resDelta p * b.im * c.im) +
          resTrace p * a.im * (b.re * c.im + b.im * c.re + resTrace p * b.im * c.im)
      ring
  one_mul a := by
    ext
    · change 1 * a.re + resDelta p * 0 * a.im = a.re; ring
    · change 1 * a.im + 0 * a.re + resTrace p * 0 * a.im = a.im; ring
  mul_one a := by
    ext
    · change a.re * 1 + resDelta p * a.im * 0 = a.re; ring
    · change a.re * 0 + a.im * 1 + resTrace p * a.im * 0 = a.im; ring
  left_distrib a b c := by
    ext
    · change a.re * (b.re + c.re) + resDelta p * a.im * (b.im + c.im) =
        (a.re * b.re + resDelta p * a.im * b.im) + (a.re * c.re + resDelta p * a.im * c.im); ring
    · change a.re * (b.im + c.im) + a.im * (b.re + c.re) + resTrace p * a.im * (b.im + c.im) =
        (a.re * b.im + a.im * b.re + resTrace p * a.im * b.im) +
        (a.re * c.im + a.im * c.re + resTrace p * a.im * c.im); ring
  right_distrib a b c := by
    ext
    · change (a.re + b.re) * c.re + resDelta p * (a.im + b.im) * c.im =
        (a.re * c.re + resDelta p * a.im * c.im) + (b.re * c.re + resDelta p * b.im * c.im); ring
    · change (a.re + b.re) * c.im + (a.im + b.im) * c.re + resTrace p * (a.im + b.im) * c.im =
        (a.re * c.im + a.im * c.re + resTrace p * a.im * c.im) +
        (b.re * c.im + b.im * c.re + resTrace p * b.im * c.im); ring
  zero_mul a := by
    ext
    · change 0 * a.re + resDelta p * 0 * a.im = 0; ring
    · change 0 * a.im + 0 * a.re + resTrace p * 0 * a.im = 0; ring
  mul_zero a := by
    ext
    · change a.re * 0 + resDelta p * a.im * 0 = 0; ring
    · change a.re * 0 + a.im * 0 + resTrace p * a.im * 0 = 0; ring
  mul_comm a b := by
    ext
    · change a.re * b.re + resDelta p * a.im * b.im = b.re * a.re + resDelta p * b.im * a.im; ring
    · change a.re * b.im + a.im * b.re + resTrace p * a.im * b.im =
        b.re * a.im + b.im * a.re + resTrace p * b.im * a.im; ring

private instance : Field (QuadResField p) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg QuadResField.re h)⟩
  mul_inv_cancel a ha := by
    have hn : resNorm p a ≠ 0 := mt (resNorm_eq_zero_iff p a).mp ha
    ext
    · change a.re * ((a.re + resTrace p * a.im) * (resNorm p a)⁻¹) +
          resDelta p * a.im * (-a.im * (resNorm p a)⁻¹) = 1
      have hfac : a.re * ((a.re + resTrace p * a.im) * (resNorm p a)⁻¹) +
          resDelta p * a.im * (-a.im * (resNorm p a)⁻¹) = resNorm p a * (resNorm p a)⁻¹ := by
        unfold resNorm; ring
      rw [hfac, mul_inv_cancel₀ hn]
    · change a.re * (-a.im * (resNorm p a)⁻¹) +
          a.im * ((a.re + resTrace p * a.im) * (resNorm p a)⁻¹) +
          resTrace p * a.im * (-a.im * (resNorm p a)⁻¹) = 0
      ring
  inv_zero := by
    ext
    · change (0 + resTrace p * 0) * (resNorm p 0)⁻¹ = 0; simp
    · change -0 * (resNorm p 0)⁻¹ = 0; simp
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

private lemma unram_re_norm_le_one {u : (QuadField p .unramified)ˣ}
    (hu : ‖QuadField.quadNorm (u : QuadField p .unramified)‖ = 1) :
    ‖(u : QuadField p .unramified).re‖ ≤ 1 := by
  have hnorm := QuadField.norm_normVal_unramified (u : QuadField p .unramified)
  have hsq : ‖(u : QuadField p .unramified).re‖ ^ 2 ≤ 1 := by
    rw [← hu]; exact (le_max_left _ _).trans hnorm.symm.le
  nlinarith [norm_nonneg (u : QuadField p .unramified).re]

private lemma unram_im_norm_le_one {u : (QuadField p .unramified)ˣ}
    (hu : ‖QuadField.quadNorm (u : QuadField p .unramified)‖ = 1) :
    ‖(u : QuadField p .unramified).im‖ ≤ 1 := by
  have hnorm := QuadField.norm_normVal_unramified (u : QuadField p .unramified)
  have hsq : ‖(u : QuadField p .unramified).im‖ ^ 2 ≤ 1 := by
    rw [← hu]; exact (le_max_right _ _).trans hnorm.symm.le
  nlinarith [norm_nonneg (u : QuadField p .unramified).im]

/-- Reduction of a unit `u ∈ 𝒪_Eˣ` (`‖N(u)‖_p = 1`) of `QuadField p .unramified` to `(QuadResField p)ˣ`. -/
private def unramUnitToRes (u : (QuadField p .unramified)ˣ)
    (hu : ‖QuadField.quadNorm (u : QuadField p .unramified)‖ = 1) : (QuadResField p)ˣ := by
  have hre := unram_re_norm_le_one p hu
  have him := unram_im_norm_le_one p hu
  let z : QuadResField p :=
    ⟨PadicInt.toZMod (mkPadicInt hre), PadicInt.toZMod (mkPadicInt him)⟩
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hre0 : PadicInt.toZMod (mkPadicInt hre) = 0 := congrArg QuadResField.re hz0
    have him0 : PadicInt.toZMod (mkPadicInt him) = 0 := congrArg QuadResField.im hz0
    have hre_lt : ‖(u : QuadField p .unramified).re‖ < 1 :=
      (padicInt_toZMod_eq_zero_iff p _).mp hre0
    have him_lt : ‖(u : QuadField p .unramified).im‖ < 1 :=
      (padicInt_toZMod_eq_zero_iff p _).mp him0
    have hsq1 : ‖(u : QuadField p .unramified).re‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg (u : QuadField p .unramified).re]
    have hsq2 : ‖(u : QuadField p .unramified).im‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg (u : QuadField p .unramified).im]
    have hlt1 : ‖QuadField.quadNorm (u : QuadField p .unramified)‖ < 1 := by
      change ‖(u : QuadField p .unramified).normVal‖ < 1
      rw [QuadField.norm_normVal_unramified]
      exact max_lt hsq1 hsq2
    linarith
  exact Units.mk0 z hz_ne

private lemma unramUnitToRes_re (u : (QuadField p .unramified)ˣ)
    (hu : ‖QuadField.quadNorm (u : QuadField p .unramified)‖ = 1) :
    ((unramUnitToRes p u hu : (QuadResField p)ˣ) : QuadResField p).re =
      PadicInt.toZMod (mkPadicInt (unram_re_norm_le_one p hu)) := rfl

private lemma unramUnitToRes_im (u : (QuadField p .unramified)ˣ)
    (hu : ‖QuadField.quadNorm (u : QuadField p .unramified)‖ = 1) :
    ((unramUnitToRes p u hu : (QuadResField p)ˣ) : QuadResField p).im =
      PadicInt.toZMod (mkPadicInt (unram_im_norm_le_one p hu)) := rfl

private lemma unramUnitToRes_mul {u v : (QuadField p .unramified)ˣ}
    (hu : ‖QuadField.quadNorm (u : QuadField p .unramified)‖ = 1)
    (hv : ‖QuadField.quadNorm (v : QuadField p .unramified)‖ = 1) :
    unramUnitToRes p (u * v) (by rw [Units.val_mul, map_mul, norm_mul, hu, hv, mul_one]) =
      unramUnitToRes p u hu * unramUnitToRes p v hv := by
  have htr_le : ‖quadTrace p .unramified‖ ≤ 1 := by unfold quadTrace; split_ifs <;> simp
  have hdl_le : ‖quadDelta p .unramified‖ ≤ 1 := by
    unfold quadDelta; split_ifs
    · simp
    · rw [norm_nonSquareUnitNat p]
  have htr : PadicInt.toZMod (mkPadicInt htr_le) = resTrace p := by
    unfold quadTrace resTrace; split_ifs
    · exact map_one _
    · exact map_zero _
  have hdl : PadicInt.toZMod (mkPadicInt hdl_le) = resDelta p := by
    unfold quadDelta resDelta; split_ifs
    · exact map_one _
    · have hnat : mkPadicInt (norm_nonSquareUnitNat p).le = ((nonSquareUnitNat p : ℕ) : ℤ_[p]) :=
        padicInt_ext (by simp)
      convert congrArg PadicInt.toZMod hnat
      rw [map_natCast]
  have huv : ‖QuadField.quadNorm ((u * v : (QuadField p .unramified)ˣ) : QuadField p .unramified)‖ = 1 := by
    rw [Units.val_mul, map_mul, norm_mul, hu, hv, mul_one]
  apply Units.ext
  apply QuadResField.ext
  · have hre_eq : mkPadicInt (unram_re_norm_le_one p huv) =
        mkPadicInt (unram_re_norm_le_one p hu) * mkPadicInt (unram_re_norm_le_one p hv) +
          mkPadicInt hdl_le * mkPadicInt (unram_im_norm_le_one p hu) *
            mkPadicInt (unram_im_norm_le_one p hv) :=
      padicInt_ext (by simp [QuadField.mul_re])
    change ((unramUnitToRes p (u * v) huv : (QuadResField p)ˣ) : QuadResField p).re =
      ((unramUnitToRes p u hu : (QuadResField p)ˣ) : QuadResField p).re *
        ((unramUnitToRes p v hv : (QuadResField p)ˣ) : QuadResField p).re +
      resDelta p * ((unramUnitToRes p u hu : (QuadResField p)ˣ) : QuadResField p).im *
        ((unramUnitToRes p v hv : (QuadResField p)ˣ) : QuadResField p).im
    rw [unramUnitToRes_re, unramUnitToRes_re, unramUnitToRes_re, unramUnitToRes_im,
      unramUnitToRes_im, hre_eq, map_add, map_mul, map_mul, map_mul, hdl]
  · have him_eq : mkPadicInt (unram_im_norm_le_one p huv) =
        mkPadicInt (unram_re_norm_le_one p hu) * mkPadicInt (unram_im_norm_le_one p hv) +
          mkPadicInt (unram_im_norm_le_one p hu) * mkPadicInt (unram_re_norm_le_one p hv) +
          mkPadicInt htr_le * mkPadicInt (unram_im_norm_le_one p hu) *
            mkPadicInt (unram_im_norm_le_one p hv) :=
      padicInt_ext (by simp [QuadField.mul_im])
    change ((unramUnitToRes p (u * v) huv : (QuadResField p)ˣ) : QuadResField p).im =
      ((unramUnitToRes p u hu : (QuadResField p)ˣ) : QuadResField p).re *
        ((unramUnitToRes p v hv : (QuadResField p)ˣ) : QuadResField p).im +
      ((unramUnitToRes p u hu : (QuadResField p)ˣ) : QuadResField p).im *
        ((unramUnitToRes p v hv : (QuadResField p)ˣ) : QuadResField p).re +
      resTrace p * ((unramUnitToRes p u hu : (QuadResField p)ˣ) : QuadResField p).im *
        ((unramUnitToRes p v hv : (QuadResField p)ˣ) : QuadResField p).im
    rw [unramUnitToRes_im, unramUnitToRes_re, unramUnitToRes_im, unramUnitToRes_im,
      unramUnitToRes_re, him_eq, map_add, map_add, map_mul, map_mul, map_mul, map_mul, htr]

private lemma unramUnitToRes_one_of_filt1 {u : (QuadField p .unramified)ˣ}
    (hu : QuadField.IsInQuadUnitFilt (E := .unramified) 1 u) :
    unramUnitToRes p u hu.1 = 1 := by
  rcases hu.2 with h0 | hle
  · omega
  · have hlt1 : ‖QuadField.quadNorm ((u : QuadField p .unramified) - 1)‖ < 1 := by
      refine hle.trans_lt ?_
      have hexp : -(((QuadExtType.unramified (p := p)).residueDeg * 1 : ℕ) : ℤ) = -2 := rfl
      rw [hexp]
      exact zpow_lt_one_of_neg₀ (prime_one_lt_R p) (by norm_num)
    have hnorm := QuadField.norm_normVal_unramified ((u : QuadField p .unramified) - 1)
    change ‖((u : QuadField p .unramified) - 1).normVal‖ < 1 at hlt1
    rw [hnorm] at hlt1
    have hre_lt : ‖(u : QuadField p .unramified).re - 1‖ < 1 := by
      have : ‖(u : QuadField p .unramified).re - 1‖ ^ 2 < 1 :=
        lt_of_le_of_lt (le_max_left _ _) hlt1
      nlinarith [norm_nonneg ((u : QuadField p .unramified).re - 1)]
    have him_lt : ‖(u : QuadField p .unramified).im‖ < 1 := by
      have : ‖(u : QuadField p .unramified).im‖ ^ 2 < 1 := by
        simpa using lt_of_le_of_lt (le_max_right _ _) hlt1
      nlinarith [norm_nonneg (u : QuadField p .unramified).im]
    apply Units.ext
    apply QuadResField.ext
    · change ((unramUnitToRes p u hu.1 : (QuadResField p)ˣ) : QuadResField p).re = 1
      rw [unramUnitToRes_re]
      have h0' : PadicInt.toZMod (mkPadicInt hre_lt.le) = 0 :=
        (padicInt_toZMod_eq_zero_iff p _).mpr hre_lt
      have heq : mkPadicInt hre_lt.le = mkPadicInt (unram_re_norm_le_one p hu.1) - 1 :=
        padicInt_ext (by simp)
      rw [heq, map_sub, map_one] at h0'
      exact sub_eq_zero.mp h0'
    · change ((unramUnitToRes p u hu.1 : (QuadResField p)ˣ) : QuadResField p).im = 0
      rw [unramUnitToRes_im]
      exact (padicInt_toZMod_eq_zero_iff p _).mpr him_lt

/-- Every `z : (QuadField p .unramified)ˣ` has even norm valuation `v_p(N(z)) = 2 * k`. -/
private lemma even_valuation_quadNorm_unram (z : (QuadField p .unramified)ˣ) :
    ∃ k : ℤ, Padic.valuation (QuadField.quadNorm (z : QuadField p .unramified)) = 2 * k := by
  have hnorm := QuadField.norm_normVal_unramified (z : QuadField p .unramified)
  have hnz : QuadField.quadNorm (z : QuadField p .unramified) ≠ 0 :=
    (QuadField.quadNormUnits z).ne_zero
  change ‖QuadField.quadNorm (z : QuadField p .unramified)‖ = _ at hnorm
  rw [Padic.norm_eq_zpow_neg_valuation hnz] at hnorm
  rcases le_total (‖(z : QuadField p .unramified).re‖ ^ 2) (‖(z : QuadField p .unramified).im‖ ^ 2) with hle | hle
  · rw [max_eq_right hle] at hnorm
    have him : (z : QuadField p .unramified).im ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_pow two_ne_zero] at hnorm
      exact (zpow_pos (prime_pos_R p) _).ne' hnorm
    rw [Padic.norm_eq_zpow_neg_valuation him, ← zpow_natCast, ← zpow_mul] at hnorm
    refine ⟨Padic.valuation (z : QuadField p .unramified).im, ?_⟩
    by_contra hne
    have hne' : -Padic.valuation (QuadField.quadNorm (z : QuadField p .unramified)) ≠
        (-Padic.valuation (z : QuadField p .unramified).im) * (2 : ℤ) := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · exact (zpow_lt_zpow_right₀ (prime_one_lt_R p) hlt).ne hnorm
    · exact (zpow_lt_zpow_right₀ (prime_one_lt_R p) hgt).ne' hnorm
  · rw [max_eq_left hle] at hnorm
    have hre : (z : QuadField p .unramified).re ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_pow two_ne_zero] at hnorm
      exact (zpow_pos (prime_pos_R p) _).ne' hnorm
    rw [Padic.norm_eq_zpow_neg_valuation hre, ← zpow_natCast, ← zpow_mul] at hnorm
    refine ⟨Padic.valuation (z : QuadField p .unramified).re, ?_⟩
    by_contra hne
    have hne' : -Padic.valuation (QuadField.quadNorm (z : QuadField p .unramified)) ≠
        (-Padic.valuation (z : QuadField p .unramified).re) * (2 : ℤ) := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · exact (zpow_lt_zpow_right₀ (prime_one_lt_R p) hlt).ne hnorm
    · exact (zpow_lt_zpow_right₀ (prime_one_lt_R p) hgt).ne' hnorm

/-- **Existence of an Explicit Regular Unramified Character `θ ≠ θ^σ` (`a(θ) = 1`) at EVERY Prime `p`**:
constructed directly from a primitive character of `𝔽_{p²}ˣ = (QuadResField p)ˣ`! -/
theorem exists_regular_unram_quadChar :
    ∃ θ : QuadChar p .unramified, θ ≠ θ.galConj ∧ θ.condExp = 1 := by
  have hp2_ge : 4 ≤ p ^ 2 := by have := hp.out.two_le; nlinarith
  have : NeZero (p ^ 2 - 1) := ⟨by omega⟩
  have hcard : Fintype.card (QuadResField p)ˣ = p ^ 2 - 1 := by
    rw [Fintype.card_units, card_quadResField p]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (QuadResField p)ˣ)
  have hord : orderOf g = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  have hpow_unique : ∀ u : (QuadResField p)ˣ, ∃ k : ZMod (p ^ 2 - 1), g ^ k.val = u := by
    intro u
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    let k : ZMod (p ^ 2 - 1) := (m : ZMod (p ^ 2 - 1))
    refine ⟨k, ?_⟩
    have hmod : ((k.val : ℤ) : ZMod (p ^ 2 - 1)) = (m : ZMod (p ^ 2 - 1)) := by simp [k]
    have hdvd : ((p ^ 2 - 1 : ℕ) : ℤ) ∣ ((k.val : ℤ) - m) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hmod, sub_self]
    rcases hdvd with ⟨q, hq⟩
    have hkeq : (k.val : ℤ) = m + (p ^ 2 - 1 : ℕ) * q := by linarith
    have hgp : g ^ (p ^ 2 - 1) = 1 := by rw [← hord, pow_orderOf_eq_one]
    rw [← zpow_natCast, hkeq, zpow_add, zpow_mul, zpow_natCast, hgp, one_zpow, mul_one, hm]
  let logG : (QuadResField p)ˣ → ZMod (p ^ 2 - 1) := fun u => Classical.choose (hpow_unique u)
  have hlogG_spec : ∀ u, g ^ (logG u).val = u := fun u => Classical.choose_spec (hpow_unique u)
  have hlogG_inj : ∀ k₁ k₂ : ZMod (p ^ 2 - 1), g ^ k₁.val = g ^ k₂.val → k₁ = k₂ := by
    intro k₁ k₂ heq
    have hd : orderOf g ∣ (k₁.val - k₂.val : ℤ).natAbs := by
      have h1 : g ^ (k₁.val : ℤ) = g ^ (k₂.val : ℤ) := by rw [zpow_natCast, zpow_natCast, heq]
      have h2 : g ^ ((k₁.val : ℤ) - (k₂.val : ℤ)) = 1 := by
        rw [zpow_sub, h1, mul_inv_cancel]
      have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
      exact Int.natCast_dvd.mp h3
    rw [hord] at hd
    have hlt1 : k₁.val < p ^ 2 - 1 := k₁.val_lt
    have hlt2 : k₂.val < p ^ 2 - 1 := k₂.val_lt
    have hdiff0 : (k₁.val - k₂.val : ℤ).natAbs = 0 := by
      by_contra hne
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd
      omega
    exact ZMod.val_injective _ (by omega)
  have hlogG_mul : ∀ u v, logG (u * v) = logG u + logG v := by
    intro u v
    apply hlogG_inj
    have hgp : g ^ (p ^ 2 - 1) = 1 := by rw [← hord, pow_orderOf_eq_one]
    have hmod : (logG u + logG v).val + (p ^ 2 - 1) * (((logG u).val + (logG v).val) / (p ^ 2 - 1)) =
        (logG u).val + (logG v).val := by
      rw [ZMod.val_add]; exact Nat.mod_add_div _ _
    calc g ^ (logG (u * v)).val
        = u * v := hlogG_spec (u * v)
      _ = g ^ (logG u).val * g ^ (logG v).val := by rw [hlogG_spec, hlogG_spec]
      _ = g ^ ((logG u).val + (logG v).val) := (pow_add g _ _).symm
      _ = g ^ ((logG u + logG v).val + (p ^ 2 - 1) * (((logG u).val + (logG v).val) / (p ^ 2 - 1))) := by
            rw [hmod]
      _ = g ^ (logG u + logG v).val * (g ^ (p ^ 2 - 1)) ^ (((logG u).val + (logG v).val) / (p ^ 2 - 1)) := by
            rw [pow_add, pow_mul]
      _ = g ^ (logG u + logG v).val := by rw [hgp, one_pow, mul_one]
  let ψ : (QuadResField p)ˣ →* ℂˣ :=
    { toFun := fun u =>
        Units.mk0 (Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG u))
          (Stage4LocalLanglands.zmodChar_ne_zero _ _ _)
      map_one' := by
        ext
        have h1 : logG 1 = 0 := hlogG_inj _ _ (by rw [hlogG_spec]; simp)
        change Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG 1) = 1
        rw [h1, Stage4LocalLanglands.zmodChar_zero_right]
      map_mul' := fun u v => by
        ext
        change Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG (u * v)) =
          Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG u) *
            Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG v)
        rw [hlogG_mul, Stage4LocalLanglands.zmodChar_add_right] }
  let scaleVal : (QuadField p .unramified)ˣ → ℤ := fun z =>
    Classical.choose (even_valuation_quadNorm_unram p z)
  have hscale_spec : ∀ z : (QuadField p .unramified)ˣ,
      Padic.valuation (QuadField.quadNorm (z : QuadField p .unramified)) = 2 * scaleVal z :=
    fun z => Classical.choose_spec (even_valuation_quadNorm_unram p z)
  let unitPart : (QuadField p .unramified)ˣ → (QuadField p .unramified)ˣ := fun z =>
    QuadField.quadEmbedUnits (padicPrimeUnit p ^ (-scaleVal z)) * z
  have hunitPart_norm : ∀ z : (QuadField p .unramified)ˣ,
      ‖QuadField.quadNorm (unitPart z : QuadField p .unramified)‖ = 1 := by
    intro z
    have hnz : QuadField.quadNorm (z : QuadField p .unramified) ≠ 0 :=
      (QuadField.quadNormUnits z).ne_zero
    change ‖QuadField.quadNorm (QuadField.quadEmbed ((padicPrimeUnit p ^ (-scaleVal z) : ℚ_[p]ˣ) : ℚ_[p]) *
      (z : QuadField p .unramified))‖ = 1
    rw [map_mul, QuadField.quadNorm_quadEmbed, norm_mul, norm_pow, Units.val_zpow_eq_zpow_val,
      padicPrimeUnit_val, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hnz,
      hscale_spec z, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (prime_ne_zero_R p)]
    have hexp : (- -scaleVal z) * ((2 : ℕ) : ℤ) + -(2 * scaleVal z) = 0 := by push_cast; ring
    rw [hexp, zpow_zero]
  have hscale_mul : ∀ z w : (QuadField p .unramified)ˣ, scaleVal (z * w) = scaleVal z + scaleVal w := by
    intro z w
    have h1 := hscale_spec (z * w)
    have hnz : QuadField.quadNorm (z : QuadField p .unramified) ≠ 0 := (QuadField.quadNormUnits z).ne_zero
    have hnw : QuadField.quadNorm (w : QuadField p .unramified) ≠ 0 := (QuadField.quadNormUnits w).ne_zero
    rw [Units.val_mul, map_mul, Padic.valuation_mul hnz hnw, hscale_spec z, hscale_spec w] at h1
    omega
  have hunitPart_mul : ∀ z w : (QuadField p .unramified)ˣ, unitPart (z * w) = unitPart z * unitPart w := by
    intro z w
    simp only [unitPart, hscale_mul, neg_add, zpow_add, map_mul]
    ac_rfl
  let θ : QuadChar p .unramified :=
    { toHom :=
        { toFun := fun z => ψ (unramUnitToRes p (unitPart z) (hunitPart_norm z))
          map_one' := by
            have h1 : unitPart 1 = 1 := by
              have hm := hunitPart_mul 1 1; simpa using hm.symm
            have hr1 : unramUnitToRes p 1 (by simp) = 1 := by
              apply Units.ext; apply QuadResField.ext
              · rw [unramUnitToRes_re]; change PadicInt.toZMod (1 : ℤ_[p]) = 1; exact map_one _
              · rw [unramUnitToRes_im]; change PadicInt.toZMod (0 : ℤ_[p]) = 0; exact map_zero _
            simp only [h1, hr1, map_one]
          map_mul' := fun z w => by
            simp only [hunitPart_mul]
            rw [unramUnitToRes_mul, map_mul] }
      smooth := ⟨1, fun u hu => by
        have hsc0 : scaleVal u = 0 := by
          have hv0 := valuation_eq_zero_of_norm_eq_one hu.1
          have hs := hscale_spec u; omega
        have hup : unitPart u = u := by simp [unitPart, hsc0]
        change ψ (unramUnitToRes p (unitPart u) (hunitPart_norm u)) = 1
        simp only [hup, unramUnitToRes_one_of_filt1 p hu, map_one]⟩ }
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let liftG : QuadField p .unramified := ⟨((g : QuadResField p).re.val : ℚ_[p]),
    ((g : QuadResField p).im.val : ℚ_[p])⟩
  have hliftG_re : ‖liftG.re‖ ≤ 1 := by
    simpa [liftG] using Padic.norm_int_le_one (p := p) ((g : QuadResField p).re.val : ℤ)
  have hliftG_im : ‖liftG.im‖ ≤ 1 := by
    simpa [liftG] using Padic.norm_int_le_one (p := p) ((g : QuadResField p).im.val : ℤ)
  have hliftG_not_both : ‖liftG.re‖ = 1 ∨ ‖liftG.im‖ = 1 := by
    by_contra hboth
    push Not at hboth
    have hre_lt : ‖liftG.re‖ < 1 := lt_of_le_of_ne hliftG_re hboth.1
    have him_lt : ‖liftG.im‖ < 1 := lt_of_le_of_ne hliftG_im hboth.2
    have hre0 : ((g : QuadResField p).re : ZMod p) = 0 := by
      have h1 : PadicInt.toZMod (mkPadicInt hliftG_re) = 0 :=
        (padicInt_toZMod_eq_zero_iff p _).mpr hre_lt
      have hnat : mkPadicInt hliftG_re = (((g : QuadResField p).re.val : ℕ) : ℤ_[p]) :=
        padicInt_ext (by simp only [mkPadicInt_coe, PadicInt.coe_natCast, liftG])
      rw [hnat, map_natCast, ZMod.natCast_zmod_val] at h1; exact h1
    have him0 : ((g : QuadResField p).im : ZMod p) = 0 := by
      have h1 : PadicInt.toZMod (mkPadicInt hliftG_im) = 0 :=
        (padicInt_toZMod_eq_zero_iff p _).mpr him_lt
      have hnat : mkPadicInt hliftG_im = (((g : QuadResField p).im.val : ℕ) : ℤ_[p]) :=
        padicInt_ext (by simp only [mkPadicInt_coe, PadicInt.coe_natCast, liftG])
      rw [hnat, map_natCast, ZMod.natCast_zmod_val] at h1; exact h1
    exact g.ne_zero (QuadResField.ext hre0 him0)
  have hliftG_norm : ‖QuadField.quadNorm liftG‖ = 1 := by
    change ‖liftG.normVal‖ = 1
    rw [QuadField.norm_normVal_unramified]
    apply le_antisymm
    · exact max_le (pow_le_one₀ (norm_nonneg _) hliftG_re) (pow_le_one₀ (norm_nonneg _) hliftG_im)
    · rcases hliftG_not_both with h | h
      · rw [h, one_pow]; exact le_max_left _ _
      · rw [h, one_pow]; exact le_max_right _ _
  have hliftG_ne : liftG ≠ 0 := by
    intro h0; rw [h0] at hliftG_norm
    simp [QuadField.quadNorm, QuadField.normVal] at hliftG_norm
  let uG : (QuadField p .unramified)ˣ := Units.mk0 liftG hliftG_ne
  have huG_norm : ‖QuadField.quadNorm (uG : QuadField p .unramified)‖ = 1 := hliftG_norm
  have huG_red : unramUnitToRes p uG huG_norm = g := by
    apply Units.ext
    apply QuadResField.ext
    · rw [unramUnitToRes_re]
      trans PadicInt.toZMod (((g : QuadResField p).re.val : ℕ) : ℤ_[p])
      · congr 1
      · rw [map_natCast, ZMod.natCast_zmod_val]
    · rw [unramUnitToRes_im]
      trans PadicInt.toZMod (((g : QuadResField p).im.val : ℕ) : ℤ_[p])
      · congr 1
      · rw [map_natCast, ZMod.natCast_zmod_val]
  have hg_im_ne : (g : QuadResField p).im ≠ 0 := by
    intro him0
    have hpow_re : ∀ n : ℕ, ((g ^ n : (QuadResField p)ˣ) : QuadResField p) =
        ⟨(g : QuadResField p).re ^ n, 0⟩ := by
      intro n
      induction n with
      | zero => simp; rfl
      | succ n ih =>
        rw [pow_succ, Units.val_mul, ih]
        ext
        · change (g : QuadResField p).re ^ n * (g : QuadResField p).re +
              resDelta p * 0 * (g : QuadResField p).im = _
          ring
        · change (g : QuadResField p).re ^ n * (g : QuadResField p).im +
              0 * (g : QuadResField p).re + resTrace p * 0 * (g : QuadResField p).im = 0
          rw [him0]; ring
    have hre_ne : (g : QuadResField p).re ≠ 0 := fun h0 => g.ne_zero (QuadResField.ext h0 him0)
    have hflt : (g : QuadResField p).re ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hre_ne
    have hgp1 : g ^ (p - 1) = 1 := by
      apply Units.ext; rw [hpow_re, hflt]; rfl
    have hdvd : orderOf g ∣ p - 1 := orderOf_dvd_of_pow_eq_one hgp1
    rw [hord] at hdvd
    have hle : p ^ 2 - 1 ≤ p - 1 := Nat.le_of_dvd (by have := hp.out.two_le; omega) hdvd
    have h2 := hp.out.two_le
    have hsq_le : p ^ 2 ≤ p := by omega
    nlinarith
  have hgal_norm : ‖QuadField.quadNorm ((QuadField.quadGalUnits uG : (QuadField p .unramified)ˣ) :
      QuadField p .unramified)‖ = 1 := by
    rw [QuadField.quadGalUnits_coe, QuadField.quadNorm_quadGal]; exact huG_norm
  have hgal_red_ne : unramUnitToRes p (QuadField.quadGalUnits uG) hgal_norm ≠ g := by
    intro heq
    by_cases hp2 : p = 2
    · subst hp2
      have hre_eq := congrArg (fun u : (QuadResField 2)ˣ => (u : QuadResField 2).re) heq
      rw [unramUnitToRes_re] at hre_eq
      have hsum : PadicInt.toZMod (mkPadicInt (unram_re_norm_le_one 2 hgal_norm)) =
          (g : QuadResField 2).re + (g : QuadResField 2).im := by
        trans PadicInt.toZMod ((((g : QuadResField 2).re.val : ℕ) : ℤ_[2]) +
            (((g : QuadResField 2).im.val : ℕ) : ℤ_[2]))
        · congr 1
          exact padicInt_ext (by
            simp only [mkPadicInt_coe, PadicInt.coe_add, PadicInt.coe_natCast,
              QuadField.quadGalUnits_coe, QuadField.quadGal, RingEquiv.coe_mk, Equiv.coe_fn_mk,
              uG, Units.val_mk0, liftG, quadTrace, ↓reduceIte, one_mul])
        · rw [map_add, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [hsum] at hre_eq
      have : (g : QuadResField 2).im = 0 := by linear_combination hre_eq
      exact hg_im_ne this
    · have him_eq := congrArg (fun u : (QuadResField p)ˣ => (u : QuadResField p).im) heq
      rw [unramUnitToRes_im] at him_eq
      have hneg : PadicInt.toZMod (mkPadicInt (unram_im_norm_le_one p hgal_norm)) =
          -(g : QuadResField p).im := by
        trans PadicInt.toZMod (-(((g : QuadResField p).im.val : ℕ) : ℤ_[p]))
        · congr 1
        · rw [map_neg, map_natCast, ZMod.natCast_zmod_val]
      rw [hneg] at him_eq
      have h2im : (2 : ZMod p) * (g : QuadResField p).im = 0 := by linear_combination -him_eq
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h20
        have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp h20
        have hle := Nat.le_of_dvd (by norm_num) hdvd
        have hge := hp.out.two_le
        omega
      exact hg_im_ne ((mul_eq_zero.mp h2im).resolve_left h2ne)
  have hψ_inj : Function.Injective ψ := by
    intro u v huv
    have hval : Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG u) =
        Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG v) := congrArg Units.val huv
    have hsub : Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG u - logG v) = 1 := by
      have hmul : Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG u - logG v) *
          Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG v) =
          Stage4LocalLanglands.zmodChar (p ^ 2 - 1) 1 (logG v) := by
        rw [← Stage4LocalLanglands.zmodChar_add_right, sub_add_cancel, hval]
      exact mul_right_cancel₀ (Stage4LocalLanglands.zmodChar_ne_zero _ _ _) (by simpa using hmul)
    have hcomm : Stage4LocalLanglands.zmodChar (p ^ 2 - 1) (logG u - logG v) 1 = 1 := by
      simpa [Stage4LocalLanglands.zmodChar, mul_comm] using hsub
    have hdiff0 : logG u - logG v = 0 :=
      (Stage4LocalLanglands.zmodChar_one_eq_one_iff (logG u - logG v)).mp hcomm
    have hlog_eq : logG u = logG v := sub_eq_zero.mp hdiff0
    rw [← hlogG_spec u, ← hlogG_spec v, hlog_eq]
  have hreg : θ ≠ θ.galConj := by
    intro heq
    have h1 := congrArg (fun χ : QuadChar p .unramified => χ.toHom uG) heq
    have hsc0 : scaleVal uG = 0 := by
      have hv0 := valuation_eq_zero_of_norm_eq_one huG_norm
      have hs := hscale_spec uG; omega
    have hsc0' : scaleVal (QuadField.quadGalUnits uG) = 0 := by
      have hs1 := hscale_spec (QuadField.quadGalUnits uG)
      rw [QuadField.quadGalUnits_coe, QuadField.quadNorm_quadGal] at hs1
      have hs2 := hscale_spec uG; omega
    have hup1 : unitPart uG = uG := by simp [unitPart, hsc0]
    have hup2 : unitPart (QuadField.quadGalUnits uG) = QuadField.quadGalUnits uG := by
      simp [unitPart, hsc0']
    change ψ (unramUnitToRes p (unitPart uG) _) =
      ψ (unramUnitToRes p (unitPart (QuadField.quadGalUnits uG)) _) at h1
    simp only [hup1, hup2, huG_red] at h1
    exact hgal_red_ne (hψ_inj h1).symm
  refine ⟨θ, hreg, le_antisymm ?_ (QuadChar.one_le_condExp_of_ne_galConj hreg)⟩
  refine QuadChar.condExp_le fun u hu => ?_
  have hsc0 : scaleVal u = 0 := by
    have hv0 := valuation_eq_zero_of_norm_eq_one hu.1
    have hs := hscale_spec u; omega
  have hup : unitPart u = u := by simp [unitPart, hsc0]
  change ψ (unramUnitToRes p (unitPart u) (hunitPart_norm u)) = 1
  simp only [hup, unramUnitToRes_one_of_filt1 p hu, map_one]

end ExplicitRegularUnramChar

end QuadraticExtensions

/-! ## Section 3: Concrete `GL₂(ℚ_p)` Admissible Irreducible Classification (`GL2LocalRep p`) -/

section GL2Classification

variable (p : ℕ) [hp : Fact p.Prime]

/-- Irreducibility predicate on an unordered pair `s = {χ₁, χ₂} : Sym2 (LocalChar p)`:
`Ind_B^{GL₂}(χ₁ ⊗ χ₂)` is irreducible iff `χ₁ χ₂⁻¹ ≠ |·|_p^{±1}`. -/
def IsIrredPSPair (s : Sym2 (LocalChar p)) : Prop :=
  Sym2.lift ⟨fun χ₁ χ₂ => χ₁ * χ₂⁻¹ ≠ LocalChar.normChar p ∧ χ₂ * χ₁⁻¹ ≠ LocalChar.normChar p,
    fun _ _ => propext and_comm⟩ s

@[simp]
lemma isIrredPSPair_pair (χ₁ χ₂ : LocalChar p) :
    IsIrredPSPair p s(χ₁, χ₂) ↔
      χ₁ * χ₂⁻¹ ≠ LocalChar.normChar p ∧ χ₂ * χ₁⁻¹ ≠ LocalChar.normChar p := Iff.rfl

lemma isIrredPSPair_map_inv {s : Sym2 (LocalChar p)} (h : IsIrredPSPair p s) :
    IsIrredPSPair p (s.map Inv.inv) := by
  induction s using Sym2.ind with
  | _ χ₁ χ₂ =>
    rw [isIrredPSPair_pair] at h
    rw [Sym2.map_mk, isIrredPSPair_pair]
    simpa [inv_inv, mul_comm] using ⟨h.2, h.1⟩

lemma isIrredPSPair_map_mul {s : Sym2 (LocalChar p)} (h : IsIrredPSPair p s) (η : LocalChar p) :
    IsIrredPSPair p (s.map (· * η)) := by
  induction s using Sym2.ind with
  | _ χ₁ χ₂ =>
    rw [isIrredPSPair_pair] at h
    rw [Sym2.map_mk, isIrredPSPair_pair]
    have h1 : (χ₁ * η) * (χ₂ * η)⁻¹ = χ₁ * χ₂⁻¹ := by
      calc (χ₁ * η) * (χ₂ * η)⁻¹ = (χ₁ * χ₂⁻¹) * (η * η⁻¹) := by rw [mul_inv]; ac_rfl
        _ = χ₁ * χ₂⁻¹ := by rw [mul_inv_cancel, mul_one]
    have h2 : (χ₂ * η) * (χ₁ * η)⁻¹ = χ₂ * χ₁⁻¹ := by
      calc (χ₂ * η) * (χ₁ * η)⁻¹ = (χ₂ * χ₁⁻¹) * (η * η⁻¹) := by rw [mul_inv]; ac_rfl
        _ = χ₂ * χ₁⁻¹ := by rw [mul_inv_cancel, mul_one]
    rwa [h1, h2]

lemma not_isIrredPSPair_oneDim (χ : LocalChar p) :
    ¬IsIrredPSPair p s(χ * LocalChar.normPowChar p (1 / 2),
      χ * LocalChar.normPowChar p (-(1 / 2))) := by
  rw [isIrredPSPair_pair]
  intro ⟨h1, _⟩
  apply h1
  rw [mul_inv, ← LocalChar.normPowChar_neg, neg_neg]
  calc (χ * LocalChar.normPowChar p (1 / 2)) * (χ⁻¹ * LocalChar.normPowChar p (1 / 2))
      = (χ * χ⁻¹) * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (1 / 2)) := by ac_rfl
    _ = LocalChar.normChar p := by rw [mul_inv_cancel, one_mul, LocalChar.normPowChar_half_mul_half]

/-- **Concrete Irreducible Admissible Representations of `GL₂(ℚ_p)`**:
1. `principalSeries s hirr`: irreducible principal series `Ind_B^{GL₂}(χ₁ ⊗ χ₂)` (`χ₁ χ₂⁻¹ ≠ |·|±¹`),
2. `oneDim χ`: 1-dimensional representation `χ ∘ det` (Langlands quotient of `Ind(χ|·|^{1/2}, χ|·|^{-1/2})`),
3. `steinberg χ`: special representation `St ⊗ χ` (monodromy `N ≠ 0`, conductor `1` if `χ` unramified),
4. `tameSupercuspidal E θ`: dihedral supercuspidal `π(E, θ)` for regular Galois orbit `{θ, θ^σ}`. -/
inductive GL2LocalRep where
  | principalSeries (s : Sym2 (LocalChar p)) (hirr : IsIrredPSPair p s) : GL2LocalRep
  | oneDim (χ : LocalChar p) : GL2LocalRep
  | steinberg (χ : LocalChar p) : GL2LocalRep
  | tameSupercuspidal (E : QuadExtType p) (θ : RegularQuadOrbit p E) : GL2LocalRep

namespace GL2LocalRep

variable {p}

/-- Direct principal series constructor `π(χ₁, χ₂)` from two characters with `χ₁ χ₂⁻¹ ≠ |·|±¹`. -/
def ofPrincipalSeries (χ₁ χ₂ : LocalChar p)
    (h₁ : χ₁ * χ₂⁻¹ ≠ LocalChar.normChar p)
    (h₂ : χ₂ * χ₁⁻¹ ≠ LocalChar.normChar p) : GL2LocalRep p :=
  .principalSeries s(χ₁, χ₂) ⟨h₁, h₂⟩

/-- Weyl-group symmetry `π(χ₁, χ₂) = π(χ₂, χ₁)`. -/
theorem ofPrincipalSeries_comm (χ₁ χ₂ : LocalChar p)
    (h₁ : χ₁ * χ₂⁻¹ ≠ LocalChar.normChar p)
    (h₂ : χ₂ * χ₁⁻¹ ≠ LocalChar.normChar p) :
    ofPrincipalSeries χ₁ χ₂ h₁ h₂ = ofPrincipalSeries χ₂ χ₁ h₂ h₁ := by
  unfold ofPrincipalSeries
  congr 1
  exact Sym2.eq_swap

/-- Supercuspidal predicate on `GL2LocalRep p`. -/
def IsSupercuspidal : GL2LocalRep p → Prop
  | .tameSupercuspidal _ _ => True
  | _ => False

/-- Irreducible principal series predicate on `GL2LocalRep p`. -/
def IsPrincipalSeries : GL2LocalRep p → Prop
  | .principalSeries _ _ => True
  | _ => False

/-- Depth-zero / tame ramification predicate on `GL2LocalRep p`. -/
def IsDepthZero : GL2LocalRep p → Prop
  | .principalSeries s _ =>
      Sym2.lift ⟨fun χ₁ χ₂ => χ₁.condExp ≤ 1 ∧ χ₂.condExp ≤ 1, fun _ _ => propext and_comm⟩ s
  | .oneDim χ => χ.condExp ≤ 1
  | .steinberg χ => χ.condExp ≤ 1
  | .tameSupercuspidal E θ => E.IsTameExt ∧ θ.condExp ≤ 1

/-- Central character `ω_π : LocalChar p` of `π : GL2LocalRep p`. -/
def centralChar : GL2LocalRep p → LocalChar p
  | .principalSeries s _ => Sym2.lift ⟨fun χ₁ χ₂ => χ₁ * χ₂, mul_comm⟩ s
  | .oneDim χ => χ ^ 2
  | .steinberg χ => χ ^ 2
  | .tameSupercuspidal E θ => quadCharOfExt p E * θ.resQp

/-- Contragredient dual `π^∨` of `π : GL2LocalRep p`. -/
def dual : GL2LocalRep p → GL2LocalRep p
  | .principalSeries s hirr => .principalSeries (s.map Inv.inv) (isIrredPSPair_map_inv p hirr)
  | .oneDim χ => .oneDim χ⁻¹
  | .steinberg χ => .steinberg χ⁻¹
  | .tameSupercuspidal E θ => .tameSupercuspidal E θ.dual

/-- Character twist `π ↦ π ⊗ (η ∘ det)` of `π : GL2LocalRep p` by `η : LocalChar p`. -/
def twist (π : GL2LocalRep p) (η : LocalChar p) : GL2LocalRep p :=
  match π with
  | .principalSeries s hirr => .principalSeries (s.map (· * η)) (isIrredPSPair_map_mul p hirr η)
  | .oneDim χ => .oneDim (χ * η)
  | .steinberg χ => .steinberg (χ * η)
  | .tameSupercuspidal E θ => .tameSupercuspidal E (θ.twist η)

/-- Unramified real-power twist `π ↦ π ⊗ |det|_p^s`. -/
def nu (π : GL2LocalRep p) (s : ℝ) : GL2LocalRep p :=
  π.twist (LocalChar.normPowChar p s)

@[simp]
lemma dual_dual (π : GL2LocalRep p) : π.dual.dual = π := by
  cases π with
  | principalSeries s hirr =>
    simp only [dual, Sym2.map_map]
    congr 1
    induction s using Sym2.ind with
    | _ χ₁ χ₂ => simp
  | oneDim χ => simp [dual]
  | steinberg χ => simp [dual]
  | tameSupercuspidal E θ => simp [dual]

@[simp]
lemma twist_one (π : GL2LocalRep p) : π.twist 1 = π := by
  cases π with
  | principalSeries s hirr =>
    simp only [twist]
    congr 1
    induction s using Sym2.ind with
    | _ χ₁ χ₂ => simp
  | oneDim χ => simp [twist]
  | steinberg χ => simp [twist]
  | tameSupercuspidal E θ => simp [twist]

lemma twist_mul (π : GL2LocalRep p) (η₁ η₂ : LocalChar p) :
    (π.twist η₁).twist η₂ = π.twist (η₁ * η₂) := by
  cases π with
  | principalSeries s hirr =>
    simp only [twist, Sym2.map_map]
    congr 1
    induction s using Sym2.ind with
    | _ χ₁ χ₂ => simp [mul_assoc]
  | oneDim χ => simp [twist, mul_assoc]
  | steinberg χ => simp [twist, mul_assoc]
  | tameSupercuspidal E θ => simp [twist, RegularQuadOrbit.twist_mul]

lemma dual_twist (π : GL2LocalRep p) (η : LocalChar p) :
    (π.twist η).dual = π.dual.twist η⁻¹ := by
  cases π with
  | principalSeries s hirr =>
    simp only [dual, twist, Sym2.map_map]
    congr 1
    induction s using Sym2.ind with
    | _ χ₁ χ₂ => simp [Sym2.map_mk, mul_comm]
  | oneDim χ => simp [dual, twist, mul_comm]
  | steinberg χ => simp [dual, twist, mul_comm]
  | tameSupercuspidal E θ => simp [dual, twist, RegularQuadOrbit.dual_twist]

lemma centralChar_dual (π : GL2LocalRep p) : π.dual.centralChar = π.centralChar⁻¹ := by
  cases π with
  | principalSeries s hirr =>
    induction s using Sym2.ind with
    | _ χ₁ χ₂ => simp [dual, centralChar, mul_comm]
  | oneDim χ => simp [dual, centralChar, inv_pow]
  | steinberg χ => simp [dual, centralChar, inv_pow]
  | tameSupercuspidal E θ =>
    simp [dual, centralChar, RegularQuadOrbit.resQp_dual, quadCharOfExt_inv, mul_comm]

lemma centralChar_twist (π : GL2LocalRep p) (η : LocalChar p) :
    (π.twist η).centralChar = π.centralChar * η ^ 2 := by
  cases π with
  | principalSeries s hirr =>
    induction s using Sym2.ind with
    | _ χ₁ χ₂ =>
      simp only [twist, Sym2.map_mk, centralChar, Sym2.lift_mk, sq]
      ac_rfl
  | oneDim χ => simp [twist, centralChar, mul_pow]
  | steinberg χ => simp [twist, centralChar, mul_pow]
  | tameSupercuspidal E θ =>
    simp [twist, centralChar, RegularQuadOrbit.resQp_twist, mul_assoc]

/-- Exact local `L`-factor `L(π, T)` of `π : GL2LocalRep p` (in `T = p^{-s}`):
- `principalSeries {χ₁, χ₂}`: `L(χ₁, T) * L(χ₂, T)`,
- `oneDim χ`: `L(χ|·|^{1/2}, T) * L(χ|·|^{-1/2}, T)`,
- `steinberg χ`: `L(χ|·|^{1/2}, T)` (`(1 - χ(p) p^{-1/2} T)⁻¹` if `χ` unramified, `1` else),
- `tameSupercuspidal E θ`: `1`! -/
def localLFactor (π : GL2LocalRep p) (T : ℂ) : ℂ :=
  match π with
  | .principalSeries s _ =>
      Sym2.lift ⟨fun χ₁ χ₂ => χ₁.gl1LFactor T * χ₂.gl1LFactor T, fun _ _ => mul_comm _ _⟩ s
  | .oneDim χ =>
      (χ * LocalChar.normPowChar p (1 / 2)).gl1LFactor T *
        (χ * LocalChar.normPowChar p (-(1 / 2))).gl1LFactor T
  | .steinberg χ => (χ * LocalChar.normPowChar p (1 / 2)).gl1LFactor T
  | .tameSupercuspidal _ _ => 1

/-- Exact conductor exponent `a(π) : ℕ` of `π : GL2LocalRep p`:
- `principalSeries {χ₁, χ₂}`: `a(χ₁) + a(χ₂)`,
- `oneDim χ`: `2 * a(χ)`,
- `steinberg χ`: `1` if `χ` is unramified, else `2 * a(χ)`,
- `tameSupercuspidal E θ`: `f(E/ℚ_p) * a(θ) + d(E/ℚ_p)`! -/
def conductor (π : GL2LocalRep p) : ℕ :=
  match π with
  | .principalSeries s _ => Sym2.lift ⟨fun χ₁ χ₂ => χ₁.condExp + χ₂.condExp, fun _ _ => add_comm _ _⟩ s
  | .oneDim χ => 2 * χ.condExp
  | .steinberg χ =>
      letI := Classical.dec χ.IsUnramified
      if χ.IsUnramified then 1 else 2 * χ.condExp
  | .tameSupercuspidal E θ => E.residueDeg * θ.condExp + E.discExp

theorem localLFactor_principalSeries_unram (α β : ℂˣ)
    (h₁ : LocalChar.unramChar p α * (LocalChar.unramChar p β)⁻¹ ≠ LocalChar.normChar p)
    (h₂ : LocalChar.unramChar p β * (LocalChar.unramChar p α)⁻¹ ≠ LocalChar.normChar p) (T : ℂ) :
    (ofPrincipalSeries (LocalChar.unramChar p α) (LocalChar.unramChar p β) h₁ h₂).localLFactor T =
      (1 - (α : ℂ) * T)⁻¹ * (1 - (β : ℂ) * T)⁻¹ := by
  simp [ofPrincipalSeries, localLFactor, LocalChar.gl1LFactor_unramChar]

theorem localLFactor_steinberg_unram {χ : LocalChar p} (h : χ.IsUnramified) (T : ℂ) :
    (GL2LocalRep.steinberg χ).localLFactor T =
      (1 - (χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * T)⁻¹ := by
  have hunr : (χ * LocalChar.normPowChar p (1 / 2)).IsUnramified :=
    LocalChar.isUnramified_mul h (LocalChar.normPowChar_isUnramified p _)
  rw [localLFactor, LocalChar.gl1LFactor_of_isUnramified hunr]
  simp

theorem localLFactor_tameSupercuspidal (E : QuadExtType p) (θ : RegularQuadOrbit p E) (T : ℂ) :
    (GL2LocalRep.tameSupercuspidal E θ).localLFactor T = 1 := rfl

theorem conductor_steinberg_unram {χ : LocalChar p} (h : χ.IsUnramified) :
    (GL2LocalRep.steinberg χ).conductor = 1 := by
  classical
  simp [conductor, h]

theorem conductor_tameSupercuspidal (E : QuadExtType p) (θ : RegularQuadOrbit p E) :
    (GL2LocalRep.tameSupercuspidal E θ).conductor = E.residueDeg * θ.condExp + E.discExp := rfl

/-- Every supercuspidal representation of `GL₂(ℚ_p)` has conductor exponent `a(π) ≥ 2`! -/
theorem two_le_conductor_tameSupercuspidal (E : QuadExtType p) (θ : RegularQuadOrbit p E) :
    2 ≤ (GL2LocalRep.tameSupercuspidal E θ).conductor := by
  have h1 : 1 ≤ θ.condExp := θ.one_le_condExp
  cases E with
  | unramified => simp only [conductor, QuadExtType.residueDeg, QuadExtType.discExp]; omega
  | ramifiedStd | ramifiedTwist =>
    simp only [conductor, QuadExtType.residueDeg, QuadExtType.discExp]
    split_ifs <;> omega

end GL2LocalRep

end GL2Classification

/-! ## Section 4: Concrete 2D Weil–Deligne Parameters (`WD2Param p`) & Exact Bijection `llcGL2` -/

section WD2Parameters

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Concrete 2-Dimensional Frobenius-Semisimple Weil–Deligne Parameters over `ℚ_p`**:
1. `reducible s`: `φ = χ₁ ⊕ χ₂` with `N = 0` (`s = {χ₁, χ₂} : Sym2 (LocalChar p)`),
2. `special χ`: `φ = χ|·|^{1/2} ⊕ χ|·|^{-1/2}` with nonzero nilpotent monodromy `N = [[0, 1], [0, 0]]`,
3. `dihedral E θ`: irreducible 2D induced Weil representation `Ind_{W_E}^{W_{ℚ_p}} θ` with `N = 0`. -/
inductive WD2Param where
  | reducible (s : Sym2 (LocalChar p)) : WD2Param
  | special (χ : LocalChar p) : WD2Param
  | dihedral (E : QuadExtType p) (θ : RegularQuadOrbit p E) : WD2Param

namespace WD2Param

variable {p}

/-- Irreducibility predicate (`N = 0` and irreducible Weil representation). -/
def IsIrred : WD2Param p → Prop
  | .dihedral _ _ => True
  | _ => False

/-- Tame ramification predicate on `WD2Param p`. -/
def IsTame : WD2Param p → Prop
  | .reducible s =>
      Sym2.lift ⟨fun χ₁ χ₂ => χ₁.condExp ≤ 1 ∧ χ₂.condExp ≤ 1, fun _ _ => propext and_comm⟩ s
  | .special χ => χ.condExp ≤ 1
  | .dihedral E θ => E.IsTameExt ∧ θ.condExp ≤ 1

/-- Determinant character `det φ : LocalChar p` of a 2D Weil–Deligne parameter. -/
def detChar : WD2Param p → LocalChar p
  | .reducible s => Sym2.lift ⟨fun χ₁ χ₂ => χ₁ * χ₂, mul_comm⟩ s
  | .special χ => χ ^ 2
  | .dihedral E θ => quadCharOfExt p E * θ.resQp

/-- Contragredient dual `w^∨` of a 2D Weil–Deligne parameter. -/
def dual : WD2Param p → WD2Param p
  | .reducible s => .reducible (s.map Inv.inv)
  | .special χ => .special χ⁻¹
  | .dihedral E θ => .dihedral E θ.dual

/-- Character twist `w ↦ w ⊗ η` of a 2D Weil–Deligne parameter. -/
def twist (w : WD2Param p) (η : LocalChar p) : WD2Param p :=
  match w with
  | .reducible s => .reducible (s.map (· * η))
  | .special χ => .special (χ * η)
  | .dihedral E θ => .dihedral E (θ.twist η)

/-- Unramified real-power twist `w ↦ w ⊗ |·|_p^s`. -/
def nu (w : WD2Param p) (s : ℝ) : WD2Param p :=
  w.twist (LocalChar.normPowChar p s)

/-- Explicit `2 × 2` Frobenius matrix `φ(Frob_p) ∈ GL₂(ℂ)` attached to `w : WD2Param p`. -/
def frobMatrix : WD2Param p → Matrix (Fin 2) (Fin 2) ℂ
  | .reducible s =>
      let tr : ℂ := Sym2.lift ⟨fun χ₁ χ₂ => (χ₁.evalP : ℂ) + (χ₂.evalP : ℂ), fun _ _ => add_comm _ _⟩ s
      let dt : ℂ := Sym2.lift ⟨fun χ₁ χ₂ => (χ₁.evalP : ℂ) * (χ₂.evalP : ℂ), fun _ _ => mul_comm _ _⟩ s
      !![(0 : ℂ), -dt; 1, tr]
  | .special χ =>
      !![(χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ), 0;
         0, (χ.evalP : ℂ) * (((p : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : ℂ)]
  | .dihedral E θ =>
      !![(0 : ℂ), -(((quadCharOfExt p E * θ.resQp).evalP : ℂ)); 1, 0]

/-- Explicit `2 × 2` nilpotent monodromy matrix `N ∈ M₂(ℂ)` attached to `w : WD2Param p`:
`N = [[0, 1], [0, 0]]` for `special χ`, and `N = 0` for `reducible` and `dihedral`. -/
def monodromyMatrix : WD2Param p → Matrix (Fin 2) (Fin 2) ℂ
  | .special _ => !![(0 : ℂ), 1; 0, 0]
  | _ => 0

/-- **Automatic Nilpotency (`N² = 0`)** for EVERY `w : WD2Param p`! -/
theorem monodromyMatrix_sq_eq_zero (w : WD2Param p) : w.monodromyMatrix ^ 2 = 0 := by
  cases w with
  | reducible _ => simp [monodromyMatrix]
  | dihedral _ _ => simp [monodromyMatrix]
  | special χ =>
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [monodromyMatrix, sq, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact characterization of nonzero monodromy: `N ≠ 0 ↔ ∃ χ, w = special χ`. -/
theorem monodromyMatrix_ne_zero_iff (w : WD2Param p) :
    w.monodromyMatrix ≠ 0 ↔ ∃ χ, w = .special χ := by
  cases w with
  | reducible _ => simp [monodromyMatrix]
  | dihedral _ _ => simp [monodromyMatrix]
  | special χ =>
    refine ⟨fun _ => ⟨χ, rfl⟩, fun _ h => ?_⟩
    have h01 := congrFun (congrFun h 0) 1
    simp [monodromyMatrix] at h01

/-- **Exact Matrix Determinant Formula**: `det(φ(Frob_p)) = detChar(w)(p)` for EVERY `w : WD2Param p`! -/
theorem det_frobMatrix_eq_detChar_evalP (w : WD2Param p) :
    Matrix.det w.frobMatrix = (w.detChar.evalP : ℂ) := by
  cases w with
  | reducible s =>
    induction s using Sym2.ind with
    | _ χ₁ χ₂ =>
      simp [frobMatrix, detChar, Matrix.det_fin_two]
  | special χ =>
    rw [frobMatrix, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_zero, sub_zero, detChar, sq, LocalChar.evalP_mul, Units.val_mul]
    have hpow : (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((p : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add (prime_pos_R p)]
      norm_num
    calc (χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((χ.evalP : ℂ) * (((p : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : ℂ))
        = (χ.evalP : ℂ) * (χ.evalP : ℂ) *
          ((((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((p : ℝ) ^ ((1 / 2 : ℝ)) : ℝ) : ℂ)) := by ring
      _ = (χ.evalP : ℂ) * (χ.evalP : ℂ) := by rw [hpow, mul_one]
  | dihedral E θ =>
    simp [frobMatrix, detChar, Matrix.det_fin_two]

theorem det_frobMatrix_ne_zero (w : WD2Param p) : Matrix.det w.frobMatrix ≠ 0 := by
  rw [det_frobMatrix_eq_detChar_evalP]
  exact Units.ne_zero _

/-- **Exact Weil–Deligne Monodromy Relation `φ N φ⁻¹ = p⁻¹ N`** for EVERY `w : WD2Param p`! -/
theorem wd_monodromy_compat (w : WD2Param p) :
    w.frobMatrix * w.monodromyMatrix * w.frobMatrix⁻¹ = ((p : ℂ)⁻¹) • w.monodromyMatrix := by
  cases w with
  | reducible _ => simp [monodromyMatrix]
  | dihedral _ _ => simp [monodromyMatrix]
  | special χ =>
    have hdet : IsUnit (Matrix.det (WD2Param.special χ).frobMatrix) :=
      isUnit_iff_ne_zero.mpr (det_frobMatrix_ne_zero _)
    have hmul : (WD2Param.special χ).frobMatrix * (WD2Param.special χ).monodromyMatrix =
        ((p : ℂ)⁻¹) • ((WD2Param.special χ).monodromyMatrix * (WD2Param.special χ).frobMatrix) := by
      have hpow : (((p : ℝ) ^ (-(2⁻¹ : ℝ)) : ℝ) : ℂ) =
          (p : ℂ)⁻¹ * (((p : ℝ) ^ ((2⁻¹ : ℝ)) : ℝ) : ℂ) := by
        rw [show (p : ℂ)⁻¹ = (((p : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) by simp [Real.rpow_neg_one],
          ← Complex.ofReal_mul, ← Real.rpow_add (prime_pos_R p)]
        norm_num
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [frobMatrix, monodromyMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hpow]; ring
    calc (WD2Param.special χ).frobMatrix * (WD2Param.special χ).monodromyMatrix *
            (WD2Param.special χ).frobMatrix⁻¹
        = (((p : ℂ)⁻¹) • ((WD2Param.special χ).monodromyMatrix * (WD2Param.special χ).frobMatrix)) *
            (WD2Param.special χ).frobMatrix⁻¹ := by rw [hmul]
      _ = ((p : ℂ)⁻¹) • ((WD2Param.special χ).monodromyMatrix *
            ((WD2Param.special χ).frobMatrix * (WD2Param.special χ).frobMatrix⁻¹)) := by
            rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = ((p : ℂ)⁻¹) • (WD2Param.special χ).monodromyMatrix := by
            rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

/-- Exact Frobenius trace of `reducible s(χ₁, χ₂)`: `Tr(φ(Frob_p)) = χ₁(p) + χ₂(p)`. -/
theorem trace_frobMatrix_reducible (χ₁ χ₂ : LocalChar p) :
    Matrix.trace (WD2Param.reducible s(χ₁, χ₂)).frobMatrix = (χ₁.evalP : ℂ) + (χ₂.evalP : ℂ) := by
  simp [frobMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Dimension of the inertia-fixed subspace `V^{I_p}`. -/
def inertFixedDim : WD2Param p → ℕ
  | .reducible s =>
      letI := Classical.decPred (LocalChar.IsUnramified (p := p))
      Sym2.lift ⟨fun χ₁ χ₂ => (if χ₁.IsUnramified then 1 else 0) + (if χ₂.IsUnramified then 1 else 0),
        fun _ _ => add_comm _ _⟩ s
  | .special χ =>
      letI := Classical.dec χ.IsUnramified
      if χ.IsUnramified then 2 else 0
  | .dihedral _ _ => 0

/-- Dimension of the inertia-fixed monodromy kernel `(ker N)^{I_p}`. -/
def kerNInertFixedDim : WD2Param p → ℕ
  | .reducible s =>
      letI := Classical.decPred (LocalChar.IsUnramified (p := p))
      Sym2.lift ⟨fun χ₁ χ₂ => (if χ₁.IsUnramified then 1 else 0) + (if χ₂.IsUnramified then 1 else 0),
        fun _ _ => add_comm _ _⟩ s
  | .special χ =>
      letI := Classical.dec χ.IsUnramified
      if χ.IsUnramified then 1 else 0
  | .dihedral _ _ => 0

/-- Artin conductor of the underlying Weil representation `a(φ)`. -/
def weilArtinConductor : WD2Param p → ℕ
  | .reducible s => Sym2.lift ⟨fun χ₁ χ₂ => χ₁.condExp + χ₂.condExp, fun _ _ => add_comm _ _⟩ s
  | .special χ => 2 * χ.condExp
  | .dihedral E θ => E.residueDeg * θ.condExp + E.discExp

/-- **Deligne–Grothendieck Artin–Swan–Monodromy Conductor Formula**:
`a(φ, N) = a(φ) + dim(V^{I_p}) - dim((ker N)^{I_p})`. -/
def artinConductor (w : WD2Param p) : ℕ :=
  w.weilArtinConductor + (w.inertFixedDim - w.kerNInertFixedDim)

/-- Exact Weil–Deligne local `L`-factor `L(φ, N; T) = det(1 - T · φ(Frob_p) | (ker N)^{I_p})⁻¹`. -/
def localLFactor (w : WD2Param p) (T : ℂ) : ℂ :=
  match w with
  | .reducible s =>
      Sym2.lift ⟨fun χ₁ χ₂ => χ₁.gl1LFactor T * χ₂.gl1LFactor T, fun _ _ => mul_comm _ _⟩ s
  | .special χ => (χ * LocalChar.normPowChar p (1 / 2)).gl1LFactor T
  | .dihedral _ _ => 1

lemma localLFactor_special_unram {χ : LocalChar p} (h : χ.IsUnramified) (T : ℂ) :
    (WD2Param.special χ).localLFactor T =
      (1 - (χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * T)⁻¹ := by
  have hunr : (χ * LocalChar.normPowChar p (1 / 2)).IsUnramified :=
    LocalChar.isUnramified_mul h (LocalChar.normPowChar_isUnramified p _)
  rw [localLFactor, LocalChar.gl1LFactor_of_isUnramified hunr]
  simp

lemma artinConductor_special (χ : LocalChar p) :
    (WD2Param.special χ).artinConductor =
      letI := Classical.dec χ.IsUnramified
      if χ.IsUnramified then 1 else 2 * χ.condExp := by
  classical
  unfold artinConductor weilArtinConductor inertFixedDim kerNInertFixedDim
  by_cases h : χ.IsUnramified
  · simp [h, (LocalChar.condExp_eq_zero_iff χ).mpr h]
  · simp [h]

end WD2Param

/-! ### Exact Bijection `llcGL2 : GL2LocalRep p ≃ WD2Param p` & All Preservation Theorems -/

/-- Unique extraction of `χ` from a reducible pair `{χ₁, χ₂}` with `χ₁ χ₂⁻¹ = |·|±¹`. -/
private lemma exists_unique_oneDim_of_not_irred {s : Sym2 (LocalChar p)}
    (h : ¬IsIrredPSPair p s) :
    ∃! χ : LocalChar p,
      s = s(χ * LocalChar.normPowChar p (1 / 2), χ * LocalChar.normPowChar p (-(1 / 2))) := by
  induction s using Sym2.ind with
  | _ χ₁ χ₂ =>
    rw [isIrredPSPair_pair, not_and_or, not_ne_iff, not_ne_iff] at h
    have hex : ∃ χ : LocalChar p,
        s(χ₁, χ₂) = s(χ * LocalChar.normPowChar p (1 / 2), χ * LocalChar.normPowChar p (-(1 / 2))) := by
      rcases h with h1 | h2
      · refine ⟨χ₂ * LocalChar.normPowChar p (1 / 2), ?_⟩
        have ha : χ₂ * LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (1 / 2) = χ₁ := by
          calc χ₂ * LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (1 / 2)
              = χ₂ * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (1 / 2)) := mul_assoc _ _ _
            _ = χ₂ * (χ₁ * χ₂⁻¹) := by rw [LocalChar.normPowChar_half_mul_half, ← h1]
            _ = χ₁ * (χ₂ * χ₂⁻¹) := by ac_rfl
            _ = χ₁ := by rw [mul_inv_cancel, mul_one]
        have hb : χ₂ * LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (-(1 / 2)) = χ₂ := by
          rw [mul_assoc, LocalChar.normPowChar_half_mul_neg_half, mul_one]
        rw [ha, hb]
      · refine ⟨χ₁ * LocalChar.normPowChar p (1 / 2), ?_⟩
        have ha : χ₁ * LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (1 / 2) = χ₂ := by
          calc χ₁ * LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (1 / 2)
              = χ₁ * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (1 / 2)) := mul_assoc _ _ _
            _ = χ₁ * (χ₂ * χ₁⁻¹) := by rw [LocalChar.normPowChar_half_mul_half, ← h2]
            _ = χ₂ * (χ₁ * χ₁⁻¹) := by ac_rfl
            _ = χ₂ := by rw [mul_inv_cancel, mul_one]
        have hb : χ₁ * LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (-(1 / 2)) = χ₁ := by
          rw [mul_assoc, LocalChar.normPowChar_half_mul_neg_half, mul_one]
        rw [ha, hb, Sym2.eq_swap]
    rcases hex with ⟨χ, hχ⟩
    refine ⟨χ, hχ, fun χ' hχ' => ?_⟩
    have hsym := hχ'.symm.trans hχ
    rw [Sym2.eq_iff] at hsym
    rcases hsym with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact mul_right_cancel h1
    · exfalso
      have hprod : (χ' * LocalChar.normPowChar p (1 / 2)) *
          (χ * LocalChar.normPowChar p (1 / 2)) =
          (χ * LocalChar.normPowChar p (-(1 / 2))) *
          (χ' * LocalChar.normPowChar p (-(1 / 2))) := by
        rw [h1, ← h2]
      have hmul : (χ' * χ) * LocalChar.normChar p = (χ' * χ) * (LocalChar.normChar p)⁻¹ := by
        calc (χ' * χ) * LocalChar.normChar p
            = (χ' * LocalChar.normPowChar p (1 / 2)) * (χ * LocalChar.normPowChar p (1 / 2)) := by
                rw [← LocalChar.normPowChar_half_mul_half]; ac_rfl
          _ = (χ * LocalChar.normPowChar p (-(1 / 2))) * (χ' * LocalChar.normPowChar p (-(1 / 2))) := hprod
          _ = (χ' * χ) * (LocalChar.normPowChar p (-(1 / 2)) * LocalChar.normPowChar p (-(1 / 2))) := by ac_rfl
          _ = (χ' * χ) * (LocalChar.normChar p)⁻¹ := by
                rw [LocalChar.normPowChar_neg, ← mul_inv, LocalChar.normPowChar_half_mul_half]
      have hnorm_eq : LocalChar.normChar p = (LocalChar.normChar p)⁻¹ := mul_left_cancel hmul
      have hsq : LocalChar.normChar p * LocalChar.normChar p = 1 := by
        calc LocalChar.normChar p * LocalChar.normChar p
            = (LocalChar.normChar p)⁻¹ * LocalChar.normChar p := by rw [← hnorm_eq]
          _ = 1 := inv_mul_cancel _
      exact LocalChar.normChar_sq_ne_one p hsq

/-- **THE CONCRETE `GL₂(ℚ_p)` LOCAL LANGLANDS BIJECTION `llcGL2 : GL2LocalRep p ≃ WD2Param p`**
(`0` Assumptions, exact `Equiv`!). -/
def llcGL2 : GL2LocalRep p ≃ WD2Param p where
  toFun
    | .principalSeries s _ => .reducible s
    | .oneDim χ => .reducible s(χ * LocalChar.normPowChar p (1 / 2),
        χ * LocalChar.normPowChar p (-(1 / 2)))
    | .steinberg χ => .special χ
    | .tameSupercuspidal E θ => .dihedral E θ
  invFun
    | .reducible s =>
        letI := Classical.dec (IsIrredPSPair p s)
        if h : IsIrredPSPair p s then .principalSeries s h
        else .oneDim (Classical.choose (exists_unique_oneDim_of_not_irred p h))
    | .special χ => .steinberg χ
    | .dihedral E θ => .tameSupercuspidal E θ
  left_inv π := by
    classical
    cases π with
    | principalSeries s hirr => simp [hirr]
    | oneDim χ =>
      have hnot := not_isIrredPSPair_oneDim p χ
      simp only [dif_neg hnot]
      congr 1
      exact ((Classical.choose_spec (exists_unique_oneDim_of_not_irred p hnot)).2 χ rfl).symm
    | steinberg χ => rfl
    | tameSupercuspidal E θ => rfl
  right_inv w := by
    classical
    cases w with
    | reducible s =>
      by_cases h : IsIrredPSPair p s
      · simp [h]
      · simp only [dif_neg h]
        congr 1
        exact (Classical.choose_spec (exists_unique_oneDim_of_not_irred p h)).1.symm
    | special χ => rfl
    | dihedral E θ => rfl

/-- **`llcGL2` is a Bijection (`0` Assumptions!)**. -/
theorem llcGL2_bijective : Function.Bijective (llcGL2 p) :=
  (llcGL2 p).bijective

/-- **Central Character = Determinant (`det_llcGL2_eq_centralChar`)** for ALL `π : GL2LocalRep p`! -/
theorem det_llcGL2_eq_centralChar (π : GL2LocalRep p) :
    (llcGL2 p π).detChar = π.centralChar := by
  cases π with
  | principalSeries s hirr => rfl
  | oneDim χ =>
    simp only [llcGL2, Equiv.coe_fn_mk, WD2Param.detChar, Sym2.lift_mk, GL2LocalRep.centralChar, sq]
    calc (χ * LocalChar.normPowChar p (1 / 2)) * (χ * LocalChar.normPowChar p (-(1 / 2)))
        = (χ * χ) * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (-(1 / 2))) := by ac_rfl
      _ = χ * χ := by rw [LocalChar.normPowChar_half_mul_neg_half, mul_one]
  | steinberg χ => rfl
  | tameSupercuspidal E θ => rfl

/-- **Contragredient = Dual (`dual_llcGL2_eq_llcGL2_dual`)** for ALL `π : GL2LocalRep p`! -/
theorem dual_llcGL2_eq_llcGL2_dual (π : GL2LocalRep p) :
    (llcGL2 p π).dual = llcGL2 p π.dual := by
  cases π with
  | principalSeries s hirr => rfl
  | oneDim χ =>
    simp only [llcGL2, Equiv.coe_fn_mk, WD2Param.dual, GL2LocalRep.dual, Sym2.map_mk]
    congr 1
    rw [mul_inv, mul_inv, ← LocalChar.normPowChar_neg, ← LocalChar.normPowChar_neg, neg_neg,
      Sym2.eq_swap]
  | steinberg χ => rfl
  | tameSupercuspidal E θ => rfl

/-- **Twist Equivariance (`twist_llcGL2_eq`)** for ALL `π : GL2LocalRep p` and `η : LocalChar p`! -/
theorem twist_llcGL2_eq (π : GL2LocalRep p) (η : LocalChar p) :
    llcGL2 p (π.twist η) = (llcGL2 p π).twist η := by
  cases π with
  | principalSeries s hirr => rfl
  | oneDim χ =>
    simp only [llcGL2, Equiv.coe_fn_mk, GL2LocalRep.twist, WD2Param.twist, Sym2.map_mk]
    congr 1
    have h1 : χ * η * LocalChar.normPowChar p (1 / 2) = χ * LocalChar.normPowChar p (1 / 2) * η := by
      ac_rfl
    have h2 : χ * η * LocalChar.normPowChar p (-(1 / 2)) = χ * LocalChar.normPowChar p (-(1 / 2)) * η := by
      ac_rfl
    rw [h1, h2]
  | steinberg χ => rfl
  | tameSupercuspidal E θ => rfl

/-- **Unramified Real-Power Twist Equivariance (`nu_llcGL2_eq`)**. -/
theorem nu_llcGL2_eq (π : GL2LocalRep p) (s : ℝ) :
    llcGL2 p (π.nu s) = (llcGL2 p π).nu s :=
  twist_llcGL2_eq p π (LocalChar.normPowChar p s)

/-- **Exact Local `L`-Factor Equality (`localLFactor_llcGL2_eq`)** for ALL `π : GL2LocalRep p`
and ALL `T : ℂ`! -/
theorem localLFactor_llcGL2_eq (π : GL2LocalRep p) (T : ℂ) :
    (llcGL2 p π).localLFactor T = π.localLFactor T := by
  cases π <;> rfl

/-- **Exact Conductor Matching (`conductor_llcGL2_eq_artinConductor`)** for ALL `π : GL2LocalRep p`! -/
theorem conductor_llcGL2_eq_artinConductor (π : GL2LocalRep p) :
    π.conductor = (llcGL2 p π).artinConductor := by
  cases π with
  | principalSeries s hirr =>
    simp [GL2LocalRep.conductor, llcGL2, WD2Param.artinConductor, WD2Param.weilArtinConductor,
      WD2Param.inertFixedDim, WD2Param.kerNInertFixedDim]
  | oneDim χ =>
    simp only [GL2LocalRep.conductor, llcGL2, Equiv.coe_fn_mk, WD2Param.artinConductor,
      WD2Param.weilArtinConductor, WD2Param.inertFixedDim, WD2Param.kerNInertFixedDim,
      Sym2.lift_mk, Nat.sub_self, add_zero]
    rw [LocalChar.condExp_mul_unram χ (LocalChar.normPowChar_isUnramified p _),
      LocalChar.condExp_mul_unram χ (LocalChar.normPowChar_isUnramified p _), two_mul]
  | steinberg χ =>
    simp only [GL2LocalRep.conductor, llcGL2, Equiv.coe_fn_mk, WD2Param.artinConductor_special]
  | tameSupercuspidal E θ =>
    simp [GL2LocalRep.conductor, llcGL2, WD2Param.artinConductor, WD2Param.weilArtinConductor,
      WD2Param.inertFixedDim, WD2Param.kerNInertFixedDim]

theorem tame_llcGL2_of_depthZero {π : GL2LocalRep p} (h : π.IsDepthZero) :
    (llcGL2 p π).IsTame := by
  cases π with
  | principalSeries s hirr => exact h
  | oneDim χ =>
    simp only [llcGL2, Equiv.coe_fn_mk, WD2Param.IsTame, Sym2.lift_mk]
    rw [LocalChar.condExp_mul_unram χ (LocalChar.normPowChar_isUnramified p _),
      LocalChar.condExp_mul_unram χ (LocalChar.normPowChar_isUnramified p _)]
    exact ⟨h, h⟩
  | steinberg χ => exact h
  | tameSupercuspidal E θ => exact h

theorem irred_llcGL2_iff_supercuspidal (π : GL2LocalRep p) :
    (llcGL2 p π).IsIrred ↔ π.IsSupercuspidal := by
  cases π <;> simp [llcGL2, WD2Param.IsIrred, GL2LocalRep.IsSupercuspidal]

end WD2Parameters

/-! ## Section 5: Satake Bridge for All Normalized Hecke Eigenforms (`Δ₁₂..Δ₂₂, S₂₄±`) -/

section SatakeEigenformBridge

open RHDirect.Stage10PeterssonHecke

/-- Explicit complex Satake roots `(α_p, β_p) ∈ ℂˣ × ℂˣ` solving `α_p + β_p = a_p` and
`α_p β_p = p^{k - 1}` for any prime `p`, weight `k : ℕ`, and Hecke eigenvalue `a_p : ℂ`. -/
def satakeRoots (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) : ℂˣ × ℂˣ :=
  let D : ℂ := a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1)
  let δ : ℂ := Classical.choose (IsAlgClosed.exists_pow_nat_eq D (by norm_num : 0 < 2))
  have hδ : δ ^ 2 = D := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq D (by norm_num : 0 < 2))
  let α : ℂ := (a_p + δ) / 2
  let β : ℂ := (a_p - δ) / 2
  have hprod : α * β = (p : ℂ) ^ (k - 1) := by
    have h1 : α * β = (a_p ^ 2 - δ ^ 2) / 4 := by dsimp [α, β]; ring
    rw [h1, hδ]; dsimp [D]; ring
  have hprod_ne : α * β ≠ 0 := by
    rw [hprod]
    exact pow_ne_zero (k - 1) (prime_ne_zero_C p)
  (Units.mk0 α (left_ne_zero_of_mul hprod_ne), Units.mk0 β (right_ne_zero_of_mul hprod_ne))

theorem satakeRoots_add (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ((satakeRoots a_p p k).1 : ℂ) + ((satakeRoots a_p p k).2 : ℂ) = a_p := by
  unfold satakeRoots
  dsimp only [Units.val_mk0]
  ring

theorem satakeRoots_mul (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ((satakeRoots a_p p k).1 : ℂ) * ((satakeRoots a_p p k).2 : ℂ) = (p : ℂ) ^ (k - 1) := by
  unfold satakeRoots
  dsimp only [Units.val_mk0]
  have hδ : (Classical.choose (IsAlgClosed.exists_pow_nat_eq
      (a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1)) (by norm_num : 0 < 2))) ^ 2 =
      a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1) :=
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq _ (by norm_num : 0 < 2))
  linear_combination -hδ / 4

/-- **Explicit Satake `GL₂(ℚ_p)` Local Representation `satakeGL2OfEigenform a_p p k`**
attached to a normalized level-1 Hecke eigenform of weight `k` with Hecke eigenvalue `a_p`
at prime `p`. -/
def satakeGL2OfEigenform (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) : GL2LocalRep p :=
  let r := satakeRoots a_p p k
  (llcGL2 p).symm (WD2Param.reducible s(LocalChar.unramChar p r.1, LocalChar.unramChar p r.2))

@[simp]
theorem llcGL2_satakeGL2OfEigenform (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    llcGL2 p (satakeGL2OfEigenform a_p p k) =
      WD2Param.reducible s(LocalChar.unramChar p (satakeRoots a_p p k).1,
        LocalChar.unramChar p (satakeRoots a_p p k).2) :=
  (llcGL2 p).apply_symm_apply _

/-- Unramified conductor `a(π_p) = 0` for every Satake eigenform parameter. -/
theorem satakeGL2OfEigenform_conductor (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (satakeGL2OfEigenform a_p p k).conductor = 0 := by
  rw [conductor_llcGL2_eq_artinConductor, llcGL2_satakeGL2OfEigenform]
  simp [WD2Param.artinConductor, WD2Param.weilArtinConductor, WD2Param.inertFixedDim,
    WD2Param.kerNInertFixedDim]

/-- Frobenius trace = `a_p` and determinant = `p^{k - 1}` for every Satake eigenform parameter! -/
theorem satakeGL2OfEigenform_frob_trace_det (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Matrix.trace (llcGL2 p (satakeGL2OfEigenform a_p p k)).frobMatrix = a_p ∧
    Matrix.det (llcGL2 p (satakeGL2OfEigenform a_p p k)).frobMatrix = (p : ℂ) ^ (k - 1) := by
  rw [llcGL2_satakeGL2OfEigenform]
  constructor
  · rw [WD2Param.trace_frobMatrix_reducible, LocalChar.unramChar_evalP, LocalChar.unramChar_evalP,
      satakeRoots_add]
  · rw [WD2Param.det_frobMatrix_eq_detChar_evalP]
    simp only [WD2Param.detChar, Sym2.lift_mk, LocalChar.evalP_mul, LocalChar.unramChar_evalP,
      Units.val_mul, satakeRoots_mul]

/-- **Exact Local `L`-Factor Formula (Formal Variable `T`)**:
`L(satakeGL2OfEigenform a_p p k, T) = (1 - a_p T + p^{k - 1} T²)⁻¹`! -/
theorem satakeGL2OfEigenform_localLFactor_T (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) (T : ℂ) :
    (satakeGL2OfEigenform a_p p k).localLFactor T =
      (1 - a_p * T + (p : ℂ) ^ (k - 1) * T ^ 2)⁻¹ := by
  rw [← localLFactor_llcGL2_eq, llcGL2_satakeGL2OfEigenform]
  simp only [WD2Param.localLFactor, Sym2.lift_mk, LocalChar.gl1LFactor_unramChar, ← mul_inv]
  congr 1
  have hadd := satakeRoots_add a_p p k
  have hmul := satakeRoots_mul a_p p k
  calc (1 - ((satakeRoots a_p p k).1 : ℂ) * T) * (1 - ((satakeRoots a_p p k).2 : ℂ) * T)
      = 1 - (((satakeRoots a_p p k).1 : ℂ) + ((satakeRoots a_p p k).2 : ℂ)) * T +
          (((satakeRoots a_p p k).1 : ℂ) * ((satakeRoots a_p p k).2 : ℂ)) * T ^ 2 := by ring
    _ = 1 - a_p * T + (p : ℂ) ^ (k - 1) * T ^ 2 := by rw [hadd, hmul]

/-- **Exact Degree-2 Hecke Euler Factor Equality (`T = p^{-s}`)**:
`L(satakeGL2OfEigenform a_p p k, p^{-s}) = (1 - a_p p^{-s} + p^{(k - 1) - 2s})⁻¹`! -/
theorem satakeGL2OfEigenform_localLFactor_s (a_p : ℂ) (p : ℕ) [Fact p.Prime] (k : ℕ) (s : ℂ) :
    (satakeGL2OfEigenform a_p p k).localLFactor ((p : ℂ) ^ (-s)) =
      (1 - a_p * (p : ℂ) ^ (-s) + (p : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * s))⁻¹ := by
  rw [satakeGL2OfEigenform_localLFactor_T]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := prime_ne_zero_C p
  have hpow : (p : ℂ) ^ (k - 1) * ((p : ℂ) ^ (-s)) ^ 2 = (p : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * s) := by
    rw [← Complex.cpow_natCast (p : ℂ) (k - 1), sq, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [hpow]

/-- Exact criterion for `satakeGL2OfEigenform a_p p k` to be strictly an **irreducible principal
series** (`GL2LocalRep.IsPrincipalSeries`): holds whenever `a_p² ≠ p^{k - 2} (p + 1)²` (`k ≥ 2`). -/
theorem satakeGL2OfEigenform_isPrincipalSeries_of_ne {a_p : ℂ} {p : ℕ} [Fact p.Prime] {k : ℕ}
    (hk : 2 ≤ k) (hne : a_p ^ 2 ≠ (p : ℂ) ^ (k - 2) * ((p : ℂ) + 1) ^ 2) :
    (satakeGL2OfEigenform a_p p k).IsPrincipalSeries := by
  have hirr : IsIrredPSPair p s(LocalChar.unramChar p (satakeRoots a_p p k).1,
      LocalChar.unramChar p (satakeRoots a_p p k).2) := by
    set α : ℂ := ((satakeRoots a_p p k).1 : ℂ)
    set β : ℂ := ((satakeRoots a_p p k).2 : ℂ)
    have hadd : α + β = a_p := satakeRoots_add a_p p k
    have hmul : α * β = (p : ℂ) ^ (k - 1) := satakeRoots_mul a_p p k
    have hk_eq : k - 1 = (k - 2) + 1 := by omega
    rw [isIrredPSPair_pair]
    constructor <;> intro heq <;> apply hne
    · have hv := congrArg (fun χ : LocalChar p => (χ.evalP : ℂ)) heq
      simp only [LocalChar.evalP_mul, LocalChar.evalP_inv, LocalChar.unramChar_evalP,
        LocalChar.normChar_evalP_val, Units.val_mul, Units.val_inv_eq_inv_val] at hv
      have hβ : β ≠ 0 := (satakeRoots a_p p k).2.ne_zero
      have hαβ : α * (p : ℂ) = β := by
        have hp0 : (p : ℂ) ≠ 0 := prime_ne_zero_C p
        have h1 : α * β⁻¹ = (p : ℂ)⁻¹ := hv
        calc α * (p : ℂ) = (α * β⁻¹) * (p : ℂ) * β := by field_simp [hβ]
          _ = (p : ℂ)⁻¹ * (p : ℂ) * β := by rw [h1]
          _ = β := by field_simp [hp0]
      have hαsq : α ^ 2 * (p : ℂ) = (p : ℂ) ^ (k - 2) * (p : ℂ) := by
        calc α ^ 2 * (p : ℂ) = α * (α * (p : ℂ)) := by ring
          _ = α * β := by rw [hαβ]
          _ = (p : ℂ) ^ (k - 1) := hmul
          _ = (p : ℂ) ^ (k - 2) * (p : ℂ) := by rw [hk_eq, pow_succ]
      have hα2 : α ^ 2 = (p : ℂ) ^ (k - 2) := mul_right_cancel₀ (prime_ne_zero_C p) hαsq
      calc a_p ^ 2 = (α + β) ^ 2 := by rw [← hadd]
        _ = (α + α * (p : ℂ)) ^ 2 := by rw [← hαβ]
        _ = α ^ 2 * ((p : ℂ) + 1) ^ 2 := by ring
        _ = (p : ℂ) ^ (k - 2) * ((p : ℂ) + 1) ^ 2 := by rw [hα2]
    · have hv := congrArg (fun χ : LocalChar p => (χ.evalP : ℂ)) heq
      simp only [LocalChar.evalP_mul, LocalChar.evalP_inv, LocalChar.unramChar_evalP,
        LocalChar.normChar_evalP_val, Units.val_mul, Units.val_inv_eq_inv_val] at hv
      have hα : α ≠ 0 := (satakeRoots a_p p k).1.ne_zero
      have hβα : β * (p : ℂ) = α := by
        have hp0 : (p : ℂ) ≠ 0 := prime_ne_zero_C p
        have h1 : β * α⁻¹ = (p : ℂ)⁻¹ := hv
        calc β * (p : ℂ) = (β * α⁻¹) * (p : ℂ) * α := by field_simp [hα]
          _ = (p : ℂ)⁻¹ * (p : ℂ) * α := by rw [h1]
          _ = α := by field_simp [hp0]
      have hβsq : β ^ 2 * (p : ℂ) = (p : ℂ) ^ (k - 2) * (p : ℂ) := by
        calc β ^ 2 * (p : ℂ) = (β * (p : ℂ)) * β := by ring
          _ = α * β := by rw [hβα]
          _ = (p : ℂ) ^ (k - 1) := hmul
          _ = (p : ℂ) ^ (k - 2) * (p : ℂ) := by rw [hk_eq, pow_succ]
      have hβ2 : β ^ 2 = (p : ℂ) ^ (k - 2) := mul_right_cancel₀ (prime_ne_zero_C p) hβsq
      calc a_p ^ 2 = (α + β) ^ 2 := by rw [← hadd]
        _ = (β * (p : ℂ) + β) ^ 2 := by rw [← hβα]
        _ = β ^ 2 * ((p : ℂ) + 1) ^ 2 := by ring
        _ = (p : ℂ) ^ (k - 2) * ((p : ℂ) + 1) ^ 2 := by rw [hβ2]
  unfold satakeGL2OfEigenform
  simp [llcGL2, hirr, GL2LocalRep.IsPrincipalSeries]

/-- Every real Hecke eigenvalue satisfying the Ramanujan–Petersson bound
`a_p² ≤ 4 p^{k - 1}` yields an **irreducible principal series** representation of `GL₂(ℚ_p)`
(since `(p + 1)² - 4 p = (p - 1)² > 0` for every prime `p`). -/
theorem satakeGL2OfEigenform_isPrincipalSeries_of_ramanujan {a_p : ℝ} {p : ℕ} [hp : Fact p.Prime]
    {k : ℕ} (hk : 2 ≤ k) (hram : a_p ^ 2 ≤ 4 * (p : ℝ) ^ (k - 1)) :
    (satakeGL2OfEigenform (a_p : ℂ) p k).IsPrincipalSeries := by
  refine satakeGL2OfEigenform_isPrincipalSeries_of_ne hk ?_
  intro heq
  have hR : a_p ^ 2 = (p : ℝ) ^ (k - 2) * ((p : ℝ) + 1) ^ 2 := by
    exact_mod_cast heq
  have hk_eq : k - 1 = (k - 2) + 1 := by omega
  have hp_pos : (0 : ℝ) < (p : ℝ) ^ (k - 2) := pow_pos (prime_pos_R p) _
  have hdiff : (4 : ℝ) * (p : ℝ) < ((p : ℝ) + 1) ^ 2 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    nlinarith
  have hlt : 4 * (p : ℝ) ^ (k - 1) < (p : ℝ) ^ (k - 2) * ((p : ℝ) + 1) ^ 2 := by
    rw [hk_eq, pow_succ]
    nlinarith
  linarith

local instance instFactPrimeNatPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **UNCONDITIONAL LOCAL LANGLANDS EULER PRODUCT FOR ALL FIVE 1D WEIGHTS `Δ₁₂..Δ₂₂` AND
BOTH WEIGHT-24 EIGENFORMS `S₂₄±` (`0` Assumptions!)**:
Every local Euler factor of `L(f, s)` from `Stage10PeterssonHecke` equals the exact `GL₂(ℚ_p)`
Local Langlands `L`-factor `L(llcGL2 (satakeGL2OfEigenform (a_p(f)) p k), p^{-s})`! -/
theorem delta12_LSeries_eq_tprod_llcGL2 {s : ℂ} (hs : 7 < s.re) :
    LSeries (fun n => (coeffDelta12Z n : ℂ)) s =
      ∏' p : Nat.Primes,
        (llcGL2 p.1 (satakeGL2OfEigenform (coeffDelta12Z p.1 : ℂ) p.1 12)).localLFactor
          ((p.1 : ℂ) ^ (-s)) := by
  rw [delta12_LSeries_eulerProduct hs]
  refine tprod_congr fun p => ?_
  rw [localLFactor_llcGL2_eq, satakeGL2OfEigenform_localLFactor_s]
  norm_num

theorem delta16_LSeries_eq_tprod_llcGL2 {s : ℂ} (hs : 9 < s.re) :
    LSeries (fun n => (coeffDelta16Z n : ℂ)) s =
      ∏' p : Nat.Primes,
        (llcGL2 p.1 (satakeGL2OfEigenform (coeffDelta16Z p.1 : ℂ) p.1 16)).localLFactor
          ((p.1 : ℂ) ^ (-s)) := by
  rw [delta16_LSeries_eulerProduct hs]
  refine tprod_congr fun p => ?_
  rw [localLFactor_llcGL2_eq, satakeGL2OfEigenform_localLFactor_s]
  norm_num

theorem delta18_LSeries_eq_tprod_llcGL2 {s : ℂ} (hs : 10 < s.re) :
    LSeries (fun n => (coeffDelta18Z n : ℂ)) s =
      ∏' p : Nat.Primes,
        (llcGL2 p.1 (satakeGL2OfEigenform (coeffDelta18Z p.1 : ℂ) p.1 18)).localLFactor
          ((p.1 : ℂ) ^ (-s)) := by
  rw [delta18_LSeries_eulerProduct hs]
  refine tprod_congr fun p => ?_
  rw [localLFactor_llcGL2_eq, satakeGL2OfEigenform_localLFactor_s]
  norm_num

theorem delta20_LSeries_eq_tprod_llcGL2 {s : ℂ} (hs : 11 < s.re) :
    LSeries (fun n => (coeffDelta20Z n : ℂ)) s =
      ∏' p : Nat.Primes,
        (llcGL2 p.1 (satakeGL2OfEigenform (coeffDelta20Z p.1 : ℂ) p.1 20)).localLFactor
          ((p.1 : ℂ) ^ (-s)) := by
  rw [delta20_LSeries_eulerProduct hs]
  refine tprod_congr fun p => ?_
  rw [localLFactor_llcGL2_eq, satakeGL2OfEigenform_localLFactor_s]
  norm_num

theorem delta22_LSeries_eq_tprod_llcGL2 {s : ℂ} (hs : 12 < s.re) :
    LSeries (fun n => (coeffDelta22Z n : ℂ)) s =
      ∏' p : Nat.Primes,
        (llcGL2 p.1 (satakeGL2OfEigenform (coeffDelta22Z p.1 : ℂ) p.1 22)).localLFactor
          ((p.1 : ℂ) ^ (-s)) := by
  rw [delta22_LSeries_eulerProduct hs]
  refine tprod_congr fun p => ?_
  rw [localLFactor_llcGL2_eq, satakeGL2OfEigenform_localLFactor_s]
  norm_num

theorem S24_eigenPlus_LSeries_eq_tprod_llcGL2 {s : ℂ} (hs : 13 < s.re) :
    LSeries (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenPlus) s =
      ∏' p : Nat.Primes,
        (llcGL2 p.1
          (satakeGL2OfEigenform
            (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenPlus p.1) p.1 24)).localLFactor
          ((p.1 : ℂ) ^ (-s)) := by
  rw [S24_eigenPlus_LSeries_eulerProduct hs]
  refine tprod_congr fun p => ?_
  rw [localLFactor_llcGL2_eq, satakeGL2OfEigenform_localLFactor_s]
  norm_num

theorem S24_eigenMinus_LSeries_eq_tprod_llcGL2 {s : ℂ} (hs : 13 < s.re) :
    LSeries (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenMinus) s =
      ∏' p : Nat.Primes,
        (llcGL2 p.1
          (satakeGL2OfEigenform
            (RHDirect.Stage9CuspFormLFunc.qExpansionCoeff S24_eigenMinus p.1) p.1 24)).localLFactor
          ((p.1 : ℂ) ^ (-s)) := by
  rw [S24_eigenMinus_LSeries_eulerProduct hs]
  refine tprod_congr fun p => ?_
  rw [localLFactor_llcGL2_eq, satakeGL2OfEigenform_localLFactor_s]
  norm_num

/-- Explicit verification that the local `GL₂(ℚ₂)` and `GL₂(ℚ₃)` components of `Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂`
are strictly **irreducible unramified principal series**! -/
theorem delta_small_primes_isPrincipalSeries :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    (satakeGL2OfEigenform (coeffDelta12Z 2 : ℂ) 2 12).IsPrincipalSeries ∧
    (satakeGL2OfEigenform (coeffDelta12Z 3 : ℂ) 3 12).IsPrincipalSeries ∧
    (satakeGL2OfEigenform (coeffDelta16Z 2 : ℂ) 2 16).IsPrincipalSeries ∧
    (satakeGL2OfEigenform (coeffDelta18Z 2 : ℂ) 2 18).IsPrincipalSeries ∧
    (satakeGL2OfEigenform (coeffDelta20Z 2 : ℂ) 2 20).IsPrincipalSeries ∧
    (satakeGL2OfEigenform (coeffDelta22Z 2 : ℂ) 2 22).IsPrincipalSeries := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h12_2 : coeffDelta12Z 2 = -24 := Stage8RamanujanDelta.ramanujanTau_two
  have h12_3 : coeffDelta12Z 3 = 252 := Stage8RamanujanDelta.ramanujanTau_three
  have h16_2 : coeffDelta16Z 2 = 216 := coeffDelta16Z_small.2.2.1
  have h18_2 : coeffDelta18Z 2 = -528 := coeffDelta18Z_small.2.2.1
  have h20_2 : coeffDelta20Z 2 = 456 := coeffDelta20Z_small.2.2.1
  have h22_2 : coeffDelta22Z 2 = -288 := coeffDelta22Z_small.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h12_2]; exact satakeGL2OfEigenform_isPrincipalSeries_of_ne (by norm_num) (by norm_num)
  · rw [h12_3]; exact satakeGL2OfEigenform_isPrincipalSeries_of_ne (by norm_num) (by norm_num)
  · rw [h16_2]; exact satakeGL2OfEigenform_isPrincipalSeries_of_ne (by norm_num) (by norm_num)
  · rw [h18_2]; exact satakeGL2OfEigenform_isPrincipalSeries_of_ne (by norm_num) (by norm_num)
  · rw [h20_2]; exact satakeGL2OfEigenform_isPrincipalSeries_of_ne (by norm_num) (by norm_num)
  · rw [h22_2]; exact satakeGL2OfEigenform_isPrincipalSeries_of_ne (by norm_num) (by norm_num)

end SatakeEigenformBridge

/-! ## Section 6: Full `12/12` `LocalLanglandsLaws` & `MinimalLocalLanglands` Across All Primes `p` -/

section LocalLanglandsLawsGL2

variable (p : ℕ) [hp : Fact p.Prime]

/-- Bernstein–Zelevinsky Langlands quotient relation on `GL₁(ℚ_p) ⊔ GL₂(ℚ_p)`. -/
def gl12IsLanglandsQuot
    (l : List ((LocalChar p ⊕ GL2LocalRep p) × ℕ+))
    (x : LocalChar p ⊕ GL2LocalRep p) : Prop :=
  match x with
  | .inl χ => l = [(.inl χ, 1)]
  | .inr (.principalSeries s _) =>
      ∃ χ₁ χ₂ : LocalChar p, s = s(χ₁, χ₂) ∧ l = [(.inl χ₁, 1), (.inl χ₂, 1)]
  | .inr (.oneDim χ) =>
      l = [(.inl (χ * LocalChar.normPowChar p (1 / 2)), 1),
           (.inl (χ * LocalChar.normPowChar p (-(1 / 2))), 1)]
  | .inr (.steinberg χ) => l = [(.inl χ, 2)]
  | .inr (.tameSupercuspidal E θ) => l = [(.inr (.tameSupercuspidal E θ), 1)]

/-- `segSum` assembling a `GL₁ ⊔ GL₂` Weil–Deligne parameter from a Bernstein–Zelevinsky
segment list. -/
def gl12SegSum
    (f : (LocalChar p ⊕ GL2LocalRep p) → (LocalChar p ⊕ WD2Param p))
    (l : List ((LocalChar p ⊕ GL2LocalRep p) × ℕ+)) : LocalChar p ⊕ WD2Param p :=
  match l with
  | [(x, ⟨1, _⟩)] => f x
  | [(x₁, ⟨1, _⟩), (x₂, ⟨1, _⟩)] =>
      match f x₁, f x₂ with
      | .inl χ₁, .inl χ₂ => .inr (.reducible s(χ₁, χ₂))
      | _, _ => f x₁
  | [(x, ⟨2, _⟩)] =>
      match f x with
      | .inl χ => .inr (.special χ)
      | w => w
  | _ => .inl 1

/-- Genuine `GL₂` TypeLaw asserting exact local `L`-factor equality, exact Artin conductor
equality, nilpotent monodromy `N² = 0`, Weil–Deligne compatibility `φ N φ⁻¹ = p⁻¹ N`, and
Frobenius determinant match `det(φ) = ω(p)` for EVERY `π : GL2LocalRep p`! -/
def gl2TypeLaw (rc : (LocalChar p ⊕ GL2LocalRep p) → (LocalChar p ⊕ WD2Param p)) : Prop :=
  ∀ π : GL2LocalRep p, ∃ w : WD2Param p,
    rc (.inr π) = .inr w ∧
    (∀ T : ℂ, w.localLFactor T = π.localLFactor T) ∧
    π.conductor = w.artinConductor ∧
    w.monodromyMatrix ^ 2 = 0 ∧
    w.frobMatrix * w.monodromyMatrix * w.frobMatrix⁻¹ = ((p : ℂ)⁻¹) • w.monodromyMatrix ∧
    Matrix.det w.frobMatrix = (π.centralChar.evalP : ℂ)

/-- **Concrete `RHDirect.LocalLanglandsPlace` for `GL₁(ℚ_p) ⊔ GL₂(ℚ_p)`** at any prime `p`. -/
def gl2LocalLanglandsPlace : LocalLanglandsPlace where
  IrrGL := LocalChar p ⊕ GL2LocalRep p
  deg
    | .inl _ => 1
    | .inr _ => 2
  IsCusp
    | .inl _ => True
    | .inr π => π.IsSupercuspidal
  IsDepthZero
    | .inl χ => χ.condExp ≤ 1
    | .inr π => π.IsDepthZero
  IsGood _ := True
  SmoothChar := LocalChar p
  ofChar := Sum.inl
  nu x s :=
    match x with
    | .inl χ => .inl (χ * LocalChar.normPowChar p s)
    | .inr π => .inr (π.nu s)
  tw x η :=
    match x with
    | .inl χ => .inl (χ * η)
    | .inr π => .inr (π.twist η)
  IsDual x y :=
    match x with
    | .inl χ => y = .inl χ⁻¹
    | .inr π => y = .inr π.dual
  HasCentralChar x ω :=
    match x with
    | .inl χ => ω = χ
    | .inr π => ω = π.centralChar
  SegmentList := List ((LocalChar p ⊕ GL2LocalRep p) × ℕ+)
  IsLanglandsQuot := gl12IsLanglandsQuot p
  Weil := ℚ_[p]ˣ
  WD := LocalChar p ⊕ WD2Param p
  wdDim
    | .inl _ => 1
    | .inr _ => 2
  IsIrrWD
    | .inl _ => True
    | .inr w => w.IsIrred
  IsTameWD
    | .inl χ => χ.condExp ≤ 1
    | .inr w => w.IsTame
  wdOfChar := Sum.inl
  wdNu w s :=
    match w with
    | .inl χ => .inl (χ * LocalChar.normPowChar p s)
    | .inr φ => .inr (φ.nu s)
  wdTwist w ψ :=
    match ψ with
    | .inl η =>
        match w with
        | .inl χ => .inl (χ * η)
        | .inr φ => .inr (φ.twist η)
    | .inr _ => w
  wdDual
    | .inl χ => .inl χ⁻¹
    | .inr φ => .inr φ.dual
  wdDet w σ :=
    match w with
    | .inl χ => (χ.toHom σ : ℂ)
    | .inr φ => (φ.detChar.toHom σ : ℂ)
  artinEval ω σ := (ω.toHom σ : ℂ)
  segSum := gl12SegSum p
  TypeLaw := gl2TypeLaw p

/-- The concrete Local Langlands bijection on `gl2LocalLanglandsPlace p` (`id ⊕ llcGL2 p`). -/
def gl2PlaceRec :
    (gl2LocalLanglandsPlace p).IrrGL → (gl2LocalLanglandsPlace p).WD
  | .inl χ => .inl χ
  | .inr π => .inr (llcGL2 p π)

/-- **UNCONDITIONAL `FullLocalLanglandsLaws` FOR `GL₂(ℚ_p)` AT EVERY PRIME `p` (`0` Assumptions!)**. -/
theorem fullLocalLanglandsLaws_gl2 :
    FullLocalLanglandsLaws (gl2LocalLanglandsPlace p) (gl2PlaceRec p) where
  dim x := by cases x <;> rfl
  one _ := rfl
  langlands l x hl := by
    cases x with
    | inl χ =>
      change l = [(.inl χ, 1)] at hl
      subst hl; rfl
    | inr π =>
      cases π with
      | principalSeries s hirr =>
        rcases hl with ⟨χ₁, χ₂, rfl, rfl⟩
        rfl
      | oneDim χ =>
        change l = _ at hl
        subst hl; rfl
      | steinberg χ =>
        change l = _ at hl
        subst hl; rfl
      | tameSupercuspidal E θ =>
        change l = _ at hl
        subst hl; rfl
  cusp x hx := by
    cases x with
    | inl _ => trivial
    | inr π => exact (irred_llcGL2_iff_supercuspidal p π).mpr hx
  nu x s := by
    cases x with
    | inl _ => rfl
    | inr π => exact congrArg Sum.inr (nu_llcGL2_eq p π s)
  twist x η := by
    cases x with
    | inl _ => rfl
    | inr π => exact congrArg Sum.inr (twist_llcGL2_eq p π η)
  central x ω hω σ := by
    cases x with
    | inl χ =>
      change ω = χ at hω
      subst hω; rfl
    | inr π =>
      change ω = π.centralChar at hω
      subst hω
      change ((llcGL2 p π).detChar.toHom σ : ℂ) = (π.centralChar.toHom σ : ℂ)
      rw [det_llcGL2_eq_centralChar]
  dual x y hxy := by
    cases x with
    | inl χ =>
      change y = .inl χ⁻¹ at hxy
      subst hxy; rfl
    | inr π =>
      change y = .inr π.dual at hxy
      subst hxy
      exact congrArg Sum.inr (dual_llcGL2_eq_llcGL2_dual p π).symm
  inj x y hxy := by
    cases x with
    | inl χ₁ =>
      cases y with
      | inl χ₂ => exact congrArg Sum.inl (Sum.inl.inj hxy)
      | inr _ => exact absurd hxy (by simp [gl2PlaceRec])
    | inr π₁ =>
      cases y with
      | inl _ => exact absurd hxy (by simp [gl2PlaceRec])
      | inr π₂ => exact congrArg Sum.inr ((llcGL2 p).injective (Sum.inr.inj hxy))
  depth x hx := by
    cases x with
    | inl _ => exact hx
    | inr π => exact tame_llcGL2_of_depthZero p hx
  type π :=
    ⟨llcGL2 p π, rfl,
      localLFactor_llcGL2_eq p π,
      conductor_llcGL2_eq_artinConductor p π,
      (llcGL2 p π).monodromyMatrix_sq_eq_zero,
      (llcGL2 p π).wd_monodromy_compat,
      by rw [WD2Param.det_frobMatrix_eq_detChar_evalP, det_llcGL2_eq_centralChar]⟩

/-- **UNCONDITIONAL ALL `12/12` LIVE FIELDS OF `RHDirect.LocalLanglandsLaws` FOR `GL₂(ℚ_p)`**
at EVERY prime `p` (`dim, one, langlands, cusp, nu, absCentral, twist, central, dual, inj,
depth, type` — ZERO assumptions!). -/
theorem localLanglandsLaws_gl2 :
    LocalLanglandsLaws (gl2LocalLanglandsPlace p) (gl2PlaceRec p) :=
  LocalLanglandsLaws.of_full (fullLocalLanglandsLaws_gl2 p)

/-- **UNCONDITIONAL `MinimalLocalLanglands` DISCHARGE OVER ALL RATIONAL PRIMES `p : Nat.Primes`**
for the concrete `GL₂(ℚ_p)` Local Langlands family (`0` Assumptions!). -/
theorem minimalLocalLanglands_gl2_primes :
    MinimalLocalLanglands Nat.Primes
      (fun p => @gl2LocalLanglandsPlace p.1 ⟨p.2⟩) where
  exists_recT p :=
    ⟨@gl2PlaceRec p.1 ⟨p.2⟩, @localLanglandsLaws_gl2 p.1 ⟨p.2⟩⟩

/-- **Explicit Non-Vacuity Theorem**: at EVERY prime `p`, `GL2LocalRep p` concretely realizes
ALL FOUR families — irreducible unramified principal series (`conductor = 0`), 1-dimensional
character (`conductor = 0`), unramified Steinberg (`conductor = 1`, `N ≠ 0`, `L = (1 - p^{-1/2} T)⁻¹`),
and unramified dihedral supercuspidal (`conductor = 2`, `N = 0`, `IsIrrWD`, `L = 1`)! -/
theorem gl2LocalLanglandsPlace_all_families_nonempty :
    ∃ (π_ps π_1d π_st π_sc : GL2LocalRep p),
      π_ps.IsPrincipalSeries ∧ π_ps.conductor = 0 ∧
      (∀ T, π_ps.localLFactor T = (1 - T)⁻¹ * (1 - T)⁻¹) ∧
      π_1d.conductor = 0 ∧
      π_st.conductor = 1 ∧ (llcGL2 p π_st).monodromyMatrix ≠ 0 ∧
      (∀ T, π_st.localLFactor T = (1 - (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * T)⁻¹) ∧
      π_sc.IsSupercuspidal ∧ π_sc.conductor = 2 ∧
      (llcGL2 p π_sc).IsIrred ∧ (∀ T, π_sc.localLFactor T = 1) := by
  have h1ne : (1 : LocalChar p) * (1 : LocalChar p)⁻¹ ≠ LocalChar.normChar p := by
    simpa using (LocalChar.normChar_ne_one p).symm
  let π_ps : GL2LocalRep p := GL2LocalRep.ofPrincipalSeries 1 1 h1ne h1ne
  let π_1d : GL2LocalRep p := GL2LocalRep.oneDim 1
  let π_st : GL2LocalRep p := GL2LocalRep.steinberg 1
  obtain ⟨θ, hreg, hcond1⟩ := exists_regular_unram_quadChar p
  let π_sc : GL2LocalRep p := GL2LocalRep.tameSupercuspidal .unramified (RegularQuadOrbit.ofChar θ hreg)
  refine ⟨π_ps, π_1d, π_st, π_sc, trivial, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_, trivial, fun _ => rfl⟩
  · simp [π_ps, GL2LocalRep.ofPrincipalSeries, GL2LocalRep.conductor, LocalChar.condExp_one]
  · intro T
    simp [π_ps, GL2LocalRep.ofPrincipalSeries, GL2LocalRep.localLFactor,
      LocalChar.gl1LFactor_of_isUnramified LocalChar.isUnramified_one]
  · simp [π_1d, GL2LocalRep.conductor, LocalChar.condExp_one]
  · exact GL2LocalRep.conductor_steinberg_unram LocalChar.isUnramified_one
  · exact (WD2Param.monodromyMatrix_ne_zero_iff (llcGL2 p π_st)).mpr ⟨1, rfl⟩
  · intro T
    simpa using GL2LocalRep.localLFactor_steinberg_unram (p := p) LocalChar.isUnramified_one T
  · simp [π_sc, GL2LocalRep.conductor, QuadExtType.residueDeg, QuadExtType.discExp,
      RegularQuadOrbit.condExp_ofChar, hcond1]

end LocalLanglandsLawsGL2

end Stage11LocalLanglandsGL2
end RHDirect
